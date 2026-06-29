import requests
import re
import os
import yaml
import csv
import threading
import hashlib
import base64
import logging
import copy
import time
from datetime import datetime, timezone, timedelta
from concurrent.futures import ThreadPoolExecutor, as_completed
from urllib.parse import unquote, parse_qsl, urlsplit, quote
from collections import deque
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

# 配置日志记录
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

# 加载配置文件 (config.yaml)
def load_config():
    if os.path.exists("config.yaml"):
        with open("config.yaml", "r", encoding="utf-8") as f:
            return yaml.safe_load(f)
    return {"settings": {"max_file_size_mb": 5, "timeout_seconds": 20, "gist_pages": 1}, "filters": {"exclude_equals": [], "exclude_contains": [], "exclude_owners": []}, "protocols": ["vless", "hysteria2", "hy2", "anytls", "hysteria", "tuic"]}

# 加载静态规则配置文件 (rules.yaml)
def load_rules_config():
    rules_file = "rules.yaml"
    if os.path.exists(rules_file):
        with open(rules_file, "r", encoding="utf-8") as f:
            try:
                return yaml.safe_load(f)
            except Exception as e:
                logging.error(f"Error loading rules.yaml: {e}")
                return {}
    return {}

config = load_config()
rules_config = load_rules_config()

# 配置常量
ALL_NODES_FILE = "all_nodes.yaml"
STATS_FILE = "gist_stats.csv"
SOURCE_HISTORY_FILE = "source_history.csv"
ALL_NODES_DAT = "all_nodes.dat"
ACTIVE_URLS_FILE = "active_raw_urls.txt"

MAX_FILE_SIZE = config["settings"].get("max_file_size_mb", 5) * 1024 * 1024
TIMEOUT = config["settings"].get("timeout_seconds", 20)
MAX_MEMO_B64 = 5000
MAX_PER_LAYER = 300
MAX_RECURSION = 3
MAX_TEXT_SIZE = 1024 * 1024

TOKEN = os.getenv("GH_TOKEN")
EXCLUDE_EQUALS = {f.lower() for f in config["filters"].get("exclude_equals", [])}
EXCLUDE_CONTAINS = {f.lower() for f in config["filters"].get("exclude_contains", [])}
EXCLUDE_OWNERS = {o.lower() for o in config["filters"].get("exclude_owners", [])}

SUPPORTED_PROTOCOLS = ["vless", "hysteria2", "hy2", "anytls", "hysteria", "tuic"]
ALLOWED_PROTOCOLS = set(SUPPORTED_PROTOCOLS)

PROTO_PATTERNS = {
    p: re.compile(rf"{re.escape(p)}[a-zA-Z0-9\-\._~:/\?#\[\]@!$&'()*+,;=]{{20,256}}", re.I)
    for p in sorted(SUPPORTED_PROTOCOLS, key=len, reverse=True)
}

# 新增 Code Search 查询关键词
GH_SEARCH_QUERIES = [
    'vless reality path:*.txt',
    'hysteria2 path:*.txt',
    'tuic path:*.txt',
    'filename:config.yaml'
]

thread_local = threading.local()

def is_valid_clash_node(node):
    if not node: return False
    return node.get("server") and node.get("port") and (node.get("type") in ALLOWED_PROTOCOLS or node.get("type") == "hysteria2")

def parse_uri_to_clash(uri):
    try:
        parsed = urlsplit(uri)
        scheme = parsed.scheme.lower()
        if not parsed.hostname or scheme not in ALLOWED_PROTOCOLS: return None

        query = dict(parse_qsl(parsed.query))
        node = {
            "name": unquote(parsed.fragment) if parsed.fragment else f"{scheme}-{parsed.hostname}-{parsed.port}",
            "type": "hysteria2" if scheme == "hy2" else scheme,
            "server": parsed.hostname,
            "port": int(parsed.port) if parsed.port else 443,
            "udp": True
        }

        if scheme == "vless":
            node.update({
                "uuid": parsed.username, "cipher": "auto",
                "tls": query.get("security") in ["tls", "reality"],
                "servername": query.get("sni", ""),
                "network": query.get("type", "tcp")
            })
            if query.get("security") == "reality":
                node["reality-opts"] = {"public-key": query.get("pbk", ""), "short-id": query.get("sid", "")}
                node["fingerprint"] = query.get("fp", "chrome")
            if node["network"] == "ws":
                node["ws-opts"] = {"path": query.get("path", "/"), "headers": {"Host": query.get("host", "")}}
            elif node["network"] == "grpc":
                node["grpc-opts"] = {"grpc-service-name": query.get("serviceName", "")}

        elif scheme in ["hysteria2", "hy2"]:
            node["type"] = "hysteria2"
            node["auth"] = parsed.username if parsed.username else query.get("auth", "")
            node["sni"] = query.get("sni", "")
            node["skip-cert-verify"] = query.get("insecure") in ["1", "true"]
            if query.get("obfs"):
                node["obfs"] = query.get("obfs")
                node["obfs-password"] = query.get("obfs-password", "")

        elif scheme == "hysteria":
            node.update({
                "auth": query.get("auth", ""), "sni": query.get("sni", ""),
                "up": query.get("up", ""), "down": query.get("down", ""),
                "protocol": query.get("protocol", "udp")
            })

        elif scheme == "tuic":
            node.update({
                "uuid": parsed.username, "password": parsed.password if parsed.password else query.get("pass", ""),
                "sni": query.get("sni", ""), "alpn": query.get("alpn", "h3").split(","),
                "congestion-controller": query.get("congestion_control", "cubic")
            })

        elif scheme == "anytls":
            node["tls"] = True
            node["sni"] = query.get("sni", "")

        return node
    except: return None

class NodeManager:
    def __init__(self):
        self.nodes = set()
        self.source_urls = set()
        self.nodes_lock = threading.Lock()
        self.source_lock = threading.Lock()
        self.seen_core_hashes = set()
        self.initial_node_count = 0

    def add_node(self, uri):
        if not uri or "://" not in uri: return
        h = core_hash(uri)
        if not h: return
        with self.nodes_lock:
            if h not in self.seen_core_hashes:
                self.nodes.add(uri)
                self.seen_core_hashes.add(h)

    def add_source(self, url):
        with self.source_lock: self.source_urls.add(url)

    def load_dat(self):
        if os.path.exists(ALL_NODES_DAT):
            with open(ALL_NODES_DAT, "r", encoding="utf-8") as f:
                for line in f:
                    line = line.strip()
                    if line and not line.startswith("#"): self.add_node(line)
            self.initial_node_count = len(self.nodes)

    def load_sources(self):
        if os.path.exists(SOURCE_HISTORY_FILE):
            with open(SOURCE_HISTORY_FILE, "r", encoding="utf-8") as f:
                for row in csv.reader(f):
                    if row: self.add_source(row[0])

    def save_to_yaml(self, file_path):
        raw_data = sorted(list(self.nodes))
        clash_proxies = [node for uri in raw_data if (node := parse_uri_to_clash(uri)) and is_valid_clash_node(node)]
        scraped_names = [p["name"] for p in clash_proxies]

        yaml_data = copy.deepcopy(rules_config)
        proxy_groups = yaml_data.get("proxy-groups", [])
        for group in proxy_groups:
            if group.get("name") in ["自动优选", "AI 优选"]:
                group["proxies"] = scraped_names
        
        yaml_data["proxies"] = clash_proxies
        beijing_time = datetime.now(timezone(timedelta(hours=8))).strftime("%Y-%m-%d %H:%M:%S")
        with open(file_path + ".tmp", "w", encoding="utf-8") as f:
            f.write(f"# Last updated: {beijing_time} | Total nodes: {len(clash_proxies)}\n")
            yaml.dump(yaml_data, f, allow_unicode=True, sort_keys=False)
        os.replace(file_path + ".tmp", file_path)

    def save_to_dat(self, file_path):
        all_uris = sorted(list(self.nodes))
        if self.initial_node_count > 10 and len(all_uris) < (self.initial_node_count * 0.5):
            logging.error(f"Critical: Current node count ({len(all_uris)}) is too low compared to initial ({self.initial_node_count}). Skipping update.")
            return

        beijing_time = datetime.now(timezone(timedelta(hours=8))).strftime("%Y-%m-%d %H:%M:%S")
        with open(file_path + ".tmp", "w", encoding="utf-8") as f:
            f.write(f"# Last updated: {beijing_time} | Total permanent nodes: {len(all_uris)}\n")
            for uri in all_uris: f.write(uri + "\n")
        os.replace(file_path + ".tmp", file_path)

    def save_sources(self):
        with open(SOURCE_HISTORY_FILE + ".tmp", "w", encoding="utf-8", newline='') as f:
            writer = csv.writer(f)
            for url in sorted(self.source_urls): writer.writerow([url])
        os.replace(SOURCE_HISTORY_FILE + ".tmp", SOURCE_HISTORY_FILE)

manager = NodeManager()
memo_lock, stats_lock, api_semaphore = threading.Lock(), threading.Lock(), threading.Semaphore(12)
memo_b64_queue, memo_b64_set, stats_data = deque(maxlen=MAX_MEMO_B64), set(), {}

def get_session():
    if not hasattr(thread_local, "session"):
        session = requests.Session()
        session.mount("https://", HTTPAdapter(pool_connections=12, pool_maxsize=12, max_retries=Retry(total=3, backoff_factor=1, status_forcelist=[429, 500, 502, 503, 504])))
        if TOKEN: session.headers.update({"Authorization": f"Bearer {TOKEN}"})
        thread_local.session = session
    return thread_local.session

def core_hash(uri):
    if not uri or "://" not in uri: return None
    parsed = urlsplit(uri)
    auth_part = f"{parsed.username}:{parsed.password}" if (parsed.username or parsed.password) else ""
    netloc = parsed.hostname if parsed.hostname else ""
    query = dict(parse_qsl(parsed.query))
    normalized_query = '&'.join(f'{k}={v}' for k, v in sorted(query.items()))
    normalized = f"{parsed.scheme}://{auth_part}@{netloc}:{parsed.port or ''}{parsed.path}?{normalized_query}"
    return hashlib.md5(normalized.encode()).hexdigest()

def is_valid_node(uri):
    if len(uri) < 20 or "://" not in uri: return False
    parsed = urlsplit(uri)
    if not parsed.hostname: return False
    if parsed.scheme.lower() not in ALLOWED_PROTOCOLS: return False
    if any(c in uri for c in ['{', '}', ' ']): return False
    return True

def extract_nodes(text, depth=0):
    if not text or len(text) < 20: return []
    found = []
    if depth < MAX_RECURSION:
        b64_matches = re.findall(r'(?:[A-Za-z0-9+/]{4}){10,}', text)
        for b64 in b64_matches[:50]:
            with memo_lock:
                if b64 in memo_b64_set: continue
                if len(memo_b64_queue) == MAX_MEMO_B64: memo_b64_set.remove(memo_b64_queue.popleft())
                memo_b64_queue.append(b64); memo_b64_set.add(b64)
            try:
                decoded = base64.b64decode(b64 + '=' * (-len(b64) % 4)).decode('utf-8', errors='ignore')
                if "://" in decoded: found.extend(extract_nodes(decoded, depth + 1))
            except: pass
    for _, pattern in PROTO_PATTERNS.items():
        matches = pattern.findall(text)
        for m in matches:
            if is_valid_node(m): found.append(m)
    return found[:MAX_PER_LAYER]

def process_raw(raw_url):
    with api_semaphore:
        try:
            r = get_session().get(raw_url, timeout=TIMEOUT)
            if r.status_code == 200 and len(r.text) < MAX_TEXT_SIZE:
                nodes = extract_nodes(r.text)
                return raw_url, nodes, len(nodes)
        except Exception as e: logging.error(f"Failed to fetch {raw_url}: {e}")
        return raw_url, [], 0

# 新增 Code Search 逻辑
def search_code_by_keywords(urls_to_scan):
    for query in GH_SEARCH_QUERIES:
        try:
            resp = get_session().get(f"https://api.github.com/search/code?q={quote(query)}&per_page=30", timeout=TIMEOUT)
            if resp.status_code == 200:
                for item in resp.json().get("items", []):
                    raw_url = item.get("html_url", "").replace("github.com", "raw.githubusercontent.com").replace("/blob/", "/")
                    if raw_url: urls_to_scan.add(raw_url)
            time.sleep(1)
        except: continue

def main():
    manager.load_dat()
    manager.load_sources()
    
    urls_to_scan = set()
    
    # 1. 执行原有的 Gist 时间流抓取
    for page in range(1, config["settings"].get("gist_pages", 1) + 1):
        try:
            resp = get_session().get(f"https://api.github.com/gists/public?page={page}&per_page=100", timeout=TIMEOUT)
            if resp.status_code == 200:
                for gist in resp.json():
                    if gist.get("owner", {}).get("login", "").lower() not in EXCLUDE_OWNERS:
                        for f_info in gist.get("files", {}).values():
                            raw = f_info.get("raw_url")
                            fn = f_info.get("filename", "").lower()
                            if raw and not (fn in EXCLUDE_EQUALS or any(k in fn for k in EXCLUDE_CONTAINS)): 
                                urls_to_scan.add(raw)
        except: continue

    # 2. 融合 Code Search 补充抓取
    search_code_by_keywords(urls_to_scan)

    active_urls_found = []
    with ThreadPoolExecutor(max_workers=12) as executor:
        futures = [executor.submit(process_raw, url) for url in urls_to_scan]
        for future in as_completed(futures):
            url, result, count = future.result()
            if count > 0:
                manager.add_source(url)
                active_urls_found.append(url)
                with stats_lock: stats_data[url] = count
                for node in result: manager.add_node(node)

    manager.save_to_yaml(ALL_NODES_FILE)
    manager.save_to_dat(ALL_NODES_DAT)
    manager.save_sources()

    existing_urls = set()
    if os.path.exists(ACTIVE_URLS_FILE):
        with open(ACTIVE_URLS_FILE, "r", encoding="utf-8") as f:
            for line in f:
                url = line.strip()
                if url: existing_urls.add(url)
    
    combined_urls = sorted(existing_urls.union(set(active_urls_found)))
    with open(ACTIVE_URLS_FILE, "w", encoding="utf-8") as f:
        for url in combined_urls:
            f.write(url + "\n")

    with open(STATS_FILE, "a", encoding="utf-8", newline='') as f:
        writer = csv.writer(f)
        writer.writerow(["url", "nodes_found"])
        for url, count in stats_data.items(): writer.writerow([url, count])
    print(f"Success! Total permanent nodes: {len(manager.nodes)}. Sources: {len(manager.source_urls)}")

if __name__ == "__main__":
    main()
