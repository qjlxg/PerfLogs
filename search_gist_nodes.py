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
import sys
import collections
from datetime import datetime, timezone, timedelta
from concurrent.futures import ThreadPoolExecutor, as_completed
from urllib.parse import unquote, parse_qsl, urlsplit
from collections import deque
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

# 配置日志记录
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

def load_config():
    config_path = "config.yaml"
    if not os.path.exists(config_path): sys.exit(1)
    try:
        with open(config_path, "r", encoding="utf-8") as f:
            config = yaml.safe_load(f)
            return config
    except: sys.exit(1)

def load_rules_config():
    rules_file = "rules.yaml"
    if os.path.exists(rules_file):
        with open(rules_file, "r", encoding="utf-8") as f:
            try: return yaml.safe_load(f)
            except: return {}
    return {}

config = load_config()
rules_config = load_rules_config()

# 配置常量
ALL_NODES_FILE = "all_nodes.yaml"
TEMP_LOG_FILE = "temp_log.yaml"
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
EXCLUDE_CONTAINS.update({f.lower() for f in config["filters"].get("exclude_files", [])})
EXCLUDE_OWNERS = {o.lower() for o in config["filters"].get("exclude_owners", [])}
SEARCH_INCLUDE = [str(k).lower() for k in config.get("search_keywords", {}).get("include", [])]
SEARCH_EXCLUDE = [str(k).lower() for k in config.get("search_keywords", {}).get("exclude", [])]

SUPPORTED_PROTOCOLS = config.get("protocols", ["vless", "hysteria2", "hy2", "anytls", "hysteria", "tuic"])
ALLOWED_PROTOCOLS = set(SUPPORTED_PROTOCOLS)

PROTO_PATTERNS = {
    p: re.compile(rf"{re.escape(p)}[a-zA-Z0-9\-\._~:/\?#\[\]@!$&'()*+,;=]{{20,256}}", re.I)
    for p in sorted(SUPPORTED_PROTOCOLS, key=len, reverse=True)
}

thread_local = threading.local()
memo_b64 = collections.OrderedDict()
memo_lock = threading.Lock()

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
        elif scheme == "hysteria":
            node.update({"auth": query.get("auth", ""), "sni": query.get("sni", ""), "protocol": query.get("protocol", "udp")})
        elif scheme == "tuic":
            node.update({"uuid": parsed.username, "password": parsed.password or query.get("pass", ""), "sni": query.get("sni", "")})
        return node
    except: return None

class NodeManager:
    def __init__(self):
        self.nodes, self.temp_nodes, self.source_urls = set(), set(), set()
        self.nodes_lock, self.temp_lock, self.source_lock = threading.Lock(), threading.Lock(), threading.Lock()
        self.seen_core_hashes_all, self.seen_core_hashes_temp = set(), set()
        self.hash_history_all, self.hash_history_temp = deque(maxlen=20000), deque(maxlen=20000)

    def add_node(self, uri, is_temp=False):
        if not uri or "://" not in uri: return
        h = core_hash(uri)
        if not h: return
        target_set, target_lock, seen_set, history = (
            (self.temp_nodes, self.temp_lock, self.seen_core_hashes_temp, self.hash_history_temp)
            if is_temp else (self.nodes, self.nodes_lock, self.seen_core_hashes_all, self.hash_history_all)
        )
        with target_lock:
            if h not in seen_set:
                target_set.add(uri); seen_set.add(h); history.append(h)
                if len(history) == 20000: seen_set.remove(history.popleft())

    def add_source(self, url):
        with self.source_lock: self.source_urls.add(url)

    def load_from_file(self, file_path, is_temp=False):
        if os.path.exists(file_path):
            try:
                with open(file_path, "r", encoding="utf-8") as f:
                    for line in f:
                        line = line.strip()
                        if line and not line.startswith("#"): self.add_node(line, is_temp)
            except: pass

    def load_sources(self):
        if os.path.exists(SOURCE_HISTORY_FILE):
            with open(SOURCE_HISTORY_FILE, "r", encoding="utf-8") as f:
                for row in csv.reader(f):
                    if row: self.add_source(row[0])

    def save_to_file(self, file_path, is_temp=False):
        raw_data = sorted(list(self.temp_nodes if is_temp else self.nodes))
        clash_proxies = [node for uri in raw_data if (node := parse_uri_to_clash(uri)) and (node.get("server") and node.get("port"))]
        scraped_names = [p["name"] for p in clash_proxies]
        yaml_data = copy.deepcopy(rules_config)
        for group in yaml_data.get("proxy-groups", []):
            if group.get("name") == "自动优选": group["proxies"] = scraped_names
        yaml_data["proxies"] = clash_proxies
        beijing_time = datetime.now(timezone(timedelta(hours=8))).strftime("%Y-%m-%d %H:%M:%S")
        with open(file_path + ".tmp", "w", encoding="utf-8") as f:
            f.write(f"# Last updated: {beijing_time} | Scraped nodes: {len(clash_proxies)}\n")
            yaml.dump(yaml_data, f, allow_unicode=True, sort_keys=False)
        os.replace(file_path + ".tmp", file_path)

    def save_to_dat(self, file_path):
        all_uris = sorted(list(self.nodes.union(self.temp_nodes)))
        beijing_time = datetime.now(timezone(timedelta(hours=8))).strftime("%Y-%m-%d %H:%M:%S")
        with open(file_path + ".tmp", "w", encoding="utf-8") as f:
            f.write(f"# Last updated: {beijing_time} | Total nodes: {len(all_uris)}\n")
            for uri in all_uris: f.write(uri + "\n")
        os.replace(file_path + ".tmp", file_path)

    def save_sources(self):
        with open(SOURCE_HISTORY_FILE + ".tmp", "w", encoding="utf-8", newline='') as f:
            writer = csv.writer(f)
            for url in sorted(self.source_urls): writer.writerow([url])
        os.replace(SOURCE_HISTORY_FILE + ".tmp", SOURCE_HISTORY_FILE)

manager = NodeManager()
stats_lock, api_semaphore = threading.Lock(), threading.Semaphore(12)
stats_data = {}

def get_session():
    if not hasattr(thread_local, "session"):
        session = requests.Session()
        session.mount("https://", HTTPAdapter(pool_connections=12, pool_maxsize=12, max_retries=Retry(total=3, backoff_factor=1, status_forcelist=[429, 500, 502, 503, 504])))
        if TOKEN: session.headers.update({"Authorization": f"Bearer {TOKEN}"})
        thread_local.session = session
    return thread_local.session

def score_nodes(count, url):
    return (10 if count <= 2 else 5 if count <= 10 else 1) + (1 if "gist" in url else 0)

# 还原回原有的 Hash 逻辑，避免过滤掉已有节点
def core_hash(uri):
    if not uri or "://" not in uri: return None
    uri = uri.replace("hy2://", "hysteria2://")
    parsed = urlsplit(uri)
    normalized = f"{parsed.scheme.lower()}://{parsed.hostname or ''}:{parsed.port or (443 if parsed.scheme.lower() == 'vless' else 0)}"
    return hashlib.md5(normalized.encode()).hexdigest()

def extract_nodes(text, depth=0):
    if not text or ("://" not in text and "base64" not in text.lower()): return []
    if len(text) < 20: return []
    found = []
    if depth < MAX_RECURSION:
        b64_matches = re.findall(r'(?:[A-Za-z0-9+/]{4}){10,}', text)
        for b64 in b64_matches[:50]:
            with memo_lock:
                if b64 in memo_b64: continue
                memo_b64[b64] = True
                if len(memo_b64) > MAX_MEMO_B64: memo_b64.popitem(last=False)
            try:
                decoded = base64.b64decode(b64 + '=' * (-len(b64) % 4)).decode('utf-8', errors='ignore')
                if "://" in decoded: found.extend(extract_nodes(decoded, depth + 1))
            except: pass
    for _, pattern in PROTO_PATTERNS.items():
        found.extend([m for m in pattern.findall(text) if len(m) >= 20 and "://" in m])
    return found[:MAX_PER_LAYER]

def process_raw(raw_url):
    with api_semaphore:
        try:
            r = get_session().get(raw_url, timeout=TIMEOUT)
            if r.status_code == 200 and len(r.text) < MAX_TEXT_SIZE:
                nodes = extract_nodes(r.text)
                return raw_url, nodes, len(nodes)
        except: pass
        return raw_url, [], 0

def main():
    manager.load_from_file(ALL_NODES_FILE, is_temp=False)
    manager.load_from_file(TEMP_LOG_FILE, is_temp=True)
    manager.load_sources()
    urls_to_scan = set()
    for page in range(1, config["settings"].get("gist_pages", 50) + 1):
        try:
            resp = get_session().get(f"https://api.github.com/gists/public?page={page}&per_page=100", timeout=TIMEOUT)
            if resp.status_code == 200:
                for gist in resp.json():
                    desc = (gist.get("description") or "").lower()
                    owner = gist.get("owner", {}).get("login", "").lower()
                    if owner not in EXCLUDE_OWNERS:
                        files = gist.get("files", {})
                        if any(k in desc for k in SEARCH_EXCLUDE): continue
                        if SEARCH_INCLUDE:
                            if not any(k in desc for k in SEARCH_INCLUDE) and not any(any(k in f.lower() for k in SEARCH_INCLUDE) for f in files): continue
                        for f_info in files.values():
                            raw = f_info.get("raw_url")
                            fn = f_info.get("filename", "").lower()
                            if raw and not (fn in EXCLUDE_EQUALS or any(k in fn for k in EXCLUDE_CONTAINS)): urls_to_scan.add(raw)
        except: continue
    active_urls_found = []
    with ThreadPoolExecutor(max_workers=12) as executor:
        futures = [executor.submit(process_raw, url) for url in urls_to_scan]
        for future in as_completed(futures):
            url, result, count = future.result()
            if count > 0:
                manager.add_source(url)
                active_urls_found.append(url)
                with stats_lock: stats_data[url] = count
                score = score_nodes(count, url)
                for node in result: manager.add_node(node, is_temp=(score >= 8))
    manager.save_to_file(ALL_NODES_FILE, is_temp=False)
    manager.save_to_file(TEMP_LOG_FILE, is_temp=True)
    manager.save_to_dat(ALL_NODES_DAT)
    manager.save_sources()
    print(f"Success! Total nodes: {len(manager.nodes) + len(manager.temp_nodes)}. Sources: {len(manager.source_urls)}")

if __name__ == "__main__":
    main()
