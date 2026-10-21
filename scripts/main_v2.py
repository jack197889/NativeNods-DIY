#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
免费节点自动测活订阅池 v3 — 全协议 · 真实测活 · 家宽/原生精选（修复版）
=====================================================================

流程：
  1. 抓取订阅源 → 解析 vless / vmess / trojan / ss / hysteria2 / tuic / anytls
     （完整保留 传输层 / TLS / Reality 等参数，测试与导出使用同一份配置）
  2. 去重 → DNS 解析 + TCP 端口预检（并发）
  3. sing-box 真实测活：本地 SOCKS 入站 → 节点出站 → generate_204（要求返回 204）
     顺带取出口 IP；可选限时测速（ENABLE_SPEED_TEST=1）
  4. 分类：
       - 国家：出口 IP 的 GeoLite2-Country
       - 原生 IP：GeoLite2 的「使用地国家」== 「注册地国家」（与检测网站的定义一致）
       - 家宽 / 机房：ip-api(hosting/mobile) + ASN 名称关键词
  5. 导出：v2ray(base64) / Clash / sing-box，总表 + 按国家，并更新 README

规则：家宽、原生节点全部保留；普通节点保留延迟最低的 MAX_NORMAL(默认 50) 个。

依赖：pip install -r requirements.txt   (requests[socks]  PyYAML  maxminddb)

可用环境变量（均可选）：
  SINGBOX_BIN / SINGBOX_VERSION   指定内核路径 / 版本
  MAX_WORKERS_TEST                测活并发（默认 48）
  MAX_CANDIDATES                  最多测试多少个节点（默认 5000，0=不限）
  MAX_NORMAL / MAX_NATIVE / MAX_RESIDENTIAL   各类保留上限（0=不限）
  ENABLE_SPEED_TEST=1             开启限时测速
  DROP_INSECURE=1                 丢弃「跳过证书验证」的节点
  DEBUG=1                         打印更多排查信息
"""

from __future__ import annotations

import base64
import collections
import html
import ipaddress
import json
import os
import platform
import random
import re
import shutil
import socket
import subprocess
import sys
import tarfile
import threading
import time
import urllib.parse
import uuid
import zipfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone

try:
    import requests
    import yaml
    import socks  # noqa: F401  (PySocks：requests 使用 socks5h 代理时必需)
except ImportError as _e:
    print(f"[!] 缺少依赖: {_e}\n    请先执行: pip install -r requirements.txt "
          f"(需要 requests[socks] / PyYAML / maxminddb)")
    sys.exit(1)

try:
    import maxminddb
except ImportError:  # 没有也能跑，只是分类精度下降
    maxminddb = None

try:
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
except Exception:
    pass


# ══════════════════════════════════════════════════════════════════
# 配置
# ══════════════════════════════════════════════════════════════════

def _env_int(name: str, default: int) -> int:
    try:
        return int((os.environ.get(name) or "").strip() or default)
    except ValueError:
        return default


def _env_flag(name: str, default: bool = False) -> bool:
    v = os.environ.get(name)
    if v is None:
        return default
    return v.strip().lower() in ("1", "true", "yes", "on")


SOURCE_URLS = [
    "https://cdn.jsdelivr.net/gh/free18/v2ray@main/v.txt",
    "https://raw.githubusercontent.com/freefq/free/master/v2",
    "https://www.ermao.net/sub/v2ray/ermao.net",
    "https://raw.githubusercontent.com/Au1rxx/free-vpn-subscriptions/main/output/v2ray-base64.txt",
    "https://raw.githubusercontent.com/Au1rxx/free-vpn-subscriptions/main/output/by-country/v2ray-base64-JP.txt",
    "https://raw.githubusercontent.com/Au1rxx/free-vpn-subscriptions/main/output/by-country/v2ray-base64-US.txt",
    "https://raw.githubusercontent.com/Au1rxx/free-vpn-subscriptions/main/output/by-country/v2ray-base64-NL.txt",
    "https://raw.githubusercontent.com/Au1rxx/free-vpn-subscriptions/main/output/by-country/v2ray-base64-HK.txt",
    "https://raw.githubusercontent.com/Au1rxx/free-vpn-subscriptions/main/output/by-country/v2ray-base64-TW.txt",
    "https://raw.githubusercontent.com/Au1rxx/free-vpn-subscriptions/main/output/by-country/v2ray-base64-AU.txt",
    "https://raw.githubusercontent.com/10ium/HiN-VPN/main/subscription/base64/mix",
    "https://raw.githubusercontent.com/10ium/HiN-VPN/main/subscription/base64/hysteria2",
    "https://raw.githubusercontent.com/0xRadikal/Free-v2ray-Configs/main/verified/configs_base64.txt",
    "https://raw.githubusercontent.com/yy1588133/proxy-pool/main/v2ray.txt",
    "https://raw.githubusercontent.com/Pawdroid/Free-servers/main/sub",
    "https://sub.445569.xyz/",
]

# 路径：脚本放在 <repo>/scripts/ 下时，输出到 <repo>/output
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
BASEDIR = (os.path.dirname(SCRIPT_DIR)
           if os.path.basename(SCRIPT_DIR).lower() == "scripts" else SCRIPT_DIR)
OUTPUT_DIR = os.path.join(BASEDIR, "output")
COUNTRY_DIR = os.path.join(OUTPUT_DIR, "by-country")
RESIDENTIAL_COUNTRY_DIR = os.path.join(OUTPUT_DIR, "residential-by-country")
NATIVE_COUNTRY_DIR = os.path.join(OUTPUT_DIR, "native-by-country")
RUNTIME_DIR = os.path.join(BASEDIR, "runtime")

IS_WINDOWS = os.name == "nt"
SINGBOX_VERSION = os.environ.get("SINGBOX_VERSION", "v1.14.0").strip() or "v1.14.0"
SINGBOX_LOCAL = os.path.join(RUNTIME_DIR, "sing-box" + (".exe" if IS_WINDOWS else ""))

GEO_COUNTRY_DB = os.path.join(RUNTIME_DIR, "Country.mmdb")
GEO_ASN_DB = os.path.join(RUNTIME_DIR, "ASN.mmdb")
GEO_DB_MAX_AGE_DAYS = 3
GEO_DB_URLS = {
    "GeoLite2-Country.mmdb": [
        "https://github.com/P3TERX/GeoLite.mmdb/raw/download/GeoLite2-Country.mmdb",
        "https://raw.githubusercontent.com/P3TERX/GeoLite.mmdb/download/GeoLite2-Country.mmdb",
        "https://cdn.jsdelivr.net/gh/P3TERX/GeoLite.mmdb@download/GeoLite2-Country.mmdb",
    ],
    "GeoLite2-ASN.mmdb": [
        "https://github.com/P3TERX/GeoLite.mmdb/raw/download/GeoLite2-ASN.mmdb",
        "https://raw.githubusercontent.com/P3TERX/GeoLite.mmdb/download/GeoLite2-ASN.mmdb",
        "https://cdn.jsdelivr.net/gh/P3TERX/GeoLite.mmdb@download/GeoLite2-ASN.mmdb",
    ],
}

# 超时与并发
PORT_KNOCK_TIMEOUT = 2.0
SINGBOX_START_TIMEOUT = 5.0
PROBE_TIMEOUT = 8
LIVENESS_BUDGET = 14.0          # 单节点测活总预算(秒)
IP_ECHO_TIMEOUT = 6.0
MAX_WORKERS_FETCH = 8
MAX_WORKERS_PREFILTER = 128
MAX_WORKERS_TEST = _env_int("MAX_WORKERS_TEST", 48)
MAX_CANDIDATES = _env_int("MAX_CANDIDATES", 5000)

# 测速（默认关闭）
ENABLE_SPEED_TEST = _env_flag("ENABLE_SPEED_TEST", False)
SPEED_TEST_BYTES = 2_500_000
SPEED_TEST_BUDGET = 4.0
SPEED_MIN_BYTES_PER_S = 70_000

# 精选规则
MAX_NORMAL = _env_int("MAX_NORMAL", 50)
MAX_NATIVE = _env_int("MAX_NATIVE", 0)
MAX_RESIDENTIAL = _env_int("MAX_RESIDENTIAL", 0)
DEDUP_BY_EXIT_IP = True         # 相同出口 IP 只保留延迟最低的一个
DROP_INSECURE = _env_flag("DROP_INSECURE", False)
ALLOW_INSECURE_DEFAULT = False  # 订阅链接没写 insecure 时，是否默认跳过证书验证
ENABLE_IP_API = _env_flag("ENABLE_IP_API", True)
DEBUG = _env_flag("DEBUG", False)
NAME_SUFFIX = "xiaohe"

LIVENESS_URLS = [
    "https://www.gstatic.com/generate_204",
    "https://www.google.com/generate_204",
    "https://cp.cloudflare.com/generate_204",
]
IP_ECHO_URLS = [
    "https://www.cloudflare.com/cdn-cgi/trace",
    "https://api.ip.sb/geoip",
    "https://ipinfo.io/json",
    "http://ip-api.com/json/?fields=status,query,countryCode",
]
SPEED_TEST_URLS = [
    "https://speed.cloudflare.com/__down?bytes=" + str(SPEED_TEST_BYTES),
    "https://cachefly.cachefly.net/10mb.test",
]

IP_API_BATCH_URL = ("http://ip-api.com/batch?fields="
                    "status,message,countryCode,isp,org,as,asname,mobile,proxy,hosting,query")
IP_API_BATCH_SIZE = 100
IP_API_BATCH_INTERVAL = 4.2     # 免费版 15 次/分钟
IP_API_MAX_IPS = 3000

USER_AGENT = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
              "(KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36")

UDP_PROTOS = ("hysteria2", "tuic")

# 机房 / ISP 关键词（只在 ip-api 不可用、或作为补充时使用）
IDC_RE = re.compile(
    r"(hosting|datacenter|data center|data centre|\bidc\b|\bvps\b|\bcloud|server|colo|dedicated|"
    r"amazon|\baws\b|google|microsoft|azure|digitalocean|linode|akamai|vultr|choopa|\bovh|hetzner|"
    r"leaseweb|oracle|alibaba|aliyun|tencent|huawei|cloudflare|contabo|m247|datacamp|quadranet|"
    r"psychz|colocrossing|zenlayer|gcore|dmit|bandwagon|racknerd|hostwinds|kamatera|scaleway|"
    r"ionos|upcloud|rackspace|softlayer|ucloud|oneprovider|frantech|buyvm|cdn77|fastly|equinix|"
    r"sharktech|clouvider|multacom|virmach)", re.I)
ISP_RE = re.compile(
    r"(broadband|pppoe|\bdsl\b|\bcable\b|fiber|fibre|ftth|residential|telecom|telekom|comcast|"
    r"spectrum|verizon|at&t|vodafone|softbank|\bocn\b|chunghwa|hinet|hkbn|pccw|\bhkt\b|singtel|"
    r"starhub|\bntt\b|kddi|rakuten|rogers|telus|charter|centurylink|telstra|optus|orange|"
    r"bouygues|kt corp|sk broadband|lg uplus|china unicom|china mobile)", re.I)

COUNTRY_NAMES = {
    "HK": "中国香港 (Hong Kong)", "TW": "中国台湾 (Taiwan)", "MO": "中国澳门 (Macao)",
    "CN": "中国大陆 (China)", "JP": "日本 (Japan)", "SG": "新加坡 (Singapore)",
    "US": "美国 (United States)", "KR": "韩国 (South Korea)", "DE": "德国 (Germany)",
    "GB": "英国 (United Kingdom)", "CA": "加拿大 (Canada)", "FR": "法国 (France)",
    "NL": "荷兰 (Netherlands)", "AU": "澳大利亚 (Australia)", "IN": "印度 (India)",
    "RU": "俄罗斯 (Russia)", "TR": "土耳其 (Turkey)", "BR": "巴西 (Brazil)",
    "ID": "印度尼西亚 (Indonesia)", "TH": "泰国 (Thailand)", "VN": "越南 (Vietnam)",
    "MY": "马来西亚 (Malaysia)", "PH": "菲律宾 (Philippines)", "AR": "阿根廷 (Argentina)",
    "IT": "意大利 (Italy)", "ES": "西班牙 (Spain)", "SE": "瑞典 (Sweden)",
    "CH": "瑞士 (Switzerland)", "PL": "波兰 (Poland)", "UA": "乌克兰 (Ukraine)",
    "FI": "芬兰 (Finland)", "IE": "爱尔兰 (Ireland)", "MX": "墨西哥 (Mexico)",
    "ZA": "南非 (South Africa)", "AE": "阿联酋 (UAE)", "IL": "以色列 (Israel)",
    "RO": "罗马尼亚 (Romania)", "BG": "保加利亚 (Bulgaria)", "NO": "挪威 (Norway)",
    "DK": "丹麦 (Denmark)", "AT": "奥地利 (Austria)", "CZ": "捷克 (Czechia)",
    "OTHER": "其他地区 (Other)",
}

DIRECT_SESSION = requests.Session()
DIRECT_SESSION.trust_env = True
DIRECT_SESSION.headers.update({"User-Agent": USER_AGENT, "Accept": "*/*"})

STATS = collections.Counter()
START_ERRORS = collections.Counter()
_STATS_LOCK = threading.Lock()


def bump(key: str, n: int = 1):
    with _STATS_LOCK:
        STATS[key] += n


# ══════════════════════════════════════════════════════════════════
# 通用工具
# ══════════════════════════════════════════════════════════════════

def get_country_flag(country_code: str) -> str:
    cc = (country_code or "").upper()
    if len(cc) == 2 and cc.isalpha() and cc.isascii() and cc not in ("ZZ", "XX", "T1", "A1", "A2"):
        return chr(ord(cc[0]) + 127397) + chr(ord(cc[1]) + 127397)
    return "🌐"


def b64_decode(data: str) -> str:
    """同时兼容标准 / URL-safe base64、缺失填充、夹杂换行空格。失败返回空串。"""
    data = re.sub(r"\s+", "", data or "")
    if not data:
        return ""
    data = data.replace("-", "+").replace("_", "/")
    data += "=" * (-len(data) % 4)
    try:
        return base64.b64decode(data).decode("utf-8", errors="ignore")
    except Exception:
        return ""


def is_ip_literal(host: str) -> bool:
    try:
        ipaddress.ip_address((host or "").strip().strip("[]"))
        return True
    except ValueError:
        return False


def is_public_ip(ip: str) -> bool:
    try:
        return ipaddress.ip_address(ip).is_global
    except ValueError:
        return False


def _truthy(v) -> bool:
    return str(v).strip().lower() in ("1", "true", "yes", "on")


def write_text(path: str, text: str):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)
    os.replace(tmp, path)


def write_sub(path: str, links: list):
    write_text(path, base64.b64encode("\n".join(links).encode("utf-8")).decode())


def remove_path(path: str):
    try:
        if os.path.isdir(path):
            shutil.rmtree(path, ignore_errors=True)
        elif os.path.exists(path):
            os.remove(path)
    except OSError:
        pass


def ensure_directories():
    for d in (OUTPUT_DIR, COUNTRY_DIR, RESIDENTIAL_COUNTRY_DIR, NATIVE_COUNTRY_DIR, RUNTIME_DIR):
        os.makedirs(d, exist_ok=True)


def download_file(urls, dest: str, timeout: int = 120, retries: int = 2, min_size: int = 1024):
    """依次尝试多个镜像地址，下载成功后原子替换 dest。"""
    if isinstance(urls, str):
        urls = [urls]
    tmp = dest + ".part"
    last_err = None
    for url in urls:
        for attempt in range(retries):
            try:
                with DIRECT_SESSION.get(url, timeout=(10, timeout), stream=True) as r:
                    r.raise_for_status()
                    with open(tmp, "wb") as f:
                        for chunk in r.iter_content(chunk_size=1 << 20):
                            if chunk:
                                f.write(chunk)
                if os.path.getsize(tmp) < min_size:
                    raise RuntimeError("下载的文件过小")
                os.replace(tmp, dest)
                return
            except Exception as e:  # noqa: BLE001
                last_err = e
                time.sleep(1.5)
    remove_path(tmp)
    raise RuntimeError(f"下载失败: {urls[0]} ({last_err})")


# ══════════════════════════════════════════════════════════════════
# 环境准备：sing-box 内核 + GeoLite2
# ══════════════════════════════════════════════════════════════════

_SINGBOX_EXE = None


def _singbox_platform():
    sysname = {"Windows": "windows", "Darwin": "darwin", "Linux": "linux"}.get(platform.system(), "linux")
    mach = platform.machine().lower()
    arch = "arm64" if mach in ("arm64", "aarch64") else "amd64"
    return sysname, arch


def _extract_singbox(archive: str, ext: str, dest_exe: str):
    target = "sing-box.exe" if ext == "zip" else "sing-box"
    if ext == "zip":
        with zipfile.ZipFile(archive) as z:
            for info in z.infolist():
                if not info.is_dir() and os.path.basename(info.filename) == target:
                    with z.open(info) as src, open(dest_exe, "wb") as dst:
                        shutil.copyfileobj(src, dst)
                    return
    else:
        with tarfile.open(archive) as t:
            for m in t.getmembers():
                if m.isfile() and os.path.basename(m.name) == target:
                    src = t.extractfile(m)
                    with open(dest_exe, "wb") as dst:
                        shutil.copyfileobj(src, dst)
                    return
    raise RuntimeError("压缩包内没有找到 sing-box 可执行文件")


def _latest_singbox_version() -> str:
    try:
        r = DIRECT_SESSION.get("https://api.github.com/repos/SagerNet/sing-box/releases/latest", timeout=15)
        if r.status_code == 200:
            return r.json().get("tag_name", "")
    except Exception:  # noqa: BLE001
        pass
    return ""


def install_singbox() -> str:
    sysname, arch = _singbox_platform()
    ext = "zip" if sysname == "windows" else "tar.gz"
    versions = [SINGBOX_VERSION]
    tried_latest = False
    last_err = None
    while versions:
        ver = versions.pop(0)
        v = ver.lstrip("v")
        suffixes = [""] + (["-glibc", "-musl"] if sysname == "linux" else [])
        for suf in suffixes:
            url = (f"https://github.com/SagerNet/sing-box/releases/download/v{v}/"
                   f"sing-box-{v}-{sysname}-{arch}{suf}.{ext}")
            archive = os.path.join(RUNTIME_DIR, f"sing-box.{ext}")
            try:
                print(f"[*] 下载 sing-box v{v} ({sysname}-{arch}{suf}) ...")
                download_file(url, archive, timeout=300, retries=2, min_size=100_000)
                _extract_singbox(archive, ext, SINGBOX_LOCAL)
                os.chmod(SINGBOX_LOCAL, 0o755)
                remove_path(archive)
                return SINGBOX_LOCAL
            except Exception as e:  # noqa: BLE001
                last_err = e
                remove_path(archive)
        if not versions and not tried_latest:
            tried_latest = True
            latest = _latest_singbox_version()
            if latest and latest.lstrip("v") != v:
                print(f"[!] {ver} 下载失败，改用最新版 {latest}")
                versions.append(latest)
    raise RuntimeError(f"无法获取 sing-box: {last_err}")


def find_singbox() -> str:
    env = os.environ.get("SINGBOX_BIN")
    if env and os.path.isfile(env):
        return env
    if os.path.isfile(SINGBOX_LOCAL) and os.path.getsize(SINGBOX_LOCAL) > 1024:
        return SINGBOX_LOCAL
    which = shutil.which("sing-box")
    if which:
        return which
    return install_singbox()


def ensure_geo_db(name: str, dest: str):
    """没有则下载；超过 GEO_DB_MAX_AGE_DAYS 天则尝试更新，更新失败沿用旧文件。"""
    exists = os.path.exists(dest) and os.path.getsize(dest) > 100_000
    if exists:
        age_days = (time.time() - os.path.getmtime(dest)) / 86400
        if age_days < GEO_DB_MAX_AGE_DAYS:
            return
    try:
        download_file(GEO_DB_URLS[name], dest, timeout=120, retries=2, min_size=100_000)
        print(f"[+] 已更新 {name}")
    except Exception as e:  # noqa: BLE001
        if exists:
            print(f"[!] {name} 更新失败，沿用旧文件 ({e})")
        else:
            print(f"[!] {name} 下载失败，将降级分类 ({e})")


def setup_environment():
    global _SINGBOX_EXE
    print("[*] 准备 sing-box 内核与 GeoLite2 离线数据库 ...")
    os.makedirs(RUNTIME_DIR, exist_ok=True)
    _SINGBOX_EXE = find_singbox()
    try:
        out = subprocess.run([_SINGBOX_EXE, "version"], capture_output=True, text=True, timeout=15)
        first = (out.stdout or out.stderr or "").strip().splitlines()
        print(f"[+] 内核: {_SINGBOX_EXE} | {first[0] if first else '?'}")
        if out.returncode != 0:
            raise RuntimeError("sing-box version 返回非 0")
    except Exception as e:  # noqa: BLE001
        print(f"[!] sing-box 无法运行: {e}")
        sys.exit(1)
    ensure_geo_db("GeoLite2-Country.mmdb", GEO_COUNTRY_DB)
    ensure_geo_db("GeoLite2-ASN.mmdb", GEO_ASN_DB)


# ══════════════════════════════════════════════════════════════════
# 节点解析：URI → sing-box outbound（完整保留 TLS / Reality / 传输层）
# 解析失败或遇到不支持的特性统一抛 ValueError
# ══════════════════════════════════════════════════════════════════

UTLS_FPS = {"chrome", "firefox", "edge", "safari", "360", "qq", "ios", "android", "random", "randomized"}
SS_METHODS = {
    "2022-blake3-aes-128-gcm", "2022-blake3-aes-256-gcm", "2022-blake3-chacha20-poly1305",
    "aes-128-gcm", "aes-192-gcm", "aes-256-gcm",
    "chacha20-ietf-poly1305", "xchacha20-ietf-poly1305",
}
SS_METHOD_ALIAS = {"chacha20-poly1305": "chacha20-ietf-poly1305",
                   "xchacha20-poly1305": "xchacha20-ietf-poly1305"}
VMESS_SECURITY = {"auto", "aes-128-gcm", "chacha20-poly1305", "none", "zero"}
HOST_PORT_RE = re.compile(r"^(\[[^\]]+\]|[^:\[\]]+)(?::(\d+))?")


def parse_host_port(hostinfo: str):
    """'host:443' / '[::1]:443' / 'host:443,5000-6000' → (host, port)；IPv6 去掉方括号。"""
    m = HOST_PORT_RE.match((hostinfo or "").strip())
    if not m:
        return "", 0
    host = m.group(1)
    if host.startswith("["):
        host = host[1:-1]
    return host, int(m.group(2)) if m.group(2) else 0


def _query_dict(query: str) -> dict:
    out = {}
    for pair in (query or "").split("&"):
        if not pair:
            continue
        k, _, v = pair.partition("=")
        out[urllib.parse.unquote(k).lower()] = urllib.parse.unquote(v)
    return out


def split_uri(uri: str):
    scheme, sep, rest = uri.partition("://")
    if not sep:
        return None
    rest, _, frag = rest.partition("#")
    rest, _, query = rest.partition("?")
    authority = rest.split("/", 1)[0]
    userinfo, at, hostport = authority.rpartition("@")
    host, port = parse_host_port(hostport)
    if not host:
        return None
    return {
        "scheme": scheme.lower(),
        "userinfo": urllib.parse.unquote(userinfo) if at else "",
        "has_at": bool(at),
        "host": host,
        "port": port,
        "params": _query_dict(query),
        "frag": urllib.parse.unquote(frag),
    }


def _first(params: dict, *keys):
    for k in keys:
        if k in params and params[k] != "":
            return params[k]
    return None


def _norm_uuid(s: str) -> str:
    try:
        return str(uuid.UUID(str(s).strip()))
    except ValueError:
        raise ValueError("invalid uuid")


def _default_host(sni: str, server: str) -> str:
    return sni or ("" if is_ip_literal(server) else server)


def build_tls(params: dict, host: str, reality: bool = False, default_alpn=None,
              insecure_default: bool = ALLOW_INSECURE_DEFAULT) -> dict:
    sni = (_first(params, "sni", "peer", "servername") or "").strip()
    if not sni and not is_ip_literal(host):
        sni = host
    tls = {"enabled": True}
    if sni:
        tls["server_name"] = sni
    alpn = [x.strip() for x in (params.get("alpn") or "").split(",") if x.strip()] or default_alpn
    if alpn:
        tls["alpn"] = list(alpn)
    fp = (params.get("fp") or "").lower()
    if reality:
        pbk = params.get("pbk", "")
        sid = params.get("sid", "")
        if not pbk or not re.fullmatch(r"[0-9a-fA-F]{0,16}", sid):
            raise ValueError("invalid reality params")
        tls["utls"] = {"enabled": True, "fingerprint": fp if fp in UTLS_FPS else "chrome"}
        tls["reality"] = {"enabled": True, "public_key": pbk, "short_id": sid}
    else:
        ins = _first(params, "allowinsecure", "insecure", "allow_insecure", "skip-cert-verify")
        tls["insecure"] = _truthy(ins) if ins is not None else insecure_default
        if fp in UTLS_FPS:
            tls["utls"] = {"enabled": True, "fingerprint": fp}
    return tls


def build_transport(net: str, path: str = "", host: str = "", service_name: str = "",
                    header_type: str = "", default_host: str = ""):
    net = (net or "tcp").lower()
    if net in ("tcp", "raw", ""):
        if header_type and header_type.lower() not in ("none", ""):
            raise ValueError("tcp http-obfs unsupported")
        return None
    host = (host or "").strip()
    if net == "ws":
        t = {"type": "ws"}
        p = path or "/"
        m = re.search(r"[?&]ed=(\d+)", p)
        if m:
            t["max_early_data"] = int(m.group(1))
            t["early_data_header_name"] = "Sec-WebSocket-Protocol"
            p = re.sub(r"([?&])ed=\d+&?", r"\1", p).rstrip("?&") or "/"
        t["path"] = p
        h = host or default_host
        if h:
            t["headers"] = {"Host": h}
        return t
    if net == "grpc":
        return {"type": "grpc", "service_name": service_name or path or ""}
    if net in ("h2", "http"):
        t = {"type": "http", "path": path or "/"}
        hosts = [x.strip() for x in (host or default_host).split(",") if x.strip()]
        if hosts:
            t["host"] = hosts
        return t
    if net == "httpupgrade":
        t = {"type": "httpupgrade", "path": path or "/"}
        h = host or default_host
        if h:
            t["host"] = h
        return t
    raise ValueError(f"unsupported transport: {net}")


def _need_authority(u):
    if not u or not u["has_at"] or not u["userinfo"]:
        raise ValueError("bad uri")
    return u


def parse_vless(uri: str):
    u = _need_authority(split_uri(uri))
    host, port, p = u["host"], u["port"], u["params"]
    ob = {"type": "vless", "tag": "node", "server": host, "server_port": port,
          "uuid": _norm_uuid(u["userinfo"])}
    if p.get("encryption", "none").lower() not in ("none", ""):
        raise ValueError("vless encryption unsupported")
    flow = p.get("flow", "")
    if flow:
        if not flow.startswith("xtls-rprx-vision"):
            raise ValueError("flow unsupported")
        ob["flow"] = "xtls-rprx-vision"
    sec = p.get("security", "").lower()
    if sec == "reality":
        ob["tls"] = build_tls(p, host, reality=True)
    elif sec in ("tls", "xtls"):
        ob["tls"] = build_tls(p, host)
    elif sec not in ("", "none"):
        raise ValueError("security unsupported")
    sni = ob.get("tls", {}).get("server_name", "")
    tr = build_transport(p.get("type", "tcp"), p.get("path", ""), p.get("host", ""),
                         p.get("servicename", ""), p.get("headertype", ""),
                         _default_host(sni, host))
    if tr:
        ob["transport"] = tr
    if p.get("packetencoding", "").lower() in ("xudp", "packetaddr"):
        ob["packet_encoding"] = p["packetencoding"].lower()
    return ob


def _vmess_from_json(data: dict):
    server = str(data.get("add", "")).strip()
    port = int(str(data.get("port", "0")).strip() or 0)
    if not server or port <= 0:
        raise ValueError("bad vmess")
    scy = str(data.get("scy", "") or "auto").lower()
    if scy not in VMESS_SECURITY:
        scy = "auto"
    ob = {"type": "vmess", "tag": "node", "server": server, "server_port": port,
          "uuid": _norm_uuid(data.get("id", "")), "security": scy}
    aid = int(str(data.get("aid", "0") or 0))
    if aid > 0:
        ob["alter_id"] = aid
    net = str(data.get("net", "tcp") or "tcp").lower()
    host_h = str(data.get("host", "") or "").strip()
    path = str(data.get("path", "") or "")
    sni = str(data.get("sni", "") or "").strip() or host_h.split(",")[0].strip()
    if str(data.get("tls", "")).lower() in ("tls", "1", "true"):
        ob["tls"] = build_tls({
            "sni": sni, "alpn": str(data.get("alpn", "") or ""), "fp": str(data.get("fp", "") or ""),
            "allowinsecure": str(data.get("allowInsecure", data.get("insecure", "")) or ""),
        }, server)
    tr = build_transport(net, path, host_h, path,
                         str(data.get("type", "") or "") if net == "tcp" else "",
                         _default_host(ob.get("tls", {}).get("server_name", ""), server))
    if tr:
        ob["transport"] = tr
    return ob


def _vmess_from_url(uri: str):
    u = _need_authority(split_uri(uri))
    host, p = u["host"], u["params"]
    scy = p.get("encryption", "auto").lower()
    ob = {"type": "vmess", "tag": "node", "server": host, "server_port": u["port"],
          "uuid": _norm_uuid(u["userinfo"]), "security": scy if scy in VMESS_SECURITY else "auto"}
    sec = p.get("security", "").lower()
    if sec in ("tls", "xtls"):
        ob["tls"] = build_tls(p, host)
    elif sec not in ("", "none"):
        raise ValueError("security unsupported")
    tr = build_transport(p.get("type", "tcp"), p.get("path", ""), p.get("host", ""),
                         p.get("servicename", ""), p.get("headertype", ""),
                         _default_host(ob.get("tls", {}).get("server_name", ""), host))
    if tr:
        ob["transport"] = tr
    return ob


def parse_vmess(uri: str):
    raw = uri[len("vmess://"):].split("#", 1)[0].strip()
    if "%" in raw:
        raw = urllib.parse.unquote(raw)
    data = None
    if "@" not in raw:
        txt = b64_decode(raw)
        if txt:
            try:
                data = json.loads(txt)
            except ValueError:
                data = None
    if isinstance(data, dict):
        return _vmess_from_json(data)
    return _vmess_from_url(uri)


def parse_trojan(uri: str):
    u = _need_authority(split_uri(uri))
    host, p = u["host"], u["params"]
    ob = {"type": "trojan", "tag": "node", "server": host, "server_port": u["port"],
          "password": u["userinfo"]}
    sec = p.get("security", "tls").lower() or "tls"
    if sec == "reality":
        ob["tls"] = build_tls(p, host, reality=True)
    elif sec in ("tls", "xtls"):
        ob["tls"] = build_tls(p, host)
    elif sec != "none":
        raise ValueError("security unsupported")
    tr = build_transport(p.get("type", "tcp"), p.get("path", ""), p.get("host", ""),
                         p.get("servicename", ""), p.get("headertype", ""),
                         _default_host(ob.get("tls", {}).get("server_name", ""), host))
    if tr:
        ob["transport"] = tr
    return ob


def parse_ss(uri: str):
    body = uri[len("ss://"):]
    body, _, _frag = body.partition("#")
    body, _, query = body.partition("?")
    if "plugin" in _query_dict(query):
        raise ValueError("ss plugin unsupported")
    if "@" in body:                                   # SIP002 或明文
        userinfo, _, hostinfo = body.rstrip("/").rpartition("@")
        hostinfo = hostinfo.split("/")[0]
        ui = urllib.parse.unquote(userinfo)
        if ":" not in ui:
            ui = b64_decode(ui)
        if ":" not in ui:
            raise ValueError("bad ss userinfo")
        method, _, password = ui.partition(":")
    else:                                             # 旧格式 base64(method:pass@host:port)
        dec = b64_decode(urllib.parse.unquote(body))
        if "@" not in dec:
            raise ValueError("bad ss")
        userinfo, _, hostinfo = dec.rpartition("@")
        method, _, password = userinfo.partition(":")
    host, port = parse_host_port(hostinfo)
    method = SS_METHOD_ALIAS.get(method.lower(), method.lower())
    if not host or port <= 0 or method not in SS_METHODS or not password:
        raise ValueError("bad ss")
    return {"type": "shadowsocks", "tag": "node", "server": host, "server_port": port,
            "method": method, "password": password}


def parse_hysteria2(uri: str):
    u = _need_authority(split_uri(uri))
    host, p = u["host"], u["params"]
    ob = {"type": "hysteria2", "tag": "node", "server": host,
          "server_port": u["port"] or 443, "password": u["userinfo"],
          "tls": build_tls(p, host)}
    obfs = p.get("obfs", "").lower()
    if obfs:
        if obfs != "salamander":
            raise ValueError("obfs unsupported")
        ob["obfs"] = {"type": "salamander", "password": p.get("obfs-password", "")}
    return ob


def parse_tuic(uri: str):
    u = _need_authority(split_uri(uri))
    host, p = u["host"], u["params"]
    uid, _, pw = u["userinfo"].partition(":")
    if not pw:
        raise ValueError("tuic v4 unsupported")
    ob = {"type": "tuic", "tag": "node", "server": host, "server_port": u["port"],
          "uuid": _norm_uuid(uid), "password": pw,
          "tls": build_tls(p, host, default_alpn=["h3"])}
    cc = p.get("congestion_control", "").lower()
    if cc in ("cubic", "new_reno", "bbr"):
        ob["congestion_control"] = cc
    if p.get("udp_relay_mode", "").lower() in ("native", "quic"):
        ob["udp_relay_mode"] = p["udp_relay_mode"].lower()
    return ob


def parse_anytls(uri: str):
    u = _need_authority(split_uri(uri))
    host = u["host"]
    return {"type": "anytls", "tag": "node", "server": host, "server_port": u["port"],
            "password": u["userinfo"], "tls": build_tls(u["params"], host)}


PARSERS = {
    "vless://": parse_vless, "vmess://": parse_vmess, "trojan://": parse_trojan,
    "ss://": parse_ss, "hy2://": parse_hysteria2, "hysteria2://": parse_hysteria2,
    "tuic://": parse_tuic, "anytls://": parse_anytls,
}


def parse_node_uri(uri: str):
    """成功返回 (outbound, server, port, type)，失败返回 None。"""
    for prefix, parser in PARSERS.items():
        if uri.startswith(prefix):
            try:
                out = parser(uri)
                host = str(out.get("server", "")).strip()
                port = int(out.get("server_port", 0))
                if (out and host and not re.search(r"\s", host) and len(host) <= 253
                        and 0 < port < 65536):
                    return out, host, port, out["type"]
            except Exception:  # noqa: BLE001
                pass
            return None
    return None


def node_key(outbound: dict) -> str:
    d = {k: v for k, v in outbound.items() if k != "tag"}
    d["server"] = str(d.get("server", "")).lower()
    return json.dumps(d, sort_keys=True, ensure_ascii=False)


# ══════════════════════════════════════════════════════════════════
# 抓取订阅
# ══════════════════════════════════════════════════════════════════

NODE_RE = re.compile(
    r"(?<![A-Za-z0-9])((?:vmess|vless|trojan|ss|hy2|hysteria2|tuic|anytls)://[^\s\"'<>\\]+)")
SCHEME_HINTS = ("vmess://", "vless://", "trojan://", "ss://", "hy2://", "hysteria2://", "tuic://", "anytls://")


def extract_nodes_from_text(text: str) -> set:
    results = set()
    if not text:
        return results
    probe = text.strip()
    for _ in range(3):
        if any(h in probe for h in SCHEME_HINTS):
            break
        decoded = b64_decode(probe)
        if not decoded or decoded == probe:
            break
        probe = decoded
    if "&amp;" in probe:
        probe = html.unescape(probe)
    for m in NODE_RE.findall(probe):
        m = m.strip().rstrip(",;")
        if len(m) > 12:
            results.add(m)
    return results


def fetch_raw_nodes() -> list:
    nodes = set()
    print(f"[*] 抓取 {len(SOURCE_URLS)} 个订阅源 ...")

    def _fetch(url):
        for _ in range(2):
            try:
                r = DIRECT_SESSION.get(url, timeout=(8, 25))
                if r.status_code == 200:
                    return url, extract_nodes_from_text(r.content.decode("utf-8", errors="ignore"))
            except Exception:  # noqa: BLE001
                time.sleep(1)
        return url, set()

    with ThreadPoolExecutor(MAX_WORKERS_FETCH) as ex:
        for fut in as_completed([ex.submit(_fetch, u) for u in SOURCE_URLS]):
            url, got = fut.result()
            print(f"    {'+' if got else '-'} {len(got):>5}  {url}")
            nodes.update(got)
    print(f"[*] 初始抓取总量: {len(nodes)}")
    return list(nodes)


def build_candidates(raw_list: list) -> list:
    seen, items = set(), []
    for uri in raw_list:
        parsed = parse_node_uri(uri)
        if not parsed:
            bump("parse_fail")
            continue
        outbound, server, port, proto = parsed
        if DROP_INSECURE and (outbound.get("tls") or {}).get("insecure"):
            bump("dropped_insecure")
            continue
        key = node_key(outbound)
        if key in seen:
            bump("duplicate")
            continue
        seen.add(key)
        items.append({"raw": uri, "outbound": outbound, "server": server, "port": port, "proto": proto})
    print(f"[*] 解析成功 {len(items)} | 解析失败/不支持 {STATS['parse_fail']} | 重复 {STATS['duplicate']}")
    return items


# ══════════════════════════════════════════════════════════════════
# 预检（并发 DNS + TCP）
# ══════════════════════════════════════════════════════════════════

_DNS_CACHE = {}


def resolve_host(host: str) -> str:
    host = (host or "").strip()
    if not host:
        return ""
    if is_ip_literal(host):
        return host.strip("[]")
    if host in _DNS_CACHE:
        return _DNS_CACHE[host]
    ip = ""
    for fam in (socket.AF_INET, socket.AF_INET6):
        try:
            ip = socket.getaddrinfo(host, None, fam, socket.SOCK_STREAM)[0][4][0]
            break
        except (OSError, UnicodeError):
            continue
    _DNS_CACHE[host] = ip
    return ip


def _prefilter_one(item):
    ip = resolve_host(item["server"])
    if not ip:
        bump("dns_fail")
        return None
    if not is_public_ip(ip):
        bump("non_public_ip")
        return None
    item = dict(item, ip=ip)
    if item["proto"] in UDP_PROTOS:          # UDP 无法用 TCP 探测，直接放行
        return item
    try:
        with socket.create_connection((ip, item["port"]), timeout=PORT_KNOCK_TIMEOUT):
            return item
    except OSError:
        bump("port_closed")
        return None


def prefilter_candidates(candidates: list) -> list:
    print(f"[*] DNS + 端口预检: {len(candidates)} 个候选 (并发 {MAX_WORKERS_PREFILTER}) ...")
    passed = []
    with ThreadPoolExecutor(MAX_WORKERS_PREFILTER) as ex:
        for fut in as_completed([ex.submit(_prefilter_one, it) for it in candidates]):
            try:
                r = fut.result()
            except Exception:  # noqa: BLE001
                r = None
            if r:
                passed.append(r)
    print(f"[+] 预检通过: {len(passed)} (DNS失败 {STATS['dns_fail']} | 非公网 {STATS['non_public_ip']} "
          f"| 端口不通 {STATS['port_closed']})")
    return passed


# ══════════════════════════════════════════════════════════════════
# 真实测活（sing-box）
# ══════════════════════════════════════════════════════════════════

_PORT_LOCK = threading.Lock()
_USED_PORTS = set()


def _alloc_socks_port() -> int:
    with _PORT_LOCK:
        for _ in range(100):
            with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                s.bind(("127.0.0.1", 0))
                port = s.getsockname()[1]
            if port not in _USED_PORTS:
                _USED_PORTS.add(port)
                return port
    raise RuntimeError("no free port")


def _release_port(port: int):
    with _PORT_LOCK:
        _USED_PORTS.discard(port)


def _parse_ip_echo(text: str):
    ip = cc = None
    text = (text or "").strip()
    try:
        j = json.loads(text)
        if isinstance(j, dict):
            ip = (j.get("ip") or j.get("query") or "").strip()
            cc = j.get("country_code") or j.get("countryCode") or j.get("country") or ""
    except ValueError:
        kv = dict(line.split("=", 1) for line in text.splitlines() if "=" in line)
        ip = kv.get("ip", "").strip()
        cc = kv.get("loc", "")
    if ip:
        try:
            ipaddress.ip_address(ip)
        except ValueError:
            return None, None
    else:
        return None, None
    cc = str(cc or "").strip().upper()
    return ip, (cc if re.fullmatch(r"[A-Z]{2}", cc) else None)


def _measure_speed(sess, proxies) -> float:
    for url in SPEED_TEST_URLS:
        try:
            t0, got = time.time(), 0
            with sess.get(url, proxies=proxies, stream=True, timeout=(6, 6)) as r:
                if r.status_code != 200:
                    continue
                for chunk in r.iter_content(65536):
                    got += len(chunk)
                    if time.time() - t0 >= SPEED_TEST_BUDGET or got >= SPEED_TEST_BYTES:
                        break
            return got / max(time.time() - t0, 0.001)
        except requests.RequestException:
            continue
    return 0.0


def _probe_through(port: int, item: dict):
    proxies = {"http": f"socks5h://127.0.0.1:{port}", "https": f"socks5h://127.0.0.1:{port}"}
    sess = requests.Session()
    sess.trust_env = False
    sess.headers.update({"User-Agent": USER_AGENT})
    try:
        latency, end = None, time.time() + LIVENESS_BUDGET
        for url in LIVENESS_URLS:
            remain = end - time.time()
            if remain <= 1:
                break
            t0 = time.time()
            try:
                r = sess.get(url, proxies=proxies, timeout=min(PROBE_TIMEOUT, remain), allow_redirects=False)
            except requests.RequestException:
                continue
            if r.status_code != 204:         # 劫持 / 门户页会返回 200，不算存活
                continue
            latency = int((time.time() - t0) * 1000)
            try:                              # 复用连接再测一次，更接近真实 RTT
                t1 = time.time()
                r2 = sess.get(url, proxies=proxies, timeout=PROBE_TIMEOUT, allow_redirects=False)
                if r2.status_code == 204:
                    latency = min(latency, int((time.time() - t1) * 1000))
            except requests.RequestException:
                pass
            break
        if latency is None:
            bump("probe_fail")
            return None

        exit_ip = exit_cc = None
        for url in IP_ECHO_URLS:
            try:
                r = sess.get(url, proxies=proxies, timeout=IP_ECHO_TIMEOUT)
                if r.status_code == 200:
                    exit_ip, exit_cc = _parse_ip_echo(r.text)
                    if exit_ip:
                        break
            except requests.RequestException:
                continue

        speed = None
        if ENABLE_SPEED_TEST:
            speed = _measure_speed(sess, proxies)
            if speed < SPEED_MIN_BYTES_PER_S:
                bump("too_slow")
                return None

        return {
            "raw": item["raw"], "outbound": item["outbound"], "server": item["server"],
            "port": item["port"], "proto": item["proto"], "ip": item["ip"],
            "latency_ms": latency, "exit_ip": exit_ip, "exit_country": exit_cc,
            "speed_bps": speed,
        }
    finally:
        sess.close()


def test_single_node(item: dict):
    ob = dict(item["outbound"])
    ob["server"] = item["ip"]       # 已在预检阶段解析，避免 sing-box 再做 DNS（SNI/Host 已在解析时固定）
    ob["tag"] = "node"
    exe = _SINGBOX_EXE

    for attempt in range(2):
        port = _alloc_socks_port()
        task = uuid.uuid4().hex[:10]
        cfg_path = os.path.join(RUNTIME_DIR, f"sb_{task}.json")
        log_path = os.path.join(RUNTIME_DIR, f"sb_{task}.log")
        proc, logf = None, None
        try:
            config = {
                "log": {"level": "error"},
                "inbounds": [{"type": "socks", "tag": "socks-in", "listen": "127.0.0.1", "listen_port": port}],
                "outbounds": [ob, {"type": "direct", "tag": "direct"}],
                "route": {"final": "node"},
            }
            with open(cfg_path, "w", encoding="utf-8") as f:
                json.dump(config, f)
            logf = open(log_path, "wb")
            proc = subprocess.Popen([exe, "run", "-c", cfg_path], stdout=subprocess.DEVNULL,
                                    stderr=logf, cwd=RUNTIME_DIR)
            ready = died = False
            deadline = time.time() + SINGBOX_START_TIMEOUT
            while time.time() < deadline:
                if proc.poll() is not None:
                    died = True
                    break
                try:
                    with socket.create_connection(("127.0.0.1", port), timeout=0.3):
                        ready = True
                        break
                except OSError:
                    time.sleep(0.1)
            if not ready:
                if died and attempt == 0:
                    continue                      # 可能是端口被抢，换个端口重试一次
                bump("start_fail")
                try:
                    logf.flush()
                    with open(log_path, "rb") as lf:
                        tail = lf.read()[-400:].decode("utf-8", errors="ignore").strip().splitlines()
                    msg = (tail[-1] if tail else "(无输出)")[:160]
                except OSError:
                    msg = "(无法读取日志)"
                with _STATS_LOCK:
                    START_ERRORS[f"[{item['proto']}] {msg}"] += 1
                return None
            return _probe_through(port, item)
        except Exception as e:  # noqa: BLE001
            bump("test_exception")
            if DEBUG:
                print(f"[debug] {item['server']}: {e}")
            return None
        finally:
            if proc is not None:
                if proc.poll() is None:
                    proc.kill()
                try:
                    proc.wait(timeout=3)
                except Exception:  # noqa: BLE001
                    pass
            if logf is not None:
                logf.close()
            for p in (cfg_path, log_path):
                remove_path(p)
            _release_port(port)
    return None


def run_liveness_test(candidates: list) -> list:
    total = len(candidates)
    print(f"[*] 真实测活: {total} 个节点 (并发 {MAX_WORKERS_TEST}) ...")
    results, done, t0 = [], 0, time.time()
    with ThreadPoolExecutor(max_workers=MAX_WORKERS_TEST) as ex:
        futs = [ex.submit(test_single_node, it) for it in candidates]
        for fut in as_completed(futs):
            done += 1
            try:
                r = fut.result()
            except Exception:  # noqa: BLE001
                r = None
            if r:
                results.append(r)
            if done % 100 == 0 or done == total:
                print(f"    进度 {done}/{total} | 存活 {len(results)} | 用时 {int(time.time() - t0)}s")
    print(f"[+] 测活通过: {len(results)}")
    return results


# ══════════════════════════════════════════════════════════════════
# 分类：国家 / 原生 / 家宽
# ══════════════════════════════════════════════════════════════════

class GeoDB:
    """GeoLite2-Country 同时含「使用地 country」与「注册地 registered_country」。"""

    def __init__(self):
        self.country = self._open(GEO_COUNTRY_DB)
        self.asn = self._open(GEO_ASN_DB)

    @staticmethod
    def _open(path):
        if maxminddb is None or not os.path.exists(path):
            return None
        try:
            return maxminddb.open_database(path)
        except Exception as e:  # noqa: BLE001
            print(f"[!] 无法打开 {os.path.basename(path)}: {e}")
            return None

    @staticmethod
    def _iso(d, key):
        v = (d or {}).get(key) or {}
        cc = str(v.get("iso_code") or "").upper()
        return cc if re.fullmatch(r"[A-Z]{2}", cc) else None

    def lookup(self, ip: str) -> dict:
        res = {"country": None, "registered": None, "asn_org": ""}
        if not ip:
            return res
        if self.country:
            try:
                rec = self.country.get(ip)
                res["country"] = self._iso(rec, "country")
                res["registered"] = self._iso(rec, "registered_country")
            except Exception:  # noqa: BLE001
                pass
        if self.asn:
            try:
                rec = self.asn.get(ip) or {}
                res["asn_org"] = str(rec.get("autonomous_system_organization") or "")
            except Exception:  # noqa: BLE001
                pass
        return res


def ip_api_batch_lookup(ip_list: list) -> dict:
    info, fails = {}, 0
    batches = [ip_list[i:i + IP_API_BATCH_SIZE] for i in range(0, len(ip_list), IP_API_BATCH_SIZE)]
    print(f"[*] ip-api 批量查询 {len(ip_list)} 个出口 IP ({len(batches)} 批) ...")
    for bi, chunk in enumerate(batches):
        ok = False
        for _ in range(3):
            try:
                r = DIRECT_SESSION.post(IP_API_BATCH_URL, json=[{"query": ip} for ip in chunk], timeout=20)
            except requests.RequestException:
                break
            if r.status_code == 429:
                try:
                    ttl = int(r.headers.get("X-Ttl", "5"))
                except ValueError:
                    ttl = 5
                time.sleep(min(ttl + 1, 65))
                continue
            if r.status_code == 200:
                try:
                    for rec in r.json():
                        if rec.get("status") == "success" and rec.get("query"):
                            info[rec["query"]] = rec
                    ok = True
                except ValueError:
                    pass
            break
        fails = 0 if ok else fails + 1
        if fails >= 2:
            print("[!] ip-api 连续失败，放弃剩余批次，改用 ASN 关键词判断")
            break
        if bi < len(batches) - 1:
            time.sleep(IP_API_BATCH_INTERVAL)
    return info


def classify_ip_type(rec: dict, asn_org: str) -> str:
    """返回 'residential'(家宽/移动) 或 'idc'(机房/未知)。"""
    text = " ".join(filter(None, [asn_org, rec.get("isp"), rec.get("org"), rec.get("asname")]))
    if rec:                                              # ip-api 有结果
        if rec.get("mobile"):
            return "residential"
        if rec.get("hosting") or IDC_RE.search(text):
            return "idc"
        return "residential"
    # ip-api 无结果：保守判断，必须明确像 ISP 才算家宽
    if ISP_RE.search(text) and not IDC_RE.search(text):
        return "residential"
    return "idc"


def classify_results(results: list):
    print("[*] 分类: 国家 / 原生(注册地==使用地) / 家宽 或 机房 ...")
    geo = GeoDB()
    if not geo.country:
        print("[!] 没有 GeoLite2-Country，国家取自出口探测，原生 IP 无法判断")

    for r in results:
        r["_look_ip"] = r.get("exit_ip") or r["ip"]
        r["_geo"] = geo.lookup(r["_look_ip"])

    ip_info = {}
    if ENABLE_IP_API:
        ips = sorted({r["exit_ip"] for r in results if r.get("exit_ip") and is_public_ip(r["exit_ip"])})
        if ips:
            ip_info = ip_api_batch_lookup(ips[:IP_API_MAX_IPS])

    items = []
    for r in results:
        g = r["_geo"]
        rec = ip_info.get(r.get("exit_ip"), {})
        actual = g["country"] or r.get("exit_country") or rec.get("countryCode")
        actual = (actual or "OTHER").upper()
        if not re.fullmatch(r"[A-Z]{2}", actual):
            actual = "OTHER"
        native = bool(g["country"] and g["registered"] and g["country"] == g["registered"])
        ip_type = classify_ip_type(rec, g["asn_org"])
        tag = "家宽·原生" if (ip_type == "residential" and native) else (
            "家宽" if ip_type == "residential" else ("原生" if native else ""))
        items.append({
            "raw": r["raw"], "outbound": r["outbound"], "server": r["server"], "port": r["port"],
            "proto": r["proto"], "ip": r["ip"], "exit_ip": r.get("exit_ip"),
            "latency_ms": r["latency_ms"], "country": actual,
            "native": native, "ip_type": ip_type, "tag": tag, "asn_org": g["asn_org"],
        })

    if DEDUP_BY_EXIT_IP:
        best = {}
        for it in items:
            key = it["exit_ip"] or ("srv", it["ip"], it["port"])
            if key not in best or it["latency_ms"] < best[key]["latency_ms"]:
                best[key] = it
        if len(best) != len(items):
            print(f"[*] 相同出口 IP 去重: {len(items)} → {len(best)}")
        items = list(best.values())

    items.sort(key=lambda x: x["latency_ms"])
    residential = [i for i in items if i["ip_type"] == "residential"]
    native = [i for i in items if i["ip_type"] != "residential" and i["native"]]
    normal = [i for i in items if i["ip_type"] != "residential" and not i["native"]]
    if MAX_RESIDENTIAL > 0:
        residential = residential[:MAX_RESIDENTIAL]
    if MAX_NATIVE > 0:
        native = native[:MAX_NATIVE]
    selected_normal = normal[:MAX_NORMAL] if MAX_NORMAL > 0 else normal
    print(f"[*] 精选结果: 家宽 {len(residential)} | 原生 {len(native)} | "
          f"普通精选 {len(selected_normal)} (候选 {len(normal)}) | 总计 "
          f"{len(residential) + len(native) + len(selected_normal)}")
    return {"residential": residential, "native": native, "normal": selected_normal}


# ══════════════════════════════════════════════════════════════════
# 格式转换：outbound → v2ray 链接 / Clash / sing-box
# ══════════════════════════════════════════════════════════════════

def _uri_host(host: str) -> str:
    return f"[{host}]" if ":" in host and not host.startswith("[") else host


def _urlencode(q: dict) -> str:
    return urllib.parse.urlencode({k: str(v) for k, v in q.items() if v not in (None, "")},
                                  quote_via=urllib.parse.quote, safe="")


def _ws_path_with_ed(t: dict) -> str:
    path = t.get("path", "/")
    ed = t.get("max_early_data")
    if ed:
        path += ("&" if "?" in path else "?") + f"ed={ed}"
    return path


def _tls_query(q: dict, tls: dict, insecure_key: str = "allowInsecure"):
    if not tls:
        q["security"] = "none"
        return
    if tls.get("reality"):
        q["security"] = "reality"
        q["pbk"] = tls["reality"].get("public_key", "")
        q["sid"] = tls["reality"].get("short_id", "")
    else:
        q["security"] = "tls"
    q["sni"] = tls.get("server_name", "")
    if tls.get("alpn"):
        q["alpn"] = ",".join(tls["alpn"])
    fp = (tls.get("utls") or {}).get("fingerprint")
    if fp:
        q["fp"] = fp
    if tls.get("insecure"):
        q[insecure_key] = "1"


def _transport_query(q: dict, t):
    if not t:
        q["type"] = "tcp"
        return
    typ = t["type"]
    if typ == "ws":
        q["type"] = "ws"
        q["path"] = _ws_path_with_ed(t)
        q["host"] = (t.get("headers") or {}).get("Host", "")
    elif typ == "grpc":
        q["type"] = "grpc"
        q["serviceName"] = t.get("service_name", "")
        q["mode"] = "gun"
    elif typ == "http":
        q["type"] = "http"
        q["path"] = t.get("path", "/")
        q["host"] = ",".join(t.get("host", []))
    elif typ == "httpupgrade":
        q["type"] = "httpupgrade"
        q["path"] = t.get("path", "/")
        q["host"] = t.get("host", "")


def outbound_to_v2ray_link(node: dict, name: str) -> str:
    t = node.get("type")
    host, port = _uri_host(node["server"]), node["server_port"]
    frag = "#" + urllib.parse.quote(name)
    tls = node.get("tls")
    if t == "vless":
        q = {"encryption": "none"}
        _tls_query(q, tls)
        if node.get("flow"):
            q["flow"] = node["flow"]
        _transport_query(q, node.get("transport"))
        if node.get("packet_encoding"):
            q["packetEncoding"] = node["packet_encoding"]
        return f"vless://{node['uuid']}@{host}:{port}?{_urlencode(q)}{frag}"
    if t == "vmess":
        tr = node.get("transport") or {}
        data = {"v": "2", "ps": name, "add": node["server"], "port": str(port), "id": node["uuid"],
                "aid": str(node.get("alter_id", 0)), "scy": node.get("security", "auto"),
                "net": "tcp", "type": "none", "host": "", "path": "",
                "tls": "tls" if tls else "", "sni": (tls or {}).get("server_name", ""),
                "alpn": ",".join((tls or {}).get("alpn", [])),
                "fp": ((tls or {}).get("utls") or {}).get("fingerprint", "")}
        if tls and tls.get("insecure"):
            data["allowInsecure"] = "1"
        typ = tr.get("type")
        if typ == "ws":
            data.update(net="ws", path=_ws_path_with_ed(tr), host=(tr.get("headers") or {}).get("Host", ""))
        elif typ == "grpc":
            data.update(net="grpc", path=tr.get("service_name", ""))
        elif typ == "http":
            data.update(net="h2", path=tr.get("path", "/"), host=",".join(tr.get("host", [])))
        elif typ == "httpupgrade":
            data.update(net="httpupgrade", path=tr.get("path", "/"), host=tr.get("host", ""))
        return "vmess://" + base64.b64encode(json.dumps(data, ensure_ascii=False).encode("utf-8")).decode()
    if t == "trojan":
        q = {}
        _tls_query(q, tls)
        _transport_query(q, node.get("transport"))
        pw = urllib.parse.quote(node["password"], safe="")
        return f"trojan://{pw}@{host}:{port}?{_urlencode(q)}{frag}"
    if t == "shadowsocks":
        ui = base64.urlsafe_b64encode(f"{node['method']}:{node['password']}".encode()).decode().rstrip("=")
        return f"ss://{ui}@{host}:{port}{frag}"
    if t == "hysteria2":
        q = {"sni": (tls or {}).get("server_name", ""), "insecure": "1" if (tls or {}).get("insecure") else "",
             "alpn": ",".join((tls or {}).get("alpn", []))}
        if node.get("obfs"):
            q["obfs"] = node["obfs"].get("type", "salamander")
            q["obfs-password"] = node["obfs"].get("password", "")
        pw = urllib.parse.quote(node["password"], safe="")
        return f"hysteria2://{pw}@{host}:{port}/?{_urlencode(q)}{frag}"
    if t == "tuic":
        q = {"congestion_control": node.get("congestion_control", ""),
             "udp_relay_mode": node.get("udp_relay_mode", ""),
             "alpn": ",".join((tls or {}).get("alpn", [])), "sni": (tls or {}).get("server_name", ""),
             "allow_insecure": "1" if (tls or {}).get("insecure") else ""}
        pw = urllib.parse.quote(node["password"], safe="")
        return f"tuic://{node['uuid']}:{pw}@{host}:{port}?{_urlencode(q)}{frag}"
    if t == "anytls":
        q = {"sni": (tls or {}).get("server_name", ""), "insecure": "1" if (tls or {}).get("insecure") else "",
             "alpn": ",".join((tls or {}).get("alpn", []))}
        pw = urllib.parse.quote(node["password"], safe="")
        return f"anytls://{pw}@{host}:{port}?{_urlencode(q)}{frag}"
    return ""


def _clash_tls(p: dict, tls: dict, sni_key: str = "servername"):
    if not tls:
        return
    if sni_key == "servername":
        p["tls"] = True
    if tls.get("server_name"):
        p[sni_key] = tls["server_name"]
    if tls.get("alpn"):
        p["alpn"] = list(tls["alpn"])
    fp = (tls.get("utls") or {}).get("fingerprint")
    if fp:
        p["client-fingerprint"] = fp
    if tls.get("insecure"):
        p["skip-cert-verify"] = True
    if tls.get("reality"):
        p["reality-opts"] = {"public-key": tls["reality"].get("public_key", ""),
                             "short-id": tls["reality"].get("short_id", "")}


def _clash_transport(p: dict, t):
    if not t:
        p["network"] = "tcp"
        return
    typ = t["type"]
    if typ == "ws":
        opts = {"path": t.get("path", "/")}
        if (t.get("headers") or {}).get("Host"):
            opts["headers"] = {"Host": t["headers"]["Host"]}
        if t.get("max_early_data"):
            opts["max-early-data"] = t["max_early_data"]
            opts["early-data-header-name"] = t.get("early_data_header_name", "Sec-WebSocket-Protocol")
        p["network"], p["ws-opts"] = "ws", opts
    elif typ == "grpc":
        p["network"], p["grpc-opts"] = "grpc", {"grpc-service-name": t.get("service_name", "")}
    elif typ == "http":
        opts = {"path": t.get("path", "/")}
        if t.get("host"):
            opts["host"] = list(t["host"])
        p["network"], p["h2-opts"] = "h2", opts
    elif typ == "httpupgrade":
        opts = {"path": t.get("path", "/"), "v2ray-http-upgrade": True}
        if t.get("host"):
            opts["headers"] = {"Host": t["host"]}
        p["network"], p["ws-opts"] = "ws", opts


def outbound_to_clash(node: dict, name: str):
    t = node.get("type")
    server, port = node.get("server"), node.get("server_port")
    if not server or not port:
        return None
    tls = node.get("tls")
    p = {"name": name, "type": "", "server": server, "port": port, "udp": True}
    if t == "vless":
        p.update(type="vless", uuid=node["uuid"])
        if node.get("flow"):
            p["flow"] = node["flow"]
        if node.get("packet_encoding") == "xudp":
            p["packet-encoding"] = "xudp"
        _clash_tls(p, tls)
        _clash_transport(p, node.get("transport"))
    elif t == "vmess":
        p.update(type="vmess", uuid=node["uuid"], alterId=node.get("alter_id", 0),
                 cipher=node.get("security", "auto"))
        _clash_tls(p, tls)
        _clash_transport(p, node.get("transport"))
    elif t == "trojan":
        if not tls:
            return None
        p.update(type="trojan", password=node["password"])
        _clash_tls(p, tls, sni_key="sni")
        _clash_transport(p, node.get("transport"))
    elif t == "shadowsocks":
        p.update(type="ss", cipher=node["method"], password=node["password"])
    elif t == "hysteria2":
        p.update(type="hysteria2", password=node["password"])
        _clash_tls(p, tls, sni_key="sni")
        if node.get("obfs"):
            p["obfs"] = node["obfs"].get("type", "salamander")
            p["obfs-password"] = node["obfs"].get("password", "")
    elif t == "tuic":
        p.update(type="tuic", uuid=node["uuid"], password=node["password"])
        _clash_tls(p, tls, sni_key="sni")
        p["congestion-controller"] = node.get("congestion_control", "bbr")
        p["udp-relay-mode"] = node.get("udp_relay_mode", "native")
    elif t == "anytls":
        p.update(type="anytls", password=node["password"])
        _clash_tls(p, tls, sni_key="sni")
    else:
        return None
    return p


def outbound_to_singbox(node: dict, name: str) -> dict:
    n = dict(node)
    n["tag"] = name
    return n


def export_clash_yaml(proxies: list, filepath: str):
    names = [p["name"] for p in proxies]
    config = {
        "port": 7890, "socks-port": 7891, "allow-lan": False, "mode": "rule", "log-level": "info",
        "proxies": proxies,
        "proxy-groups": [
            {"name": "🚀 节点选择", "type": "select", "proxies": ["♻️ 自动选择"] + names},
            {"name": "♻️ 自动选择", "type": "url-test", "proxies": names,
             "url": "https://www.gstatic.com/generate_204", "interval": 300, "tolerance": 50},
        ],
        "rules": ["MATCH,🚀 节点选择"],
    }
    write_text(filepath, yaml.dump(config, allow_unicode=True, sort_keys=False, default_flow_style=False))


def export_singbox_json(nodes: list, filepath: str):
    """生成可直接使用的 sing-box 客户端配置（需要 sing-box 1.12+）。"""
    tags = [n["tag"] for n in nodes]
    config = {
        "log": {"level": "warn"},
        "dns": {"servers": [{"type": "local", "tag": "local"}]},
        "inbounds": [{"type": "mixed", "tag": "mixed-in", "listen": "127.0.0.1", "listen_port": 2080}],
        "outbounds": [
            {"type": "selector", "tag": "proxy", "outbounds": ["auto"] + tags, "default": "auto"},
            {"type": "urltest", "tag": "auto", "outbounds": tags,
             "url": "https://www.gstatic.com/generate_204", "interval": "5m"},
            *nodes,
            {"type": "direct", "tag": "direct"},
        ],
        "route": {"final": "proxy", "auto_detect_interface": True, "default_domain_resolver": "local"},
    }
    write_text(filepath, json.dumps(config, indent=2, ensure_ascii=False))


# ══════════════════════════════════════════════════════════════════
# 导出
# ══════════════════════════════════════════════════════════════════

def make_node_name(item: dict, idx: int) -> str:
    cc = item["country"]
    tag = f" ({item['tag']})" if item.get("tag") else ""
    return f"{get_country_flag(cc)} {COUNTRY_NAMES.get(cc, cc)} {idx:02d}{tag} - {NAME_SUFFIX}"


def build_group(nodes_list: list):
    counters = collections.Counter()
    links, proxies, sb_nodes = [], [], []
    for item in nodes_list:
        counters[item["country"]] += 1
        name = make_node_name(item, counters[item["country"]])
        ob = item["outbound"]
        link = outbound_to_v2ray_link(ob, name)
        if link:
            links.append(link)
        cp = outbound_to_clash(ob, name)
        if cp:
            proxies.append(cp)
        sb_nodes.append(outbound_to_singbox(ob, name))
    return links, proxies, sb_nodes


def group_by_country(nodes: list) -> dict:
    d = {}
    for n in nodes:
        d.setdefault(n["country"], []).append(n)
    return d


def export_group(nodes_list: list, sub_path: str, clash_path: str, singbox_path: str = None):
    links, proxies, sb = build_group(nodes_list)
    if links:
        write_sub(sub_path, links)
    else:
        remove_path(sub_path)
    if proxies:
        export_clash_yaml(proxies, clash_path)
    else:
        remove_path(clash_path)
    if singbox_path:
        if sb:
            export_singbox_json(sb, singbox_path)
        else:
            remove_path(singbox_path)
    return len(links)


def export_by_country(nodes_list: list, directory: str):
    remove_path(directory)
    os.makedirs(directory, exist_ok=True)
    for cc, lst in group_by_country(nodes_list).items():
        export_group(lst, os.path.join(directory, f"{cc}.txt"), os.path.join(directory, f"clash-{cc}.yaml"))


def export_all(groups: dict) -> dict:
    ensure_directories()
    res, nat, normal = groups["residential"], groups["native"], groups["normal"]
    everything = res + nat + normal
    n_all = export_group(everything, os.path.join(OUTPUT_DIR, "v2ray.txt"),
                         os.path.join(OUTPUT_DIR, "clash.yaml"), os.path.join(OUTPUT_DIR, "singbox.json"))
    n_res = export_group(res, os.path.join(OUTPUT_DIR, "residential.txt"),
                         os.path.join(OUTPUT_DIR, "residential-clash.yaml"))
    n_nat = export_group(nat, os.path.join(OUTPUT_DIR, "native.txt"),
                         os.path.join(OUTPUT_DIR, "native-clash.yaml"))
    export_by_country(res, RESIDENTIAL_COUNTRY_DIR)
    export_by_country(nat, NATIVE_COUNTRY_DIR)
    export_by_country(normal, COUNTRY_DIR)
    stats = {
        "updated": datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC"),
        "total": n_all, "residential": n_res, "native": n_nat, "normal": len(normal),
        "countries": sorted({i["country"] for i in everything}),
    }
    write_text(os.path.join(OUTPUT_DIR, "stats.json"), json.dumps(stats, indent=2, ensure_ascii=False))
    print(f"[*] 导出完毕: 全量 {n_all} | 家宽 {n_res} | 原生 {n_nat} | 普通精选 {len(normal)}")
    return stats


def update_readme(stats: dict, groups: dict):
    repo = (os.environ.get("GITHUB_REPOSITORY") or "jack197889/NativeNods-DIY").strip()
    raw = f"https://raw.githubusercontent.com/{repo}/main/output"
    cdn = f"https://cdn.jsdelivr.net/gh/{repo}@main/output"

    def country_lines(nodes, sub_dir):
        out = []
        for cc in sorted(group_by_country(nodes)):
            name = COUNTRY_NAMES.get(cc, cc)
            out.append(f"- {get_country_flag(cc)} {name}: "
                       f"[v2ray]({raw}/{sub_dir}/{cc}.txt) · [clash]({raw}/{sub_dir}/clash-{cc}.yaml)")
        return "\n".join(out) or "- (暂无)"

    text = f"""# 🚀 免费节点自动测活订阅池 (含真实家宽/原生IP甄选)

> ⚡ **真实测活**: 每个节点都通过 sing-box 建立隧道，并访问 generate_204 验证。
> 🕒 **最近更新**: `{stats['updated']}`
> 📌 **精选节点总数**: `{stats['total']}` 个 (家宽 `{stats['residential']}` | 原生 `{stats['native']}` | 普通精选 `{stats['normal']}`)
> 🏠 家宽 / 原生节点全部保留；普通节点保留延迟最低的前 {MAX_NORMAL} 个；相同出口 IP 只保留一个。

## 📎 订阅链接

| 类型 | v2ray (base64) | Clash / Mihomo |
| --- | --- | --- |
| 全部 | `{raw}/v2ray.txt` | `{raw}/clash.yaml` |
| 家宽 | `{raw}/residential.txt` | `{raw}/residential-clash.yaml` |
| 原生 | `{raw}/native.txt` | `{raw}/native-clash.yaml` |

sing-box 客户端配置 (1.12+): `{raw}/singbox.json`

> 国内网络访问 GitHub Raw 不稳定时，把链接前缀换成 `{cdn}/` (jsDelivr，有缓存延迟)。

## 🌍 按国家 / 地区

### 🏠 家宽
{country_lines(groups['residential'], 'residential-by-country')}

### 🧬 原生
{country_lines(groups['native'], 'native-by-country')}

### ⚡ 普通精选
{country_lines(groups['normal'], 'by-country')}

## 📖 说明

- **原生 IP**: 出口 IP 的「注册地国家」与「实际使用地国家」一致 (GeoLite2-Country 的 registered_country 与 country)。
- **家宽**: ip-api 判断非机房 (hosting=false) 或移动网络，并结合 ASN 名称关键词；属于近似判断，可能与第三方检测网站不完全一致。
- 免费节点来自公开订阅源，**不可信**，可能嗅探或篡改流量，请勿用于登录银行、邮箱等敏感账号。
"""
    write_text(os.path.join(BASEDIR, "README.md"), text)


# ══════════════════════════════════════════════════════════════════
# 主流程
# ══════════════════════════════════════════════════════════════════

def print_diagnostics():
    keys = ["parse_fail", "duplicate", "dropped_insecure", "dns_fail", "non_public_ip", "port_closed",
            "start_fail", "probe_fail", "too_slow", "test_exception"]
    line = " | ".join(f"{k}={STATS[k]}" for k in keys if STATS[k])
    if line:
        print(f"[*] 统计: {line}")
    if START_ERRORS:
        print("[!] sing-box 启动失败原因 Top5 (若数量很大，多半是内核版本与配置字段不兼容):")
        for msg, n in START_ERRORS.most_common(5):
            print(f"    {n:>5} × {msg}")


def main():
    t_start = time.time()
    print("==== 免费节点测活脚本启动 ====")
    ensure_directories()
    setup_environment()

    raw = fetch_raw_nodes()
    candidates = build_candidates(raw)
    if not candidates:
        print("[!] 没有可解析的节点，请检查订阅源 / 网络")
        sys.exit(1)

    candidates = prefilter_candidates(candidates)
    if not candidates:
        print("[!] 预检后没有节点，请检查网络 / DNS")
        print_diagnostics()
        sys.exit(1)

    if MAX_CANDIDATES > 0 and len(candidates) > MAX_CANDIDATES:
        random.shuffle(candidates)
        print(f"[*] 候选过多，随机抽取 {MAX_CANDIDATES} 个测试 (可用 MAX_CANDIDATES 调整)")
        candidates = candidates[:MAX_CANDIDATES]

    results = run_liveness_test(candidates)
    print_diagnostics()
    if not results:
        print("[!] 没有存活节点 —— 为避免覆盖旧订阅，本次不写入输出。")
        print("    排查: 1) 是否安装 requests[socks] (PySocks)  2) 上面的 sing-box 启动失败原因  "
              "3) 运行环境能否访问 gstatic.com (DEBUG=1 查看更多)")
        sys.exit(1)

    groups = classify_results(results)
    stats = export_all(groups)
    update_readme(stats, groups)
    print(f"===== 运行结束，用时 {int(time.time() - t_start)}s =====")


if __name__ == "__main__":
    main()
