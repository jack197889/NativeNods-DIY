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
  4. 分类（每个节点只属于一类，优先级 家宽 > 原生 > 普通）：
       - 家宽：家庭宽带 IP（含移动网络）且为原生 IP。识别沿用原作者方案
               (ip-api hosting/proxy/mobile → CDN 网段 → ASN 名单 → 名称关键词 → rDNS)，无需额外核验
       - 原生：非家宽，且为原生 IP（注册地国家 == 使用地国家；注册地取 RDAP，查不到用 GeoLite2）
       - 普通：其余，含「广播 IP」(包括家庭宽带但广播的 IP)
  5. 导出：v2ray(base64) / Clash / sing-box，总表 + 按国家，并更新 README

规则：风控值(Scamalytics) 超过 MAX_RISK_SCORE(默认 45) 的节点一律淘汰；家宽、原生节点全部保留；普通节点保留延迟最低的 MAX_NORMAL(默认 50) 个。

依赖：pip install -r requirements.txt   (requests[socks]  PyYAML  maxminddb)

可用环境变量（均可选）：
  SINGBOX_BIN / SINGBOX_VERSION   指定内核路径 / 版本
  MAX_WORKERS_TEST                测活并发（默认 48）
  MAX_CANDIDATES                  最多测试多少个节点（默认 5000，0=不限）
  MAX_NORMAL / MAX_NATIVE / MAX_RESIDENTIAL   各类保留上限（0=不限）
  MAX_RISK_SCORE / ENABLE_RISK_FILTER / DROP_RISK_UNKNOWN   风控值过滤(默认 45 / 开 / 查询失败保留)
  ENABLE_SPEED_TEST=1             开启限时测速
  ENABLE_RDAP=0                   关闭 RDAP 注册地查询（仅用 GeoLite2）
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
ENABLE_RISK_FILTER = _env_flag("ENABLE_RISK_FILTER", True)   # 风控值过滤（所有节点，含普通）
MAX_RISK_SCORE = _env_int("MAX_RISK_SCORE", 45)              # 风控值超过它的节点淘汰
DROP_RISK_UNKNOWN = _env_flag("DROP_RISK_UNKNOWN", False)    # 风控值查询失败的节点：默认保留
RISK_WORKERS = 4
RISK_BATCH = 60
NO_EXIT_MAX_RATIO = 0.5         # 取不到出口 IP 的存活节点占比超过它 → 视为探测服务故障，不淘汰
MAX_NORMAL = _env_int("MAX_NORMAL", 50)
MAX_NATIVE = _env_int("MAX_NATIVE", 0)
MAX_RESIDENTIAL = _env_int("MAX_RESIDENTIAL", 0)
DEDUP_BY_EXIT_IP = True         # 相同出口 IP 只保留延迟最低的一个
DROP_INSECURE = _env_flag("DROP_INSECURE", False)
ALLOW_INSECURE_DEFAULT = False  # 订阅链接没写 insecure 时，是否默认跳过证书验证
ENABLE_IP_API = _env_flag("ENABLE_IP_API", True)
ENABLE_RDAP = _env_flag("ENABLE_RDAP", True)   # 用 RIR(RDAP) 确认注册地
RDAP_MAX_IPS = 1500
RDAP_WORKERS = 8
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
                    "status,message,countryCode,regionName,city,isp,org,as,asname,"
                    "mobile,proxy,hosting,query")
IP_API_BATCH_SIZE = 100
IP_API_BATCH_INTERVAL = 4.2     # 免费版 15 次/分钟
IP_API_MAX_IPS = 3000

USER_AGENT = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
              "(KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36")

UDP_PROTOS = ("hysteria2", "tuic")

# 以下名单与关键词沿用原作者方案（CDN 网段 / 机房 ASN / 家宽 ASN / 名称关键词）
# Cloudflare 官方 Anycast 全网段 (命中即 CDN 任播, 绝非家宽)
CLOUDFLARE_IP_NETWORKS = [ipaddress.ip_network(n) for n in (
    "173.245.48.0/20","103.21.244.0/22","103.22.200.0/22","103.31.4.0/22",
    "141.101.64.0/18","108.162.192.0/18","190.93.240.0/20","188.114.96.0/20",
    "197.234.240.0/22","198.41.128.0/17","162.158.0.0/15","104.16.0.0/13",
    "104.24.0.0/14","172.64.0.0/13","131.0.72.0/22",
)]

# Google / Fastly / Akamai 等常见 CDN 与云入口段 (命中即标 CDN/机房)
CDN_IP_NETWORKS_EXTRA = [ipaddress.ip_network(n) for n in (
    # Google
    "8.8.4.0/24","8.8.8.0/24","8.34.208.0/20","8.35.192.0/20","34.64.0.0/10","35.184.0.0/13",
    "35.192.0.0/14","35.196.0.0/15","35.200.0.0/13","35.216.0.0/15","35.220.0.0/14",
    "64.15.112.0/20","64.233.160.0/19","66.102.0.0/20","66.249.64.0/19","72.14.192.0/18",
    "74.125.0.0/16","108.177.0.0/17","142.250.0.0/15","172.217.0.0/16","173.194.0.0/16",
    "209.85.128.0/17","216.58.192.0/19","216.239.32.0/19",
    # Fastly
    "23.235.32.0/20","43.249.72.0/22","103.244.50.0/24","103.245.222.0/23",
    "104.156.80.0/20","140.248.64.0/18","146.75.0.0/16","151.101.0.0/16",
    "157.52.64.0/18","167.82.0.0/17","199.232.0.0/16","204.129.196.0/22",
    # Akamai (核心段)
    "23.32.0.0/13","23.64.0.0/14","23.192.0.0/11","23.197.0.0/16",
    "95.100.0.0/15","104.64.0.0/10","184.24.0.0/13","184.84.0.0/14",
    # Cloudflare Spectrum / 托管入口
    "104.16.0.0/12",
)]

# 已知云/机房 ASN (离线兜底用; 在线 ip-api hosting=true 为主判据)
DATACENTER_ASNS = {
    13335,  # Cloudflare
    16509, 14618,  # AWS
    15169, 396982,  # Google
    8075, 8068,  # Microsoft
    24940,  # Hetzner
    16276,  # OVH
    14061,  # DigitalOcean
    31898, 63949,  # Oracle
    45102,  # Alibaba
    132203,  # Tencent
    20473,  # Choopa/Vultr 早期
    60068,  # Datacamp (CDN77)
    55081,  # Hostinger
    197540,  # Hostinger EU
    51167,  # Contabo
    8560,  # 1&1 / IONOS
    42708,  # IONOS
    201814, 49981,  # Hosthatch/Hostkey 类
    212238, 46652,  # Serverius/OVH 类
    141995, 200019, 136907, 39351, 9009,  # M247/Hosthatch 等
    174, 3356, 1299, 2914, 6939,  # 骨干 (Cogent/Lumen/Arelion/NTT/Hurricane)
    199524, 206096, 49505,  # Selectel/WorldStream
    62240, 49304, 34665, 209242, 219337, 44477,
    200651, 202685, 210644, 205628, 51852, 204544, 397373, 140224,  # 小型 IDC
    54866,  # Parsebian/HydraTransit 类
    45899,  # VNPT 云? 标记为 IDC
    # ★ 实测漏网: 收购家宽段/伪装 DSL rDNS 的云边网络 (ip-api proxy=true 案例补充)
    62610,  # Zenlayer (AS62610, rDNS 带 dsl.speakeasy.net 但 proxy=true)
    60205,  # 62610 关联段
    8342,  # Deltacomputers/Evrasia 类
    9009, 47692, 62041, 56630, 57502,  # Serverius/ProXmedia/Clouvider 类
}

# 民用宽带 ASN 白名单 (离线兜底; 关键国家主流运营商)
RESIDENTIAL_ASNS = {
    # 台湾
    3462,    # Chunghwa Telecom (中华电信)
    9924, 17709, 4780, 18049,  # 亚太电信/远传/台湾大哥大/凯擘
    9269, 3491,  # 台湾硕网/和宇宽频
    # 香港
    4760, 476, 4515, 9229, 9266, 10103,  # PCCW/HKT/CUHK/HGC/HKBN/HKTBB
    9059, 38861,  # Hong Kong Broadband
    # 日本
    4713, 2516, 17676, 4721, 2497, 9605, 17511, 9318, 2518, 20193,
    # Softbank/NTT Communications/KDDI/IIJ/Sony/Plala/@nifty/JCN
    4766, 3786, 17816, 9357,
    # 韩国
    4713, 9318, 17816, 9357, 4766,  # KT/LG/SK  
    # 美国
    701, 7018, 7922, 20115, 22773, 10796, 20057, 11427, 10507, 6128,
    33363, 21928, 10777, 33660, 33661, 33662, 36466, 53417, 55136,
    20057, 19024, 12271, 11404, 6983, 33554, 7155, 30162, 10790,
    # Comcast (7922/33487/22263...) / Charter (20115/10796/20057) / Cox / AT&T / Verizon
    702, 703, 704, 705, 706, 709, 710, 711, 712, 713, 714, 715,  # legacy Verizon
    2828, 20001, 3549,  # CenturyLink/Level3 (部分为家宽)
    6167, 6162, 7018,  # AT&T
    5056,  # Cox East
    10796,  # Charter
    11351,  # TWC
    6128,  # Atlantis
    # 英国
    2856, 5607, 20650, 13285, 12576, 12725, 19541, 33950, 5413,
    # BT/TalkTalk/Orange/Virgin/Plusnet/Sky/Eclipse
    # 德国
    3320, 3209, 6805, 8888, 9145, 13237, 15366, 20879, 16097, 15594,
    # DT/Vodafone/EWE/netcup/Telefónica
    # 法国
    3215, 12322, 15557, 5410, 21590, 22869, 8228, 8220, 12670,
    # Orange/Free/SFR/Bouygues/LDN/9.tel
    # 荷兰 / 比利时
    33915, 20857, 5418, 6777, 15535, 6830, 8683,
    # KPN/Ziggo/Tele2/Solcon/Proximus/Telenet
    # 加拿大
    577, 6539, 812, 7992, 22995, 23498, 30645, 11260, 5645, 13331,
    # Bell/Rogers/Corus/Cogeco/Videotron/Telus
    # 澳大利亚 / 新西兰
    1221, 4764, 4761, 4747, 4802, 4804, 38293, 9443, 23871, 4771,
    # Telstra/Optus/iinet/AAPT/Exetel/SparkNZ
    # 新加坡 / 马来西亚
    9506, 9224, 10091, 4657, 32308, 55553, 177545, 9534, 17971, 24210,
    # Singtel/StarHub/M1/MyRepublic/TM/Maxis/Time
    # 巴西 / 拉美
    28573, 26599, 28598, 22085, 27699, 11014, 16832, 16397, 26615,
    # Claro/Vivo/Algar/Brisanet
    # 土耳其 / 俄罗斯 / 哈萨克
    9121, 34984, 15924, 31103, 47853, 25513, 12714, 8359, 12389,
    # Türk Telekom/Vodafone TR/MTS/Rostelecom/Kazakhtelecom
    # 意大利 / 西班牙
    3269, 30722, 12874, 12392, 12474, 3352, 12479, 12430,
    # Telecom Italia/Fastweb/Vodafone IT/Telefónica ES
    # 印度 / 越南 / 泰国 / 菲律宾 / 印尼
    55836, 9829, 9498, 17813, 45899, 7552, 9675, 7568, 45773, 45543,
    7590, 17457, 7552, 131293, 9336, 23969, 17816, 24099, 38251,
    # 印尼 Telkomsel/Indosat/Smartfren; 越南 Viettel/FPT; 泰国 AIS/True
}

# rDNS / ISP 名称关键词 (大小写不敏感; 离线兜底)
IDC_NAME_PATTERNS = [
    "hosting", "hoster", "datacenter", "data center", "cloud", "server",
    "vps", "dedicated", "colo", "colocation", "compute", "storage",
    "amazon", "aws", "google cloud", "microsoft", "azure", "oracle",
    "digitalocean", "linode", "vultr", "choopa", "hetzner", "ovh",
    "contabo", "m247", "leaseweb", "online s.a.s", "scaleway",
    "alibaba", "tencent", "huawei cloud", "ucloud", "jdcloud", "ksyun",
    "fastly", "cloudflare", "akamai", "cdn", "anycast", "edge network",
    "hostkey", "selectel", "aeza", "justhost", "idnica", "hostinger",
    "ionos", "1&1", "godaddy", "namecheap", "sucuri", "ispxk",
    "zenlayer", "zencom", "g-core", "gcore", "netcup", "hetzner",
]

RESIDENTIAL_NAME_PATTERNS = [
    # 通用家宽特征
    "broadband", "pppoe", "pppoa", "dsl", "cable", "fiber", "ftth",
    "fibre", "dynamic", "dial", "dialup", "residential", "home",
    "consumer", "cust", "customer", "subscriber", "pool", "dynamic-ip",
    # 台湾
    "chunghwa", "hinet", "taiwanmobile", "twn", "aptg", "kbro",
    "tfn", "sparq", "seednet", "data communication business group",
    # 香港
    "hkbn", "hong kong broadband", "pccw", "hkt", "hgc", "smartone",
    "netvigator", "citic telecom", "i-cable", "hk cable",
    # 日本
    "softbank", "ocn", "plala", "so-net", "iiJmio home", "eonet",
    "kddi", "jcom", "au broadband", "biglobe", "nifty",
    # 韩国
    "korea telecom", "kt corp", "sk broadband", "lgu+", "lg uplus",
    # 美国
    "comcast", "charter communications", "spectrum", "cox communications",
    "at&t", "at and t", "bellsouth", "sbc internet", "qwest", "centurylink",
    "verizon fios", "verizon online", "frontier communications", "windstream",
    "altice", "optimum online", "rcn", "wave broadband", "consolidated",
    "hughes", "viasat", "starlink", "mediaserv",
    # 欧洲
    "deutsche telekom", "telekom deutschland", "vodafone d2", "kabel deutschland",
    "british telecom", "bt broadband", "virgin media", "sky uk", "talktalk",
    "orange sa", "free SAS".lower(), "sfr", "bouygues", "bbox", "numericable",
    "kpn", "ziggo", "t-mobile netherlands", "proximus", "telenet",
    "telefonica", "movistar", "vodafone espana", "jazztel", "orange es",
    "telecom italia", "fastweb home", "iliad italia", "windtre",
    "swisscom", "a1 telekom", "magyar telekom", "o2 czech",
    "telia sweden", "telenor", "tele2 sweden", "bredband2",
    "rostelecom home", "mgts", "ertelecom", "dom.ru", "mtu-moscow",
    # 亚太其他
    "singtel", "starhub", "m1 limited", "myrepublic", "viewqwest",
    "maxis", "unifi", "time dotcom", "tm net", "celcom",
    "ais", "true internet", "3bb", "dtac tri", "ntc net",
    "viettel", "vnpt", "fpt telecom", "cmc telecom", "vinaphone",
    "pldt", "globe telecom", "converge ict", "sky broadband ph",
    "telkomsel", "indosat", "xl axiata", "biznet networks", "first media",
    # 拉美 / 土耳其 / 其他
    "claro", "vivo", "tim brasil", "oi internet", "net servicos",
    "turk telekom", "superonline", "ttk", "kablonet", "vodafone net",
    " kazakhtelecom", "beeline kz", "izatelecom",
    "bigpond", "iinet", "optus", "tpg internet", "aussie broadband",
    "spark nz", "vodafone nz", "2degrees", "orcon", "slingshot",
]

# ── 本项目补充 ──
RESIDENTIAL_ASNS.add(2527)                       # Sony Network Communications / So-net / nuro（截图中的家庭宽带样例）
RESIDENTIAL_NAME_PATTERNS.extend(["sony network", "nuro"])

COUNTRY_NAMES = {
    "HK": "香港", "TW": "台湾", "MO": "澳门",
    "CN": "中国大陆", "JP": "日本", "SG": "新加坡",
    "US": "美国", "KR": "韩国", "DE": "德国",
    "GB": "英国", "CA": "加拿大", "FR": "法国",
    "NL": "荷兰", "AU": "澳大利亚", "IN": "印度",
    "RU": "俄罗斯", "TR": "土耳其", "BR": "巴西",
    "ID": "印度尼西亚", "TH": "泰国", "VN": "越南",
    "MY": "马来西亚", "PH": "菲律宾", "AR": "阿根廷",
    "IT": "意大利", "ES": "西班牙", "SE": "瑞典",
    "CH": "瑞士", "PL": "波兰", "UA": "乌克兰",
    "FI": "芬兰", "IE": "爱尔兰", "MX": "墨西哥",
    "ZA": "南非", "AE": "阿联酋", "IL": "以色列",
    "RO": "罗马尼亚", "BG": "保加利亚", "NO": "挪威",
    "DK": "丹麦", "AT": "奥地利", "CZ": "捷克",
    "OTHER": "其他地区",
}

# 城市英→中映射（key 小写；覆盖节点常见落地城市，未命中则保留原文）
CITY_NAMES_ZH = {
    # 美国
    "new york": "纽约", "new york city": "纽约", "nyc": "纽约",
    "los angeles": "洛杉矶", "la": "洛杉矶",
    "san francisco": "旧金山", "san jose": "圣何塞", "san diego": "圣地亚哥",
    "seattle": "西雅图", "chicago": "芝加哥", "dallas": "达拉斯", "houston": "休斯顿",
    "austin": "奥斯汀", "miami": "迈阿密", "atlanta": "亚特兰大", "boston": "波士顿",
    "denver": "丹佛", "phoenix": "凤凰城", "las vegas": "拉斯维加斯",
    "washington": "华盛顿", "washington d.c.": "华盛顿", "washington dc": "华盛顿",
    "philadelphia": "费城", "detroit": "底特律", "minneapolis": "明尼阿波利斯",
    "portland": "波特兰", "salt lake city": "盐湖城", "charlotte": "夏洛特",
    "ashburn": "阿什本", "buffalo": "布法罗", "tampa": "坦帕",
    "santa clara": "圣克拉拉", "sunnyvale": "桑尼维尔", "mountain view": "山景城",
    "palo alto": "帕洛阿尔托", "fremont": "弗里蒙特", "irvine": "尔湾",
    "boardman": "博德曼", "hillsboro": "希尔斯伯勒", "council bluffs": "康瑟尔布拉夫斯",
    # 日本
    "tokyo": "东京", "osaka": "大阪", "yokohama": "横滨", "nagoya": "名古屋",
    "sapporo": "札幌", "fukuoka": "福冈", "kyoto": "京都", "kobe": "神户",
    "kawasaki": "川崎", "chiba": "千叶", "sendai": "仙台", "hiroshima": "广岛",
    # 韩国
    "seoul": "首尔", "busan": "釜山", "incheon": "仁川", "daegu": "大邱",
    "daejeon": "大田", "gwangju": "光州",
    # 港澳台 / 新加坡
    "hong kong": "香港", "taipei": "台北", "kaohsiung": "高雄", "taichung": "台中",
    "tainan": "台南", "hsinchu": "新竹", "macau": "澳门", "macao": "澳门",
    "singapore": "新加坡",
    # 英国 / 爱尔兰
    "london": "伦敦", "manchester": "曼彻斯特", "birmingham": "伯明翰",
    "edinburgh": "爱丁堡", "glasgow": "格拉斯哥", "liverpool": "利物浦",
    "bristol": "布里斯托尔", "leeds": "利兹", "dublin": "都柏林", "cork": "科克",
    # 德国 / 荷兰 / 比利时
    "berlin": "柏林", "frankfurt": "法兰克福", "munich": "慕尼黑", "hamburg": "汉堡",
    "cologne": "科隆", "dusseldorf": "杜塞尔多夫", "düsseldorf": "杜塞尔多夫",
    "stuttgart": "斯图加特", "nuremberg": "纽伦堡", "amsterdam": "阿姆斯特丹",
    "rotterdam": "鹿特丹", "the hague": "海牙", "utrecht": "乌得勒支",
    "brussels": "布鲁塞尔", "antwerp": "安特卫普",
    # 法国 / 意大利 / 西班牙 / 瑞士
    "paris": "巴黎", "marseille": "马赛", "lyon": "里昂", "milan": "米兰",
    "rome": "罗马", "turin": "都灵", "naples": "那不勒斯", "madrid": "马德里",
    "barcelona": "巴塞罗那", "valencia": "瓦伦西亚", "zurich": "苏黎世",
    "geneva": "日内瓦", "bern": "伯尔尼",
    # 北欧 / 东欧
    "stockholm": "斯德哥尔摩", "oslo": "奥斯陆", "copenhagen": "哥本哈根",
    "helsinki": "赫尔辛基", "warsaw": "华沙", "prague": "布拉格", "vienna": "维也纳",
    "budapest": "布达佩斯", "bucharest": "布加勒斯特", "sofia": "索非亚",
    "kyiv": "基辅", "kiev": "基辅", "moscow": "莫斯科",
    "saint petersburg": "圣彼得堡", "st. petersburg": "圣彼得堡",
    # 加拿大 / 澳大利亚 / 新西兰
    "toronto": "多伦多", "vancouver": "温哥华", "montreal": "蒙特利尔",
    "ottawa": "渥太华", "calgary": "卡尔加里", "sydney": "悉尼",
    "melbourne": "墨尔本", "brisbane": "布里斯班", "perth": "珀斯",
    "adelaide": "阿德莱德", "auckland": "奥克兰", "wellington": "惠灵顿",
    # 东南亚 / 南亚
    "bangkok": "曼谷", "ho chi minh city": "胡志明市", "hanoi": "河内",
    "jakarta": "雅加达", "kuala lumpur": "吉隆坡", "manila": "马尼拉",
    "mumbai": "孟买", "delhi": "德里", "new delhi": "新德里",
    "bangalore": "班加罗尔", "bengaluru": "班加罗尔", "chennai": "钦奈",
    "hyderabad": "海得拉巴",
    # 中东 / 其他
    "dubai": "迪拜", "abu dhabi": "阿布扎比", "istanbul": "伊斯坦布尔",
    "ankara": "安卡拉", "tel aviv": "特拉维夫", "jerusalem": "耶路撒冷",
    "sao paulo": "圣保罗", "são paulo": "圣保罗", "rio de janeiro": "里约热内卢",
    "buenos aires": "布宜诺斯艾利斯", "mexico city": "墨西哥城",
    "johannesburg": "约翰内斯堡", "cape town": "开普敦",
    # 香港区名（HK 节点命名不展示城市，映射仅作备用）
    "mong kok": "旺角", "mongkok": "旺角", "central": "中环", "tsim sha tsui": "尖沙咀",
    "kwun tong": "观塘", "sha tin": "沙田", "tuen mun": "屯门", "yuen long": "元朗",
    "tai po": "大埔", "sai wan": "西环", "causeway bay": "铜锣湾", "wan chai": "湾仔",
    # 台湾
    "nangang": "南港", "nan gang": "南港", "banqiao": "板桥", "zhonghe": "中和",
    "taoyuan": "桃园", "keelung": "基隆", "new taipei": "新北", "hualien": "花莲",
    # 用户反馈补充
    "flower mound": "弗劳尔芒德", "flowermound": "弗劳尔芒德",
    "ban wang man": "万曼村", "frankfurt am main": "法兰克福",
    "minamishinagawa": "南品川", "minami-shinagawa": "南品川",
    "falkenstein": "法尔肯施泰因",
    "north kansas city": "北堪萨斯城",
    "bear": "贝尔",
    "beauharnois": "博阿尔努瓦",
    "charlottesville": "夏洛茨维尔",
    "staten island": "斯塔滕岛",
    "kansas city": "堪萨斯城",
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
    no_exit = [r for r in results if not r.get("exit_ip")]
    if no_exit:
        if len(results) >= 10 and len(no_exit) / len(results) > NO_EXIT_MAX_RATIO:
            print(f"[!] {len(no_exit)}/{len(results)} 个存活节点取不到出口 IP，疑似探测服务故障，本次不淘汰 "
                  f"(这些节点只会归入普通)")
        else:
            results = [r for r in results if r.get("exit_ip")]
            bump("no_exit_ip", len(no_exit))
            print(f"[*] 取不到出口 IP 的节点已淘汰: {len(no_exit)} 个，剩余 {len(results)}")
    return results


# ══════════════════════════════════════════════════════════════════
# 分类：家宽 / 原生 / 普通
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
        res = {"country": None, "registered": None, "asn": None, "asn_org": ""}
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
                res["asn"] = rec.get("autonomous_system_number")
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


def _make_matcher(patterns):
    """短词(<=4字符)按单词边界匹配，长词按子串匹配，避免 colo→colombia、ais→mais 之类误判。"""
    clean = sorted({p.strip().lower() for p in patterns if p and p.strip()})
    short = [p for p in clean if len(p) <= 4]
    long_ = [p for p in clean if len(p) > 4]
    rx = (re.compile(r"(?<![a-z0-9])(?:" + "|".join(re.escape(p) for p in short) + r")(?![a-z0-9])")
          if short else None)

    def match(text: str) -> bool:
        t = (text or "").lower()
        return bool((rx and rx.search(t)) or any(k in t for k in long_))
    return match


_IDC_MATCH = _make_matcher(IDC_NAME_PATTERNS)
_RES_MATCH = _make_matcher(RESIDENTIAL_NAME_PATTERNS)
_ALL_CDN_NETS = CLOUDFLARE_IP_NETWORKS + CDN_IP_NETWORKS_EXTRA


def _asn_int(v):
    if isinstance(v, int):
        return v
    m = re.match(r"\s*(?:AS)?(\d+)", str(v or ""), re.I)
    return int(m.group(1)) if m else None


def get_rdns(ip: str) -> str:
    try:
        return socket.gethostbyaddr(ip)[0].lower()
    except (OSError, UnicodeError):
        return ""


def classify_network_type(ip: str, asn_int, org_text: str, rec: dict, rdns: str = ""):
    """网络类型识别（沿用原作者的优先级）。
    返回 (net_type, confidence)，net_type ∈ cdn / datacenter / mobile / residential / unknown
    优先级: CDN 网段 > ip-api(hosting / proxy / mobile) > ASN 名单 > 名称关键词 > rDNS"""
    try:
        ip_obj = ipaddress.ip_address(ip)
    except ValueError:
        return "unknown", 0
    for net in _ALL_CDN_NETS:
        if ip_obj in net:
            return "cdn", 100
    rec = rec or {}
    if rec.get("hosting"):
        return "datacenter", 90
    if rec.get("proxy"):          # 机房收购家宽段、伪装 DSL 的典型形态，硬否决家宽
        return "datacenter", 88
    if rec.get("mobile"):
        return "mobile", 85
    if asn_int:
        if asn_int in DATACENTER_ASNS:
            return "datacenter", 80
        if asn_int in RESIDENTIAL_ASNS:
            return "residential", 82
    if org_text:
        if _IDC_MATCH(org_text):
            return "datacenter", 70
        if _RES_MATCH(org_text):
            return "residential", 70
    if rdns:
        if _IDC_MATCH(rdns):
            return "datacenter", 60
        if _RES_MATCH(rdns):
            return "residential", 60
    return "unknown", 30


def native_check(geo_cc, registered, echo_cc, ipapi_cc) -> bool:
    """原生 IP：注册地国家 == 使用地国家，且其它地理来源与之不矛盾（否则按「广播 IP」处理）。"""
    if not geo_cc or not registered or geo_cc != registered:
        return False
    for other in (echo_cc, ipapi_cc):
        if other and other != geo_cc:
            return False
    return True


_RDAP_CACHE = {}


def rdap_country(ip: str):
    """向 RIR(RDAP) 查询 IP 段登记国家，即「注册地」。查不到返回 None。"""
    if ip in _RDAP_CACHE:
        return _RDAP_CACHE[ip]
    cc = None
    try:
        r = DIRECT_SESSION.get(f"https://rdap.org/ip/{ip}", timeout=12,
                               headers={"Accept": "application/rdap+json, application/json"})
        if r.status_code == 200:
            c = str((r.json() or {}).get("country") or "").upper()
            cc = c if re.fullmatch(r"[A-Z]{2}", c) else None
    except (requests.RequestException, ValueError):
        pass
    _RDAP_CACHE[ip] = cc
    return cc


def rdap_lookup_many(ips: list) -> dict:
    ips = ips[:RDAP_MAX_IPS]
    if not ips:
        return {}
    print(f"[*] RDAP 查询 {len(ips)} 个出口 IP 的登记国家(注册地) ...")
    out = {}
    with ThreadPoolExecutor(RDAP_WORKERS) as ex:
        futs = {ex.submit(rdap_country, ip): ip for ip in ips}
        for fut in as_completed(futs):
            try:
                out[futs[fut]] = fut.result()
            except Exception:  # noqa: BLE001
                out[futs[fut]] = None
    print(f"    RDAP 有结果: {sum(1 for v in out.values() if v)}/{len(ips)}")
    return out


_RISK_CACHE = {}


def scamalytics_fraud_score(ip: str) -> int:
    """Scamalytics 风控评分 0-100，越高越脏（抓取网页，方式同原作者；可能被拦截或改版）。失败返回 -1。"""
    if ip in _RISK_CACHE:
        return _RISK_CACHE[ip]
    score = -1
    for _ in range(2):
        try:
            r = DIRECT_SESSION.get(f"https://scamalytics.com/ip/{ip}", timeout=12)
            if r.status_code == 200:
                m = re.search(r"Fraud Score:\s*(\d+)", r.text)
                if m:
                    score = int(m.group(1))
                break
        except requests.RequestException:
            pass
        time.sleep(1.5)
    _RISK_CACHE[ip] = score
    return score


def risk_select(cands: list, cap: int, label: str) -> list:
    """按延迟从低到高取节点，淘汰风控值 > MAX_RISK_SCORE 的；有上限时按需分批查询，淘汰后继续往后补满。"""
    if not ENABLE_RISK_FILTER:
        return cands[:cap] if cap > 0 else list(cands)
    picked, pos, rejected, unknown = [], 0, 0, 0
    while pos < len(cands) and (cap <= 0 or len(picked) < cap):
        size = RISK_BATCH if cap <= 0 else max(20, cap - len(picked))
        chunk = cands[pos:pos + size]
        pos += len(chunk)
        ips = sorted({c["look_ip"] for c in chunk if c["look_ip"] not in _RISK_CACHE})
        if ips:
            with ThreadPoolExecutor(RISK_WORKERS) as ex:
                _RISK_CACHE.update(zip(ips, ex.map(scamalytics_fraud_score, ips)))
        for c in chunk:
            sc = _RISK_CACHE.get(c["look_ip"], -1)
            c["risk"] = sc
            if sc > MAX_RISK_SCORE:
                c["risk_drop"] = True
                rejected += 1
                continue
            if sc < 0:
                unknown += 1
                if DROP_RISK_UNKNOWN:
                    c["risk_drop"] = True
                    continue
            picked.append(c)
            if cap > 0 and len(picked) >= cap:
                break
    print(f"    {label}: 保留 {len(picked)} | 风控值>{MAX_RISK_SCORE} 淘汰 {rejected} | 风控查询失败 {unknown}")
    return picked


def classify_results(results: list):
    """每个节点只属于一类：家宽 > 原生 > 普通，互不重叠。
       家宽 = 家庭宽带 IP（含移动网络）且是原生 IP，无需额外核验
       原生 = 非家宽，且是原生 IP（注册地国家 == 使用地国家，典型如机房原生）
       普通 = 其余（含「广播 IP」，包括家庭宽带但广播的 IP）"""
    print("[*] 分类: 家宽 / 原生 / 普通 ...")

    if DEDUP_BY_EXIT_IP:                    # 先去重，减少后续所有外部查询
        best = {}
        for r in results:
            key = r.get("exit_ip") or ("srv", r["ip"], r["port"])
            if key not in best or r["latency_ms"] < best[key]["latency_ms"]:
                best[key] = r
        if len(best) != len(results):
            print(f"[*] 相同出口 IP 去重: {len(results)} → {len(best)}")
        results = list(best.values())

    geo = GeoDB()
    if not geo.country:
        print("[!] 没有 GeoLite2-Country，无法判断原生 IP (全部按普通处理)")

    ip_info = {}
    if ENABLE_IP_API:
        ips = sorted({r["exit_ip"] for r in results if r.get("exit_ip") and is_public_ip(r["exit_ip"])})
        if ips:
            ip_info = ip_api_batch_lookup(ips[:IP_API_MAX_IPS])

    items = []
    for r in results:
        look_ip = r.get("exit_ip") or r["ip"]
        g = geo.lookup(look_ip)
        rec = ip_info.get(r.get("exit_ip"), {})
        asn = _asn_int(rec.get("as")) or g["asn"]
        org_text = rec.get("asname") or rec.get("org") or g["asn_org"] or ""
        net_type, conf = classify_network_type(look_ip, asn, org_text, rec)
        ipapi_cc = str(rec.get("countryCode") or "").upper() or None
        actual = (g["country"] or r.get("exit_country") or ipapi_cc or "OTHER").upper()
        if not re.fullmatch(r"[A-Z]{2}", actual):
            actual = "OTHER"
        # 城市：有有效值才写入，空/unknown 一律不写（命名时回退到仅国家）
        city_raw = str(rec.get("city") or "").strip()
        city = city_raw if city_raw and city_raw.lower() not in ("unknown", "n/a", "-", "null") else ""
        region_raw = str(rec.get("regionName") or "").strip()
        region = region_raw if region_raw and region_raw.lower() not in ("unknown", "n/a", "-", "null") else ""
        items.append({
            "raw": r["raw"], "outbound": r["outbound"], "server": r["server"], "port": r["port"],
            "proto": r["proto"], "ip": r["ip"], "exit_ip": r.get("exit_ip"), "look_ip": look_ip,
            "latency_ms": r["latency_ms"], "country": actual, "city": city, "region": region,
            "asn": asn, "org_text": org_text,
            "net_type": net_type, "confidence": conf, "geo": g, "echo_cc": r.get("exit_country"),
            "ipapi_cc": ipapi_cc, "registered": None, "native": False, "tag": "",
            "risk": None, "risk_drop": False,
        })

    # rDNS 兜底：仅对「仍无法判断」的 IP
    unknown = [i for i in items if i["net_type"] == "unknown" and i["exit_ip"]][:600]
    if unknown:
        with ThreadPoolExecutor(32) as ex:
            for it, rd in zip(unknown, ex.map(lambda i: get_rdns(i["look_ip"]), unknown)):
                if rd:
                    it["rdns"] = rd
                    it["net_type"], it["confidence"] = classify_network_type(
                        it["look_ip"], it["asn"], it["org_text"], ip_info.get(it["exit_ip"], {}), rd)

    # 原生判断：注册地 = RDAP 登记国家，查不到时用 GeoLite2 registered_country
    rdap = {}
    if ENABLE_RDAP:
        rdap = rdap_lookup_many(sorted({i["look_ip"] for i in items if is_public_ip(i["look_ip"])}))
    for i in items:
        i["registered"] = rdap.get(i["look_ip"]) or i["geo"]["registered"]
        i["native"] = (bool(i["exit_ip"]) and i["net_type"] != "cdn"
                       and native_check(i["geo"]["country"], i["registered"], i["echo_cc"], i["ipapi_cc"]))
        # 家庭宽带 / 移动网络 + 广播 IP → 普通，所以家宽必须同时是原生
        i["residential"] = i["net_type"] in ("residential", "mobile") and i["confidence"] >= 60 and i["native"]
        i["native_final"] = i["native"] and not i["residential"]
        i["tag"] = ("移动家宽" if i["net_type"] == "mobile" else "家宽") if i["residential"] else (
            "原生" if i["native_final"] else "")

    print("[*] 网络类型: " + " | ".join(f"{t}={sum(1 for i in items if i['net_type'] == t)}"
          for t in ("residential", "mobile", "datacenter", "cdn", "unknown"))
          + f" | 原生={sum(1 for i in items if i['native'])}")

    items.sort(key=lambda x: x["latency_ms"])
    residential = [i for i in items if i["residential"]]
    native = [i for i in items if i["native_final"]]
    normal = [i for i in items if not i["residential"] and not i["native_final"]]
    if ENABLE_RISK_FILTER:
        print(f"[*] 风控值过滤: 淘汰风控值 > {MAX_RISK_SCORE} 的节点 (家宽/原生/普通均适用) ...")
    residential = risk_select(residential, MAX_RESIDENTIAL, "家宽")
    native = risk_select(native, MAX_NATIVE, "原生")
    selected_normal = risk_select(normal, MAX_NORMAL, "普通")
    queried = [i for i in items if i["risk"] is not None]
    if len(queried) >= 10 and sum(1 for i in queried if i["risk"] < 0) / len(queried) > 0.5:
        print("[!] 超过一半的风控查询失败 (可能被 scamalytics 拦截)，本次风控过滤基本没有生效")
    print(f"[*] 精选结果: 家宽 {len(residential)} | 原生 {len(native)} | "
          f"普通精选 {len(selected_normal)} (候选 {len(normal)}) | 总计 "
          f"{len(residential) + len(native) + len(selected_normal)}")
    if DEBUG:
        os.makedirs(os.path.join(OUTPUT_DIR, "debug"), exist_ok=True)
        write_text(os.path.join(OUTPUT_DIR, "debug", "classification.json"), json.dumps([{
            "exit_ip": i["exit_ip"], "country": i["country"], "city": i.get("city"), "region": i.get("region"),
            "asn": i["asn"], "org": i["org_text"],
            "rdns": i.get("rdns"), "net_type": i["net_type"], "confidence": i["confidence"],
            "geo_country": i["geo"]["country"], "mm_registered": i["geo"]["registered"],
            "registered_used": i["registered"], "echo_country": i["echo_cc"], "ipapi_country": i["ipapi_cc"],
            "native": i["native"], "risk": i["risk"], "risk_dropped": i["risk_drop"],
            "result": i["tag"] or "普通",
        } for i in items], indent=1, ensure_ascii=False))
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

def city_to_zh(city: str) -> str:
    """将 ip-api 返回的英文城市名转为中文；未命中映射则原样返回。"""
    c = (city or "").strip()
    if not c:
        return ""
    return CITY_NAMES_ZH.get(c.lower(), c)


def make_node_name(item: dict, idx: int) -> str:
    """中文命名：国旗 + 国家[-城市] + 序号 +（家宽/原生）标签。
    香港不展示区名，只写「香港」；序号按国家自增；无城市时不填「未知」。
    不再附加 NAME_SUFFIX。"""
    cc = item["country"]
    place = COUNTRY_NAMES.get(cc, cc)
    # 香港：不细分区名，统一「香港」
    if cc != "HK":
        city_zh = city_to_zh(item.get("city") or "")
        if city_zh:
            place = f"{place}-{city_zh}"
    tag = f" ({item['tag']})" if item.get("tag") else ""
    return f"{get_country_flag(cc)} {place} {idx:02d}{tag}"


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

- **分类互斥**: 每个节点只属于「家宽 / 原生 / 普通」之一，优先级 家宽 > 原生。
- **节点命名**: 中文国家名，有城市时用「国家-城市」（如「日本-东京」）；香港统一写「香港」不展示区名；映射表未覆盖的城市保留英文原文；序号按国家自增。
- **风控值过滤**: 风控值超过 {MAX_RISK_SCORE} 的节点一律淘汰 (Scamalytics 评分，与检测网站的风控值数据源不同，数值不能直接等同)。
- **原生 IP**: 注册地国家与实际使用地国家一致 (注册地取 RDAP 登记国家，查不到用 GeoLite2；多个地理库互相矛盾则不算)。「广播 IP」归普通。
- **家宽**: 家庭宽带 IP（含移动网络）且为原生 IP，识别沿用原作者方案；家庭宽带但广播的 IP 归普通。
- 免费节点来自公开订阅源，**不可信**，可能嗅探或篡改流量，请勿用于登录银行、邮箱等敏感账号。
"""
    write_text(os.path.join(BASEDIR, "README.md"), text)


# ══════════════════════════════════════════════════════════════════
# 主流程
# ══════════════════════════════════════════════════════════════════

def print_diagnostics():
    keys = ["parse_fail", "duplicate", "dropped_insecure", "dns_fail", "non_public_ip", "port_closed",
            "start_fail", "probe_fail", "no_exit_ip", "too_slow", "test_exception"]
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
