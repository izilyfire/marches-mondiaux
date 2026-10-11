#!/usr/bin/env python3
"""
IZILY FIRE — Relais « Marchés mondiaux »
=========================================
Exécuté toutes les 10 minutes par GitHub Actions (voir marches.yml).
Récupère les cours (Yahoo Finance, sans clé) et les actualités (flux RSS
français), puis écrit un fichier JSON unique que la page lit directement :

    https://raw.githubusercontent.com/<compte>/<depot>/data/marches.json

Format du JSON :
    {
      "updated": "2026-10-11T03:20:00Z",
      "q": { "SPX": {"p": 5800.1, "c": 0.45, "t": 1760000000, "u": "USD", "s": [..22 clôtures..]}, ... },
      "news": [ {"title": "...", "url": "https://...", "src": "Le Monde", "ts": 1760000000, "img": "https://..."} ],
      "errors": ["JSE", ...]
    }
    p = dernier cours · c = variation du jour en % · t = heure du cours (epoch)
    u = devise · s = clôtures quotidiennes sur ~1 mois (mini-graphique)

AUCUNE valeur inventée : un actif sans réponse garde son DERNIER cours réel
connu (avec son heure d'origine) pendant 5 jours maximum, puis disparaît.
Les identifiants (SPX, EURUSD, ...) doivent rester identiques à ceux de la page.
"""
import json
import os
import re
import sys
import time
import urllib.error
import urllib.request
import xml.etree.ElementTree as ET
from datetime import datetime, timezone
from email.utils import parsedate_to_datetime
from html import unescape

YAHOO_BASE = os.environ.get("YAHOO_BASE", "https://query1.finance.yahoo.com").rstrip("/")
YAHOO_ALT = os.environ.get("YAHOO_ALT", "https://query2.finance.yahoo.com").rstrip("/")
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/124.0 Safari/537.36")
MAX_CARRY_S = 5 * 24 * 3600  # on garde un ancien cours réel 5 jours maximum
SPARK_POINTS = 22

# identifiant de la page -> symbole Yahoo Finance
SYMBOLS = {
    # Indices
    "SPX": "^GSPC", "NDX": "^NDX", "DJI": "^DJI", "RUT": "^RUT",
    "DAX": "^GDAXI", "CAC": "^FCHI", "FTSE": "^FTSE", "STOXX50": "^STOXX50E",
    "NKY": "^N225", "HSI": "^HSI", "SHC": "000001.SS", "ASX": "^AXJO",
    "BVSP": "^BVSP", "JSE": "^J200.JO", "EGX30": "^CASE30",
    # Devises
    "EURUSD": "EURUSD=X", "USDJPY": "JPY=X", "GBPUSD": "GBPUSD=X",
    "USDCHF": "CHF=X", "AUDUSD": "AUDUSD=X", "USDCAD": "CAD=X",
    # Matières premières
    "WTI": "CL=F", "BRENT": "BZ=F", "GOLD": "GC=F", "SILVER": "SI=F",
    "COPPER": "HG=F", "WHEAT": "ZW=F", "NATGAS": "NG=F",
    # Cryptos (secours : la page interroge CoinGecko en direct)
    "BTC": "BTC-USD", "ETH": "ETH-USD", "BNB": "BNB-USD",
    "SOL": "SOL-USD", "XRP": "XRP-USD", "DOGE": "DOGE-USD",
    # Actions
    "AAPL": "AAPL", "MSFT": "MSFT", "NVDA": "NVDA", "AMZN": "AMZN",
    "TSLA": "TSLA", "GOOGL": "GOOGL", "MC": "MC.PA", "TTE": "TTE.PA",
    "AIR": "AIR.PA", "SAP": "SAP.DE", "ASML": "ASML.AS", "7203": "7203.T",
}

# Flux RSS (en français). Un flux en panne est simplement ignoré.
FEEDS = [
    ("Le Monde", "https://www.lemonde.fr/economie/rss_full.xml"),
    ("Les Échos", "https://services.lesechos.fr/rss/les-echos-finance-marches.xml"),
    ("BFM Business", "https://www.bfmtv.com/rss/economie/"),
    ("Investing.com", "https://fr.investing.com/rss/news.rss"),
]
NEWS_MAX = 14
NEWS_PER_FEED = 6


def log(*a):
    print(*a, file=sys.stderr, flush=True)


def http_get(url, tries=3, timeout=20):
    """GET avec quelques tentatives ; renvoie des octets ou None."""
    last = None
    for i in range(tries):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept": "*/*"})
            with urllib.request.urlopen(req, timeout=timeout) as r:
                return r.read()
        except urllib.error.HTTPError as e:
            last = "HTTP %s" % e.code
            if e.code in (400, 401, 403, 404):
                break
        except Exception as e:  # réseau, délai dépassé...
            last = repr(e)
        time.sleep(1.5 * (i + 1))
    log("  échec", url, last)
    return None


# --------------------------------------------------------------------------
# Cours (Yahoo Finance : endpoint « chart », sans clé)
# --------------------------------------------------------------------------
def parse_chart(payload):
    """Transforme la réponse Yahoo « chart » en {p, c, t, u, s} ou None."""
    try:
        res = payload["chart"]["result"][0]
        meta = res["meta"]
    except (KeyError, IndexError, TypeError):
        return None
    ts = res.get("timestamp") or []
    try:
        closes = res["indicators"]["quote"][0].get("close") or []
    except (KeyError, IndexError, TypeError):
        closes = []
    pairs = [(t, c) for t, c in zip(ts, closes) if isinstance(c, (int, float))]

    price = meta.get("regularMarketPrice")
    if not isinstance(price, (int, float)):
        price = pairs[-1][1] if pairs else None
    if price is None:
        return None

    # Clôture de la veille : la dernière barre quotidienne est-elle celle du jour ?
    t_now = meta.get("regularMarketTime")
    off = meta.get("gmtoffset") or 0
    prev = None
    if pairs and isinstance(t_now, (int, float)):
        same_day = (pairs[-1][0] + off) // 86400 == (t_now + off) // 86400
        if same_day:
            prev = pairs[-2][1] if len(pairs) >= 2 else meta.get("chartPreviousClose")
        else:
            prev = pairs[-1][1]
    elif pairs:
        prev = pairs[-1][1]
    if not isinstance(prev, (int, float)) or prev == 0:
        prev = meta.get("chartPreviousClose") or meta.get("previousClose")

    out = {"p": round(float(price), 6)}
    if isinstance(prev, (int, float)) and prev != 0:
        out["c"] = round((float(price) / float(prev) - 1) * 100, 4)
    if isinstance(t_now, (int, float)):
        out["t"] = int(t_now)
    if meta.get("currency"):
        out["u"] = meta["currency"]
    serie = [round(c, 4) for _, c in pairs][-SPARK_POINTS:]
    if len(serie) >= 2:
        out["s"] = serie
    return out


def fetch_quote(symbol):
    path = "/v8/finance/chart/%s?interval=1d&range=1mo" % urllib.request.quote(symbol, safe="")
    for base in (YAHOO_BASE, YAHOO_ALT):
        raw = http_get(base + path, tries=2)
        if raw:
            try:
                q = parse_chart(json.loads(raw.decode("utf-8", "replace")))
            except ValueError:
                q = None
            if q:
                return q
    return None


def previous_file(path_out):
    """Ancien JSON (fichier local, sinon branche data du dépôt) pour ne jamais
    afficher un trou si Yahoo ne répond pas pour un symbole."""
    if os.path.exists(path_out):
        try:
            with open(path_out, encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            pass
    repo = os.environ.get("GITHUB_REPOSITORY")
    if repo:
        raw = http_get("https://raw.githubusercontent.com/%s/data/marches.json" % repo, tries=1, timeout=15)
        if raw:
            try:
                return json.loads(raw.decode("utf-8"))
            except ValueError:
                pass
    return {}


# --------------------------------------------------------------------------
# Actualités (flux RSS)
# --------------------------------------------------------------------------
MEDIA_NS = "{http://search.yahoo.com/mrss/}"


def clean(text):
    text = re.sub(r"<[^>]+>", " ", unescape(text or ""))
    return re.sub(r"\s+", " ", text).strip()


def safe_url(u):
    u = (u or "").strip()
    return u if re.match(r"^https?://", u, re.I) else ""


def parse_rss(xml_bytes, source, limit=NEWS_PER_FEED):
    try:
        root = ET.fromstring(xml_bytes)
    except ET.ParseError:
        return []
    out = []
    for item in root.iter("item"):
        title = clean(item.findtext("title"))
        link = safe_url(item.findtext("link"))
        if not title or not link:
            continue
        ts = 0
        d = item.findtext("pubDate")
        if d:
            try:
                ts = int(parsedate_to_datetime(d).timestamp())
            except (TypeError, ValueError):
                ts = 0
        img = ""
        for tag in ("content", "thumbnail"):
            el = item.find(MEDIA_NS + tag)
            if el is not None and el.get("url"):
                img = safe_url(el.get("url"))
                break
        if not img:
            enc = item.find("enclosure")
            if enc is not None and (enc.get("type") or "").startswith("image"):
                img = safe_url(enc.get("url"))
        news = {"title": title[:220], "url": link, "src": source, "ts": ts}
        if img:
            news["img"] = img
        out.append(news)
        if len(out) >= limit:
            break
    return out


def fetch_news():
    allnews = []
    for source, url in FEEDS:
        raw = http_get(url, tries=2, timeout=20)
        if raw:
            got = parse_rss(raw, source)
            log("  flux", source, "->", len(got), "articles")
            allnews += got
    seen, uniq = set(), []
    for n in sorted(allnews, key=lambda x: x["ts"], reverse=True):
        key = n["title"].lower()[:80]
        if key not in seen:
            seen.add(key)
            uniq.append(n)
    return uniq[:NEWS_MAX]


# --------------------------------------------------------------------------
def main(path_out):
    os.makedirs(os.path.dirname(os.path.abspath(path_out)), exist_ok=True)
    prev = previous_file(path_out)
    prev_q = prev.get("q", {}) if isinstance(prev, dict) else {}
    now = int(time.time())

    quotes, errors = {}, []
    for ident, symbol in SYMBOLS.items():
        q = fetch_quote(symbol)
        if q is None:
            old = prev_q.get(ident)
            if isinstance(old, dict) and now - int(old.get("t", 0) or 0) < MAX_CARRY_S and "p" in old:
                quotes[ident] = old  # dernier cours réel connu, heure d'origine conservée
            errors.append(ident)
            log("  sans réponse :", ident, symbol)
        else:
            quotes[ident] = q
        time.sleep(0.35)  # politesse envers Yahoo

    fresh = len(SYMBOLS) - len(errors)
    news = fetch_news()
    if not news and isinstance(prev, dict):
        news = prev.get("news", [])  # on garde les dernières actualités connues

    if fresh == 0:
        log("Aucun cours récupéré : le fichier précédent est conservé.")
        sys.exit(1)

    data = {
        "updated": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "q": quotes,
        "news": news,
        "errors": errors,
    }
    with open(path_out, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, separators=(",", ":"))
    carried = len([e for e in errors if e in quotes])
    log("OK : %d cours frais, %d repris, %d actualités" % (fresh, carried, len(news)))


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "out/marches.json")
