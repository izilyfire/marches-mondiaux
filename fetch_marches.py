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
      "pol": { "FED": {"lo": 4.0, "hi": 4.25, "since": "2025-12-10", "asof": "2026-10-09"},
               "BCE": {"dfr": 2.0, "mrr": 2.15, "since": "2025-06-11", "asof": "2026-10-09"} },
      "news": [ {"title": "...", "url": "https://...", "src": "Le Monde", "ts": 1760000000, "img": "https://..."} ],
      "errors": ["JSE", ...]
    }
    p = dernier cours · c = variation du jour en % · t = heure du cours (epoch)
    u = devise · s = clôtures quotidiennes sur ~1 mois (mini-graphique)
    Taux 10 ans (US10, FR10...) : p = rendement en %, d = variation en points de %,
    k = "y", m = 1 si moyenne mensuelle (secours FRED), dt = date de la donnée.
    pol = taux directeurs (source : FRED, séries FED et BCE).

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
import csv
import io
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from html import unescape

YAHOO_BASE = os.environ.get("YAHOO_BASE", "https://query1.finance.yahoo.com").rstrip("/")
YAHOO_ALT = os.environ.get("YAHOO_ALT", "https://query2.finance.yahoo.com").rstrip("/")
STOOQ_BASE = os.environ.get("STOOQ_BASE", "https://stooq.com").rstrip("/")
FRED_BASE = os.environ.get("FRED_BASE", "https://fred.stlouisfed.org").rstrip("/")
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
    "WTI": "CL=F", "BRENT": "BZ=F", "NATGAS": "NG=F", "TTF": "TTF=F", "COAL": "MTF=F",
    "GOLD": "GC=F", "SILVER": "SI=F", "COPPER": "HG=F", "PALLAD": "PA=F",
    "WHEAT": "ZW=F", "SUGAR": "SB=F", "COFFEE": "KC=F", "CORN": "ZC=F",
    # Indice de la peur
    "VIX": "^VIX",
    # Cryptos (secours : la page interroge CoinGecko en direct)
    "BTC": "BTC-USD", "ETH": "ETH-USD", "BNB": "BNB-USD",
    "SOL": "SOL-USD", "XRP": "XRP-USD", "DOGE": "DOGE-USD",
    # Actions
    "AAPL": "AAPL", "MSFT": "MSFT", "NVDA": "NVDA", "AMZN": "AMZN",
    "TSLA": "TSLA", "GOOGL": "GOOGL", "MC": "MC.PA", "TTE": "TTE.PA",
    "AIR": "AIR.PA", "SAP": "SAP.DE", "ASML": "ASML.AS", "7203": "7203.T",
}

# Taux 10 ans : (stooq, FRED quotidien, FRED mensuel, Yahoo)
YIELDS = {
    "US10": ("10usy.b", "DGS10", "IRLTLT01USM156N", "^TNX"),
    "FR10": ("10fry.b", None, "IRLTLT01FRM156N", None),
    "DE10": ("10dey.b", None, "IRLTLT01DEM156N", None),
    "IT10": ("10ity.b", None, "IRLTLT01ITM156N", None),
    "ES10": ("10esy.b", None, "IRLTLT01ESM156N", None),
    "JP10": ("10jpy.b", None, "IRLTLT01JPM156N", None),
    "UK10": ("10uky.b", None, "IRLTLT01GBM156N", None),
}
# Taux directeurs (FRED) : FED = fourchette cible haute/basse ; BCE = dépôt / refinancement
POLICY = {"FED": ("DFEDTARL", "DFEDTARU"), "BCE": ("ECBDFR", "ECBMRRFR")}

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
# Taux 10 ans et taux directeurs (Stooq / FRED, sans clé)
# --------------------------------------------------------------------------
def _num(x):
    try:
        v = float(str(x).strip())
        return v if v == v else None
    except ValueError:
        return None


def stooq_series(sym):
    """[(date, clôture)] des ~45 derniers jours, ou []."""
    d2 = datetime.now(timezone.utc).date()
    d1 = d2 - timedelta(days=45)
    url = "%s/q/d/l/?s=%s&i=d&d1=%s&d2=%s" % (STOOQ_BASE, sym, d1.strftime("%Y%m%d"), d2.strftime("%Y%m%d"))
    raw = http_get(url, tries=2)
    if not raw:
        return []
    rows = list(csv.reader(io.StringIO(raw.decode("utf-8", "replace"))))
    if not rows or [c.strip().lower() for c in rows[0][:1]] != ["date"]:
        return []
    out = []
    for r in rows[1:]:
        v = _num(r[4]) if len(r) > 4 else None
        if v is not None:
            out.append((r[0], v))
    return out


def fred_series(series_id, days=60):
    """[(date, valeur)] ; ignore les valeurs manquantes (« . »)."""
    start = (datetime.now(timezone.utc).date() - timedelta(days=days)).isoformat()
    raw = http_get("%s/graph/fredgraph.csv?id=%s&cosd=%s" % (FRED_BASE, series_id, start), tries=2)
    if not raw:
        return []
    rows = list(csv.reader(io.StringIO(raw.decode("utf-8", "replace"))))
    out = []
    for r in rows[1:]:
        v = _num(r[1]) if len(r) > 1 else None
        if v is not None and re.match(r"^\d{4}-\d{2}-\d{2}$", r[0]):
            out.append((r[0], v))
    return out


def day_ts(d):
    try:
        return int(datetime.strptime(d, "%Y-%m-%d").replace(hour=16, tzinfo=timezone.utc).timestamp())
    except ValueError:
        return int(time.time())


def yield_quote(pairs, monthly=False):
    if not pairs:
        return None
    vals = [v for _, v in pairs]
    q = {"p": round(vals[-1], 4), "t": day_ts(pairs[-1][0]), "k": "y", "dt": pairs[-1][0]}
    if len(vals) >= 2:
        q["d"] = round(vals[-1] - vals[-2], 4)
    if len(vals) >= 3:
        q["s"] = [round(v, 4) for v in vals][-SPARK_POINTS:]
    if monthly:
        q["m"] = 1
    return q


def fetch_yield(ident):
    stooq, fred_d, fred_m, yahoo = YIELDS[ident]
    q = yield_quote(stooq_series(stooq))
    if q:
        return q
    if fred_d:
        q = yield_quote(fred_series(fred_d))
        if q:
            return q
    if yahoo:
        y = fetch_quote(yahoo)
        if y and y.get("p") is not None:
            p = y["p"] / 10.0 if y["p"] > 25 else y["p"]  # ^TNX : parfois en dixièmes
            k = (10.0 if y["p"] > 25 else 1.0)
            out = {"p": round(p, 4), "t": y.get("t", int(time.time())), "k": "y", "dt": datetime.now(timezone.utc).date().isoformat()}
            if "c" in y:
                out["d"] = round(p - p / (1 + y["c"] / 100.0), 4)
            if y.get("s"):
                out["s"] = [round(v / k, 4) for v in y["s"]]
            return out
    return yield_quote(fred_series(fred_m, days=200), monthly=True)


def last_change(pairs):
    """Date à laquelle la valeur actuelle est entrée en vigueur (ou None)."""
    if not pairs:
        return None
    cur = pairs[-1][1]
    for i in range(len(pairs) - 1, 0, -1):
        if abs(pairs[i - 1][1] - cur) > 1e-9:
            return pairs[i][0]
    return None


def fetch_policy():
    out = {}
    for name, (a, b) in POLICY.items():
        pa, pb = fred_series(a, days=900), fred_series(b, days=900)
        if not pa or not pb:
            continue
        if name == "FED":
            out[name] = {"lo": pa[-1][1], "hi": pb[-1][1], "since": last_change(pb), "asof": pb[-1][0]}
        else:
            out[name] = {"dfr": pa[-1][1], "mrr": pb[-1][1], "since": last_change(pa), "asof": pa[-1][0]}
    return out


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

    for ident in YIELDS:
        q = fetch_yield(ident)
        if q is None:
            old = prev_q.get(ident)
            if isinstance(old, dict) and now - int(old.get("t", 0) or 0) < 40 * 24 * 3600 and "p" in old:
                quotes[ident] = old
            errors.append(ident)
            log("  taux sans réponse :", ident)
        else:
            quotes[ident] = q
        time.sleep(0.35)

    pol = fetch_policy()
    for k in POLICY:
        if k not in pol and isinstance(prev.get("pol"), dict) and k in prev["pol"]:
            pol[k] = prev["pol"][k]
    news = fetch_news()
    if not news and isinstance(prev, dict):
        news = prev.get("news", [])  # on garde les dernières actualités connues

    if fresh == 0:
        log("Aucun cours récupéré : le fichier précédent est conservé.")
        sys.exit(1)

    data = {
        "updated": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "q": quotes,
        "pol": pol,
        "news": news,
        "errors": errors,
    }
    with open(path_out, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, separators=(",", ":"))
    carried = len([e for e in errors if e in quotes])
    log("Taux directeurs :", ", ".join(sorted(pol)) or "aucun")
    log("OK : %d cours frais, %d repris, %d actualités" % (fresh, carried, len(news)))


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "out/marches.json")
