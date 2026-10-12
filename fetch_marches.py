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
from concurrent.futures import ThreadPoolExecutor
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
POLICY = {"FED": ("DFEDTARL", "DFEDTARU"), "BCE": ("ECBDFR", "ECBMRRFR"), "BOJ": ("IRSTCB01JPM156N",)}

# Flux RSS (en français). Un flux en panne est simplement ignoré.
FEEDS = [
    ("Le Monde", "https://www.lemonde.fr/economie/rss_full.xml"),
    ("Le Figaro Éco", "https://www.lefigaro.fr/rss/figaro_economie.xml"),
    ("BFM Business", "https://www.bfmtv.com/rss/economie/"),
    ("Investing.com", "https://fr.investing.com/rss/news.rss"),
]
NEWS_MAX = 14
NEWS_PER_FEED = 6


STATE = {}


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
# Historique des ETF de référence (tableau de bord : « portefeuille vs marchés »)
# --------------------------------------------------------------------------
# iShares MSCI World Swap PEA (WPEA) et iShares S&P 500 Swap PEA (SPEA), cotés à Paris.
# Si Yahoo ne répond pas pour le premier symbole, on essaie un ETF équivalent.
HIST_SYMBOLS = {
    "WPEA": ["WPEA.PA", "EWLD.PA", "IWDA.AS"],
    "SPEA": ["SPEA.PA", "ESE.PA", "CSPX.AS"],
}


def fetch_hist_one(symbols):
    """5 ans de clôtures quotidiennes -> {"s": symbole, "d": [jours], "v": [cours]} ou None."""
    for sym in symbols:
        path = "/v8/finance/chart/%s?interval=1d&range=5y" % urllib.request.quote(sym, safe="")
        for base in (YAHOO_BASE, YAHOO_ALT):
            raw = http_get(base + path, tries=2, timeout=30)
            if not raw:
                continue
            try:
                res = json.loads(raw.decode("utf-8", "replace"))["chart"]["result"][0]
                ts = res["timestamp"]
                cl = res["indicators"]["quote"][0]["close"]
            except (ValueError, KeyError, IndexError, TypeError):
                continue
            days, vals = [], []
            for t, c in zip(ts, cl):
                if not isinstance(c, (int, float)) or c <= 0:
                    continue
                d = int(t // 86400)
                if days and d <= days[-1]:
                    continue
                days.append(d)
                vals.append(round(float(c), 4))
            if len(days) > 100:
                return {"s": sym, "d": days, "v": vals}
        log("  historique indisponible :", sym)
    return None


def previous_hist(path_hist):
    if os.path.exists(path_hist):
        try:
            with open(path_hist, encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            pass
    repo = os.environ.get("GITHUB_REPOSITORY")
    if repo:
        raw = http_get("https://raw.githubusercontent.com/%s/data/hist.json" % repo, tries=1, timeout=20)
        if raw:
            try:
                return json.loads(raw.decode("utf-8"))
            except ValueError:
                pass
    return {}


def write_history(path_hist):
    """Écrit hist.json (jamais bloquant : en cas d'échec on garde l'ancien fichier)."""
    try:
        old = previous_hist(path_hist)
        old_h = old.get("h", {}) if isinstance(old, dict) else {}
        h = {}
        for key, syms in HIST_SYMBOLS.items():
            one = fetch_hist_one(syms)
            if one is None and isinstance(old_h.get(key), dict):
                one = old_h[key]  # dernier historique connu
            if one is not None:
                h[key] = one
        if not h:
            log("Historique : aucun ETF de référence récupéré.")
            return
        out = {"updated": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"), "h": h}
        with open(path_hist, "w", encoding="utf-8") as f:
            json.dump(out, f, separators=(",", ":"))
        log("Historique : %s" % ", ".join("%s (%d jours, %s)" % (k, len(v["d"]), v.get("s", "?")) for k, v in h.items()))
    except Exception as e:  # ne doit jamais faire échouer la mise à jour des cours
        log("Historique : erreur", repr(e))


# --------------------------------------------------------------------------
# Cours des titres et ETF du catalogue (autocomplétion du tableau de bord) -> quotes.json
# --------------------------------------------------------------------------
QUOTE_SYMBOLS = ["WPEA.PA", "SPEA.PA", "DCAM.PA", "EWLD.PA", "PSP5.PA", "PE500.PA", "PUST.PA", "PANX.PA", "PAEEM.PA", "PTPXE.PA", "PCEU.PA", "CW8.PA", "500.PA", "ANX.PA", "MEUD.PA", "MSE.PA", "CAC.PA", "RS2K.PA", "BNK.PA", "ESE.PA", "GOLD.PA", "IWDA.AS", "EUNL.DE", "SSAC.L", "CSPX.AS", "SXR8.DE", "IUSA.AS", "CNDX.AS", "SXRV.DE", "EIMI.AS", "IMEU.AS", "IJPA.AS", "SXRT.DE", "EXSA.DE", "INRG.L", "IDVY.AS", "VWCE.DE", "VWRL.AS", "VWRA.L", "VUSA.AS", "VUAA.DE", "VHYL.AS", "VEUR.AS", "VFEM.AS", "VJPN.AS", "EQQQ.DE", "XDWD.DE", "XMME.DE", "SPYY.DE", "SGLD.L", "4GLD.DE", "SPY", "QQQ", "VOO", "VTI", "SCHD", "VYM", "JEPI", "GLD", "SLV", "TLT", "ARKK", "AC.PA", "AI.PA", "AIR.PA", "MT.AS", "CS.PA", "BNP.PA", "EN.PA", "BVI.PA", "CAP.PA", "CA.PA", "ACA.PA", "BN.PA", "DSY.PA", "EDEN.PA", "FGR.PA", "ENGI.PA", "EL.PA", "ERF.PA", "ENX.PA", "RMS.PA", "KER.PA", "LR.PA", "OR.PA", "MC.PA", "ML.PA", "ORA.PA", "RI.PA", "PUB.PA", "RNO.PA", "SAF.PA", "SGO.PA", "SAN.PA", "SU.PA", "GLE.PA", "STLAP.PA", "STMPA.PA", "HO.PA", "TTE.PA", "URW.PA", "VIE.PA", "DG.PA", "ADP.PA", "AF.PA", "ALO.PA", "ATE.PA", "ALTA.PA", "AMUN.PA", "APAM.AS", "ARG.PA", "AKE.PA", "ATO.PA", "AYV.PA", "BEN.PA", "BB.PA", "BIM.PA", "BOL.PA", "CARM.PA", "CLARI.PA", "COFA.PA", "COV.PA", "AM.PA", "DBG.PA", "ELIOR.PA", "ELIS.PA", "EMEIS.PA", "ERA.PA", "ES.PA", "RF.PA", "ETL.PA", "FDJ.PA", "FNAC.PA", "FRVIA.PA", "GFC.PA", "GET.PA", "GTT.PA", "ICAD.PA", "IDL.PA", "NK.PA", "ITP.PA", "IPN.PA", "IPS.PA", "DEC.PA", "LI.PA", "MAU.PA", "MEDCL.PA", "MERY.PA", "MRN.PA", "MMT.PA", "NEOEN.PA", "NEX.PA", "NXI.PA", "POM.PA", "PLNW.PA", "PLX.PA", "RCO.PA", "RXL.PA", "RBT.PA", "RUI.PA", "SK.PA", "DIM.PA", "SCR.PA", "SESG.PA", "SW.PA", "SOI.PA", "SOLB.BR", "SOP.PA", "SPIE.PA", "TE.PA", "TEP.PA", "TFI.PA", "TKO.PA", "TRI.PA", "UBI.PA", "FR.PA", "VK.PA", "VLA.PA", "VRLA.PA", "VCT.PA", "VIRP.PA", "VIRI.PA", "VIV.PA", "VU.PA", "MF.PA", "WLN.PA", "SAP.DE", "SIE.DE", "ALV.DE", "ADS.DE", "BAS.DE", "BAYN.DE", "BEI.DE", "BMW.DE", "BNR.DE", "CBK.DE", "CON.DE", "DTG.DE", "DBK.DE", "DB1.DE", "DHL.DE", "DTE.DE", "EOAN.DE", "FRE.DE", "HEI.DE", "HEN3.DE", "IFX.DE", "MBG.DE", "MRK.DE", "MTX.DE", "MUV2.DE", "P911.DE", "RHM.DE", "RWE.DE", "ENR.DE", "SHL.DE", "SY1.DE", "VOW3.DE", "VNA.DE", "ZAL.DE", "QIA.DE", "ASML.AS", "ADYEN.AS", "AD.AS", "AKZA.AS", "ASM.AS", "BESI.AS", "HEIA.AS", "INGA.AS", "JDEP.AS", "KPN.AS", "NN.AS", "PHIA.AS", "PRX.AS", "RAND.AS", "WKL.AS", "UMG.AS", "UNA.AS", "RACE.MI", "ABI.BR", "KBC.BR", "UCB.BR", "UMI.BR", "AGS.BR", "SOF.BR", "GBLB.BR", "ARGX.BR", "ITX.MC", "SAN.MC", "BBVA.MC", "IBE.MC", "TEF.MC", "CABK.MC", "REP.MC", "AMS.MC", "FER.MC", "CLNX.MC", "NTGY.MC", "AENA.MC", "ELE.MC", "RED.MC", "GRF.MC", "ACS.MC", "SAB.MC", "BKT.MC", "ANA.MC", "IDR.MC", "ENEL.MI", "ENI.MI", "ISP.MI", "UCG.MI", "G.MI", "PRY.MI", "MONC.MI", "LDO.MI", "TRN.MI", "SRG.MI", "PST.MI", "MB.MI", "BAMI.MI", "BPE.MI", "CPR.MI", "AMP.MI", "DIA.MI", "NEXI.MI", "REC.MI", "PIRC.MI", "BC.MI", "TEN.MI", "STLAM.MI", "NESN.SW", "ROG.SW", "NOVN.SW", "UBSG.SW", "ZURN.SW", "CFR.SW", "ABBN.SW", "LONN.SW", "NOVO-B.CO", "SHEL.L", "AZN.L", "HSBA.L", "BP.L", "DGE.L", "GSK.L", "RIO.L", "BATS.L", "7203.T", "6758.T", "7974.T", "AAPL", "MSFT", "NVDA", "AMZN", "GOOGL", "GOOG", "META", "TSLA", "BRK-B", "AVGO", "LLY", "JPM", "V", "MA", "UNH", "XOM", "JNJ", "PG", "HD", "COST", "ABBV", "MRK", "CVX", "KO", "PEP", "BAC", "WMT", "ORCL", "CRM", "ADBE", "NFLX", "AMD", "TMO", "ACN", "MCD", "CSCO", "ABT", "DIS", "TXN", "WFC", "INTC", "QCOM", "VZ", "PM", "INTU", "IBM", "GE", "CAT", "AMGN", "NOW", "UBER", "BKNG", "GS", "MS", "RTX", "LOW", "HON", "UNP", "T", "NKE", "PFE", "SBUX", "LMT", "DE", "BLK", "AXP", "PYPL", "PLTR", "PANW", "CRWD", "MU", "AMAT", "COIN", "SPOT", "SNOW", "UPS", "GILD", "BMY", "CVS", "TMUS", "CMCSA", "MO", "TGT", "F", "GM", "O", "AMT", "NEE", "DUK", "SO", "AEP", "MDLZ", "CL", "KMB", "GIS", "LRCX", "KLAC", "ANET", "MRVL", "NET", "DDOG", "SHOP", "ABNB", "ARM", "NVO", "TSM", "BABA", "SONY", "TM", "PDD", "JD", "BIDU"]
FX_PAIRS = {"USD": "EURUSD=X", "GBP": "EURGBP=X", "CHF": "EURCHF=X", "DKK": "EURDKK=X", "JPY": "EURJPY=X"}


def previous_quotes(path_q):
    if os.path.exists(path_q):
        try:
            with open(path_q, encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            pass
    repo = os.environ.get("GITHUB_REPOSITORY")
    if repo:
        raw = http_get("https://raw.githubusercontent.com/%s/data/quotes.json" % repo, tries=1, timeout=20)
        if raw:
            try:
                return json.loads(raw.decode("utf-8"))
            except ValueError:
                pass
    return {}


def write_quotes(path_q):
    """Cours en euros de chaque valeur du catalogue (jamais bloquant)."""
    try:
        old = previous_quotes(path_q)
        old_q = old.get("q", {}) if isinstance(old, dict) else {}
        fx = {"EUR": 1.0}
        for cur, pair in FX_PAIRS.items():
            q = fetch_quote(pair)
            if q and q.get("p"):
                fx[cur] = q["p"]
            time.sleep(0.2)
        now = int(time.time())
        out, ok, failed = {}, 0, []

        def one(sym):
            q = fetch_quote(sym)
            if not q:
                return sym, None
            cur, p = q.get("u", "EUR"), q["p"]
            if cur == "GBp":
                cur, p = "GBP", p / 100.0
            rate = fx.get(cur)
            if not rate:
                return sym, None
            e = {"p": round(p / rate, 4), "t": q.get("t", now)}
            if "c" in q:
                e["c"] = q["c"]
            return sym, e

        from concurrent.futures import ThreadPoolExecutor
        with ThreadPoolExecutor(max_workers=6) as ex:
            for sym, e in ex.map(one, QUOTE_SYMBOLS):
                if e:
                    out[sym] = e
                    ok += 1
                    continue
                failed.append(sym)
                o = old_q.get(sym)
                if isinstance(o, dict) and now - int(o.get("t", 0) or 0) < 10 * 24 * 3600:
                    out[sym] = o
        if failed:
            log("Cours du catalogue sans réponse :", ", ".join(failed))
        if ok == 0:
            log("Cours du catalogue : aucun cours récupéré, fichier précédent conservé.")
            return
        data = {"updated": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"), "q": out}
        with open(path_q, "w", encoding="utf-8") as f:
            json.dump(data, f, separators=(",", ":"))
        log("Cours du catalogue : %d/%d à jour" % (ok, len(QUOTE_SYMBOLS)))
    except Exception as e:
        log("Cours du catalogue : erreur", repr(e))



# --------------------------------------------------------------------------
# Patrimoine des ménages (Insee) -> insee.json  (déciles début N, mis à jour quand l'Insee republie)
# --------------------------------------------------------------------------
INSEE_XLSX = "https://www.insee.fr/fr/statistiques/fichier/2388851/reve-patrim-decile.xlsx"
INSEE_KEYS = ["D1", "D2", "D3", "D4", "D5", "D6", "D7", "D8", "D9", "P95", "P99"]


def _label_key(text):
    """Reconnaît « D1 », « 1er décile (D1) », « Médiane », « P95 », « 95e centile »... -> clé ou None."""
    import re
    s = text.strip().upper().replace("É", "E").replace("\u00a0", " ")
    m = re.search(r"\bD\s?([1-9])\b", s)
    if m:
        return "D" + m.group(1)
    if "MEDIANE" in s:
        return "D5"
    m = re.search(r"\bP\s?(95|99)\b", s) or re.search(r"\b(95|99)\s?(?:E|EME)?\s*(?:CENTILE|PERCENTILE)", s)
    if m:
        return "P" + m.group(1)
    m = re.search(r"\b([1-9])\s?(?:ER|E|EME)\s+DECILE", s)
    if m:
        return "D" + m.group(1)
    return None


def parse_insee_xlsx(raw):
    """Lit le classeur Insee (zip + XML, sans dépendance) -> {"year", "brut":[11], "net":[11]} ou None."""
    import re, zipfile, io
    import xml.etree.ElementTree as ET
    ns = {"m": "http://schemas.openxmlformats.org/spreadsheetml/2006/main"}
    z = zipfile.ZipFile(io.BytesIO(raw))
    shared = []
    if "xl/sharedStrings.xml" in z.namelist():
        for si in ET.fromstring(z.read("xl/sharedStrings.xml")).findall("m:si", ns):
            shared.append("".join(x.text or "" for x in si.iter("{%s}t" % ns["m"])))
    best = None
    for name in sorted(n for n in z.namelist() if n.startswith("xl/worksheets/sheet") and n.endswith(".xml")):
        grid = {}
        for c in ET.fromstring(z.read(name)).iter("{%s}c" % ns["m"]):
            ref = c.get("r", "")
            mm = re.match(r"([A-Z]+)(\d+)", ref)
            if not mm:
                continue
            col = 0
            for ch in mm.group(1):
                col = col * 26 + ord(ch) - 64
            row = int(mm.group(2))
            v = c.find("m:v", ns)
            if c.get("t") == "inlineStr":
                val = "".join(x.text or "" for x in c.iter("{%s}t" % ns["m"]))
            elif v is None or v.text is None:
                continue
            elif c.get("t") == "s":
                val = shared[int(v.text)]
            else:
                try:
                    val = float(v.text)
                except ValueError:
                    val = v.text
            grid[(row, col)] = val
        res = _extract_deciles(grid)
        if res:
            texts = " ".join(str(v) for v in grid.values() if isinstance(v, str))
            ym = re.findall(r"(?:d[ée]but|debut|au 1er janvier)\s+(20\d\d)", texts, re.I) or re.findall(r"\b(20[12]\d)\b", texts)
            res["year"] = int(max(ym, key=int)) if ym else None
            best = res
            break
    return best


def _extract_deciles(grid):
    rows = sorted({r for r, _ in grid})
    cols = sorted({c for _, c in grid})
    # repère des colonnes/lignes « brut » et « net »
    def find_axis(word):
        for (r, c), v in grid.items():
            if isinstance(v, str) and word in v.lower():
                return r, c
        return None
    pb, pn = find_axis("brut"), find_axis("net")
    out = {}
    for layout in ("rows", "cols"):
        found = {}
        for (r, c), v in grid.items():
            if not isinstance(v, str):
                continue
            k = _label_key(v)
            if not k or k in found:
                continue
            if layout == "rows":
                nums = [(cc, grid[(r, cc)]) for cc in cols if cc > c and isinstance(grid.get((r, cc)), float)]
            else:
                nums = [(rr, grid[(rr, c)]) for rr in rows if rr > r and isinstance(grid.get((rr, c)), float)]
            if len(nums) >= 2:
                found[k] = nums[:2]
        if all(k in found for k in INSEE_KEYS):
            first_is_brut = True
            if pb and pn:
                first_is_brut = (pb[1] < pn[1]) if layout == "rows" else (pb[0] < pn[0])
            brut, net = [], []
            for k in INSEE_KEYS:
                a, b = found[k][0][1], found[k][1][1]
                brut.append(a if first_is_brut else b)
                net.append(b if first_is_brut else a)
            out = {"brut": brut, "net": net}
            break
    if not out:
        return None
    for arr in (out["brut"], out["net"]):
        if any(arr[i] <= arr[i - 1] for i in range(1, 11)) or not (20000 < arr[4] < 2000000):
            return None
    out["brut"] = [int(round(x)) for x in out["brut"]]
    out["net"] = [int(round(x)) for x in out["net"]]
    return out


def write_insee(path_i):
    """Ne remplace insee.json que si le fichier Insee est lu et cohérent (jamais bloquant)."""
    try:
        raw = http_get(INSEE_XLSX, tries=2, timeout=40)
        res = parse_insee_xlsx(raw) if raw else None
        if not res:
            log("Insee : fichier illisible ou inchangé, version précédente conservée.")
            return
        old = {}
        repo = os.environ.get("GITHUB_REPOSITORY")
        if repo:
            r = http_get("https://raw.githubusercontent.com/%s/data/insee.json" % repo, tries=1, timeout=15)
            if r:
                try:
                    old = json.loads(r.decode("utf-8"))
                except ValueError:
                    old = {}
        pub = old.get("pub") if old.get("brut") == res["brut"] and old.get("net") == res["net"] else None
        data = {"updated": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"), "year": res.get("year"),
                "pub": pub or datetime.now(timezone.utc).strftime("%Y-%m-%d"), "brut": res["brut"], "net": res["net"]}
        with open(path_i, "w", encoding="utf-8") as f:
            json.dump(data, f, separators=(",", ":"))
        log("Insee : médiane brute %s, nette %s (début %s)" % (res["brut"][4], res["net"][4], res.get("year")))
    except Exception as e:
        log("Insee : erreur", repr(e))



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
    if STATE.get("stooq_dead"):
        return []
    raw = http_get(url, tries=1, timeout=12)
    if not raw:
        STATE["stooq_dead"] = True  # stooq injoignable depuis ce serveur : inutile d'insister (CNBC prend le relais)
        log("  stooq injoignable : source ignorée pour cette exécution")
        return []
    text = raw.decode("utf-8", "replace")
    rows = list(csv.reader(io.StringIO(text)))
    if not rows or [c.strip().lower() for c in rows[0][:1]] != ["date"]:
        if not STATE.get("stooq_logged"):
            STATE["stooq_logged"] = True
            log("  stooq : réponse inattendue :", text[:90].replace("\n", " "))
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
    raw = http_get("%s/graph/fredgraph.csv?id=%s&cosd=%s" % (FRED_BASE, series_id, start), tries=1, timeout=25)
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


ECB_BASE = os.environ.get("ECB_BASE", "https://data-api.ecb.europa.eu").rstrip("/")
CNBC_URL = os.environ.get("CNBC_URL", "https://quote.cnbc.com/quote-html-webservice/quote.htm")
CNBC = {"US10": "US10Y", "DE10": "DE10Y-DE", "FR10": "FR10Y-FR", "IT10": "IT10Y-IT",
        "ES10": "ES10Y-ES", "JP10": "JP10Y-JP", "UK10": "UK10Y-GB"}


def ecb_series(key, days=900):
    """Taux directeurs BCE depuis le portail de données de la BCE (secours de FRED)."""
    start = (datetime.now(timezone.utc).date() - timedelta(days=days)).isoformat()
    raw = http_get("%s/service/data/FM/%s?startPeriod=%s&format=csvdata" % (ECB_BASE, key, start), tries=2, timeout=40)
    if not raw:
        return []
    out = []
    for r in csv.DictReader(io.StringIO(raw.decode("utf-8", "replace"))):
        v = _num(r.get("OBS_VALUE"))
        d = (r.get("TIME_PERIOD") or "")[:10]
        if v is not None and re.match(r"^\d{4}-\d{2}-\d{2}$", d):
            out.append((d, v))
    return out


def fetch_cnbc():
    """Rendements 10 ans (7 pays) en un seul appel, sans clé."""
    syms = "|".join(list(CNBC.values()) + ["GB10Y-GB"])
    url = ("%s?symbols=%s&requestMethod=itv&noform=1&partnerId=2&fund=1&exthrs=1&output=json&events=1"
           % (CNBC_URL, urllib.request.quote(syms, safe="|-")))
    raw = http_get(url, tries=2, timeout=30)
    if not raw:
        return {}
    try:
        data = json.loads(raw.decode("utf-8", "replace"))
    except ValueError:
        log("  cnbc : réponse non JSON")
        return {}
    rows = []

    def walk(o):
        if isinstance(o, dict):
            if "symbol" in o and "last" in o:
                rows.append(o)
            for v in o.values():
                walk(v)
        elif isinstance(o, list):
            for x in o:
                walk(x)
    walk(data)
    by = {str(r["symbol"]): r for r in rows}
    out = {}
    for ident, sym in CNBC.items():
        r = by.get(sym) or (by.get("GB10Y-GB") if ident == "UK10" else None)
        if not r:
            continue
        clean = lambda v: _num(str(v).replace("%", "").replace(",", ""))
        p = clean(r.get("last"))
        if p is None or not (0 < p < 30):
            continue
        prev = clean(r.get("previous_day_closing"))
        ch = clean(r.get("change"))
        d = (p - prev) if prev else ch
        q = {"p": round(p, 4), "k": "y", "dt": datetime.now(timezone.utc).date().isoformat()}
        tm = clean(r.get("last_time_msec"))
        q["t"] = int(tm / 1000) if tm and tm > 1e11 else int(time.time())
        if d is not None and abs(d) < 1:
            q["d"] = round(d, 4)
        out[ident] = q
    log("  cnbc :", len(out), "taux")
    return out


def yahoo_yield(sym):
    y = fetch_quote(sym)
    if not y or y.get("p") is None:
        return None
    k = 10.0 if y["p"] > 25 else 1.0  # ^TNX : parfois en dixièmes
    p = y["p"] / k
    out = {"p": round(p, 4), "t": y.get("t", int(time.time())), "k": "y", "dt": datetime.now(timezone.utc).date().isoformat()}
    if "c" in y:
        out["d"] = round(p - p / (1 + y["c"] / 100.0), 4)
    if y.get("s"):
        out["s"] = [round(v / k, 4) for v in y["s"]]
    return out


def fred_fallback(ident):
    _, fred_d, fred_m, _ = YIELDS[ident]
    if fred_d:
        q = yield_quote(fred_series(fred_d))
        if q:
            return q
    return yield_quote(fred_series(fred_m, days=200), monthly=True)


def fetch_all_yields():
    out = {}
    for ident, (stooq, _, _, _) in YIELDS.items():
        q = yield_quote(stooq_series(stooq))
        if q:
            out[ident] = q
    miss = [i for i in YIELDS if i not in out]
    if miss:
        c = fetch_cnbc()
        for i in miss:
            if i in c:
                out[i] = c[i]
    if "US10" not in out and YIELDS["US10"][3]:
        q = yahoo_yield(YIELDS["US10"][3])
        if q:
            out["US10"] = q
    miss = [i for i in YIELDS if i not in out]
    if miss:
        with ThreadPoolExecutor(max_workers=6) as ex:
            futs = {i: ex.submit(fred_fallback, i) for i in miss}
            for i, f in futs.items():
                try:
                    q = f.result(timeout=240)
                except Exception as e:  # noqa: BLE001
                    log("  fred :", i, repr(e))
                    q = None
                if q:
                    out[i] = q
    return out



def last_change(pairs):
    """Date à laquelle la valeur actuelle est entrée en vigueur (ou None)."""
    if not pairs:
        return None
    cur = pairs[-1][1]
    for i in range(len(pairs) - 1, 0, -1):
        if abs(pairs[i - 1][1] - cur) > 1e-9:
            return pairs[i][0]
    return None


NYFED_URL = os.environ.get("NYFED_URL", "https://markets.newyorkfed.org/api/rates/unsecured/effr/last/260.json")


# Dernier taux connu de la Banque du Japon, utilisé UNIQUEMENT si aucune source en ligne ne répond.
# À mettre à jour après chaque décision de la BoJ (rate = taux directeur en %, asof = date de la réunion).
BOJ_MANUAL = {"rate": 1.0, "since": None, "asof": "2026-07-31"}


def bis_series(area, days=900):
    """Taux directeur d'une banque centrale (BRI, dataflow WS_CBPOL) -> [(date, valeur)], ou []."""
    url = "https://stats.bis.org/api/v2/data/dataflow/BIS/WS_CBPOL/1.0/D.%s?lastNObservations=%d&format=csv" % (area, days)
    raw = http_get(url, tries=1, timeout=25)
    if not raw:
        return []
    try:
        rows = list(csv.reader(io.StringIO(raw.decode("utf-8", "replace"))))
        head = [c.strip().upper() for c in rows[0]]
        it, iv = head.index("TIME_PERIOD"), head.index("OBS_VALUE")
    except (ValueError, IndexError):
        return []
    out = []
    for r in rows[1:]:
        v = _num(r[iv]) if len(r) > iv else None
        if v is not None and len(r) > it and re.match(r"^\d{4}-\d{2}-\d{2}$", r[it]):
            out.append((r[it], v))
    out.sort()
    return out


def nyfed_fed():
    """Secours FED : fourchette cible publiée avec le taux EFFR par la Fed de New York."""
    raw = http_get(NYFED_URL, tries=2, timeout=40)
    if not raw:
        return None
    try:
        rows = json.loads(raw.decode("utf-8", "replace")).get("refRates", [])
    except (ValueError, AttributeError):
        return None
    pts = []
    for r in rows:
        lo, hi, d = _num(r.get("targetRateFrom")), _num(r.get("targetRateTo")), str(r.get("effectiveDate", ""))[:10]
        if lo is not None and hi is not None and re.match(r"^\d{4}-\d{2}-\d{2}$", d):
            pts.append((d, lo, hi))
    if not pts:
        return None
    pts.sort()
    his = [(d, hi) for d, _, hi in pts]
    return {"lo": pts[-1][1], "hi": pts[-1][2], "since": last_change(his), "asof": pts[-1][0]}


def fetch_policy():
    out = {}
    with ThreadPoolExecutor(max_workers=5) as ex:
        f = {k: ex.submit(fred_series, k, 900) for k in ("DFEDTARL", "DFEDTARU", "ECBDFR", "ECBMRRFR", "IRSTCB01JPM156N")}
        got = {}
        for k, fut in f.items():
            try:
                got[k] = fut.result(timeout=240)
            except Exception as e:  # noqa: BLE001
                log("  fred :", k, repr(e))
                got[k] = []
    lo, hi = got["DFEDTARL"], got["DFEDTARU"]
    if lo and hi:
        out["FED"] = {"lo": lo[-1][1], "hi": hi[-1][1], "since": last_change(hi), "asof": hi[-1][0]}
    else:
        f = nyfed_fed()
        if f:
            out["FED"] = f
    dfr, mrr = got["ECBDFR"], got["ECBMRRFR"]
    if not dfr or not mrr:  # secours : portail de données de la BCE
        dfr = ecb_series("B.U2.EUR.4F.KR.DFR.LEV")
        mrr = ecb_series("B.U2.EUR.4F.KR.MRR_FR.LEV")
    if dfr and mrr:
        out["BCE"] = {"dfr": dfr[-1][1], "mrr": mrr[-1][1], "since": last_change(dfr), "asof": dfr[-1][0]}
    boj = got.get("IRSTCB01JPM156N") or []  # Banque du Japon : taux directeur (série mensuelle OCDE via FRED)
    if not boj:
        boj = bis_series("JP")  # secours : base des taux directeurs de la BRI (quotidienne)
    if boj:
        out["BOJ"] = {"rate": boj[-1][1], "since": last_change(boj), "asof": boj[-1][0]}
    else:
        log("  BoJ : FRED et BRI injoignables, valeur de référence utilisée (", BOJ_MANUAL["asof"], ")")
        out["BOJ"] = dict(BOJ_MANUAL, ref=True)
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


# Dividendes des 24 derniers mois (calendrier du tableau de bord) -> divs.json
# --------------------------------------------------------------------------
def previous_json(path, name):
    if os.path.exists(path):
        try:
            with open(path, encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            pass
    repo = os.environ.get("GITHUB_REPOSITORY")
    if repo:
        raw = http_get("https://raw.githubusercontent.com/%s/data/%s" % (repo, name), tries=1, timeout=20)
        if raw:
            try:
                return json.loads(raw.decode("utf-8"))
            except ValueError:
                pass
    return {}


def fetch_divs(symbol):
    """-> (devise, [[jour_epoch, montant], ...]) ou None si Yahoo ne répond pas."""
    path = "/v8/finance/chart/%s?interval=1mo&range=2y&events=div" % urllib.request.quote(symbol, safe="")
    for base in (YAHOO_BASE, YAHOO_ALT):
        raw = http_get(base + path, tries=2)
        if not raw:
            continue
        try:
            res = json.loads(raw.decode("utf-8", "replace"))["chart"]["result"][0]
            cur = (res.get("meta") or {}).get("currency")
            evs = (res.get("events") or {}).get("dividends") or {}
        except (ValueError, KeyError, IndexError, TypeError):
            continue
        if not cur:
            continue
        rows = []
        for e in evs.values():
            try:
                rows.append([int(e["date"]) // 86400, float(e["amount"])])
            except (KeyError, TypeError, ValueError):
                pass
        rows.sort()
        return cur, rows
    return None


def write_divs(path_d):
    """Dividendes par titre, convertis en euros (jamais bloquant, fichier toujours réécrit)."""
    try:
        old = previous_json(path_d, "divs.json")
        old_d = old.get("d", {}) if isinstance(old, dict) else {}
        fx = {"EUR": 1.0}
        for cur, pair in FX_PAIRS.items():
            q = fetch_quote(pair)
            if q and q.get("p"):
                fx[cur] = q["p"]
            time.sleep(0.2)

        def one(sym):
            r = fetch_divs(sym)
            if not r:
                return sym, None
            cur, rows = r
            if cur == "GBp":
                cur, rows = "GBP", [[d, a / 100.0] for d, a in rows]
            rate = fx.get(cur)
            if not rate:
                return sym, None
            return sym, [[d, round(a / rate, 4)] for d, a in rows]

        syms = [s for s in QUOTE_SYMBOLS if not s.endswith("=X")]
        out, ok, failed = {}, 0, []
        with ThreadPoolExecutor(max_workers=6) as ex:
            for sym, rows in ex.map(one, syms):
                if rows is not None:
                    out[sym] = rows  # liste vide = titre sans dividende
                    ok += 1
                elif sym in old_d:
                    out[sym] = old_d[sym]
                else:
                    failed.append(sym)
        if failed:
            log("Dividendes sans réponse :", ", ".join(failed))
        if not out:
            log("Dividendes : rien récupéré, aucun fichier écrit.")
            return
        data = {"updated": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"), "d": out}
        with open(path_d, "w", encoding="utf-8") as f:
            json.dump(data, f, separators=(",", ":"))
        log("Dividendes : %d/%d titres à jour" % (ok, len(syms)))
    except Exception as e:
        log("Dividendes : erreur", repr(e))


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

    ys = fetch_all_yields()
    for ident in YIELDS:
        q = ys.get(ident)
        if q is None:
            old = prev_q.get(ident)
            if isinstance(old, dict) and now - int(old.get("t", 0) or 0) < 40 * 24 * 3600 and "p" in old:
                quotes[ident] = old
            errors.append(ident)
            log("  taux sans réponse :", ident)
        else:
            quotes[ident] = q

    pol = fetch_policy()
    for k in POLICY:
        if k not in pol and isinstance(prev.get("pol"), dict) and k in prev["pol"]:
            pol[k] = prev["pol"][k]
    news = fetch_news()
    if not news and isinstance(prev, dict):
        news = prev.get("news", [])  # on garde les dernières actualités connues

    write_history(os.path.join(os.path.dirname(os.path.abspath(path_out)), "hist.json"))
    write_quotes(os.path.join(os.path.dirname(os.path.abspath(path_out)), "quotes.json"))
    write_insee(os.path.join(os.path.dirname(os.path.abspath(path_out)), "insee.json"))
    write_divs(os.path.join(os.path.dirname(os.path.abspath(path_out)), "divs.json"))

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
