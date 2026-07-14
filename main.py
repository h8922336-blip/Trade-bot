import requests
import time
import json
import os
import threading
import logging
from datetime import datetime, timedelta
from zoneinfo import ZoneInfo
from collections import Counter

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[logging.FileHandler("tsm_v32g.log"), logging.StreamHandler()]
)
logger = logging.getLogger(__name__)

TELEGRAM_TOKEN = os.getenv("TELEGRAM_TOKEN", "YOUR_TOKEN_HERE")
CHAT_ID        = os.getenv("CHAT_ID", "YOUR_CHAT_ID_HERE")
NEWS_API_KEY   = os.getenv("NEWS_API_KEY", "")
ANTHROPIC_API_KEY = os.getenv("ANTHROPIC_API_KEY", "")      # CryptoPanic API key (optional)

BINANCE_PRICE_URL   = "https://data-api.binance.vision/api/v3/ticker/price"
BINANCE_KLINE_URL   = "https://data-api.binance.vision/api/v3/klines"
BINANCE_FUTURES_PRICE_URL = "https://fapi.binance.com/fapi/v1/ticker/price"
BINANCE_FUTURES_KLINE_URL = "https://fapi.binance.com/fapi/v1/klines"
# Symbols confirmed Futures-only (Binance TradFi Perpetuals, launched under a
# dedicated [TradFi] tab on Futures — no Spot listing exists for XAU/XAG).
# PAXG is genuinely available on BOTH Spot and Futures (verified: real PAXG/
# USDT spot trading, spot grid bots, spot DCA all confirmed live) — routed to
# Futures anyway for consistency with the other two precious-metals symbols.
#
# ADVISORY: PAXG's Futures liquidity can vary by region and is sometimes less
# reliable than its Spot market. If price/kline WARNING log lines start
# appearing for PAXG specifically, remove "PAXGUSDT" from this set below —
# it will then fall back to the Spot engine automatically, no other code
# changes needed. Not applied preemptively here since there's no current
# evidence of an actual problem; this is a one-line self-service fix for if
# that changes.
# CONFIRMED (not just theoretical): live Railway logs showed
# "get_price PAXGUSDT: Futures endpoint returned 451" and the matching
# get_klines warning — the exact symptom this set's docstring said to
# watch for. PAXG hits the same Binance Geo-Block as XAU/XAG did.
# Emptied per that log evidence — PAXG now routes through the standard
# Spot API (unrestricted) via the existing `if symbol in
# FUTURES_ONLY_SYMBOLS` branches in get_price/get_klines/
# get_funding_rate/get_oi_trend, automatically, no other code changes
# needed anywhere else.
FUTURES_ONLY_SYMBOLS = set()
BINANCE_AGG_URL     = "https://api.binance.com/api/v3/aggTrades"
BINANCE_FUNDING_URL = "https://fapi.binance.com/fapi/v1/fundingRate"
BINANCE_OI_URL      = "https://fapi.binance.com/futures/data/openInterestHist"

trade_lock = threading.Lock()
IST        = ZoneInfo("Asia/Kolkata")

COINS = list(dict.fromkeys([
    "BTC","ETH","BNB","SOL","XRP","DOGE","ADA","TRX","AVAX","SHIB",
    "DOT","LINK","BCH","NEAR","LTC","UNI","APT","ETC","HBAR","FIL",
    "ARB","VET","INJ","OP","ATOM","TIA","SUI","SEI","ALGO","EGLD",
    "FLOW","EOS","XTZ","AAVE","MKR","GRT","SNX","COMP","CRV","SUSHI",
    "LDO","CAKE","1INCH","DYDX","GMX","ENS","PENDLE","RNDR","FET","WLD",
    "AR","THETA","LPT","AKT","SAND","MANA","AXS","GALA","CHZ","APE",
    "GMT","ENJ","PEPE","WIF","FLOKI","BONK","ORDI","BOME","NOT","DOGS",
    "JUP","PYTH","JTO","STRK","EIGEN","ETHFI","IO","ZERO","ONDO",
    "BLUR","CFX","METIS","MANTA","ZETA","TRB","ALT","PIXEL","PORTAL","STPT","KAS",
    "PIPPIN","BSB","CL","LAB","PAXG"
    # XRP, ADA, LINK, AVAX already present earlier in this list (see the
    # "BTC","ETH","BNB","SOL","XRP",...,"ADA",... and "LINK" lines above) —
    # not re-added here to avoid a misleading duplicate literal entry.
    # dict.fromkeys() below would have silently deduped it either way, but
    # this is clearer for anyone reading the list later.
]))

active_trades             = {}
pending_signals           = {}
hourly_queue              = {}
sent_coins                = []
daily_losses              = 0
circuit_breaker_until     = None
last_reset_day            = datetime.now(IST).date()
trade_journal             = []
learning_notes            = []
coin_cooldowns            = {}
retest_watchlist          = {}   # coin -> {level, direction, pattern, logged_at, symbol}
htf_zones_cache           = {}   # symbol -> {"zones": {...}, "cached_at": datetime} — 15min TTL, see get_htf_zones
consecutive_loss_patterns = {}
price_alerts              = {}
market_memory = {
    "bull":     {"wins":0,"losses":0,"best_pattern":None},
    "bear":     {"wins":0,"losses":0,"best_pattern":None},
    "sideways": {"wins":0,"losses":0,"best_pattern":None}
}
pattern_stats = {p: {"signals":0,"wins":0,"losses":0,"total_pnl":0.0,"weight":1.0,
                     "bull_wr":0.0,"bear_wr":0.0,"sideways_wr":0.0} for p in [
    "EMA Trend","Breakout","Pullback to 20 EMA","RSI Reversal","Momentum Surge",
    "Volume Spike","Double Bottom","Double Top","Support Bounce","Resistance Rejection",
    "Bullish Engulfing","Bearish Engulfing","Volume Breakout","Bull Flag Break","Bear Flag Break",
    "BOS Breakout","Change of Character (ChoCh)","Liquidity Sweep","Volatility Contraction (Coiling)","Pre-Breakout Compression"
]}

last_update_id         = None
last_river_time        = 0
last_hourly_time       = time.time()
last_pnl_update_time   = time.time() + 1800
last_8h_desk_time      = time.time()
last_weekly_report_day = None

SCAN_INTERVAL            = 90
RIVER_INTERVAL           = 900
MIN_SETUP_SCORE          = 90
MIN_PRIMARY_SCORE        = 85    # matches the normalized pattern base (Point 5) — the floor
                                  # a pattern must exist at, not a bar it must clear pre-confirmation
INSTANT_SIGNAL_THRESHOLD = 97
GRADE_A_THRESHOLD        = 92.2  # Point 5/6: setup_score >= this = Grade A -> eligible for AI review
VIP_AI_COINS             = {"MANA","LAB","ENJ"}  # RIVER replaced with LAB (RIVER no longer liquid/supported on Binance)

# Point 3: 24/7 Premium Institutional Watchlist. These assets are granted
# VIP immunity from Dead Hour (2-7AM IST) and scheduled macro-event pauses
# — they scan continuously because high-liquidity institutional assets
# genuinely do respect technicals around the clock, unlike thin altcoins
# that go dead/erratic during low-volume overnight hours.
PREMIUM_COINS             = {"BTC","ETH","BNB","SOL","PAXG","XRP","ADA","LINK","AVAX"}
# XAU/XAG removed per reported Geo-Block (451) errors on the Futures TradFi
# endpoint — see FUTURES_ONLY_SYMBOLS and get_price/get_klines's docstrings
# for the regional-access background (separate regulated entity, Nest
# Exchange Limited/ADGM-FSRA, from standard Binance Futures). PAXG was NOT
# reported as failing, so it stays in both PREMIUM_COINS and
# FUTURES_ONLY_SYMBOLS unchanged — only XAU/XAG are being pulled here.
# Replaced with 4 high-liquidity top-cap assets (XRP, ADA, LINK, AVAX) that
# were already present in the main COINS scan universe (verified — no new
# unvalidated symbols introduced) and trade on standard Spot/Futures with
# no regional-routing complications.
MIN_PROFIT_TARGET        = 15.0
SIGNAL_EXPIRY_MINUTES    = 120
INSTANT_EXPIRY_MINUTES   = 30
DELAY_BETWEEN_COINS      = 0.15
MAX_SIGNALS_PER_CYCLE    = 3
MAX_ACTIVE_TRADES        = 5
ATR_SL_MULTIPLIER        = 2.5
ATR_TP_MULTIPLIER        = 5.0
MIN_RR_RATIO             = 2.0  # TP must be at least this many multiples of the
                                  # actual SL distance — see the TP anchoring fix
                                  # in format_and_send (the ATR-only TP could
                                  # previously land inside a 1:0.5 R/R when the
                                  # structural SL was tight but ATR was also small)
MAX_DAILY_LOSSES         = 3
CIRCUIT_BREAKER_MIN_LOSS = -5.0
WHALE_TRADE_THRESHOLD    = 500000
ATR_VOLATILITY_RATIO     = 3.0
CONSEC_LOSS_SUSPEND      = 5
MIN_SIGNALS_TO_SUSPEND   = 15
SUSPEND_HOURS            = 12
ADX_MIN_TREND            = 21
ST_PERIOD                = 10
ST_MULTIPLIER            = 3.0
MIN_SL_PCT               = 0.003  # was 0.02 (2%) — that floor was silently widening
                                    # every tight structural stop back to 2%, via the
                                    # min()/max() clamp in get_structure_sl, completely
                                    # overriding the swing-pivot-based SL system. 0.3%
                                    # stays meaningfully wider than the 0.05% one-tick
                                    # buffer (still a genuine sanity floor against a stop
                                    # sitting on entry) while letting realistic tight
                                    # swing stops (0.3%-2% away) actually be respected.
DEAD_HOUR_START          = 2
DEAD_HOUR_END            = 7

# Golden Hours: first 2 hours of London and New York opens, when
# institutional volume injects real, sustained momentum vs quieter
# Asian-session hours. Verified via search — sources vary slightly
# (12:30-1:30 PM and 5:30-6:30 PM IST depending on source), used the
# most consistently-cited standard-time anchors below.
# KNOWN LIMITATION: these are STANDARD TIME only. During US/UK Daylight
# Saving Time (roughly late March - late October), both sessions shift
# about 1 hour EARLIER in IST. This is not auto-adjusted — same category
# of manual-upkeep limitation as SCHEDULED_MACRO_EVENTS below.
LONDON_OPEN_HOUR         = 12   # 12:30 PM IST standard time
LONDON_GOLDEN_END_HOUR   = 14   # first ~2 hours: 12:30-2:30 PM IST
NY_OPEN_HOUR             = 17   # 5:30 PM IST standard time
NY_GOLDEN_END_HOUR       = 19   # first ~2 hours: 5:30-7:30 PM IST

def is_golden_hour():
    """
    Point 4: "Golden Hours" vs Dead Zones. Returns True during the first
    ~2 hours of the London or New York open (standard IST, see the DST
    caveat on the constants above). Used as a scorecard bonus, NOT a
    hard block — Dead Hour already hard-blocks the genuinely thin
    2-7AM window; this only rewards the best hours, it doesn't punish
    the rest of the day.
    """
    hour = datetime.now(IST).hour
    in_london = LONDON_OPEN_HOUR <= hour < LONDON_GOLDEN_END_HOUR
    in_ny = NY_OPEN_HOUR <= hour < NY_GOLDEN_END_HOUR
    return in_london or in_ny

# Point 4: Macro-Time Awareness.
# HONEST SCOPE: this bot has no live economic calendar API, so it cannot
# know "FOMC in 10 minutes" in real time on its own. What it DOES do:
#  (a) flags known low-liquidity weekend windows (Sat/Sun chop is real
#      and doesn't need an API to detect),
#  (b) checks a manually-maintained list below of major scheduled dates
#      you update occasionally (FOMC, CPI, major unlocks) — add entries
#      as "YYYY-MM-DD HH:MM" in IST, the bot pauses new signals for a
#      window around each,
#  (c) falls back to a volatility/spread-based "erratic market" read
#      using existing ATR data as a real-time signal when (b) is empty.
MACRO_EVENT_PAUSE_MIN_BEFORE = 30   # pause new signals starting 30 min before a listed event
MACRO_EVENT_PAUSE_MIN_AFTER  = 30   # and for 30 min after, while the market digests it

# Point 3: Squeeze detection thresholds. Verified via search rather than
# guessed — reported "deeply negative"/squeeze-signal funding rates on
# Binance cluster around -0.01% to -0.02% per 8h interval (one source
# explicitly labels -0.02% "Short squeeze potential"), and Binance caps
# funding at roughly +/-0.75-3% depending on the pair. -0.03% (-0.0003
# in Binance's raw fraction format) sits meaningfully beyond the reported
# squeeze-signal level — genuinely extreme, not just elevated.
SQUEEZE_FUNDING_EXTREME_NEG = -0.0003   # -0.03% — shorts paying heavily, over-leveraged short side
SQUEEZE_FUNDING_EXTREME_POS = 0.0003    # +0.03% — mirror case for long-squeeze setups
SQUEEZE_OI_RISING_PCT       = 3.0       # OI must have grown at least 3% in the last 15m reading
                                          # to count as "skyrocketing" rather than routine drift

SCHEDULED_MACRO_EVENTS = [
    # Add known high-impact events here as "YYYY-MM-DD HH:MM" (IST).
    # Example: "2026-08-01 18:00",  # FOMC rate decision
]

def is_macro_event_window():
    """
    Point 4(b): checks the manually-maintained scheduled events list.

    BUG FIX #1 (label parsing): entries saved via /addmacroevent with a
    label look like "2026-07-14 18:30  # CPI Data" (label suffix appended
    by that command). datetime.strptime() on the raw string throws
    "unconverted data remains: # CPI Data" — silently swallowed by the
    except below via `continue`, so any LABELED event was completely
    ignored with no log line, no warning, nothing.

    BUG FIX #2 (found while verifying fix #1 — more severe, pre-existing,
    affected EVERY entry regardless of label): this codebase uses
    `from zoneinfo import ZoneInfo` for IST (see top of file), NOT pytz.
    zoneinfo.ZoneInfo objects have NO `.localize()` method — that's a
    pytz-only API. `IST.localize(...)` therefore raised AttributeError
    on every single call, for every entry, unlabeled or not. That
    AttributeError was ALSO silently swallowed by the same broad
    except/continue. Net effect: is_macro_event_window() has returned
    (False, "") unconditionally since this feature was first built —
    the macro-event pause has never actually paused anything, for any
    entry, ever. Confirmed directly: reproduced the AttributeError,
    confirmed the working fix pattern (`.replace(tzinfo=IST)`, verified
    against get_ist_datetime()'s pattern) and confirmed it now compares
    correctly against real "now" values inside/outside the pause window.

    Both fixed together: split at '#' and strip before parsing (fix #1),
    and use `.replace(tzinfo=IST)` instead of `.localize()` (fix #2).
    """
    now = get_ist_datetime()
    for ev_str in SCHEDULED_MACRO_EVENTS:
        try:
            date_part = ev_str.split("#")[0].strip()
            ev_time = datetime.strptime(date_part, "%Y-%m-%d %H:%M").replace(tzinfo=IST)
        except Exception:
            continue
        window_start = ev_time - timedelta(minutes=MACRO_EVENT_PAUSE_MIN_BEFORE)
        window_end = ev_time + timedelta(minutes=MACRO_EVENT_PAUSE_MIN_AFTER)
        if window_start <= now <= window_end:
            return True, f"scheduled macro event at {ev_time.strftime('%H:%M IST')}"
    return False, ""

def is_weekend_low_liquidity():
    """Point 4(a): Sat/Sun chop detection — doesn't need an API, just the clock."""
    now = get_ist_datetime()
    # Saturday (5) and Sunday (6) — weekday() is 0=Mon .. 6=Sun
    return now.weekday() in (5, 6)

BTC_CORRELATED           = ["ETH","BNB","SOL","AVAX","NEAR","APT","SUI"]

# Point 3: Sector groupings — used for the "check the neighborhood" correlation
# check before confirming a signal. Coins not in any listed sector are treated
# as having no sector peers and skip this check (falls through, doesn't block).
SECTOR_GROUPS = {
    "gaming":     ["SAND","MANA","AXS","GALA","ENJ","PIXEL","LAB","GMT","APE"],
    "layer1":     ["ETH","SOL","AVAX","NEAR","APT","SUI","ADA","DOT","ATOM","TIA","SEI","ALGO","EGLD","FLOW","KAS"],
    "defi":       ["UNI","AAVE","MKR","SNX","COMP","CRV","SUSHI","LDO","CAKE","1INCH","DYDX","GMX","PENDLE"],
    "meme":       ["DOGE","SHIB","PEPE","WIF","FLOKI","BONK","ORDI","BOME","NOT","DOGS"],
    "ai_compute": ["RNDR","FET","WLD","AR","AKT","IO","THETA"],
    "l2":         ["ARB","OP","STRK","METIS","ZETA","MANTA"],
    "oracle_data":["LINK","PYTH","GRT","BLUR"],
}
# Reverse lookup: coin -> sector name, built once at import time
COIN_SECTOR = {}
for _sector, _coins in SECTOR_GROUPS.items():
    for _c in _coins:
        COIN_SECTOR[_c] = _sector
LEV_TIER_1               = ["BTC","ETH"]
LEV_TIER_2               = ["BNB","SOL","XRP","ADA","AVAX","DOT","LINK","LTC",
                             "NEAR","UNI","ATOM","APT","SUI","ARB","OP","INJ"]
LEV_TIER_3               = ["DOGE","SHIB","PEPE","WIF","FLOKI","BONK","DOGS",
                             "BOME","NOT","APE","GMT","CHZ","GALA","SAND","MANA"]
BOT_VERSION = "v32G"
BOT_NAME    = "TRADING SIGNAL MASTER"
BOT_HEADER  = f"⚙️ {BOT_NAME} {BOT_VERSION}"

def S(c="━",n=30): return c*n
def fmt_pnl(v): return ("🟢 " if v>=0 else "🔴 ")+f"{v:+.2f}%"

def save_active_trades():
    with trade_lock:
        try:
            s={k:{**v,"timestamp":v["timestamp"].isoformat(),
                  "expires_at":v["expires_at"].isoformat() if v.get("expires_at") else None}
               for k,v in active_trades.items()}
            with open("active_trades.json","w") as f: json.dump(s,f)
        except Exception as e: logger.error(f"save_active_trades: {e}")

def load_active_trades():
    global active_trades
    try:
        if os.path.exists("active_trades.json"):
            with open("active_trades.json") as f: data=json.load(f)
            active_trades={k:{**v,
                "timestamp":datetime.fromisoformat(v["timestamp"]),
                "expires_at":datetime.fromisoformat(v["expires_at"]) if v.get("expires_at") else None}
                for k,v in data.items()}
            logger.info(f"Loaded {len(active_trades)} active trades.")
    except Exception as e: logger.error(f"load_active_trades: {e}")

def save_trade_history():
    with trade_lock:
        try:
            with open("trades.json","w") as f: json.dump(pattern_stats,f)
        except Exception as e: logger.error(f"save_trade_history: {e}")

def load_trade_history():
    global pattern_stats
    try:
        if os.path.exists("trades.json"):
            with open("trades.json") as f: loaded=json.load(f)
            for p in pattern_stats:
                if p in loaded: pattern_stats[p]=loaded[p]
    except Exception as e: logger.error(f"load_trade_history: {e}")

def save_journal():
    try:
        with open("journal.json","w") as f: json.dump(trade_journal,f)
    except Exception as e: logger.error(f"save_journal: {e}")

def load_journal():
    global trade_journal
    try:
        if os.path.exists("journal.json"):
            with open("journal.json") as f: trade_journal=json.load(f)
        logger.info(f"Loaded {len(trade_journal)} journal entries.")
    except Exception as e: logger.error(f"load_journal: {e}")

def save_learning():
    try:
        with open("learning.json","w") as f:
            json.dump({"notes":learning_notes,"memory":market_memory,"clp":consecutive_loss_patterns},f)
    except Exception as e: logger.error(f"save_learning: {e}")

def load_learning():
    global learning_notes,market_memory,consecutive_loss_patterns
    try:
        if os.path.exists("learning.json"):
            with open("learning.json") as f: data=json.load(f)
            learning_notes=data.get("notes",[])
            market_memory.update(data.get("memory",{}))
            consecutive_loss_patterns=data.get("clp",{})
    except Exception as e: logger.error(f"load_learning: {e}")

def save_alerts():
    try:
        with open("alerts.json","w") as f: json.dump(price_alerts,f)
    except Exception as e: logger.error(f"save_alerts: {e}")

def load_alerts():
    global price_alerts
    try:
        if os.path.exists("alerts.json"):
            with open("alerts.json") as f: price_alerts=json.load(f)
    except Exception as e: logger.error(f"load_alerts: {e}")

def save_pending_signals():
    try:
        s={}
        for coin,sig in list(pending_signals.items()):
            d=dict(sig)
            if isinstance(d.get("timestamp"),datetime): d["timestamp"]=d["timestamp"].isoformat()
            if isinstance(d.get("expires_at"),datetime): d["expires_at"]=d["expires_at"].isoformat()
            s[coin]=d
        with open("pending_signals.json","w") as f: json.dump(s,f)
    except Exception as e: logger.error(f"save_pending: {e}")

def save_retest_watchlist():
    try:
        s={}
        for coin,w in list(retest_watchlist.items()):
            d=dict(w)
            if isinstance(d.get("logged_at"),datetime): d["logged_at"]=d["logged_at"].isoformat()
            s[coin]=d
        with open("retest_watchlist.json","w") as f: json.dump(s,f)
    except Exception as e: logger.error(f"save_retest_watchlist: {e}")

def load_retest_watchlist():
    global retest_watchlist
    try:
        if not os.path.exists("retest_watchlist.json"): return
        with open("retest_watchlist.json") as f: data=json.load(f)
        for coin,w in data.items():
            if w.get("logged_at"):
                try: w["logged_at"]=datetime.fromisoformat(w["logged_at"])
                except Exception: w["logged_at"]=get_ist_datetime()
            retest_watchlist[coin]=w
        logger.info(f"Loaded {len(retest_watchlist)} retest watchlist entries.")
    except Exception as e: logger.error(f"load_retest_watchlist: {e}")

def save_macro_events():
    """
    Point 2: Persists SCHEDULED_MACRO_EVENTS to disk so events added via
    /addmacroevent survive a bot restart — same JSON-file pattern as
    save_retest_watchlist()/save_pending_signals() above.
    """
    try:
        with open("macro_events.json","w") as f: json.dump(SCHEDULED_MACRO_EVENTS,f)
    except Exception as e: logger.error(f"save_macro_events: {e}")

def load_macro_events():
    global SCHEDULED_MACRO_EVENTS
    try:
        if not os.path.exists("macro_events.json"): return
        with open("macro_events.json") as f: data=json.load(f)
        if isinstance(data,list):
            SCHEDULED_MACRO_EVENTS = data
            logger.info(f"Loaded {len(SCHEDULED_MACRO_EVENTS)} macro events.")
    except Exception as e: logger.error(f"load_macro_events: {e}")

def load_pending_signals():
    global pending_signals
    try:
        if not os.path.exists("pending_signals.json"): return
        with open("pending_signals.json") as f: data=json.load(f)
        now=get_ist_datetime()
        for coin,sig in data.items():
            if sig.get("expires_at"):
                try:
                    exp=datetime.fromisoformat(sig["expires_at"])
                    if now>exp: continue
                    sig["expires_at"]=exp
                except Exception: continue
            if sig.get("timestamp"):
                try: sig["timestamp"]=datetime.fromisoformat(sig["timestamp"])
                except Exception: pass
            pending_signals[coin]=sig
        logger.info(f"Loaded {len(pending_signals)} pending signals.")
    except Exception as e: logger.error(f"load_pending: {e}")

def save_circuit_breaker():
    try:
        with open("cb.json","w") as f:
            json.dump({"daily_losses":daily_losses,
                       "circuit_breaker_until":circuit_breaker_until,
                       "date":str(last_reset_day)},f)
    except Exception as e: logger.error(f"save_cb: {e}")

def load_circuit_breaker():
    global daily_losses,circuit_breaker_until,last_reset_day
    try:
        if os.path.exists("cb.json"):
            with open("cb.json") as f: data=json.load(f)
            if data.get("date")==str(datetime.now(IST).date()):
                daily_losses=data.get("daily_losses",0)
                circuit_breaker_until=data.get("circuit_breaker_until")
    except Exception as e: logger.error(f"load_cb: {e}")

# ── Cloud save aliases — all use local JSON ──
def cloud_save_journal():       save_journal();       save_trade_history()
def cloud_save_pattern_stats(): save_trade_history()
def cloud_save_learning():      save_learning()
def cloud_save_active_trades(): save_active_trades()
def cloud_save_all():
    save_journal(); save_trade_history(); save_learning(); save_active_trades()

def cloud_load_all():
    """Load all data from local JSON files on startup."""
    load_active_trades(); load_trade_history()
    load_journal();       load_learning()
    logger.info("Local JSON data loaded.")

def format_price(p):
    if p>=1000:   return f"{p:.2f}"
    elif p>=1:    return f"{p:.4f}"
    elif p>=0.01: return f"{p:.6f}"
    else:         return f"{p:.8f}"

def get_ist_time():     return datetime.now(IST).strftime("%I:%M:%S %p IST")
def get_ist_datetime(): return datetime.now(IST)

def send_telegram(text, parse_mode="HTML", reply_markup=None, disable_web_page_preview=True):
    payload={"chat_id":CHAT_ID,"text":text,"parse_mode":parse_mode,
             "disable_web_page_preview":disable_web_page_preview}
    if reply_markup: payload["reply_markup"]=reply_markup
    try:
        res=requests.post(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage",
                          json=payload,timeout=15)
        if res.status_code!=200:
            logger.warning(f"Telegram [{res.status_code}]: {res.text[:200]}")
            # Retry without HTML parse mode if parse error
            if "parse" in res.text.lower() or "can't parse" in res.text.lower():
                payload2={"chat_id":CHAT_ID,"text":text,
                          "disable_web_page_preview":True}
                if reply_markup: payload2["reply_markup"]=reply_markup
                res2=requests.post(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage",
                                   json=payload2,timeout=15)
                return res2.status_code==200
        return res.status_code==200
    except requests.RequestException as e:
        logger.error(f"Telegram error: {e}"); return False

def safe_send(fn, label="command"):
    """Call any dashboard function safely — always sends something even on error."""
    try:
        result = fn()
        if result:
            send_telegram(result)
        else:
            send_telegram(f"⚠️ <b>{label}</b> returned empty — no data yet.")
    except Exception as e:
        logger.error(f"safe_send {label}: {e}")
        send_telegram(f"⚠️ <b>{label}</b> — error: <code>{str(e)[:100]}</code>")

def answer_callback(cbid, text="OK"):
    try:
        requests.post(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/answerCallbackQuery",
                      json={"callback_query_id":cbid,"text":text},timeout=10)
    except Exception as e:
        logger.warning(f"answerCallback: {e}")

def get_price(symbol):
    """
    Originally XAU/XAG (and briefly PAXG) were routed to Binance Futures
    here, since XAUUSDT/XAGUSDT are Futures-only TradFi Perpetuals with no
    Spot listing. XAU/XAG were later fully removed from the bot, and PAXG
    was moved back to Spot after live logs confirmed it hit the same
    Geo-Block (451) restriction — see FUTURES_ONLY_SYMBOLS's definition
    above for that history. FUTURES_ONLY_SYMBOLS is now an empty set, so
    every symbol including PAXG currently routes through Spot
    (data-api.binance.vision) via the branch below. Kept as a per-symbol
    routing switch (not deleted) since it's a real, working mechanism if
    a genuinely Futures-only symbol is ever added back to the bot.
    """
    price_url = BINANCE_FUTURES_PRICE_URL if symbol in FUTURES_ONLY_SYMBOLS else BINANCE_PRICE_URL
    try:
        res=requests.get(price_url,params={"symbol":symbol},timeout=10)
        if res.status_code==200: return float(res.json()["price"])
        if symbol in FUTURES_ONLY_SYMBOLS:
            # DORMANT as of the PAXG 451 fix: FUTURES_ONLY_SYMBOLS is now
            # empty, so this branch can never fire for anyone currently.
            # Left in place rather than deleted — becomes live again
            # automatically if any symbol is ever added back to that set.
            logger.warning(f"get_price {symbol}: Futures endpoint returned {res.status_code} — "
                          f"if this persists for PAXG, remove it from FUTURES_ONLY_SYMBOLS")
        return None
    except Exception as e:
        logger.warning(f"get_price {symbol}: {e}"); return None

def get_klines(symbol,interval,limit=100):
    """See get_price's docstring for the Futures-routing reasoning."""
    kline_url = BINANCE_FUTURES_KLINE_URL if symbol in FUTURES_ONLY_SYMBOLS else BINANCE_KLINE_URL
    try:
        res=requests.get(kline_url,
                         params={"symbol":symbol,"interval":interval,"limit":limit},timeout=10)
        if res.status_code==200: return res.json()
        if symbol in FUTURES_ONLY_SYMBOLS:
            # DORMANT — see get_price's matching note above.
            logger.warning(f"get_klines {symbol}: Futures endpoint returned {res.status_code} — "
                          f"if this persists for PAXG, remove it from FUTURES_ONLY_SYMBOLS")
        return []
    except Exception as e:
        logger.warning(f"get_klines {symbol}: {e}"); return []

def calculate_ema(closes,period):
    if len(closes)<period: return None
    ema=sum(closes[:period])/period
    k=2.0/(period+1)
    for p in closes[period:]: ema=p*k+ema*(1-k)
    return ema

def calculate_rsi(closes,period=14):
    if len(closes)<period+1: return 50.0
    gains,losses=[],[]
    for i in range(1,len(closes)):
        d=closes[i]-closes[i-1]
        gains.append(max(0,d)); losses.append(max(0,-d))
    ag=sum(gains[-period:])/period; al=sum(losses[-period:])/period
    return 100.0-(100.0/(1+ag/al)) if al!=0 else 100.0

def calculate_atr(klines,period=14):
    if len(klines)<period+1: return 0.0
    trs=[]
    for i in range(1,len(klines)):
        h=float(klines[i][2]); l=float(klines[i][3]); pc=float(klines[i-1][4])
        trs.append(max(h-l,abs(h-pc),abs(l-pc)))
    return sum(trs[-period:])/period

def calculate_adx(klines,period=14):
    if len(klines)<period*2+1: return 30.0
    try:
        highs=[float(k[2]) for k in klines]; lows=[float(k[3]) for k in klines]
        closes=[float(k[4]) for k in klines]
        pdm,mdm,trl=[],[],[]
        for i in range(1,len(klines)):
            hd=highs[i]-highs[i-1]; ld=lows[i-1]-lows[i]
            pdm.append(hd if hd>ld and hd>0 else 0)
            mdm.append(ld if ld>hd and ld>0 else 0)
            trl.append(max(highs[i]-lows[i],abs(highs[i]-closes[i-1]),abs(lows[i]-closes[i-1])))
        def smooth(data,p):
            s=sum(data[:p]); r=[s]
            for v in data[p:]: s=s-s/p+v; r.append(s)
            return r
        atr_s=smooth(trl,period); pdm_s=smooth(pdm,period); mdm_s=smooth(mdm,period)
        pdi=[100*p/a if a else 0 for p,a in zip(pdm_s,atr_s)]
        mdi=[100*m/a if a else 0 for m,a in zip(mdm_s,atr_s)]
        dx=[100*abs(p-m)/(p+m) if (p+m) else 0 for p,m in zip(pdi,mdi)]
        return sum(dx[-period:])/period if len(dx)>=period else 30.0
    except Exception: return 30.0

def calculate_vwap(klines):
    try:
        tp=sum(((float(k[2])+float(k[3])+float(k[4]))/3)*float(k[5]) for k in klines)
        tv=sum(float(k[5]) for k in klines)
        return tp/tv if tv>0 else None
    except Exception: return None

def get_dol_signal(klines):
    try:
        highs=[float(k[2]) for k in klines[-30:]]; lows=[float(k[3]) for k in klines[-30:]]
        closes=[float(k[4]) for k in klines[-30:]]
        max_high=max(highs[-10:]); min_low=min(lows[-10:])
        eq_highs=sum(1 for h in highs[-10:] if abs(h-max_high)/max_high<0.003)
        eq_lows=sum(1 for l in lows[-10:] if abs(l-min_low)/min_low<0.003)
        last_range=highs[-1]-lows[-1]
        upper_wick=highs[-1]-max(closes[-1],float(klines[-1][1]))
        lower_wick=min(closes[-1],float(klines[-1][1]))-lows[-1]
        if eq_highs>=3 and eq_lows<2:   return "Liquidity ABOVE - sell sweep likely"
        elif eq_lows>=3 and eq_highs<2: return "Liquidity BELOW - buy sweep likely"
        elif upper_wick>last_range*0.6: return "Upper wick rejection - sellers strong"
        elif lower_wick>last_range*0.6: return "Lower wick rejection - buyers strong"
        else:                           return "No clear liquidity imbalance"
    except Exception: return "N/A"

def detect_rsi_divergence(closes):
    if len(closes)<10: return None
    try:
        prices=closes[-6:]
        rsi_vals=[calculate_rsi(closes[:i+1]) for i in range(len(closes)-6,len(closes))]
        if prices[-1]<prices[0] and rsi_vals[-1]>rsi_vals[0]: return "BULLISH_DIV"
        if prices[-1]>prices[0] and rsi_vals[-1]<rsi_vals[0]: return "BEARISH_DIV"
        return None
    except Exception: return None

def detect_market_structure(klines):
    """Audit Fix #7: Real market structure — HH/HL/LH/LL + BOS + CHOCH detection."""
    if len(klines) < 30: return {"bias": "neutral", "bos": False, "choch": False, "swing_high": 0, "swing_low": 0}
    highs = [float(k[2]) for k in klines]
    lows  = [float(k[3]) for k in klines]
    closes= [float(k[4]) for k in klines]
    # Find swing points (local highs/lows over 5-bar window)
    swing_highs, swing_lows = [], []
    for i in range(5, len(klines) - 5):
        if highs[i] == max(highs[i-5:i+6]): swing_highs.append((i, highs[i]))
        if lows[i]  == min(lows[i-5:i+6]):  swing_lows.append((i, lows[i]))
    if len(swing_highs) < 2 or len(swing_lows) < 2:
        return {"bias": "neutral", "bos": False, "choch": False,
                "swing_high": max(highs[-20:]), "swing_low": min(lows[-20:])}
    # Last 3 swing points for structure
    sh = swing_highs[-3:]; sl = swing_lows[-3:]
    hh = len(sh) >= 2 and sh[-1][1] > sh[-2][1]   # Higher High
    hl = len(sl) >= 2 and sl[-1][1] > sl[-2][1]   # Higher Low
    lh = len(sh) >= 2 and sh[-1][1] < sh[-2][1]   # Lower High
    ll = len(sl) >= 2 and sl[-1][1] < sl[-2][1]   # Lower Low
    # Market bias
    if hh and hl:   bias = "bullish"
    elif lh and ll: bias = "bearish"
    else:           bias = "neutral"
    # Break of Structure (BOS) — price breaks last swing high/low in trend direction
    last_sh = swing_highs[-1][1] if swing_highs else max(highs[-20:])
    last_sl = swing_lows[-1][1]  if swing_lows  else min(lows[-20:])
    bos_bull  = closes[-1] > last_sh and bias == "bullish"
    bos_bear  = closes[-1] < last_sl and bias == "bearish"
    bos = bos_bull or bos_bear
    # Change of Character (CHOCH) — price breaks structure against current bias
    choch = (closes[-1] < last_sl and bias == "bullish") or \
            (closes[-1] > last_sh and bias == "bearish")
    return {"bias": bias, "bos": bos, "choch": choch,
            "swing_high": last_sh, "swing_low": last_sl,
            "hh": hh, "hl": hl, "lh": lh, "ll": ll}


def detect_supply_demand_zones(klines):
    """Audit Fix #5: Professional S&D zones — unmitigated, multi-retest, volume-confirmed."""
    zones = {"demand": [], "supply": []}
    if len(klines) < 30: return zones
    try:
        closes = [float(k[4]) for k in klines]
        opens  = [float(k[1]) for k in klines]
        highs  = [float(k[2]) for k in klines]
        lows   = [float(k[3]) for k in klines]
        vols   = [float(k[5]) for k in klines]
        avg_vol = sum(vols[-30:]) / 30
        for i in range(5, len(klines) - 3):
            body = abs(closes[i] - opens[i])
            avg_body = sum(abs(closes[j] - opens[j]) for j in range(i-4, i)) / 4
            if avg_body == 0: continue
            is_strong_move = body > avg_body * 1.8
            high_vol = vols[i] > avg_vol * 1.3
            if not (is_strong_move and high_vol): continue
            zone_high = max(highs[i-2:i+1])
            zone_low  = min(lows[i-2:i+1])
            # Check unmitigated: price hasn't returned to zone since creation
            future_closes = closes[i+1:]
            if closes[i] > opens[i]:  # Bullish impulse → demand zone below
                mitigated = any(c < zone_low for c in future_closes)
                if not mitigated:
                    # Count retests (price came close but bounced)
                    retests = sum(1 for c in future_closes if zone_low * 0.995 <= c <= zone_high * 1.005)
                    zones["demand"].append({
                        "high": zone_high, "low": zone_low,
                        "retests": retests, "vol_strength": vols[i] / avg_vol,
                        "unmitigated": True
                    })
            else:  # Bearish impulse → supply zone above
                mitigated = any(c > zone_high for c in future_closes)
                if not mitigated:
                    retests = sum(1 for c in future_closes if zone_low * 0.995 <= c <= zone_high * 1.005)
                    zones["supply"].append({
                        "high": zone_high, "low": zone_low,
                        "retests": retests, "vol_strength": vols[i] / avg_vol,
                        "unmitigated": True
                    })
        # Sort by quality: unmitigated zones with 1-2 retests are strongest
        for key in zones:
            zones[key].sort(key=lambda z: (z["retests"] in [1,2], z["vol_strength"]), reverse=True)
    except Exception as e:
        logger.warning(f"S&D zones: {e}")
    return zones


# get_orderbook_imbalance was completely deleted here (Point 2) — data was
# thin, frequently returned "N/A", and was dragging down confirmation
# scorecard grades on missing data rather than genuine signal weakness.
# Replaced throughout (get_signal_grade, compute_confirmation_bonus, and
# the Telegram message) with a real BTC 1-Hour trend alignment check
# (👑 BTC Aligned) — see get_signal_grade's docstring for the full
# before/after scoring breakdown.


def calculate_supertrend(klines, period=10, multiplier=3.0):
    """Audit Fix #6: Real SuperTrend with proper band tracking over time."""
    if len(klines) < period + 5: return None
    try:
        highs  = [float(k[2]) for k in klines]
        lows   = [float(k[3]) for k in klines]
        closes = [float(k[4]) for k in klines]
        # Calculate ATR for each bar
        trs = []
        for i in range(1, len(klines)):
            h = highs[i]; l = lows[i]; pc = closes[i-1]
            trs.append(max(h - l, abs(h - pc), abs(l - pc)))
        # Smooth ATR
        atr_vals = []
        atr = sum(trs[:period]) / period
        atr_vals.append(atr)
        for tr in trs[period:]:
            atr = (atr * (period - 1) + tr) / period
            atr_vals.append(atr)
        # Calculate SuperTrend bands with proper state tracking
        direction = 1  # 1=BUY, -1=SELL
        prev_upper = prev_lower = 0
        for i in range(len(atr_vals)):
            idx = i + period
            if idx >= len(closes): break
            hl2 = (highs[idx] + lows[idx]) / 2
            upper = hl2 + multiplier * atr_vals[i]
            lower = hl2 - multiplier * atr_vals[i]
            # Band continuity rules
            if i > 0:
                lower = max(lower, prev_lower) if closes[idx-1] > prev_lower else lower
                upper = min(upper, prev_upper) if closes[idx-1] < prev_upper else upper
            prev_upper = upper; prev_lower = lower
            if closes[idx] > upper:   direction = 1
            elif closes[idx] < lower: direction = -1
        return "BUY" if direction == 1 else "SELL"
    except Exception: return None


def detect_bull_flag(closes, highs, lows, vols, avg_vol):
    """Audit Fix #1: Professional Bull Flag — impulse + consolidation + volume contraction + breakout."""
    if len(closes) < 30: return False
    # Step 1: Strong impulse (5-10 bars of strong up move)
    impulse_bars = closes[-25:-15]
    impulse_gain = (impulse_bars[-1] - impulse_bars[0]) / impulse_bars[0] * 100 if impulse_bars[0] > 0 else 0
    if impulse_gain < 3.0: return False  # Need at least 3% impulse
    # Step 2: Consolidation channel (last 10 bars stay within tight range)
    consol = closes[-15:-3]
    consol_range = (max(consol) - min(consol)) / min(consol) * 100 if min(consol) > 0 else 999
    if consol_range > 4.0: return False  # Channel must be tight (<4%)
    # Step 3: Volume contraction during consolidation
    impulse_avg_vol = sum(vols[-25:-15]) / 10
    consol_avg_vol  = sum(vols[-15:-3])  / 12
    vol_contracting = consol_avg_vol < impulse_avg_vol * 0.8  # 20% drop in volume
    if not vol_contracting: return False
    # Step 4: Breakout — last close breaks above consolidation high with volume
    breakout_level = max(highs[-15:-3])
    breakout = closes[-1] > breakout_level and vols[-1] > avg_vol * 1.3
    return breakout


def detect_bear_flag(closes, highs, lows, vols, avg_vol):
    """Professional Bear Flag — mirror of bull flag."""
    if len(closes) < 30: return False
    impulse_bars = closes[-25:-15]
    impulse_drop = (impulse_bars[0] - impulse_bars[-1]) / impulse_bars[0] * 100 if impulse_bars[0] > 0 else 0
    if impulse_drop < 3.0: return False
    consol = closes[-15:-3]
    consol_range = (max(consol) - min(consol)) / min(consol) * 100 if min(consol) > 0 else 999
    if consol_range > 4.0: return False
    impulse_avg_vol = sum(vols[-25:-15]) / 10
    consol_avg_vol  = sum(vols[-15:-3])  / 12
    if consol_avg_vol >= impulse_avg_vol * 0.8: return False
    breakout_level = min(lows[-15:-3])
    return closes[-1] < breakout_level and vols[-1] > avg_vol * 1.3


def detect_double_bottom_pro(highs, lows, closes, vols, price, avg_vol):
    """Audit Fix #1: Professional Double Bottom — two clear lows + neckline + volume confirmation."""
    if len(lows) < 50: return False
    # Find the two lowest points in last 50 bars (separated by at least 8 bars)
    region = lows[-50:]
    low1_idx = region.index(min(region))
    # Find second low (at least 8 bars away)
    second_region_start = min(low1_idx + 8, len(region) - 1)
    if second_region_start >= len(region): return False
    region2 = region[second_region_start:]
    if not region2: return False
    low2_val = min(region2)
    # Two lows must be within 1.5% of each other (tighter than before)
    if abs(low1_idx - (second_region_start + region2.index(low2_val))) < 8: return False
    low1_val = region[low1_idx]
    similarity = abs(low1_val - low2_val) / low1_val if low1_val > 0 else 1
    if similarity > 0.015: return False  # Within 1.5%
    # Neckline breakout — current price must break above the high between the two lows
    neckline = max(highs[-50 + low1_idx: -50 + second_region_start + region2.index(low2_val) + 1] or [0])
    if neckline == 0: return False
    breakout = price > neckline * 1.002  # 0.2% buffer
    # Volume should increase on breakout
    vol_ok = vols[-1] > avg_vol * 1.1
    return breakout and vol_ok


def detect_double_top_pro(highs, lows, closes, vols, price, avg_vol):
    """Professional Double Top — mirror of double bottom."""
    if len(highs) < 50: return False
    region = highs[-50:]
    high1_idx = region.index(max(region))
    second_region_start = min(high1_idx + 8, len(region) - 1)
    if second_region_start >= len(region): return False
    region2 = region[second_region_start:]
    if not region2: return False
    high2_val = max(region2)
    high1_val = region[high1_idx]
    if abs(high1_val - high2_val) / high1_val > 0.015: return False
    neckline = min(lows[-50 + high1_idx: -50 + second_region_start + region2.index(high2_val) + 1] or [999999])
    if neckline == 999999: return False
    breakdown = price < neckline * 0.998
    vol_ok = vols[-1] > avg_vol * 1.1
    return breakdown and vol_ok


def detect_volatility_contraction(closes, highs, lows, vols, price):
    """
    Point 2: Volatility Contraction Pattern (VCP) — catches the setup BEFORE
    the breakout candle and its volume spike, instead of after.

    Looks for: a prior impulse move, followed by a tightening range with
    shrinking (dying) volume, price resting just under resistance / just
    above support. This is the "coiling" phase — the bot flags it as a
    signal candidate while the crowd is still waiting for volume confirmation.

    Returns (direction, tightness_score) or (None, 0) if no contraction found.
    """
    if len(closes) < 40: return None, 0
    lookback = closes[-40:]
    look_highs = highs[-40:]
    look_lows = lows[-40:]
    look_vols = vols[-40:]

    # Split into: impulse window (older) vs contraction window (recent 12 candles)
    impulse = lookback[:-12]
    contraction = lookback[-12:]
    contraction_highs = look_highs[-12:]
    contraction_lows = look_lows[-12:]
    contraction_vols = look_vols[-12:]
    impulse_vols = look_vols[:-12]

    if len(impulse) < 10 or not impulse_vols: return None, 0

    # 1. Was there a real prior impulse (up or down) into this range?
    impulse_move_pct = (impulse[-1] - impulse[0]) / impulse[0] * 100 if impulse[0] > 0 else 0

    # 2. Is the recent range genuinely tight (contracting)?
    range_high = max(contraction_highs)
    range_low = min(contraction_lows)
    range_pct = (range_high - range_low) / price * 100 if price > 0 else 99

    # 3. Is volume dying out in the contraction vs the impulse?
    avg_impulse_vol = sum(impulse_vols) / len(impulse_vols)
    avg_contraction_vol = sum(contraction_vols) / len(contraction_vols)
    vol_dying = avg_contraction_vol < avg_impulse_vol * 0.75

    # 4. Where does current price sit inside the tight range? (resting near the top = bullish coil)
    pos_in_range = (price - range_low) / (range_high - range_low) if range_high > range_low else 0.5

    tight_enough = range_pct < 3.5  # tight coil, not a wide chop
    if not tight_enough or not vol_dying:
        return None, 0

    tightness_score = max(0, 100 - range_pct * 15)  # tighter range = higher score

    # Bullish coil: prior impulse up, resting in upper half of tight range, dying volume
    if impulse_move_pct > 4.0 and pos_in_range > 0.55:
        return "BUY", tightness_score
    # Bearish coil: prior impulse down, resting in lower half of tight range, dying volume
    if impulse_move_pct < -4.0 and pos_in_range < 0.45:
        return "SELL", tightness_score

    return None, 0


def detect_pre_breakout_compression(closes, highs, lows, vols, price, sup, res, direction_bias):
    """
    Pre-Breakout Compression — catches the coil BEFORE a BOS Breakout
    fires, not after. Genuinely distinct from detect_volatility_contraction
    (VCP): VCP requires a prior impulse move (impulse_move_pct > 4.0) into
    the tightening range — it's "coil after a run." This pattern requires
    NO prior impulse at all — a coin can be quietly pinning against
    resistance with a flat/mixed run-up and this still fires, which VCP's
    impulse-gate would miss entirely. Checked before writing: confirmed
    this is a real gap, not a duplicate of existing logic.

    Conditions (as specified):
    1. Price sitting within 1% of major resistance (for a bullish
       compression) or support (bearish mirror) — using the same sup/res
       swing levels already computed by detect_market_structure() in the
       caller, no new data source needed.
    2. The last 3-5 candles are tiny/tight (small range relative to
       recent volatility) — "institutional accumulation/coiling," not
       requiring a large prior move like VCP does.
    3. Volume is quiet (below-average) — the crowd hasn't noticed yet.

    Returns (direction, tightness_score) or (None, 0).
    """
    if len(closes) < 20 or res <= 0 or sup <= 0:
        return None, 0

    recent_highs = highs[-5:]
    recent_lows = lows[-5:]
    recent_vols = vols[-5:]
    avg_vol_20 = sum(vols[-20:]) / 20 if len(vols) >= 20 else (vols[-1] if vols else 1)

    # Condition 3: quiet volume over the last 3-5 candles
    avg_recent_vol = sum(recent_vols) / len(recent_vols)
    volume_quiet = avg_recent_vol < avg_vol_20 * 0.85

    # Condition 2: tiny/tight candles — small range relative to a normal
    # 20-candle ATR-like baseline, checked across the last 3-5 candles
    typical_range = (max(highs[-20:]) - min(lows[-20:])) / 20 if len(highs) >= 20 else 1
    tight_candles = all((h - l) < typical_range * 0.8 for h, l in zip(recent_highs, recent_lows)) if typical_range > 0 else False

    if not volume_quiet or not tight_candles:
        return None, 0

    # Condition 1: pinning within 1% of resistance (bullish) or support (bearish)
    dist_to_res_pct = abs(res - price) / res * 100 if res > 0 else 99
    dist_to_sup_pct = abs(price - sup) / sup * 100 if sup > 0 else 99

    tightness_score = max(0, 100 - (max(recent_highs) - min(recent_lows)) / price * 100 * 20)

    if dist_to_res_pct <= 1.0 and direction_bias != "bearish":
        return "BUY", tightness_score
    if dist_to_sup_pct <= 1.0 and direction_bias != "bullish":
        return "SELL", tightness_score

    return None, 0


def detect_liquidity_sweep(klines, highs, lows, closes, opens, sup, res, ms):
    """
    Liquidity Sweep (failed breakout / stop hunt), per instruction.

    SCOPE NOTE: the instruction described this against a "known supply or
    demand zone." detect_patterns() does not receive S/D zone data (zones
    are computed separately, in scan_coins/format_and_send, via
    get_htf_zones — adding a zones parameter here would require touching
    all 5 call sites of detect_patterns and adding new HTF zone fetches
    to several scan paths that don't currently make them, multiplying API
    cost significantly). Implemented instead against the structural swing
    high/low (`sup`/`res`, already computed from detect_market_structure) —
    both represent "a level that matters," and this keeps the change
    contained to detect_patterns without new fetches or signature changes
    across the codebase. Flagging this as a real interpretation choice,
    not a silent substitution.

    Looks for, in the most recent 1-3 candles:
    1. A wick that pierces beyond the structural level (sup for a bullish
       sweep-reversal, res for a bearish one) — this is the stop-hunt,
       retail stops on the wrong side of the level get triggered.
    2. The candle's CLOSE reverts back inside the level — the piercing
       was rejected, not accepted.
    3. A Change of Character (ms["choch"]) confirms the reversal is real,
       not just a random wick.

    This is deliberately a narrower, higher-conviction condition than
    ChoCh alone — it requires the specific sweep-then-reject candle
    shape on top of the same structure-shift signal.

    Returns (direction, sweep_strength) or (None, 0).
    """
    if len(closes) < 10 or not ms["choch"]:
        return None, 0

    # Check the most recent 1-3 candles for the sweep-and-reject shape
    for i in range(1, 4):
        if i > len(closes): break
        idx = -i
        c_open, c_high, c_low, c_close = opens[idx], highs[idx], lows[idx], closes[idx]
        candle_range = c_high - c_low
        if candle_range <= 0: continue

        # Bullish sweep: wick pierces BELOW support, close reverts back above it
        pierced_support = c_low < sup and sup > 0
        closed_back_above = c_close > sup
        lower_wick_pct = (min(c_open, c_close) - c_low) / candle_range * 100
        if pierced_support and closed_back_above and lower_wick_pct > 40:
            if ms["bias"] == "bullish" or ms["choch"]:
                sweep_depth_pct = abs(sup - c_low) / sup * 100 if sup > 0 else 0
                strength = min(100, 60 + sweep_depth_pct * 20 + lower_wick_pct * 0.3)
                return "BUY", strength

        # Bearish sweep: wick pierces ABOVE resistance, close reverts back below it
        pierced_resistance = c_high > res and res > 0
        closed_back_below = c_close < res
        upper_wick_pct = (c_high - max(c_open, c_close)) / candle_range * 100
        if pierced_resistance and closed_back_below and upper_wick_pct > 40:
            if ms["bias"] == "bearish" or ms["choch"]:
                sweep_depth_pct = abs(c_high - res) / res * 100 if res > 0 else 0
                strength = min(100, 60 + sweep_depth_pct * 20 + upper_wick_pct * 0.3)
                return "SELL", strength

    return None, 0


def detect_patterns(symbol, klines, price, btc_trend):
    """
    Upgraded pattern detection with:
    - Professional Bull/Bear Flag (impulse + consolidation + vol contraction + breakout)
    - Professional Double Bottom/Top (neckline breakout + volume)
    - Real market structure (HH/HL/LH/LL + BOS)
    - BTC independence for strong altcoin setups
    - Order book awareness built into scoring
    """
    if len(klines) < 50: return []
    closes = [float(k[4]) for k in klines]
    opens  = [float(k[1]) for k in klines]
    highs  = [float(k[2]) for k in klines]
    lows   = [float(k[3]) for k in klines]
    vols   = [float(k[5]) for k in klines]
    avg_vol = sum(vols[-20:]) / 20
    rsi    = calculate_rsi(closes)
    ema20  = calculate_ema(closes, 20)
    ema50  = calculate_ema(closes, 50)
    adx    = calculate_adx(klines)
    # Minimum activity filter
    if ((max(highs[-20:]) - min(lows[-20:])) / price) * 100 < 1.5: return []
    if adx < ADX_MIN_TREND: return []
    # Market structure
    ms = detect_market_structure(klines)
    ms_bias = ms["bias"]  # "bullish", "bearish", "neutral"
    # Audit Fix #4: BTC independence — allow strong altcoin structure to override BTC
    # If altcoin has clear HH+HL (bullish structure), allow BUY even if BTC neutral
    # If altcoin has clear LH+LL (bearish structure), allow SELL even if BTC neutral
    alt_bull_ok  = btc_trend == 1 or ms_bias == "bullish"
    alt_bear_ok  = btc_trend == -1 or ms_bias == "bearish"
    p = []
    sup = ms["swing_low"] if ms["swing_low"] > 0 else min(lows[-30:-1])
    res = ms["swing_high"] if ms["swing_high"] > 0 else max(highs[-30:-1])

    # ── TIER 1 / TIER 2 BASE SCORES (Hard AI Cap) ───────────────
    # Tier 1 (AI-eligible): Volatility Contraction, Double Bottom/Top,
    #   Bull/Bear Flags, Zone Bounces (Support/Resistance), BOS Breakout.
    #   Base 88.0 — chosen specifically because it's the value in the
    #   stated 88.0-90.0 range that genuinely "easily hits the AI
    #   threshold with just a little volume": 88.0 + zone bonus (+3.5)
    #   + one more confirmation reaches 92.2+ without needing everything
    #   maxed out. At 90.0, even strong volume alone falls short (92.0).
    #
    # Tier 2 (auto-execute only, mathematically banned from AI):
    #   Engulfing, RSI Reversal, EMA Trend, Pullback, Momentum Surge,
    #   Volume Spike. Base 75.0. These are EXCLUDED from the Zone, BOS,
    #   and ChoCh bonuses entirely in compute_confirmation_bonus (not
    #   just "start lower" — structurally cannot receive them), so their
    #   real ceiling is 75.0 + HTF(3.0) + OB(2.2) + vol(2.0) + ADX(1.5)
    #   = 83.7, safely under both the stated 85.0 ceiling and nowhere
    #   near 92.2. This is a hard mathematical guarantee, not a
    #   probabilistic one.
    TIER1_BASE = 88.0
    TIER2_BASE = 75.0

    # ── Volatility Contraction Pattern — Tier 1 ──
    vcp_dir, vcp_tightness = detect_volatility_contraction(closes, highs, lows, vols, price)
    if vcp_dir == "BUY" and alt_bull_ok:
        p.append(("Volatility Contraction (Coiling)", TIER1_BASE, "BUY"))
    elif vcp_dir == "SELL" and alt_bear_ok:
        p.append(("Volatility Contraction (Coiling)", TIER1_BASE, "SELL"))

    # ── Pre-Breakout Compression — Tier 1, catches the coil BEFORE a BOS ──
    # fires, buying before the crowd sees the breakout (the fix for
    # Claude correctly rejecting already-broken-out BOS signals as
    # STAGE: LATE — this pattern is designed to reach the AI while the
    # setup is still genuinely STAGE: EARLY).
    pbc_dir, pbc_tightness = detect_pre_breakout_compression(closes, highs, lows, vols, price, sup, res, ms_bias)
    if pbc_dir == "BUY" and alt_bull_ok:
        p.append(("Pre-Breakout Compression", TIER1_BASE, "BUY"))
    elif pbc_dir == "SELL" and alt_bear_ok:
        p.append(("Pre-Breakout Compression", TIER1_BASE, "SELL"))

    # ── Professional Bull Flag — Tier 1 ──
    if detect_bull_flag(closes, highs, lows, vols, avg_vol) and alt_bull_ok:
        p.append(("Bull Flag Break", TIER1_BASE, "BUY"))

    # ── Professional Bear Flag — Tier 1 ──
    if detect_bear_flag(closes, highs, lows, vols, avg_vol) and alt_bear_ok:
        p.append(("Bear Flag Break", TIER1_BASE, "SELL"))

    # ── Breakout with structure confirmation — Tier 1 (zone-adjacent behavior) ──
    if closes[-1] > max(highs[-20:-1]) and vols[-1] > avg_vol * 1.4:
        if alt_bull_ok:
            p.append(("Breakout", TIER1_BASE, "BUY"))
    elif closes[-1] < min(lows[-20:-1]) and vols[-1] > avg_vol * 1.4:
        if alt_bear_ok:
            p.append(("Breakout", TIER1_BASE, "SELL"))

    # ── Bullish Engulfing — Tier 2 (auto-execute only) ──
    if opens[-2] > closes[-2] and opens[-1] < closes[-2] and closes[-1] > opens[-2]:
        body_ratio = (closes[-1] - opens[-1]) / (opens[-2] - closes[-2]) if (opens[-2] - closes[-2]) > 0 else 0
        if body_ratio > 1.2 and alt_bull_ok:  # Must engulf by 20%
            p.append(("Bullish Engulfing", TIER2_BASE, "BUY"))

    # ── Bearish Engulfing — Tier 2 ──
    elif opens[-2] < closes[-2] and opens[-1] > closes[-2] and closes[-1] < opens[-2]:
        body_ratio = (opens[-1] - closes[-1]) / (closes[-2] - opens[-2]) if (closes[-2] - opens[-2]) > 0 else 0
        if body_ratio > 1.2 and alt_bear_ok:
            p.append(("Bearish Engulfing", TIER2_BASE, "SELL"))

    # ── EMA Trend — Tier 2 ──
    if ema20 and ema50:
        if price > ema20 > ema50 and alt_bull_ok:
            p.append(("EMA Trend", TIER2_BASE, "BUY"))
        elif price < ema20 < ema50 and alt_bear_ok:
            p.append(("EMA Trend", TIER2_BASE, "SELL"))

    # ── Pullback to 20 EMA — Tier 2 ──
    if ema20 and abs(price - ema20) / ema20 < 0.008:
        if price > ema50 and alt_bull_ok and ms_bias == "bullish":
            p.append(("Pullback to 20 EMA", TIER2_BASE, "BUY"))
        elif price < ema50 and alt_bear_ok and ms_bias == "bearish":
            p.append(("Pullback to 20 EMA", TIER2_BASE, "SELL"))

    # ── RSI Reversal (extreme only) — Tier 2 ──
    if rsi < 28 and alt_bull_ok:   p.append(("RSI Reversal", TIER2_BASE, "BUY"))
    elif rsi > 72 and alt_bear_ok: p.append(("RSI Reversal", TIER2_BASE, "SELL"))

    # ── Momentum Surge — Tier 2 ──
    mom = (closes[-1] - closes[-4]) / closes[-4] * 100 if len(closes) > 4 else 0
    if mom > 3.5 and vols[-1] > avg_vol * 1.2 and alt_bull_ok:
        p.append(("Momentum Surge", TIER2_BASE, "BUY"))
    elif mom < -3.5 and vols[-1] > avg_vol * 1.2 and alt_bear_ok:
        p.append(("Momentum Surge", TIER2_BASE, "SELL"))

    # ── Volume Spike — Tier 2 ──
    if vols[-1] > avg_vol * 3.0:
        direction = "BUY" if closes[-1] > opens[-1] else "SELL"
        if (direction == "BUY" and alt_bull_ok) or (direction == "SELL" and alt_bear_ok):
            p.append(("Volume Spike", TIER2_BASE, direction))

    # ── Support Bounce (Zone Bounce) — Tier 1 ──
    if price <= sup * 1.008 and closes[-1] > opens[-1] and alt_bull_ok:
        p.append(("Support Bounce", TIER1_BASE, "BUY"))

    # ── Resistance Rejection (Zone Bounce) — Tier 1 ──
    if price >= res * 0.992 and closes[-1] < opens[-1] and alt_bear_ok:
        p.append(("Resistance Rejection", TIER1_BASE, "SELL"))

    # ── Professional Double Bottom — Tier 1 ──
    if detect_double_bottom_pro(highs, lows, closes, vols, price, avg_vol) and alt_bull_ok:
        p.append(("Double Bottom", TIER1_BASE, "BUY"))

    # ── Professional Double Top — Tier 1 ──
    if detect_double_top_pro(highs, lows, closes, vols, price, avg_vol) and alt_bear_ok:
        p.append(("Double Top", TIER1_BASE, "SELL"))

    # ── Volume Breakout — Tier 1 ──
    if price > res and vols[-1] > avg_vol * 2.2 and alt_bull_ok:
        p.append(("Volume Breakout", TIER1_BASE, "BUY"))

    # ── BOS Signal (pure structure break) — Tier 1 ──
    if ms["bos"] and not ms["choch"]:
        if ms_bias == "bullish" and alt_bull_ok:
            p.append(("BOS Breakout", TIER1_BASE, "BUY"))
        elif ms_bias == "bearish" and alt_bear_ok:
            p.append(("BOS Breakout", TIER1_BASE, "SELL"))

    # ── Change of Character (ChoCh) — Tier 1, "the ultimate human prediction tool" ──
    # Lower Lows -> hits Demand Zone -> sudden Higher High (or the bearish mirror).
    # detect_market_structure() already computes ms["choch"]; this pattern makes
    # it an explicit, tradeable signal instead of the flag being nearly unused.
    # Direction is inferred from which way structure just flipped: a bullish
    # ChoCh means price broke the recent swing HIGH against a prior bearish
    # bias (reversal up); a bearish ChoCh means it broke the recent swing LOW
    # against a prior bullish bias (reversal down).
    if ms["choch"]:
        if ms_bias == "bearish" and closes[-1] > ms["swing_high"] and alt_bull_ok:
            p.append(("Change of Character (ChoCh)", TIER1_BASE, "BUY"))
        elif ms_bias == "bullish" and closes[-1] < ms["swing_low"] and alt_bear_ok:
            p.append(("Change of Character (ChoCh)", TIER1_BASE, "SELL"))

    # ── Liquidity Sweep — Tier 1, "exactly when smart money steps in" ──
    # Institutions engineer a false break beyond a known level to trigger
    # retail stop losses, then reverse sharply. Detected as: a long wick
    # piercing the structural level that closes back inside it, combined
    # with a genuine ChoCh (see detect_liquidity_sweep's docstring for the
    # zone-vs-structure scope note). Scored slightly above TIER1_BASE since
    # this is a narrower, higher-conviction condition than ChoCh alone —
    # it requires the specific sweep-and-reject candle shape on top of it.
    sweep_dir, sweep_strength = detect_liquidity_sweep(klines, highs, lows, closes, opens, sup, res, ms)
    if sweep_dir == "BUY" and alt_bull_ok:
        p.append(("Liquidity Sweep", min(TIER1_BASE + 1.0, 99), "BUY"))
    elif sweep_dir == "SELL" and alt_bear_ok:
        p.append(("Liquidity Sweep", min(TIER1_BASE + 1.0, 99), "SELL"))

    return p

def is_in_zone(price,direction,zones):
    key="demand" if direction=="BUY" else "supply"
    for zone in zones.get(key,[])[-5:]:
        if zone["low"]*0.995<=price<=zone["high"]*1.005:
            return True,f"{format_price(zone['low'])}-{format_price(zone['high'])}"
    return False,""

def get_htf_zones(symbol):
    """
    Point 2 (HTF Zones): A professional top-down approach establishes true
    market bias and locates major institutional zones on the 4-Hour chart
    FIRST, using the 1-Hour as a secondary/backup source — the 15-minute
    chart is only used afterward to time the specific entry when price
    taps one of these larger levels.

    Previously detect_supply_demand_zones was called ONLY on 15m klines
    at every call site — those are structurally weak, low-conviction
    zones that get run straight through by any real trend, which is
    exactly the problem reported.

    Returns a merged {"demand":[...], "supply":[...]} dict. 4h zones are
    listed first (checked first by is_in_zone's [-5:] window, and treated
    as the "major" levels), with 1h zones appended as secondary/backup
    coverage when 4h data is thin.

    CACHED (15min TTL, per Point 3 rate-limit fix): this function used to
    make 2 fresh HTTP requests (4h + 1h klines) EVERY call, with no reuse.
    If 10 coins passed the filter in the same scan cycle, that's 20
    simultaneous requests to Binance — real IP-ban risk. 4h zone data
    genuinely doesn't change meaningfully within 15 minutes, so repeat
    calls for the same symbol within that window now return the cached
    result with zero HTTP requests. Chose caching over a time.sleep(0.5)
    throttle because sleeping still makes the same 2N requests total (just
    slower), while caching actually reduces request volume — and a sleep
    would add synchronous delay directly into the signal-scoring path at
    both call sites, which matters since that path gates whether a signal
    reaches the user at all.
    """
    now = get_ist_datetime()
    cached = htf_zones_cache.get(symbol)
    if cached and (now - cached["cached_at"]).total_seconds() < 900:  # 15 min
        return cached["zones"]

    zones_4h = {"demand": [], "supply": []}
    zones_1h = {"demand": [], "supply": []}
    try:
        klines_4h = get_klines(symbol, "4h", 100)
        if klines_4h and len(klines_4h) >= 30:
            zones_4h = detect_supply_demand_zones(klines_4h)
    except Exception as e:
        logger.warning(f"get_htf_zones 4h {symbol}: {e}")
    try:
        klines_1h = get_klines(symbol, "1h", 100)
        if klines_1h and len(klines_1h) >= 30:
            zones_1h = detect_supply_demand_zones(klines_1h)
    except Exception as e:
        logger.warning(f"get_htf_zones 1h {symbol}: {e}")

    merged = {
        "demand": zones_4h["demand"] + zones_1h["demand"],
        "supply": zones_4h["supply"] + zones_1h["supply"],
    }
    htf_zones_cache[symbol] = {"zones": merged, "cached_at": now}
    return merged

def get_structural_tp(entry, direction, zones, min_tp_dist):
    """
    Point 2: Structural Take Profit — targets the nearest mapped
    institutional Supply/Demand zone in the trade's favor, instead of a
    generic ATR-derived distance. A human trader takes profit exactly at
    the next major resistance/support wall, not at an arbitrary
    mathematical multiple.

    Design decision (not explicitly specified by either instruction, so
    stating it plainly): this does NOT override Point 1's 1:2 minimum
    Risk/Reward guarantee. If the nearest structural zone sits CLOSER
    than min_tp_dist (the SL-derived 1:2 floor), using it as TP would
    silently produce a worse ratio than Point 1 guarantees — so that zone
    is skipped, and the search continues outward for the next zone that
    clears the floor. If NO zone anywhere clears the floor, this returns
    None and the caller falls back to the existing ATR/min-RR logic
    unchanged — Point 1's guarantee is never given up in exchange for
    "aim at a real level."

    For a BUY: target the nearest SUPPLY zone above entry (that's where
    sellers are expected to defend — natural resistance for a long).
    For a SELL: target the nearest DEMAND zone below entry (buyers'
    defense level — natural support for a short).

    Returns the target price (float) or None if no qualifying zone exists.
    """
    key = "supply" if direction == "BUY" else "demand"
    candidates = zones.get(key, [])
    if not candidates:
        return None

    qualifying = []
    for z in candidates:
        # Use the near edge of the zone (low for supply/BUY-target,
        # high for demand/SELL-target) — the price a trader would
        # realistically take profit at first touch, not requiring price
        # to punch all the way through the zone.
        if direction == "BUY":
            zone_price = z["low"]
            if zone_price <= entry: continue  # zone must be above entry for a long TP
            dist = zone_price - entry
        else:
            zone_price = z["high"]
            if zone_price >= entry: continue  # zone must be below entry for a short TP
            dist = entry - zone_price
        if dist >= min_tp_dist:
            qualifying.append((dist, zone_price))

    if not qualifying:
        return None
    # Nearest qualifying zone — the closest realistic target that still
    # respects the 1:2 floor, not the farthest/most optimistic one.
    qualifying.sort(key=lambda x: x[0])
    return qualifying[0][1]

def detect_market_condition(btc_price,btc_klines):
    try:
        closes=[float(k[4]) for k in btc_klines]
        e20=calculate_ema(closes,20); e50=calculate_ema(closes,50)
        h20=max(closes[-20:]); l20=min(closes[-20:])
        rng=((h20-l20)/l20)*100 if l20>0 else 0
        if e20 and e50:
            if e20>e50*1.02 and btc_price>e20:   return "bull"
            elif e20<e50*0.98 and btc_price<e20: return "bear"
        return "sideways" if rng<5.0 else ("bull" if btc_price>(e50 or btc_price) else "bear")
    except Exception: return "sideways"

def is_good_trading_session(coin=None):
    """
    Point 3: PREMIUM_COINS (BTC, ETH, BNB, SOL, PAXG, XAU, XAG) get VIP
    immunity from both Dead Hour (2-7AM IST) and scheduled macro-event
    pauses — these are high-liquidity institutional assets that genuinely
    trade and respect technicals around the clock, unlike thin altcoins
    that go quiet or erratic overnight. `coin` defaults to None so
    existing callers that only want the generic/non-premium session
    state (e.g. status displays) keep their old behavior unchanged.
    """
    if coin in PREMIUM_COINS:
        return True
    hour=datetime.now(IST).hour
    if DEAD_HOUR_START<=hour<DEAD_HOUR_END:
        logger.info(f"Dead session {hour}:xx IST"); return False
    # Point 4(b): scheduled macro events are a genuine deliberate pause window,
    # not indicator lag — kept as a hard block, same as opening a leveraged
    # position 10 minutes before FOMC would be a bad idea for a human too.
    is_macro, macro_note = is_macro_event_window()
    if is_macro:
        logger.info(f"Paused - {macro_note}"); return False
    return True

def get_smart_leverage(symbol, atr_pct, score, grade="Grade B"):
    """
    Leverage tiers based on BOTH coin tier AND signal grade:
    ┌──────────┬──────────┬─────────┬──────────┐
    │          │ Grade A+ │ Grade A │ Grade B/C│
    ├──────────┼──────────┼─────────┼──────────┤
    │ Tier 1   │  15x     │  10x    │   7x     │ BTC, ETH
    │ Tier 2   │  12x     │   8x    │   5x     │ BNB, SOL, XRP...
    │ Tier 3   │   5x     │   4x    │   3x     │ Meme coins
    │ Default  │  10x     │   7x    │   5x     │ Other altcoins
    └──────────┴──────────┴─────────┴──────────┘
    ATR safety cap: high volatility always reduces leverage.
    """
    g = grade[0] if isinstance(grade, tuple) else str(grade)
    is_aplus = "A+" in g
    is_a     = "A 🍀" in g or (not is_aplus and "A" in g)

    base = symbol.replace("USDT","")
    if base in LEV_TIER_3:
        lev = 5 if is_aplus else 4 if is_a else 3
    elif base in LEV_TIER_1:
        lev = 15 if is_aplus else 10 if is_a else 7
    elif base in LEV_TIER_2:
        lev = 12 if is_aplus else 8 if is_a else 5
    else:
        # Default altcoin tier
        lev = 10 if is_aplus else 7 if is_a else 5

    # ATR safety cap — reduce leverage for high-volatility setups
    if atr_pct >= 6.0:   lev = min(lev, 3)
    elif atr_pct >= 4.0: lev = min(lev, 5)
    elif atr_pct >= 2.5: lev = min(lev, 8)

    return max(lev, 1)

def get_signal_grade(score,vol_ratio,oi_rising,tf_score,vol_ok,rsi_ok,funding_ok,st_ok,vwap_ok,zone_ok,adx_val,btc_aligned=False,ms_bias=None,bos=False):
    """
    Unified grading fix: the letter grade is now decided PURELY by the
    confirmation scorecard, completely disconnected from the 100-point
    base `score`. Previously the grade was authoritative on `score` alone,
    which caused the exact bug reported: a trade could earn a perfect
    scorecard (every confirmation hit) and still be labeled "Grade C" if
    its 100-point base happened to be low. That's backwards — "if a trade
    hits the right confirmations, it earns the A," regardless of what
    pattern/base score it started from.

    Thresholds (as specified): 18+ pts = Grade A+, 14+ pts = Grade A.
    The B/C split (8 pts) was NOT specified in the instruction — I chose
    8 as a reasonable third-of-max boundary, flagging this as my own
    judgment call.

    MAX POINTS: 21 (score 3 + volume 2 + tf 2 + vol_ok 1 + rsi 1 +
    funding 1 + supertrend 2 + vwap 1 + zone 2 + adx 1 + btc_aligned 2 +
    structure 1 + bos 1 + golden_hour 1).

    WHALE/OI REMOVAL (earlier round): `whale` replaced with `vol_ratio`
    tiered scoring; `oi_rising` kept as a parameter but no longer scored.

    ORDER BOOK REMOVAL (earlier round): `ob_imbalance` deleted entirely —
    data was thin/frequently "N/A". Replaced with `btc_aligned` (+2 pts).

    GOLDEN HOURS (this round): +1 pt if the signal fires during the first
    ~2 hours of London or New York open (is_golden_hour()). Chosen +1 (not
    +2) from the instruction's stated 1-or-2 range, since "which hour is
    it" is a simpler, single-factor signal compared to the other 2pt
    lines (SuperTrend, S/D Zone, BTC Aligned, full TF alignment), which
    are all multi-factor market-structure confirmations — didn't want
    session timing alone to weigh as heavily as those. This shifts max
    points from 20 to 21 and the 14/18 thresholds fractionally again
    (70%→67% for A, 90%→86% for A+ — coincidentally landing back near
    the pre-BTC-alignment-round proportions). Not recalibrated, same
    reasoning as the prior rounds' threshold-shift notes.
    """
    breakdown=[]
    pts=0
    if score>=98:    pts+=3; breakdown.append(("🎯 Score ≥98",      3))
    elif score>=96:  pts+=2; breakdown.append(("🎯 Score ≥96",      2))
    elif score>=92:  pts+=2; breakdown.append(("🎯 Score ≥92",      2))
    elif score>=85:  pts+=1; breakdown.append(("🎯 Score ≥85",      1))
    else:                    breakdown.append(("🎯 Score",           0))
    if vol_ratio>=1.5:   pts+=2; breakdown.append((f"📊 Volume {vol_ratio:.1f}x (strong)",   2))
    elif vol_ratio>=1.2: pts+=1; breakdown.append((f"📊 Volume {vol_ratio:.1f}x (moderate)",  1))
    else:                        breakdown.append((f"📊 Volume {vol_ratio:.1f}x",              0))
    if tf_score==3:  pts+=2; breakdown.append(("📡 4h+1h Aligned",  2))
    elif tf_score==2:pts+=1; breakdown.append(("📡 4h Aligned",     1))
    else:                    breakdown.append(("📡 TF Alignment",    0))
    if vol_ok:       pts+=1; breakdown.append(("📊 Volume Confirm",  1))
    else:                    breakdown.append(("📊 Volume",          0))
    if rsi_ok:       pts+=1; breakdown.append(("📈 RSI Valid",       1))
    else:                    breakdown.append(("📈 RSI",             0))
    if funding_ok:   pts+=1; breakdown.append(("💸 Funding OK",      1))
    else:                    breakdown.append(("💸 Funding",         0))
    if st_ok:        pts+=2; breakdown.append(("🌀 SuperTrend ✓✓",  2))
    else:                    breakdown.append(("🌀 SuperTrend",      0))
    if vwap_ok:      pts+=1; breakdown.append(("💧 VWAP Confirm",    1))
    else:                    breakdown.append(("💧 VWAP",            0))
    if zone_ok:      pts+=2; breakdown.append(("📍 S/D Zone Hit",    2))
    else:                    breakdown.append(("📍 S/D Zone",        0))
    if adx_val>=35:  pts+=1; breakdown.append(("💪 ADX Strong",      1))
    else:                    breakdown.append(("💪 ADX",             0))
    if btc_aligned:  pts+=2; breakdown.append(("👑 BTC Aligned",     2))
    else:            breakdown.append(("👑 BTC Aligned",     0))
    if is_golden_hour(): pts+=1; breakdown.append(("⏰ Golden Hour",  1))
    else:                        breakdown.append(("⏰ Golden Hour",  0))
    if ms_bias in ("bullish","bearish"):
        pts+=1; breakdown.append(("🏗️ Market Structure", 1))
    else:            breakdown.append(("🏗️ Structure",        0))
    if bos:          pts+=1; breakdown.append(("🔥 BOS Confirm",     1))
    else:            breakdown.append(("🔥 BOS",              0))

    # Grade label — PURELY scorecard-based now, not the 100-point score.
    if pts >= 18:   grade = "Grade A+ 🍀"
    elif pts >= 14: grade = "Grade A 🍀"
    elif pts >= 8:  grade = "Grade B"
    else:           grade = "Grade C"
    return grade, pts, breakdown

def get_position_size_pct(grade):
    g=grade[0] if isinstance(grade,tuple) else grade
    if "A+" in g: return 10.0
    elif "A 🍀" in g: return 7.0
    elif "B" in g: return 5.0
    else:          return 3.0

def is_volume_confirmed(klines):
    vols=[float(k[5]) for k in klines]
    # Only reject truly dead volume (below 85% of average) — not require above-average
    return len(vols)>=20 and vols[-1]>sum(vols[-20:])/20*0.85

def is_rsi_valid(closes,direction):
    rsi=calculate_rsi(closes)
    return not (direction=="BUY" and rsi>72) and not (direction=="SELL" and rsi<28)

def is_volatility_normal(klines):
    an=calculate_atr(klines,14); as_=calculate_atr(klines,50)
    return as_==0 or (an/as_)<=ATR_VOLATILITY_RATIO

def is_pattern_blacklisted(name):
    s=pattern_stats.get(name)
    if not s or s["signals"]<10: return False
    return (s["wins"]/s["signals"])*100<40

def is_pattern_suspended(name):
    d=consecutive_loss_patterns.get(name,{})
    if d.get("consecutive_losses",0)>=CONSEC_LOSS_SUSPEND:
        su=d.get("suspended_until")
        if su:
            try:
                if datetime.now(IST)<datetime.fromisoformat(su): return True
                consecutive_loss_patterns[name]["consecutive_losses"]=0
                consecutive_loss_patterns[name]["suspended_until"]=None
            except Exception: pass
    return False

def too_many_correlated_active():
    return sum(1 for c in active_trades if c in BTC_CORRELATED)>=2

def too_many_sector_active(coin):
    """
    Point 1: Law of Portfolio Heat — sector position limit.
    too_many_correlated_active() already guards general BTC-correlation
    exposure, but a coin can share almost no BTC correlation while still
    being highly correlated to OTHER open trades within its own sector
    (e.g. MANA + ENJ are both "gaming" — a sudden gaming-sector-specific
    hit lands on both positions at once, even if BTC itself is flat).
    Hard cap: max 1 open trade per sector at any time. Coins with no
    sector mapping (not in COIN_SECTOR — e.g. BTC, PAXG) are never
    restricted by this check, since there's nothing to compare against.
    """
    sector = COIN_SECTOR.get(coin)
    if not sector:
        return False  # no sector data for this coin — nothing to restrict against
    return sum(1 for c in active_trades if COIN_SECTOR.get(c) == sector) >= 1

def get_funding_rate(symbol):
    """
    Bypass added for PAXG/XAU/XAG: these trade as Binance "TradFi Perpetual
    Contracts" under a separate entity (Nest Exchange Limited, ADGM/FSRA
    regulated) from standard crypto futures, and may not be recognized by
    the standard fapi.binance.com funding-rate endpoint. NOTE: the existing
    try/except below already prevents a hard crash on an error response
    (verified: an error-shaped JSON body raises inside the try block and
    is caught, returning None) — this bypass's real value is skipping a
    predictably-failing HTTP call entirely, reducing wasted requests and
    the rate-limit pressure flagged separately.

    BUG FIX: FUTURES_ONLY_SYMBOLS was emptied in an earlier round (to fix
    PAXG's price/klines routing, which now correctly goes through Spot).
    That silently broke the `symbol in FUTURES_ONLY_SYMBOLS` guard THIS
    function relies on for the same reason — an empty set means the guard
    can never trigger, so this function kept calling the 451-prone
    Futures funding-rate endpoint for PAXG even after price/klines were
    fixed. Reproduced and confirmed: PAXGUSDT genuinely still hit
    fapi.binance.com here before this fix. Added an explicit "PAXG" in
    symbol check so this guard no longer depends on FUTURES_ONLY_SYMBOLS'
    current (empty) state. Kept the FUTURES_ONLY_SYMBOLS check alongside
    it too — harmless no-op right now, but keeps this guard consistent
    and future-proof if that set is ever repopulated for a different
    genuinely-Futures-only symbol later.
    """
    if "PAXG" in symbol or symbol in FUTURES_ONLY_SYMBOLS: return None
    try:
        res=requests.get(BINANCE_FUNDING_URL,params={"symbol":symbol,"limit":1},timeout=10)
        return float(res.json()[0]["fundingRate"]) if res.status_code==200 and res.json() else None
    except Exception as e:
        logger.warning(f"funding {symbol}: {e}"); return None

def is_funding_favorable(symbol,direction):
    rate=get_funding_rate(symbol)
    if rate is None: return True
    if direction=="BUY"  and rate>0.002:  return False
    if direction=="SELL" and rate<-0.002: return False
    return True

def get_oi_trend(symbol):
    """
    Bypass for PAXG/XAU/XAG — see get_funding_rate's docstring for the
    reasoning, including the FUTURES_ONLY_SYMBOLS-emptying bug this
    function shared with it, now fixed the same way.
    """
    if "PAXG" in symbol or symbol in FUTURES_ONLY_SYMBOLS: return None
    try:
        res=requests.get(BINANCE_OI_URL,params={"symbol":symbol,"period":"15m","limit":5},timeout=10)
        if res.status_code==200 and len(res.json())>=2:
            d=res.json()
            return float(d[-1]["sumOpenInterest"])>float(d[-2]["sumOpenInterest"])
        return None
    except Exception as e:
        logger.warning(f"OI {symbol}: {e}"); return None

def get_oi_change_pct(symbol):
    """
    Point 3: Squeeze detection needs OI MAGNITUDE ("is it skyrocketing"),
    not just direction. get_oi_trend() only returns True/False (up or
    down between the last two 15m readings) — deliberately NOT changed
    here, since it's still passed as an unused parameter into
    get_signal_grade elsewhere and changing its return type would be an
    unrequested contract change for a function other code already calls.
    This is a separate, purpose-built function instead: returns the
    actual percent change in Open Interest between the last two 15m
    readings (e.g. +8.3 = OI grew 8.3%), or None if data unavailable.
    Same endpoint/bypass logic as get_oi_trend, just returns the real
    number instead of collapsing it to a boolean.

    BUG FIX: shared the same FUTURES_ONLY_SYMBOLS-emptying issue as
    get_funding_rate/get_oi_trend — see that docstring. Fixed the same
    way. Kept the FUTURES_ONLY_SYMBOLS check alongside the new "PAXG" in
    symbol check for consistency with the other two functions, rather
    than dropping it entirely.
    """
    if "PAXG" in symbol or symbol in FUTURES_ONLY_SYMBOLS: return None
    try:
        res=requests.get(BINANCE_OI_URL,params={"symbol":symbol,"period":"15m","limit":5},timeout=10)
        if res.status_code==200 and len(res.json())>=2:
            d=res.json()
            prev=float(d[-2]["sumOpenInterest"]); curr=float(d[-1]["sumOpenInterest"])
            if prev<=0: return None
            return (curr-prev)/prev*100
        return None
    except Exception as e:
        logger.warning(f"OI change {symbol}: {e}"); return None

def has_whale_activity(symbol):
    """
    UNUSED as of the whale/OI removal — no live call sites remain (was
    only ever called from get_signal_grade's two call sites, both now
    pass vol_ratio instead). Left defined rather than deleted, in case
    it's wanted back later; not currently doing anything.
    """
    try:
        res=requests.get(BINANCE_AGG_URL,params={"symbol":symbol,"limit":20},timeout=10)
        if res.status_code==200:
            for t in res.json():
                if float(t["p"])*float(t["q"])>WHALE_TRADE_THRESHOLD: return True
        return False
    except Exception as e:
        logger.warning(f"whale {symbol}: {e}"); return False

def get_fear_greed_index():
    try:
        res=requests.get("https://api.alternative.me/fng/?limit=1",timeout=10)
        return int(res.json()["data"][0]["value"]) if res.status_code==200 else 50
    except Exception as e:
        logger.warning(f"F&G: {e}"); return 50

def is_sentiment_valid(direction,fng):
    return not (direction=="BUY" and fng<20) and not (direction=="SELL" and fng>80)

def get_htf_trend(symbol,interval="1h"):
    try:
        klines=get_klines(symbol,interval,50)
        if not klines or len(klines)<50: return 0
        closes=[float(k[4]) for k in klines]
        e20=calculate_ema(closes,20); e50=calculate_ema(closes,50)
        if e20 and e50: return 1 if e20>e50 else -1
        return 0
    except Exception as e:
        logger.warning(f"HTF {symbol} {interval}: {e}"); return 0

def is_btc_aligned(direction):
    """
    Shared BTC 1h alignment check — replaces the deleted Order Book check
    (👑 BTC Aligned scoring). Consolidated here: this same 2-line pattern
    was previously written independently 3 times (cmd_hidden_gems,
    format_and_send, scan_coins) with _gem/_chk suffixes to avoid name
    collisions. Now called once from each site instead.
    """
    btc_1h_trend = get_htf_trend("BTCUSDT","1h")
    aligned = (btc_1h_trend==1 and direction=="BUY") or (btc_1h_trend==-1 and direction=="SELL")
    return aligned, btc_1h_trend

def get_volume_ratio(klines):
    """
    Shared volume-vs-20-candle-average ratio. Consolidated here: this same
    3-line `avg_vol = sum(vols[-20:])/20; ratio = vols[-1]/avg_vol` pattern
    was previously written independently 11 times across the file (AI-call
    prep, grading, compute_confirmation_bonus, message display, hidden
    gems, etc.) — same computation, never factored out. Now called once
    from each site instead.
    """
    if not klines: return 1.0
    vols = [float(k[5]) for k in klines]
    avg_vol = sum(vols[-20:])/20 if len(vols)>=20 else (vols[-1] if vols else 1)
    return vols[-1]/avg_vol if avg_vol>0 else 1.0

def get_timeframe_score(symbol,direction):
    """
    Point 4 (Daily Macro Filter): a Daily-trend disagreement is now a HARD
    BLOCK, same treatment as the existing 4h check below — not a score
    penalty. The instruction is explicit ("permanently block... trades
    that fight against the heavy daily macro direction"), which is a
    stronger requirement than the soft/scoring treatment used for some
    other signals in earlier rounds (e.g. sector correlation, SuperTrend
    partial lag) — those were deliberately kept as penalties because they
    can reasonably lag a genuine move. The Daily chart disagreeing is
    treated the same way the 4h disagreement already was: an absolute
    veto, checked FIRST (before 4h/1h), since Daily is the highest
    timeframe and should have final say — a human always checks the 1-Day
    chart first, per the instruction's own framing.
    """
    di=1 if direction=="BUY" else -1
    d1=get_htf_trend(symbol,"1d")
    if d1!=0 and d1!=di: return -1
    h4=get_htf_trend(symbol,"4h"); h1=get_htf_trend(symbol,"1h")
    if h4!=0 and h4!=di: return -1
    score=0
    if h4==di: score+=2
    if h1==di: score+=1
    return score

def get_structure_sl(klines,direction,entry,atr):
    """
    Structural Stop Loss (tighter Risk/Reward), rewritten per instruction.

    PREVIOUS BEHAVIOR (the actual bug): despite being named get_structure_sl,
    this took the WORSE (wider) of the structural level and the ATR-based
    level via min()/max() — so ATR still won whenever it produced a wider
    stop, which defeats the entire point of a structural stop. It also used
    a raw min/max of the last 20 candles as "structure," not the real
    swing pivot from detect_market_structure (5-bar-window pivot detection,
    already used elsewhere in the codebase for zones/BOS/ChoCh).

    NOW: the stop is placed exactly one tick beyond the most recent real
    swing low (BUY) or swing high (SELL) from detect_market_structure —
    genuinely tight, not a min/max blend with ATR. ATR is used ONLY as a
    fallback when structure data is unavailable (e.g. insufficient candles
    for swing detection), not as a competing wider distance that can
    override a valid structural level.

    "One tick" — since this codebase doesn't track each symbol's exact
    exchange tick size, 0.05% of entry price is used as a close, safe
    approximation (small enough to stay genuinely tight, large enough to
    not sit exactly on the swing level where noise could tag it instantly).
    """
    ONE_TICK_PCT = 0.0005  # 0.05% of entry, approximating "one tick"
    min_dist = entry * MIN_SL_PCT  # existing minimum stop distance floor

    ms = detect_market_structure(klines)
    has_valid_swing = ms["swing_low"] > 0 and ms["swing_high"] > 0

    if has_valid_swing:
        if direction == "BUY":
            sl = ms["swing_low"] * (1 - ONE_TICK_PCT)
        else:
            sl = ms["swing_high"] * (1 + ONE_TICK_PCT)
    else:
        # Fallback only — structure data unavailable (e.g. too few candles)
        logger.info("get_structure_sl: no valid swing data, falling back to ATR")
        if direction == "BUY":
            sl = entry - atr * ATR_SL_MULTIPLIER
        else:
            sl = entry + atr * ATR_SL_MULTIPLIER

    # Still enforce the existing minimum distance floor — a structural
    # stop sitting unrealistically close to entry (e.g. noisy micro-swing)
    # is still bumped out to at least MIN_SL_PCT away.
    if direction == "BUY":
        return min(sl, entry - min_dist)
    return max(sl, entry + min_dist)

def check_circuit_breaker():
    global daily_losses,circuit_breaker_until,last_reset_day
    today=datetime.now(IST).date()
    if today!=last_reset_day:
        daily_losses=0; circuit_breaker_until=None; last_reset_day=today
        save_circuit_breaker(); return False
    if circuit_breaker_until:
        try:
            until_dt=datetime.fromisoformat(circuit_breaker_until)
            if datetime.now(IST)>=until_dt:
                daily_losses=0; circuit_breaker_until=None
                save_circuit_breaker()
                send_telegram(f"✅ <b>{BOT_HEADER}</b>\nCircuit Breaker RESET - scanning resumed!")
                return False
            return True
        except Exception:
            circuit_breaker_until=None; return False
    return daily_losses>=MAX_DAILY_LOSSES

def increment_daily_losses(pnl):
    global daily_losses,circuit_breaker_until
    if pnl>CIRCUIT_BREAKER_MIN_LOSS:
        logger.info(f"Small loss {pnl:.2f}% - not counted"); return
    daily_losses+=1
    if daily_losses>=MAX_DAILY_LOSSES:
        midnight=(datetime.now(IST)+timedelta(days=1)).replace(hour=0,minute=0,second=0,microsecond=0)
        circuit_breaker_until=midnight.isoformat()
        save_circuit_breaker()
        send_telegram(f"🚨 <b>{BOT_HEADER}</b>\nCIRCUIT BREAKER ACTIVE\n3 big losses today.\nResumes at midnight IST.")

def is_btc_crashing():
    try:
        klines=get_klines("BTCUSDT","1h",5)
        if not klines or len(klines)<4: return False
        now=float(klines[-1][4]); h4=float(klines[-4][4])
        drop=((now-h4)/h4)*100
        if drop<-5.0: logger.info(f"BTC crashed {drop:.1f}% in 4h"); return True
        return False
    except Exception: return False

def get_adjusted_score(pattern_name,base_score,market_condition):
    """
    FIX: previously this blended base_score with historical win rate (mc_wr)
    using a factor up to 0.6 at 20+ signals — meaning a pattern with a 45%
    historical win rate could drag an 85.0 normalized base down to ~61,
    making it mathematically impossible to ever reach GRADE_A_THRESHOLD
    (92.2) again, no matter how strong today's confirmation bonuses are.
    That defeated the entire point of the normalized baseline (Point 5):
    the score is supposed to reflect THIS setup's confirmation quality,
    not get silently overridden by yesterday's win-rate history before
    confirmations are even applied.

    Now: base_score passes through untouched, except for the existing
    lightweight `weight` multiplier (bounded 0.5x-1.5x, moves by only
    0.1-0.15 per trade, only triggers at >=70% or <40% win rate — see
    learn_from_trade()). That's a much gentler, bounded adjustment than
    the removed blend, and genuinely bad patterns are still caught
    separately by is_pattern_blacklisted() (win rate <40% over 10+ signals).
    """
    stats=pattern_stats.get(pattern_name,{})
    weight=stats.get("weight",1.0)
    adjusted=base_score*weight
    return min(round(adjusted,1),99.0)

def check_sector_correlation(coin, direction):
    """
    Point 3: Trade like a human — check the "neighborhood" before confirming.
    If the bot wants to BUY a gaming coin but the rest of the gaming sector
    is red, that's a likely fake-out/trap rather than a genuine sector move.
    Checks up to 4 sector peers' 15m price change; requires the majority to
    agree with the trade direction. Coins with no defined sector, or fewer
    than 2 peers with data, skip this check (returns True — doesn't block).
    Returns (passes: bool, note: str) — this feeds the AI prompt as context
    and can also be used as a soft scoring signal, not a hard block on its own,
    since a genuine sector-leading move can happen before peers catch up.
    """
    sector = COIN_SECTOR.get(coin)
    if not sector:
        return True, "no sector defined"
    peers = [c for c in SECTOR_GROUPS[sector] if c != coin][:4]
    if len(peers) < 2:
        return True, "insufficient sector peers"

    agree = 0
    checked = 0
    for peer in peers:
        try:
            k = get_klines(peer+"USDT", "15m", 5)
            if not k or len(k) < 3: continue
            closes_p = [float(x[4]) for x in k]
            change_pct = (closes_p[-1] - closes_p[-3]) / closes_p[-3] * 100 if closes_p[-3] > 0 else 0
            checked += 1
            if direction == "BUY" and change_pct > -0.3: agree += 1
            elif direction == "SELL" and change_pct < 0.3: agree += 1
        except Exception:
            continue

    if checked < 2:
        return True, "insufficient sector data"

    agree_ratio = agree / checked
    passes = agree_ratio >= 0.5
    note = f"sector {sector}: {agree}/{checked} peers agree"
    return passes, note


def compute_confirmation_bonus(symbol, direction, klines, vols, tf_score, btc_aligned=False, zone_ok=False, ms_bos=False, ms_bias=None, ms_choch=False, is_tier1=True, is_compression=False):
    """
    The Location Multiplier + hard Tier 1/Tier 2 AI cap.

    Bonus weights:
      +7.5  ChoCh occurred INSIDE a Supply/Demand zone — "the ultimate
            human prediction tool": lower lows into a demand zone then a
            sudden higher high (or the bearish mirror). This is the single
            largest bonus in the system, deliberately above the standalone
            Location bonus, since ChoCh-in-zone is Location + Shift at once.
      +6.0  Location: price is inside a valid Supply/Demand zone in the
            trade's favor (Point 1's "Location Multiplier" — mathematically
            forces the bot toward trading only where institutions trade)
      +3.5  Pre-Breakout Accumulation: the pattern is a verified compression
            (detect_pre_breakout_compression fired) sitting right at a key
            level. VERIFIED BEFORE ADDING (not just implemented on request):
            ran the actual live scoring code with a realistic compression
            scenario. The originally-reported cause (missing BOS points)
            did NOT reproduce — a realistic compression case with just
            zone+structure already totaled 96.7, clearing the 92.0 floor
            fine, since BOS was never required in the first place
            (structure-agrees-only already gives +1.2 as a fallback). The
            REAL gap found: `zone_ok` requires the price sit inside a
            FORMALLY MAPPED HTF Supply/Demand zone (get_htf_zones), which
            is stricter than detect_pre_breakout_compression's own check
            (just "within 1% of the local sup/res swing level" — a
            different, looser threshold). When a compression fires near a
            real level that ISN'T also a formally mapped HTF zone,
            zone_ok=False and the total lands at 90.7 — clears
            MIN_SETUP_SCORE(90) but fails the stricter 92.0 floor.
            This dedicated bonus fixes that real gap directly, regardless
            of zone_ok's state, since it's checking the same "resting at
            a real level with quiet volume" condition through a second,
            independent signal.
      +3.0  Squeeze: rising Open Interest (>=3% growth) combined with an
            extreme funding rate against the trade's crowd (extreme
            negative funding + bullish setup = shorts overloaded, primed
            for a short squeeze; extreme positive funding + bearish setup
            = mirror long-squeeze setup). Thresholds are evidence-based,
            not guessed — see SQUEEZE_FUNDING_EXTREME_NEG/POS and
            SQUEEZE_OI_RISING_PCT constants for the sourcing.
      +3.0  Shift: Break of Structure (BOS) confirms the trade direction
      +1.2  structure bias agrees with trade direction, no fresh BOS/ChoCh yet
      +3.0  HTF trend alignment (4h+1h both agree — tf_score==3)
      +1.5  partial HTF alignment (tf_score==2)
      +2.0  this coin's trade direction matches the 1-Hour BTC trend
            (👑 BTC Aligned — replaces the deleted order book check,
            whose data was thin/frequently unavailable and dragging
            grades down on missing data rather than genuine weakness)
      +2.0  strong volume (1.5x+ average)
      +1.0  moderate volume (1.2x-1.5x average)
      +1.5  strong ADX (>=30, real trend strength not chop — note: tested
            and confirmed ADX can genuinely read "strong" even during a
            quiet compression tail, since ADX is a smoothed/lagging
            measure over a longer window than just the last few tight
            candles — it reflects trend strength BEFORE the coil started,
            not a contradiction of compression itself)

    HARD TIER 2 CAP (is_tier1=False): Tier 2 patterns (Engulfing, RSI
    Reversal, EMA Trend, Pullback, Momentum Surge, Volume Spike) are
    STRUCTURALLY EXCLUDED from the ChoCh, Location, Compression, and
    BOS/structure bonuses below — not just scored lower, the code
    physically skips those branches (is_compression is only ever True
    for the Pre-Breakout Compression pattern anyway, which is Tier 1
    by definition, so this exclusion is mostly redundant with that, but
    stated explicitly for clarity). The Squeeze bonus IS available to
    Tier 2 (it's an independent market-condition signal, not a
    structural/location one). Their available bonuses are HTF + Squeeze +
    BTC alignment + volume + ADX = 11.5 max. On a 75.0 base that's a hard
    ceiling of 86.5 — this DOES cross the stated 85.0 Tier 2 target by
    1.5pts in the single worst case where every signal fires
    simultaneously, though it remains well under the 92.2 AI threshold.
    """
    bonus = 0.0
    notes = []

    if is_tier1:
        # ── ChoCh-in-Zone: the single biggest bonus — Location + Shift at once ──
        choch_in_zone = ms_choch and zone_ok
        if choch_in_zone:
            bonus += 7.5; notes.append("ChoCh inside zone - ultimate signal (+7.5)")
        else:
            # ── LOCATION: Supply/Demand Zone — Point 1's Location Multiplier ──
            if zone_ok:
                bonus += 6.0; notes.append("in S/D zone - Location Multiplier (+6.0)")

            # ── SHIFT: Market Structure / BOS, or Pre-Breakout Accumulation ──
            structure_agrees = ms_bias == ("bullish" if direction == "BUY" else "bearish")
            if is_compression:
                bonus += 3.5; notes.append("Pre-breakout coiling consolidation (+3.5)")
            elif ms_bos and structure_agrees:
                bonus += 3.0; notes.append("BOS confirms direction - Shift (+3.0)")
            elif structure_agrees:
                bonus += 1.2; notes.append("structure bias agrees (+1.2)")
    else:
        notes.append("Tier 2: zone/BOS/ChoCh bonuses excluded by design (auto-execute only)")

    # ── SQUEEZE: OI + Funding divergence hunting forced liquidations ──
    oi_change_pct = get_oi_change_pct(symbol)
    funding_rate = get_funding_rate(symbol)
    if oi_change_pct is not None and funding_rate is not None and oi_change_pct >= SQUEEZE_OI_RISING_PCT:
        if direction == "BUY" and funding_rate <= SQUEEZE_FUNDING_EXTREME_NEG:
            bonus += 3.0; notes.append(f"Squeeze: OI +{oi_change_pct:.1f}% + funding {funding_rate*100:.3f}% (short squeeze setup) (+3.0)")
        elif direction == "SELL" and funding_rate >= SQUEEZE_FUNDING_EXTREME_POS:
            bonus += 3.0; notes.append(f"Squeeze: OI +{oi_change_pct:.1f}% + funding {funding_rate*100:.3f}% (long squeeze setup) (+3.0)")

    if tf_score == 3:
        bonus += 3.0; notes.append("HTF fully aligned (+3.0)")
    elif tf_score == 2:
        bonus += 1.5; notes.append("HTF partially aligned (+1.5)")

    if btc_aligned:
        bonus += 2.0; notes.append("BTC 1h trend aligned (+2.0)")

    avg_vol = sum(vols[-20:]) / 20 if len(vols) >= 20 else (vols[-1] if vols else 1)
    vol_ratio = vols[-1] / avg_vol if avg_vol > 0 else 1.0
    if vol_ratio >= 1.5:
        bonus += 2.0; notes.append("volume strong (+2.0)")
    elif vol_ratio >= 1.2:
        bonus += 1.0; notes.append("volume moderate (+1.0)")

    adx_val = calculate_adx(klines)
    if adx_val >= 30:
        bonus += 1.5; notes.append("ADX strong (+1.5)")

    return round(bonus, 1), notes


def get_all_pattern_scores(patterns,market_condition):
    scored=[]
    for name,base_score,direction in patterns:
        adj=get_adjusted_score(name,base_score,market_condition)
        scored.append((name,adj,direction,base_score))
    scored.sort(key=lambda x:x[1],reverse=True)
    return scored

def learn_from_trade(coin,pattern,result,pnl,mc,tf_score):
    global learning_notes,market_memory,consecutive_loss_patterns
    if result=="WIN": market_memory[mc]["wins"]+=1
    else:             market_memory[mc]["losses"]+=1
    wins_by_pat={}
    for e in trade_journal:
        if e.get("market_condition")==mc and e.get("result")=="WIN":
            p=e.get("pattern","?"); wins_by_pat[p]=wins_by_pat.get(p,0)+1
    if wins_by_pat:
        market_memory[mc]["best_pattern"]=max(wins_by_pat,key=wins_by_pat.get)
    if pattern not in consecutive_loss_patterns:
        consecutive_loss_patterns[pattern]={"consecutive_losses":0,"suspended_until":None}
    if result=="LOSS":
        consecutive_loss_patterns[pattern]["consecutive_losses"]+=1
        cl=consecutive_loss_patterns[pattern]["consecutive_losses"]
        sigs=pattern_stats.get(pattern,{}).get("signals",0)
        if cl>=CONSEC_LOSS_SUSPEND and sigs>=MIN_SIGNALS_TO_SUSPEND:
            su=(datetime.now(IST)+timedelta(hours=SUSPEND_HOURS)).isoformat()
            consecutive_loss_patterns[pattern]["suspended_until"]=su
            send_telegram(f"🧠 <b>{BOT_HEADER}</b>\nPattern suspended: {pattern}\n{cl} consecutive losses.")
    else:
        consecutive_loss_patterns[pattern]["consecutive_losses"]=0
        consecutive_loss_patterns[pattern]["suspended_until"]=None
    if pattern in pattern_stats:
        s=pattern_stats[pattern]; sigs=s.get("signals",0)
        if sigs>=3:
            wr=(s["wins"]/sigs)*100
            if wr>=70:   s["weight"]=min(s["weight"]+0.1,1.5)
            elif wr<40:  s["weight"]=max(s["weight"]-0.15,0.5)
            mc_trades=[t for t in trade_journal if t.get("pattern")==pattern and t.get("market_condition")==mc]
            mc_wins=sum(1 for t in mc_trades if t["result"]=="WIN")
            mc_wr=(mc_wins/len(mc_trades)*100) if mc_trades else 50.0
            s[f"{mc}_wr"]=round(mc_wr,1)
    stats=pattern_stats.get(pattern,{}); sigs2=stats.get("signals",0); note=None
    if sigs2>=5:
        wr=(stats["wins"]/sigs2)*100
        if result=="LOSS" and wr<45:
            note=f"Pattern '{pattern}' only {wr:.1f}% WR - consider avoiding in {mc} market."
        elif result=="WIN" and wr>70:
            note=f"Pattern '{pattern}' strong - {wr:.1f}% WR in {mc} market."
    if note and note not in learning_notes:
        learning_notes.append(note)
        if len(learning_notes)>100: learning_notes=learning_notes[-100:]
    save_learning()
    cloud_save_learning()

def get_crypto_news():
    """Fetch news from CryptoPanic (primary) + CryptoCompare (fallback) with beautiful output."""
    headlines = []
    # ── Primary: CryptoPanic ──
    if NEWS_API_KEY:
        try:
            res = requests.get(
                "https://cryptopanic.com/api/v1/posts/",
                params={"auth_token": NEWS_API_KEY, "kind": "news",
                        "filter": "hot", "public": "true"},
                timeout=10
            )
            if res.status_code == 200:
                for item in res.json().get("results", [])[:8]:
                    title  = item.get("title", "")[:90]
                    source = item.get("domain", "CryptoPanic")
                    votes  = item.get("votes", {})
                    pos = votes.get("positive", 0); neg = votes.get("negative", 0)
                    sent = "🟢" if pos > neg else "🔴" if neg > pos else "⚪"
                    currencies = [c["code"] for c in item.get("currencies", [])[:3]]
                    tags = "  <i>" + " ".join(f"#{c}" for c in currencies) + "</i>" if currencies else ""
                    if title:
                        headlines.append(f"{sent} <b>{title}</b>\n     <i>— {source}</i>{tags}")
        except Exception as e:
            logger.warning(f"CryptoPanic: {e}")
    # ── Fallback: CryptoCompare ──
    if not headlines:
        try:
            res = requests.get(
                "https://min-api.cryptocompare.com/data/v2/news/?lang=EN&sortOrder=latest",
                timeout=10
            )
            if res.status_code == 200:
                for a in res.json().get("Data", [])[:6]:
                    title  = a.get("title", "")[:90]
                    source = a.get("source_info", {}).get("name", "Unknown")
                    if title:
                        headlines.append(f"⚪ <b>{title}</b>\n     <i>— {source}</i>")
        except Exception as e:
            logger.warning(f"CryptoCompare: {e}")
    fng = get_fear_greed_index()
    fng_lbl = ("Extreme Fear 😨" if fng<=25 else "Fear 😟" if fng<=45 else
               "Neutral 😐" if fng<=55 else "Greed 😊" if fng<=75 else "Extreme Greed 🤑")
    fng_bar = "█"*min(int(fng/10),10) + "░"*(10-min(int(fng/10),10))
    fng_em = "🔴" if fng<=25 else "🟠" if fng<=45 else "🟡" if fng<=55 else "🟢"
    prices = []
    for sym, lbl in [("BTCUSDT","₿  BTC"),("ETHUSDT","Ξ  ETH"),
                     ("SOLUSDT","◎  SOL"),("BNBUSDT","◈  BNB"),("XRPUSDT","✦  XRP")]:
        p = get_price(sym)
        if p: prices.append(f"  │  {lbl}  <code>${format_price(p)}</code>")
    news_src = "CryptoPanic 🔥" if (NEWS_API_KEY and headlines) else "CryptoCompare"
    msg  = (f"╔══════════════════════════════════╗\n"
            f"║   📰  CRYPTO NEWS & MARKET       ║\n"
            f"╚══════════════════════════════════╝\n\n")
    msg += f"  {fng_em} <b>Fear & Greed: {fng} — {fng_lbl}</b>\n"
    msg += f"  [{fng_bar}]\n\n"
    msg += f"  ┌── LIVE PRICES ──────────────┐\n"
    for p in prices: msg += p + "\n"
    msg += f"  └─────────────────────────────┘\n\n"
    msg += f"  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
    msg += f"  🗞️ <b>Latest News</b>  <i>(via {news_src})</i>\n\n"
    if headlines:
        msg += "\n\n".join(f"  {h}" for h in headlines[:6])
    else:
        msg += "  No news available right now."
    msg += f"\n\n  🕐 {get_ist_time()}"
    return msg

def run_backtest(symbol):
    """Audit Fix #3: Realistic backtest with fees (0.05% per side) and slippage (0.1%)."""
    FEE_PCT      = 0.05   # 0.05% per trade side (Binance futures taker)
    SLIPPAGE_PCT = 0.10   # 0.1% slippage on entry and exit
    LEVERAGE     = 5
    try:
        klines=get_klines(symbol,"15m",1000)
        if not klines or len(klines)<100: return f"Not enough data for {symbol}"
        results={"WIN":0,"LOSS":0,"SKIP":0}
        cond_res={"bull":{"W":0,"L":0},"bear":{"W":0,"L":0},"sideways":{"W":0,"L":0}}
        total_pnl=0.0; window=60
        for i in range(window,len(klines)-10):
            wk=klines[i-window:i]; price=float(klines[i][4])
            closes=[float(k[4]) for k in wk]; e20=calculate_ema(closes,20); e50=calculate_ema(closes,50)
            rng=((max(closes[-20:])-min(closes[-20:]))/min(closes[-20:]))*100 if min(closes[-20:])>0 else 0
            if e20 and e50:
                if e20>e50*1.02:   cond="bull"
                elif e20<e50*0.98: cond="bear"
                else:              cond="sideways" if rng<5 else ("bull" if price>e50 else "bear")
            else: cond="sideways"
            bt=1 if (e20 and e50 and e20>e50) else -1
            found=detect_patterns(symbol,wk,price,bt)
            if not found: continue
            best=max(found,key=lambda x:x[1])
            if best[1]<MIN_PRIMARY_SCORE: continue
            atr=calculate_atr(wk)
            if atr==0: continue
            direction=best[2]
            # Apply slippage to entry
            slip = price * SLIPPAGE_PCT / 100
            entry = price + slip if direction=="BUY" else price - slip
            sl=entry-atr*ATR_SL_MULTIPLIER if direction=="BUY" else entry+atr*ATR_SL_MULTIPLIER
            tp=entry+atr*ATR_TP_MULTIPLIER if direction=="BUY" else entry-atr*ATR_TP_MULTIPLIER
            hit="SKIP"
            for j in range(i+1,min(i+96,len(klines))):
                fh=float(klines[j][2]); fl=float(klines[j][3])
                if direction=="BUY":
                    if fh>=tp: hit="WIN";  break
                    if fl<=sl: hit="LOSS"; break
                else:
                    if fl<=tp: hit="WIN";  break
                    if fh>=sl: hit="LOSS"; break
            if hit=="SKIP": results["SKIP"]+=1; continue
            results[hit]+=1; cond_res[cond]["W" if hit=="WIN" else "L"]+=1
            # Gross PnL
            gross = (abs(tp-entry)/entry)*100*LEVERAGE if hit=="WIN" else -(abs(sl-entry)/entry)*100*LEVERAGE
            # Deduct fees (entry + exit) and exit slippage
            total_cost = (FEE_PCT * 2 + SLIPPAGE_PCT) * LEVERAGE
            pnl = gross - total_cost
            total_pnl+=pnl
        total=results["WIN"]+results["LOSS"]; wr=(results["WIN"]/total*100) if total>0 else 0
        r =(f"┌──────────────────────────────────┐\n"
            f"│  🔬  BACKTEST: {symbol:<18}│\n"
            f"└──────────────────────────────────┘\n\n"
            f"  ⚠️ Realistic: fees {FEE_PCT*2:.2f}% + slippage {SLIPPAGE_PCT:.2f}%\n\n"
            f"  📊 Total Trades : {total}\n"
            f"  ✅ Wins         : {results['WIN']}\n"
            f"  ❌ Losses       : {results['LOSS']}\n"
            f"  🎯 Win Rate     : <b>{wr:.1f}%</b>\n"
            f"  💰 Net PnL      : {fmt_pnl(total_pnl)}\n\n"
            f"  ── By Market Condition ──\n")
        for cond,res in cond_res.items():
            ct=res["W"]+res["L"]; wr2=(res["W"]/ct*100) if ct>0 else 0
            em="📈" if cond=="bull" else "📉" if cond=="bear" else "➡️"
            r+=f"  {em} {cond:<9}: {res['W']}W/{res['L']}L ({wr2:.1f}%)\n"
        r+=f"\n  🕐 {get_ist_time()}"
        return r
    except Exception as e: return f"Backtest failed: {e}"

def _H(title, emoji=""):
    """Safe Telegram header — no box drawing chars that can cause parse failures."""
    icon = f"{emoji} " if emoji else ""
    return f"{'━'*32}\n{icon}<b>{title}</b>\n{'━'*32}"

def get_active_trades_text():
    if not active_trades:
        return (f"{_H('ACTIVE TRADES','📊')}\n\n"
                f"  ⚪  No active trades right now.\n\n"
                f"  🛡️ CB      : {'🔴 ACTIVE' if check_circuit_breaker() else '🟢 OK'}\n"
                f"  ⏳ Pending : {len(pending_signals)}\n"
                f"  🕐 {get_ist_time()}")
    now=get_ist_datetime(); lines=[]; total_pnl=0.0
    for coin,t in active_trades.items():
        price=get_price(t.get("symbol",coin+"USDT"))
        sl_pct=abs(t["entry"]-t["sl"])/t["entry"]*100
        tp_pct=abs(t["tp"]-t["entry"])/t["entry"]*100
        rr=round(tp_pct/sl_pct,1) if sl_pct>0 else 0
        dirn=t.get("direction","?"); lev=t.get("leverage",1)
        pat=t.get("pattern","?").split(" + ")[0]
        dir_em="🟢 LONG  ▲" if dirn=="BUY" else "🔴 SHORT ▼"
        dur=""
        if t.get("timestamp"):
            try:
                m=int((now-t["timestamp"]).total_seconds()/60)
                dur=f"{m}m" if m<60 else f"{m//60}h {m%60}m"
            except Exception: pass
        if price:
            pnl=((price-t["entry"])/t["entry"])*100*lev if dirn=="BUY" else ((t["entry"]-price)/t["entry"])*100*lev
            total_pnl+=pnl; pnl_txt=fmt_pnl(pnl)
        else: pnl_txt="⏳"
        ms=t.get("milestones_sent",[])
        badge=("  🚀 M3 LOCKED" if "p3" in ms else "  🔥 M2 LOCKED" if "p2" in ms else "  ✅ M1 BREAKEVEN" if "p1" in ms else "")
        target=t.get("profit_target", abs(t['tp']-t['entry'])/t['entry']*100*lev)
        partial="  💰 Partial TP" if t.get("partial_tp_taken") else ""
        lines.append(
            f"  ┌─────────────────────────────┐\n"
            f"  │  🪙 <b>{coin}</b>  {dir_em}  ✦ {lev}x\n"
            f"  │  💰 Entry  : <code>{format_price(t['entry'])}</code>\n"
            f"  │  🎯 Target : <code>{format_price(t['tp'])}</code>  ↑{tp_pct:.2f}%\n"
            f"  │  🛑 Stop   : <code>{format_price(t['sl'])}</code>  ↓{sl_pct:.2f}%\n"
            f"  │  ⚖️  RR 1:{rr}   ⏱️ {dur or 'just now'}\n"
            f"  │  📈 PnL    : {pnl_txt}  🎯Target:+{target:.1f}%{partial}\n"
            f"  │  📌 {pat}{badge}\n"
            f"  └─────────────────────────────┘"
        )
    return (f"{_H(f'ACTIVE TRADES  {len(active_trades)}/{MAX_ACTIVE_TRADES}','📊')}\n\n"
            + "\n\n".join(lines) +
            f"\n\n  ══════════════════════════════\n"
            f"  💼 Portfolio PnL : {fmt_pnl(total_pnl)}\n"
            f"  🛡️ CB      : {'🔴 ACTIVE' if check_circuit_breaker() else '🟢 OK'}\n"
            f"  ⏳ Pending : {len(pending_signals)}\n"
            f"  🕐 {get_ist_time()}")

def get_pattern_stats_text():
    tw=sum(s["wins"] for s in pattern_stats.values())
    tl=sum(s["losses"] for s in pattern_stats.values())
    ts=sum(s["signals"] for s in pattern_stats.values())
    owr=(tw/ts*100) if ts>0 else 0
    tp_=sum(s["total_pnl"] for s in pattern_stats.values())
    text=(f"{_H('PATTERN PERFORMANCE','📈')}\n\n"
          f"  🔢 Signals  : {ts}   ✅ {tw}W  ❌ {tl}L\n"
          f"  🎯 Win Rate : <b>{owr:.1f}%</b>\n"
          f"  💰 Total PnL: {fmt_pnl(tp_)}\n\n"
          f"  ══════════════════════════════\n\n")
    for pat,s in sorted(pattern_stats.items(),key=lambda x:x[1]["signals"],reverse=True):
        if s["signals"]>0:
            wr=(s["wins"]/s["signals"])*100
            filled=int(wr/10); bar="█"*filled+"░"*(10-filled)
            flag="🔴" if wr<40 else "🟡" if wr<60 else "🟢"
            susp="  🔒 SUSP" if is_pattern_suspended(pat) else ""
            w=s.get("weight",1.0); wt="📈" if w>1.05 else "📉" if w<0.95 else "━"
            text+=(f"  {flag} <b>{pat}</b>{susp}\n"
                   f"  [{bar}] {wr:.1f}%  •  {s['signals']} signals  •  {wt}{w:.1f}x\n"
                   f"  {s['wins']}W / {s['losses']}L  •  {fmt_pnl(s['total_pnl'])}\n\n")
    text+=f"  🕐 {get_ist_time()}"
    return text

def get_10day_summary_text():
    today=datetime.now(IST).date()
    text=f"{_H('10-DAY PERFORMANCE','📅')}\n\n"
    ow=ol=0; op=0.0; best_pnl=worst_pnl=None; best_ds=worst_ds=""
    for days_ago in range(9,-1,-1):
        day=today-timedelta(days=days_ago)
        dt=[j for j in trade_journal if j.get("date")==str(day)]
        w=sum(1 for t in dt if t["result"]=="WIN"); l=sum(1 for t in dt if t["result"]=="LOSS")
        total=w+l; pnl=sum(t["pnl"] for t in dt)
        ow+=w; ol+=l; op+=pnl; ds=day.strftime("%d %b")
        if total==0:
            text+=f"  ⚪ <b>{ds}</b>  ──────────  No trades\n"
        else:
            em="✅" if w>l else "❌" if l>w else "➖"
            bar="█"*w+"░"*l
            text+=f"  {em} <b>{ds}</b>  [{bar[:8]}]  {w}W/{l}L  {fmt_pnl(pnl)}\n"
            if best_pnl is None or pnl>best_pnl: best_pnl=pnl; best_ds=ds
            if worst_pnl is None or pnl<worst_pnl: worst_pnl=pnl; worst_ds=ds
    ot=ow+ol; owr=(ow/ot*100) if ot>0 else 0
    text+=(f"\n  ══════════════════════════════\n"
           f"  ✅ Wins     : {ow}   ❌ Losses  : {ol}\n"
           f"  🎯 Win Rate : <b>{owr:.1f}%</b>\n"
           f"  💰 PnL      : {fmt_pnl(op)}   📊 Avg/Day: {fmt_pnl(op/10)}\n")
    if best_ds:  text+=f"  🏆 Best Day : {best_ds}  ({fmt_pnl(best_pnl)})\n"
    if worst_ds: text+=f"  📉 Worst    : {worst_ds}  ({fmt_pnl(worst_pnl)})\n"
    text+=f"  🕐 {get_ist_time()}"
    return text

def get_streak_text():
    if not trade_journal:
        return f"{_H('STREAK TRACKER','🔥')}\n\n  ⚪ No trades recorded yet."
    st=trade_journal[-1]["result"]; sc=0
    for t in reversed(trade_journal):
        if t["result"]==st: sc+=1
        else: break
    total=len(trade_journal); wins=sum(1 for t in trade_journal if t["result"]=="WIN")
    owr=(wins/total*100) if total>0 else 0
    em="🔥" if st=="WIN" else "❄️"
    bar=(em*min(sc,8)).ljust(8)
    label="WINNING 🏆" if st=="WIN" else "LOSING ⚠️"
    return (f"{_H('STREAK TRACKER','🔥')}\n\n"
            f"  {bar}\n\n"
            f"  Current  : <b>{sc} {label}</b>\n"
            f"  Trades   : {total}\n"
            f"  Win Rate : <b>{owr:.1f}%</b>\n\n"
            f"  🕐 {get_ist_time()}")

def get_best_text():
    if not trade_journal:
        return f"{_H('BEST PERFORMERS','🏆')}\n\n  ⚪ No trade data yet."
    cs={}; ps2={}
    for t in trade_journal:
        c=t["coin"]
        if c not in cs: cs[c]={"W":0,"L":0,"pnl":0.0}
        cs[c]["W" if t["result"]=="WIN" else "L"]+=1; cs[c]["pnl"]+=t["pnl"]
        p=t["pattern"]
        if p not in ps2: ps2[p]={"W":0,"L":0}
        ps2[p]["W" if t["result"]=="WIN" else "L"]+=1
    medals=["🥇","🥈","🥉","🏅","🏅"]
    sc=sorted(cs.items(),key=lambda x:(x[1]["W"]/(x[1]["W"]+x[1]["L"])) if (x[1]["W"]+x[1]["L"])>0 else 0,reverse=True)[:5]
    sp=sorted(ps2.items(),key=lambda x:(x[1]["W"]/(x[1]["W"]+x[1]["L"])) if (x[1]["W"]+x[1]["L"])>0 else 0,reverse=True)[:5]
    text=(f"{_H('BEST PERFORMERS','🏆')}\n\n"
          f"  💰 <b>Top Coins by Win Rate</b>\n\n")
    for i,(c,s) in enumerate(sc):
        tot=s["W"]+s["L"]; wr=(s["W"]/tot*100) if tot>0 else 0
        text+=f"  {medals[i]} <b>{c}</b>  {wr:.1f}% WR  ({tot} trades)  {fmt_pnl(s['pnl'])}\n"
    text+=f"\n  ══════════════════════════════\n\n  🌀 <b>Top Patterns by Win Rate</b>\n\n"
    for i,(p,s) in enumerate(sp):
        tot=s["W"]+s["L"]; wr=(s["W"]/tot*100) if tot>0 else 0
        text+=f"  {medals[i]} <b>{p}</b>  {wr:.1f}%  ({tot} trades)\n"
    text+=f"\n  🕐 {get_ist_time()}"
    return text

def get_risk_text():
    if not active_trades:
        return (f"{_H('RISK MONITOR','🛡️')}\n\n"
                f"  ⚪  No active trades — zero exposure.\n\n"
                f"  🛡️ CB     : {'🔴 ACTIVE' if check_circuit_breaker() else '🟢 OK'}\n"
                f"  📉 Losses : {daily_losses}/{MAX_DAILY_LOSSES}\n"
                f"  🕐 {get_ist_time()}")
    text=f"{_H('RISK MONITOR','🛡️')}\n\n"; total_risk=0.0
    for coin,t in active_trades.items():
        rp=abs(t["entry"]-t["sl"])/t["entry"]*100*t["leverage"]
        tp_pct=abs(t["tp"]-t["entry"])/t["entry"]*100
        sl_pct=abs(t["entry"]-t["sl"])/t["entry"]*100
        total_risk+=rp
        filled=min(int(rp/5),10); bar="█"*filled+"░"*(10-filled)
        em="🔴" if rp>20 else "🟡" if rp>10 else "🟢"
        text+=(f"  {em} <b>{coin}</b>  {t['direction']}  {t['leverage']}x\n"
               f"  [{bar}]  Max loss: <b>{rp:.1f}%</b>\n"
               f"  SL dist: {sl_pct:.2f}%  TP dist: {tp_pct:.2f}%\n\n")
    total_em="🔴" if total_risk>40 else "🟡" if total_risk>20 else "🟢"
    text+=(f"  ══════════════════════════════\n"
           f"  {total_em} Portfolio Risk : <b>{total_risk:.1f}%</b>\n"
           f"  📌 Slots   : {len(active_trades)}/{MAX_ACTIVE_TRADES}\n"
           f"  🛡️ CB      : {'🔴 ACTIVE' if check_circuit_breaker() else '🟢 OK'}\n"
           f"  📉 Losses  : {daily_losses}/{MAX_DAILY_LOSSES}\n"
           f"  ⏳ Pending : {len(pending_signals)}\n"
           f"  🕐 {get_ist_time()}")
    return text

def get_learning_text():
    text=(f"{_H('BOT LEARNING','🧠')}\n\n"
          f"  📊 <b>Market Memory</b>\n\n")
    icons={"bull":"📈","bear":"📉","sideways":"➡️"}
    for cond in ["bull","bear","sideways"]:
        mem=market_memory[cond]; tot=mem["wins"]+mem["losses"]
        wr=(mem["wins"]/tot*100) if tot>0 else 0
        text+=(f"  {icons.get(cond,'')} <b>{cond.capitalize()}</b>   {mem['wins']}W / {mem['losses']}L   {wr:.1f}%\n"
               f"     Best: {mem['best_pattern'] or 'N/A'}\n\n")
    text+=f"  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
    if learning_notes:
        text+=f"  💡 <b>Latest Insights</b>\n\n"
        for note in learning_notes[-8:]: text+=f"  ◆ {note}\n"
    else:
        text+=f"  💡 <b>Insights</b>\n\n  ⚪ No insights yet — keeps building as trades close.\n"
    text+=f"\n  🕐 {get_ist_time()}"
    return text

def get_journal_text():
    if not trade_journal:
        return f"{_H('TRADE JOURNAL','📓')}\n\n  ⚪ No trades recorded yet."
    recent=trade_journal[-10:][::-1]
    text=f"{_H('TRADE JOURNAL  (Last 10)','📓')}\n\n"
    for t in recent:
        em="✅" if t.get("result")=="WIN" else "🔴"
        dirn_em="🟢" if t.get("direction")=="BUY" else "🔴"
        text+=(f"  {em} <b>{t.get('coin','?')}</b>  {dirn_em} {t.get('direction','?')}\n"
               f"  ◆ {t.get('pattern','?')}\n"
               f"  💰 {fmt_pnl(t.get('pnl',0))}  ⏱️ {t.get('duration','?')}  📅 {t.get('date','?')}\n\n")
    total=len(trade_journal); wins=sum(1 for t in trade_journal if t.get("result")=="WIN")
    wr=(wins/total*100) if total>0 else 0
    text+=(f"  ══════════════════════════════\n"
           f"  Total: {total}   Win Rate: <b>{wr:.1f}%</b>\n"
           f"  🕐 {get_ist_time()}")
    return text

def get_patterns_ranked_text():
    text=f"{_H('ALL PATTERNS RANKED','🌀')}\n\n"
    all_pats=[]
    for pat,s in pattern_stats.items():
        sigs=s.get("signals",0); wr=(s["wins"]/sigs*100) if sigs>0 else 0
        w=s.get("weight",1.0); adj=get_adjusted_score(pat,80,"bull")
        all_pats.append((pat,sigs,wr,w,adj))
    all_pats.sort(key=lambda x:x[4],reverse=True)
    medal_list=["🥇","🥈","🥉"]
    for i,(pat,sigs,wr,w,adj) in enumerate(all_pats):
        medal=medal_list[i] if i<len(medal_list) else f"{i+1}."
        flag="🔴" if wr<40 and sigs>=5 else "🟢" if wr>=60 else "🟡"
        susp="  🔒" if is_pattern_suspended(pat) else ""
        wt="📈" if w>1.05 else "📉" if w<0.95 else "━"
        filled=int(wr/10); bar="█"*filled+"░"*(10-filled)
        if sigs==0:
            text+=f"  {medal} <b>{pat}</b>{susp}  <i>(no trades yet)</i>\n\n"
        else:
            text+=(f"  {medal} <b>{pat}</b>{susp}\n"
                   f"  {flag} [{bar}] {wr:.1f}%\n"
                   f"  {sigs} trades · {wt}{w:.2f}x · Adj:{adj:.1f}\n\n")
    if not all_pats:
        text+="  ⚪ No pattern data yet.\n"
    text+=f"  🕐 {get_ist_time()}"
    return text

def get_trend_label(ema20,ema50,price,label):
    if not ema20 or not ema50: return "Neutral"
    diff_pct=((ema20-ema50)/ema50)*100
    if price>ema20>ema50:
        if diff_pct>3:   return "Strong Uptrend"
        elif diff_pct>1: return "Uptrend"
        else:            return "Weak Uptrend"
    elif price<ema20<ema50:
        if diff_pct<-3:  return "Strong Downtrend"
        elif diff_pct<-1:return "Downtrend"
        else:            return "Weak Downtrend"
    elif price>ema50: return "Ranging Above EMA50"
    else:             return "Ranging Below EMA50"

def cmd_trend(coin_input):
    coin=coin_input.upper().replace("USDT","").strip()
    symbol=coin+"USDT"; price=get_price(symbol)
    if not price:
        return f"{_H(f'TREND  {coin}','📉')}\n\n  ❌ Could not fetch price for <b>{coin}</b>."
    tfs=[("1d","Daily"),("4h","4 Hour"),("1h","1 Hour"),("15m","15 Min")]
    results=[]; bull_c=bear_c=0
    for tf,label in tfs:
        klines=get_klines(symbol,tf,60)
        if not klines or len(klines)<50: results.append((label,"No data",50,0)); continue
        closes=[float(k[4]) for k in klines]
        e20=calculate_ema(closes,20); e50=calculate_ema(closes,50)
        rsi=calculate_rsi(closes); adx=calculate_adx(klines)
        trend=get_trend_label(e20,e50,price,label)
        if "Uptrend" in trend:   bull_c+=1
        if "Downtrend" in trend: bear_c+=1
        results.append((label,trend,rsi,adx))
    if bull_c>=3:   bias="STRONGLY BULLISH 🚀"; bias_em="🟢"
    elif bull_c>=2: bias="BULLISH 📈";           bias_em="🟢"
    elif bear_c>=3: bias="STRONGLY BEARISH 🔻"; bias_em="🔴"
    elif bear_c>=2: bias="BEARISH 📉";           bias_em="🔴"
    else:           bias="MIXED / SIDEWAYS ➡️"; bias_em="🟡"
    klines_4h=get_klines(symbol,"4h",30); s1=r1=0
    if klines_4h and len(klines_4h)>=5:
        highs=[float(k[2]) for k in klines_4h]; lows=[float(k[3]) for k in klines_4h]
        c4=[float(k[4]) for k in klines_4h]
        pivot=(highs[-2]+lows[-2]+c4[-2])/3
        r1=2*pivot-lows[-2]; s1=2*pivot-highs[-2]
    rsi_1h=results[2][2] if len(results)>2 else 50
    adx_1h=results[2][3] if len(results)>2 else 0
    text=(f"{_H(f'TREND ANALYSIS  {coin}','📉')}\n\n"
          f"  💰 Price  : <code>{format_price(price)}</code>\n"
          f"  {bias_em} Bias   : <b>{bias}</b>\n\n"
          f"  ┌── TIMEFRAMES ───────────────┐\n")
    for label,trend,rsi,adx in results:
        em="🟢" if "Up" in trend else "🔴" if "Down" in trend else "🟡"
        text+=f"  │  {em} <b>{label:<8}</b> {trend}\n"
    text+=(f"  └─────────────────────────────┘\n\n"
           f"  ┌── KEY LEVELS ───────────────┐\n"
           f"  │  🎯 Resistance : <code>{format_price(r1)}</code>\n"
           f"  │  🛡️ Support    : <code>{format_price(s1)}</code>\n"
           f"  │  📊 RSI(1h)   : {rsi_1h:.1f}   ADX: {adx_1h:.1f}\n"
           f"  └─────────────────────────────┘\n\n"
           f"  🕐 {get_ist_time()}")
    return text

DESK_REPORT_COINS = ["LAB","BTC","ETH","PIPPIN","LINK","NEAR"]

def send_8h_ai_desk_report():
    """
    Point 4: The 8-Hour VIP "Prop-Desk" AI Report (retimed from 4h to 8h per user request).

    Every 4 hours, pulls 4h (macro structure) and 15m (entry timing) data
    for DESK_REPORT_COINS, batches all six into ONE Claude call (single
    request, not six separate ones — keeps this cheap regardless of how
    many coins are on the list), and asks for a human-like top-down desk
    report. If Claude flags any coin as genuinely ready to execute right
    now, that gets a distinct, more urgent ping — not buried in the
    regular report — since "specifically ping you to take action" was an
    explicit part of the request, not just a status summary.

    Uses the same API-call/response-parsing pattern as ai_analyst_review()
    (existing, proven code) rather than inventing a new one, adapted for:
    fixed named coins instead of open trades, and 4h+15m structure data
    instead of live PnL numbers.
    """
    if not ANTHROPIC_API_KEY:
        logger.info("send_8h_ai_desk_report: ANTHROPIC_API_KEY not set, skipping")
        return

    coin_summaries = []
    ready_candidates = []  # coins with enough data to plausibly be "ready" — informs prompt only
    for coin in DESK_REPORT_COINS:
        symbol = coin + "USDT"
        price = get_price(symbol)
        if not price:
            coin_summaries.append(f"{coin}: price unavailable, skipping")
            continue
        klines_4h = get_klines(symbol, "4h", 50)
        klines_15m = get_klines(symbol, "15m", 50)
        if not klines_4h or len(klines_4h) < 30 or not klines_15m or len(klines_15m) < 30:
            coin_summaries.append(f"{coin}: insufficient chart data, skipping")
            continue

        closes_4h = [float(k[4]) for k in klines_4h]
        e20_4h = calculate_ema(closes_4h, 20); e50_4h = calculate_ema(closes_4h, 50)
        trend_4h = "BULLISH" if (e20_4h and e50_4h and e20_4h > e50_4h) else "BEARISH" if (e20_4h and e50_4h) else "UNCLEAR"
        adx_4h = calculate_adx(klines_4h)

        closes_15m = [float(k[4]) for k in klines_15m]
        rsi_15m = calculate_rsi(closes_15m)
        ms_15m = detect_market_structure(klines_15m)
        vcp_dir, vcp_tightness = detect_volatility_contraction(closes_15m,
            [float(k[2]) for k in klines_15m], [float(k[3]) for k in klines_15m],
            [float(k[5]) for k in klines_15m], price)
        zones = get_htf_zones(symbol)
        zone_ok_buy, zone_label_buy = is_in_zone(price, "BUY", zones)
        zone_ok_sell, zone_label_sell = is_in_zone(price, "SELL", zones)
        zone_note = (f"in demand zone {zone_label_buy}" if zone_ok_buy else
                     f"in supply zone {zone_label_sell}" if zone_ok_sell else "no zone tap")

        coin_summaries.append(
            f"{coin}: price {format_price(price)} | 4H trend:{trend_4h} ADX:{adx_4h:.0f} | "
            f"15m RSI:{rsi_15m:.0f} structure:{ms_15m['bias']}{' +ChoCh' if ms_15m['choch'] else ''}"
            f"{' +BOS' if ms_15m['bos'] else ''} | {zone_note}"
            f"{' | coiling (VCP)' if vcp_dir else ''}"
        )

    if not coin_summaries:
        logger.warning("send_8h_ai_desk_report: no coin data available, skipping")
        return

    # User-requested addition: a dedicated BTC trend / overall market
    # regime header, separate from the per-coin list. Reuses
    # detect_market_condition() — the same function the rest of the bot
    # already relies on for bull/bear/sideways classification — rather
    # than inventing a second, possibly-inconsistent regime read. That
    # function's vocabulary is bull/bear/sideways only (no "mixed"
    # category exists anywhere else in the codebase to be consistent
    # with); rather than guess at new "mixed" thresholds, per-coin
    # disagreement is left to show up naturally in the AI's own per-coin
    # reads in the report body below, instead of a second invented
    # classifier layered on top.
    btc_price_desk = get_price("BTCUSDT")
    btc_klines_desk = get_klines("BTCUSDT", "1h", 60)
    market_regime = detect_market_condition(btc_price_desk, btc_klines_desk) if btc_price_desk and btc_klines_desk else "sideways"
    regime_label = {"bull":"BULLISH 📈","bear":"BEARISH 📉","sideways":"SIDEWAYS ➡️"}.get(market_regime, "UNKNOWN")

    prompt = (
        "You are running the 8-hour desk check for a proprietary trading desk, reviewing "
        "a fixed watchlist top-down: 4-Hour macro structure first, then 15-minute entry timing.\n\n"
        "WATCHLIST:\n" + "\n".join(coin_summaries) + "\n\n"
        "For EACH coin with data, give a one-line read: what's the macro bias, and is anything "
        "actionable forming on the 15m (zone tap, ChoCh, coiling, clean structure)? Be direct, "
        "like a real trader's desk note, not a generic summary.\n"
        "Format EXACTLY like this per coin:\n"
        "COIN: [read] — [1 short sentence]\n\n"
        "Then, if and ONLY if a coin genuinely looks ready to execute RIGHT NOW (not just "
        "'watching', an actual clean entry), add this exact line for each one:\n"
        "READY: COIN — [why, 1 sentence]\n"
        "If nothing is ready, omit the READY lines entirely — do not force one."
    )

    try:
        res = requests.post(
            "https://api.anthropic.com/v1/messages",
            headers={"x-api-key":ANTHROPIC_API_KEY,"anthropic-version":"2023-06-01",
                     "content-type":"application/json"},
            json={"model":"claude-haiku-4-5-20251001","max_tokens":600,
                  "messages":[{"role":"user","content":prompt}]},
            timeout=25
        )
        if res.status_code != 200:
            logger.warning(f"send_8h_ai_desk_report: API returned {res.status_code}")
            return
        text = res.json()["content"][0]["text"].strip()
    except Exception as e:
        logger.warning(f"send_8h_ai_desk_report: {e}")
        return

    ready_lines = []
    report_lines = []
    for line in text.split("\n"):
        line = line.strip()
        if not line: continue
        if line.upper().startswith("READY:"):
            ready_lines.append(line)
        else:
            report_lines.append(line)

    msg = f"{_H('8H PROP-DESK REPORT','🏦')}\n\n"
    msg += f"  ₿ BTC Trend: <b>{regime_label}</b>\n\n"
    for line in report_lines:
        if ":" in line:
            coin_part, rest = line.split(":", 1)
            msg += f"  🔹 <b>{coin_part.strip()}</b>:{rest}\n"
    msg += f"\n  🕐 {get_ist_time()}"
    send_telegram(msg)
    logger.info(f"8h desk report sent, {len(ready_lines)} ready candidate(s)")

    # Explicit, distinct ping for anything flagged genuinely trade-ready —
    # not buried inside the regular report, per "specifically ping you to
    # take action."
    if ready_lines:
        ping_msg = f"{_H('⚡ DESK ALERT — TRADE READY','🚨')}\n\n"
        for line in ready_lines:
            _, rest = line.split(":", 1) if ":" in line else ("", line)
            ping_msg += f"  🎯 {rest.strip()}\n"
        ping_msg += f"\n  Check the chart now — this may be your entry.\n  🕐 {get_ist_time()}"
        send_telegram(ping_msg)


def ai_analyst_review():
    """
    AI Analyst — reviews ALL active trades using Claude, like a portfolio manager.
    Suggests: HOLD, TAKE PROFIT, EXIT NOW, or WATCH CLOSELY for each trade.
    """
    if not active_trades:
        return f"{_H('AI ANALYST','🧠')}\n\n  🌙 No active trades to review.\n\n  🕐 {get_ist_time()}"
    if not ANTHROPIC_API_KEY:
        return f"{_H('AI ANALYST','🧠')}\n\n  ⚠️ ANTHROPIC_API_KEY not set — AI Analyst unavailable.\n\n  🕐 {get_ist_time()}"

    trades_summary=[]
    for coin,t in active_trades.items():
        symbol=t.get("symbol",coin+"USDT")
        price=get_price(symbol)
        if not price: continue
        direction=t.get("direction","BUY"); entry=t["entry"]
        tp=t["tp"]; sl=t["sl"]; lev=t.get("leverage",1)
        if direction=="BUY": pnl=((price-entry)/entry)*100*lev
        else:                pnl=((entry-price)/entry)*100*lev
        klines=get_klines(symbol,"15m",30)
        rsi=calculate_rsi([float(k[4]) for k in klines]) if klines else 50
        adx=calculate_adx(klines) if klines else 20
        dist_tp=abs(tp-price)/price*100
        dist_sl=abs(price-sl)/price*100
        trades_summary.append(
            f"{coin}: {direction} | Entry:{format_price(entry)} Now:{format_price(price)} "
            f"PnL:{pnl:+.1f}% | TP:{dist_tp:.1f}% away SL:{dist_sl:.1f}% away | "
            f"RSI:{rsi:.0f} ADX:{adx:.0f} | Pattern:{t.get('pattern','?')}"
        )

    if not trades_summary:
        return f"{_H('AI ANALYST','🧠')}\n\n  ⚠️ Could not fetch live prices.\n\n  🕐 {get_ist_time()}"

    prompt = (
        "You are a professional portfolio manager reviewing open crypto futures positions.\n\n"
        "OPEN TRADES:\n" + "\n".join(trades_summary) + "\n\n"
        "For EACH trade, give a one-line action: HOLD, TAKE PROFIT NOW, EXIT NOW (cut loss), "
        "or WATCH CLOSELY (risk building). Base it on PnL, distance to TP/SL, RSI, and ADX.\n"
        "Format EXACTLY like this per trade:\n"
        "COIN: ACTION — short reason (max 12 words)\n\n"
        "Then add one line: OVERALL: [1 sentence portfolio-level insight]"
    )

    try:
        res = requests.post(
            "https://api.anthropic.com/v1/messages",
            headers={"x-api-key":ANTHROPIC_API_KEY,"anthropic-version":"2023-06-01",
                     "content-type":"application/json"},
            json={"model":"claude-haiku-4-5-20251001","max_tokens":400,
                  "messages":[{"role":"user","content":prompt}]},
            timeout=20
        )
        if res.status_code!=200:
            return f"{_H('AI ANALYST','🧠')}\n\n  ⚠️ AI request failed.\n\n  🕐 {get_ist_time()}"
        text = res.json()["content"][0]["text"].strip()
    except Exception as e:
        return f"{_H('AI ANALYST','🧠')}\n\n  ⚠️ Error: {e}\n\n  🕐 {get_ist_time()}"

    msg = f"{_H('AI ANALYST — PORTFOLIO REVIEW','🧠')}\n\n"
    for line in text.split("\n"):
        line=line.strip()
        if not line: continue
        if line.upper().startswith("OVERALL:"):
            msg += f"\n  📌 <b>{line}</b>\n"
        elif ":" in line:
            coin_part, rest = line.split(":",1)
            em = "🟢" if "HOLD" in rest.upper() else "✅" if "TAKE PROFIT" in rest.upper() else "🔴" if "EXIT" in rest.upper() else "⚠️"
            msg += f"  {em} <b>{coin_part.strip()}</b>:{rest}\n"
    msg += f"\n  🕐 {get_ist_time()}"
    return msg


def cmd_market():
    btc=get_price("BTCUSDT"); eth=get_price("ETHUSDT"); sol=get_price("SOLUSDT")
    bnb=get_price("BNBUSDT"); xrp=get_price("XRPUSDT")
    btc_klines=get_klines("BTCUSDT","1h",50); btc_trend="N/A"
    if btc_klines and len(btc_klines)>=50:
        closes=[float(k[4]) for k in btc_klines]
        e20=calculate_ema(closes,20); e50=calculate_ema(closes,50)
        btc_trend=get_trend_label(e20,e50,btc,"1h") if btc else "N/A"
    scan_list=["BTC","ETH","BNB","SOL","XRP","ADA","AVAX","DOT","LINK","NEAR",
               "INJ","SUI","APT","ARB","OP","ATOM","PEPE","WIF","BONK","DOGE"]
    gainers=[]; losers=[]
    for coin in scan_list:
        try:
            klines=get_klines(coin+"USDT","1d",3)
            if klines and len(klines)>=2:
                prev=float(klines[-2][4]); curr=float(klines[-1][4])
                chg=((curr-prev)/prev)*100 if prev>0 else 0
                if chg>0: gainers.append((coin,chg))
                else:     losers.append((coin,chg))
        except Exception: continue
    gainers.sort(key=lambda x:x[1],reverse=True)
    losers.sort(key=lambda x:x[1])
    fng=get_fear_greed_index()
    fng_lbl=("Extreme Fear 😨" if fng<=25 else "Fear 😟" if fng<=45 else
             "Neutral 😐" if fng<=55 else "Greed 😊" if fng<=75 else "Extreme Greed 🤑")
    fng_bar="█"*min(int(fng/10),10)+"░"*(10-min(int(fng/10),10))
    fng_em="🔴" if fng<=25 else "🟠" if fng<=45 else "🟡" if fng<=55 else "🟢"
    bt_em="🟢" if "Up" in btc_trend else "🔴" if "Down" in btc_trend else "🟡"
    text=(f"{_H('MARKET OVERVIEW','🌍')}\n\n"
          f"  {fng_em} <b>Fear & Greed: {fng} — {fng_lbl}</b>\n"
          f"  [{fng_bar}]\n\n"
          f"  ┌── LIVE PRICES ──────────────┐\n")
    for sym,lbl,p in [("BTC","₿  BTC",btc),("ETH","Ξ  ETH",eth),
                       ("SOL","◎  SOL",sol),("BNB","◈  BNB",bnb),("XRP","✦  XRP",xrp)]:
        if p: text+=f"  │  {lbl}  <code>${format_price(p)}</code>\n"
    text+=(f"  │\n"
           f"  │  {bt_em} BTC Trend: {btc_trend}\n"
           f"  └─────────────────────────────┘\n\n")
    text+=f"  🚀 <b>Top Gainers 24h</b>\n"
    for coin,chg in gainers[:5]:
        bar="▓"*min(int(abs(chg)/2),8)
        text+=f"  🟢 <b>{coin:<6}</b> +{chg:.2f}%  {bar}\n"
    text+=f"\n  📉 <b>Top Losers 24h</b>\n"
    for coin,chg in losers[:5]:
        bar="░"*min(int(abs(chg)/2),8)
        text+=f"  🔴 <b>{coin:<6}</b> {chg:.2f}%  {bar}\n"
    text+=f"\n  🕐 {get_ist_time()}"
    return text

def cmd_compare(coins_str):
    coins=[c.upper().replace("USDT","") for c in coins_str.split()[:4]]
    if not coins: return f"{_H('COIN COMPARE','🆚')}\n\n  Usage: /compare BTC ETH SOL"
    text=f"{_H('COIN COMPARE','🆚')}\n\n"
    for coin in coins:
        symbol=coin+"USDT"; price=get_price(symbol)
        if not price: text+=f"  ❌ <b>{coin}</b> — Not found\n\n"; continue
        klines=get_klines(symbol,"4h",60); trend="N/A"; rsi=50.0; adx=0.0
        if klines and len(klines)>=50:
            closes=[float(k[4]) for k in klines]
            e20=calculate_ema(closes,20); e50=calculate_ema(closes,50)
            rsi=calculate_rsi(closes); adx=calculate_adx(klines)
            trend=get_trend_label(e20,e50,price,"4h")
        em="🟢" if "Up" in trend else "🔴" if "Down" in trend else "🟡"
        rsi_em="🔴" if rsi>70 else "🟢" if rsi<30 else "🟡"
        text+=(f"  {em} <b>{coin}</b>  <code>{format_price(price)}</code>\n"
               f"  Trend: {trend}\n"
               f"  RSI: {rsi_em} {rsi:.1f}   ADX: {adx:.1f}\n\n")
    text+=f"  🕐 {get_ist_time()}"
    return text

def cmd_scan_manual(btc_trend,fng,market_condition):
    send_telegram(
        f"{_H('SCANNING NOW','🔍')}\n\n"
        f"  ⚙️ Scanning {len(COINS)} coins...\n"
        f"  📊 Market: {market_condition.upper()}  F&G: {fng}\n"
        f"  🕐 {get_ist_time()}"
    )
    results=[]
    for coin in COINS:
        try:
            symbol=coin+"USDT"; price=get_price(symbol); klines=get_klines(symbol,"15m",100)
            if not price or not klines: continue
            found=detect_patterns(symbol,klines,price,btc_trend)
            if not found: continue
            scored=get_all_pattern_scores(found,market_condition)
            if not scored: continue
            best=scored[0]; adj_score=min(best[1]+min(len(scored)*0.5,3),99)
            tf_score=get_timeframe_score(symbol,best[2])
            if tf_score==-1: continue
            results.append({"coin":coin,"direction":best[2],"score":adj_score,
                            "pattern":best[0],"tf_score":tf_score})
        except Exception: continue
        time.sleep(0.1)
    if not results:
        return (f"{_H('SCAN RESULTS','🔍')}\n\n"
                f"  ⚪ No qualifying setups found right now.\n\n"
                f"  📊 Market: {market_condition.upper()}   F&G: {fng}\n"
                f"  🕐 {get_ist_time()}")
    results.sort(key=lambda x:x["score"],reverse=True)
    text=f"{_H(f'SCAN RESULTS  ({len(results)} found)','🔍')}\n\n"
    for r in results[:5]:
        em="🟢" if r["direction"]=="BUY" else "🔴"
        dir_arrow="▲ LONG" if r["direction"]=="BUY" else "▼ SHORT"
        tf="⭐⭐" if r["tf_score"]==3 else "⭐" if r["tf_score"]==2 else "◆"
        filled=min(int(r["score"]/10),10); bar="█"*filled+"░"*(10-filled)
        text+=(f"  {em} <b>{r['coin']}</b>  {dir_arrow}  {tf}\n"
               f"  [{bar}] {r['score']:.1f}\n"
               f"  ◆ {r['pattern']}\n\n")
    text+=(f"  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
           f"  📊 {market_condition.upper()}   F&G: {fng}\n"
           f"  🕐 {get_ist_time()}")
    return text

def cmd_hidden_gems():
    """
    💎 Hidden Gems Scanner
    Finds coins with:
    - Volume suddenly spiking (2x+ vs 20-bar average)
    - Price not yet pumped (within 5% of recent lows)
    - Early momentum building (RSI 40-60, not overbought)
    - Increasing OI (smart money entering)
    """
    send_telegram(
        f"{_H('SCANNING FOR HIDDEN GEMS','💎')}\n\n"
        f"  ⚙️ Analysing {len(COINS)} coins...\n"
        f"  🔍 Looking for volume spikes + early momentum\n"
        f"  🕐 {get_ist_time()}"
    )
    gems = []; vol_spikes = []; unpumped = []; early_mom = []
    for coin in COINS:
        try:
            symbol = coin + "USDT"
            price  = get_price(symbol)
            if not price: continue
            klines = get_klines(symbol, "1h", 50)
            if not klines or len(klines) < 30: continue
            closes = [float(k[4]) for k in klines]
            highs  = [float(k[2]) for k in klines]
            lows   = [float(k[3]) for k in klines]
            vols   = [float(k[5]) for k in klines]
            vol_ratio  = get_volume_ratio(klines)
            rsi        = calculate_rsi(closes)
            ema20      = calculate_ema(closes, 20)
            ema50      = calculate_ema(closes, 50)
            # Price change 24h
            chg_24h = ((closes[-1] - closes[-24]) / closes[-24] * 100) if len(closes) >= 24 else 0
            # Distance from recent low (last 48 bars)
            recent_low  = min(lows[-48:])
            dist_low_pct = ((price - recent_low) / recent_low * 100) if recent_low > 0 else 999
            # Volume spike: current vol > 2x average AND price moved up
            if vol_ratio >= 2.0 and closes[-1] > closes[-2] and chg_24h < 15:
                vol_spikes.append({
                    "coin": coin, "vol_ratio": vol_ratio,
                    "price": price, "chg_24h": chg_24h, "rsi": rsi
                })
            # Unpumped: near recent lows, volume starting to build, RSI neutral
            if dist_low_pct < 8 and vol_ratio >= 1.3 and 35 <= rsi <= 58:
                unpumped.append({
                    "coin": coin, "dist_low": dist_low_pct,
                    "price": price, "vol_ratio": vol_ratio, "rsi": rsi
                })
            # Early momentum: EMA20 crossing above EMA50, RSI rising from neutral
            if ema20 and ema50 and ema20 > ema50 and 45 <= rsi <= 65 and chg_24h > 1 and vol_ratio >= 1.2:
                early_mom.append({
                    "coin": coin, "rsi": rsi,
                    "price": price, "chg_24h": chg_24h, "vol_ratio": vol_ratio
                })
            time.sleep(0.1)
        except Exception: continue

    # Sort each category
    vol_spikes.sort(key=lambda x: x["vol_ratio"], reverse=True)
    unpumped.sort(key=lambda x: x["dist_low"])
    early_mom.sort(key=lambda x: x["rsi"])

    msg = f"{_H('HIDDEN GEMS REPORT','💎')}\n\n"

    # Volume Spikes
    msg += f"  🚀 <b>Volume Spikes</b>  <i>(sudden activity)</i>\n"
    if vol_spikes:
        for g in vol_spikes[:5]:
            bar = "█" * min(int(g["vol_ratio"]), 8)
            msg += (f"  🔹 <b>{g['coin']}</b>  <code>{format_price(g['price'])}</code>\n"
                    f"      Vol: {bar} {g['vol_ratio']:.1f}x avg  •  24h: {g['chg_24h']:+.1f}%  •  RSI:{g['rsi']:.0f}\n\n")
    else:
        msg += "  ⚪ No volume spikes right now.\n\n"

    msg += f"  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"

    # Not yet pumped
    msg += f"  💤 <b>Not Yet Pumped</b>  <i>(near lows, vol building)</i>\n"
    if unpumped:
        for g in unpumped[:5]:
            msg += (f"  🔹 <b>{g['coin']}</b>  <code>{format_price(g['price'])}</code>\n"
                    f"      {g['dist_low']:.1f}% above low  •  Vol:{g['vol_ratio']:.1f}x  •  RSI:{g['rsi']:.0f}\n\n")
    else:
        msg += "  ⚪ No unpumped coins found.\n\n"

    msg += f"  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"

    # Early momentum
    msg += f"  📈 <b>Early Momentum</b>  <i>(EMA cross + rising RSI)</i>\n"
    if early_mom:
        for g in early_mom[:5]:
            msg += (f"  🔹 <b>{g['coin']}</b>  <code>{format_price(g['price'])}</code>\n"
                    f"      24h: {g['chg_24h']:+.1f}%  •  Vol:{g['vol_ratio']:.1f}x  •  RSI:{g['rsi']:.0f}\n\n")
    else:
        msg += "  ⚪ No early momentum coins found.\n\n"

    total = len(set([g["coin"] for g in vol_spikes+unpumped+early_mom]))
    msg += (f"  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
            f"  💎 {total} potential gems found\n")

    # ── BEST PICK — highest-confidence tradeable setup among all gems ──
    candidate_coins = list(dict.fromkeys(
        [g["coin"] for g in vol_spikes] + [g["coin"] for g in unpumped] + [g["coin"] for g in early_mom]
    ))
    best=None
    btc_p=get_price("BTCUSDT"); btc_k=get_klines("BTCUSDT","1h",50)
    bt_e=calculate_ema([float(x[4]) for x in btc_k],50) if btc_k else None
    btc_trend=1 if (btc_p and bt_e and btc_p>bt_e) else -1
    mc = detect_market_condition(btc_p,btc_k) if btc_p and btc_k else "sideways"
    for coin in candidate_coins[:25]:
        try:
            symbol=coin+"USDT"; price=get_price(symbol)
            klines=get_klines(symbol,"15m",100)
            if not price or not klines or len(klines)<50: continue
            found=detect_patterns(symbol,klines,price,btc_trend)
            if not found: continue
            scored=get_all_pattern_scores(found,mc)
            if not scored: continue
            top=scored[0]; adj_score=min(top[1]+min(len(scored)*0.5,3),99)
            if adj_score<MIN_SETUP_SCORE: continue
            tf_score=get_timeframe_score(symbol,top[2])
            if tf_score==-1: continue
            if best is None or adj_score>best["score"]:
                best={"coin":coin,"symbol":symbol,"price":price,"klines":klines,
                      "direction":top[2],"pattern":top[0],"score":adj_score,"tf_score":tf_score}
        except Exception: continue
        time.sleep(0.05)

    if best:
        klines_15m=best["klines"]; entry=best["price"]
        atr_1h_klines=get_klines(best["symbol"],"1h",30)
        atr_1h=calculate_atr(atr_1h_klines) if atr_1h_klines else calculate_atr(klines_15m)
        atr_pct=(atr_1h/entry)*100 if entry>0 else 0
        sl=get_structure_sl(klines_15m,best["direction"],entry,atr_1h)
        # TP anchored to the ACTUAL sl distance, guaranteeing >=1:2 R/R at minimum
        # (already existed — see format_and_send's identical block). NEW this
        # round: try the nearest real Supply/Demand zone first via
        # get_structural_tp — only fires once here (for the single best gem
        # candidate, not per-scanned-coin), so the extra get_htf_zones call is
        # cheap and cached.
        sl_dist=abs(entry-sl)
        atr_tp_dist=atr_1h*ATR_TP_MULTIPLIER
        min_rr_tp_dist=sl_dist*MIN_RR_RATIO
        gem_zones=get_htf_zones(best["symbol"])
        structural_tp_gem=get_structural_tp(entry,best["direction"],gem_zones,min_rr_tp_dist)
        if structural_tp_gem is not None:
            tp=structural_tp_gem
        else:
            tp_dist=max(atr_tp_dist,min_rr_tp_dist)
            tp=entry+tp_dist if best["direction"]=="BUY" else entry-tp_dist
        ms_b=detect_market_structure(klines_15m)
        vol_ratio_gem=get_volume_ratio(klines_15m)
        oi_rising=get_oi_trend(best["symbol"])
        adx_val=calculate_adx(klines_15m)
        closes=[float(k[4]) for k in klines_15m]
        rsi_val=calculate_rsi(closes)
        vol_ok=is_volume_confirmed(klines_15m)
        rsi_ok=35<=rsi_val<=65 if best["direction"]=="BUY" else 35<=rsi_val<=65
        funding_ok=True
        vwap=calculate_vwap(klines_15m); vwap_ok=(entry>vwap if best["direction"]=="BUY" else entry<vwap) if vwap else False
        st_15m=calculate_supertrend(klines_15m,ST_PERIOD,ST_MULTIPLIER)
        st_ok=(st_15m==best["direction"])
        zone_ok=False
        btc_aligned_gem,_=is_btc_aligned(best["direction"])
        grade,pts,_=get_signal_grade(best["score"],vol_ratio_gem,oi_rising,best["tf_score"],vol_ok,rsi_ok,funding_ok,st_ok,vwap_ok,zone_ok,adx_val,btc_aligned_gem,ms_b["bias"],ms_b["bos"])
        lev=get_smart_leverage(best["symbol"],atr_pct,best["score"],grade)
        profit_target=(abs(tp-entry)/entry)*100*lev
        sl_pct=abs(entry-sl)/entry*100; tp_pct=abs(tp-entry)/entry*100
        rr=tp_pct/sl_pct if sl_pct>0 else 0
        dir_arrow="🟢 LONG ▲" if best["direction"]=="BUY" else "🔴 SHORT ▼"
        grade_em="🏆" if "A+" in grade else "🍀" if " A" in grade else "🥈" if "B" in grade else "🥉"
        msg += (f"\n  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
                f"  ⭐ <b>BEST PICK RIGHT NOW</b>  {grade_em}\n"
                f"  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
                f"  🪙 <b>{best['coin']}</b>  {dir_arrow}  ✦ {lev}x\n"
                f"  {grade_em} {grade}  •  Score {best['score']:.0f}/100\n"
                f"  📌 {best['pattern']}\n\n"
                f"  💰 Entry  : <code>{format_price(entry)}</code>\n"
                f"  🎯 Target : <code>{format_price(tp)}</code>  +{tp_pct:.2f}%\n"
                f"  🛑 Stop   : <code>{format_price(sl)}</code>  -{sl_pct:.2f}%\n"
                f"  ⚖️ RR 1:{rr:.1f}  •  📈 Max Profit +{profit_target:.1f}%\n\n"
                f"  💡 Type <code>/trend {best['coin']}</code> to confirm before entering.\n")
    else:
        msg += f"\n  ⭐ <b>BEST PICK</b>: No setup ≥{MIN_SETUP_SCORE} found among gems right now.\n"

    msg += (f"  ⚠️ <i>Always confirm before trading</i>\n"
            f"  🕐 {get_ist_time()}")
    return msg

def ai_analyze_setup(coin, direction, klines, price, pattern, rsi_val, adx_val, vol_strength, is_volatile=False, penalty_notes=None, htf_4h_trend=None, zone_ok=False, zone_label="", ms_bos=False, ms_choch=False, ms_bias=None, is_sweep=False, sl_pct=None, rr_ratio=None, hist_wr=None, hist_signals=0):
    """
    The Human Narrative upgrade: Claude previously only saw 20 raw 15m
    candles (~5 hours of data) with no idea what the 4h trend was or
    whether price is sitting on a real institutional level. That's not
    what a human trader uses to decide — a human's first questions are
    "what's the bigger trend, and where are we relative to it," THEN
    they look at the local candles.

    Now the prompt leads with the actual top-down narrative, built from
    real data already computed by the caller (4h trend via get_htf_trend,
    zone status via detect_supply_demand_zones/is_in_zone, structure/BOS/
    ChoCh via detect_market_structure, whether a Liquidity Sweep
    (detect_liquidity_sweep) just occurred in this trade's direction, the
    planned sl_pct/rr_ratio so the AI can reject a beautiful pattern if
    the required stop is too wide for the current volatility, and — Point
    3 fix — this specific pattern's real historical win rate from
    pattern_stats, so live price-action reading gets weighed against
    actual data-driven probability, not evaluated in a vacuum) — not
    invented context. Only after establishing that narrative does the
    prompt hand over the raw candles, the same order a discretionary
    trader actually works in.

    Cost ~$0.004 per call (larger prompt now, still Haiku-tier cheap).
    """
    if not ANTHROPIC_API_KEY: return None
    try:
        recent=klines[-20:]
        candle_desc=[]
        for i,k in enumerate(recent):
            o,h,l,c=float(k[1]),float(k[2]),float(k[3]),float(k[4])
            body=abs(c-o); rng=h-l if h>l else 0.0001
            lower_wick=(min(o,c)-l)/rng*100
            upper_wick=(h-max(o,c))/rng*100
            ctype="BULL" if c>o else "BEAR"
            strength="strong" if body/rng>0.6 else "weak" if body/rng<0.3 else "normal"
            candle_desc.append(f"C{i+1}:{ctype} {strength} low_wick={lower_wick:.0f}% up_wick={upper_wick:.0f}%")
        dir_word="LONG (BUY)" if direction=="BUY" else "SHORT (SELL)"
        vol_note = "Volatility is currently ELEVATED vs normal — could mean a real breakout OR just chop. Judge from candle quality." if is_volatile else "Volatility is normal."
        penalty_line = f"Note: scanner flagged secondary weakness — {', '.join(penalty_notes)}. Weigh this against price action quality.\n" if penalty_notes else ""

        # ── THE HUMAN NARRATIVE — top-down context, built from real data ──
        htf_desc = {1:"BULLISH",-1:"BEARISH",0:"NEUTRAL/UNCLEAR",None:"UNKNOWN"}.get(htf_4h_trend,"UNKNOWN")
        zone_line = f"We are currently sitting INSIDE a {'Demand' if direction=='BUY' else 'Supply'} zone ({zone_label})." if zone_ok else "Price is NOT inside a known Supply/Demand zone right now — no man's land."
        if ms_choch and zone_ok:
            shift_line = "A Change of Character (ChoCh) just fired INSIDE this zone — the market just reversed structure exactly at a key level. This is the strongest possible setup type."
        elif ms_choch:
            shift_line = "A Change of Character (ChoCh) just fired, but NOT inside a known zone — a real structure shift, though without the location confirmation."
        elif ms_bos:
            shift_line = f"A Break of Structure (BOS) just confirmed, structure bias is {ms_bias or 'unclear'}."
        else:
            shift_line = f"No fresh structure break yet — current bias reads {ms_bias or 'neutral'}."

        narrative = (
            f"THE NARRATIVE (read this first, the way a trader scans top-down):\n"
            + (f"- 🚨 A LIQUIDITY SWEEP just occurred! Price pierced a key structural "
               f"level to trap retail stop-losses and reversed.\n" if is_sweep else "")
            + f"- 4-Hour trend: {htf_desc}.\n"
            f"- {zone_line}\n"
            f"- {shift_line}\n"
            f"- On the 15-minute chart, the scanner flagged: {pattern}.\n"
            + (f"- DATA-DRIVEN PROBABILITY: this pattern has historically won "
               f"{hist_wr:.0f}% of the time over {hist_signals} tracked signals. "
               f"Weigh this real track record against what you see in the candles — "
               f"a clean-looking setup on a historically weak pattern deserves more "
               f"skepticism, and vice versa.\n" if hist_wr is not None
               else "- DATA-DRIVEN PROBABILITY: not enough tracked history for this "
                    "pattern yet to have a reliable win rate — judge on price action alone.\n")
            + (f"- The planned Stop Loss is {sl_pct:.2f}% away with a 1:{rr_ratio:.1f} "
               f"Risk/Reward. Reject this trade if the required stop is too wide for "
               f"the current local volatility.\n" if sl_pct is not None and rr_ratio is not None else "")
        )

        prompt=(f"You are a veteran prop-firm trader with years on a funded desk — blunt, "
                f"experienced, and speaking with the raw conviction of someone who has seen "
                f"this exact setup a hundred times before. You are NOT writing a textbook "
                f"summary or a balanced research note. You call it like you see it: "
                f"'Clear retail trap,' 'Heavy accumulation,' 'Chop zone, avoiding,' 'This is "
                f"a gift,' 'Textbook, but late.' Deciding whether to actually "
                f"take this trade with real money, the way you would after scanning a chart top-down "
                f"across multiple timeframes — starting with the big picture, then zooming in.\n\n"
                f"Setup: {coin}/USDT {dir_word}\n\n"
                f"{narrative}\n"
                f"Price: {format_price(price)}\n"
                f"RSI: {rsi_val:.0f} | ADX (trend strength): {adx_val:.0f} | Volume: {vol_strength:.1f}x average\n"
                f"{vol_note}\n{penalty_line}\n"
                f"Last 20 candles on the 15m chart, oldest to newest (C20 = right now):\n"+"\n".join(candle_desc)+
                f"\n\nUsing the narrative above FIRST — is this accumulation/distribution happening at a "
                f"real level, with the higher timeframe on your side? Then look at the local candles: "
                f"do NOT just grade whether momentum already confirmed — a confirmed breakout candle "
                f"often means the easy money is already made. Judge the STAGE of this move by looking "
                f"for signs of build-up: volatility contraction, absorption (heavy volume with small net "
                f"price change), dying volume before a squeeze, or wicks showing rejection at a level "
                f"repeatedly tested. A calm, tightening range sitting just under resistance (or above "
                f"support), inside a real zone, with the 4h trend aligned, is often the BEST entry — "
                f"before the crowd's breakout signal fires.\n\n"
                f"Classify the STAGE: EARLY (still coiling/building, low risk entry), MID (breaking out now, "
                f"some room left), or LATE (already extended, chasing).\n\n"
                f"Respond EXACTLY in this format:\n"
                f"VERDICT: [CLEAN/MESSY]\nCONFIDENCE: [HIGH/MEDIUM/LOW]\n"
                f"STAGE: [EARLY/MID/LATE]\nTRADE: [YES/NO]\n"
                f"ETA_READ: [short phrase, e.g. 'could take 2-4h to develop' or 'move may already be exhausted']\n"
                f"REASONING: [2 sentences max — speak like a trader calling it on the desk, not a "
                f"textbook. Be specific and blunt about what you saw. Real desk language, not "
                f"hedge-everything corporate-speak.]")
        res=requests.post("https://api.anthropic.com/v1/messages",
            headers={"x-api-key":ANTHROPIC_API_KEY,"anthropic-version":"2023-06-01",
                     "content-type":"application/json"},
            json={"model":"claude-haiku-4-5-20251001","max_tokens":220,
                  "messages":[{"role":"user","content":prompt}]},timeout=15)
        if res.status_code!=200: return None
        text=res.json()["content"][0]["text"].strip()
        verdict="CLEAN" if "VERDICT: CLEAN" in text else "MESSY"
        confidence="HIGH" if "CONFIDENCE: HIGH" in text else "MEDIUM" if "CONFIDENCE: MEDIUM" in text else "LOW"
        stage="EARLY" if "STAGE: EARLY" in text else "MID" if "STAGE: MID" in text else "LATE" if "STAGE: LATE" in text else "UNKNOWN"
        trade="YES" in (text.split("TRADE:")[-1].split("\n")[0] if "TRADE:" in text else "")
        eta_read=text.split("ETA_READ:")[-1].split("REASONING:")[0].strip() if "ETA_READ:" in text else ""
        reasoning=text.split("REASONING:")[-1].strip() if "REASONING:" in text else ""
        logger.info(f"AI {coin}: {verdict}/{confidence}/STAGE:{stage}/TRADE:{'YES' if trade else 'NO'}")
        return {"verdict":verdict,"confidence":confidence,"stage":stage,"trade":trade,
                "eta_read":eta_read,"reasoning":reasoning}
    except Exception as e:
        logger.warning(f"AI error {coin}: {e}"); return None

def expire_pending_signals():
    now=get_ist_datetime()
    expired=[c for c,s in list(pending_signals.items()) if s.get("expires_at") and now>s["expires_at"]]
    for coin in expired:
        del pending_signals[coin]
        send_telegram(f"⏰ <b>{BOT_HEADER}</b>\nSignal expired: <b>{coin}</b>")
    if expired: save_pending_signals()

def check_price_alerts():
    triggered=[]
    for sym,alert in list(price_alerts.items()):
        price=get_price(sym+"USDT")
        if not price: continue
        if alert["direction"]=="above" and price>=alert["price"]:
            send_telegram(
                f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
                f"🔔 <b>PRICE ALERT TRIGGERED</b>\n"
                f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
                f"  🪙 <b>{sym}</b> broke ABOVE target\n"
                f"  🎯 Target : <code>{format_price(alert['price'])}</code>\n"
                f"  💰 Now    : <code>{format_price(price)}</code>\n"
                f"  🕐 {get_ist_time()}"
            )
            triggered.append(sym)
        elif alert["direction"]=="below" and price<=alert["price"]:
            send_telegram(
                f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
                f"🔔 <b>PRICE ALERT TRIGGERED</b>\n"
                f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
                f"  🪙 <b>{sym}</b> broke BELOW target\n"
                f"  🎯 Target : <code>{format_price(alert['price'])}</code>\n"
                f"  💰 Now    : <code>{format_price(price)}</code>\n"
                f"  🕐 {get_ist_time()}"
            )
            triggered.append(sym)
    for sym in triggered: del price_alerts[sym]
    if triggered: save_alerts()

def update_trailing_sl(coin,trade,price):
    trail=abs(trade["tp"]-trade["entry"])*0.3
    if trade["direction"]=="BUY":
        new_sl=price-trail
        if new_sl>trade["sl"]: active_trades[coin]["sl"]=new_sl; save_active_trades()
    else:
        new_sl=price+trail
        if new_sl<trade["sl"]: active_trades[coin]["sl"]=new_sl; save_active_trades()

def check_profit_milestones(coin,trade,price,pnl):
    """
    Proportional milestone system — scales with the trade's ACTUAL profit target,
    not a fixed +10/+20/+35. A 70% target gets milestones at 21/42/59.5%.
    Each milestone locks in a growing share of the gain reached so far.
    """
    milestones=trade.get("milestones_sent",[])
    ep=trade["entry"]; direction=trade["direction"]; lev=trade.get("leverage",1)
    target=trade.get("profit_target", abs(trade["tp"]-ep)/ep*100*lev)
    if target<=0: target=10  # safety fallback

    m1=target*0.30; m2=target*0.60; m3=target*0.85

    def _price_at_pnl(target_pnl):
        move = ep * (target_pnl/100) / lev
        return ep+move if direction=="BUY" else ep-move

    def _sl_lock_price(target_pnl, lock_ratio):
        gain_price = abs(_price_at_pnl(target_pnl) - ep)
        locked = gain_price * lock_ratio
        return ep+locked if direction=="BUY" else ep-locked

    def _ms(icon,title,detail,sl_price):
        return (f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
                f"{icon} <b>{title}</b>\n"
                f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
                f"  🪙 Coin    : <b>{coin}</b>\n"
                f"  📈 PnL     : {fmt_pnl(pnl)}\n"
                f"  🎯 Target  : +{target:.1f}%\n"
                f"  🛑 Move SL : <code>{format_price(sl_price)}</code>\n"
                f"  💡 {detail}\n"
                f"  🕐 {get_ist_time()}")

    if pnl>=m1 and "p1" not in milestones:
        sl_price=_sl_lock_price(m1,0.0)  # breakeven
        active_trades[coin].setdefault("milestones_sent",[]).append("p1")
        active_trades[coin]["sl"]=sl_price
        save_active_trades()
        send_telegram(_ms("✅",f"MILESTONE 1  •  +{m1:.1f}% reached",
                          "SL moved to breakeven — trade is now risk-free!",sl_price))
    elif pnl>=m2 and "p2" not in milestones:
        sl_price=_sl_lock_price(m2,0.5)
        active_trades[coin].setdefault("milestones_sent",[]).append("p2")
        active_trades[coin]["sl"]=sl_price
        save_active_trades()
        send_telegram(_ms("🔥",f"MILESTONE 2  •  +{m2:.1f}% reached",
                          f"SL moved to lock in ~50% of current gain ({fmt_pnl(m2*0.5)} minimum).",sl_price))
    elif pnl>=m3 and "p3" not in milestones:
        sl_price=_sl_lock_price(m3,0.8)
        active_trades[coin].setdefault("milestones_sent",[]).append("p3")
        active_trades[coin]["sl"]=sl_price
        save_active_trades()
        send_telegram(_ms("🚀",f"MILESTONE 3  •  +{m3:.1f}% reached",
                          f"SL moved to lock in ~80% of current gain ({fmt_pnl(m3*0.8)} minimum). Final target +{target:.1f}%!",sl_price))

def get_ltf_confirmation(symbol, direction):
    """
    Point 3: Lower Timeframe (5m) execution trigger.
    The 15m/1h scan builds the candidate ("watchlist" logic already happening
    via the main scan cycle) — this checks the 5m chart for the actual
    execution-timing confirmation, so entries aren't stale by a full 15m candle.
    Returns (confirmed: bool, note: str) — this is informational/scoring,
    not a hard block, since 5m data can be noisy on its own.
    """
    try:
        k5 = get_klines(symbol, "5m", 20)
        if not k5 or len(k5) < 10:
            return True, "5m data unavailable"
        closes5 = [float(k[4]) for k in k5]
        last3_move = (closes5[-1] - closes5[-3]) / closes5[-3] * 100 if closes5[-3] > 0 else 0
        rsi5 = calculate_rsi(closes5)
        if direction == "BUY":
            confirmed = last3_move > -0.3 and rsi5 > 35
            note = f"5m momentum {'holding' if confirmed else 'fading'} ({last3_move:+.2f}%, RSI {rsi5:.0f})"
        else:
            confirmed = last3_move < 0.3 and rsi5 < 65
            note = f"5m momentum {'holding' if confirmed else 'fading'} ({last3_move:+.2f}%, RSI {rsi5:.0f})"
        return confirmed, note
    except Exception:
        return True, "5m check unavailable"


def format_and_send(setup,coin,is_river=False,is_instant=False,market_condition="bull"):
    global sent_coins,coin_cooldowns
    if check_circuit_breaker(): return False
    if not is_good_trading_session(coin): return False
    live_price=get_price(setup["symbol"])
    if not live_price: return False
    entry=live_price
    drift_pct=abs(entry-setup["scan_price"])/setup["scan_price"]*100
    if drift_pct>3.5:
        logger.info(f"{coin} rejected - drifted {drift_pct:.1f}%"); return False
    klines_15m=get_klines(setup["symbol"],"15m",100)
    klines_1h=get_klines(setup["symbol"],"1h",50)
    if not klines_15m: return False
    closes=[float(x[4]) for x in klines_15m]
    atr_1h=calculate_atr(klines_1h) if len(klines_1h)>=15 else calculate_atr(klines_15m)
    atr_pct=(atr_1h/entry)*100 if entry>0 else 0
    vol_ok=is_volume_confirmed(klines_15m)
    rsi_ok=is_rsi_valid(closes,setup["direction"])
    funding_ok=is_funding_favorable(setup["symbol"],setup["direction"])
    is_volatile=not is_volatility_normal(klines_15m)

    # ── WEIGHTED SCORING (Point 1) ──────────────────────────────
    # Secondary indicators no longer hard-block a signal outright.
    # Each miss subtracts from setup_score instead, so a genuinely
    # strong price-action pattern can still survive one weak indicator,
    # while stacking multiple misses correctly kills a weak setup.
    score_penalty = 0
    penalty_notes = []
    if not vol_ok:
        score_penalty += 6; penalty_notes.append("volume soft (-6)")
    if not rsi_ok:
        score_penalty += 5; penalty_notes.append("RSI stretched (-5)")
    if not funding_ok:
        score_penalty += 4; penalty_notes.append("funding against (-4)")
    if is_volatile:
        logger.info(f"{coin} high volatility — noted, letting AI judge")

    # Point 3: LTF (5m) execution timing check — informational, feeds scoring not a hard block
    ltf_confirmed, ltf_note = get_ltf_confirmation(setup["symbol"], setup["direction"])
    if not ltf_confirmed:
        score_penalty += 4; penalty_notes.append(f"5m timing weak (-4)")
    logger.info(f"{coin} LTF check: {ltf_note}")

    # Point 3: Sector correlation — "check the neighborhood" like a human trader.
    # A coin moving against its own sector is more likely a fake-out/trap.
    sector_ok, sector_note = check_sector_correlation(coin, setup["direction"])
    if not sector_ok:
        score_penalty += 5; penalty_notes.append(f"sector diverging (-5)")
    logger.info(f"{coin} sector check: {sector_note}")

    # Point 4(a): weekend low-liquidity — soft penalty, not a full block.
    # Weekend moves can be genuine, but choppy low-volume weekend action
    # is a well-known trap generator, so it costs a modest score deduction
    # rather than shutting the bot down for 2 out of every 7 days.
    if is_weekend_low_liquidity():
        score_penalty += 3; penalty_notes.append("weekend low-liquidity (-3)")

    st_15m=calculate_supertrend(klines_15m,ST_PERIOD,ST_MULTIPLIER)
    st_1h=calculate_supertrend(klines_1h,ST_PERIOD,ST_MULTIPLIER) if klines_1h else st_15m
    st_ok=(st_15m==setup["direction"]) and (st_1h==setup["direction"])
    st_strongly_against = (st_15m!=setup["direction"]) and (st_1h!=setup["direction"])
    if st_strongly_against:
        # Both timeframes opposed is still a hard block — this isn't lag,
        # it's the trend actively pointing the other way on two timeframes.
        logger.info(f"{coin} rejected - SuperTrend opposed on both 15m+1h"); return False
    elif st_15m!=setup["direction"] or st_1h!=setup["direction"]:
        score_penalty += 5; penalty_notes.append("SuperTrend partial lag (-5)")

    setup["setup_score"] = max(setup["setup_score"] - score_penalty, 0)
    if penalty_notes:
        logger.info(f"{coin} score adjusted: -{score_penalty} ({', '.join(penalty_notes)}) -> {setup['setup_score']:.1f}")
    # Point 1 fix: is_instant was being decided by the CALLER using the
    # pre-penalty score (e.g. 99.0), then passed in as a fixed boolean —
    # so a signal that dropped to 93.0 after penalties here still kept
    # showing the ⚡ INSTANT tag, because that decision was already locked
    # in before this function even ran. Confirmed exactly in the logs:
    # "INSTANT: DYDX|SELL|Score:99.0" at tag time, "Signal sent:
    # DYDX|SELL|Score:93" at send time — still tagged Instant either way.
    # Recomputed here, AFTER the real final score is known, so the tag
    # (and the expiry window / message wording that depend on it below)
    # are authoritative on the true final score, not a stale snapshot.
    is_instant = setup["setup_score"] >= INSTANT_SIGNAL_THRESHOLD
    # A setup that's now too weak after penalties gets dropped here,
    # instead of earlier — so strong price action had a chance to survive.
    # ── STRICT HARD FLOOR (Point 2) ─────────────────────────────
    # Previously this checked MIN_SETUP_SCORE-8 (=82), which is the exact
    # leak responsible for 88.0-scored signals — some tagged "Instant" —
    # reaching Telegram. Raised to a literal 92.0 floor as specified: a
    # signal below 92.0 after penalties is killed here, before any of the
    # more expensive zone/OI/whale lookups below even run.
    if setup["setup_score"] < 92.0:
        logger.info(f"{coin} rejected - score {setup['setup_score']:.1f} below strict floor 92.0"); return False
    vwap=calculate_vwap(klines_15m); vwap_ok=False; vwap_label="N/A"
    if vwap:
        if setup["direction"]=="BUY" and entry>vwap:    vwap_ok=True; vwap_label=f"Above {format_price(vwap)}"
        elif setup["direction"]=="SELL" and entry<vwap: vwap_ok=True; vwap_label=f"Below {format_price(vwap)}"
        else: vwap_label=f"{'Below' if setup['direction']=='BUY' else 'Above'} {format_price(vwap)}"
    zones=get_htf_zones(setup["symbol"])
    zone_ok,zone_label=is_in_zone(entry,setup["direction"],zones)
    div=detect_rsi_divergence(closes)
    oi_rising=get_oi_trend(setup["symbol"])
    # Point (whale/OI removal): replaced has_whale_activity's boolean-only
    # signal with the real volume-vs-average multiple — computed once here,
    # reused both for grading (get_signal_grade below) and for the message
    # display further down, so the actual number is finally visible instead
    # of a whale emoji that never showed any underlying data.
    vol_ratio=get_volume_ratio(klines_15m)
    adx_val=calculate_adx(klines_15m)
    tf_score=setup.get("tf_score",get_timeframe_score(setup["symbol"],setup["direction"]))
    # Order Book removed (Point 2) — data was thin/frequently "N/A" and
    # dragging grades down on missing data rather than genuine weakness.
    # Replaced with a real BTC 1-Hour trend alignment check (Point 3).
    btc_aligned,btc_1h_trend=is_btc_aligned(setup["direction"])
    ms = detect_market_structure(klines_15m)
    highs_15m=[float(k[2]) for k in klines_15m]; lows_15m=[float(k[3]) for k in klines_15m]
    res = ms["swing_high"] if ms["swing_high"] > 0 else max(highs_15m[-30:-1])
    sup = ms["swing_low"]  if ms["swing_low"]  > 0 else min(lows_15m[-30:-1])
    # Point 4: re-check for a Liquidity Sweep here so the result can be passed
    # into the AI narrative. detect_patterns() already ran this same check
    # earlier in scan_coins, but its result never propagated past deciding
    # whether "Liquidity Sweep" got added to the pattern list — the actual
    # sweep_dir/sweep_strength were local to that function and never reached
    # here. Re-running it is cheap: pure computation on klines_15m, already
    # fetched above, no new API calls.
    opens_15m=[float(k[1]) for k in klines_15m]
    sweep_dir_chk, sweep_strength_chk = detect_liquidity_sweep(klines_15m, highs_15m, lows_15m, closes, opens_15m, sup, res, ms)
    is_sweep = sweep_dir_chk is not None and sweep_dir_chk == setup["direction"]
    # Compute grade FIRST so leverage can use it
    grade_result=get_signal_grade(setup["setup_score"],vol_ratio,oi_rising,tf_score,vol_ok,rsi_ok,funding_ok,st_ok,vwap_ok,zone_ok,adx_val,btc_aligned,ms["bias"],ms["bos"])
    grade,pts,breakdown=grade_result

    # Second half of the strict floor: kill Grade C outright, regardless
    # of the numeric score. A signal could clear 92.0 on the 100-point
    # score yet still score poorly on the confirmation scorecard (e.g.
    # a Tier 1 pattern with a big Location bonus but weak everything
    # else) — that combination is still not good enough to reach Telegram.
    if grade == "Grade C":
        logger.info(f"{coin} rejected - Grade C on scorecard ({pts} pts) despite score {setup['setup_score']:.1f}"); return False

    lev=get_smart_leverage(setup["symbol"],atr_pct,setup["setup_score"],grade)
    sl=get_structure_sl(klines_15m,setup["direction"],entry,atr_1h)
    # TP anchored to the ACTUAL sl distance, guaranteeing >=1:2 R/R at minimum
    # (this part already existed — see cmd_hidden_gems's identical block for
    # the original reasoning). NEW this round: before falling back to that
    # generic ATR-based distance, try targeting the nearest real Supply/
    # Demand zone (get_structural_tp) — a human trader aims at an actual
    # level, not a mathematical multiple. The structural target is only
    # used if it clears the same 1:2 floor; otherwise the guaranteed
    # ATR/min-RR fallback below is used unchanged, so the R:R guarantee is
    # never weakened by this addition.
    sl_dist=abs(entry-sl)
    atr_tp_dist=atr_1h*ATR_TP_MULTIPLIER
    min_rr_tp_dist=sl_dist*MIN_RR_RATIO
    structural_tp=get_structural_tp(entry,setup["direction"],zones,min_rr_tp_dist)
    if structural_tp is not None:
        tp=structural_tp
        logger.info(f"{coin} TP anchored to structural zone at {format_price(tp)} "
                    f"(R:R {abs(tp-entry)/sl_dist:.1f}:1)")
    else:
        tp_dist=max(atr_tp_dist,min_rr_tp_dist)
        tp=entry+tp_dist if setup["direction"]=="BUY" else entry-tp_dist
    profit_target=(abs(tp-entry)/entry)*100*lev
    if profit_target<MIN_PROFIT_TARGET:
        risk=abs(tp-entry)/entry
        if risk>0:
            needed=int(MIN_PROFIT_TARGET/(risk*100))+1
            if needed<=20: lev=needed; profit_target=(abs(tp-entry)/entry)*100*lev
            else: return False
    setup["leverage"]=lev

    # ── SCORE GATE — UNIVERSAL, NO COIN RESTRICTION ─────────────
    # Claude is called if and only if the letter grade (scorecard-based,
    # see get_signal_grade) is "Grade A" or "Grade A+" — the VIP_AI_COINS/
    # PREMIUM_COINS name-check that used to additionally require the coin
    # be on a specific watchlist has been DELETED per explicit instruction.
    # Confirmed via logs this was a real, active restriction (not stale
    # drift): "IO not on VIP/Premium watchlist — executing on pure code,
    # no AI call" despite IO scoring a genuine Grade A+. Any coin on the
    # scanner that earns Grade A/A+ now reaches the AI, full stop.
    #
    # NOTE ON THRESHOLD: the instruction was given in two slightly
    # different framings — "Grade A or A+" vs "final setup score of 93.0
    # or higher." These are NOT the same condition: `grade` is purely
    # scorecard-point-based (14+/18+ pts, from an earlier round that
    # deliberately decoupled it from the 100-point score), so a coin
    # could be Grade A at score 90, or Grade B at score 95. Kept the
    # grade-based check (the more detailed framing, and consistent with
    # that earlier round's whole point of making `grade` the authoritative
    # signal-quality indicator) rather than silently switching to a raw
    # score>=93 check, which would partially undo that decoupling. Flagging
    # this choice explicitly rather than picking silently.
    #
    # VIP_AI_COINS is now entirely unused (no longer referenced by any
    # live conditional) — left defined at the top of the file rather than
    # deleted, in case the restriction is wanted back later. PREMIUM_COINS
    # is still genuinely used elsewhere (the 24/7 session override), so
    # that one remains load-bearing.
    ai_result=None
    is_grade_a = grade in ("Grade A 🍀","Grade A+ 🍀")
    if is_grade_a:
        # vol_ratio already computed earlier in this function (same
        # klines_15m, same formula) — reused directly instead of
        # recomputing an identical value under a different name.
        rsi_ai=calculate_rsi(closes)
        adx_ai=calculate_adx(klines_15m)
        # The Human Narrative: fetch the real 4h trend and pass the zone/
        # structure data already computed above (zone_ok, zone_label, ms)
        # instead of sending Claude only raw 15m candles with no context.
        htf_4h=get_htf_trend(setup["symbol"],"4h")
        # Point 4: sl_pct/rr_ratio computed here specifically for the AI call —
        # entry/sl/tp are already available at this point (defined above), so
        # this is a cheap local computation, kept separate from the later
        # sl_pct/rr_ratio used for message formatting to avoid any risk of
        # colliding with that existing, independently-scoped calculation.
        sl_pct_ai = abs(entry-sl)/entry*100 if entry>0 else 0
        tp_pct_ai = abs(tp-entry)/entry*100 if entry>0 else 0
        rr_ratio_ai = tp_pct_ai/sl_pct_ai if sl_pct_ai>0 else 0
        # Point 3 (Market Memory Integration): pull this pattern's real historical
        # win rate from pattern_stats. NOTE: the instruction named "market_memory"
        # as the source, but that dict is actually keyed by market condition
        # (bull/bear/sideways) and only stores which pattern is "best" per
        # condition — it does not contain per-pattern win rates. pattern_stats is
        # the actual tracker with wins/losses/signals per pattern name, so that's
        # what's used here. setup["pattern"] can be a compound string like
        # "Bull Flag Break + EMA Trend" (primary + confluence patterns) — split
        # to the primary pattern, matching how trade-close already attributes
        # wins/losses (see the identical .split(" + ")[0] at trade-close time).
        primary_pattern = setup["pattern"].split(" + ")[0]
        pstat = pattern_stats.get(primary_pattern, {})
        p_signals = pstat.get("signals", 0)
        hist_wr = (pstat.get("wins", 0) / p_signals * 100) if p_signals >= 3 else None
        logger.info(f"{coin} AI-eligible + {grade} ({pts}pts) — calling Claude for final verification")
        ai_result=ai_analyze_setup(coin,setup["direction"],klines_15m,entry,
                                   setup["pattern"],rsi_ai,adx_ai,vol_ratio,is_volatile,penalty_notes,
                                   htf_4h_trend=htf_4h,zone_ok=zone_ok,zone_label=zone_label,
                                   ms_bos=ms["bos"],ms_choch=ms["choch"],ms_bias=ms["bias"],
                                   is_sweep=is_sweep,sl_pct=sl_pct_ai,rr_ratio=rr_ratio_ai,
                                   hist_wr=hist_wr,hist_signals=p_signals)
        if ai_result and ai_result["trade"]==False:
            stage = ai_result.get("stage","")
            if stage == "MID":
                # User-requested carve-out: STAGE:MID means the AI is
                # genuinely uncertain (still developing, not clearly bad
                # like a LATE/exhausted move) — send it anyway rather than
                # veto outright, with the AI's real verdict/confidence/
                # reasoning shown in the message so the user can make the
                # final call themselves. STAGE:LATE keeps its existing
                # retest-logging behavior below, unchanged — this carve-out
                # is deliberately scoped to MID only, not a blanket
                # override of AI rejections.
                logger.info(f"{coin} AI said TRADE:NO but STAGE:MID — sending anyway per user preference, AI notes will be shown")
            else:
                logger.info(f"{coin} rejected by AI — {ai_result['verdict']}/{ai_result['confidence']}/STAGE:{stage}")
                # Cooldown fix: previously a rejected signal set NO cooldown
                # at all (the cooldown is only set later, after a successful
                # send) — meaning the same coin was immediately eligible to
                # be re-scanned and re-flagged on the very next cycle
                # (SCAN_INTERVAL=90s), producing the exact "same signal every
                # ~2 minutes" pattern reported. A shorter cooldown than a
                # normal successful signal's ETA-based one (which can be
                # hours) — 20 minutes — since an AI rejection isn't the same
                # as a completed trade, conditions can genuinely change
                # faster, but it shouldn't re-fire every single cycle either.
                coin_cooldowns[coin]=get_ist_datetime()+timedelta(minutes=20)
                return False
        if ai_result and ai_result.get("stage")=="LATE":
            logger.info(f"{coin} AI flagged stage LATE — logging as retest candidate instead of chasing")
            highs_r=[float(k[2]) for k in klines_15m]; lows_r=[float(k[3]) for k in klines_15m]
            log_retest_candidate(coin,setup["symbol"],setup["direction"],closes,highs_r,lows_r,setup["pattern"])
            coin_cooldowns[coin]=get_ist_datetime()+timedelta(minutes=20)
            return False
    else:
        logger.info(f"{coin} grade is {grade} ({pts}pts, not A/A+) — executing on pure code, no AI call")

    price_range=(max(closes[-10:])-min(closes[-10:]))/10
    eta=int(abs(tp-entry)/(price_range if price_range>0 else 0.001)*15)
    eta=max(30,min(eta,1440)); setup["eta_minutes"]=eta
    expiry_minutes=INSTANT_EXPIRY_MINUTES if is_instant else SIGNAL_EXPIRY_MINUTES
    expiry_time=get_ist_datetime()+timedelta(minutes=expiry_minutes)
    expiry_str=expiry_time.strftime("%I:%M %p IST")
    mom=(closes[-1]-closes[-3])/closes[-3]*100
    rsi_val=calculate_rsi(closes)
    # grade, pts, breakdown already computed above (before leverage)
    pos_size=get_position_size_pct(grade)
    sl_pct=abs(entry-sl)/entry*100; tp_pct=abs(tp-entry)/entry*100
    rr_ratio=tp_pct/sl_pct if sl_pct>0 else 0
    tf_map={3:"4h + 1h  ✅✅",2:"4h Only  ✅",1:"1h Only  ⚡",0:"Counter  ⚠️"}
    tf_label=tf_map.get(tf_score,"N/A")
    cond_em={"bull":"Bullish 📈","bear":"Bearish 📉","sideways":"Sideways ➡️"}.get(market_condition,"")
    if is_instant: sig_type="⚡ INSTANT SIGNAL"
    elif is_river: sig_type="🌊 LAB SIGNAL"
    else:          sig_type="🔥 VERIFIED SETUP"
    dir_arrow="🟢 LONG  ▲" if setup["direction"]=="BUY" else "🔴 SHORT ▼"
    grade_em="🏆" if "A+" in grade else "🍀" if " A" in grade else "🥈" if "B" in grade else "🥉"
    cond_icon="📈" if market_condition=="bull" else "📉" if market_condition=="bear" else "➡️"

    # ── Score bar ──
    filled=min(int(setup["setup_score"]/10),10)
    score_bar="█"*filled+"░"*(10-filled)

    # ── Grade bar ──
    max_pts=22
    grade_filled=min(int(pts/max_pts*10),10)
    grade_bar="█"*grade_filled+"░"*(10-grade_filled)

    msg  = f"{'⚡' if is_instant else '🔥'} <b>{sig_type}</b>\n"
    msg += f"┌─────────────────────────────────┐\n"
    msg += f"│  ⚙️  TRADING SIGNAL MASTER v32G  │\n"
    msg += f"└─────────────────────────────────┘\n\n"
    msg += f"  🪙 <b>{coin}</b>  {dir_arrow}  🔧 <b>{lev}x Leverage</b>\n"
    msg += f"  {grade_em} <b>{grade}</b>  •  {pts}/{max_pts} pts\n"
    msg += f"  [{grade_bar}]\n"
    msg += f"  📊 Setup Score: <b>{setup['setup_score']:.0f}/100</b>  [{score_bar}]\n"
    msg += f"  {cond_icon} Market: <b>{cond_em}</b>\n\n"

    msg += f"  ┌── TRADE LEVELS ─────────────┐\n"
    msg += f"  │  💰 Entry      <code>{format_price(entry)}</code>\n"
    msg += f"  │  🎯 Target     <code>{format_price(tp)}</code>  <i>+{tp_pct:.2f}%</i>\n"
    msg += f"  │  🛑 Stop       <code>{format_price(sl)}</code>  <i>-{sl_pct:.2f}%</i>\n"
    res_dist=abs(res-entry)/entry*100; sup_dist=abs(entry-sup)/entry*100

    def _break_prob(dist_pct, favourable_dir):
        """Heuristic probability that price breaks through this level."""
        # Closer level = easier to test/break (inverse distance factor)
        dist_score = max(0, 50 - dist_pct*8)
        # Momentum aligned with breaking direction adds probability
        mom_score = mom * 3 if favourable_dir else -mom * 3
        # ADX strong trend = more likely to break levels
        adx_score = (adx_val - 20) * 0.6
        # Volume confirmation adds push
        vol_score = 8 if vol_ok else -4
        # RSI room to move
        if favourable_dir:  # breaking up (resistance)
            rsi_score = (rsi_val - 50) * 0.4
        else:               # breaking down (support)
            rsi_score = (50 - rsi_val) * 0.4
        prob = 35 + dist_score*0.4 + mom_score + adx_score + vol_score + rsi_score
        return max(5, min(95, prob))

    res_break_pct = _break_prob(res_dist, favourable_dir=True)   # breaking resistance = upward
    sup_break_pct = _break_prob(sup_dist, favourable_dir=False)  # breaking support = downward
    msg += f"  │  🚧 Resistance <code>{format_price(res)}</code>  <i>{res_dist:.2f}% away</i>  •  Break: <b>{res_break_pct:.0f}%</b>\n"
    msg += f"  │  🛡️ Support    <code>{format_price(sup)}</code>  <i>{sup_dist:.2f}% away</i>  •  Break: <b>{sup_break_pct:.0f}%</b>\n"
    msg += f"  └─────────────────────────────┘\n\n"

    msg += f"  📈 Max Profit : <b>+{profit_target:.1f}%</b>\n"
    msg += f"  ⚖️  Risk/Reward: <b>1 : {rr_ratio:.1f}</b>\n"
    msg += f"  💼 Position   : <b>{pos_size:.0f}% of capital</b>\n\n"

    msg += f"  ┌── ALIGNMENT SCORECARD ──────┐\n"
    for name,p in breakdown:
        bar="●" if p>0 else "○"
        pts_txt=f"+{p}pt{'s' if p!=1 else ''}" if p>0 else "  —  "
        msg+=f"  │  {bar} {name:<22} {pts_txt}\n"
    msg += f"  │                              \n"
    msg += f"  │  Total: <b>{pts} / {max_pts} points</b>\n"
    msg += f"  └─────────────────────────────┘\n\n"

    msg += f"  ┌── CONFIRMATIONS ────────────┐\n"
    msg += f"  │  📡 TF   : {tf_label}\n"
    st_icon="✅✅" if st_ok else "⚠️"
    msg += f"  │  🌀 ST   : {st_icon}  VWAP: {'✅' if vwap_ok else '⚠️'}\n"
    # OI/whale removed — both were boolean-only with no visible underlying
    # number, per explicit request ("we're not getting the data from
    # anywhere for this"). Replaced with the real volume ratio (same
    # value now feeding get_signal_grade's tiered volume scoring above).
    vol_icon="✅" if vol_ratio>=1.5 else "⚠️" if vol_ratio>=1.2 else "➖"
    msg += f"  │  📊 Vol  : {vol_icon} {vol_ratio:.2f}x avg\n"
    msg += f"  │  📌 Pat  : {setup['pattern']}\n"
    msg += f"  │  📊 RSI  : {rsi_val:.1f}   ADX: {adx_val:.1f}   Mom: {mom:+.2f}%\n"
    if zone_ok: msg += f"  │  📍 Zone : ✅ {'Demand' if setup['direction']=='BUY' else 'Supply'}\n"
    if div=="BULLISH_DIV":   msg += f"  │  🔀 Div  : 🟢 Bullish RSI Divergence\n"
    elif div=="BEARISH_DIV": msg += f"  │  🔀 Div  : 🔴 Bearish RSI Divergence\n"
    # Order book removed (was Audit Fix #2) — thin/frequently unavailable
    # data. Replaced with real BTC 1h trend alignment (Point 3).
    btc_em = "👑" if btc_aligned else "➖"
    btc_trend_label = "Bullish" if btc_1h_trend==1 else "Bearish" if btc_1h_trend==-1 else "Neutral"
    msg += f"  │  {btc_em} BTC   : {'Aligned' if btc_aligned else 'Not aligned'} ({btc_trend_label} 1h)\n"
    # Market structure (Audit Fix #7)
    ms_bias_em = "📈" if ms["bias"]=="bullish" else "📉" if ms["bias"]=="bearish" else "➡️"
    hh_str = "HH✅" if ms.get("hh") else "HH❌"
    hl_str = "HL✅" if ms.get("hl") else "HL❌"
    lh_str = "LH✅" if ms.get("lh") else "LH❌"
    ll_str = "LL✅" if ms.get("ll") else "LL❌"
    if setup["direction"] == "BUY":
        struct_str = f"{hh_str} {hl_str}"
    else:
        struct_str = f"{lh_str} {ll_str}"
    bos_str = "  🔥BOS" if ms["bos"] else ""
    msg += f"  │  🏗️ MS   : {ms_bias_em} {struct_str}{bos_str}\n"
    msg += f"  └─────────────────────────────┘\n\n"

    # Proportional milestone plan — scales with the ACTUAL profit target (not fixed 35%)
    m1_pnl = profit_target*0.30; m2_pnl = profit_target*0.60; m3_pnl = profit_target*0.85
    def _price_at_pnl(target_pnl):
        move = entry * (target_pnl/100) / lev
        return entry+move if setup["direction"]=="BUY" else entry-move
    def _sl_lock_price(target_pnl, lock_ratio):
        # SL locks in lock_ratio of the gain reached at target_pnl
        gain_price = abs(_price_at_pnl(target_pnl) - entry)
        locked = gain_price * lock_ratio
        return entry+locked if setup["direction"]=="BUY" else entry-locked
    ms1=format_price(_sl_lock_price(m1_pnl, 0.0))   # at 30% of target → SL to breakeven
    ms2=format_price(_sl_lock_price(m2_pnl, 0.5))   # at 60% of target → lock half the gain so far
    ms3=format_price(_sl_lock_price(m3_pnl, 0.8))   # at 85% of target → lock 80% of gain
    msg += f"  ┌── MILESTONE PLAN ───────────┐\n"
    msg += f"  │  🎯 +{m1_pnl:.1f}%  → SL to <code>{ms1}</code>  <i>(breakeven)</i>\n"
    msg += f"  │  🔥 +{m2_pnl:.1f}%  → SL to <code>{ms2}</code>  <i>(lock 50%)</i>\n"
    msg += f"  │  🚀 +{m3_pnl:.1f}%  → SL to <code>{ms3}</code>  <i>(lock 80%)</i>\n"
    msg += f"  │  🏁 Final Target: +{profit_target:.1f}%\n"
    msg += f"  └─────────────────────────────┘\n\n"

    # AI Analysis in message
    if ai_result:
        v_em="✅" if ai_result["verdict"]=="CLEAN" else "⚠️"
        c_em="🟢" if ai_result["confidence"]=="HIGH" else "🟡" if ai_result["confidence"]=="MEDIUM" else "🔴"
        stage_em={"EARLY":"🌱","MID":"🔥","LATE":"⏰"}.get(ai_result.get("stage","UNKNOWN"),"❔")
        msg+=f"\n  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
        msg+=f"  🧠 <b>AI ANALYSIS</b>\n"
        if ai_result.get("trade")==False:
            msg+=f"  ⚠️ <b>AI said TRADE:NO but STAGE:MID — sent for your review, not an AI approval</b>\n"
        msg+=f"  {v_em} Pattern: <b>{ai_result['verdict']}</b>  {c_em} Confidence: <b>{ai_result['confidence']}</b>\n"
        if ai_result.get("stage") and ai_result["stage"]!="UNKNOWN":
            msg+=f"  {stage_em} Stage: <b>{ai_result['stage']}</b>\n"
        if ai_result.get("eta_read"):
            msg+=f"  ⏱️ {ai_result['eta_read']}\n"
        if ai_result['reasoning']:
            msg+=f"  💡 {ai_result['reasoning']}\n"
        if penalty_notes:
            msg+=f"  📉 Score adj: {', '.join(penalty_notes)}\n"
    msg += f"  ⏳ ETA: ~{eta} min  •  ⏰ Exp: {expiry_str}\n"
    msg += f"  🕐 {get_ist_time()}"
    setup.update({"entry":entry,"sl":sl,"tp":tp,"timestamp":get_ist_datetime(),
                  "expires_at":expiry_time,"reversal_alerted":False,"breakeven_sent":False,
                  "partial_tp_taken":False,"milestones_sent":[],"tf_score":tf_score,
                  "market_condition":market_condition,"eta_minutes":eta,
                  "profit_target":profit_target})
    pending_signals[coin]=setup
    reply_markup={"inline_keyboard":[[
        {"text":"✅ Activate Trade","callback_data":f"ACTIVATE_{coin}"},
        {"text":"❌ Ignore","callback_data":f"IGNORE_{coin}"}
    ]]}
    result=send_telegram(msg,reply_markup=reply_markup)
    if result:
        sent_coins.append(coin)
        coin_cooldowns[coin]=get_ist_datetime()+timedelta(minutes=eta)
        save_pending_signals()
        logger.info(f"Signal sent: {coin}|{setup['direction']}|Score:{setup['setup_score']}|ETA:{eta}m")
        return True
    else:
        if coin in pending_signals: del pending_signals[coin]
        return False

def check_active_trades():
    for coin,trade in list(active_trades.items()):
        price=get_price(trade["symbol"])
        if not price: continue
        if trade["direction"]=="BUY":
            pnl=((price-trade["entry"])/trade["entry"])*100*trade["leverage"]
        else:
            pnl=((trade["entry"]-price)/trade["entry"])*100*trade["leverage"]
        update_trailing_sl(coin,trade,price)
        check_profit_milestones(coin,trade,price,pnl)
        if not trade.get("reversal_alerted",False):
            klines=get_klines(trade["symbol"],"15m",20)
            if klines:
                closes=[float(x[4]) for x in klines]; ema20=calculate_ema(closes,20)
                if ema20:
                    rev=((trade["direction"]=="BUY" and price<ema20*0.995) or
                         (trade["direction"]=="SELL" and price>ema20*1.005))
                    if rev:
                        send_telegram(f"⚠️ <b>{BOT_HEADER}</b>\nReversal alert: {coin}\nPrice broke EMA20")
                        active_trades[coin]["reversal_alerted"]=True; save_active_trades()
        hit=None
        if trade["direction"]=="BUY":
            if price>=trade["tp"]:   hit="WIN"
            elif price<=trade["sl"]: hit="LOSS"
        else:
            if price<=trade["tp"]:   hit="WIN"
            elif price>=trade["sl"]: hit="LOSS"
        if hit:
            with trade_lock:
                primary=trade["pattern"].split(" + ")[0]
                if primary in pattern_stats:
                    pattern_stats[primary]["signals"]+=1
                    pattern_stats[primary]["total_pnl"]+=pnl
                    pattern_stats[primary]["wins" if hit=="WIN" else "losses"]+=1
                increment_daily_losses(pnl)
                if hit=="LOSS":
                    coin_cooldowns[coin]=get_ist_datetime()+timedelta(hours=4)
                duration=""
                if trade.get("timestamp"):
                    mins=int((get_ist_datetime()-trade["timestamp"]).total_seconds()/60)
                    duration=f"{mins} mins"
                mc=trade.get("market_condition","bull")
                trade_journal.append({"date":str(datetime.now(IST).date()),"coin":coin,
                    "direction":trade["direction"],"pattern":primary,
                    "entry":trade["entry"],"exit":price,"pnl":pnl,"result":hit,
                    "duration":duration,"tf_score":trade.get("tf_score",0),"market_condition":mc})
                save_journal(); learn_from_trade(coin,primary,hit,pnl,mc,trade.get("tf_score",0))
            em="✅" if hit=="WIN" else "🛑"
            send_telegram(
                f"{em} <b>TRADE {'WON' if hit=='WIN' else 'CLOSED'} — {coin}</b>\n"
                f"⚙️ <b>TRADING SIGNAL MASTER v32G</b>\n"
                f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
                f"🪙 <b>{coin}</b>  {'🟢' if trade['direction']=='BUY' else '🔴'} {trade['direction']}\n"
                f"📌 Pattern: {primary}\n\n"
                f"💰 Entry: <code>{format_price(trade['entry'])}</code>\n"
                f"📍 Exit:  <code>{format_price(price)}</code>\n"
                f"⏱️ Duration: {duration}\n\n"
                f"📈 <b>PnL: {fmt_pnl(pnl)}</b>\n"
                f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
                f"🕐 {get_ist_time()}"
            )
            del active_trades[coin]
            save_active_trades(); save_trade_history()
            cloud_save_journal(); cloud_save_pattern_stats(); cloud_save_active_trades()

def poll_telegram():
    global last_update_id
    while True:
        try:
            params={}
            if last_update_id is not None: params["offset"]=last_update_id+1
            res=requests.get(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/getUpdates",
                             params=params,timeout=15)
            if res.status_code!=200: time.sleep(2); continue
            for update in res.json().get("result",[]):
                last_update_id=update["update_id"]
                if "callback_query" in update:
                    cb=update["callback_query"]
                    data=cb.get("data","")
                    cbid=cb.get("id","")
                    answer_callback(cbid,"Processing...")
                    logger.info(f"Callback received: data={data} pending={list(pending_signals.keys())}")
                    if data and "_" in data:
                        action=data.split("_",1)[0]
                        coin=data.split("_",1)[1]
                        if action=="ACTIVATE":
                            if coin in pending_signals:
                                lp=get_price(pending_signals[coin].get("symbol",coin+"USDT"))
                                if lp and lp>0: pending_signals[coin]["entry"]=lp
                                pending_signals[coin]["breakeven_sent"]=False
                                pending_signals[coin]["partial_tp_taken"]=False
                                pending_signals[coin]["reversal_alerted"]=False
                                pending_signals[coin]["milestones_sent"]=[]
                                pending_signals[coin]["timestamp"]=get_ist_datetime()
                                pending_signals[coin]["expires_at"]=None
                                with trade_lock:
                                    active_trades[coin]=pending_signals[coin]
                                save_active_trades()
                                t=active_trades[coin]
                                ep=t.get("entry",0); sl_p=t.get("sl",0); tp_p=t.get("tp",0)
                                lev=t.get("leverage",5); dirn=t.get("direction","?"); pat=t.get("pattern","?")
                                sl_pct=abs(ep-sl_p)/ep*100 if ep>0 else 0
                                tp_pct=abs(tp_p-ep)/ep*100 if ep>0 else 0
                                rr=round(tp_pct/sl_pct,1) if sl_pct>0 else 0
                                if dirn=="BUY":
                                    sl_10=format_price(ep); sl_20=format_price(ep+(tp_p-ep)*0.5); sl_35=format_price(ep+(tp_p-ep)*0.75)
                                else:
                                    sl_10=format_price(ep); sl_20=format_price(ep-(ep-tp_p)*0.5); sl_35=format_price(ep-(ep-tp_p)*0.75)
                                dir_em2 = "🟢 LONG" if dirn=="BUY" else "🔴 SHORT"
                                send_telegram(
                                    f"🚀 <b>TRADE ACTIVATED</b>\n"
                                    f"⚙️ <b>TRADING SIGNAL MASTER v32G</b>\n"
                                    f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
                                    f"🪙 <b>{coin}</b>  {dir_em2}  🔧 <b>{lev}x</b>\n"
                                    f"⚖️ Risk/Reward: <b>1:{rr}</b>\n\n"
                                    f"💰 <b>Entry</b>    <code>{format_price(ep)}</code>\n"
                                    f"🎯 <b>Target</b>   <code>{format_price(tp_p)}</code>  (+{tp_pct:.1f}%)\n"
                                    f"🛑 <b>Stop</b>     <code>{format_price(sl_p)}</code>  (-{sl_pct:.1f}%)\n\n"
                                    f"📌 Pattern: {pat}\n"
                                    f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
                                    f"📋 <b>Milestone Plan:</b>\n"
                                    f"  🎯 +10% → Move SL to <code>{sl_10}</code>\n"
                                    f"  🎯 +20% → Move SL to <code>{sl_20}</code>\n"
                                    f"  🚀 +35% → Move SL to <code>{sl_35}</code>\n"
                                    f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
                                    f"✏️ Set your trade on CoinDCX now!\n"
                                    f"🕐 {get_ist_time()}"
                                )
                                del pending_signals[coin]
                                save_pending_signals()
                                logger.info(f"ACTIVATED: {coin}|{dirn}|Entry:{ep}|{lev}x")
                            else:
                                send_telegram(f"⏰ <b>{BOT_HEADER}</b>\nSignal for {coin} expired.\nWait for next signal.")
                                logger.warning(f"ACTIVATE failed: {coin} not in pending={list(pending_signals.keys())}")
                        elif action=="IGNORE":
                            if coin in pending_signals: del pending_signals[coin]
                            save_pending_signals()
                            send_telegram(f"❌ <b>{BOT_HEADER}</b>\n{coin} signal ignored.")
                elif "message" in update:
                    txt=update["message"].get("text","").strip().lower()
                    txt_slash=txt  # for slash commands (already lowercase)
                    txt_clean = txt.replace('\ufe0f','').replace('\ufe0e','').strip()
                    if   txt_slash=="/trades":   safe_send(get_active_trades_text,"📊 Trades")
                    elif txt_slash=="/pending":
                        if pending_signals:
                            msg=f"{_H('PENDING SIGNALS','⏳')}\n\n"
                            for c,s in pending_signals.items():
                                exp=s.get("expires_at"); exp_str=exp.strftime("%I:%M %p IST") if isinstance(exp,datetime) else "N/A"
                                dirn_em="🟢 LONG" if s.get("direction")=="BUY" else "🔴 SHORT"
                                msg+=(f"  🪙 <b>{c}</b>  {dirn_em}\n"
                                      f"  ◆ {s.get('pattern','?')}\n"
                                      f"  Score: {s.get('setup_score',0):.0f}  ⏰ {exp_str}\n\n")
                            msg+=f"  🕐 {get_ist_time()}"
                            send_telegram(msg)
                        else: send_telegram(f"{_H('PENDING SIGNALS','⏳')}\n\n  ⚪ No pending signals.\n\n  🕐 {get_ist_time()}")
                    elif txt_slash=="/retests":   safe_send(get_retest_watchlist_text,"👀 Retests")
                    elif txt_slash=="/stats":    safe_send(get_pattern_stats_text,"📈 Stats")
                    elif txt_slash=="/summary":  safe_send(get_10day_summary_text,"📅 Summary")
                    elif txt_slash=="/streak":   safe_send(get_streak_text,"🔥 Streak")
                    elif txt_slash=="/best":     safe_send(get_best_text,"🏆 Best")
                    elif txt_slash=="/risk":     safe_send(get_risk_text,"🛡️ Risk")
                    elif txt_slash=="/learn":    safe_send(get_learning_text,"🧠 Learn")
                    elif txt_slash=="/journal":  safe_send(get_journal_text,"📓 Journal")
                    elif txt_slash=="/patterns": safe_send(get_patterns_ranked_text,"🌀 Patterns")
                    elif txt_slash=="/news":
                        send_telegram(f"⚙️ Fetching latest news...")
                        safe_send(get_crypto_news,"📰 News")
                    elif txt_slash=="/gems":    safe_send(cmd_hidden_gems,"💎 Hidden Gems")
                    elif txt_slash=="/analyst":
                        send_telegram("🧠 AI Analyst reviewing your trades...", parse_mode="")
                        safe_send(ai_analyst_review,"🧠 AI Analyst")
                    elif txt_slash in ("/counsel","/regime"):
                        pass  # handled below
                    elif txt_slash=="/market":   safe_send(cmd_market,"🌍 Market")
                    elif txt_slash=="/cb":
                        cb_on=check_circuit_breaker()
                        send_telegram(
                            f"{_H('CIRCUIT BREAKER','⚡')}\n\n"
                            f"  Status   : {'🔴 ACTIVE — paused' if cb_on else '🟢 OK — scanning'}\n"
                            f"  Losses   : {daily_losses}/{MAX_DAILY_LOSSES}\n"
                            f"  Resets   : Midnight IST\n\n"
                            f"  🕐 {get_ist_time()}"
                        )
                    elif txt_slash.startswith("/trend"):
                        parts=txt.split(); coin2=parts[1].upper() if len(parts)>1 else "BTC"
                        safe_send(lambda: cmd_trend(coin2),"📉 Trend")
                    elif txt_slash.startswith("/compare"):
                        parts=txt.split(maxsplit=1); coins_str=parts[1].upper() if len(parts)>1 else "BTC ETH SOL"
                        safe_send(lambda: cmd_compare(coins_str),"🆚 Compare")
                    elif txt_slash=="/scan":
                        btc_p=get_price("BTCUSDT"); btc_k=get_klines("BTCUSDT","1h",50)
                        bt_e50=calculate_ema([float(x[4]) for x in btc_k],50) if btc_k else None
                        bt=1 if (btc_p and bt_e50 and btc_p>bt_e50) else -1
                        fng2=get_fear_greed_index(); mc2=detect_market_condition(btc_p,btc_k) if btc_p and btc_k else "sideways"
                        send_telegram(cmd_scan_manual(bt,fng2,mc2))
                    elif txt_slash.startswith("/alert "):
                        parts=txt.split()
                        if len(parts)>=4:
                            try:
                                sym=parts[1].upper(); target=float(parts[2]); direction=parts[3].lower()
                                price_alerts[sym]={"price":target,"direction":direction}; save_alerts()
                                send_telegram(f"🔔 Alert set: {sym} {direction} {format_price(target)}")
                            except Exception: send_telegram("Usage: /alert BTC 95000 above")
                        else: send_telegram("Usage: /alert BTC 95000 above")
                    elif txt_slash=="/alerts":
                        if price_alerts:
                            msg=f"<b>{BOT_HEADER} Alerts</b>\n{S()}\n\n"
                            for sym,a in price_alerts.items(): msg+=f"{sym}: {a['direction']} {format_price(a['price'])}\n"
                            send_telegram(msg)
                        else: send_telegram(f"<b>{BOT_HEADER}</b>\nNo alerts set.")
                    elif txt_slash.startswith("/addmacroevent"):
                        # Point 2: maintainable macro calendar. Usage:
                        # /addmacroevent 2026-08-01 18:00 FOMC rate decision
                        # Date+time must match is_macro_event_window's exact
                        # expected format "%Y-%m-%d %H:%M" (IST) or it will
                        # silently be skipped there (that function already
                        # has a try/except continue on bad entries) — so we
                        # validate the format HERE before accepting it, to
                        # catch a typo immediately instead of it silently
                        # never firing weeks later.
                        raw = update["message"].get("text","").strip()
                        body = raw[len("/addmacroevent"):].strip()
                        parts = body.split(maxsplit=2)
                        if len(parts) < 2:
                            send_telegram("Usage: /addmacroevent 2026-08-01 18:00 FOMC rate decision")
                        else:
                            date_part, time_part = parts[0], parts[1]
                            label = parts[2] if len(parts) > 2 else ""
                            ev_str = f"{date_part} {time_part}"
                            # BUG FIX: this codebase uses zoneinfo (not pytz) for IST
                            # — zoneinfo.ZoneInfo has no .localize() method, so the
                            # original IST.localize(...) call here raised
                            # AttributeError, which `except ValueError` below does
                            # NOT catch. Confirmed directly: the exception would
                            # propagate up to poll_telegram's outer handler (logged,
                            # not crashing the bot), but neither send_telegram
                            # branch here would ever run — meaning /addmacroevent
                            # would silently do nothing, no reply at all, the first
                            # time anyone actually used it. Fixed alongside the
                            # matching bug in is_macro_event_window() — same
                            # `.replace(tzinfo=IST)` pattern, and broadened to
                            # `except Exception` since ValueError was never the
                            # right exception type to catch here in the first place.
                            try:
                                datetime.strptime(ev_str, "%Y-%m-%d %H:%M").replace(tzinfo=IST)
                                SCHEDULED_MACRO_EVENTS.append(ev_str + (f"  # {label}" if label else ""))
                                save_macro_events()
                                send_telegram(f"📅 Macro event added: {ev_str} IST" + (f" — {label}" if label else "") +
                                             f"\nBot will pause new signals ±{MACRO_EVENT_PAUSE_MIN_BEFORE}min around this time.")
                            except Exception:
                                send_telegram("⚠️ Invalid format. Use: /addmacroevent 2026-08-01 18:00 FOMC rate decision\n(date as YYYY-MM-DD, time as 24h HH:MM, IST)")
                    elif txt_slash=="/macroevents":
                        if SCHEDULED_MACRO_EVENTS:
                            msg=f"<b>{BOT_HEADER} Scheduled Macro Events</b>\n{S()}\n\n"
                            for i,ev in enumerate(SCHEDULED_MACRO_EVENTS,1): msg+=f"{i}. {ev}\n"
                            msg+=f"\nUse /clearmacroevents to remove all."
                            send_telegram(msg)
                        else:
                            send_telegram(f"<b>{BOT_HEADER}</b>\nNo scheduled macro events. Add one with:\n/addmacroevent 2026-08-01 18:00 FOMC rate decision")
                    elif txt_slash=="/clearmacroevents":
                        SCHEDULED_MACRO_EVENTS.clear()
                        save_macro_events()
                        send_telegram("🗑️ All scheduled macro events cleared.")
                    elif txt_slash.startswith("/backtest"):
                        parts=txt.split(); bc=(parts[1].upper() if len(parts)>1 else "BTC")+"USDT"
                        send_telegram(f"Running backtest for {bc}...")
                        send_telegram(run_backtest(bc))
                    elif txt_slash in ("/start","/help","/menu"):
                        menu_kb={
                            "keyboard":[
                                [{"text":"📊 Trades"},   {"text":"⏳ Pending"},   {"text":"📈 Stats"}],
                                [{"text":"📅 Summary"},  {"text":"🔥 Streak"},    {"text":"🏆 Best"}],
                                [{"text":"🛡 Risk"},     {"text":"🧠 Learn"},     {"text":"📓 Journal"}],
                                [{"text":"🌀 Patterns"}, {"text":"📰 News"},      {"text":"🌍 Market"}],
                                [{"text":"🔍 Scan"},     {"text":"⚡ CB Status"}, {"text":"📡 Status"}],
                                [{"text":"🔔 Alerts"},   {"text":"📉 Trend BTC"}, {"text":"💎 Hidden Gems"}],
                                [{"text":"🧠 AI Analyst"},{"text":"🔮 Counsel"},  {"text":"🌐 Regime"}],
                            ],
                            "resize_keyboard":True,
                            "persistent":True
                        }
                        send_telegram(
                            f"{_H('TRADING SIGNAL MASTER v32G','⚙️')}\n\n"
                            f"  Tap a button or type a command:\n\n"
                            f"  📊 /trades    — Active trades\n"
                            f"  ⏳ /pending   — Pending signals\n"
                            f"  👀 /retests   — Coins watched for pullback\n"
                            f"  📈 /stats     — Pattern stats\n"
                            f"  🧠 /analyst   — AI reviews open trades\n"
                            f"  🔮 /counsel   — AI suggestion per trade\n"
                            f"  📅 /summary   — 10-day summary\n"
                            f"  🔥 /streak    — Win/loss streak\n"
                            f"  🏆 /best      — Top performers\n"
                            f"  🛡 /risk      — Risk exposure\n"
                            f"  🧠 /learn     — Bot insights\n"
                            f"  📓 /journal   — Trade journal\n"
                            f"  🌀 /patterns  — Patterns ranked\n"
                            f"  📰 /news      — Crypto news\n"
                            f"  🌍 /market    — Market overview\n"
                            f"  🔍 /scan      — Manual scan\n"
                            f"  ⚡ /cb        — Circuit breaker\n"
                            f"  📡 /status    — Live bot status\n"
                            f"  🔔 /alerts    — Price alerts\n"
                            f"  📉 /trend BTC — Trend analysis\n"
                            f"  🆚 /compare BTC ETH — Compare\n"
                            f"  💎 /gems      — Hidden gems scan\n"
                            f"  🔬 /backtest BTC — Backtest\n\n"
                            f"  🕐 {get_ist_time()}",
                            reply_markup=menu_kb
                        )
                    # ── /status + 📡 Status button ──
                    elif txt_slash in ("/status","📡 status"):
                        # handled by txt_clean block below — trigger it
                        pass
                    # ── Reply keyboard button tap handlers ──
                    elif txt_clean=="📊 trades":   safe_send(get_active_trades_text,"📊 Trades")
                    elif txt_clean=="⏳ pending":
                        if pending_signals:
                            msg=f"{_H('PENDING SIGNALS','⏳')}\n\n"
                            for c,s in pending_signals.items():
                                exp=s.get("expires_at")
                                exp_str=exp.strftime("%I:%M %p IST") if isinstance(exp,datetime) else "N/A"
                                dirn_em="🟢 LONG" if s.get("direction")=="BUY" else "🔴 SHORT"
                                msg+=(f"  🪙 <b>{c}</b>  {dirn_em}\n"
                                      f"  ◆ {s.get('pattern','?')}\n"
                                      f"  Score: {s.get('setup_score',0):.0f}  ⏰ {exp_str}\n\n")
                            msg+=f"  🕐 {get_ist_time()}"
                            send_telegram(msg)
                        else:
                            send_telegram(f"{_H('PENDING SIGNALS','⏳')}\n\n  ⚪ No pending signals right now.\n\n  🕐 {get_ist_time()}")
                    elif txt_clean=="📈 stats":    safe_send(get_pattern_stats_text,"📈 Stats")
                    elif txt_clean=="📅 summary":  safe_send(get_10day_summary_text,"📅 Summary")
                    elif txt_clean=="🔥 streak":   safe_send(get_streak_text,"🔥 Streak")
                    elif txt_clean=="🏆 best":     safe_send(get_best_text,"🏆 Best")
                    elif txt_clean in ("🛡️ risk","🛡 risk"):  safe_send(get_risk_text,"🛡 Risk")
                    elif txt_clean=="🧠 learn":    safe_send(get_learning_text,"🧠 Learn")
                    elif txt_clean=="📓 journal":  safe_send(get_journal_text,"📓 Journal")
                    elif txt_clean=="🌀 patterns": safe_send(get_patterns_ranked_text,"🌀 Patterns")
                    elif txt_clean=="📰 news":
                        send_telegram("⚙️ Fetching latest news...")
                        safe_send(get_crypto_news,"📰 News")
                    elif txt_clean=="🌍 market":   safe_send(cmd_market,"🌍 Market")
                    elif txt_clean=="🔍 scan":
                        btc_p2=get_price("BTCUSDT"); btc_k2=get_klines("BTCUSDT","1h",50)
                        bt_e2=calculate_ema([float(x[4]) for x in btc_k2],50) if btc_k2 else None
                        bt2=1 if (btc_p2 and bt_e2 and btc_p2>bt_e2) else -1
                        fg2=get_fear_greed_index()
                        mc2=detect_market_condition(btc_p2,btc_k2) if btc_p2 and btc_k2 else "sideways"
                        safe_send(lambda: cmd_scan_manual(bt2,fg2,mc2),"🔍 Scan")
                    elif txt_clean in ("⚡ cb status","⚡ cb"):
                        cb_on=check_circuit_breaker()
                        send_telegram(
                            f"{_H('CIRCUIT BREAKER','⚡')}\n\n"
                            f"  Status   : {'🔴 ACTIVE — scanning paused' if cb_on else '🟢 OK — scanning active'}\n"
                            f"  Losses   : {daily_losses}/{MAX_DAILY_LOSSES}\n"
                            f"  Resets   : Midnight IST\n\n"
                            f"  🕐 {get_ist_time()}"
                        )
                    elif txt_clean in ("📡 status","📡status"):
                        btc_p=get_price("BTCUSDT"); fng=get_fear_greed_index()
                        btc_k=get_klines("BTCUSDT","1h",50)
                        bt_e=calculate_ema([float(x[4]) for x in btc_k],50) if btc_k else None
                        bt=1 if (btc_p and bt_e and btc_p>bt_e) else -1
                        mc=detect_market_condition(btc_p,btc_k) if btc_p and btc_k else "unknown"
                        sess=is_good_trading_session(); sess_premium=is_good_trading_session("BTC"); cb=check_circuit_breaker()
                        btc_crash=is_btc_crashing()
                        send_telegram(
                            f"{_H('LIVE BOT STATUS','📡')}\n\n"
                            f"  {'✅' if sess else '🔴'} Session (regular): {'ACTIVE' if sess else 'DEAD (2-7AM IST)'}\n"
                            f"  {'✅' if sess_premium else '🔴'} Session (premium): {'ACTIVE 24/7' if sess_premium else 'DEAD'}\n"
                            f"  {'✅' if not cb else '🔴'} CB         : {'OK' if not cb else 'ACTIVE — paused'}\n"
                            f"  {'✅' if not btc_crash else '🔴'} BTC Crash  : {'OK' if not btc_crash else 'CRASHING'}\n"
                            f"  {'🟢' if bt==1 else '🔴'} BTC Trend  : {'BULLISH ▲' if bt==1 else 'BEARISH ▼'}\n"
                            f"  📊 Market   : {mc.upper()}\n"
                            f"  😰 F&G      : {fng}\n"
                            f"  📌 Trades   : {len(active_trades)}/{MAX_ACTIVE_TRADES}\n"
                            f"  ⏳ Pending  : {len(pending_signals)}\n"
                            f"  🔒 Cooldowns: {len(coin_cooldowns)} coins\n"
                            f"  📉 Losses   : {daily_losses}/{MAX_DAILY_LOSSES}\n"
                            f"  🎯 Min Score: {MIN_SETUP_SCORE}\n\n"
                            f"  {'🟢 Bot CAN send signals' if sess and not cb else '🔴 Bot BLOCKED'}\n\n"
                            f"  🕐 {get_ist_time()}"
                        )
                    elif txt_clean=="🔔 alerts":
                        if price_alerts:
                            msg=f"{_H('PRICE ALERTS','🔔')}\n\n"
                            for sym,a in price_alerts.items():
                                msg+=f"  🔔 <b>{sym}</b>  {a['direction'].upper()}  <code>{format_price(a['price'])}</code>\n"
                            msg+=f"\n  ➕ /alert BTC 95000 above\n  🕐 {get_ist_time()}"
                            send_telegram(msg)
                        else:
                            send_telegram(f"{_H('PRICE ALERTS','🔔')}\n\n  ⚪ No alerts set.\n\n  ➕ /alert BTC 95000 above\n  🕐 {get_ist_time()}")
                    elif txt_clean.startswith("📉 trend"):
                        parts=txt_clean.split(); coin_t=(parts[-1].upper() if len(parts)>1 and parts[-1].upper()!="TREND" else "BTC")+"USDT"
                        safe_send(lambda: cmd_trend(coin_t),"📉 Trend")
                    elif txt_clean.startswith("🔬 backtest"):
                        parts=txt_clean.split(); bc2=(parts[-1].upper() if len(parts)>1 and parts[-1].upper()!="BACKTEST" else "BTC")+"USDT"
                        send_telegram(f"🔬 Running backtest for <b>{bc2}</b>...")
                        safe_send(lambda: run_backtest(bc2),"🔬 Backtest")
                    elif txt_clean in ("💎 hidden gems","/gems"):
                        safe_send(cmd_hidden_gems,"💎 Hidden Gems")
                    elif txt_clean in ("🧠 ai analyst","/analyst"):
                        send_telegram("🧠 AI Analyst reviewing your trades...", parse_mode="")
                        safe_send(ai_analyst_review,"🧠 AI Analyst")
                    elif txt_clean in ("🔮 counsel","/counsel"):
                        if not active_trades:
                            send_telegram(_H("COUNSEL","🔮")+"\n\n  🌙 No open trades.\n\n  🕐 "+get_ist_time())
                        else:
                            lines=[_H("TRADE COUNSEL","🔮")+"\n"]
                            for coin,t in active_trades.items():
                                symbol=t.get("symbol",coin+"USDT"); price=get_price(symbol)
                                if not price: continue
                                direction=t.get("direction","BUY"); entry=t["entry"]; lev=t.get("leverage",1)
                                pnl=((price-entry)/entry)*100*lev if direction=="BUY" else ((entry-price)/entry)*100*lev
                                dist_tp=abs(t["tp"]-price)/price*100
                                em="🟢" if pnl>=0 else "🔴"
                                lines.append(f"  {em} <b>{coin}</b> {direction} PnL:{pnl:+.1f}% TP:{dist_tp:.1f}% away")
                            lines.append(f"\n  🕐 {get_ist_time()}")
                            send_telegram("\n".join(lines))
                    elif txt_clean in ("🌐 regime","/regime"):
                        btc_p=get_price("BTCUSDT"); btc_k=get_klines("BTCUSDT","1h",50)
                        adx=calculate_adx(btc_k) if btc_k else 0
                        fng=get_fear_greed_index()
                        mc=detect_market_condition(btc_p,btc_k) if btc_p and btc_k else "sideways"
                        em="📈" if mc=="bull" else "📉" if mc=="bear" else "➡️"
                        send_telegram(
                            _H("MARKET REGIME","🌐")+"\n\n"
                            f"  {em} Regime: <b>{mc.upper()}</b>\n"
                            f"  💪 ADX: {adx:.1f}\n"
                            f"  😰 F&G: {fng}\n"
                            f"  ₿ BTC: <code>${format_price(btc_p) if btc_p else 'N/A'}</code>\n\n"
                            f"  🕐 {get_ist_time()}"
                        )
        except requests.RequestException as e: logger.error(f"Poll network: {e}")
        except Exception as e:                 logger.error(f"Poll error: {e}",exc_info=True)
        time.sleep(2)

def send_hourly_report():
    r=f"<b>{BOT_HEADER} Hourly Report</b>\n{get_ist_time()}\n{S()}\n\n"
    r+=f"Active: {len(active_trades)} | Pending: {len(pending_signals)}\n"
    r+=f"Circuit Breaker: {'ACTIVE' if check_circuit_breaker() else 'OK'}\n\n"
    r+=get_pattern_stats_text()
    send_telegram(r)

def send_live_pnl_update():
    if not active_trades: return
    total_pnl=0.0; wins=losses=0
    msg=f"<b>{BOT_HEADER} Live PnL</b>\n{get_ist_time()}\n{S()}\n\n"
    for coin,t in active_trades.items():
        price=get_price(t["symbol"])
        if not price: continue
        pnl=(((price-t["entry"])/t["entry"])*100*t["leverage"] if t["direction"]=="BUY"
             else ((t["entry"]-price)/t["entry"])*100*t["leverage"])
        total_pnl+=pnl
        if pnl>=3: wins+=1
        elif pnl<=-3: losses+=1
        msg+=f"{coin} {t['direction']} | {fmt_pnl(pnl)}\n"
    total=wins+losses; wr=(wins/total*100) if total>0 else 0
    msg+=f"\n{S()}\nTotal: {fmt_pnl(total_pnl)} | WR: {wr:.1f}%"
    send_telegram(msg)


def generate_weekly_insight():
    today = datetime.now(IST).date()
    wt = [j for j in trade_journal
          if (today - datetime.strptime(j["date"], "%Y-%m-%d").date()).days < 7]
    if not wt: return "Not enough data for weekly insight yet."
    wins   = [t for t in wt if t["result"] == "WIN"]
    losses = [t for t in wt if t["result"] == "LOSS"]
    total  = len(wt)
    wr     = (len(wins) / total * 100) if total > 0 else 0
    day_wins = {}
    for t in wins:
        d = t["date"]; day_wins[d] = day_wins.get(d, 0) + 1
    best_day  = max(day_wins, key=day_wins.get) if day_wins else None
    wp        = [t["pattern"] for t in wins]
    lp        = [t["pattern"] for t in losses]
    best_pat  = Counter(wp).most_common(1)[0][0]  if wp  else None
    worst_pat = Counter(lp).most_common(1)[0][0]  if lp  else None
    sw_losses = sum(1 for t in losses if t.get("market_condition") == "sideways")
    msg  = f"AI Weekly Insight:\n"
    msg += f"{len(wins)}W / {len(losses)}L | WR: {wr:.1f}%\n"
    if best_day:  msg += f"Best day: {best_day}\n"
    if best_pat:  msg += f"Best pattern: {best_pat}\n"
    if worst_pat: msg += f"Most losses from: {worst_pat}\n"
    if sw_losses >= 2:
        msg += f"{sw_losses} losses in sideways — reduce size when BTC ranges\n"
    if wr >= 70:   msg += "Excellent week!"
    elif wr >= 50: msg += "Decent week. Stay disciplined."
    else:          msg += "Tough week. Review learning notes."
    return msg

def send_weekly_report():
    today=datetime.now(IST).date(); week=[today-timedelta(days=i) for i in range(6,-1,-1)]
    wins=losses=0; total_pnl=0.0
    msg=f"<b>{BOT_HEADER} Weekly Report</b>\n{today.strftime('%d %b %Y')}\n{S()}\n\n"
    for day in week:
        dt=[j for j in trade_journal if j.get("date")==str(day)]
        w=sum(1 for t in dt if t["result"]=="WIN"); l=sum(1 for t in dt if t["result"]=="LOSS")
        pnl=sum(t["pnl"] for t in dt); wins+=w; losses+=l; total_pnl+=pnl
        em="✅" if w>l else "❌" if l>w else "⚪"
        msg+=f"{em} {day.strftime('%a %d')}: {w}W/{l}L {fmt_pnl(pnl)}\n"
    total=wins+losses; wr=(wins/total*100) if total>0 else 0
    msg+=f"\n{S()}\nTotal: {wins}W/{losses}L | WR:{wr:.1f}% | {fmt_pnl(total_pnl)}"
    msg+=f"\n\n{generate_weekly_insight()}"
    send_telegram(msg)

def scan_river(now,market_condition):
    """
    NOTE: function/variable names (scan_river, last_river_time, RIVER_INTERVAL)
    kept as-is — only the actual coin/symbol scanned was retargeted from
    RIVER to LAB per instruction (RIVER no longer liquid/supported).
    Renaming every internal identifier was judged out of scope / cosmetic-only.

    SEPARATE FINDING (not fixed here, flagging for visibility): this
    dedicated scan path builds its own setup dict and calls format_and_send
    directly, bypassing the SuperTrend/sector/LTF/weekend penalty system
    that scan_coins applies to every other coin, and — as of Point 1
    (too_many_sector_active) — also bypasses the new 1-trade-per-sector
    position limit. LAB is in the "gaming" sector; this path does not
    check whether another gaming-sector coin (MANA, ENJ, etc.) already
    has an open trade before potentially opening LAB. format_and_send's
    own 92.0 strict floor still applies (so nothing below 92.0 ever
    reaches Telegram from here), but this specific portfolio-heat
    protection does not extend to this path. Documented rather than
    silently retrofitted, since expanding this function's checks wasn't
    part of what was asked when Point 1 was built.
    """
    global last_river_time
    try:
        if "LAB" not in active_trades and "LAB" not in pending_signals:
            price=get_price("LABUSDT"); klines=get_klines("LABUSDT","15m",100)
            if not price or not klines or len(klines)<50: return
            found=detect_patterns("LABUSDT",klines,price,1)+detect_patterns("LABUSDT",klines,price,-1)
            seen=set(); unique=[]
            for pat in found:
                if (pat[0],pat[2]) not in seen: seen.add((pat[0],pat[2])); unique.append(pat)
            if unique:
                best=max(unique,key=lambda x:x[1])
                if best[1]<MIN_PRIMARY_SCORE: return
                confirmed=list(dict.fromkeys([x[0] for x in unique]))
                primary=best[0]; extras=[p for p in confirmed if p!=primary]
                pt=primary+(" + "+" + ".join(extras[:2]) if extras else "")
                score=min(best[1]+min(len(unique)*0.5,2),99)
                if score>=82:
                    atr=calculate_atr(klines); atr_pct=(atr/price)*100 if price>0 else 0
                    setup={"coin":"LAB","symbol":"LABUSDT","direction":best[2],"pattern":pt,
                           "setup_score":score,"leverage":get_smart_leverage("LABUSDT",atr_pct,score),
                           "scan_price":price}
                    format_and_send(setup,"LAB",is_river=True,is_instant=score>=INSTANT_SIGNAL_THRESHOLD,market_condition=market_condition)
        last_river_time=now
    except Exception as e: logger.error(f"River: {e}",exc_info=True)


def is_move_already_extended(closes, direction):
    """
    Point 5: Detects if a move has already run too far to chase.
    If price moved 8%+ in the last 12 candles in the signal direction,
    the easy part of the move is likely already gone.
    """
    if len(closes) < 12: return False
    recent = closes[-12:]
    move_pct = (recent[-1] - recent[0]) / recent[0] * 100 if recent[0] > 0 else 0
    if direction == "BUY" and move_pct > 8.0: return True
    if direction == "SELL" and move_pct < -8.0: return True
    return False


def log_retest_candidate(coin, symbol, direction, closes, highs, lows, pattern):
    """
    Point 5: Silent background logging. When a move is too extended to chase,
    log the breakout level as a Demand/Supply zone to watch for a pullback,
    instead of sending a push notification. Visible via /retests command,
    and only pings Telegram once price actually returns to the level.
    """
    global retest_watchlist
    # Use the recent swing as the level to watch for a retest back to
    level = min(lows[-12:]) if direction == "BUY" else max(highs[-12:])
    retest_watchlist[coin] = {
        "symbol": symbol,
        "direction": direction,
        "level": level,
        "pattern": pattern,
        "logged_at": get_ist_datetime(),
        "current_price": closes[-1],
        "notified": False
    }
    save_retest_watchlist()
    logger.info(f"{coin} move already extended — logged retest watch at {format_price(level)} (silent, no push)")


def check_retest_triggers():
    """
    Point 5: Runs each cycle against the silent watchlist. Only sends an
    active Telegram ping when price actually pulls back to the logged level —
    this is the one case where a push notification is warranted.
    """
    global retest_watchlist
    triggered = []
    for coin, w in list(retest_watchlist.items()):
        # Expire stale watches after 12 hours — the setup is no longer relevant
        if (get_ist_datetime() - w["logged_at"]).total_seconds() > 12*3600:
            del retest_watchlist[coin]; continue
        price = get_price(w["symbol"])
        if not price: continue
        near_level = abs(price - w["level"]) / w["level"] * 100 < 1.0 if w["level"] > 0 else False
        if near_level and not w["notified"]:
            w["notified"] = True
            triggered.append((coin, w, price))
    if triggered: save_retest_watchlist()
    return triggered


def get_retest_watchlist_text():
    if not retest_watchlist:
        return f"{_H('RETEST WATCHLIST','👀')}\n\n  🌙 No coins currently being watched for retest.\n\n  🕐 {get_ist_time()}"
    lines = [f"{_H('RETEST WATCHLIST','👀')}\n"]
    for coin, w in retest_watchlist.items():
        price = get_price(w["symbol"]) or w["current_price"]
        dist = abs(price - w["level"]) / w["level"] * 100 if w["level"] > 0 else 0
        dir_em = "🟢" if w["direction"] == "BUY" else "🔴"
        age_min = int((get_ist_datetime() - w["logged_at"]).total_seconds() / 60)
        lines.append(
            f"  {dir_em} <b>{coin}</b> {w['direction']} — watching <code>{format_price(w['level'])}</code>\n"
            f"     now {format_price(price)} ({dist:.1f}% away) · {w['pattern']} · {age_min}m ago\n"
        )
    lines.append(f"\n  🕐 {get_ist_time()}")
    return "\n".join(lines)


def scan_coins(btc_trend,fng,market_condition):
    btc_crashing=is_btc_crashing(); signals_this_cycle=0
    for coin in COINS:
        if signals_this_cycle>=MAX_SIGNALS_PER_CYCLE: break
        try:
            if coin in coin_cooldowns:
                if get_ist_datetime()<coin_cooldowns[coin]:
                    logger.info(f"Skip {coin} - cooldown until {coin_cooldowns[coin].strftime('%H:%M')}"); continue
                else: del coin_cooldowns[coin]
            symbol=coin+"USDT"; price=get_price(symbol); klines=get_klines(symbol,"15m")
            if not price or not klines: continue
            found=detect_patterns(symbol,klines,price,btc_trend)
            if not found: continue
            scored=get_all_pattern_scores(found,market_condition)
            signal_sent=False
            for direction in ["BUY","SELL"]:
                if signal_sent: break
                dir_pats=[p for p in scored if p[2]==direction]
                if not dir_pats: continue
                best_pat=dir_pats[0]; primary=best_pat[0]; adj_score=best_pat[1]; base_s=best_pat[3]
                if base_s<MIN_PRIMARY_SCORE:                                   continue
                if is_pattern_blacklisted(primary):                             continue
                if is_pattern_suspended(primary):                               continue
                if not is_sentiment_valid(direction,fng):                       continue
                if btc_crashing and direction=="BUY":                           continue
                if coin in BTC_CORRELATED and too_many_correlated_active():     continue
                if too_many_sector_active(coin):
                    logger.info(f"Skip {coin} {direction} - sector already has an open trade")
                    continue
                tf_score=get_timeframe_score(symbol,direction)
                if tf_score==-1: logger.info(f"Skip {coin} {direction} - counter-trend"); continue
                extras=[p[0] for p in dir_pats[1:3]]
                pt=primary+(" + "+" + ".join(extras) if extras else "")
                vols_chk=[float(k[5]) for k in klines]
                # Order Book removed (Point 2) — replaced with real BTC
                # 1-Hour trend alignment (Point 3).
                btc_aligned_chk,_=is_btc_aligned(direction)
                # Location + Shift: check S/D zone and market structure/BOS/ChoCh before
                # scoring — these are now the heaviest-weighted confirmations for Tier 1.
                # Uses get_htf_zones (4h primary, 1h secondary) rather than 15m-only,
                # since this point already only runs on candidates that survived the
                # upstream pattern/blacklist/sentiment/counter-trend filters above —
                # not every coin on every scan tick.
                zones_chk=get_htf_zones(symbol)
                zone_ok,_zone_label=is_in_zone(price,direction,zones_chk)
                ms_chk=detect_market_structure(klines)
                # base_s is the pattern's own untouched base score (TIER1_BASE=88.0 or
                # TIER2_BASE=75.0 from detect_patterns) — use it directly to determine
                # tier, rather than matching on pattern name strings.
                is_tier1_pattern = base_s >= 88.0
                is_comp_pattern = "Pre-Breakout Compression" in primary
                confirm_bonus,bonus_notes=compute_confirmation_bonus(
                    symbol,direction,klines,vols_chk,tf_score,btc_aligned_chk,
                    zone_ok=zone_ok,ms_bos=ms_chk["bos"],ms_bias=ms_chk["bias"],
                    ms_choch=ms_chk["choch"],is_tier1=is_tier1_pattern,is_compression=is_comp_pattern
                )
                # Extra-pattern confluence still counts, but modestly — it's not the main driver anymore
                confluence_bonus=min(len(dir_pats)*0.3,1.0)
                score=min(adj_score+confirm_bonus+confluence_bonus,99)
                if bonus_notes:
                    logger.info(f"{coin} {direction} confirmation: base={adj_score:.1f} +{confirm_bonus} ({', '.join(bonus_notes)}) -> {score:.1f}")
                if score<MIN_SETUP_SCORE: continue
                closes_chk=[float(k[4]) for k in klines]
                highs_chk=[float(k[2]) for k in klines]
                lows_chk=[float(k[3]) for k in klines]
                if "Volatility Contraction" not in primary and is_move_already_extended(closes_chk,direction):
                    log_retest_candidate(coin,symbol,direction,closes_chk,highs_chk,lows_chk,pt)
                    continue
                atr=calculate_atr(klines); atr_pct=(atr/price)*100 if price>0 else 0
                lev=get_smart_leverage(symbol,atr_pct,score)
                setup={"coin":coin,"symbol":symbol,"direction":direction,"pattern":pt,
                       "setup_score":score,"leverage":lev,"scan_price":price,
                       "market_condition":market_condition,"tf_score":tf_score}
                if (coin not in active_trades and coin not in pending_signals and len(active_trades)<MAX_ACTIVE_TRADES):
                    is_inst=score>=INSTANT_SIGNAL_THRESHOLD
                    logger.info(f"{'INSTANT' if is_inst else 'SIGNAL'}: {coin}|{direction}|Score:{score:.1f}|{primary}")
                    if format_and_send(setup,coin,is_instant=is_inst,market_condition=market_condition):
                        signal_sent=True; signals_this_cycle+=1
        except Exception as e: logger.error(f"Scan {coin}: {e}",exc_info=True)
        time.sleep(DELAY_BETWEEN_COINS)

def main():
    global last_river_time,last_hourly_time,last_pnl_update_time,last_8h_desk_time,last_weekly_report_day
    load_alerts(); load_circuit_breaker(); load_pending_signals(); load_retest_watchlist(); load_macro_events()
    cloud_load_all()   # loads journal, pattern_stats, learning, active_trades from Supabase (falls back to local JSON)
    threading.Thread(target=poll_telegram,daemon=True).start()
    logger.info(f"{BOT_NAME} {BOT_VERSION} starting...")
    send_telegram(
        f"🚀 <b>TRADING SIGNAL MASTER v32G</b> 🚀\n"
        f"<i>Smart • Fast • Accurate • AI</i>\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
        f"<b>✅ All Systems Active</b>\n\n"
        f"🔍 Scanner: <b>{len(COINS)} coins</b>\n"
        f"📊 4h + 1h Trend Filter\n"
        f"🌀 SuperTrend (15m + 1h)\n"
        f"📈 ADX Min: <b>{ADX_MIN_TREND}</b>\n"
        f"💧 VWAP Institutional Filter\n"
        f"📍 Supply & Demand Zones\n"
        f"📊 VWAP Institutional Filter\n"
        f"🔀 RSI Divergence Detection\n"
        f"🐋 Whale Detection\n"
        f"😱 Fear & Greed Index\n"
        f"💰 Funding Rate + OI\n"
        f"🛡️ Circuit Breaker (≤ -5% only)\n"
        f"🔄 CB Auto-Reset Midnight IST\n"
        f"⚡ Instant Signals ≥ {INSTANT_SIGNAL_THRESHOLD}\n"
        f"🎯 Smart Position Sizing\n"
        f"🏆 Signal Grading A+/A/B/C\n"
        f"📋 Profit Milestones +10/20/35%\n"
        f"🧠 AI Pattern Learning\n"
        f"⏱️ ETA-Based Coin Cooldown\n"
        f"🌙 Dead Session (2AM-7AM IST)\n"
        f"📰 CryptoPanic News {'✅' if NEWS_API_KEY else '⚠️ (set NEWS_API_KEY)'}\n"
        f"💾 Storage: Local JSON files\n"
        f"📊 Backtest Engine\n"
        f"🗓️ Weekly AI Insight\n"
        f"🎯 Min Score: <b>{MIN_SETUP_SCORE}</b>\n"
        f"🌀 SuperTrend: 15m = hard block, 1h = grade bonus\n"
        f"📊 Volume: Dead-volume filter (≥85% avg)\n"
        f"📍 Drift: Price must stay within 2% of scan\n\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"📌 Type /help for all commands\n"
        f"🕐 {get_ist_time()}"
    )
    while True:
        try:
            btc_price=get_price("BTCUSDT"); btc_klines=get_klines("BTCUSDT","1h",100)
            btc_ema50=calculate_ema([float(x[4]) for x in btc_klines],50) if btc_klines else None
            if not btc_price or btc_ema50 is None:
                logger.warning("BTC data unavailable"); time.sleep(60); continue
            btc_trend=1 if btc_price>btc_ema50 else -1
            fng=get_fear_greed_index()
            market_condition=detect_market_condition(btc_price,btc_klines)
            logger.info(f"BTC:{'BULL' if btc_trend==1 else 'BEAR'}|Market:{market_condition}|F&G:{fng}|Losses:{daily_losses}/{MAX_DAILY_LOSSES}|CB:{'ACTIVE' if check_circuit_breaker() else 'OK'}")
            scan_coins(btc_trend,fng,market_condition)
            check_active_trades()
            expire_pending_signals()
            check_price_alerts()
            for coin,w,price in check_retest_triggers():
                dir_em="🟢 LONG" if w["direction"]=="BUY" else "🔴 SHORT"
                send_telegram(
                    f"👀 <b>RETEST TRIGGERED — {coin}</b>\n"
                    f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
                    f"  {dir_em}  •  {w['pattern']}\n"
                    f"  Missed the initial move — price pulled back to\n"
                    f"  the watched level <code>{format_price(w['level'])}</code>\n"
                    f"  Now: <code>{format_price(price)}</code>\n\n"
                    f"  Check the chart — this may be your entry.\n"
                    f"  🕐 {get_ist_time()}"
                )
                logger.info(f"RETEST PING sent: {coin}")
            now=time.time()
            if (now-last_hourly_time)>=3600:          send_hourly_report();   last_hourly_time=now
            if (now-last_pnl_update_time)>=3600:      send_live_pnl_update(); last_pnl_update_time=now
            if (now-last_river_time)>=RIVER_INTERVAL:  scan_river(now,market_condition); last_river_time=now
            if (now-last_8h_desk_time)>=28800:         send_8h_ai_desk_report(); last_8h_desk_time=now  # 8h = 28800s
            today=datetime.now(IST).date()
            if today.weekday()==6 and last_weekly_report_day!=today:
                send_weekly_report(); last_weekly_report_day=today
            time.sleep(SCAN_INTERVAL)
        except Exception as e:
            logger.error(f"Main loop: {e}",exc_info=True); time.sleep(60)

if __name__=="__main__":
    main()
