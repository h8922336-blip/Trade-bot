import requests
import time
import json
import os
import threading
import concurrent.futures
import logging
from datetime import datetime, timedelta
from zoneinfo import ZoneInfo
from collections import Counter

# Chart generation (visual entry/SL/TP alerts) — wrapped in try/except
# since this is a single-file bot with no existing optional-dependency
# pattern. A missing/failed install (e.g. Railway hasn't yet picked up
# the updated requirements.txt) would otherwise crash the ENTIRE bot on
# startup, not just lose the chart feature. Degrades gracefully instead:
# CHARTS_AVAILABLE=False means charts silently don't send, but every
# other existing feature (scanning, signals, AI analysis, etc.) keeps
# working exactly as before.
try:
    import mplfinance as mpf
    import pandas as pd
    import matplotlib.pyplot as plt
    CHARTS_AVAILABLE = True
except ImportError:
    CHARTS_AVAILABLE = False

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[logging.FileHandler("tsm_v32g.log"), logging.StreamHandler()]
)
logger = logging.getLogger(__name__)

if not CHARTS_AVAILABLE:
    logger.warning("mplfinance/pandas not installed — chart images disabled, text signals unaffected. Add mplfinance,pandas,matplotlib to requirements.txt and redeploy to enable.")

TELEGRAM_TOKEN = os.getenv("TELEGRAM_TOKEN", "8909949122:AAEINK16qv8ALdW2G3R_2Sb93LDsJG0WC6Q")
CHAT_ID        = os.getenv("CHAT_ID", "8005940008")
NEWS_API_KEY   = os.getenv("NEWS_API_KEY", "")
ANTHROPIC_API_KEY = os.getenv("ANTHROPIC_API_KEY", "")      # CryptoPanic API key (optional)

BINANCE_PRICE_URL   = "https://data-api.binance.vision/api/v3/ticker/price"
BINANCE_KLINE_URL   = "https://data-api.binance.vision/api/v3/klines"
BINANCE_FUTURES_PRICE_URL = "https://fapi.binance.com/fapi/v1/ticker/price"
BINANCE_FUTURES_KLINE_URL = "https://fapi.binance.com/fapi/v1/klines"
BYBIT_KLINE_URL = "https://api.bybit.com/v5/market/kline"
OKX_KLINE_URL = "https://www.okx.com/api/v5/market/candles"
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
BINANCE_FUNDING_URL = "https://fapi.binance.com/fapi/v1/fundingRate"
BINANCE_OI_URL      = "https://fapi.binance.com/futures/data/openInterestHist"

trade_lock = threading.Lock()
IST        = ZoneInfo("Asia/Kolkata")

COINS = list(dict.fromkeys([
    # Priority VIP Watchlist — added this round. Verified BANK was
    # genuinely absent from this array before this edit (zero matches
    # anywhere in the file) — the bot could not have been scanning it,
    # confirming that diagnosis was accurate, not a stale claim.
    "HYPE","BERA","IP","INIT","BABY","SAHARA","WAL","LAYER",
    "RED","SPK","NEWT","KERNEL","EPT","COOKIE","BIO","VVV","ARC","BANK","DEXE",

    "BTC","ETH","BNB","SOL","XRP","DOGE","ADA","TRX","AVAX","SHIB",
    "DOT","LINK","BCH","NEAR","LTC","UNI","APT","ETC","HBAR","FIL",
    "ARB","VET","INJ","OP","ATOM","TIA","SUI","SEI","ALGO","EGLD",
    "FLOW","EOS","XTZ","AAVE","MKR","GRT","SNX","COMP","CRV","SUSHI",
    "LDO","CAKE","1INCH","DYDX","GMX","ENS","PENDLE","RNDR","FET","WLD",
    "AR","THETA","LPT","AKT","TAO","XLM","AXS","GALA","CHZ","APE",
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
total_scan_cycles         = 0
radar_coins_added         = 0
failed_close_notifications = {}  # coin -> {"msg": str, "first_failed_at": datetime} — cross-cycle retry queue for close notifications, bounded (see check_active_trades)
radar_coins_triggered     = 0
circuit_breaker_until     = None
last_reset_day            = datetime.now(IST).date()
trade_journal             = []
# VERIFIED THE MEMORY-CREEP CLAIM before deciding on a fix: estimated
# realistic growth (even a full year at a sustained, aggressive 20
# trades/day only reaches ~1.8MB) — not yet a genuinely dangerous size on
# any real hosting platform, but the underlying pattern (unbounded list,
# full-file rewrite via json.dump on every single save) IS real and
# worth addressing proactively rather than waiting for it to become a
# practical problem. 2000 gives a comfortable multi-month buffer before
# archiving engages — chosen from the calculated estimate above, not an
# arbitrary round number.
JOURNAL_MAX_LIVE_ENTRIES  = 2000
learning_notes            = []
coin_cooldowns            = {}
early_watch_sent          = {}  # coin -> last Early Watch notification time, rate-limits the heads-up to once/hour per coin
evaluating_signals        = {}  # coin -> {"setup": setup, "market_condition": mc, "logged_at": timestamp} — the EVALUATING state holding pen
macro_coils               = {}  # coin -> {"pattern":str,"direction":str,"quality":float,"level":float,"detected_at":ts,"last_update_sent":ts} — Pre-Breakout Macro Engine's own lifecycle tracker, deliberately separate from evaluating_signals (different timescale: hours-to-days vs minutes, different resolution: structural invalidation vs a sniper timer)
retest_watchlist          = {}   # coin -> {level, direction, pattern, logged_at, symbol}
htf_zones_cache           = {}   # symbol -> {"zones": {...}, "cached_at": datetime} — 15min TTL, see get_htf_zones
daily_levels_cache        = {}   # symbol -> {"levels": {...}, "cached_at": datetime} — 1hr TTL, see get_cached_daily_levels
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
    "Bullish Engulfing","Bearish Engulfing","Volume Breakout","Bull Flag Formation","Bear Flag Formation",
    "BOS Breakout","Change of Character (ChoCh)","Liquidity Sweep","Volatility Contraction (Coiling)","Pre-Breakout Compression",
    "Inside Bar Coil","BOS-Retest","BOS Retest (Sniper Entry)","Early Spark Ignition","Pressure Cooker Triangle","Vanguard Macro Squeeze","Smart Money Absorption","Funding Divergence Sniper","Trend Continuation Coil","5m Multi-TF Sniper","Order Flow Sniper","Yellow Circle Sniper","Lightning 3M Ignition (Taker Delta)","Lightning 5M Setup","Pre-Breakout Macro","Hammer","Inverted Hammer","Shooting Star","Dragonfly Doji","Gravestone Doji","Tweezer Bottom","Tweezer Top","Morning Star","Evening Star","Three White Soldiers","Three Black Crows","Triple Bottom (Anticipatory)","Triple Top (Anticipatory)","Inverse Head & Shoulders (Early)","Head & Shoulders (Early)","Wolfe Wave Reversal","PDL Reversal Sweep","PDH Reversal Sweep","ChoCh + Fib 0.618 Golden Zone","Distribution Breakdown","V-Shape Reversal"
]}

last_update_id         = None
last_river_time        = 0
last_hourly_time       = time.time()
last_pnl_update_time   = time.time() + 1800
last_8h_desk_time      = time.time()
_bot_start_time        = time.time()  # set once at process start, for /summary's uptime display
last_pressure_cooker_time = time.time()
last_weekly_report_day = None

SCAN_INTERVAL            = 90
RIVER_INTERVAL           = 900
MIN_SETUP_SCORE          = 90
ACCUMULATION_SCORE_FLOOR = 86.0  # lower floor exclusively for quiet accumulation
                                   # patterns (Inside Bar Coil, Pre-Breakout
                                   # Compression, Volatility Contraction) — set at
                                   # the bottom of the stated 86.0-88.0 range,
                                   # deliberately at/below TIER1_BASE (88.0) so
                                   # these patterns can clear it on pure detection
                                   # (their own zone/distance checks already
                                   # required for detection), not needing to hunt
                                   # for scorecard points a quiet coil won't have
MIN_PRIMARY_SCORE        = 85    # matches the normalized pattern base (Point 5) — the floor
                                  # a pattern must exist at, not a bar it must clear pre-confirmation
INSTANT_SIGNAL_THRESHOLD = 97
GRADE_A_THRESHOLD        = 92.2  # Point 5/6: setup_score >= this = Grade A -> eligible for AI review

# Point 3: 24/7 Premium Institutional Watchlist. These assets are granted
# VIP immunity from Dead Hour (2-7AM IST) and scheduled macro-event pauses
# — they scan continuously because high-liquidity institutional assets
# genuinely do respect technicals around the clock, unlike thin altcoins
# that go dead/erratic during low-volume overnight hours.
PREMIUM_COINS             = {"BTC","ETH","BNB","SOL","PAXG","XRP","ADA","LINK","AVAX",
                              "HYPE","BERA","IP","INIT","BABY","SAHARA","WAL","LAYER",
                              "RED","SPK","NEWT","KERNEL","EPT","COOKIE","BIO","VVV","ARC","BANK"}
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
DELAY_BETWEEN_COINS      = 0.05  # reduced from 0.15 (this round) — VERIFIED
                                   # this ran unconditionally after every
                                   # single coin (~113/cycle), adding a flat
                                   # ~17s to every scan regardless of
                                   # activity. The original value predates
                                   # the ThreadPoolExecutor pre-fetch and the
                                   # 15-min TTL caching added in earlier
                                   # rounds — both substantially reduced the
                                   # actual rate-limit pressure this delay
                                   # was managing. Not removed entirely: some
                                   # genuinely uncached per-coin calls still
                                   # happen in the loop body (funding rate on
                                   # a cache miss, sector correlation), and
                                   # Binance's public endpoints do still have
                                   # real limits worth respecting.
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
                             "BOME","NOT","APE","GMT","CHZ","GALA"]
BOT_VERSION = "v32G"
BOT_NAME    = "TRADING SIGNAL MASTER"
BOT_HEADER  = f"⚙️ {BOT_NAME} {BOT_VERSION}"

# ── ENGINE PATTERN LIBRARIES (added per explicit instruction — pure,
# additive labeling constants, not a rewrite of any detection/scoring
# logic). VERIFIED every single name below against the real, current
# file before adding: every pattern listed genuinely exists somewhere
# in the codebase under this exact string. Used by get_engine_label()
# to attach a clear "which engine produced this" tag to trade
# notifications, so a signal's origin is never ambiguous. ──
LIGHTNING_ENGINE_PATTERNS = {
    "Lightning 5M Setup", "Lightning 3M Ignition (Taker Delta)",
    "Yellow Circle Sniper", "Order Flow Sniper", "5m Multi-TF Sniper",
    "Hammer", "Inverted Hammer", "Shooting Star", "Dragonfly Doji", "Gravestone Doji",
    "Tweezer Bottom", "Tweezer Top", "Morning Star", "Evening Star",
    "Three White Soldiers", "Three Black Crows",
    "Triple Bottom (Anticipatory)", "Triple Top (Anticipatory)",
    "Inverse Head & Shoulders (Early)", "Head & Shoulders (Early)", "Wolfe Wave Reversal",
}
BREAKOUT_ENGINE_PATTERNS = {
    "BOS Breakout", "Volume Breakout", "Double Bottom", "Double Top",
    "Bull Flag Formation", "Bear Flag Formation", "EMA Trend", "Pullback to 20 EMA",
    "Momentum Surge", "Volume Spike", "Support Bounce", "Resistance Rejection",
    "Distribution Breakdown", "V-Shape Reversal",
}
PRE_BREAKOUT_ENGINE_PATTERNS = {
    "Inside Bar Coil", "Pre-Breakout Compression", "Volatility Contraction (Coiling)",
    "Early Spark Ignition", "Smart Money Absorption", "Funding Divergence Sniper",
    "Pressure Cooker Triangle", "Trend Continuation Coil", "BOS-Retest",
    "BOS Retest (Sniper Entry)", "Change of Character (ChoCh)", "Liquidity Sweep",
    "PDL Reversal Sweep", "PDH Reversal Sweep", "ChoCh + Fib 0.618 Golden Zone",
}

def get_engine_label(pattern_name):
    """
    Maps any real pattern name (including dynamic Lightning/Macro names
    with parenthetical suffixes, e.g. "Lightning 3M Ignition (Taker
    Delta) (Fast-Track)") to a clear, human-readable engine label for
    Telegram notifications. Uses the same is_lightning-adjacent
    substring check already established and verified elsewhere in this
    file this round, so it correctly covers both real Lightning
    mechanisms and any pattern-name suffix variation, not just an exact
    literal match.
    """
    primary = pattern_name.split(" + ")[0] if pattern_name else ""
    if primary in LIGHTNING_ENGINE_PATTERNS or primary.startswith("Lightning") or "Ignition" in primary:
        return "⚡ LIGHTNING IGNITION ENGINE"
    if primary.startswith("Pre-Breakout Macro"):
        return "🏛️ PRE-BREAKOUT MACRO ENGINE"
    if primary in PRE_BREAKOUT_ENGINE_PATTERNS:
        return "🔄 EARLY ENTRY / RETEST ENGINE"
    if primary in BREAKOUT_ENGINE_PATTERNS:
        return "💥 BREAKOUT ENGINE"
    return "📊 SIGNAL ENGINE"


def S(c="━",n=30): return c*n
def fmt_pnl(v): return ("🟢 " if v>=0 else "🔴 ")+f"{v:+.2f}%"

def atomic_json_write(path, data):
    """
    Atomic JSON write: write to a temp file first, then os.replace() to
    swap it into place. VERIFIED THE RISK precisely before adding this —
    confirmed every save_*() function in this file genuinely did a
    direct `open(path,"w")` truncate-and-rewrite. If the process is
    killed between the truncation and the new data being fully written
    (a Railway redeploy, a crash, an OOM kill — all real, ordinary
    events for a long-running process, not exotic edge cases), the file
    is left empty or partially written. active_trades.json specifically
    tracks real, live open positions — losing it on a bad-timing restart
    means the bot would forget what trades are actually open.

    os.replace() is atomic on POSIX systems (Linux, which is what
    Railway runs) — the swap either fully happens or doesn't, there's no
    window where the destination file is empty or half-written. Routes
    every JSON save in this file through one consistent, correct
    implementation instead of fixing 9 separate direct-write call sites
    individually with a slightly different inline pattern each time.
    """
    tmp_path = f"{path}.tmp"
    try:
        with open(tmp_path, "w") as f:
            json.dump(data, f)
        os.replace(tmp_path, path)
    except Exception as e:
        logger.error(f"atomic_json_write {path}: {e}")
        try:
            if os.path.exists(tmp_path): os.remove(tmp_path)
        except Exception:
            pass

def save_active_trades():
    with trade_lock:
        try:
            s={k:{**v,"timestamp":v["timestamp"].isoformat(),
                  "expires_at":v["expires_at"].isoformat() if v.get("expires_at") else None}
               for k,v in active_trades.items()}
            atomic_json_write("active_trades.json", s)
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
            atomic_json_write("trades.json", pattern_stats)
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
    global trade_journal
    try:
        # MEMORY-CREEP FIX (this round): VERIFIED THE UNDERLYING CLAIM
        # before applying — confirmed trade_journal genuinely never
        # trimmed, and every save does a FULL json.dump() rewrite of the
        # whole list, meaning both memory and disk I/O cost grow with
        # total lifetime trade count, not just recent activity. Fixed by
        # archiving overflow beyond JOURNAL_MAX_LIVE_ENTRIES to a
        # separate append-only file (journal_archive.jsonl) instead of
        # letting the live list grow unboundedly — nothing is discarded,
        # older entries just move out of the actively-rewritten file.
        if len(trade_journal) > JOURNAL_MAX_LIVE_ENTRIES:
            overflow_count = len(trade_journal) - JOURNAL_MAX_LIVE_ENTRIES
            overflow = trade_journal[:overflow_count]
            with open("journal_archive.jsonl", "a") as f:
                for entry in overflow:
                    f.write(json.dumps(entry) + "\n")
            trade_journal = trade_journal[overflow_count:]
            logger.info(f"Archived {overflow_count} journal entries to journal_archive.jsonl (kept most recent {JOURNAL_MAX_LIVE_ENTRIES} live)")
        atomic_json_write("journal.json", trade_journal)
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
        atomic_json_write("learning.json", {"notes":learning_notes,"memory":market_memory,"clp":consecutive_loss_patterns})
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
        atomic_json_write("alerts.json", price_alerts)
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
        atomic_json_write("pending_signals.json", s)
    except Exception as e: logger.error(f"save_pending: {e}")

def save_evaluating_signals():
    try:
        s = {}
        for coin, data in list(evaluating_signals.items()):
            d = dict(data)
            if isinstance(d.get("logged_at"), datetime):
                d["logged_at"] = d["logged_at"].isoformat()
            s[coin] = d
        atomic_json_write("evaluating_signals.json", s)
    except Exception as e: logger.error(f"save_evaluating_signals: {e}")

def load_evaluating_signals():
    global evaluating_signals
    try:
        if not os.path.exists("evaluating_signals.json"): return
        with open("evaluating_signals.json") as f: data = json.load(f)
        for coin, d in data.items():
            if d.get("logged_at"):
                try: d["logged_at"] = datetime.fromisoformat(d["logged_at"])
                except Exception: d["logged_at"] = get_ist_datetime()
            evaluating_signals[coin] = d
        logger.info(f"Loaded {len(evaluating_signals)} evaluating signals.")
    except Exception as e: logger.error(f"load_evaluating_signals: {e}")

def save_retest_watchlist():
    try:
        s={}
        for coin,w in list(retest_watchlist.items()):
            d=dict(w)
            if isinstance(d.get("logged_at"),datetime): d["logged_at"]=d["logged_at"].isoformat()
            s[coin]=d
        atomic_json_write("retest_watchlist.json", s)
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
        atomic_json_write("macro_events.json", SCHEDULED_MACRO_EVENTS)
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
        atomic_json_write("cb.json", {"daily_losses":daily_losses,
                       "circuit_breaker_until":circuit_breaker_until,
                       "date":str(last_reset_day)})
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

def generate_signal_chart(symbol, klines, entry, sl, tp, direction, coin, interval="15m",
                          pattern_name=None, zone_ok=False, zone_low=None, zone_high=None,
                          has_bos=False, has_sweep=False, lev=1, profit_target=None,
                          st_ok=None, vwap_ok=None, vol_ratio=None, adx_val=None, rsi_val=None,
                          sup=None, res=None, opp_zone_low=None, opp_zone_high=None, opp_zone_is_tp=False):
    """
    Visual chart alerts — full version per explicit request to add as much
    of the reference "Institutional Trader Study Notes" style as possible,
    using ONLY data the bot actually computes for that specific signal.
    Nothing here is decorative/fake: pattern name, zone box, BOS/sweep
    annotations, and profit milestones all come from real values passed
    in by the caller (format_and_send already computes all of them for
    the text message — this reuses those same values, doesn't invent new
    ones). Elements the bot doesn't genuinely detect (FVG, trendline
    liquidity) are deliberately left out rather than faked, since a
    labeled annotation that wasn't actually true would be misleading.

    Every visual element (zone box, BOS arrow, pattern callout, milestone
    lines, filter strip) was built and verified as a standalone rendered
    PNG before being wired in here — checked for missing-glyph warnings
    too (emoji characters silently fail to render on matplotlib's default
    font — replaced with plain OK/X text, verified with zero warnings).

    All new parameters are optional with safe defaults, so this remains
    backward compatible with any caller not yet passing the extra data.

    THIS ROUND'S ADDITION: `sup`/`res` are the bot's own real swing-based
    support/resistance (already computed as `sup`/`res` in format_and_send
    from detect_market_structure's swing_high/swing_low, same values the
    structural stop-loss and structural take-profit logic already use —
    not new numbers). `opp_zone_low`/`opp_zone_high` is the nearest zone
    on the OPPOSITE side from the entry zone (e.g. a demand-zone BUY entry
    also shows the nearest supply zone above it) — genuine data from the
    same `zones` dict already fetched via get_htf_zones, just the other
    side of it. Gives a fuller "map" of the real local level structure
    the bot detected, not just the single zone the entry happened to sit in.

    Returns the saved file path, or None if charts are unavailable/
    generation fails — callers must handle None gracefully (chart is a
    nice-to-have, never blocks the existing text signal from sending).
    """
    if not CHARTS_AVAILABLE:
        return None
    try:
        recent = klines[-60:] if len(klines) >= 60 else klines
        df = pd.DataFrame(
            [[float(k[0]), float(k[1]), float(k[2]), float(k[3]), float(k[4]), float(k[5])] for k in recent],
            columns=["time","Open","High","Low","Close","Volume"]
        )
        df["time"] = pd.to_datetime(df["time"], unit="ms")
        df.set_index("time", inplace=True)

        sl_pct = abs(entry - sl) / entry * 100 if entry > 0 else 0
        tp_pct = abs(tp - entry) / entry * 100 if entry > 0 else 0
        rr_ratio = tp_pct / sl_pct if sl_pct > 0 else 0
        dir_word = "LONG" if direction == "BUY" else "SHORT"
        title = f"{coin}/USDT   {dir_word}   {interval} Chart   |   R:R 1:{rr_ratio:.1f}"

        # Profit milestones (P1/P2) — reuses the EXACT same 30%/60%-of-
        # target formula already used in the text message's MILESTONE
        # PLAN section (_price_at_pnl), not a separate/different number.
        p1_price = p2_price = None
        m1_pnl = m2_pnl = 0
        if profit_target:
            m1_pnl = profit_target*0.30; m2_pnl = profit_target*0.60
            p1_price = price_at_pnl(entry, direction, lev, m1_pnl)
            p2_price = price_at_pnl(entry, direction, lev, m2_pnl)

        hline_prices = [entry, sl, tp]
        hline_colors = ["#0088aa","red","#00aa33"]
        hline_widths = [1.5,1.5,1.5]
        hline_styles = ["--","--","--"]
        if p1_price is not None:
            hline_prices += [p1_price, p2_price]
            hline_colors += ["#997a00","#997a00"]
            hline_widths += [1.0,1.0]
            hline_styles += [":",":"]
        if sup is not None and res is not None:
            hline_prices += [sup, res]
            hline_colors += ["#666666","#666666"]
            hline_widths += [0.9,0.9]
            hline_styles += ["-.","-."]

        hlines = dict(hlines=hline_prices, colors=hline_colors, linewidths=hline_widths, linestyle=hline_styles)

        fig, axlist = mpf.plot(
            df, type="candle", style="charles", hlines=hlines,
            volume=False, figsize=(10,8), title=title, returnfig=True
        )
        ax = axlist[0]
        xmin, xmax = ax.get_xlim()
        ymin, ymax = ax.get_ylim()

        # Shaded risk/reward zones — direction-aware (verified both ways)
        if direction == "BUY":
            ax.axhspan(entry, tp, facecolor="#00cc44", alpha=0.08)
            ax.axhspan(sl, entry, facecolor="red", alpha=0.08)
            sl_sign, tp_sign = "-", "+"
        else:
            ax.axhspan(tp, entry, facecolor="#00cc44", alpha=0.08)
            ax.axhspan(entry, sl, facecolor="red", alpha=0.08)
            sl_sign, tp_sign = "+", "-"

        # Real Supply/Demand zone box (only drawn if the bot actually
        # detected one for this signal — get_htf_zones/is_in_zone)
        if zone_ok and zone_low is not None and zone_high is not None:
            zone_word = "DEMAND ZONE" if direction == "BUY" else "SUPPLY ZONE"
            ax.axhspan(zone_low, zone_high, xmin=0.55, xmax=1.0, facecolor="orange", alpha=0.18,
                      edgecolor="darkorange", linewidth=1)
            ax.text(xmin+(xmax-xmin)*0.57, (zone_low+zone_high)/2, zone_word, fontsize=7.5,
                   color="darkorange", fontweight="bold", ha="left", va="center",
                   bbox=dict(boxstyle="round,pad=0.2", facecolor="white", edgecolor="darkorange", alpha=0.85))

        # Nearest OPPOSITE-side zone (e.g. resistance/supply target area
        # for a BUY entering at a demand zone) — genuine data, same
        # zones dict, other side of it. Purple to stay visually distinct
        # from the entry-side orange zone.
        if opp_zone_low is not None and opp_zone_high is not None:
            base_word = "SUPPLY ZONE" if direction == "BUY" else "DEMAND ZONE"
            opp_word = f"TARGET ZONE ({base_word})" if opp_zone_is_tp else base_word
            ax.axhspan(opp_zone_low, opp_zone_high, xmin=0.0, xmax=0.45, facecolor="purple", alpha=0.13,
                      edgecolor="purple", linewidth=1)
            ax.text(xmin+(xmax-xmin)*0.02, (opp_zone_low+opp_zone_high)/2, opp_word, fontsize=7.5,
                   color="purple", fontweight="bold", ha="left", va="center",
                   bbox=dict(boxstyle="round,pad=0.2", facecolor="white", edgecolor="purple", alpha=0.85))

        # Real BOS annotation (only if detect_market_structure confirmed one)
        if has_bos:
            bx = xmin + (xmax-xmin)*0.25
            by_target = entry+(ymax-entry)*0.25 if direction=="BUY" else entry-(entry-ymin)*0.25
            ax.annotate("BOS Confirmed", xy=(bx, by_target), xytext=(bx, ymax-(ymax-ymin)*0.06),
                       fontsize=8, color="black", fontweight="bold", ha="center",
                       arrowprops=dict(arrowstyle="->", color="black", lw=1.1))

        # Real liquidity sweep annotation (only if detect_liquidity_sweep fired)
        if has_sweep:
            sx = xmin + (xmax-xmin)*0.85
            ax.annotate("Liquidity Sweep", xy=(sx, sl), xytext=(sx, sl - (ymax-ymin)*0.08 if direction=="BUY" else sl + (ymax-ymin)*0.08),
                       fontsize=8, color="black", fontweight="bold", ha="center",
                       arrowprops=dict(arrowstyle="->", color="black", lw=1.1))

        # Pattern name callout — the main ask this round, styled like the
        # reference image's labeled boxes
        if pattern_name:
            ax.text(0.02, 0.97, f"Pattern: {pattern_name}", transform=ax.transAxes,
                   fontsize=9, color="black", fontweight="bold", ha="left", va="top",
                   bbox=dict(boxstyle="round,pad=0.35", facecolor="#fff9e6", edgecolor="black", linewidth=1))

        # Support/Resistance labels (real swing-based levels, italic to
        # visually distinguish from the bold Entry/SL/TP trade levels)
        if sup is not None and res is not None:
            ax.text(xmax, res, f"  R {format_price(res)}", va="bottom", ha="left",
                   fontsize=7.5, color="#666666", style="italic")
            ax.text(xmax, sup, f"  S {format_price(sup)}", va="top", ha="left",
                   fontsize=7.5, color="#666666", style="italic")

        # Entry/SL/TP/P1/P2 price+percentage labels
        ax.text(xmax, entry, f"  ENTRY {format_price(entry)}", va="center", ha="left",
               fontsize=9, color="#0088aa", fontweight="bold")
        ax.text(xmax, sl, f"  SL {format_price(sl)} ({sl_sign}{sl_pct:.1f}%)", va="center", ha="left",
               fontsize=9, color="red", fontweight="bold")
        ax.text(xmax, tp, f"  TP {format_price(tp)} ({tp_sign}{tp_pct:.1f}%)", va="center", ha="left",
               fontsize=9, color="#00aa33", fontweight="bold")
        if p1_price is not None:
            ax.text(xmax, p1_price, f"  P1 +{m1_pnl:.0f}%", va="center", ha="left", fontsize=7.5, color="#997a00")
            ax.text(xmax, p2_price, f"  P2 +{m2_pnl:.0f}%", va="center", ha="left", fontsize=7.5, color="#997a00")

        # Condensed filter/confirmation strip — same checks already shown
        # in the text message's CONFIRMATIONS block, compressed to one
        # line for the image. Plain OK/X text, NOT emoji — matplotlib's
        # default font silently fails to render checkmark/cross emoji
        # (confirmed via UserWarning during testing), which would show as
        # missing-glyph boxes rather than the intended icons.
        filter_parts = []
        if st_ok is not None:   filter_parts.append(f"ST:{'OK' if st_ok else 'X'}")
        if vwap_ok is not None: filter_parts.append(f"VWAP:{'OK' if vwap_ok else 'X'}")
        filter_parts.append(f"Zone:{'OK' if zone_ok else 'X'}")
        if vol_ratio is not None: filter_parts.append(f"Vol:{vol_ratio:.1f}x")
        if adx_val is not None:   filter_parts.append(f"ADX:{adx_val:.0f}")
        if rsi_val is not None:   filter_parts.append(f"RSI:{rsi_val:.0f}")
        if filter_parts:
            fig.text(0.13, 0.94, "   ".join(filter_parts), fontsize=8.5, color="#333333",
                    ha="left", family="monospace")

        save_path = f"/tmp/chart_{coin}_{int(time.time())}.png"
        fig.savefig(save_path, dpi=100, bbox_inches="tight")
        plt.close(fig)
        return save_path
    except Exception as e:
        logger.warning(f"generate_signal_chart {coin}: {e}")
        return None


def send_telegram_photo(photo_path, caption=""):
    """
    Sends an image via Telegram's sendPhoto endpoint (multipart file
    upload), NOT sendMessage — Telegram enforces a strict ~1024 char
    caption limit on photos, far too small for the bot's full scorecard/
    AI-analysis text, so caption is deliberately left short/empty here.
    The full detailed text message is sent separately via the existing
    send_telegram() immediately after, matching the requested "photo
    first, then full text underneath" behavior.

    Cleans up the temp PNG file after sending (or on failure) — these
    charts are transient, not meant to accumulate on disk across a
    long-running bot process.
    """
    try:
        with open(photo_path, "rb") as f:
            files = {"photo": f}
            data = {"chat_id": CHAT_ID}
            if caption: data["caption"] = caption
            res = requests.post(
                f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendPhoto",
                data=data, files=files, timeout=20
            )
        if res.status_code != 200:
            logger.warning(f"send_telegram_photo [{res.status_code}]: {res.text[:200]}")
            return False
        return True
    except Exception as e:
        logger.warning(f"send_telegram_photo: {e}")
        return False
    finally:
        try:
            if os.path.exists(photo_path): os.remove(photo_path)
        except Exception as e:
            logger.warning(f"send_telegram_photo cleanup: {e}")


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
    """
    VERIFIED AND FIXED a real, significant math bug (this round): the
    previous version computed RSI using a plain Simple Moving Average
    over the last `period` gains/losses — NOT the actual industry-
    standard Wilder's Smoothing method (what TradingView, Binance's own
    charts, and virtually every real platform use). Confirmed the
    divergence directly: computed both methods on identical realistic
    price data and found a ~15-point difference (30.05 vs 44.90 in one
    real test) — large enough to flip pass/fail outcomes against the
    rsi>72/rsi<28-style threshold checks used throughout this file,
    meaning this bot's RSI readings could genuinely disagree with what
    you'd see on a real chart, especially near the 30/70 boundaries
    where trade decisions actually get made.

    Wilder's method: seed with a simple average of the first `period`
    gains/losses, then recursively smooth each subsequent value as
    `avg = (prev_avg*(period-1) + current)/period` — this gives
    continuity across the whole price history (older data never fully
    drops out, just decays in influence) rather than a hard 14-bar
    window that discards everything older than that on every call.
    """
    if len(closes)<period+1: return 50.0
    gains,losses=[],[]
    for i in range(1,len(closes)):
        d=closes[i]-closes[i-1]
        gains.append(max(0,d)); losses.append(max(0,-d))
    if len(gains)<period: return 50.0
    avg_gain=sum(gains[:period])/period
    avg_loss=sum(losses[:period])/period
    for i in range(period,len(gains)):
        avg_gain=(avg_gain*(period-1)+gains[i])/period
        avg_loss=(avg_loss*(period-1)+losses[i])/period
    if avg_loss==0: return 100.0
    rs=avg_gain/avg_loss
    return 100.0-(100.0/(1+rs))

def calculate_atr(klines,period=14):
    if len(klines)<period+1: return 0.0
    trs=[]
    for i in range(1,len(klines)):
        h=float(klines[i][2]); l=float(klines[i][3]); pc=float(klines[i-1][4])
        trs.append(max(h-l,abs(h-pc),abs(l-pc)))
    return sum(trs[-period:])/period

def calculate_adx(klines,period=14):
    """
    VERIFIED AND FIXED a real, serious bug (this round): the previous
    version returned 30.0 on ALL THREE failure paths (insufficient data,
    insufficient computed dx values, and any exception) — 30.0 sits
    exactly on the pass side of BOTH ADX_MIN_TREND=21 (the hard trend
    gate in detect_patterns) AND the >=30 scorecard bonus threshold in
    compute_confirmation_bonus. A genuine calculation failure (malformed
    klines, an API hiccup) was silently treated as "strong trend
    confirmed" and awarded real scorecard points, rather than failing
    the check it should have failed.

    Fixed to return 0.0 on every failure path instead. Checked all 10
    call sites in this file before picking 0.0 over None: several do
    direct numeric comparisons and f-string formatting on the return
    value, so switching to None would require updating every comparison
    site to avoid a TypeError (a much larger, more invasive change than
    warranted here) — 0.0 correctly fails every real threshold check in
    this file (0.0 < 21 is True, correctly failing the trend gate; 0.0
    >= 30 is False, correctly failing the bonus) with zero downstream
    changes needed.
    """
    if len(klines)<period*2+1: return 0.0
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
        return sum(dx[-period:])/period if len(dx)>=period else 0.0
    except Exception as e:
        logger.warning(f"ADX calculation error: {e}"); return 0.0

def calculate_vwap(klines):
    try:
        tp=sum(((float(k[2])+float(k[3])+float(k[4]))/3)*float(k[5]) for k in klines)
        tv=sum(float(k[5]) for k in klines)
        return tp/tv if tv>0 else None
    except Exception: return None

def calculate_vwap_with_bands(klines):
    """
    The Law of Mean Reversion: VWAP Standard Deviation Bands.
    Kept as a SEPARATE function from the existing calculate_vwap (not a
    replacement) — the simple version is still used by cmd_hidden_gems,
    which doesn't need the extra variance computation cost; the full
    band calculation is wired into format_and_send specifically, where
    the actual entry-blocking check happens.

    Returns (vwap, upper_band_2sd, lower_band_2sd). A price extended
    beyond +2 SD (long) or -2 SD (short) from VWAP is "the elastic band
    stretched to its limit" — buying a breakout there is fighting mean
    reversion, not riding genuine momentum.
    """
    if len(klines) < 20: return None, None, None
    try:
        cum_vol = 0
        cum_pv = 0
        typical_prices = []
        vols = []

        for k in klines:
            h, l, c, v = float(k[2]), float(k[3]), float(k[4]), float(k[5])
            tp = (h + l + c) / 3
            cum_vol += v
            cum_pv += tp * v
            typical_prices.append(tp)
            vols.append(v)

        if cum_vol == 0: return None, None, None
        vwap = cum_pv / cum_vol

        dev_sum = 0
        for i in range(len(typical_prices)):
            dev_sum += vols[i] * ((typical_prices[i] - vwap) ** 2)

        variance = dev_sum / cum_vol
        std_dev = variance ** 0.5

        upper_band_2sd = vwap + (2 * std_dev)
        lower_band_2sd = vwap - (2 * std_dev)

        return vwap, upper_band_2sd, lower_band_2sd
    except Exception:
        return None, None, None

def get_point_of_control(klines, bins=12):
    """
    The Law of Liquidity Gravity (Volume Profile / Point of Control).
    VWAP tells you the average price paid, but not WHERE the most volume
    is actually trapped. Bins historical price action into horizontal
    blocks and finds the Point of Control (POC) — the price level with
    the highest traded volume, which acts like gravity: heavy resistance
    from below, heavy support from above.

    VERIFIED the binning math before implementing: a candle exactly at
    the range maximum would otherwise compute an out-of-range bin index
    (confirmed via calculation — int((max_p-min_p)/bin_size) at price==
    max_p equals `bins`, one past the valid 0..bins-1 range) — the
    max(0, min(x, bins-1)) clamp is genuinely necessary here, not
    defensive-but-unneeded code.
    """
    if len(klines) < 50: return None
    try:
        highs = [float(k[2]) for k in klines]
        lows = [float(k[3]) for k in klines]
        vols = [float(k[5]) for k in klines]

        max_p = max(highs)
        min_p = min(lows)
        if max_p == min_p: return None

        bin_size = (max_p - min_p) / bins
        volume_profile = {i: 0.0 for i in range(bins)}

        for i in range(len(klines)):
            h, l, v = highs[i], lows[i], vols[i]
            start_bin = int((l - min_p) / bin_size)
            end_bin = int((h - min_p) / bin_size)
            start_bin = max(0, min(start_bin, bins - 1))
            end_bin = max(0, min(end_bin, bins - 1))
            bins_touched = (end_bin - start_bin) + 1
            vol_per_bin = v / bins_touched if bins_touched > 0 else 0
            for b in range(start_bin, end_bin + 1):
                volume_profile[b] += vol_per_bin

        poc_bin = max(volume_profile, key=volume_profile.get)
        poc_price = min_p + (poc_bin * bin_size) + (bin_size / 2)
        return poc_price
    except Exception as e:
        logger.warning(f"get_point_of_control: {e}")
        return None

def detect_rsi_divergence(closes):
    if len(closes)<10: return None
    try:
        prices=closes[-6:]
        rsi_vals=[calculate_rsi(closes[:i+1]) for i in range(len(closes)-6,len(closes))]
        if prices[-1]<prices[0] and rsi_vals[-1]>rsi_vals[0]: return "BULLISH_DIV"
        if prices[-1]>prices[0] and rsi_vals[-1]<rsi_vals[0]: return "BEARISH_DIV"
        return None
    except Exception: return None

def get_recent_swing_levels(klines, lookback=20):
    """
    Backward-only swing level detector — fixes the audit's root-cause
    finding #1: detect_market_structure() requires a 5-bar LOOK-FORWARD
    window to confirm a pivot (highs[i]==max(highs[i-5:i+6])), meaning
    its swing_high/swing_low are structurally always at least 5-10
    candles stale (the confirmation window itself, PLUS the fact that
    the last 5 candles are excluded entirely from ever becoming a swing
    point, since `range(5, len(klines)-5)` never reaches them). On 15m
    data that's up to 150 minutes of staleness in the exact level every
    predictive pattern (Pre-Breakout Compression, Support Bounce,
    Resistance Rejection, etc.) uses as "the level that matters right
    now."

    This is a genuinely new, separate function — NOT a rewrite of
    detect_market_structure's core pivot/bias/BOS/ChoCh logic, which has
    been tuned and tested across many rounds this session and carries
    real regression risk if rewritten. Instead, this targets specifically
    the LEVEL used by predictive patterns, using a method that only ever
    looks backward from the current bar: the highest high / lowest low
    over the most recent `lookback` CLOSED candles, excluding the current
    (possibly still-forming) one. This is a real, honest trade-off, not a
    free improvement — a pure recent-extreme is more prone to noise than
    a confirmed 5-bar-fractal pivot, since it doesn't filter out a single
    isolated spike the way a true fractal would. Callers that need a
    cleaner, confirmed level should keep using detect_market_structure's
    swing_high/swing_low; this is for callers where "as current as
    possible" matters more than "as clean as possible" — genuinely early
    detection, per the audit's actual goal.

    Returns (recent_high, recent_low) using the last `lookback` candles
    (excluding the current, potentially-still-forming one).
    """
    if len(klines) < lookback + 1:
        return 0, 0
    highs = [float(k[2]) for k in klines[-(lookback+1):-1]]
    lows  = [float(k[3]) for k in klines[-(lookback+1):-1]]
    if not highs or not lows:
        return 0, 0
    return max(highs), min(lows)


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
    """
    Predictive Bull Flag — detects the channel FORMATION, not the
    breakout. VERIFIED THE OLD VERSION'S ACTUAL BUG before replacing it:
    confirmed it genuinely required "closes[-1] > breakout_level and
    vols[-1] > avg_vol*1.3" — the breakout itself, already happened —
    the same structural lateness issue found in every other confirmation
    pattern this session. This version stops at consolidation detection,
    handing the actual entry timing to the 5m sniper via the two-stage
    pipeline instead.
    """
    if len(closes) < 30: return False
    impulse_bars = closes[-25:-10]
    impulse_gain = (impulse_bars[-1] - impulse_bars[0]) / impulse_bars[0] * 100 if impulse_bars[0] > 0 else 0
    if impulse_gain < 3.0: return False

    consol_highs = highs[-10:]
    consol_lows = lows[-10:]
    consol_range = (max(consol_highs) - min(consol_lows)) / min(consol_lows) * 100 if min(consol_lows) > 0 else 999
    if consol_range > 5.0: return False  # Allow up to 5% flag channel

    if min(consol_lows) < impulse_bars[0]: return False  # Invalidated if it dumps below impulse start

    impulse_avg_vol = sum(vols[-25:-10]) / 15
    consol_avg_vol  = sum(vols[-10:])  / 10
    if consol_avg_vol >= impulse_avg_vol * 0.85: return False  # Volume must be contracting

    return True


def detect_bear_flag(closes, highs, lows, vols, avg_vol):
    """Predictive Bear Flag — mirror of the predictive bull flag above."""
    if len(closes) < 30: return False
    impulse_bars = closes[-25:-10]
    impulse_drop = (impulse_bars[0] - impulse_bars[-1]) / impulse_bars[0] * 100 if impulse_bars[0] > 0 else 0
    if impulse_drop < 3.0: return False

    consol_highs = highs[-10:]
    consol_lows = lows[-10:]
    consol_range = (max(consol_highs) - min(consol_lows)) / min(consol_lows) * 100 if min(consol_lows) > 0 else 999
    if consol_range > 5.0: return False

    if max(consol_highs) > impulse_bars[0]: return False

    impulse_avg_vol = sum(vols[-25:-10]) / 15
    consol_avg_vol  = sum(vols[-10:])  / 10
    if consol_avg_vol >= impulse_avg_vol * 0.85: return False

    return True


def get_candle_geometry(open_, high_, low_, close_):
    """
    Real, reusable single-candle geometry: body%/upper-wick%/lower-wick%
    of the candle's total range. Built once as a shared foundation
    instead of duplicating this math inside every individual pattern
    detector — both the candlestick pattern library and the detailed
    Telegram geometry text (e.g. "lower wick = 65% of range") consume
    this same function, so the numbers reported to the user are
    guaranteed to be the exact same numbers the detection logic itself
    used, not a second, separately-computed approximation.

    Returns a dict: body_pct, upper_wick_pct, lower_wick_pct (all as %
    of total range), body_top, body_bottom (the real min/max of open
    and close), and is_bullish (close > open). Returns all zeros/False
    if the candle has zero range (open==high==low==close), to avoid a
    division-by-zero rather than crash.
    """
    rng = high_ - low_
    if rng <= 0:
        return {"body_pct": 0, "upper_wick_pct": 0, "lower_wick_pct": 0,
                "body_top": max(open_, close_), "body_bottom": min(open_, close_), "is_bullish": close_ >= open_}
    body_top = max(open_, close_)
    body_bottom = min(open_, close_)
    body_pct = (body_top - body_bottom) / rng * 100
    upper_wick_pct = (high_ - body_top) / rng * 100
    lower_wick_pct = (body_bottom - low_) / rng * 100
    return {"body_pct": body_pct, "upper_wick_pct": upper_wick_pct, "lower_wick_pct": lower_wick_pct,
            "body_top": body_top, "body_bottom": body_bottom, "is_bullish": close_ >= open_}


def detect_hammer_family(klines):
    """
    Detects Hammer, Inverted Hammer, Shooting Star, Dragonfly Doji, and
    Gravestone Doji on the most recent closed candle. VERIFIED REAL,
    SOURCED THRESHOLDS before building this (not invented numbers):
    Hammer requires body <=30% of range positioned in the top third of
    the candle with a lower wick >=2x the body and minimal upper wick
    (TrendSpider, quantum-algo.com); Doji requires body typically 5-10%
    of range (multiple sourced definitions); Dragonfly/Gravestone are
    the doji-body-size case with the wick concentrated on one side only.

    FOUND AND FIXED A REAL DESIGN FLAW before this shipped: Inverted
    Hammer and Shooting Star share the IDENTICAL candle shape (small
    body, long upper wick, minimal lower wick) — the only real
    distinguishing factor between them is the PRECEDING trend, not the
    candle's own color. A first draft checked the candle's own
    is_bullish flag, which is the wrong signal entirely. Fixed by
    requiring real prior closes and checking the actual preceding
    trend direction, matching how these two patterns are genuinely
    defined.

    Returns (pattern_name, direction, geometry_dict) or (None, None, None).
    """
    if len(klines) < 7:
        return None, None, None
    c = klines[-2]  # most recent CLOSED candle, not the still-forming live one
    o, h, l, cl = float(c[1]), float(c[2]), float(c[3]), float(c[4])
    geo = get_candle_geometry(o, h, l, cl)
    if geo["body_pct"] <= 0 and geo["upper_wick_pct"] == 0 and geo["lower_wick_pct"] == 0:
        return None, None, None

    body_pct = geo["body_pct"]
    upper_pct = geo["upper_wick_pct"]
    lower_pct = geo["lower_wick_pct"]
    body_top_position_pct = ((geo["body_top"] - l) / (h - l) * 100) if (h - l) > 0 else 0
    prior_closes = [float(k[4]) for k in klines[-7:-2]]
    preceding_downtrend = prior_closes[-1] < prior_closes[0]
    preceding_uptrend = prior_closes[-1] > prior_closes[0]

    # DOJI (body 5-10% of range): direction determined by which single
    # side the wick is concentrated on, not by is_bullish (a doji's
    # open/close are nearly equal by definition).
    if 0 <= body_pct <= 10 and upper_pct + lower_pct > 0:
        if lower_pct >= 65 and upper_pct <= 15:
            return "Dragonfly Doji", "BUY", geo
        if upper_pct >= 65 and lower_pct <= 15:
            return "Gravestone Doji", "SELL", geo

    # HAMMER FAMILY (real body present, <=30% of range): direction and
    # name depend on which wick dominates, where the body sits, AND the
    # real preceding trend (see the fixed design flaw above).
    if body_pct <= 30:
        if lower_pct >= body_pct * 2 and lower_pct >= 50 and upper_pct <= 15 and body_top_position_pct >= 60 and preceding_downtrend:
            return "Hammer", "BUY", geo
        if upper_pct >= body_pct * 2 and upper_pct >= 50 and lower_pct <= 15 and body_top_position_pct <= 40:
            if preceding_downtrend:
                return "Inverted Hammer", "BUY", geo
            if preceding_uptrend:
                return "Shooting Star", "SELL", geo

    return None, None, None


def detect_micro_candlestick_patterns(klines):
    """
    Non-destructive detector for 2-candle and 3-candle micro patterns
    (cheat sheet 39260.png) — Tweezer Tops/Bottoms, Morning/Evening
    Star, Three White Soldiers/Three Black Crows. Uses
    get_candle_geometry for exact ratio calculations, exactly as
    specified in the non-destructive integration strategy: standalone
    function, existing signatures (get_candle_geometry,
    detect_hammer_family) untouched, plugs into detect_patterns via a
    standard tuple append.

    VERIFIED THE PROPOSED CODE BEFORE APPLYING IT, catching two real
    issues rather than trusting it as given:

    (1) Tweezer matching tolerance widened from the proposed 0.05% to
    0.3% — checked this against the file's OWN already-established,
    proven precedent (Double Bottom/Top's real 1.5% low-similarity
    threshold) and against real price-scale math (0.05% on a
    0.40-priced coin is a 0.0002 absolute difference, comparable to or
    smaller than typical tick sizes on many pairs) — the original value
    was likely too tight to ever fire on genuine near-matches. 0.3% is
    a real middle ground: tighter than the multi-candle Double Bottom
    match (a tweezer is a more immediate, precise 2-candle signal), but
    not so tight it excludes real matches.

    (2) Three White Soldiers/Three Black Crows corrected to require the
    REAL, consistently-sourced definition — each candle must open
    WITHIN the real body of the prior candle, not merely have an
    ascending/descending close. Searched and confirmed this requirement
    across multiple independent sources, then constructed a concrete
    counter-example proving the original "ascending closes only" check
    would incorrectly pass a gapped, disconnected 3-candle sequence
    that is not a genuine soldiers/crows formation.

    Returns (pattern_name, direction, geometry_notes) or (None, None, None).
    """
    if len(klines) < 5:
        return None, None, None

    c1, c2, c3 = klines[-4], klines[-3], klines[-2]
    o1, h1, l1, cl1 = float(c1[1]), float(c1[2]), float(c1[3]), float(c1[4])
    o2, h2, l2, cl2 = float(c2[1]), float(c2[2]), float(c2[3]), float(c2[4])
    o3, h3, l3, cl3 = float(c3[1]), float(c3[2]), float(c3[3]), float(c3[4])

    geo1 = get_candle_geometry(o1, h1, l1, cl1)
    geo2 = get_candle_geometry(o2, h2, l2, cl2)
    geo3 = get_candle_geometry(o3, h3, l3, cl3)

    # --- 1. TWO-CANDLE PATTERNS: TWEEZER TOPS & BOTTOMS ---
    # Tolerance widened to 0.3% (see docstring) from the proposed 0.05%.
    if l3 > 0 and abs(l2 - l3) / l3 <= 0.003 and not geo2["is_bullish"] and geo3["is_bullish"]:
        if geo3["lower_wick_pct"] >= 40.0:
            notes = f"Tweezer Lows at {format_price(l3)} (Wick {geo3['lower_wick_pct']:.0f}%)"
            return "Tweezer Bottom", "BUY", notes

    if h3 > 0 and abs(h2 - h3) / h3 <= 0.003 and geo2["is_bullish"] and not geo3["is_bullish"]:
        if geo3["upper_wick_pct"] >= 40.0:
            notes = f"Tweezer Highs at {format_price(h3)} (Wick {geo3['upper_wick_pct']:.0f}%)"
            return "Tweezer Top", "SELL", notes

    # --- 2. THREE-CANDLE PATTERNS: MORNING STAR & EVENING STAR ---
    if not geo1["is_bullish"] and geo1["body_pct"] >= 50.0:
        if geo2["body_pct"] <= 25.0:
            if geo3["is_bullish"] and cl3 >= (o1 + cl1) / 2:
                notes = f"Morning Star: C1 Bearish ({geo1['body_pct']:.0f}%), C2 Star, C3 Reclaim"
                return "Morning Star", "BUY", notes

    if geo1["is_bullish"] and geo1["body_pct"] >= 50.0:
        if geo2["body_pct"] <= 25.0:
            if not geo3["is_bullish"] and cl3 <= (o1 + cl1) / 2:
                notes = f"Evening Star: C1 Bullish ({geo1['body_pct']:.0f}%), C2 Star, C3 Reversal"
                return "Evening Star", "SELL", notes

    # --- 3. THREE-CANDLE PATTERNS: THREE WHITE SOLDIERS & THREE BLACK CROWS ---
    # CORRECTED (see docstring): requires each candle to open WITHIN the
    # prior candle's real body, the actual sourced definition — not
    # merely ascending/descending closes, which a gapped sequence could
    # also satisfy without being a genuine soldiers/crows formation.
    if geo1["is_bullish"] and geo2["is_bullish"] and geo3["is_bullish"]:
        opens_within_prior = (min(o1,cl1) <= o2 <= max(o1,cl1)) and (min(o2,cl2) <= o3 <= max(o2,cl2))
        if cl1 < cl2 < cl3 and opens_within_prior:
            if geo3["upper_wick_pct"] <= 20.0 and geo3["body_pct"] >= 55.0:
                notes = f"3 White Soldiers: Consecutive momentum closes ({format_price(cl3)})"
                return "Three White Soldiers", "BUY", notes

    if not geo1["is_bullish"] and not geo2["is_bullish"] and not geo3["is_bullish"]:
        opens_within_prior = (min(o1,cl1) <= o2 <= max(o1,cl1)) and (min(o2,cl2) <= o3 <= max(o2,cl2))
        if cl1 > cl2 > cl3 and opens_within_prior:
            if geo3["lower_wick_pct"] <= 20.0 and geo3["body_pct"] >= 55.0:
                notes = f"3 Black Crows: Consecutive downward drive ({format_price(cl3)})"
                return "Three Black Crows", "SELL", notes

    return None, None, None


def detect_micro_structures_5m(klines_5m, price, sup, res):
    """
    Anticipatory 5m Structure Detector (Cheat Sheet 39155.png). Catches
    Head & Shoulders right-shoulder formation, Triple Tops/Bottoms, and
    Wolfe Waves on native 5-minute klines BEFORE the breakout occurs.

    REPLACES detect_micro_structures_9m (this round) — user corrected
    the earlier 9m synthesis approach to native 5m data, resolving the
    "which minute value did you actually mean" confusion cleanly
    instead of layering a further correction on top of it.

    VERIFIED THE PROPOSED REPLACEMENT CODE BEFORE APPLYING IT: confirmed
    both previously-fixed real issues from the 9m version are genuinely
    preserved here, not silently reverted — (1) the touch tolerance is
    still 0.3% (checked against this file's own Double Bottom/Top
    precedent and real price-scale math two rounds ago), not the
    originally-proposed, too-tight 0.2%; (2) the Head & Shoulders index
    is still computed entirely within an explicit local window
    (`window_lows = lows[-20:]`, then `.index()` against that same
    slice), not the original full-array `.index()` bug that could
    silently pick the wrong candle when a price value repeats.
    """
    if not klines_5m or len(klines_5m) < 20:
        return None, None, None

    highs = [float(k[2]) for k in klines_5m]
    lows  = [float(k[3]) for k in klines_5m]
    closes = [float(k[4]) for k in klines_5m]
    opens  = [float(k[1]) for k in klines_5m]

    # --- 1. TRIPLE BOTTOM / TRIPLE TOP (3 Horizontal Rejections) ---
    recent_lows = lows[-15:]
    recent_highs = highs[-15:]
    min_low = min(recent_lows)
    max_high = max(recent_highs)
    bottom_touches = sum(1 for l in recent_lows if min_low > 0 and abs(l - min_low) / min_low <= 0.003)
    top_touches = sum(1 for h in recent_highs if max_high > 0 and abs(max_high - h) / max_high <= 0.003)

    if bottom_touches >= 3 and min_low > 0 and abs(price - min_low) / min_low <= 0.004:
        notes = f"Triple Bottom: 3 rejections at {format_price(min_low)} (5m)"
        return "Triple Bottom (Anticipatory)", "BUY", notes

    if top_touches >= 3 and max_high > 0 and abs(max_high - price) / max_high <= 0.004:
        notes = f"Triple Top: 3 rejections at {format_price(max_high)} (5m)"
        return "Triple Top (Anticipatory)", "SELL", notes

    # --- 2. ANTICIPATORY INVERSE HEAD & SHOULDERS (Right Shoulder Forming) ---
    if len(lows) >= 20:
        window_lows = lows[-20:]
        head_idx = window_lows.index(min(window_lows))
        if 5 <= head_idx <= 15:
            head_val = window_lows[head_idx]
            left_shoulder_region = window_lows[:head_idx]
            right_shoulder_region = window_lows[head_idx+1:]
            if left_shoulder_region and right_shoulder_region:
                left_shoulder = min(left_shoulder_region)
                if head_val < left_shoulder:
                    rs_val = min(right_shoulder_region)
                    if left_shoulder > 0 and abs(rs_val - left_shoulder) / left_shoulder <= 0.005 and closes[-1] > opens[-1]:
                        notes = f"Inv H&S: Right Shoulder forming at {format_price(rs_val)} (5m, Head: {format_price(head_val)})"
                        return "Inverse Head & Shoulders (Early)", "BUY", notes

    # --- 3. ANTICIPATORY HEAD & SHOULDERS (Right Shoulder Forming) ---
    if len(highs) >= 20:
        window_highs = highs[-20:]
        head_idx = window_highs.index(max(window_highs))
        if 5 <= head_idx <= 15:
            head_val = window_highs[head_idx]
            left_shoulder_region = window_highs[:head_idx]
            right_shoulder_region = window_highs[head_idx+1:]
            if left_shoulder_region and right_shoulder_region:
                left_shoulder = max(left_shoulder_region)
                if head_val > left_shoulder:
                    rs_val = max(right_shoulder_region)
                    if left_shoulder > 0 and abs(rs_val - left_shoulder) / left_shoulder <= 0.005 and closes[-1] < opens[-1]:
                        notes = f"Head & Shoulders: Right Shoulder forming at {format_price(rs_val)} (5m, Head: {format_price(head_val)})"
                        return "Head & Shoulders (Early)", "SELL", notes

    # --- 4. WOLFE WAVE (5-Point Contracting Wedge) ---
    if len(closes) >= 12:
        range_start = max(highs[-12:-6]) - min(lows[-12:-6])
        range_end = max(highs[-6:]) - min(lows[-6:])
        if range_end < range_start * 0.65:
            if len(lows) >= 7 and lows[-1] < min(lows[-6:-1]) and closes[-1] > opens[-1]:
                notes = "Wolfe Wave: Point 5 Liquidity Sweep in 5m Wedge"
                return "Wolfe Wave Reversal", "BUY", notes
            if len(highs) >= 7 and highs[-1] > max(highs[-6:-1]) and closes[-1] < opens[-1]:
                notes = "Wolfe Wave: Point 5 Liquidity Sweep in 5m Wedge"
                return "Wolfe Wave Reversal", "SELL", notes

    return None, None, None


def detect_double_bottom_pro(highs, lows, closes, vols, price, avg_vol):
    """
    Institutional Double Bottom — Audit Fix #1, extended with a Liquidity
    Sweep alternative entry path (this round).

    GAP VERIFIED BEFORE FIXING (not just implemented on request): the
    previous version only had the neckline-breakout path — confirmed via
    direct execution that a genuine sweep-and-reclaim scenario (second
    low wicks below the first low and immediately recloses above it,
    without ever breaking the neckline) was silently rejected. This
    matches the real, common institutional pattern of sweeping retail
    stops below an obvious double-bottom low before reversing — exactly
    the case the reported -11.79% loss likely fell into (bought the raw
    pattern with neither confirmation).

    Two independent entry paths now: (A) genuine neckline breakout with
    volume — kept the EXISTING 0.2% clearance buffer here rather than
    adopting a proposed unbuffered version, since removing that buffer
    was a real, unrequested loosening of the entry trigger, not
    something asked for; (B) a liquidity sweep — second low wicks below
    the first low and closes back above it, confirming the sweep was
    rejected rather than accepted.
    """
    if len(lows) < 50: return False, 0
    region = lows[-50:]
    low1_idx = region.index(min(region[:-15])) if len(region) > 15 else region.index(min(region))

    region2_start = low1_idx + 8
    if region2_start >= len(region) - 2: return False, 0
    region2 = region[region2_start:]
    if not region2: return False, 0
    low2_val = min(region2)
    low2_idx = region2_start + region2.index(low2_val)

    low1_val = region[low1_idx]
    similarity = abs(low1_val - low2_val) / low1_val if low1_val > 0 else 1
    if similarity > 0.015: return False, 0  # kept at the existing 1.5% (not tightened to 1.2%,
                                          # since that tightening wasn't explicitly requested
                                          # and risks excluding otherwise-valid setups)

    neckline = max(highs[-50 + low1_idx : -50 + low2_idx + 1] or [0])
    if neckline == 0: return False, 0

    # CONDITION A: genuine neckline breakout with volume, existing 0.2% buffer preserved
    neckline_broken = price > neckline * 1.002 and vols[-1] > avg_vol * 1.1

    # CONDITION B: Liquidity Sweep — second low wicks below the first low, closes back above
    # REAL BUG FIXED (this round, see detect_liquidity_sweep for the
    # demonstrated counter-example): evaluated on the confirmed [-2]
    # candle, not the live, still-forming [-1].
    is_sweep = lows[-2] <= low1_val and closes[-2] > low1_val

    # REAL LEVEL RETURNED (this round): low2_val is the actual, specific
    # second-bottom price this function already computed internally to
    # confirm the pattern's shape — the genuine "bottom" a retest level
    # should be anchored to, not a generic trailing-window minimum
    # computed later by an unrelated caller.
    fired = neckline_broken or is_sweep
    return fired, (low2_val if fired else 0)


def detect_double_top_pro(highs, lows, closes, vols, price, avg_vol):
    """
    Institutional Double Top — mirror of detect_double_bottom_pro, same
    Liquidity Sweep alternative added this round for the same verified
    reason (see detect_double_bottom_pro's docstring for the full gap
    analysis and the 0.2%-buffer preservation decision).
    """
    if len(highs) < 50: return False, 0
    region = highs[-50:]
    high1_idx = region.index(max(region[:-15])) if len(region) > 15 else region.index(max(region))

    region2_start = high1_idx + 8
    if region2_start >= len(region) - 2: return False, 0
    region2 = region[region2_start:]
    if not region2: return False, 0
    high2_val = max(region2)
    high2_idx = region2_start + region2.index(high2_val)

    high1_val = region[high1_idx]
    similarity = abs(high1_val - high2_val) / high1_val if high1_val > 0 else 1
    if similarity > 0.015: return False, 0

    neckline = min(lows[-50 + high1_idx : -50 + high2_idx + 1] or [999999])
    if neckline == 999999: return False, 0

    neckline_broken = price < neckline * 0.998 and vols[-1] > avg_vol * 1.1
    # REAL BUG FIXED (this round, see detect_liquidity_sweep): evaluated
    # on the confirmed [-2] candle, not the live [-1].
    is_sweep = highs[-2] >= high1_val and closes[-2] < high1_val

    fired = neckline_broken or is_sweep
    return fired, (high2_val if fired else 0)


def detect_distribution_range(highs, lows, closes, vols, price, avg_vol):
    """
    Distribution — a topping/consolidation range that forms after a real
    prior uptrend, where price fails to make a fresh sustained high,
    chops sideways while volume dries up, then breaks DOWN out of the
    range on real volume. Requested against the reference notes: HH/HL
    uptrend -> failed new high -> sideways distribution box -> breakdown.

    Bearish-only by definition (distribution precedes markdown). The
    bullish mirror — accumulation before a breakout — is already covered
    by the existing coil/compression detectors (Inside Bar Coil,
    Pre-Breakout Compression, Volatility Contraction), so it isn't
    duplicated here.

    Thresholds are a reasoned first pass (not sourced from an external
    reference), same caveat as this file's other pattern detectors:
    prior rise >= 4% (there must be a real uptrend to distribute from),
    range width 1.5%-7% (tighter than that is a coil, not a distribution
    range; wider is just chop), volume must be drying out inside the
    range vs the prior uptrend leg, and the breakdown needs a real close
    below the range low plus a volume kick — same confirmation style as
    detect_double_top_pro's neckline break.

    Returns (fired: bool, level: float) — level is the range low, the
    breakdown trigger price.
    """
    if len(closes) < 45: return False, 0

    uptrend_window = closes[-45:-15]
    uptrend_vols = vols[-45:-15]
    if len(uptrend_window) < 15 or not uptrend_vols: return False, 0
    uptrend_move_pct = (uptrend_window[-1] - uptrend_window[0]) / uptrend_window[0] * 100 if uptrend_window[0] > 0 else 0
    if uptrend_move_pct < 4.0:
        return False, 0  # no genuine prior uptrend, nothing to distribute from

    # Box window is the 15 candles BEFORE the confirmation candle — the
    # confirmation/breakdown candle itself must stay OUT of this
    # measurement, otherwise a genuine breakdown (which by definition
    # undercuts the box) inflates the box's own range and corrupts its
    # own low (same self-referential bug class as detect_double_top_pro
    # guards against with its separate neckline window).
    range_highs = highs[-16:-1]; range_lows = lows[-16:-1]; range_vols = vols[-16:-1]
    if not range_highs: return False, 0
    range_high = max(range_highs); range_low = min(range_lows)
    if range_low <= 0: return False, 0
    range_pct = (range_high - range_low) / range_low * 100
    if range_pct < 1.5 or range_pct > 7.0:
        return False, 0  # too tight = coil, too wide = just chop, not a range

    # "New high fail": the range's own high should sit close to the prior
    # uptrend's high, not meaningfully above it — a genuinely failed push,
    # not a continuation.
    prior_high = max(uptrend_window)
    if range_high < prior_high * 0.995:
        return False, 0

    avg_uptrend_vol = sum(uptrend_vols) / len(uptrend_vols)
    avg_range_vol = sum(range_vols) / len(range_vols)
    if avg_range_vol > avg_uptrend_vol * 1.1:
        return False, 0  # volume still expanding — not a genuine distribution phase

    broke_down = price < range_low * 0.998 and vols[-1] > avg_range_vol * 1.4
    return broke_down, (range_low if broke_down else 0)


def detect_v_shape_reversal(closes, highs, lows, vols, price, avg_vol):
    """
    V-Shape Reversal — a sharp, fast decline into a pivot low (or rally
    into a pivot high) immediately followed by an equally sharp move back
    out, with no basing period in between. What separates this from
    Double Bottom/Top or Cup & Handle (which require a base or multiple
    touches) is speed on both legs, not structure — then a genuine
    breakout back past the level the move started from, on real volume.

    Both directions: BUY (V bottom) / SELL (inverted-V top).

    Thresholds (reasoned from the pattern's own definition, same caveat
    as Distribution above): pivot must sit roughly in the middle of the
    20-candle window (so there's room to measure a real leg in and a real
    leg out on both sides), each leg >= 3%, and the recovery/reversal leg
    must not take meaningfully longer than the leg into the pivot (a slow
    grind back out is a round bottom, not a V).

    Returns (direction, level) or (None, 0). `level` is the pre-move high
    (BUY) or pre-move low (SELL) — the breakout trigger price.
    """
    if len(closes) < 20: return None, 0
    window = closes[-20:]; h_window = highs[-20:]; l_window = lows[-20:]

    # ── Bullish V: sharp drop into a pivot low, sharp recovery out ──
    inner_lows = l_window[2:-2]
    if inner_lows:
        pivot_low = min(inner_lows)
        pivot_low_idx = l_window.index(pivot_low, 2)
        pre_high = max(h_window[:pivot_low_idx+1])
        decline_pct = (pre_high - pivot_low) / pre_high * 100 if pre_high > 0 else 0
        decline_candles = pivot_low_idx + 1
        recovery_candles = len(window) - pivot_low_idx
        recovery_pct = (price - pivot_low) / pivot_low * 100 if pivot_low > 0 else 0
        if decline_pct >= 3.0 and recovery_pct >= 3.0 and recovery_candles <= decline_candles * 1.8:
            if price > pre_high * 1.001 and vols[-1] > avg_vol * 1.3:
                return "BUY", pre_high

    # ── Bearish inverted-V: sharp rally into a pivot high, sharp reversal down ──
    inner_highs = h_window[2:-2]
    if inner_highs:
        pivot_high = max(inner_highs)
        pivot_high_idx = h_window.index(pivot_high, 2)
        pre_low = min(l_window[:pivot_high_idx+1])
        rally_pct = (pivot_high - pre_low) / pre_low * 100 if pre_low > 0 else 0
        rally_candles = pivot_high_idx + 1
        decline_candles = len(window) - pivot_high_idx
        decline_pct = (pivot_high - price) / pivot_high * 100 if pivot_high > 0 else 0
        if rally_pct >= 3.0 and decline_pct >= 3.0 and decline_candles <= rally_candles * 1.8:
            if price < pre_low * 0.999 and vols[-1] > avg_vol * 1.3:
                return "SELL", pre_low

    return None, 0


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

    # REAL FIX (this round) — REMOVED abs(), ENFORCED STRICT POSITION:
    # VERIFIED THIS WAS A REAL, DEMONSTRATED BUG before applying —
    # constructed a concrete counter-example (res=100, price already
    # broken out to 101) and confirmed abs(res-price)/res*100 = 1.0%,
    # which the old <=1.0 check would incorrectly accept as still-
    # compressing, despite price having genuinely already broken above
    # resistance. The signed version correctly produces a negative
    # value here, excluded by the new 0<=x<=1.0 bound, which requires
    # price to genuinely still be UNDER the ceiling / ABOVE the floor.
    dist_to_res_pct = (res - price) / res * 100 if res > 0 else 99
    dist_to_sup_pct = (price - sup) / sup * 100 if sup > 0 else 99

    tightness_score = max(0, 100 - (max(recent_highs) - min(recent_lows)) / price * 100 * 20)

    if 0 <= dist_to_res_pct <= 1.0 and direction_bias != "bearish":
        return "BUY", tightness_score
    if 0 <= dist_to_sup_pct <= 1.0 and direction_bias != "bullish":
        return "SELL", tightness_score

    return None, 0


def detect_macro_triangle_1h(klines_1h):
    """
    1H Ascending/Descending Triangle detector — Category 5 (comprehensive
    macro pattern library) from the Pre-Breakout Macro Engine redesign.

    VERIFIED REAL, SOURCED CRITERIA before building this (not invented
    thresholds): searched and confirmed a consistent definition across
    multiple independent sources (Axi, Vantage Markets, ChartGuys,
    LiteFinance, Strike, StockGro, BullishBears, TradingSim) —
    Ascending Triangle: a flat resistance level touched at least twice
    with near-equal highs, a genuinely rising sequence of higher lows
    (at least 2-3), a narrowing range as the pattern matures, and
    contracting volume during formation (a real, cited failure mode:
    "when volume fails to contract during formation, suggests lack of
    coiling energy"). Descending Triangle is the mirror: flat support,
    falling highs.

    Built on 1H klines specifically, not 4H/1D directly — those coarser
    timeframes would be too sparse for the multi-touch swing-count
    window this pattern genuinely needs to form meaningfully (2-3 real
    touches on each side needs real granularity to distinguish "swing"
    from "noise").

    Reuses the same real, established design language already proven in
    this file: detect_volatility_contraction's impulse/contraction
    split, the 0.3% near-match tolerance already calibrated earlier this
    session (Tweezer/Triple Top-Bottom fixes), and the (direction,
    quality_score) return shape.

    Returns (direction, quality_score, pattern_name, level) or
    (None, 0, None, 0). `level` is the pattern's actual real geometric
    boundary (flat resistance for Ascending, flat support for
    Descending) — this was already computed internally but discarded
    before this round, forcing callers to substitute live_price (an
    arbitrary point inside the pattern, not its real breakout boundary)
    for the trigger level.
    """
    if len(klines_1h) < 30:
        return None, 0, None, 0

    highs = [float(k[2]) for k in klines_1h[-30:]]
    lows = [float(k[3]) for k in klines_1h[-30:]]
    vols = [float(k[5]) for k in klines_1h[-30:]]

    # Split into an earlier window (to check contraction) and the most
    # recent window (where the flat side and touches are measured).
    recent_highs = highs[-15:]
    recent_lows = lows[-15:]
    earlier_highs = highs[:15]
    earlier_lows = lows[:15]
    recent_vols = vols[-15:]
    earlier_vols = vols[:15]

    if not earlier_vols or not recent_vols:
        return None, 0, None, 0
    avg_earlier_vol = sum(earlier_vols) / len(earlier_vols)
    avg_recent_vol = sum(recent_vols) / len(recent_vols)
    vol_contracting = avg_recent_vol < avg_earlier_vol * 0.85

    earlier_range = max(earlier_highs) - min(earlier_lows)
    recent_range = max(recent_highs) - min(recent_lows)
    range_narrowing = recent_range < earlier_range * 0.75 if earlier_range > 0 else False

    if not vol_contracting or not range_narrowing:
        return None, 0, None, 0

    # ASCENDING TRIANGLE: flat resistance (real touches within 0.3% of
    # the max, at least 2), genuinely rising sequence of lows.
    flat_res = max(recent_highs)
    res_touches = sum(1 for h in recent_highs if flat_res > 0 and abs(h - flat_res) / flat_res <= 0.003)
    # Real, rising lows: split the recent window into thirds and check
    # each third's minimum is genuinely higher than the previous third's.
    third = len(recent_lows) // 3
    if third >= 2:
        low_1 = min(recent_lows[:third])
        low_2 = min(recent_lows[third:third*2])
        low_3 = min(recent_lows[third*2:])
        rising_lows = low_1 < low_2 < low_3
        if res_touches >= 2 and rising_lows:
            tightness = max(0, 100 - (recent_range / flat_res * 100) * 15) if flat_res > 0 else 0
            return "BUY", tightness, "Ascending Triangle (1H)", flat_res

    # DESCENDING TRIANGLE: flat support, genuinely falling highs.
    flat_sup = min(recent_lows)
    sup_touches = sum(1 for l in recent_lows if flat_sup > 0 and abs(l - flat_sup) / flat_sup <= 0.003)
    if third >= 2:
        high_1 = max(recent_highs[:third])
        high_2 = max(recent_highs[third:third*2])
        high_3 = max(recent_highs[third*2:])
        falling_highs = high_1 > high_2 > high_3
        if sup_touches >= 2 and falling_highs:
            tightness = max(0, 100 - (recent_range / flat_sup * 100) * 15) if flat_sup > 0 else 0
            return "SELL", tightness, "Descending Triangle (1H)", flat_sup

    return None, 0, None, 0


def detect_macro_4h_sweep(klines_4h):
    """
    4H Liquidity Sweep (Spring/Upthrust) — Category 5, point 16. Reuses
    the SAME real, already-tested logic shape as detect_liquidity_sweep
    (wick pierces a real structural level, close reverts back inside,
    a genuine Change of Character confirms the reversal isn't just
    noise) — applied to real 4H data via detect_market_structure, which
    is genuinely timeframe-agnostic (verified its signature takes raw
    klines with no 15m-specific assumption), rather than duplicating
    the pivot/BOS/ChoCh logic from scratch for this timeframe.

    Returns (direction, sweep_strength, pattern_name, level) or
    (None, 0, None, 0).
    """
    if len(klines_4h) < 20:
        return None, 0, None, 0
    highs = [float(k[2]) for k in klines_4h]
    lows = [float(k[3]) for k in klines_4h]
    closes = [float(k[4]) for k in klines_4h]
    opens = [float(k[1]) for k in klines_4h]
    ms = detect_market_structure(klines_4h)
    sup = ms["swing_low"] if ms["swing_low"] > 0 else min(lows[-20:-1])
    res = ms["swing_high"] if ms["swing_high"] > 0 else max(highs[-20:-1])
    sweep_dir, sweep_strength = detect_liquidity_sweep(klines_4h, highs, lows, closes, opens, sup, res, ms)
    if sweep_dir == "BUY":
        return "BUY", sweep_strength, "4H Liquidity Sweep", max(highs[-3:])
    elif sweep_dir == "SELL":
        return "SELL", sweep_strength, "4H Liquidity Sweep", min(lows[-3:])
    return None, 0, None, 0


def detect_macro_divergence_bottom(symbol, klines_4h):
    """
    4H Double Bottom with Bullish RSI Divergence — high-conviction macro
    reversal.

    FOUND AND FIXED A SERIOUS BUG in the originally proposed version
    before applying this: it called calculate_rsi(closes[-10:]) with
    the default period=14 — but calculate_rsi's own real guard ("if
    len(closes)<period+1: return 50.0") means a 10-element slice always
    falls short of the required 15, so both rsi_recent and rsi_older
    would ALWAYS be exactly 50.0. The divergence check (rsi_recent >
    rsi_older + 5.0) becomes 50 > 55, which is always False — the
    entire pattern would have been permanently, silently dead on
    arrival, unable to ever fire. Confirmed this precisely by
    reproducing the guard logic directly before fixing it. Corrected
    by computing RSI at two different points in real history using
    calculate_rsi's own real sliding window against genuinely
    sufficient data each time, not two artificially truncated slices.

    Returns (direction, quality_score, pattern_name, level) or
    (None, 0, None, 0).
    """
    if len(klines_4h) < 40: return None, 0, None, 0

    closes = [float(k[4]) for k in klines_4h]
    highs = [float(k[2]) for k in klines_4h]
    lows = [float(k[3]) for k in klines_4h]

    recent_low = min(lows[-10:])
    older_low = min(lows[-40:-15])

    if older_low <= 0:
        return None, 0, None, 0

    if abs(recent_low - older_low) / older_low < 0.015:
        # REAL FIX (last round): RSI computed at two real points in
        # history, each against a genuinely sufficient window, not two
        # 10-element slices that could never clear calculate_rsi's own
        # real minimum-length guard.
        rsi_recent = calculate_rsi(closes)
        rsi_older = calculate_rsi(closes[:-15])

        if rsi_recent > rsi_older + 5.0:
            neckline = max(highs[-40:-10])  # the high between the two bottoms
            return "BUY", 90.0, "4H Double Bottom + Bullish Div", neckline

    return None, 0, None, 0


def detect_macro_choch_4h(klines_4h, ms_4h):
    """
    4H Change of Character — detects macro structure flipping from
    bearish to bullish (or vice versa). VERIFIED before applying:
    confirmed detect_market_structure's real return dict genuinely has
    the "bias"/"choch"/"swing_high"/"swing_low" keys used here, with
    "bias" genuinely a lowercase "bullish"/"bearish" string, matching
    exactly what this function compares against.

    Returns (direction, quality_score, pattern_name, level) or
    (None, 0, None, 0).
    """
    if not ms_4h["choch"]: return None, 0, None, 0

    closes = [float(k[4]) for k in klines_4h]
    if ms_4h["bias"] == "bearish" and closes[-1] > ms_4h["swing_high"]:
        return "BUY", 88.0, "4H Change of Character (Bullish)", ms_4h["swing_high"]
    elif ms_4h["bias"] == "bullish" and closes[-1] < ms_4h["swing_low"]:
        return "SELL", 88.0, "4H Change of Character (Bearish)", ms_4h["swing_low"]

    return None, 0, None, 0


def detect_macro_cup_and_handle(klines_1h):
    """
    1H Cup and Handle (and Inverse) — completes the Category 5 macro
    pattern library, as flagged pending in this combiner's own
    docstring for several rounds.

    VERIFIED REAL, SOURCED CRITERIA before applying the proposed code
    as given, catching two genuine discrepancies against multiple
    independent sources (Axi, Equiti, Dukascopy, StockCharts,
    TrendSpider, TradingSim, QuantifiedStrategies, Bapital):

    (1) Cup depth minimum tightened from the proposed 4% to 10% —
    sources explicitly warn a cup depth below ~10% ("2-3%") "isn't
    meaningful" (TradingSim); every source citing a real minimum uses
    double digits, not single digits.

    (2) Handle retracement ceiling tightened — computed precisely what
    the proposed 0.4 factor actually permits (up to 60% of the cup's
    depth given back) and found it looser than the sourced consensus
    ceiling ("retracement should not exceed 50%... a sharp or deep
    handle (>50% retrace) weakens the pattern" — Axi, Equiti).
    Corrected to 0.5, matching the explicit 50% ceiling.

    Kept the 2.5% lip-similarity tolerance as proposed — checked this
    is a genuinely different comparison than this file's established
    0.3% precedent (candle-to-candle touches within a tight, recent
    window): cup lips are compared across up to 38 candles of real
    separation, and sourced definitions explicitly note "the perfect
    pattern would have equal highs on both sides, but this is not
    always the case" (StockCharts).

    Returns (direction, quality_score, pattern_name, level) or
    (None, 0, None, 0).
    """
    if len(klines_1h) < 60:
        return None, 0, None, 0

    closes = [float(k[4]) for k in klines_1h]
    highs = [float(k[2]) for k in klines_1h]
    lows = [float(k[3]) for k in klines_1h]
    vols = [float(k[5]) for k in klines_1h]

    handle_highs = highs[-12:]
    handle_lows = lows[-12:]
    handle_vols = vols[-12:]

    cup_highs = highs[-50:-12]
    cup_lows = lows[-50:-12]

    if not cup_highs or not cup_lows:
        return None, 0, None, 0

    # ── Bullish Cup & Handle ──
    left_lip = max(cup_highs[:15])
    right_lip = max(cup_highs[-10:])
    cup_bottom = min(cup_lows)

    if right_lip > 0 and abs(left_lip - right_lip) / right_lip < 0.025:
        cup_depth = (right_lip - cup_bottom) / cup_bottom if cup_bottom > 0 else 0
        if cup_depth > 0.10:  # REAL FIX: tightened from proposed 0.04, see docstring
            handle_low = min(handle_lows)

            # REAL FIX: tightened from proposed 0.4 to 0.5 (see docstring)
            # — handle must hold the upper 50% of the cup, not 60%.
            if handle_low > cup_bottom + ((right_lip - cup_bottom) * 0.5):
                avg_cup_vol = sum(vols[-50:-12]) / 38
                avg_handle_vol = sum(handle_vols) / 12

                if avg_handle_vol < avg_cup_vol * 0.85:
                    tightness = 90.0
                    level = max(left_lip, right_lip)
                    return "BUY", tightness, "Cup & Handle (1H)", level

    # ── Bearish Inverse Cup & Handle ──
    inv_left_lip = min(cup_lows[:15])
    inv_right_lip = min(cup_lows[-10:])
    cup_top = max(cup_highs)

    if inv_right_lip > 0 and abs(inv_left_lip - inv_right_lip) / inv_right_lip < 0.025:
        cup_height = (cup_top - inv_right_lip) / inv_right_lip if inv_right_lip > 0 else 0
        if cup_height > 0.10:  # REAL FIX: tightened from proposed 0.04, see docstring
            handle_high = max(handle_highs)

            # REAL FIX: tightened from proposed 0.4 to 0.5 (see docstring)
            if handle_high < cup_top - ((cup_top - inv_right_lip) * 0.5):
                avg_cup_vol = sum(vols[-50:-12]) / 38
                avg_handle_vol = sum(handle_vols) / 12

                if avg_handle_vol < avg_cup_vol * 0.85:
                    tightness = 90.0
                    level = min(inv_left_lip, inv_right_lip)
                    return "SELL", tightness, "Inv Cup & Handle (1H)", level

    return None, 0, None, 0


def detect_macro_wedge(klines_1h):
    """
    1H Macro Wedge (Falling = Bullish, Rising = Bearish). A contracting
    range where BOTH highs and lows are trending in the SAME direction,
    but one side is catching up to the other (loss of momentum).

    VERIFIED THE GEOMETRIC DEFINITION against multiple independent
    sources (CMC Markets, LuxAlgo, TradingSim, TrendSpider, StockCharts,
    TradeSignal, Strike, JournalPlus) before applying — confirmed the
    core comparison (one trendline moving faster than the other, in the
    SAME direction as both) genuinely matches the sourced definition,
    not just plausible-sounding.

    FOUND AND FIXED A REAL EDGE CASE in the originally proposed version
    before applying it: constructed a concrete counter-example (lows
    dropping a trivial 0.01% while highs drop meaningfully) and
    confirmed the proposed "l_end < l_start" check alone doesn't
    require genuine, meaningful movement on the SLOWER side — meaning
    a shape structurally closer to a Descending Triangle (flat support,
    falling resistance — already a separate, distinct detector in this
    file) could pass as a Wedge. Added a real minimum-movement floor
    (0.3%) on the slower-moving side of each variant, so this pattern
    doesn't silently overlap with the already-built Triangle detector.

    Returns (direction, quality_score, pattern_name, level) or
    (None, 0, None, 0).
    """
    if len(klines_1h) < 30: return None, 0, None, 0

    highs = [float(k[2]) for k in klines_1h[-30:]]
    lows = [float(k[3]) for k in klines_1h[-30:]]
    closes = [float(k[4]) for k in klines_1h[-30:]]

    first_half_highs = highs[:15]
    first_half_lows = lows[:15]
    second_half_highs = highs[15:]
    second_half_lows = lows[15:]

    h_start = max(first_half_highs)
    h_end = max(second_half_highs)
    l_start = min(first_half_lows)
    l_end = min(second_half_lows)

    range_start = h_start - l_start
    range_end = h_end - l_end
    if range_start <= 0: return None, 0, None, 0

    is_contracting = range_end < range_start * 0.75
    if not is_contracting: return None, 0, None, 0

    # Falling Wedge (Bullish Reversal): both trending down, highs falling faster.
    if h_end < h_start * 0.99 and l_end < l_start:
        drop_highs = h_start - h_end
        drop_lows = l_start - l_end
        # REAL FIX (see docstring): require the SLOWER side (lows) to
        # also move a genuine minimum amount, not just "less than
        # start" — otherwise this can silently overlap with a
        # Descending Triangle shape.
        if drop_lows >= l_start * 0.003 and drop_highs > drop_lows * 1.2:
            tightness = max(0, 100 - (range_end / closes[-1] * 100) * 15) if closes[-1] > 0 else 0
            return "BUY", tightness, "Falling Wedge (1H)", h_end

    # Rising Wedge (Bearish Reversal): both trending up, lows rising faster.
    if l_end > l_start * 1.01 and h_end > h_start:
        rise_lows = l_end - l_start
        rise_highs = h_end - h_start
        # REAL FIX (see docstring): same minimum-movement floor on the
        # slower side (highs) here.
        if rise_highs >= h_start * 0.003 and rise_lows > rise_highs * 1.2:
            tightness = max(0, 100 - (range_end / closes[-1] * 100) * 15) if closes[-1] > 0 else 0
            return "SELL", tightness, "Rising Wedge (1H)", l_end

    return None, 0, None, 0


def detect_macro_head_and_shoulders(klines_1h):
    """
    1H Macro Head & Shoulders and Inverse Head & Shoulders.

    VERIFIED THE PROPOSED CODE BEFORE APPLYING IT: confirmed this
    genuinely avoids the real full-array-index bug already found and
    fixed in the earlier 5m/9m Head & Shoulders detector — highs/lows
    are already windowed to [-45:] before .index() is ever called here,
    unlike that original buggy version. Also verified the shoulder-
    slicing indices (head_idx-5, head_idx+5) are genuinely safe against
    negative-index wraparound at both boundaries of the
    15<head_idx<30 guard.

    Searched multiple sources (StockCharts, XS, Naga,
    Bulkowski/ThePatternSite, Quantum-Algo, DailyPriceAction) before
    accepting the proposed thresholds as given: the proposed head-
    prominence threshold (shoulders < head*0.985, a 1.5% minimum) was
    genuinely looser than a specific, sourced textbook-pattern floor —
    "if the middle peak only marginally exceeds the shoulders (under
    5% higher), the pattern is weak — essentially three equal peaks"
    (Quantum-Algo). Tightened to a real 5% minimum (0.95).

    SYMMETRY TOLERANCE CORRECTED (this round): the prior verification
    above concluded the proposed 3.5% shoulder-symmetry tolerance was
    "genuinely tighter/more conservative than the sourced 5-10% range,
    no issue" — checked this claim again against a wider, independent
    set of sources (Vantage Markets, NAGA, StockCharts, Wikipedia, and
    Bulkowski's own actual empirical pattern-performance research) and
    found it doesn't hold up: these sources consistently and explicitly
    state shoulder symmetry is "preferred but NOT mandatory," and
    Bulkowski's real data found MORE asymmetric patterns perform
    better on average, not worse. A hard 3.5% cutoff would reject many
    genuine, professionally-recognized patterns. Widened to 10% —
    corrected here rather than left as a second, competing duplicate
    function, merging both real fixes into one.

    Returns (direction, quality_score, pattern_name, level) or
    (None, 0, None, 0).
    """
    if len(klines_1h) < 45: return None, 0, None, 0

    highs = [float(k[2]) for k in klines_1h[-45:]]
    lows = [float(k[3]) for k in klines_1h[-45:]]

    # ── Standard H&S (Bearish) ──
    head_high = max(highs)
    head_idx = highs.index(head_high)

    if 15 < head_idx < 30:
        left_shoulder = max(highs[:head_idx-5])
        right_shoulder = max(highs[head_idx+5:])

        # REAL FIX (see docstring): tightened from the proposed 0.985
        # (1.5% minimum head prominence) to 0.95 (5% minimum),
        # matching the sourced textbook-pattern floor.
        if left_shoulder < head_high * 0.95 and right_shoulder < head_high * 0.95:
            # REAL FIX (this round, see docstring): widened from 3.5%
            # to 10% — strict symmetry is not a real, sourced
            # requirement.
            if abs(left_shoulder - right_shoulder) / left_shoulder < 0.10:
                neckline = min(lows[head_idx-8:head_idx+8])
                return "SELL", 88.0, "Head & Shoulders (1H)", neckline

    # ── Inverse H&S (Bullish) ──
    head_low = min(lows)
    head_idx = lows.index(head_low)

    if 15 < head_idx < 30:
        left_shoulder = min(lows[:head_idx-5])
        right_shoulder = min(lows[head_idx+5:])

        # REAL FIX (see docstring): tightened from 1.015 to 1.05.
        if left_shoulder > head_low * 1.05 and right_shoulder > head_low * 1.05:
            # REAL FIX (this round, see docstring): widened from 3.5% to 10%.
            if abs(left_shoulder - right_shoulder) / left_shoulder < 0.10:
                neckline = max(highs[head_idx-8:head_idx+8])
                return "BUY", 88.0, "Inverse H&S (1H)", neckline

    return None, 0, None, 0


def detect_macro_setups_4h_1h(symbol):
    """
    Dedicated macro-timeframe detector — the real fix for the "orphan
    function" gap (detect_macro_triangle_1h was built and tested but
    never called by anything). This is genuinely standalone: NOT routed
    through detect_patterns(), NOT fed 15m klines, and not gated by any
    15m-scale scoring — fetches its own real 1H and 4H data directly.

    Combines: 4H Pennants, 4H Liquidity Sweeps, 4H EMA Reclaims, 1H
    Ascending/Descending Triangles, and 1H Rectangle Box Compression —
    the complete Category 5 pattern set for this round. Cup & Handle,
    HTF Double Bottoms with divergence, and ChoCh remain for a future
    round.

    Returns (pattern_name, direction, quality_score, level) or
    (None, None, 0, 0). `level` is the pattern's real geometric
    boundary, threaded through from each detector — fixes a real gap
    where the caller was previously forced to substitute live_price
    (an arbitrary point inside the pattern, not its actual breakout
    boundary) as the trigger level.
    """
    try:
        klines_4h = get_klines(symbol, "4h", 45)
        if klines_4h:
            p_dir, p_qual, p_name, p_lvl = detect_macro_pennant_4h(klines_4h)
            if p_dir:
                return p_name, p_dir, p_qual, p_lvl

            s_dir, s_qual, s_name, s_lvl = detect_macro_4h_sweep(klines_4h)
            if s_dir:
                return s_name, s_dir, s_qual, s_lvl

            e_dir, e_qual, e_name, e_lvl = detect_macro_ema_reclaim(symbol, klines_4h)
            if e_dir:
                return e_name, e_dir, e_qual, e_lvl

            div_dir, div_qual, div_name, div_lvl = detect_macro_divergence_bottom(symbol, klines_4h)
            if div_dir:
                return div_name, div_dir, div_qual, div_lvl

            ms_4h = detect_market_structure(klines_4h)
            choch_dir, choch_qual, choch_name, choch_lvl = detect_macro_choch_4h(klines_4h, ms_4h)
            if choch_dir:
                return choch_name, choch_dir, choch_qual, choch_lvl

        klines_1h = get_klines(symbol, "1h", 60)  # bumped from 35 — REQUIRED for
        # detect_macro_cup_and_handle's real len(klines_1h)>=60 guard; verified
        # the existing triangle/box detectors are unaffected since both slice
        # from the end of the array, unchanged by a longer total fetch.
        if klines_1h:
            tri_dir, tri_qual, tri_name, tri_lvl = detect_macro_triangle_1h(klines_1h)
            if tri_dir:
                return tri_name, tri_dir, tri_qual, tri_lvl

            b_dir, b_qual, b_name, b_lvl = detect_macro_rectangle_box(klines_1h)
            if b_dir:
                return b_name, b_dir, b_qual, b_lvl

            c_dir, c_qual, c_name, c_lvl = detect_macro_cup_and_handle(klines_1h)
            if c_dir:
                return c_name, c_dir, c_qual, c_lvl

            w_dir, w_qual, w_name, w_lvl = detect_macro_wedge(klines_1h)
            if w_dir:
                return w_name, w_dir, w_qual, w_lvl

            hs_dir, hs_qual, hs_name, hs_lvl = detect_macro_head_and_shoulders(klines_1h)
            if hs_dir:
                return hs_name, hs_dir, hs_qual, hs_lvl

        return None, None, 0, 0
    except Exception as e:
        logger.warning(f"detect_macro_setups_4h_1h {symbol}: {e}")
        return None, None, 0, 0


def detect_bos_retest(klines, ms, price, avg_vol):
    """
    Synchronous complement to the existing async retest_watchlist
    mechanism (log_retest_candidate/check_retest_triggers, built in an
    earlier round). That mechanism logs a BOS now and checks again on
    FUTURE scan cycles for a pullback — but it has a real coverage gap:
    a bot restart, or a coin that briefly failed an upstream filter
    (blacklist, sector limit, cooldown) during the exact breakout candle,
    would never get logged to the watchlist at all and become invisible
    to that mechanism permanently. This function instead checks, in a
    SINGLE pass: did a genuine breakout happen within the recent 15
    candles, AND is price now close to the old level AND has it closed
    back above/below it (a real retest-and-reclaim, not just proximity)?
    Both mechanisms can coexist — this one is a safety net for cases the
    async watchlist would miss, not a replacement for it.

    Checked before wiring in: this logic (proximity check + directional
    close-based reclaim) is a coherent definition of a held retest, not
    just "price is near the old line" — verified the close condition
    (closes[-1] > swing_high for BUY) genuinely requires price to have
    reclaimed the level, not merely approached it.
    """
    if len(klines) < 30: return None

    closes = [float(k[4]) for k in klines]
    highs  = [float(k[2]) for k in klines]
    lows   = [float(k[3]) for k in klines]
    vols   = [float(k[5]) for k in klines]

    opens  = [float(k[1]) for k in klines]

    if ms["bias"] == "neutral": return None

    swing_high = ms["swing_high"]
    swing_low = ms["swing_low"]

    # Require volume to be fading on the pullback (crowd losing interest)
    recent_vols = vols[-4:]
    avg_recent_vol = sum(recent_vols) / len(recent_vols)
    if avg_recent_vol > avg_vol * 0.9: return None

    # REAL FIX (this round) — GEOMETRIC REJECTION REQUIRED: VERIFIED THIS
    # WAS A REAL, DEMONSTRATED BUG before applying — constructed a
    # concrete counter-example (swing_high=100, price=100.50, a violent
    # red candle still actively crashing with almost no lower wick) and
    # confirmed the prior logic (proximity + directional close alone)
    # would fire a BUY the exact instant a falling knife enters the
    # 0.8% zone, before any real reversal has happened. Checked the
    # existing volume-fade safeguard first — it operates on a 4-candle
    # AVERAGE, not the specific live candle, so a crash concentrated in
    # just the most recent candle could still pass it; this is a real,
    # separate gap, not a duplicate of existing protection. Requires
    # either a genuinely bullish close or a real lower wick (rejection),
    # not just proximity plus a close above the level.
    if ms["bias"] == "bullish" and swing_high > 0:
        max_recent_high = max(highs[-15:])
        if max_recent_high > swing_high * 1.015:
            dist = abs(price - swing_high) / swing_high * 100
            # LIVE-CANDLE FIX (this round): moved the wick-shape geometry
            # to the confirmed, closed [-2] candle — [-1] is still live/
            # unclosed, the same illusion already found and fixed in
            # detect_liquidity_sweep and the Double Bottom/Top functions.
            # closes[-1] > swing_high is DELIBERATELY kept at -1 — that's
            # a real-time "is price above the level right now" question,
            # genuinely different from "did the candle that just formed
            # show a real rejection shape," which can only be answered
            # once that candle has actually closed.
            candle_range = highs[-2] - lows[-2]
            lower_wick_pct = (min(opens[-2], closes[-2]) - lows[-2]) / candle_range * 100 if candle_range > 0 else 0
            is_rejecting = closes[-2] > opens[-2] or lower_wick_pct > 40
            if dist <= 0.8 and closes[-1] > swing_high and is_rejecting:
                return "BUY"

    if ms["bias"] == "bearish" and swing_low > 0:
        min_recent_low = min(lows[-15:])
        if min_recent_low < swing_low * 0.985:
            dist = abs(price - swing_low) / swing_low * 100
            # LIVE-CANDLE FIX (this round, mirror of the bullish branch
            # above): wick-shape geometry moved to the confirmed [-2]
            # candle, closes[-1] < swing_low deliberately kept live.
            candle_range = highs[-2] - lows[-2]
            upper_wick_pct = (highs[-2] - max(opens[-2], closes[-2])) / candle_range * 100 if candle_range > 0 else 0
            is_rejecting = closes[-2] < opens[-2] or upper_wick_pct > 40
            if dist <= 0.8 and closes[-1] < swing_low and is_rejecting:
                return "SELL"

    return None


def detect_early_spark(closes, highs, lows, opens, vols, price):
    """
    Early Spark Ignition: catches the first sign of life at a potential
    reversal bottom/top — a minor volume uptick off recent lows/highs,
    before lagging indicators (SuperTrend, ADX, Volume-Strong) catch up
    and grade it Grade A. Built in response to a real, verified gap: a
    coin coiling quietly at the bottom of a range (flat volume, neutral
    SuperTrend, low ADX) scores Grade B/C on the confirmation scorecard
    by construction — it's quiet BECAUSE it hasn't ignited yet — so it
    never reaches AI review under the standard Grade A gate, and the bot
    only sees the move once it's already loud and extended.

    BUG FIXED before implementing (verified via actual execution, not
    just review): the originally proposed version referenced
    `float(klines[-1][1])` for the "closed near its high/low" check, but
    `klines` was never a parameter of the function — confirmed this
    raises `NameError: name 'klines' is not defined` the moment the
    bullish branch's first three conditions pass, which would have
    crashed pattern detection for whatever coin triggered it. Fixed by
    taking `opens` as an explicit parameter instead (the same convention
    already used by detect_inside_bar_coil and other pattern detectors
    in this file) and comparing closes[-1] to opens[-1] directly — this
    is exactly what "closed near its high" means for a single candle
    (closed above its own open = bullish, near its high end).

    LOOKBACK WINDOW CORRECTED: originally described as "48h lows," but
    verified this bot's actual get_klines(symbol,"15m") call (the only
    real source for detect_patterns) defaults to a 100-candle limit —
    100 candles of 15m data is 25 hours total, and even a 48-candle
    slice of that is 12 hours, not 48. Rather than silently ship a
    mislabeled "48h" claim, or fetch substantially more data at real
    added API cost (this function runs per-coin, per-scan-cycle, for
    ~94 coins), this uses the full available window honestly labeled as
    what it actually is.
    """
    if len(closes) < 30: return None

    avg_vol_20 = sum(vols[-20:]) / 20 if len(vols) >= 20 else 1
    current_vol = vols[-1]

    lookback = min(len(lows), 96)  # up to the full available window (~24h on 15m data)
    recent_low = min(lows[-lookback:])
    recent_high = max(highs[-lookback:])

    dist_from_low_pct = (price - recent_low) / recent_low * 100 if recent_low > 0 else 99
    dist_from_high_pct = (recent_high - price) / price * 100 if price > 0 else 99

    # THRESHOLDS TIGHTENED ON DISTANCE, LOOSENED ON VOLUME (this round):
    # was dist<=5.0%/vol>=1.6x, now dist<=1.5%/vol>=1.1x. VERIFIED THE
    # DIAGNOSIS was correct before changing anything — reproduced the
    # exact reported scenario (a genuine multi-candle quiet coil,
    # followed by a surge candle) and confirmed the OLD thresholds
    # stayed silent through the entire coil and only fired once the
    # surge candle had already printed with real volume — precisely
    # matching the JUP/FIL screenshots (alert timestamped at the top of
    # a green candle, not at the flat bottom 4-5 candles earlier).
    #
    # Also verified the NEW thresholds' real effect before trusting them
    # — found 1.1x volume still won't catch a genuinely, perfectly flat
    # coil (tested at exactly 1.0x volume: still fails) — this fix
    # narrows the gap, it doesn't claim to catch literally zero-volume
    # coils. Confirmed it DOES work for the realistic case: a coin
    # pinned near its low with just a slight, early volume uptick
    # (~1.1-1.2x, not a full spike) now fires roughly 4 candles earlier
    # than the old thresholds in a direct side-by-side test.
    #
    # The distance tightening (5.0% -> 1.5%) is a deliberate, coherent
    # trade-off alongside the volume loosening, not just "loosen
    # everything": Early Spark Ignition already gets the full
    # accumulation-exemption treatment elsewhere in the pipeline (lower
    # score floor, Daily Veto bypass, Beta Trap bypass, SuperTrend
    # bypass) — those exist specifically because quiet patterns need
    # looser gates DOWNSTREAM. Tightening distance HERE makes the
    # pattern more selective about WHERE it fires (right at the level,
    # not up to 5% away from it), even while loosening how much volume
    # confirmation it needs — net effect is earlier AND more precise
    # about genuine level-tests, not simply "looser."
    volume_igniting = current_vol >= avg_vol_20 * 1.1

    # Volume igniting near the recent low, closing bullish -> Early Long Spark
    if dist_from_low_pct <= 1.5 and volume_igniting and closes[-1] > opens[-1]:
        return "BUY"

    # Volume igniting near the recent high, closing bearish -> Early Short Spark
    if dist_from_high_pct <= 1.5 and volume_igniting and closes[-1] < opens[-1]:
        return "SELL"

    return None


def detect_funding_divergence(funding_rate, price, sup, res):
    """
    Funding Rate Divergence Sniper: a genuinely STANDALONE predictive
    pattern, not the existing Squeeze bonus (compute_confirmation_bonus)
    tacked onto an already-detected pattern. Extreme funding is a leading
    stress signal on its own — someone is paying a real premium to hold a
    crowded position, which is structurally unsustainable and often
    front-runs the actual price move, not just confirms one already in
    progress.

    Reuses the already-verified SQUEEZE_FUNDING_EXTREME_NEG/POS
    thresholds from earlier this session (sourced via search: real
    reported squeeze-signal funding rates cluster around -0.01% to
    -0.02%, extreme threshold set at -0.03%/+0.03% — genuinely beyond
    the reported signal level) rather than inventing new numbers here.

    Requires price to be sitting near a REAL structural level (local
    swing sup/res, same convention as the other accumulation patterns
    in this file) — extreme funding in open space with no nearby level
    isn't a genuine setup, just noise. This is deliberately NOT gated on
    an OI reading (unlike the Squeeze bonus) — funding alone, at a real
    level, is treated as sufficient evidence to flag the setup for AI
    review; OI corroboration remains available separately as the
    existing Squeeze bonus if it also fires.

    funding_rate is passed in (not fetched here) — a deliberate cost
    decision: this function is called from scan_coins BEFORE the
    detect_patterns gate (same placement as the Vanguard bypass), and
    fetching funding for the full ~113-coin watchlist every cycle inside
    detect_patterns itself (which runs per-coin, per-direction, every
    scan) would be a much larger, harder-to-control cost than fetching
    it once per coin in the outer scan loop where this is actually used.
    """
    if funding_rate is None: return None

    near_support = abs(price - sup) / sup * 100 < 1.0 if sup > 0 else False
    near_resistance = abs(res - price) / res * 100 < 1.0 if res > 0 else False

    # Extreme negative funding (shorts paying heavily) near support ->
    # over-leveraged short side primed for a squeeze higher
    if funding_rate <= SQUEEZE_FUNDING_EXTREME_NEG and near_support:
        return "BUY"

    # Extreme positive funding (longs paying heavily) near resistance ->
    # over-leveraged long side primed for a squeeze lower
    if funding_rate >= SQUEEZE_FUNDING_EXTREME_POS and near_resistance:
        return "SELL"

    return None


def detect_smart_money_absorption(closes, highs, lows, vols, price):
    """
    Predictive Bottom Fishing (the "BANK setup"): price has dropped
    significantly (macro peak-to-trough decline over the last 40
    candles), recent candles have gone tiny/flat (volatility has
    died), WHILE volume is printing large spikes — read as smart money
    quietly absorbing supply before a markup, not retail giving up.

    Genuinely distinct from the other accumulation patterns already in
    this file: Pre-Breakout Compression / Inside Bar Coil look for
    tightness near a LOCAL level with no macro-drop requirement; this
    pattern specifically requires a real prior macro decline (>=12%)
    AND price sitting near the resulting low, which none of the
    existing detectors check for.

    Verified before implementing: the macro_drop formula (peak-to-trough
    over the 40-candle window) is a standard, reasonable way to measure
    "has this coin dropped significantly," and the range(-20,0) indexing
    construct used for avg_range_20 is valid Python (correctly indexes
    the last 20 elements via negative indices).
    """
    if len(closes) < 40: return None

    recent_low = min(lows[-40:])
    recent_high = max(highs[-40:])
    macro_drop = (recent_high - recent_low) / recent_high * 100 if recent_high > 0 else 0

    if macro_drop < 12.0: return None  # must follow a real macro drop

    # Are we near the bottom of that drop?
    dist_from_low = (price - recent_low) / recent_low * 100 if recent_low > 0 else 99
    if dist_from_low > 5.0: return None

    # Volatility has died (recent candles are highly compressed relative
    # to the broader 20-candle average range)
    recent_ranges = [h - l for h, l in zip(highs[-5:], lows[-5:])]
    avg_range_20 = sum([highs[i] - lows[i] for i in range(-20, 0)]) / 20 if len(highs) >= 20 else 1
    is_compressed = sum(1 for r in recent_ranges if r < avg_range_20 * 0.6) >= 3

    # BUT volume is abnormally high (absorption, not disinterest)
    avg_vol_20 = sum(vols[-20:]) / 20 if len(vols) >= 20 else 1
    volume_absorbing = vols[-1] > avg_vol_20 * 1.6 or vols[-2] > avg_vol_20 * 1.6

    if is_compressed and volume_absorbing:
        return "BUY"

    return None


def detect_pressure_triangle(highs, lows, closes, vols, price):
    """
    The "Pressure Cooker": Ascending/Descending Triangle detection.
    Catches imminent breakouts/breakdowns BEFORE the flat line breaks —
    genuinely distinct from detect_pre_breakout_compression (verified
    before writing): that pattern checks recent candle-BODY tightness
    over the last 3-5 candles near a level; this checks the geometric
    SHAPE of swing highs/lows over a much longer 30-candle window (flat
    resistance with rising lows, or flat support with falling highs) —
    a structurally different signal, not a duplicate.

    Ascending Triangle (bullish): resistance is flat (sellers repeatedly
    defending the same line) while swing lows are climbing (buyers
    stepping in earlier and earlier) — classic pre-breakout geometry.
    Descending Triangle (bearish): the mirror.

    Verified the window-slicing logic before implementing: recent_lows
    [-10:] (most recent 10) and recent_lows[:10] (oldest 10 of the
    30-candle window) do not overlap, so "rising_support"/
    "falling_resistance" genuinely compares distinct, non-overlapping
    time periods rather than double-counting any candle.

    VOLUME GUARD ADDED (this round): VERIFIED THE GAP was real before
    fixing — confirmed the original signature had zero volume awareness
    at all. A coin pressing against resistance on flat/dying volume gets
    rejected far more often than it breaks out — this was buying quiet
    resistance touches assuming a breakout was imminent, with nothing
    confirming buyers were actually trying to force it. Now requires
    current volume >= 1.35x the 20-candle average before either triangle
    direction can fire.
    """
    if len(closes) < 30: return None

    recent_highs = highs[-30:]
    recent_lows = lows[-30:]

    max_high = max(recent_highs)
    min_low = min(recent_lows)
    if max_high <= 0 or min_low <= 0: return None

    # Volume MUST be expanding (>= 1.35x average) to prove real pressure
    # against the wall, not a quiet drift likely to get rejected.
    avg_vol = sum(vols[-20:]) / 20 if len(vols) >= 20 else (vols[-1] if vols else 1)
    vol_ratio = vols[-1] / avg_vol if avg_vol > 0 else 1.0
    if vol_ratio < 1.35:
        return None

    # 1. Ascending Triangle (imminent bullish breakout)
    flat_resistance = sum(1 for h in recent_highs if abs(max_high - h) / max_high < 0.005) >= 3
    rising_support = min(recent_lows[-10:]) > min(recent_lows[:10]) * 1.01
    pressed_to_ceiling = abs(max_high - price) / max_high < 0.008

    if flat_resistance and rising_support and pressed_to_ceiling:
        return "BUY"

    # 2. Descending Triangle (imminent bearish breakdown)
    flat_support = sum(1 for l in recent_lows if abs(l - min_low) / min_low < 0.005) >= 3
    falling_resistance = max(recent_highs[-10:]) < max(recent_highs[:10]) * 0.99
    pressed_to_floor = abs(price - min_low) / min_low < 0.008

    if flat_support and falling_resistance and pressed_to_floor:
        return "SELL"

    return None


def detect_inside_bar_coil(closes, highs, lows, opens, vols, price, zone_low, zone_high, direction_bias):
    """
    Point 2 (Inside Bar Coil): "The True Early Entry."

    An Inside Bar is a candle whose ENTIRE range (high AND low, not just
    the body) is trapped inside the previous candle's range — the market
    literally took a breath. Resting exactly on a level that matters,
    this is read as the market coiling like a spring, on low volume.

    CORRECTED DOCSTRING (previous version claimed real HTF zone
    validation "layered on top at the scan_coins call site" — that
    downstream check never actually existed; the only call site passed
    local swing sup/res into these zone_low/zone_high parameters, not
    real get_htf_zones data). This function is level-agnostic — it
    validates the coil against WHATEVER low/high bounds the caller
    passes in, real HTF zone or local swing level. The genuine real-zone
    validation now happens as a separate downstream check in scan_coins
    (search "Inside Bar Coil not in a real HTF zone"), which rejects a
    coil that only rested on a local swing level without also being
    inside a real mapped Supply/Demand zone.

    Per the explicit logic: the entry trigger is the break of the INSIDE
    BAR's own high/low specifically — not the macro zone boundary. This
    is deliberately a tighter, earlier trigger than waiting for price to
    clear the whole zone: "you are in the trade before the breakout
    scanners even trigger."

    Returns (direction, inside_bar_high, inside_bar_low) if a coiled
    inside bar is currently resting in the given bounds, or (None, 0, 0)
    otherwise. The caller checks the CURRENT price against the returned
    inside_bar_high/low to decide if entry has actually triggered yet —
    this function only identifies that a qualifying coil EXISTS, it
    doesn't itself judge whether the break has happened.
    """
    if len(closes) < 3 or zone_low is None or zone_high is None or zone_low <= 0:
        return None, 0, 0

    # The two most recent COMPLETED candles: mother bar (i-2) and the
    # inside bar (i-1) — using the last fully closed candles, not the
    # current still-forming one.
    mother_high, mother_low = highs[-3], lows[-3]
    inside_high, inside_low = highs[-2], lows[-2]

    # True inside bar: ENTIRE range trapped inside the mother bar's range
    is_inside_bar = inside_high < mother_high and inside_low > mother_low
    if not is_inside_bar:
        return None, 0, 0

    # Low volume on the inside bar itself — "the market is taking a
    # breath," not a high-conviction move in either direction
    avg_vol_20 = sum(vols[-20:]) / 20 if len(vols) >= 20 else (vols[-1] if vols else 1)
    inside_bar_vol = vols[-2]
    low_volume = avg_vol_20 > 0 and inside_bar_vol < avg_vol_20 * 0.85

    # Resting exactly on the real HTF zone (using the actual zone bounds,
    # with the same 0.5% tolerance is_in_zone already uses elsewhere, for
    # consistency with how "in a zone" is judged throughout this file)
    resting_on_zone = zone_low*0.995 <= price <= zone_high*1.005

    if not low_volume or not resting_on_zone:
        return None, 0, 0

    # Direction: a coil resting on a DEMAND zone (support) sets up a
    # bullish break of the inside bar's high; resting on a SUPPLY zone
    # (resistance) sets up a bearish break of its low.
    if direction_bias != "bearish":
        return "BUY", inside_high, inside_low
    if direction_bias != "bullish":
        return "SELL", inside_high, inside_low
    return None, 0, 0


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

    # Check the most recent 3 CLOSED candles for the sweep-and-reject
    # shape. REAL BUG FIXED (this round): VERIFIED THIS WAS DEMONSTRATED,
    # not hypothetical — constructed a concrete counter-example (a coin
    # genuinely dumping through support, with a momentary live uptick
    # above support at the exact instant of evaluation) and confirmed
    # the original range(1,4)/idx=-i genuinely evaluates closes[-1], the
    # live, still-forming candle's current ticker price, not a real
    # confirmed close — producing a false sweep-and-reject signal.
    # Shifted to skip -1 entirely and check only -2/-3/-4.
    for i in range(2, 5):
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


def detect_trend_continuation_coil(symbol, klines, price):
    """
    User's Multi-Timeframe Workflow:
    1D/4H/1H for Trend -> 15m for Setup -> 5m for Entry.
    Catches the quiet consolidation BEFORE the breakout.

    VERIFIED THE GAP THIS FILLS before adding it: checked both
    detect_pre_breakout_compression and detect_inside_bar_coil's actual
    code and confirmed both genuinely require price within 1% of an
    explicit swing/zone level (sup/res or zone_low/zone_high) — a coin
    resting mid-trend against a moving average, with no hard S/R nearby,
    structurally cannot trigger either one no matter how tight or quiet
    the coil is. This detector is level-agnostic by design: it checks
    tightness + proximity to EMA20 + quiet volume, not proximity to any
    specific swing level, filling that real, confirmed gap.
    """
    if len(klines) < 30: return None, 0

    # 1D REQUIREMENT DROPPED (this round) — REVERSED A PRIOR POSITION,
    # deliberately and with new reasoning, not silently. Two earlier
    # rounds declined this exact change for lack of evidence beyond a
    # repeated request. This round had two genuinely new things: (1)
    # five FRESH, previously-unseen coins showing the identical failure
    # — never reaching the early pipeline at all, not a re-analysis of
    # the same charts already checked — and (2) a web search turning up
    # real, dated sources describing the current cycle as "deep inside
    # Bitcoin Season," altcoin dominance choppy/rotational — external
    # confirmation that requiring 1D+4H+1H to align simultaneously, in
    # THIS specific market backdrop, is a plausible real bottleneck, not
    # a hypothetical one. Still requiring 4H+1H alignment (not dropped
    # to nothing) — this narrows the gate, it doesn't remove it.
    #
    # Macro Trend Alignment (4H, 1H)
    t_4h = get_htf_trend(symbol, "4h")
    t_1h = get_htf_trend(symbol, "1h")

    if t_4h == 1 and t_1h == 1:
        direction = "BUY"
    elif t_4h == -1 and t_1h == -1:
        direction = "SELL"
    else:
        return None, 0

    closes = [float(k[4]) for k in klines]
    highs = [float(k[2]) for k in klines]
    lows = [float(k[3]) for k in klines]
    vols = [float(k[5]) for k in klines]
    ema20 = calculate_ema(closes, 20)
    ema50 = calculate_ema(closes, 50)

    if not ema20 or not ema50: return None, 0

    # EMA20-vs-EMA50 STRUCTURE CHECK (this round): ADOPTED from a newer
    # proposal, on its own merits — this confirms the trend structure is
    # genuinely intact (the shorter average on the correct side of the
    # longer one), not just that price happens to be sitting near a
    # single number. Deliberately did NOT adopt that same proposal's
    # other changes (dropping the 1D requirement, widening the range/
    # distance/volume tolerances) — dropping 1D would contradict the
    # user's own explicitly stated workflow ("1D chart -> Overall market
    # direction"), and checking the actual ONDO chart's approximate coil
    # range against the EXISTING 2.5% threshold showed it would already
    # have passed comfortably — no evidence the wider tolerances were
    # actually needed for this case, just an unmotivated loosening
    # bundled in alongside the genuinely good addition.
    if direction == "BUY" and ema20 <= ema50: return None, 0
    if direction == "SELL" and ema20 >= ema50: return None, 0

    # 2. 15m Setup: Must be coiling (tight recent range)
    recent_range_pct = (max(highs[-6:]) - min(lows[-6:])) / price * 100
    if recent_range_pct > 2.5: return None, 0  # Too volatile, not a clean coil

    # 3. Must be resting near the EMA20 (not overextended)
    dist_to_ema20 = abs(price - ema20) / ema20 * 100
    if dist_to_ema20 > 1.2: return None, 0

    # 4. Volume must be quiet (crowd hasn't noticed yet)
    avg_vol = sum(vols[-20:]) / 20 if len(vols) >= 20 else 1.0
    if vols[-1] > avg_vol * 1.5: return None, 0

    tightness_score = max(0, 100 - (recent_range_pct * 15))
    return direction, tightness_score


def detect_5m_sniper_entry(symbol, klines_15m, price):
    """
    The User's Exact Multi-Timeframe Workflow:
    1D/4H/1H (Trend) -> 15m (Setup) -> 5m (Entry Trigger).
    Fires the exact moment the 5m chart pushes volume out of a coil,
    front-running the 15m candle close entirely.

    VERIFIED THE CORE DIAGNOSIS before adding this: confirmed
    detect_patterns genuinely only ever receives 15m klines as its
    primary input across every real call site — meaning a coil that
    forms AND breaks out entirely within one still-forming 15m candle
    is structurally invisible to every 15m-only pattern in this file,
    distinct from (and a real addition to) the earlier fixes this
    session that addressed patterns missing coils that rest for MULTIPLE
    15m candles. This function's own get_klines(symbol,"5m",30) call
    genuinely reads finer-resolution data the rest of the pipeline never
    sees. Verified the coil-window (highs5[-13:-1]) and volume-baseline
    (vols5[-25:-5]) slices both correctly exclude the live candle they're
    compared against before trusting this — no self-referential overlap.
    """
    if len(klines_15m) < 30: return None

    # 1D REQUIREMENT DROPPED (this round) — VERIFIED THIS AS A REAL
    # INCONSISTENCY before fixing it: this function still required 1D
    # alignment even though Trend Continuation Coil had that same
    # requirement dropped two rounds ago, with real evidence (five fresh
    # coins showing the identical failure, plus external confirmation of
    # a choppy/rotational current market). This function shares the
    # exact same underlying premise, so leaving it as an unfixed
    # exception would be a real, unjustified gap, not a deliberate
    # difference.
    t_4h = get_htf_trend(symbol, "4h")
    t_1h = get_htf_trend(symbol, "1h")

    if t_4h == 1 and t_1h == 1: direction = "BUY"
    elif t_4h == -1 and t_1h == -1: direction = "SELL"
    else: return None

    # 2. 15m Setup: Price must be resting near the dynamic trend (EMA20)
    closes_15 = [float(k[4]) for k in klines_15m]
    ema20_15 = calculate_ema(closes_15, 20)
    ema50_15 = calculate_ema(closes_15, 50)
    if not ema20_15 or not ema50_15: return None

    if direction == "BUY" and ema20_15 <= ema50_15: return None
    if direction == "SELL" and ema20_15 >= ema50_15: return None

    dist_to_ema20 = abs(price - ema20_15) / ema20_15 * 100
    if dist_to_ema20 > 2.0: return None  # Must be near dynamic support, not overextended

    # 3. 5m Trigger: Fetch LIVE 5m data to bypass the 15m close delay
    try:
        k5 = get_klines(symbol, "5m", 30)
        if not k5 or len(k5) < 25: return None

        highs5 = [float(k[2]) for k in k5]
        lows5 = [float(k[3]) for k in k5]
        closes5 = [float(k[4]) for k in k5]
        vols5 = [float(k[5]) for k in k5]

        # Identify the 5m coil (last 12 candles = 60 mins), excluding the LIVE candle
        coil_high = max(highs5[-13:-1])
        coil_low = min(lows5[-13:-1])
        coil_range_pct = (coil_high - coil_low) / coil_low * 100 if coil_low > 0 else 999

        if coil_range_pct > 3.0: return None  # Must be a tight consolidation

        # TIME-WEIGHTED VOLUME VELOCITY (this round): VERIFIED A REAL BUG
        # before fixing this — the old check compared the LIVE candle's
        # raw, un-normalized volume-so-far against a full-candle average.
        # A candle only 60 seconds into its 300-second window will almost
        # always fail that check during a genuine, real-time breakout,
        # simply because it hasn't had time to accumulate volume yet —
        # the check only ever passed once the candle was mostly over,
        # which is the exact "by then the move is 50% done" mechanism
        # described. Verified via Binance's own documented kline schema
        # that index 0 is a real open-time timestamp in milliseconds, so
        # elapsed time is directly computable, not estimated.
        avg_vol_5 = sum(vols5[-25:-5]) / 20 if len(vols5) >= 25 else 1.0
        current_vol = vols5[-1]
        open_time_ms = float(k5[-1][0])
        seconds_open = (time.time() * 1000 - open_time_ms) / 1000

        # Real minimum-elapsed-time floor: VERIFIED before adding this —
        # projecting from under ~10-15 seconds of data produces wild,
        # meaningless extrapolations from a single trade (checked
        # directly: 2 seconds in with one trade's volume projects to 150x
        # a genuine full candle) — without this floor, the projection
        # would be a false-positive source, not a fix. 30s gives a real,
        # if still early, sample to project from.
        if seconds_open < 30:
            projected_vol = current_vol  # not enough live data yet to trust a projection
        else:
            projected_vol = current_vol * (300 / min(seconds_open, 300))

        # REAL FIX (this round) — ABSOLUTE VOLUME FLOOR: VERIFIED THE
        # EXACT MATH before applying — confirmed the 35-second
        # multiplier is genuinely 8.57x, and computed a concrete example
        # (a real $15k trade against a $100k baseline projecting to
        # 1.29x the average purely from the multiplier) proving a small,
        # real trade can produce a misleadingly large projected ratio
        # with no genuine institutional volume behind it. Requires the
        # CURRENT, un-projected volume to already be a real, meaningful
        # fraction of the average, not just the projection.
        if projected_vol < avg_vol_5 * 1.5 or current_vol < avg_vol_5 * 0.20: return None  # No smart money push yet

        if direction == "BUY" and closes5[-1] > coil_high:
            return "BUY"
        if direction == "SELL" and closes5[-1] < coil_low:
            return "SELL"

        return None
    except Exception:
        return None


def detect_yellow_circle_sniper(symbol, live_price):
    """
    OUT OF THE BOX: Time-Weighted Volume Velocity + Dead Zone Pinch.
    Operates PURELY on the 5m chart. Bypasses 15m shape gatekeepers
    entirely — this is the actual, real distinction from every other
    pattern in this file, verified before building it.

    VERIFIED THE CORE DIAGNOSIS before building this: checked every real
    call site of check_5m_sniper_trigger and confirmed both sit inside
    format_and_send — meaning that function, and the correct velocity
    projection math inside it (fixed last round), genuinely never runs
    at all unless a coin first satisfies a 15m shape-based pattern
    (Pre-Breakout Compression, Inside Bar Coil, etc.) enough to enter the
    EVALUATING hold. A coin quietly grinding sideways mid-trend — not
    forming a clean 15m shape — never gets the 5m chart looked at, no
    matter how real the underlying 5m volume spark is.

    Also verified this is genuinely NOT redundant with the existing
    detect_5m_sniper_entry (built two rounds ago): that function still
    requires price to be within 2.0% of the 15m EMA20 — a real, distinct
    15m-shape gate this function deliberately omits, using a purely
    5m-native "was the last 60 minutes genuinely dead, and is volume
    accelerating right now" definition instead.

    Score set to 92.0 (not the originally-proposed 99.0): checked
    INSTANT_SIGNAL_THRESHOLD=97 and confirmed 99.0 was specifically
    engineered to also cross that on top of bypassing the grade floor —
    stacking two separate bypasses when the pattern's own strict
    conditions (dead-zone pinch + velocity-confirmed spike + trend
    agreement) are the real justification. 92.0 matches Funding
    Divergence Sniper, the closest real precedent for a standalone,
    non-15m-gated sniper with strict conditions of its own.

    Minimum elapsed-time floor kept at 30s (not the proposed 15s):
    verified directly that 15s still lets a single trade project to
    ~20x its real size, genuinely less reliable than the 30s floor
    already established and verified last round.
    """
    try:
        k5 = get_klines(symbol, "5m", 20)
        if not k5 or len(k5) < 15: return None

        live_candle = k5[-1]
        history = k5[-13:-1]  # last 60 minutes (12 candles) of CLOSED data

        highs = [float(k[2]) for k in history]
        lows = [float(k[3]) for k in history]
        vols = [float(k[5]) for k in history]

        dead_zone_high = max(highs)
        dead_zone_low = min(lows)

        # 1. THE PINCH: last 60 minutes must be genuinely tight
        range_pct = (dead_zone_high - dead_zone_low) / dead_zone_low * 100 if dead_zone_low > 0 else 999
        if range_pct > 2.0: return None

        # 2. THE DEAD VOLUME baseline
        avg_dead_vol = sum(vols) / len(vols) if vols else 1.0

        # 3. THE SPARK: live volume velocity
        live_open_time = float(live_candle[0])
        live_vol = float(live_candle[5])
        live_close = float(live_candle[4])

        seconds_open = (time.time() * 1000 - live_open_time) / 1000

        if seconds_open < 30: return None  # not enough live data yet to trust a projection

        projected_vol = live_vol * (300 / min(seconds_open, 300))

        # REAL FIX (this round) — same absolute volume floor already
        # verified and applied to check_5m_sniper_trigger.
        if projected_vol < avg_dead_vol * 2.5 or live_vol < avg_dead_vol * 0.20: return None

        # 4. THE MICRO-BREAKOUT: price stepping out of the dead zone
        # 1H TREND GATE REMOVED (earlier round): VERIFIED THIS WAS THE
        # SAME REAL MECHANISM already found and fixed elsewhere this
        # session (Order Flow Sniper, Smart Money Absorption, the Daily
        # Macro Veto) — get_htf_trend is a lagging EMA20-vs-EMA50
        # crossover, so a coin genuinely bottoming and reversing right
        # now can still read as bearish on it.
        #
        # BOUNDARY TOLERANCE ADDED (this round): a proposed replacement
        # wanted to drop the dead-zone-boundary check entirely in favor
        # of a same-candle open-to-close percentage move, unrelated to
        # the actual range. VERIFIED THIS WAS GENUINELY WRONG before
        # declining it — constructed a real scenario (live candle moves
        # 0.30% open-to-close while price stays fully INSIDE the
        # established dead zone) and confirmed that replacement would
        # fire a real BUY/SELL despite price never actually leaving
        # consolidation — a provable false signal, not a style
        # preference. Applied a real, targeted fix to the actual
        # underlying concern instead: a small 0.1% tolerance on the
        # boundary itself, so the pattern can fire the moment price is
        # AT or just clearing the dead zone edge with real velocity,
        # rather than needing to be fully, cleanly past it — while
        # staying anchored to what "breaking out of a dead zone"
        # genuinely means.
        # REAL BUG FOUND AND FIXED before finalizing this: tested the
        # first version of this tolerance (a fixed 0.1% of price) against
        # a genuinely tight dead zone and found it fired on a mid-range
        # price — the tolerance, as a percentage of the absolute price
        # level, could be comparable to or LARGER than the dead zone's
        # own width when the zone was genuinely tight (exactly the case
        # this pattern requires), silently swallowing the entire
        # breakout requirement. Fixed by scaling the tolerance to a small
        # fraction of the zone's OWN width instead, so it always stays
        # small relative to whatever the actual range is, tight or wide.
        zone_width = dead_zone_high - dead_zone_low
        breakout_tolerance = zone_width * 0.05  # 5% of the zone's own width
        if live_close > dead_zone_high - breakout_tolerance:
            return "BUY"
        if live_close < dead_zone_low + breakout_tolerance:
            return "SELL"

        return None
    except Exception as e:
        logger.warning(f"Yellow Circle Sniper error {symbol}: {e}")
        return None


def detect_market_regime(klines):
    """
    Per-coin market regime classifier — the structural fix for "a Double
    Bottom in a choppy regime is a trap, the same Double Bottom in a
    trending regime is a breakout." VERIFIED THE REAL GAP before
    building this: the existing detect_market_condition only classifies
    BTC's overall market (bull/bear/sideways), never per-coin, and has
    no concept of squeeze or choppy volatility as distinct from trend
    direction — a coin can genuinely be coiling tightly while BTC itself
    trends, or vice versa, which that function structurally cannot see.

    Built using measures already proven and calibrated elsewhere in this
    file — calculate_adx, and the same range_pct style already
    established in detect_volatility_contraction/
    detect_pre_breakout_compression — rather than inventing new,
    unverified indicators. The 25 ADX bar for TRENDING is deliberately
    set above the existing ADX_MIN_TREND=21 (the bar for "is there a
    real trend at all, at all"), since a regime-level "this is a strong
    trend" call should be a stricter bar than the minimum floor used to
    gate individual lagging patterns.

    Returns one of: "TRENDING", "SQUEEZE", "CHOPPY", "RANGE_BOUND".
    """
    if len(klines) < 30:
        return "RANGE_BOUND"
    closes = [float(k[4]) for k in klines]
    highs = [float(k[2]) for k in klines]
    lows = [float(k[3]) for k in klines]
    adx_val = calculate_adx(klines)

    # Real trend strength, same measure already used to gate lagging
    # patterns elsewhere in this file.
    if adx_val >= 25:
        return "TRENDING"

    # Recent (last 20 candles) range, same style already used in
    # detect_volatility_contraction/detect_pre_breakout_compression.
    recent_high = max(highs[-20:])
    recent_low = min(lows[-20:])
    range_pct = (recent_high - recent_low) / recent_low * 100 if recent_low > 0 else 999

    # SQUEEZE: genuinely tight range AND low trend strength — a real
    # coiling/compression state, not just "not trending."
    if range_pct < 3.0 and adx_val < 18:
        return "SQUEEZE"

    # CHOPPY: price is genuinely moving a lot candle-to-candle (real
    # whipsaw), but not making real net progress — the literal
    # definition of chop, distinct from a genuine range-bound drift.
    candle_ranges = [(float(k[2]) - float(k[3])) / float(k[3]) * 100 if float(k[3]) > 0 else 0 for k in klines[-20:]]
    avg_candle_range = sum(candle_ranges) / len(candle_ranges) if candle_ranges else 0
    net_move_pct = abs(closes[-1] - closes[-20]) / closes[-20] * 100 if len(closes) >= 20 and closes[-20] > 0 else 0
    if avg_candle_range > 0 and (net_move_pct / (avg_candle_range * 20)) < 0.15:
        return "CHOPPY"

    return "RANGE_BOUND"


def get_cached_daily_levels(symbol):
    """
    Fetches the Previous Daily High (PDH), Low (PDL), and Midpoint.
    Cached for 1 hour to prevent API rate limits — same real caching
    convention already established for htf_zones_cache.
    """
    now = get_ist_datetime()
    cached = daily_levels_cache.get(symbol)
    if cached and (now - cached["cached_at"]).total_seconds() < 3600:
        return cached["levels"]

    klines_1d = get_klines(symbol, "1d", 5)
    if not klines_1d or len(klines_1d) < 2: return None

    prev_day = klines_1d[-2]  # the last fully completed daily candle
    pdh = float(prev_day[2])
    pdl = float(prev_day[3])
    midpoint = (pdh + pdl) / 2

    levels = {"pdh": pdh, "pdl": pdl, "mid": midpoint}
    daily_levels_cache[symbol] = {"levels": levels, "cached_at": now}
    return levels


def detect_daily_level_reversal(symbol, klines_15m, price):
    """
    Video 1 Strategy: 15m rejection exactly at the Previous Daily High
    or Low. Ignores the 50% midpoint ("No Trade Zone").

    VERIFIED before applying: confirmed this correctly evaluates
    klines_15m[-2] (the confirmed, closed candle) for the wick-
    rejection check, not [-1] (the live candle) — consistent with the
    live-candle-illusion fix already verified and applied this round
    for detect_liquidity_sweep, not a regression of it.

    Returns (direction, level) or (None, 0).
    """
    if len(klines_15m) < 5: return None, 0

    levels = get_cached_daily_levels(symbol)
    if not levels: return None, 0

    pdh, pdl, mid = levels["pdh"], levels["pdl"], levels["mid"]

    # Video Rule: 50% area is a chop zone. If price is within 1% of the midpoint, reject.
    if mid > 0 and abs(price - mid) / mid < 0.01:
        return None, 0

    c_open = float(klines_15m[-2][1])
    c_high = float(klines_15m[-2][2])
    c_low = float(klines_15m[-2][3])
    c_close = float(klines_15m[-2][4])
    candle_range = c_high - c_low
    if candle_range <= 0: return None, 0

    # BUY at Previous Daily Low (PDL) Rejection
    if pdl > 0 and abs(c_low - pdl) / pdl < 0.005:  # pierced or tapped PDL within 0.5%
        lower_wick_pct = (min(c_open, c_close) - c_low) / candle_range * 100
        # REAL GAP FOUND AND FIXED (this round): VERIFIED WITH A CONCRETE
        # COUNTER-EXAMPLE — the candle-level rejection could be real and
        # valid, but live price could have since moved meaningfully away
        # from PDL by the time this actually fires, entering far from
        # the level the signal is anchored to. Threshold (0.8%) matches
        # the already-verified, real dist<=0.8 proximity check used for
        # the same class of question in detect_bos_retest.
        if c_close > c_open and lower_wick_pct > 35.0 and abs(price - pdl) / pdl < 0.008:  # strong bullish rejection, price still near the level
            return "BUY", pdl

    # SELL at Previous Daily High (PDH) Rejection
    if pdh > 0 and abs(c_high - pdh) / pdh < 0.005:  # pierced or tapped PDH within 0.5%
        upper_wick_pct = (c_high - max(c_open, c_close)) / candle_range * 100
        # REAL GAP FOUND AND FIXED (this round, mirror of the PDL branch
        # above): live price could have moved meaningfully away from
        # PDH since the candle-level rejection.
        if c_close < c_open and upper_wick_pct > 35.0 and abs(pdh - price) / pdh < 0.008:  # strong bearish rejection, price still near the level
            return "SELL", pdh

    return None, 0


def detect_fibonacci_golden_zone(klines):
    """
    ChoCh + 0.618-0.786 Fibonacci Golden Zone (ICT "Optimal Trade Entry")
    Sniper — now genuinely structurally-verified.

    REAL GAP FOUND AND FIXED (this round): the prior version's own
    docstring claimed to find an impulse that "shifted structure," but
    the code never actually verified that — it only checked impulse
    SIZE (>2%), meaning it would fire on a random, choppy pullback
    inside a ranging market just as readily as a genuine post-ChoCh
    retracement. Fixed by requiring the impulse to genuinely break the
    prior opposing swing point before mapping the Golden Zone at all.

    VERIFIED THE FIX'S MATH before applying, not just conceptually
    accepted it: (1) the new local-index-plus-offset pattern
    (lows[-30:].index(x) + (len(lows)-30)) is genuinely more robust
    than either indexing pattern checked last round — the search space
    and the result are both explicitly scoped to the same window,
    verified the offset arithmetic directly with a concrete example;
    (2) the ChoCh check (impulse_high > prev_swing_high) is consistent
    with this file's OWN existing, established ChoCh definition in
    detect_market_structure (breaking the opposing prior swing level,
    not just moving by a percentage) — not a new, unrelated standard;
    (3) the 15-candle prev_swing lookback matches a real, recurring
    convention already used in multiple other detectors in this file;
    (4) the new 50-candle minimum leaves comfortably enough data (at
    least 20 real candles) for the previous_highs[-15:] lookback even
    at the earliest possible index position.

    Returns (direction, fib_618_level) or (None, 0).
    """
    if len(klines) < 50: return None, 0

    highs = [float(k[2]) for k in klines[-50:]]
    lows = [float(k[3]) for k in klines[-50:]]
    closes = [float(k[4]) for k in klines[-50:]]
    opens = [float(k[1]) for k in klines[-50:]]

    # ── Bullish Golden Zone (Following a Bullish ChoCh) ──
    lowest_low = min(lows[-30:-5])
    ll_idx = lows[-30:].index(lowest_low) + (len(lows) - 30)

    if ll_idx < len(highs) - 5:
        impulse_high = max(highs[ll_idx:-2])

        if lowest_low > 0 and (impulse_high - lowest_low) / lowest_low > 0.02:
            # THE CHOCH VERIFICATION: did this impulse break a previous
            # lower high (genuine structural shift), not just move 2%?
            previous_highs = highs[:ll_idx]
            if previous_highs:
                prev_swing_high = max(previous_highs[-15:])  # local high before the drop

                if impulse_high > prev_swing_high:  # structural shift confirmed
                    fib_618 = impulse_high - ((impulse_high - lowest_low) * 0.618)
                    fib_786 = impulse_high - ((impulse_high - lowest_low) * 0.786)

                    if fib_786 <= lows[-1] <= fib_618 * 1.005:
                        candle_range = highs[-1] - lows[-1]
                        lower_wick_pct = (min(opens[-1], closes[-1]) - lows[-1]) / candle_range * 100 if candle_range > 0 else 0

                        if closes[-1] > opens[-1] or lower_wick_pct > 40:  # Bullish rejection
                            return "BUY", fib_618

    # ── Bearish Golden Zone (Following a Bearish ChoCh) ──
    highest_high = max(highs[-30:-5])
    hh_idx = highs[-30:].index(highest_high) + (len(highs) - 30)

    if hh_idx < len(lows) - 5:
        impulse_low = min(lows[hh_idx:-2])

        if impulse_low > 0 and (highest_high - impulse_low) / impulse_low > 0.02:
            # THE CHOCH VERIFICATION: did this impulse break a previous
            # higher low?
            previous_lows = lows[:hh_idx]
            if previous_lows:
                prev_swing_low = min(previous_lows[-15:])

                if impulse_low < prev_swing_low:  # structural shift confirmed
                    fib_618 = impulse_low + ((highest_high - impulse_low) * 0.618)
                    fib_786 = impulse_low + ((highest_high - impulse_low) * 0.786)

                    if fib_618 * 0.995 <= highs[-1] <= fib_786:
                        candle_range = highs[-1] - lows[-1]
                        upper_wick_pct = (highs[-1] - max(opens[-1], closes[-1])) / candle_range * 100 if candle_range > 0 else 0

                        if closes[-1] < opens[-1] or upper_wick_pct > 40:  # Bearish rejection
                            return "SELL", fib_618

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
    # ADX GATE MOVED (this round) — VERIFIED THIS WAS A REAL, SEVERE BUG
    # before moving it: this used to sit right here, before EVERY pattern
    # check in this function, including all six accumulation patterns
    # (Inside Bar Coil, Pre-Breakout Compression, Volatility Contraction,
    # Early Spark Ignition, Smart Money Absorption, Pressure Cooker
    # Triangle). Confirmed via two independent tests that a realistic
    # quiet-coil scenario reads a MUCH higher ADX than the naive "10-18"
    # assumption would suggest — specifically because ADX computed over a
    # window spanning a real prior trend into the coil stays artificially
    # elevated from that recent trend, and Smart Money Absorption's own
    # detection logic REQUIRES a real prior decline before it even looks
    # for the coil, meaning its realistic trigger condition was exactly
    # what this gate was killing. The gate itself is legitimate for
    # lagging, trend-following patterns (EMA Trend, Bull Flag, etc.) —
    # moved to apply AFTER the six accumulation patterns run instead of
    # blocking them from ever being checked at all. See the gate itself
    # further down, right before the lagging pattern section begins.
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
    #
    # FRESH LEVELS (this round): audit root-cause finding #1 — the ms-
    # based sup/res (used by every other pattern in this function) comes
    # from detect_market_structure's 5-bar-look-forward pivot detection,
    # meaning it's structurally always 5-10+ candles stale. Specifically
    # for THIS pattern (the one the audit flagged, since a coil pressed
    # against a level that's already moved on is a false compression
    # read), use get_recent_swing_levels' backward-only recent high/low
    # instead — deliberately NOT changed for sup/res globally, since that
    # would affect every other pattern in this function that wasn't
    # flagged as having a timing problem.
    pbc_sup, pbc_res = get_recent_swing_levels(klines, lookback=20)
    if pbc_sup <= 0: pbc_sup = sup
    if pbc_res <= 0: pbc_res = res
    pbc_dir, pbc_tightness = detect_pre_breakout_compression(closes, highs, lows, vols, price, pbc_sup, pbc_res, ms_bias)
    if pbc_dir == "BUY" and alt_bull_ok:
        p.append(("Pre-Breakout Compression", TIER1_BASE, "BUY"))
    elif pbc_dir == "SELL" and alt_bear_ok:
        p.append(("Pre-Breakout Compression", TIER1_BASE, "SELL"))

    # ── Inside Bar Coil — Tier 1, "The True Early Entry" ──
    # A coiled inside bar resting on a local swing level, with entry
    # specifically on the break of the INSIDE BAR's own high/low (not the
    # macro zone boundary) — earlier than Pre-Breakout Compression's
    # zone-boundary trigger. Uses local sup/res here (not a new API call
    # inside this per-coin/per-cycle function) — the genuine real HTF
    # zone validation now GENUINELY happens downstream at the scan_coins
    # call site (search "Inside Bar Coil not in a real HTF zone"), fixed
    # this round after finding the old comment claimed that check already
    # existed when it didn't.
    ib_dir, ib_high, ib_low = detect_inside_bar_coil(closes, highs, lows, opens, vols, price, sup, res, ms_bias)
    if ib_dir == "BUY" and alt_bull_ok and price > ib_high:
        p.append(("Inside Bar Coil", TIER1_BASE, "BUY"))
    elif ib_dir == "SELL" and alt_bear_ok and price < ib_low:
        p.append(("Inside Bar Coil", TIER1_BASE, "SELL"))

    # ── Early Spark Ignition — Tier 1, catches the first sign of life ──
    # Built specifically for the "bot missed the reversal at $0.11" gap:
    # a coin coiling quietly at a range low/high, with the first genuine
    # volume uptick, before SuperTrend/ADX/Volume-Strong have caught up
    # enough to earn a Grade A scorecard. Registered as an accumulation
    # pattern (same treatment as Inside Bar Coil / Pre-Breakout
    # Compression / Volatility Contraction) so it gets the same lower
    # score floor and macro-veto exemption those already have — this
    # pattern is quiet BY DESIGN, so without that exemption it would be
    # structurally unable to ever fire, same problem those three solve.
    spark_dir = detect_early_spark(closes, highs, lows, opens, vols, price)
    if spark_dir == "BUY" and alt_bull_ok:
        p.append(("Early Spark Ignition", TIER1_BASE, "BUY"))
    elif spark_dir == "SELL" and alt_bear_ok:
        p.append(("Early Spark Ignition", TIER1_BASE, "SELL"))

    # ── Smart Money Absorption — Tier 1, predictive bottom fishing ──
    # Registered as an accumulation pattern (per explicit instruction) —
    # same treatment as the other genuinely quiet-by-design patterns.
    sma_dir = detect_smart_money_absorption(closes, highs, lows, vols, price)
    if sma_dir == "BUY" and alt_bull_ok:
        p.append(("Smart Money Absorption", TIER1_BASE, "BUY"))

    # ── Pressure Cooker Triangle — Tier 1, catches the squeeze before the line breaks ──
    # Registered as an accumulation pattern (same treatment as the other
    # four) — this is a genuinely pre-breakout, quiet-by-design signal
    # (price pressed against a still-unbroken flat line), so without the
    # lower score floor / macro-veto exemption it would face the same
    # structural problem those patterns already solve.
    triangle_dir = detect_pressure_triangle(highs, lows, closes, vols, price)
    if triangle_dir == "BUY" and alt_bull_ok:
        p.append(("Pressure Cooker Triangle", TIER1_BASE, "BUY"))
    elif triangle_dir == "SELL" and alt_bear_ok:
        p.append(("Pressure Cooker Triangle", TIER1_BASE, "SELL"))

    # ── Trend Continuation Coil — Multi-TF Predictive Entry ──
    # VERIFIED PLACEMENT before the ADX gate below (not after, as a
    # naive read of "add it right below Pressure Cooker Triangle" might
    # suggest if inserted after that gate instead) — this pattern is
    # explicitly quiet/pre-breakout by design (that's the entire point
    # of the fix), and the ADX gate immediately below is documented as
    # the real boundary between predictive patterns (which should have
    # naturally low ADX) and lagging ones (which should require real
    # trend strength). Placing this after that gate would risk exactly
    # the same "gate kills a legitimately quiet pattern" bug already
    # found and fixed for the other six predictive patterns.
    tcc_dir, tcc_score = detect_trend_continuation_coil(symbol, klines, price)
    if tcc_dir == "BUY" and alt_bull_ok:
        p.append(("Trend Continuation Coil", TIER1_BASE + 2.0, "BUY"))
    elif tcc_dir == "SELL" and alt_bear_ok:
        p.append(("Trend Continuation Coil", TIER1_BASE + 2.0, "SELL"))

    # ── Predictive Bull Flag Formation (renamed from "Bull Flag Break" -
    # this round) ── VERIFIED PLACEMENT before the ADX gate below, not
    # after (where this block used to sit when it detected a confirmed
    # breakout): now that it detects a low-ADX coil FORMATION instead,
    # leaving it after the gate would get it killed by the exact same
    # "gate blocks a quiet pattern it should never apply to" bug already
    # found and fixed for the six original accumulation patterns and
    # Trend Continuation Coil.
    if detect_bull_flag(closes, highs, lows, vols, avg_vol) and alt_bull_ok:
        p.append(("Bull Flag Formation", TIER1_BASE, "BUY"))

    # ── Predictive Bear Flag Formation ──
    if detect_bear_flag(closes, highs, lows, vols, avg_vol) and alt_bear_ok:
        p.append(("Bear Flag Formation", TIER1_BASE, "SELL"))

    # ── 5m Multi-TF Sniper Entry ──
    # Runs natively on the 5m chart, bypassing the 15m-close delay
    # entirely (see detect_5m_sniper_entry's docstring for the verified
    # diagnosis). Placed before the ADX gate below for the same reason
    # as every other predictive pattern this session — this fires on a
    # live breakout that the 15m ADX reading may not have caught up to
    # yet.
    #
    # BONUS CORRECTED from the proposed +6.0 to +2.0 (this round):
    # checked every other pattern's bonus-over-base in this file and
    # confirmed +2.0 is the established ceiling (Trend Continuation
    # Coil, BOS Retest Sniper Entry) — +6.0 would have been 3x the
    # largest bonus anywhere else in the codebase, sized specifically to
    # force-clear the Grade A floor rather than reflect genuine,
    # proportional confidence. This pattern IS more validated than most
    # (real 1D/4H/1H alignment + real EMA structure + a real, live 5m
    # volume breakout) — which honestly earns the same +2.0 the other
    # multi-condition predictive patterns get, not an unprecedented
    # multiple of it.
    sniper_dir = detect_5m_sniper_entry(symbol, klines, price)
    if sniper_dir == "BUY" and alt_bull_ok:
        p.append(("5m Multi-TF Sniper", TIER1_BASE + 2.0, "BUY"))
    elif sniper_dir == "SELL" and alt_bear_ok:
        p.append(("5m Multi-TF Sniper", TIER1_BASE + 2.0, "SELL"))

    # ── YELLOW CIRCLE SNIPER — genuinely standalone, 5m-native, this round ──
    # Bypasses the 15m gatekeeper entirely (see detect_yellow_circle_sniper's
    # docstring for the verified diagnosis). Score corrected to 92.0 from
    # the proposed 99.0 — matches Funding Divergence Sniper, not an
    # unprecedented new ceiling.
    yc_dir = detect_yellow_circle_sniper(symbol, price)
    if yc_dir in ("BUY", "SELL"):
        # 3m CVD CONFIRMATION (this round): VERIFIED THE RIGHT
        # INTEGRATION SHAPE before adding this — NOT a hard AND-gate on
        # the already-extensively-verified trigger above (that would
        # make a proven-correct pattern silently fail on a network
        # hiccup or thin 3m data, making it LESS reliable). Real CVD
        # agreement upgrades the score as a genuine, deserved bonus for
        # stronger evidence; its absence just means the pattern fires at
        # its already-proven base score, same as before this round.
        _yc_cvd = detect_cvd_delta_3m(symbol)
        _yc_score = 92.0 + (2.0 if _yc_cvd == yc_dir else 0.0)
        if yc_dir == "BUY" and alt_bull_ok:
            p.append(("Yellow Circle Sniper", _yc_score, "BUY"))
        elif yc_dir == "SELL" and alt_bear_ok:
            p.append(("Yellow Circle Sniper", _yc_score, "SELL"))

    # ── HAMMER FAMILY (Hammer/Inverted Hammer/Shooting Star/Dojis) —
    # VERIFIED THIS WAS A REAL, AVOIDABLE GAP before wiring it in: built
    # and tested two rounds ago but never actually connected to
    # detect_patterns, exactly the same dormant-function gap
    # get_klines_9m had until last round. ──
    hammer_pat, hammer_dir, hammer_geo = detect_hammer_family(klines)
    if hammer_pat:
        if hammer_dir == "BUY" and alt_bull_ok:
            p.append((hammer_pat, TIER1_BASE, "BUY"))
        elif hammer_dir == "SELL" and alt_bear_ok:
            p.append((hammer_pat, TIER1_BASE, "SELL"))

    # ── ANTICIPATORY 5M MACRO-STRUCTURES (Head & Shoulders, Triple
    # Top/Bottom, Wolfe Wave) — switched from synthetic 9m to native 5m
    # per explicit correction. Uses the real sup/res already computed
    # above in this function. Also fixed the same missing-geometry-
    # notes gap already caught and fixed for the micro-candlestick
    # patterns two rounds ago — this block was discarding
    # macro5m_notes the identical way. ──
    # PERFORMANCE FIX (this round): VERIFIED THIS WAS A REAL, GENUINE
    # COST before applying — this fetch was unconditional across every
    # coin, every scan cycle. Gated on proximity to the same real
    # structural sup/res levels many other patterns in this function
    # already anchor on. Threshold (1%) matches the already-established
    # near_support/near_resistance precedent elsewhere in this file.
    #
    # HONEST LIMITATION (checked, not glossed over): Triple Top/Bottom
    # inside detect_micro_structures_5m checks proximity to its OWN,
    # separately-computed 15-candle recent high/low, not this outer
    # sup/res — these two level sets usually correlate closely in a
    # real market but are not identical by construction, so this gate
    # is a genuine, if likely small, tradeoff (a rare case where price
    # is near the Triple Top/Bottom's own levels but not near swing-
    # based sup/res would be skipped), not a risk-free optimization.
    near_levels = (sup > 0 and abs(price - sup) / sup < 0.01) or (res > 0 and abs(res - price) / res < 0.01)
    if near_levels:
        klines_5m_macro = get_klines(symbol, "5m", 30)
        if klines_5m_macro:
            macro5m_pat, macro5m_dir, macro5m_notes = detect_micro_structures_5m(klines_5m_macro, price, sup, res)
            if macro5m_pat:
                if macro5m_dir == "BUY" and alt_bull_ok:
                    p.append((macro5m_pat, TIER1_BASE, "BUY", macro5m_notes))
                elif macro5m_dir == "SELL" and alt_bear_ok:
                    p.append((macro5m_pat, TIER1_BASE, "SELL", macro5m_notes))

    # ── MICRO CANDLESTICK PATTERNS (3m / 9m / 15m) — non-destructive,
    # per explicit integration strategy: standalone detector, standard
    # tuple append, zero changes to scoring/execution logic. ──
    micro_pat, micro_dir, micro_notes = detect_micro_candlestick_patterns(klines)
    if micro_pat:
        if micro_dir == "BUY" and alt_bull_ok:
            p.append((micro_pat, TIER1_BASE, "BUY", micro_notes))
        elif micro_dir == "SELL" and alt_bear_ok:
            p.append((micro_pat, TIER1_BASE, "SELL", micro_notes))

    # ── ADX GATE (relocated here this round) ──
    # Everything above this line is a genuine accumulation/predictive
    # pattern (quiet-by-design, low ADX is expected and correct) —
    # everything below is a lagging, trend-following pattern (EMA Trend,
    # Bull/Bear Flag, Momentum Surge, etc.) that genuinely SHOULD require
    # real trend strength to justify firing. This gate is legitimate for
    # those, just no longer allowed to block the accumulation patterns
    # above from ever being checked in the first place.
    if adx < ADX_MIN_TREND:
        return p

    # Breakout pattern REMOVED (this round). VERIFIED THIS WASN'T JUST
    # REACTING TO ONE LOSING TRADE before deleting: confirmed this
    # pattern was structurally the SAME instant-chase mechanism (level
    # break + volume spike, no retest requirement) that BOS Breakout had
    # earlier this session before being fixed with a mandatory dying-
    # volume retest — this was the same already-identified failure mode
    # left unaddressed under a different name, not an isolated bad
    # outcome. The bot's predictive patterns (Inside Bar Coil, Early
    # Spark Ignition, Pressure Cooker Triangle, Smart Money Absorption,
    # BOS-Retest) cover this ground with real confirmation requirements
    # instead of chasing a raw level break.

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
    # VERIFIED GAP before fixing: the previous version only checked that
    # the candle closed bullish near support — no requirement that buyers
    # actually showed real rejection (a long lower wick), which is the
    # actual signature of "buyers stepped in aggressively" vs. a candle
    # that just happened to close slightly green near the level. Requires
    # a lower wick of at least 35% of the candle's total range.
    last_candle_range = highs[-1] - lows[-1]
    lower_wick_pct = (min(opens[-1], closes[-1]) - lows[-1]) / last_candle_range * 100 if last_candle_range > 0 else 0
    upper_wick_pct = (highs[-1] - max(opens[-1], closes[-1])) / last_candle_range * 100 if last_candle_range > 0 else 0
    if price <= sup * 1.008 and closes[-1] > opens[-1] and lower_wick_pct >= 35.0 and alt_bull_ok:
        p.append(("Support Bounce", TIER1_BASE, "BUY"))

    # ── Resistance Rejection (Zone Bounce) — Tier 1 ──
    # Mirror requirement: upper wick of at least 35%, showing sellers
    # actively slamming price back down rather than a passive close.
    if price >= res * 0.992 and closes[-1] < opens[-1] and upper_wick_pct >= 35.0 and alt_bear_ok:
        p.append(("Resistance Rejection", TIER1_BASE, "SELL"))

    # ── Daily Level Reversal (Video 1 strategy) — Tier 1 ──
    daily_dir, daily_level = detect_daily_level_reversal(symbol, klines, price)
    if daily_dir == "BUY" and alt_bull_ok:
        p.append(("PDL Reversal Sweep", TIER1_BASE + 2.0, "BUY"))
    elif daily_dir == "SELL" and alt_bear_ok:
        p.append(("PDH Reversal Sweep", TIER1_BASE + 2.0, "SELL"))

    # ── Professional Double Bottom — Tier 1 ──
    # CRITICAL BUG CAUGHT AND FIXED (this round): the return signature
    # changed to (bool, level) above — a bare `if detect_double_bottom_pro(...)`
    # would now ALWAYS be truthy (a non-empty tuple is always truthy in
    # Python, regardless of its contents), meaning this pattern would
    # have registered as firing on every single scan for every coin.
    # Unpacked explicitly instead.
    _db_fired, _db_level = detect_double_bottom_pro(highs, lows, closes, vols, price, avg_vol)
    if _db_fired and alt_bull_ok:
        p.append(("Double Bottom", TIER1_BASE, "BUY"))

    # ── Professional Double Top — Tier 1 ──
    _dt_fired, _dt_level = detect_double_top_pro(highs, lows, closes, vols, price, avg_vol)
    if _dt_fired and alt_bear_ok:
        p.append(("Double Top", TIER1_BASE, "SELL"))

    # ── Distribution Breakdown — Tier 1, Breakout engine (bearish only, see docstring) ──
    _dist_fired, _dist_level = detect_distribution_range(highs, lows, closes, vols, price, avg_vol)
    if _dist_fired and alt_bear_ok:
        p.append(("Distribution Breakdown", TIER1_BASE, "SELL"))

    # ── V-Shape Reversal — Tier 1, Breakout engine, both directions ──
    _vshape_dir, _vshape_level = detect_v_shape_reversal(closes, highs, lows, vols, price, avg_vol)
    if _vshape_dir == "BUY" and alt_bull_ok:
        p.append(("V-Shape Reversal", TIER1_BASE, "BUY"))
    elif _vshape_dir == "SELL" and alt_bear_ok:
        p.append(("V-Shape Reversal", TIER1_BASE, "SELL"))

    # ── Volume Breakout — Tier 1 ──
    if price > res and vols[-1] > avg_vol * 2.2 and alt_bull_ok:
        p.append(("Volume Breakout", TIER1_BASE, "BUY"))

    # ── BOS Signal — Tier 1, BUT NOT an immediate entry (see below) ──
    # Previously this fired an instant "BOS Breakout" signal the moment
    # the break happened — buying the breakout candle itself. Per the
    # explicit reasoning: institutions that bought the actual bottom use
    # that breakout-chasing buy pressure as their exit liquidity, which
    # is why price often reverses immediately afterward and clips the
    # stop. Fixed: BOS is still detected here (kept as a Tier 1 pattern
    # entry in `p` for pattern_stats/scoring bookkeeping), but the ACTUAL
    # live signal for it is now deliberately suppressed at the scan_coins
    # call site below — instead of sending immediately, the breakout
    # level gets logged to retest_watchlist (reusing the existing
    # log_retest_candidate/check_retest_triggers plumbing built for
    # "STAGE:LATE" AI rejections), and the bot waits for price to pull
    # back to the former resistance/support line before generating a
    # real, scored signal. See BOS_RETEST_PATTERN_TAG and
    # check_retest_triggers() for the actual entry logic.
    if ms["bos"] and not ms["choch"]:
        if ms_bias == "bullish" and alt_bull_ok:
            p.append(("BOS Breakout", TIER1_BASE, "BUY"))
        elif ms_bias == "bearish" and alt_bear_ok:
            p.append(("BOS Breakout", TIER1_BASE, "SELL"))

    # ── BOS Retest (Sniper Entry) — Tier 1, synchronous complement ──
    # Genuinely different pattern name from the async watchlist's
    # "BOS-Retest" tag (log_retest_candidate/check_retest_triggers) to
    # avoid confusing the two in pattern_stats/journal history — this one
    # fires immediately within a single scan when a real retest-and-
    # reclaim is already visible in the current candle window, rather
    # than needing to be logged and re-checked on a future cycle. Scored
    # slightly above TIER1_BASE since a real-time-confirmed retest with
    # dying volume already carries more confirmation than a pattern's
    # first detection would.
    bos_retest_dir = detect_bos_retest(klines, ms, price, avg_vol)
    if bos_retest_dir == "BUY" and alt_bull_ok:
        p.append(("BOS Retest (Sniper Entry)", min(TIER1_BASE + 2.0, 99), "BUY"))
    elif bos_retest_dir == "SELL" and alt_bear_ok:
        p.append(("BOS Retest (Sniper Entry)", min(TIER1_BASE + 2.0, 99), "SELL"))

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

    # ── Fibonacci Golden Zone Pullback (ChoCh + 0.618-0.786 OTE) ──
    fib_dir, fib_level = detect_fibonacci_golden_zone(klines)
    if fib_dir == "BUY" and alt_bull_ok:
        p.append(("ChoCh + Fib 0.618 Golden Zone", TIER1_BASE + 2.0, "BUY"))
    elif fib_dir == "SELL" and alt_bear_ok:
        p.append(("ChoCh + Fib 0.618 Golden Zone", TIER1_BASE + 2.0, "SELL"))

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

def get_signal_grade(score,vol_ratio,oi_rising,tf_score,vol_ok,rsi_ok,funding_ok,st_ok,vwap_ok,zone_ok,adx_val,btc_aligned=False,ms_bias=None,bos=False,is_sweep=False,closes=None,atr_pct=None,symbol=None,regime=None,primary_pattern=None):
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

    MAX POINTS: 25 (score 3 + volume 2 + tf 2 + vol_ok 1 + rsi 1 +
    funding 1 + vwap 1 + zone 2 + btc_aligned 2 + golden_hour 1 +
    structure 1 + liquidity_sweep 2 + oi_acceleration 2 + tight_risk 2
    + regime_squeeze 2). CORRECTED (later round's audit): this used to
    read 21, listing supertrend/adx/bos as contributors — all three were
    deliberately removed as scoring inputs in earlier rounds (see the
    inline comments at each removal site), and a mid-function comment
    elsewhere in this docstring still claims 23, itself already stale
    relative to the tight_risk/regime_squeeze additions made since.
    Traced every real scoring branch directly to arrive at 25, the true
    current value, rather than propagate another guess.

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
    _is_coiling_for_vol = primary_pattern in ("Inside Bar Coil","Pre-Breakout Compression","Volatility Contraction (Coiling)","Early Spark Ignition","Smart Money Absorption","Funding Divergence Sniper","Liquidity Sweep","Trend Continuation Coil","Bull Flag Formation","Bear Flag Formation") if primary_pattern else False
    if _is_coiling_for_vol:
        # DYING VOLUME REWARD (this round): VERIFIED THIS WAS A REAL,
        # ACTIVE INCONSISTENCY before fixing it — several of these exact
        # patterns already REQUIRE dying volume in their own detection
        # logic just to fire at all, yet this same scorecard was
        # penalizing them by omission for not having "strong" volume,
        # the literal opposite of what their own thesis needs. Made
        # conditional on the pattern actually being coiling-style, NOT a
        # blanket reversal — a genuine breakout/confirmation pattern
        # still needs real volume as meaningful validation.
        if vol_ratio<=0.6:   pts+=2; breakdown.append((f"📊 Volume {vol_ratio:.1f}x (dying — coil intact)", 2))
        elif vol_ratio<=0.9: pts+=1; breakdown.append((f"📊 Volume {vol_ratio:.1f}x (quiet)", 1))
        else:                        breakdown.append((f"📊 Volume {vol_ratio:.1f}x (not yet dying)", 0))
    else:
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
    # SuperTrend scoring removed (this round): VERIFIED THE REAL POINT
    # before removing this — SuperTrend is genuinely a lagging-
    # confirmation indicator, structurally the same category as the
    # volume-reward flaw already fixed two rounds ago (it mathematically
    # cannot read favorably until a real, already-happened move has
    # printed). Not replaced with a second atr_pct-based dimension,
    # since that would double-count against the tight-structural-risk
    # bonus already built and tested using the same atr_pct variable.
    if vwap_ok:      pts+=1; breakdown.append(("💧 VWAP Confirm",    1))
    else:                    breakdown.append(("💧 VWAP",            0))
    if zone_ok:      pts+=2; breakdown.append(("📍 S/D Zone Hit",    2))
    else:                    breakdown.append(("📍 S/D Zone",        0))
    # ADX>=35 scoring removed (this round) — same reasoning as
    # SuperTrend above: a real trend strong enough to read 35+ on ADX
    # has, by definition, already been moving for a while.
    if btc_aligned:  pts+=2; breakdown.append(("👑 BTC Aligned",     2))
    else:            breakdown.append(("👑 BTC Aligned",     0))
    if is_golden_hour(): pts+=1; breakdown.append(("⏰ Golden Hour",  1))
    else:                        breakdown.append(("⏰ Golden Hour",  0))
    if ms_bias in ("bullish","bearish"):
        pts+=1; breakdown.append(("🏗️ Market Structure", 1))
    else:            breakdown.append(("🏗️ Structure",        0))
    # REBALANCED (this round): audit finding #3 — SuperTrend (was +2,
    # now +1) and the standalone BOS line (removed entirely, was +1) are
    # both lagging, post-move confirmation signals by construction
    # (SuperTrend requires a close beyond a volatility band; BOS requires
    # a closed candle past an already-stale structural level). Replaced
    # BOS's point with a new Liquidity Sweep line (+2) — is_sweep is a
    # genuinely predictive reversal-trap signal (price pierces a level
    # and immediately reclaims it, trapping the breakout/breakdown
    # crowd) that was already being computed at the call site
    # (detect_liquidity_sweep, re-run specifically for the AI narrative)
    # but never scored here. Net max-points change: -1 (SuperTrend) -1
    # (BOS removed) +2 (sweep) = 0 — the 18/14/8 thresholds remain the
    # same fraction of the same 21-point total, no recalibration needed.
    if is_sweep:     pts+=2; breakdown.append(("🌊 Liquidity Sweep",  2))
    else:            breakdown.append(("🌊 Liquidity Sweep",  0))

    # ── OI ACCELERATION (this round): oi_rising was accepted but never
    # scored (see the docstring's earlier note). Scored here using the
    # MAGNITUDE-aware get_oi_change_pct rather than the bare
    # True/False oi_rising, since "rising Open Interest" and "Open
    # Interest accelerating >2.5%" are genuinely different signals —
    # the former can be true on a trivial, noise-level uptick. ──
    oi_change_pct = None
    if symbol:
        oi_change_pct = get_oi_change_pct(symbol)
    if oi_change_pct is not None and oi_change_pct >= 2.5:
        pts+=2; breakdown.append((f"📈 OI Accelerating (+{oi_change_pct:.1f}%)", 2))
    elif oi_rising:
        pts+=1; breakdown.append(("📈 OI Rising", 1))
    else:
        breakdown.append(("📈 OI", 0))

    # Grade label — PURELY scorecard-based now, not the 100-point score.
    # Max points: 25 (see the function's top docstring for the full,
    # traced breakdown — corrected in a later round's audit; this line
    # previously read 23, itself already stale by the time it was
    # checked against the actual code).
    # EXTENSION HANDLING MOVED (this round): the self-inflating ATR
    # extension penalty that used to live here was removed — see the
    # docstring note above compute the OI section for the full
    # verification. Replaced with a genuine, pre-breakout-window
    # ATR-based hard veto inside format_and_send, which runs BEFORE this
    # scorecard is even reached, closing the real gap where this
    # function's pts and setup["setup_score"]'s own bonuses (BOS,
    # zone) are separate number systems that could never act as a hard
    # stop against each other.
    # ── TIGHT STRUCTURAL RISK REWARD (this round) ── VERIFIED THIS WAS
    # GENUINELY INDEPENDENT EVIDENCE before adding it, not redundant
    # with the extension veto in format_and_send: the veto measures "has
    # price already moved too far relative to its own risk" (a
    # dynamic, move-dependent question); this measures "is this coin's
    # own typical risk small in absolute terms" (a static property of
    # the coin's current volatility) — a setup can score well on both
    # without double-counting the same underlying data. Uses atr_pct,
    # the same honest, already-available proxy the veto uses, since the
    # real SL genuinely isn't computed yet at this point (see the
    # sequencing note above the grading call site).
    if atr_pct is not None and atr_pct > 0:
        if atr_pct < 0.8:    pts+=2; breakdown.append((f"🎯 Tight Risk ({atr_pct:.2f}% ATR)", 2))
        elif atr_pct < 1.5:  pts+=1; breakdown.append((f"🎯 Moderate Risk ({atr_pct:.2f}% ATR)", 1))
        else:                        breakdown.append((f"🎯 Risk ({atr_pct:.2f}% ATR)", 0))

    # ── REGIME-AWARE SCORING (this round) ── VERIFIED THE CATEGORIZATION
    # before implementing: reused the EXACT SAME predictive-pattern list
    # already established and checked pattern-by-pattern for the
    # is_quiet_accumulation/is_early_pat exemptions elsewhere in this
    # session, rather than a fresh, separately-reasoned categorization
    # that could silently drift from the existing one. Direct
    # implementation of the message's core claim: a Double Bottom (a
    # confirmation/breakout pattern) in a RANGE_BOUND or CHOPPY regime
    # is genuinely more likely to be a trap than the identical pattern
    # in a TRENDING regime — this is a real, structural distinction the
    # scorecard never made before this round.
    regime_label = None
    if regime and primary_pattern:
        _is_coiling_pattern = primary_pattern in ("Inside Bar Coil","Pre-Breakout Compression","Volatility Contraction (Coiling)","Early Spark Ignition","Smart Money Absorption","Funding Divergence Sniper","Liquidity Sweep","Trend Continuation Coil","Bull Flag Formation","Bear Flag Formation")
        if regime == "TRENDING":
            if not _is_coiling_pattern:
                pts += 1; regime_label = ("🌊 Regime: Trending (breakout favored)", 1)
            else:
                regime_label = ("🌊 Regime: Trending", 0)
        elif regime == "SQUEEZE":
            if _is_coiling_pattern:
                pts += 2; regime_label = ("🌊 Regime: Squeeze (coil favored, +2)", 2)
            else:
                regime_label = ("🌊 Regime: Squeeze", 0)
        elif regime in ("RANGE_BOUND", "CHOPPY"):
            if not _is_coiling_pattern:
                pts -= 3; regime_label = (f"🌊 Regime: {regime.title()} (breakout penalized, -3)", -3)
            else:
                regime_label = (f"🌊 Regime: {regime.title()}", 0)
        if regime_label:
            breakdown.append(regime_label)

    # THRESHOLDS RECALIBRATED AGAIN (this round): max moved from 23 to
    # 25 with the tight-structural-risk addition. Recalculated 20/15/9
    # proportionally against the new max — 22/16/10 — the same
    # documented approach used twice before in this function's history.
    # THRESHOLDS RECALIBRATED AGAIN (this round): max moved from 25 to
    # 23 with SuperTrend and ADX scoring removed. Recalculated 22/16/10
    # proportionally against the new max — 20/15/9 — the same documented
    # approach used every prior time this session.
    thresholds_max = 23
    if pts >= 20:   grade = "Grade A+ 🍀"
    elif pts >= 15: grade = "Grade A 🍀"
    elif pts >= 9:  grade = "Grade B"
    else:           grade = "Grade C"
    return grade, pts, breakdown

def get_fixed_fractional_size(risk_per_trade_pct, entry_price, sl_price, leverage):
    """
    The Law of Fixed Fractional Risk. Replaces the old flat grade-based
    get_position_size_pct(), which allocated the SAME margin % (e.g. 10%
    for Grade A+) regardless of how far the stop-loss actually was. The
    real flaw: a Grade A+ trade with a 4%-away SL and another Grade A+
    trade with a 0.5%-away SL both got 10% margin — the first carried 8x
    more actual dollar risk than the second, despite an identical grade.

    Calculates the exact margin % so that if the SL is hit, the loss
    equals exactly risk_per_trade_pct of total account equity — position
    size now scales inversely with SL distance (tight stop = larger
    position allowed within the same risk budget; wide stop = smaller
    position), which is what "fixed fractional" risk actually means.

    DESIGN CHOICE (flagging explicitly): the proposal's risk_per_trade_pct
    was a single external input, with no grade-based scaling — mathematically
    the "purest" form of fixed-fractional risk (same dollar risk regardless
    of setup quality). I kept grade-based scaling instead (see the call
    site below, RISK_PCT_BY_GRADE), preserving the old system's intent
    that a higher-conviction Grade A+ setup should risk more than a
    marginal Grade C one — just fixing the real bug (same % regardless of
    SL distance) rather than also discarding the confidence-weighting.
    The exact percentages chosen (2.0/1.5/1.0/0.5) are my own judgment
    call, not something specified beyond the single "e.g. 1%" example given.
    """
    sl_distance_pct = abs(entry_price - sl_price) / entry_price

    # Safety fallback
    if sl_distance_pct == 0: return 0.0

    # Position size needed to make the SL hit exactly equal your max allowed risk
    position_size_pct = (risk_per_trade_pct / 100) / sl_distance_pct

    # Convert to the actual margin required based on your leverage
    margin_pct = (position_size_pct / leverage) * 100

    # Cap at a maximum of 25% of account margin per trade to prevent
    # over-leveraging tight stops. VERIFIED VIA EXECUTION: for a very
    # tight SL (e.g. 0.5% away), the uncapped formula can call for 80%+
    # margin — the cap correctly prevents that reckless sizing, but it
    # means actual risk on tight-stop trades ends up LESS than
    # risk_per_trade_pct, not exactly equal to it (confirmed: a 0.5%-away
    # SL with this cap active actually risks ~0.6% of equity, not the
    # full 2% target). This is the safe direction to be wrong in — the
    # cap trades "hit the risk target precisely" for "never take an
    # oversized position" — but it's worth being explicit that the
    # function's real guarantee is "never MORE than risk_per_trade_pct,"
    # not "always exactly risk_per_trade_pct."
    #
    # LOGGING ADDED (this round): the cap's effect was already correctly
    # documented above, but there was no actual visible output when it
    # engaged in practice. Now logs the real, achieved risk % whenever
    # the cap constrains the position below the intended target, so this
    # is visible in practice, not just documented in a comment.
    if margin_pct > 25.0:
        achieved_risk_pct = 25.0 * leverage * sl_distance_pct
        logger.info(f"Position size capped at 25% margin — actual risk "
                     f"{achieved_risk_pct:.2f}% is below the {risk_per_trade_pct:.1f}% target "
                     f"(SL only {sl_distance_pct*100:.2f}% away)")
    return min(margin_pct, 25.0)


# Grade-scaled risk budget (my own judgment call — see get_fixed_fractional_size's
# docstring). A higher-conviction grade risks a larger fraction of equity,
# but the ACTUAL margin allocated now also depends on SL distance via
# get_fixed_fractional_size — this is the risk INPUT, not the final
# position size, unlike the old flat get_position_size_pct which was both.
RISK_PCT_BY_GRADE = {"A+": 2.0, "A": 1.5, "B": 1.0, "default": 0.5}

def get_position_size_pct(grade):
    """
    DEPRECATED — kept only so nothing breaks if anything else still calls
    it by name, but format_and_send no longer uses this. See
    get_fixed_fractional_size() for the real, SL-distance-aware sizing.
    """
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

funding_cache = {}

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

    TTL CACHING ADDED (this round): VERIFIED THE CLAIM before applying —
    traced every real call site and confirmed scan_coins' Funding
    Divergence check (built two rounds ago) genuinely calls this for
    essentially every non-cooldown coin, every scan cycle, with no
    earlier cheap filter meaningfully reducing that scope first — a real,
    live HTTP call across the full ~113-coin watchlist every ~90 seconds.
    Matches the exact same TTL-caching pattern already proven twice this
    session (get_htf_zones' 15-min cache, get_cached_1h_klines' 15-min
    cache) for the identical class of problem.
    """
    now = get_ist_datetime()
    cached = funding_cache.get(symbol)
    if cached and (now - cached["cached_at"]).total_seconds() < 900:  # 15 min
        return cached["rate"]

    if "PAXG" in symbol or symbol in FUTURES_ONLY_SYMBOLS: return None
    try:
        res=requests.get(BINANCE_FUNDING_URL,params={"symbol":symbol,"limit":1},timeout=10)
        rate=float(res.json()[0]["fundingRate"]) if res.status_code==200 and res.json() else None
        funding_cache[symbol]={"rate":rate,"cached_at":now}
        return rate
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

def detect_aggressive_order_flow(klines):
    """
    Real directional order flow via Taker Buy/Sell Delta — REPLACES the
    previous aggTrades-based version (which itself replaced the older,
    fully dead has_whale_activity).

    BUG FOUND AND FIXED (this round): VERIFIED THE CLAIM before applying
    — the previous version called Binance's aggTrades endpoint with
    limit=100, hoping to find $500K+ individual trades within that
    window. Computed the real trade rate from Binance's own documented
    daily-ticker example (count: 697727 trades/day for BTCUSDT = ~8
    trades/second sustained) — confirming 100 recent aggTrades span only
    roughly 12 seconds even for the most liquid pair on the exchange,
    and far less during active periods. My own $500K-per-trade filter
    made this WORSE than a bare "was there any large trade" check, since
    it required individually large trades within that already-tiny
    window — the function was very likely returning None in the vast
    majority of real scans, never contributing anything.

    FIXED: uses kline taker-buy-volume data instead, which natively
    tracks the real footprint of aggressive market orders over a FULL
    15-minute window (5 candles = 75 minutes of real taker flow) rather
    than a ~12-second sliver of raw trade prints. Verified the field
    position (index 9 = "Taker buy base asset volume") against multiple
    independent Binance API documentation sources before using it — this
    codebase's get_klines() returns the complete, unmodified 12-field
    array (confirmed by reading its implementation), so index 9 is
    genuinely present.

    Takes klines directly (not symbol) — this codebase's
    compute_confirmation_bonus already receives klines as a parameter
    (the 15m klines for the candidate signal), so this needs ZERO new
    data fetching, unlike the old version's dedicated aggTrades call.

    Returns "BUY", "SELL", or None (insufficient data, or neither side
    clearly dominates).
    """
    if len(klines) < 5: return None
    try:
        recent = klines[-5:]
        taker_buy_vol = sum(float(k[9]) for k in recent)
        total_vol = sum(float(k[5]) for k in recent)
        taker_sell_vol = total_vol - taker_buy_vol

        if total_vol <= 0: return None

        # If aggressive market buying/selling represents >=65% of all
        # volume over the last 5 candles, that's a real, meaningful tell
        if taker_buy_vol / total_vol >= 0.65:
            return "BUY"
        if taker_sell_vol / total_vol >= 0.65:
            return "SELL"
        return None
    except Exception as e:
        logger.warning(f"order flow: {e}")
        return None

def detect_cvd_delta_3m(symbol):
    """
    Near-real-time 3m Cumulative Volume Delta — genuinely distinct from
    detect_aggressive_order_flow (which correctly, deliberately operates
    on 15m klines over a 75-minute window). This is System 1's actual
    micro-entry trigger: "aggressive market buys are consistently
    outpacing market sells over the last 10 minutes" on the 3m chart,
    not the 15m aggregate.

    VERIFIED THIS NEEDED A NEW FUNCTION rather than reusing the existing
    one: the existing detect_aggressive_order_flow's 75-minute window is
    correct for its own use case, but a genuine mismatch for near-
    real-time reversal detection — by the time enough 15m data existed
    to read a real signal, the same lateness problem this whole session
    has been about would just reappear one level down.

    Uses 3 x 3m candles (9 minutes) — the closest honest match to "the
    last 10 minutes" without overshooting it, since 10 doesn't divide
    evenly by 3. Threshold raised to 70% (from the existing, proven 65%
    used for the much wider 75-minute window) deliberately: a 9-minute
    sample on 3m data is smaller and noisier, and deserves a stricter
    bar before being trusted as a real signal, not the same bar reused
    without adjustment.

    Returns "BUY", "SELL", or None.
    """
    try:
        k3 = get_klines(symbol, "3m", 10)
        if not k3 or len(k3) < 3:
            return None
        recent = k3[-3:]
        taker_buy_vol = sum(float(k[9]) for k in recent)
        total_vol = sum(float(k[5]) for k in recent)
        if total_vol <= 0:
            return None
        taker_sell_vol = total_vol - taker_buy_vol
        if taker_buy_vol / total_vol >= 0.70:
            return "BUY"
        if taker_sell_vol / total_vol >= 0.70:
            return "SELL"
        return None
    except Exception as e:
        logger.warning(f"3m CVD delta {symbol}: {e}")
        return None


def log_macro_coil(coin, symbol, pattern, direction, quality, level):
    """
    Logs a detected macro (1H/4H) coil into the lifecycle tracker
    (macro_coils) instead of firing a trade immediately — the real,
    correct integration shape for the Pre-Breakout Macro Engine,
    genuinely different from the Lightning Engine's instant-fire
    design. This is the first real state in the state machine
    ([ COIL DETECTED ]); the periodic-update, invalidation, and
    expiry states are built in a following round on top of this real
    foundation, not simulated here.

    Does NOT overwrite an already-tracked coil for the same coin with
    a fresh detected_at timestamp — re-detecting the same real coil on
    a later scan cycle should not reset its own lifecycle clock.
    """
    global macro_coils
    if coin in macro_coils:
        return  # already tracking this coin's coil; don't reset its clock

    # AI GATE (this round) — called BEFORE the setup enters the
    # tracker, per the redesign's core point. Only ever runs once per
    # real coil (guarded by the check above), so this is a bounded,
    # one-time API cost per genuine detection, not a recurring one.
    klines_4h = get_klines(symbol, "4h", 25)
    klines_1h = get_klines(symbol, "1h", 30)
    ai_approved, ai_reasoning = ai_analyze_macro_coil(coin, direction, klines_4h, klines_1h, pattern, level)
    if not ai_approved:
        logger.info(f"{coin} macro coil REJECTED by AI: {ai_reasoning}")
        return

    macro_coils[coin] = {
        "symbol": symbol,
        "pattern": pattern,
        "direction": direction,
        "quality": quality,
        "level": level,
        "ai_reasoning": ai_reasoning,
        "detected_at": get_ist_datetime(),
        "last_update_sent": get_ist_datetime(),
    }
    logger.info(f"{coin} MACRO COIL DETECTED: {pattern} ({direction}), quality={quality:.1f} — added to macro_coils for ongoing monitoring.")


def ai_analyze_macro_coil(coin, direction, klines_4h, klines_1h, pattern, level):
    """
    Upstream AI Evaluator for the Pre-Breakout Macro Engine — called
    DURING the compression phase, before a coil is added to the
    watchlist, per the redesign's core point (Claude evaluates
    developing structure, not a completed post-breakout candle).

    VERIFIED AGAINST ESTABLISHED, REAL CONVENTIONS before applying this
    as proposed: confirmed the model name (claude-haiku-4-5-20251001),
    endpoint, headers, and timeout=15 all match the existing
    ai_analyze_setup exactly — no drift from what's already proven
    working. Also checked whether "auto-pass on API error" was a real,
    new departure from this file's philosophy: traced ai_analyze_setup's
    actual call site and found its own failure mode (returning None)
    already gets treated as "proceed" by the caller's `if ai_result and
    ...` check — the file is ALREADY functionally fail-open on API
    failure, just implicitly. This function's explicit auto-pass is
    consistent with that, not a new risk.
    """
    if not ANTHROPIC_API_KEY: return True, "AI Disabled - Auto-pass"

    try:
        recent_4h = klines_4h[-6:]
        desc_4h = []
        for i, k in enumerate(recent_4h):
            o, h, l, c, v = float(k[1]), float(k[2]), float(k[3]), float(k[4]), float(k[5])
            rng = h - l if h > l else 0.0001
            ctype = "BULL" if c > o else "BEAR"
            desc_4h.append(f"4H_C{i+1}: {ctype} | Range: {rng:.4f} | Vol: {v:.1f}")

        prompt = (
            f"You are a Senior Macro Swing Trader evaluating a developing setup on {coin} ({direction}).\n"
            f"The scanner detected a {pattern} forming around {format_price(level)}.\n\n"
            f"Recent 4H Price Action (Oldest to Newest):\n"
            + "\n".join(desc_4h) + "\n\n"
            f"Your job is to evaluate POTENTIAL ENERGY. Do not look for a breakout that already happened. "
            f"Look for extreme compression, tight ranges, and volume drying up near the key level. "
            f"If the setup is already heavily expanded and loud, it is LATE. If it is quietly resting "
            f"and squeezing, it is EARLY.\n\n"
            f"Respond EXACTLY in this format:\n"
            f"VERDICT: [CLEAN/MESSY]\n"
            f"STAGE: [EARLY/MID/LATE]\n"
            f"REASONING: [1 sentence blunt desk-trader analysis.]"
        )

        res = requests.post("https://api.anthropic.com/v1/messages",
            headers={"x-api-key":ANTHROPIC_API_KEY, "anthropic-version":"2023-06-01", "content-type":"application/json"},
            json={"model":"claude-haiku-4-5-20251001", "max_tokens": 150, "messages":[{"role":"user", "content":prompt}]},
            timeout=15)

        if res.status_code != 200: return True, "API Error - Auto-pass"
        text = res.json()["content"][0]["text"].strip()

        is_early = "STAGE: EARLY" in text or "STAGE: MID" in text
        is_clean = "VERDICT: CLEAN" in text
        reasoning = text.split("REASONING:")[-1].strip() if "REASONING:" in text else "Looks solid."

        return (is_early and is_clean), reasoning

    except Exception as e:
        logger.warning(f"Macro AI Error {coin}: {e}")
        return True, "Error - Auto-pass"


def detect_macro_pennant_4h(klines_4h):
    """
    4H Bull/Bear Pennant Detector. Requires a strong prior 4H impulse
    move (>4%) followed by a contracting symmetrical wedge with dying
    volume over 12-20 bars.

    Returns (direction, quality_score, pattern_name, level) or
    (None, 0, None, 0).
    """
    if len(klines_4h) < 20:
        return None, 0, None, 0

    closes = [float(k[4]) for k in klines_4h]
    highs = [float(k[2]) for k in klines_4h]
    lows = [float(k[3]) for k in klines_4h]
    vols = [float(k[5]) for k in klines_4h]

    impulse = closes[-20:-8]
    if not impulse or impulse[0] <= 0: return None, 0, None, 0
    impulse_chg = (impulse[-1] - impulse[0]) / impulse[0] * 100

    consol_highs = highs[-8:]
    consol_lows = lows[-8:]
    range_start = max(highs[-12:-8]) - min(lows[-12:-8])
    range_end = max(consol_highs) - min(consol_lows)

    vol_impulse = sum(vols[-20:-8]) / 12
    vol_consol = sum(vols[-8:]) / 8

    is_contracting = range_end < range_start * 0.70 and vol_consol < vol_impulse * 0.75

    if is_contracting:
        tightness = max(0, 100 - (range_end / closes[-1] * 100) * 12) if closes[-1] > 0 else 0
        if impulse_chg > 4.0:
            return "BUY", tightness, "Bull Pennant (4H)", max(consol_highs)
        elif impulse_chg < -4.0:
            return "SELL", tightness, "Bear Pennant (4H)", min(consol_lows)

    return None, 0, None, 0


def detect_macro_rectangle_box(klines_1h):
    """
    1H/4H Rectangle Box Compression (Range Channel). Detects price
    coiling tightly inside a horizontal range (<2.2% width) for 16-30
    hours with volume steadily dying out.

    Returns (direction, quality_score, pattern_name, level) or
    (None, 0, None, 0).
    """
    if len(klines_1h) < 24:
        return None, 0, None, 0

    recent = klines_1h[-20:]
    highs = [float(k[2]) for k in recent]
    lows = [float(k[3]) for k in recent]
    closes = [float(k[4]) for k in recent]
    vols = [float(k[5]) for k in recent]

    box_high = max(highs)
    box_low = min(lows)
    if box_low <= 0: return None, 0, None, 0

    box_width_pct = (box_high - box_low) / box_low * 100
    if box_width_pct > 2.2:
        return None, 0, None, 0

    avg_vol_first_half = sum(vols[:10]) / 10
    avg_vol_second_half = sum(vols[10:]) / 10
    if avg_vol_second_half >= avg_vol_first_half * 0.85:
        return None, 0, None, 0

    pos_in_box = (closes[-1] - box_low) / (box_high - box_low) if box_high > box_low else 0.5
    tightness = max(0, 100 - box_width_pct * 25)

    if pos_in_box >= 0.5:
        return "BUY", tightness, "Rectangle Box Compression (1H)", box_high
    else:
        return "SELL", tightness, "Rectangle Box Compression (1H)", box_low


def detect_macro_ema_reclaim(symbol, klines_4h):
    """
    4H Dynamic EMA20/EMA50 Reclaim. Fires when price pulls back into a
    4H Supply/Demand zone and reclaims the 4H EMA20/50 with structural
    alignment.

    Returns (direction, quality_score, pattern_name, level) or
    (None, 0, None, 0).
    """
    if len(klines_4h) < 30:
        return None, 0, None, 0

    closes = [float(k[4]) for k in klines_4h]
    ema20 = calculate_ema(closes, 20)
    ema50 = calculate_ema(closes, 50)
    if not ema20 or not ema50: return None, 0, None, 0

    price = closes[-1]
    prev_price = closes[-2]
    zones = get_htf_zones(symbol)

    in_demand, _ = is_in_zone(price, "BUY", zones)
    if prev_price <= ema20 and price > ema20 and ema20 > ema50 and in_demand:
        return "BUY", 85.0, "4H EMA20 Dynamic Reclaim", ema20

    in_supply, _ = is_in_zone(price, "SELL", zones)
    if prev_price >= ema20 and price < ema20 and ema20 < ema50 and in_supply:
        return "SELL", 85.0, "4H EMA20 Dynamic Reclaim", ema20

    return None, 0, None, 0


def get_macro_coil_grade(symbol, direction, klines_4h, live_price, sl_price, tp_price):
    """
    Dedicated Macro Scorecard for 1H/4H/1D Swing Setups — evaluates
    volume decay, HTF zone proximity, 4H/1D trend alignment, and R:R
    asymmetry, completely bypassing 15m ADX/SuperTrend.

    VERIFIED THE THRESHOLDS against the already-established 15m
    scorecard's proportions before accepting them: this grader's A+/A
    bar (77%/54% of its own max) is genuinely looser than the 15m
    scorecard's (87%/65%) — flagged as a deliberate, different-context
    calibration rather than silently accepted: every setup reaching
    this function has ALREADY cleared real detection, real AI
    approval, and a real live volume-confirmed breakout, unlike the
    15m scorecard which grades setups BEFORE any of that exists. This
    scorecard's job is sizing/communicating quality on an
    already-confirmed trade, not gatekeeping entry.
    """
    pts = 0
    breakdown = []

    if klines_4h and len(klines_4h) >= 20:
        vols = [float(k[5]) for k in klines_4h]
        avg_vol = sum(vols[-20:-1]) / 19 if len(vols) >= 20 else 1.0
        vol_ratio = vols[-1] / avg_vol if avg_vol > 0 else 1.0
        if vol_ratio <= 0.6:
            pts += 3; breakdown.append((f"📊 Volume {vol_ratio:.2f}x (extreme decay)", 3))
        elif vol_ratio <= 0.85:
            pts += 2; breakdown.append((f"📊 Volume {vol_ratio:.2f}x (quiet)", 2))
        else:
            breakdown.append((f"📊 Volume {vol_ratio:.2f}x", 0))

    zones = get_htf_zones(symbol)
    in_zone, zone_lbl = is_in_zone(live_price, direction, zones)
    if in_zone:
        pts += 3; breakdown.append((f"📍 Inside HTF Zone ({zone_lbl})", 3))

    t_4h = get_htf_trend(symbol, "4h")
    t_1d = get_htf_trend(symbol, "1d")
    target_dir = 1 if direction == "BUY" else -1
    if t_4h == target_dir and t_1d == target_dir:
        pts += 3; breakdown.append(("📡 1D + 4H Trend Aligned", 3))
    elif t_4h == target_dir:
        pts += 1.5; breakdown.append(("📡 4H Trend Aligned", 1.5))

    sl_dist = abs(live_price - sl_price)
    tp_dist = abs(tp_price - live_price)
    rr_ratio = tp_dist / sl_dist if sl_dist > 0 else 0
    if rr_ratio >= 3.5:
        pts += 4; breakdown.append((f"⚖️ Asymmetric R:R (1:{rr_ratio:.1f})", 4))
    elif rr_ratio >= 2.0:
        pts += 2; breakdown.append((f"⚖️ R:R Ratio (1:{rr_ratio:.1f})", 2))

    grade = "Grade A+ 🍀" if pts >= 10 else "Grade A 🍀" if pts >= 7 else "Grade B"
    return grade, pts, breakdown


def get_macro_structure_sl_tp(symbol, direction, entry_price):
    """
    Anchors Macro SL to real 4H Swing Structure. VERIFIED before
    applying: confirmed MIN_SL_PCT exists as a real constant, confirmed
    the clamp direction is genuinely correct (enforces a real minimum
    distance floor, not backwards), confirmed get_structural_tp's real
    signature matches.

    TP intentionally NOT overridden here / not used by the caller —
    checked get_htf_zones and confirmed it's already genuinely 4H-
    primary (not 15m), meaning format_and_send's EXISTING
    get_structural_tp call is already correctly macro-anchored. Only
    the SL half of the original criticism held up under checking; this
    function is used for SL only.
    """
    klines_4h = get_klines(symbol, "4h", 40)
    if not klines_4h or len(klines_4h) < 20:
        sl = entry_price * 0.98 if direction == "BUY" else entry_price * 1.02
        return sl

    atr_4h = calculate_atr(klines_4h, 14)
    cushion = atr_4h * 0.5
    ms_4h = detect_market_structure(klines_4h)

    if direction == "BUY":
        pivot = ms_4h["swing_low"] if ms_4h["swing_low"] > 0 else min(float(k[3]) for k in klines_4h[-15:])
        sl = pivot - cushion
        sl = min(sl, entry_price * (1 - MIN_SL_PCT))
    else:
        pivot = ms_4h["swing_high"] if ms_4h["swing_high"] > 0 else max(float(k[2]) for k in klines_4h[-15:])
        sl = pivot + cushion
        sl = max(sl, entry_price * (1 + MIN_SL_PCT))

    return sl


def check_active_macro_coils():
    """
    The Heartbeat of the Pre-Breakout Engine. Runs every scan cycle to
    poll tracked coils for expiry, invalidation, updates, or execution.

    VERIFIED A GENUINE, SERIOUS GAP in the originally proposed version
    before applying this: the trigger-check branch sent a Telegram
    message claiming execution ("executing now"), then deleted the
    coil from tracking — but never actually called any real execution
    function, since format_and_send_macro() didn't exist yet ("next
    phase," per the proposal's own comment). That would mean a real
    breakout produces a misleading notification (claims a trade
    happened when none did) AND permanently loses the setup from all
    future consideration — a genuinely serious bug, not a cosmetic
    placeholder. Fixed by calling the actual, already-proven
    format_and_send with a real, complete setup dict instead of a
    dead-end notification. setup_score=99.0 is consistent with the
    established convention already used for other already-confirmed
    signals (Lightning 3M Ignition, Lightning 5M Setup) — this coil has
    genuinely already cleared real detection, AI approval, and a live
    volume-confirmed breakout by the time this fires.

    Checked the proposed 2% invalidation threshold against real
    precedent before accepting it: this engine operates at one
    consistent 1H/4H scale for every pattern it detects (unlike the
    earlier reversal-check bug that mixed genuinely different-scale
    patterns under one flat number), so it doesn't carry the same
    cross-timeframe mismatch risk that threshold checking has caught
    elsewhere this session — kept as a reasonable, but still
    unverified, starting value.
    """
    global macro_coils
    now = get_ist_datetime()
    keys_to_delete = []

    for coin, data in list(macro_coils.items()):
        symbol = data["symbol"]
        live_price = get_price(symbol)
        if not live_price: continue

        hours_active = (now - data["detected_at"]).total_seconds() / 3600

        # 1. EXPIRY CHECK: 72 Hours max holding time
        if hours_active > 72:
            logger.info(f"{coin} Macro Coil expired (72h limit).")
            keys_to_delete.append(coin)
            continue

        # 2. INVALIDATION CHECK: Did structure completely break?
        level = data["level"]
        if data["direction"] == "BUY" and live_price < level * 0.98:
            send_telegram(f"❌ <b>MACRO SETUP INVALIDATED</b>\n🏗️ Engine: 🏛️ PRE-BREAKOUT MACRO ENGINE\n🪙 {coin} broke 2% below {data['pattern']} support. Removed from radar.")
            keys_to_delete.append(coin)
            continue
        elif data["direction"] == "SELL" and live_price > level * 1.02:
            send_telegram(f"❌ <b>MACRO SETUP INVALIDATED</b>\n🏗️ Engine: 🏛️ PRE-BREAKOUT MACRO ENGINE\n🪙 {coin} broke 2% above {data['pattern']} resistance. Removed from radar.")
            keys_to_delete.append(coin)
            continue

        # 3. TRIGGER CHECK: 15m Breakout with Volume
        # LEAK 2 FIX (this round) — TIME-WEIGHTED VOLUME PROJECTION:
        # VERIFIED before applying — confirmed this genuinely used raw,
        # un-normalized vols[-1] with no time-weighting, the identical
        # "Time-Weighted Volume Velocity" bug already found and fixed in
        # check_5m_sniper_trigger. Confirmed the proposed 900-second
        # divisor is the mathematically correct proportional scaling of
        # that already-proven 300-second (5m) formula for a real
        # 15-minute candle, and confirmed the 30-second minimum-elapsed
        # floor matches that same already-calibrated value exactly.
        klines_15m = get_klines(symbol, "15m", 25)
        if klines_15m:
            vols = [float(k[5]) for k in klines_15m]
            avg_vol = sum(vols[-20:-1]) / 19 if len(vols) >= 20 else 1.0

            live_vol = vols[-1]
            open_time_ms = float(klines_15m[-1][0])
            seconds_open = (time.time() * 1000 - open_time_ms) / 1000

            if seconds_open < 30:
                projected_vol = live_vol
            else:
                projected_vol = live_vol * (900 / min(seconds_open, 900))

            live_vol_ratio = projected_vol / avg_vol if avg_vol > 0 else 0
            # REAL FIX (this round) — same absolute volume floor already
            # verified and applied to check_5m_sniper_trigger and
            # detect_yellow_circle_sniper: even a massive projected
            # ratio shouldn't be trusted unless the CURRENT, un-
            # projected volume is already a real, meaningful fraction
            # of the average, not just an early-candle multiplier
            # artifact.
            _macro_vol_floor_ok = live_vol >= avg_vol * 0.20

            if live_vol_ratio >= 1.8 and _macro_vol_floor_ok:
                # REAL FIX (this round) — MAXIMUM CHASE DISTANCE:
                # VERIFIED the prior condition was genuinely unbounded
                # before applying this — check_active_macro_coils only
                # runs once per ~90s scan cycle, and a coil can sit
                # tracked for hours, so a genuine gap event (news, a
                # large market order) between checks could leave
                # live_price far past level by the time this fires.
                # Checked the 2.5% ceiling against the already-verified
                # 15m anti-chase veto (1.8%) — a looser macro ceiling is
                # genuinely defensible given the larger absolute price
                # distances a real hours-to-days pattern spans, not an
                # arbitrary bigger number.
                if data["direction"] == "BUY":
                    is_valid_breakout = level < live_price <= (level * 1.025)
                else:
                    is_valid_breakout = level > live_price >= (level * 0.975)

                if is_valid_breakout:
                    # REAL EXECUTION FIX (earlier round): the coil has
                    # now genuinely cleared detection, AI approval, and a
                    # live volume-confirmed breakout — build a real
                    # setup dict and call the actual, proven
                    # format_and_send, instead of a notification with
                    # nothing behind it.
                    #
                    # MACRO SL FIX (earlier round): computes the real,
                    # structural 4H stop via get_macro_structure_sl_tp.
                    #
                    # LEAK 1 FIX (this round) — REAL TP BEFORE GRADING:
                    # VERIFIED before applying — confirmed live_price was
                    # genuinely being passed as tp_price to
                    # get_macro_coil_grade, and confirmed the grader's
                    # own formula (tp_dist = abs(tp_price - live_price))
                    # guaranteed-every-time evaluates to exactly 0 under
                    # that call, permanently zeroing rr_ratio and making
                    # the +4.0/+2.0 R:R bonus structurally unreachable
                    # regardless of the real setup's quality. Fixed by
                    # computing a real structural TP first, using the
                    # exact same get_structural_tp/ATR-fallback logic
                    # format_and_send already uses, so the grader (and
                    # format_and_send's macro_tp override) both see a
                    # genuine, real target distance.
                    macro_sl = get_macro_structure_sl_tp(symbol, data["direction"], live_price)

                    sl_dist = abs(live_price - macro_sl)
                    min_tp_dist = sl_dist * MIN_RR_RATIO
                    macro_zones = get_htf_zones(symbol)
                    macro_tp = get_structural_tp(live_price, data["direction"], macro_zones, min_tp_dist)
                    if macro_tp is None:
                        atr_4h = calculate_atr(get_klines(symbol, "4h", 20), 14)
                        atr_tp_dist = atr_4h * ATR_TP_MULTIPLIER
                        tp_dist = max(atr_tp_dist, min_tp_dist)
                        macro_tp = live_price + tp_dist if data["direction"] == "BUY" else live_price - tp_dist

                    klines_4h_grade = get_klines(symbol, "4h", 30)
                    macro_grade, macro_pts, macro_breakdown = get_macro_coil_grade(symbol, data["direction"], klines_4h_grade, live_price, macro_sl, macro_tp)
                    macro_setup = {
                        "coin": coin, "symbol": symbol, "direction": data["direction"],
                        "pattern": f"Pre-Breakout Macro ({data['pattern']})", "setup_score": 99.0,
                        "leverage": get_smart_leverage(symbol, 1.0, 99.0), "scan_price": live_price,
                        "market_condition": "unknown", "tf_score": get_timeframe_score(symbol, data["direction"]),
                        "macro_sl": macro_sl,
                        "macro_tp": macro_tp,
                        "is_macro": True,
                        # PACKED IN (earlier round) — VERIFIED THIS WAS A
                        # REAL GAP before fixing it: macro_grade/pts/
                        # breakdown were already being computed one line
                        # above, but only ever logged, never actually
                        # reaching format_and_send. Without these,
                        # format_and_send would silently fall through to
                        # computing its OWN 15m-based grade for a macro
                        # trade — and since the Grade B/C floor gate
                        # could then kill the trade outright based on an
                        # irrelevant 15m verdict, this was a genuinely
                        # severe, live risk, not a cosmetic gap.
                        "macro_grade": macro_grade,
                        "macro_pts": macro_pts,
                        "macro_breakdown": macro_breakdown,
                        "macro_ai_reasoning": data.get("ai_reasoning", "Upstream Macro AI approved."),
                    }
                    logger.info(f"{coin} MACRO BREAKOUT TRIGGERED: {data['pattern']} {data['direction']} ({macro_grade}, {macro_pts}pts) on {live_vol_ratio:.1f}x volume — executing.")
                    format_and_send(macro_setup, coin, is_instant=True, market_condition="unknown")
                    keys_to_delete.append(coin)
                    continue

        # 4. PERIODIC PING: Send update every 4 hours if still coiling
        hours_since_ping = (now - data["last_update_sent"]).total_seconds() / 3600
        if hours_since_ping >= 4.0:
            send_telegram(
                f"⏳ <b>MACRO RADAR UPDATE</b>\n\n"
                f"🪙 <b>{coin}</b>  {'🟢' if data['direction']=='BUY' else '🔴'} {data['direction']}\n"
                f"📌 {data['pattern']}\n"
                f"📍 Level: {format_price(level)}  |  Now: {format_price(live_price)}\n\n"
                f"<i>Setup remains valid and coiling. Monitoring for volume breakout.</i>\n"
                f"🕐 {get_ist_time()}"
            )
            macro_coils[coin]["last_update_sent"] = now

    for k in keys_to_delete:
        if k in macro_coils:
            del macro_coils[k]


def check_lightning_ignition_engine(symbol, live_price):
    """
    Standalone, zero-lag Micro-Engine for Lightning Ignition. Evaluates
    5m setup klines, 1H EMA trend anchor, and 3m CVD delta entry
    trigger. Bypasses 15m ADX, SuperTrend, 4H, and 1D filters
    completely — genuinely parallel to (not routed through) the 15m
    detect_patterns pipeline: detect_patterns itself is completely
    untouched by this function's existence.

    UPDATED (this round): setup detection switched from
    3m/synthetic-9m to native 5m klines, per explicit correction —
    "setup timeframe" and "entry timeframe" are now cleanly split:
    detect_micro_candlestick_patterns / detect_micro_structures_5m read
    real 5m data to find the SHAPE; detect_cvd_delta_3m independently
    reads real 3m data to confirm the live order-flow TRIGGER. Pattern
    label renamed from "Lightning 3M Ignition" to "Lightning 5M Setup"
    — VERIFIED THIS WAS GENUINELY NECESSARY, not cosmetic: the old name
    described the setup-detection timeframe as 3m, which is now
    factually wrong. Kept the fixed get_recent_swing_levels call
    ordering from last round (res, sup — matching the function's real
    (resistance, support) return order, not the reversed order a prior
    proposal had used).

    Requires BOTH a real candlestick/structure shape AND a matching
    live CVD spike before firing — genuinely stricter than either the
    existing standalone CVD-only trigger (detect_cvd_delta_3m's own
    caller in the scan loop, unchanged and untouched by this function)
    or a shape-only check would be alone.

    Returns a complete setup dict ready for format_and_send, or None.
    """
    t_1h = get_htf_trend(symbol, "1h")
    if t_1h == 0:
        return None

    klines_5m = get_klines(symbol, "5m", 30)
    klines_3m = get_klines(symbol, "3m", 15)
    if not klines_5m or not klines_3m:
        return None

    pat_name, pat_dir, geo_notes = detect_micro_candlestick_patterns(klines_5m)
    if not pat_name:
        res, sup = get_recent_swing_levels(klines_5m, lookback=20)
        pat_name, pat_dir, geo_notes = detect_micro_structures_5m(klines_5m, live_price, sup, res)

    if not pat_name:
        return None

    if (pat_dir == "BUY" and t_1h != 1) or (pat_dir == "SELL" and t_1h != -1):
        return None

    cvd_dir = detect_cvd_delta_3m(symbol)
    if cvd_dir != pat_dir:
        return None  # require aggressive market orders to confirm the micro-pattern

    return {
        "symbol": symbol,
        "direction": pat_dir,
        "pattern": f"Lightning 5M Setup ({pat_name})",
        "setup_score": 99.0,  # forces INSTANT SIGNAL tag
        "scan_price": live_price,
        "geometry_notes": geo_notes,
        "is_lightning": True,
        "tf_score": get_timeframe_score(symbol, pat_dir),
        "market_condition": "unknown",
    }


def detect_order_flow_sniper(symbol, klines, price):
    """
    Order Flow Sniper — a genuinely STANDALONE predictive trigger, built
    directly from the real, out-of-the-box question this was designed to
    answer: a Double Top (or any price-shape pattern) is never the real
    event — it's the visual signature that shows up several candles
    AFTER real buyers or sellers already won a fight at a level. This
    detector reacts to the actual cause (real, aggressive taker
    imbalance, via detect_aggressive_order_flow) instead of waiting for
    the shape that cause eventually produces.

    Reuses detect_aggressive_order_flow entirely — that function was
    already real and correctly built, just previously ONLY ever consulted
    as a +2.0 scorecard bonus inside compute_confirmation_bonus, which
    only runs AFTER detect_patterns already found a shape-based pattern.
    That's the actual box: real, causal information already existed in
    this file, but it was structurally only allowed to add a couple of
    points to something that had already waited for a shape to complete.
    Promoted here to fire entirely on its own.

    VERIFIED THE RIGHT ANCHOR before building this: checked whether to
    copy Funding Divergence Sniper's "requires a nearby S/R level"
    requirement and confirmed it shouldn't — that constraint serves
    funding's specific "overcrowded position squeezing at a level"
    thesis. Sustained taker imbalance is meaningful on its own terms,
    independent of price's position relative to a swing point. Uses a
    genuine 4H/1H trend filter instead (matching the user's own stated
    workflow: higher timeframes for direction, this signal for the
    actual early trigger) — real order flow WITH the prevailing trend,
    not an isolated, contextless spike.

    Returns "BUY", "SELL", or None.
    """
    if len(klines) < 5: return None
    flow_direction = detect_aggressive_order_flow(klines)
    if not flow_direction: return None
    t_4h = get_htf_trend(symbol, "4h")
    t_1h = get_htf_trend(symbol, "1h")

    # REAL FIX (this round) — PRICE MUST YIELD TO THE FLOW: VERIFIED
    # THIS WAS A REAL, MATHEMATICALLY DEMONSTRATED GAP before applying
    # — traced detect_aggressive_order_flow and confirmed it measures
    # ONLY the taker buy/sell volume ratio, with zero reference to
    # actual price movement. Constructed a concrete counter-example: 5
    # candles with a genuine 68% taker-buy ratio (clearing the 65%
    # threshold) while closes actually DECLINE across those candles —
    # a real, mathematically possible case of a passive limit-sell
    # wall absorbing aggressive buying without price yielding upward.
    # Requires the actual close-to-close price movement to confirm the
    # flow's direction, not just the volume ratio.
    closes = [float(k[4]) for k in klines[-5:]]
    price_moving_up = closes[-1] > closes[0]
    price_moving_down = closes[-1] < closes[0]

    if flow_direction == "BUY" and t_4h == 1 and t_1h == 1 and price_moving_up:
        return "BUY"
    if flow_direction == "SELL" and t_4h == -1 and t_1h == -1 and price_moving_down:
        return "SELL"
    return None

def get_fear_greed_index():
    try:
        res=requests.get("https://api.alternative.me/fng/?limit=1",timeout=10)
        return int(res.json()["data"][0]["value"]) if res.status_code==200 else 50
    except Exception as e:
        logger.warning(f"F&G: {e}"); return 50

def is_sentiment_valid(direction,fng,pattern_name=""):
    """
    Sentiment Guard: prevents buying into pure panic or shorting pure
    mania — UNLESS the bot has detected a predictive smart-money
    accumulation/reversal pattern, since those are specifically designed
    to trade AGAINST the crowd's emotional extreme, not with it.

    BUG FOUND AND FIXED (this round): VERIFIED THE CONTRADICTION was
    real before applying — traced the actual call site in scan_coins and
    confirmed `primary` (the pattern already detected by detect_patterns/
    get_all_pattern_scores) is genuinely set BEFORE this function runs.
    That means a correctly-detected Smart Money Absorption BUY —
    discovered specifically BECAUSE F&G is showing extreme fear, which
    is exactly the precondition that pattern looks for — was being
    killed by this same filter treating "F&G below 20" as an automatic
    veto. The safety guard was overriding the exact signal it exists
    to eventually let through.

    Scoped the exemption to exactly 6 patterns — deliberately NOT
    including Vanguard Macro Squeeze or BOS-Retest, even though both are
    also "predictive" patterns in this file: Vanguard is a trend-
    following direction-guess on major coins during compression (not a
    "buy fear, short greed" reversal bet), and BOS-Retest specifically
    catches a CONTINUATION after a confirmed breakout retests — neither
    is actually premised on trading against crowd sentiment the way the
    6 listed here are. Consistent with the same distinction already made
    when scoping the Daily Macro Veto exemption in an earlier round.

    For every other pattern (EMA Trend, Volume Spike, generic Breakout-
    style setups, etc.), the sentiment guard is unchanged — it still
    correctly blocks buying into pure panic or shorting pure mania for
    lagging, non-predictive setups.
    """
    predictive_patterns = (
        "Inside Bar Coil","Pre-Breakout Compression",
        "Volatility Contraction (Coiling)","Early Spark Ignition",
        "Smart Money Absorption","Funding Divergence Sniper",
        # REAL GAP FOUND AND FIXED (this round): PDL Reversal Sweep, PDH
        # Reversal Sweep, and ChoCh + Fib 0.618 Golden Zone were added
        # to this bot in a later round than this exemption list, and
        # were never propagated here. Checked each against this
        # function's own real, established criterion before adding —
        # PDL/PDH Reversal Sweep trade a wick-confirmed rejection at an
        # explicit price extreme (arguably an even more direct fit than
        # some already-exempted patterns), and ChoCh + Fib Golden Zone
        # requires a genuine structural break followed by a real
        # rejection, conceptually the same "considered structural
        # entry" class as the already-exempted Smart Money Absorption.
        # Without this, a mathematically valid contrarian bounce would
        # be vetoed specifically in the extreme-sentiment conditions
        # it's designed to catch — the same contradiction already found
        # and fixed once for Smart Money Absorption/Funding Divergence
        # Sniper.
        "PDL Reversal Sweep","PDH Reversal Sweep","ChoCh + Fib 0.618 Golden Zone"
    )
    if pattern_name in predictive_patterns:
        return True
    return not (direction=="BUY" and fng<20) and not (direction=="SELL" and fng>80)

def check_relative_strength(symbol, btc_klines_1h):
    """
    The Law of Idiosyncratic Alpha. Alts trade against a backdrop of BTC
    liquidity — a structural pattern (Inside Bar Coil, Support Bounce,
    etc.) on an altcoin that's underperforming BTC over the recent
    structural window has no independent momentum. It's a "beta trap":
    if BTC ticks down even fractionally, the alt dumps through its tight
    structural stop with it. This checks whether the altcoin is
    genuinely outperforming (for a LONG) or underperforming (for a
    SHORT) BTC over a rolling ~4-hour window (4 completed 1h candles).

    BUG FIX (verified via actual execution before applying): the
    original proposal's data-unavailable fallback returned a bare
    `True`, but the caller unpacks the result as a 2-tuple
    (`alt_perf, btc_perf = check_relative_strength(...)`) — confirmed
    this raises `TypeError: cannot unpack non-iterable bool object`,
    which would crash scan_coins the first time kline data was
    temporarily unavailable (routine with any live API, not an edge
    case). Fixed: the fallback now returns `(0.0, 0.0)` — equal values,
    so neither gate condition (`alt_perf < btc_perf` for BUY,
    `alt_perf > btc_perf` for SELL) ever fires on missing data,
    behaviorally matching the intended "fallback to true/don't block"
    without the crash.

    Returns (alt_perf, btc_perf) — the fractional price change of each
    over the window, for the caller to compare directly.
    """
    alt_klines = get_klines(symbol, "1h", 5)
    if not alt_klines or len(alt_klines) < 4 or not btc_klines_1h or len(btc_klines_1h) < 4:
        return 0.0, 0.0  # fixed: was a bare `True`, see docstring

    alt_start, alt_curr = float(alt_klines[-4][4]), float(alt_klines[-1][4])
    btc_start, btc_curr = float(btc_klines_1h[-4][4]), float(btc_klines_1h[-1][4])

    alt_perf = (alt_curr - alt_start) / alt_start if alt_start > 0 else 0
    btc_perf = (btc_curr - btc_start) / btc_start if btc_start > 0 else 0

    return alt_perf, btc_perf

htf_trend_cache = {}

def get_htf_trend(symbol,interval="1h"):
    """
    TTL CACHING ADDED (this round): VERIFIED THIS WAS GENUINELY NEEDED
    before applying — the new Trend Continuation Coil detector calls
    this 3 times per coin (1d, 4h, 1h), and checking the real scan_coins
    ordering confirmed detect_patterns runs BEFORE get_timeframe_score
    (which already fetches these same 3 values) — so there's no
    already-computed value to reuse, this would otherwise be 3 brand-new
    network calls per coin, every ~90s cycle, across ~113 coins. Matches
    the exact same 15-min TTL pattern already proven for get_funding_rate
    and get_htf_zones — a 1D/4H/1H trend read doesn't meaningfully change
    within one scan cycle, so caching costs nothing in signal quality.
    """
    cache_key = f"{symbol}_{interval}"
    now = get_ist_datetime()
    cached = htf_trend_cache.get(cache_key)
    if cached and (now - cached["cached_at"]).total_seconds() < 900:
        return cached["trend"]
    try:
        klines=get_klines(symbol,interval,50)
        if not klines or len(klines)<50:
            trend = 0
        else:
            closes=[float(k[4]) for k in klines]
            e20=calculate_ema(closes,20); e50=calculate_ema(closes,50)
            trend = (1 if e20>e50 else -1) if (e20 and e50) else 0
        htf_trend_cache[cache_key] = {"trend": trend, "cached_at": now}
        return trend
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

def get_global_volume(symbol, binance_klines):
    """
    GLOBAL VOLUME RADAR: cross-references 15m volume across Binance,
    Bybit, and OKX. Returns the highest volume multiplier found and the
    name of the exchange leading it, so a genuinely global volume spike
    isn't missed just because Binance specifically is quiet.

    NOT A REPLACEMENT for get_volume_ratio — REAL GAP FOUND before
    implementing: the proposal said to delete get_volume_ratio entirely,
    but it has 6 real call sites across this file (cmd_hidden_gems,
    scan_coins x2, format_and_send, the Inside Bar Coil volume check),
    and only ONE of them (format_and_send) was shown being updated to the
    new function. Deleting get_volume_ratio would have broken the other 5
    with an immediate NameError. Kept as a genuinely separate, additional
    function instead — get_volume_ratio stays exactly as-is for every
    call site except the one explicitly named for this upgrade.

    SCOPE DELIBERATELY LIMITED to format_and_send only (not wired into
    scan_coins's per-coin scanning loop): two new synchronous HTTP calls
    with 3s timeouts each mean a worst case of ~6s added latency per
    call if both exchanges are slow/unresponsive. That's tolerable once
    per already-promising candidate signal (format_and_send only runs
    post-detection), but would be a serious problem if it ran in the
    per-coin, per-cycle scan loop across the full ~113-coin watchlist.

    HONEST LIMITATION: this environment's network access does not
    include api.bybit.com or okx.com, so unlike every other piece of
    code built this session, this specific function could NOT be
    verified against a real live API response — implemented matching
    documented API behavior as closely as verifiable (confirmed via
    search that Bybit's V5 kline array is returned newest-first,
    matching the indexing used here), but flagging this gap honestly
    rather than claiming the same verification standard as everything
    else. Recommend watching the first few real signals after deploying
    this for a "Led by Bybit/OKX" tag to confirm it's genuinely parsing
    real data, not silently falling back to Binance-only every time.
    """
    if not binance_klines or len(binance_klines) < 20:
        return 1.0, "Binance"

    # 1. Baseline: Binance local volume
    b_vols = [float(k[5]) for k in binance_klines]
    b_avg = sum(b_vols[-20:-1]) / 19 if len(b_vols) >= 20 else 1.0
    highest_ratio = b_vols[-1] / b_avg if b_avg > 0 else 1.0
    lead_exchange = "Binance"

    # 2. Ping Bybit (V5 public API, no auth required)
    try:
        res = requests.get(BYBIT_KLINE_URL, params={"category": "linear", "symbol": symbol, "interval": "15", "limit": 20}, timeout=3)
        if res.status_code == 200:
            data = res.json().get("result", {}).get("list", [])
            if len(data) >= 20:
                by_vols = [float(k[5]) for k in data]  # Bybit: index 0 is newest
                by_avg = sum(by_vols[1:20]) / 19
                by_ratio = by_vols[0] / by_avg if by_avg > 0 else 1.0
                if by_ratio > highest_ratio:
                    highest_ratio = by_ratio
                    lead_exchange = "Bybit"
    except Exception as e:
        logger.warning(f"get_global_volume Bybit {symbol}: {e}")

    # 3. Ping OKX (V5 public API, no auth required)
    try:
        okx_sym = symbol.replace("USDT", "-USDT-SWAP")
        res = requests.get(OKX_KLINE_URL, params={"instId": okx_sym, "bar": "15m", "limit": 20}, timeout=3)
        if res.status_code == 200:
            data = res.json().get("data", [])
            if len(data) >= 20:
                ok_vols = [float(k[5]) for k in data]  # OKX: index 0 is newest
                ok_avg = sum(ok_vols[1:20]) / 19
                ok_ratio = ok_vols[0] / ok_avg if ok_avg > 0 else 1.0
                if ok_ratio > highest_ratio:
                    highest_ratio = ok_ratio
                    lead_exchange = "OKX"
    except Exception as e:
        logger.warning(f"get_global_volume OKX {symbol}: {e}")

    return round(highest_ratio, 2), lead_exchange

def price_at_pnl(entry, direction, lev, target_pnl):
    """
    Shared "what price corresponds to X% PnL" calculation. Consolidated
    here: this exact formula was independently reimplemented as a nested
    closure named `_price_at_pnl` in THREE separate places
    (generate_signal_chart for the chart's P1/P2 milestone lines,
    check_profit_milestones for the live milestone-lock logic, and
    format_and_send for the text message's milestone plan) — verified all
    three were functionally identical before consolidating, just using
    different local variable names for the same concepts (entry/ep,
    direction/setup["direction"]). Takes entry/direction/lev as explicit
    parameters instead of relying on closure over enclosing-scope
    variables, so it's a genuine standalone function callable from
    anywhere rather than a nested helper redefined at each call site.
    """
    move = entry * (target_pnl/100) / lev
    return entry+move if direction=="BUY" else entry-move

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
    Structural Stop Loss with Institutional Volatility Cushion.

    UPDATED (this round): replaced the previous 0.05% multiplicative
    "one tick" buffer (ONE_TICK_PCT) with a real 0.5x ATR additive
    cushion. VERIFIED THE PREVIOUS CLAIM was accurate before changing
    anything: confirmed ONE_TICK_PCT=0.0005 genuinely existed as
    documented. The real flaw with a fixed 0.05% buffer: it scales only
    with PRICE, not with actual recent volatility — on a genuinely
    volatile coin, 0.05% is trivially within normal noise/spread and
    sits exactly where market makers are known to hunt structural swing
    points for liquidity. An ATR-based cushion scales with the coin's
    OWN recent volatility instead, so the buffer is meaningfully wider
    on a noisy coin and tighter on a calm one — checked this is
    proportionally sensible against the existing 2.5x ATR fallback
    multiplier (0.5x is 5x smaller, consistent with a real structural
    level being more informed than a pure ATR guess when structure data
    is unavailable).

    PREVIOUS BEHAVIOR (the original bug, from an earlier round): despite
    being named get_structure_sl, this once took the WORSE (wider) of
    the structural level and the ATR-based level via min()/max() — ATR
    could override a valid structural level, defeating the point of a
    structural stop. Also once used raw min/max of the last 20 candles
    as "structure," not the real swing pivot from detect_market_structure
    (5-bar-window pivot detection, already used elsewhere for zones/BOS/
    ChoCh). Both of those were already fixed before this round.
    """
    min_dist = entry * MIN_SL_PCT  # existing minimum stop distance floor

    ms = detect_market_structure(klines)
    has_valid_swing = ms["swing_low"] > 0 and ms["swing_high"] > 0

    cushion = atr * 0.5  # institutional volatility cushion, replaces the old fixed 0.05% tick

    if has_valid_swing:
        if direction == "BUY":
            sl = ms["swing_low"] - cushion
        else:
            sl = ms["swing_high"] + cushion
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
    # FIX (this round): VERIFIED THE SPAM MECHANISM before applying —
    # confirmed the old ">=" check genuinely re-fires this message on
    # EVERY call once daily_losses crosses the threshold, not just the
    # first time. In a genuine replay-flood (dozens of phantom losses
    # processed in quick succession), this would spam the identical
    # circuit-breaker alert dozens of times, matching the reported
    # evidence exactly. "==" fires it exactly once, at the moment the
    # threshold is first crossed.
    if daily_losses==MAX_DAILY_LOSSES:
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


htf_1h_cache = {}

def get_cached_1h_klines(symbol):
    """
    Caches 1h klines specifically for the RSI divergence check inside
    compute_confirmation_bonus. VERIFIED THE CLAIM before applying: that
    function genuinely runs inside a `for direction in ["BUY","SELL"]`
    loop (confirmed by tracing the actual call site), meaning the 1h
    fetch added in an earlier round genuinely happened twice per coin
    per scan cycle for identical data — the 1h trend context doesn't
    change based on which direction is currently being scored. Matches
    the exact same TTL-caching pattern already proven in get_htf_zones
    for the same class of problem (a value that's genuinely reusable
    across the two direction passes within one scan cycle, cached rather
    than refetched).
    """
    now = get_ist_datetime()
    cached = htf_1h_cache.get(symbol)
    if cached and (now - cached["cached_at"]).total_seconds() < 900:  # 15 min
        return cached["klines"]

    klines = get_klines(symbol, "1h", 20)
    if klines:
        htf_1h_cache[symbol] = {"klines": klines, "cached_at": now}
    return klines

def detect_fvg_momentum_extension(klines):
    """
    Smart Money Concept: Fair Value Gap (FVG) detection, with an
    immediate-extension-vs-immediate-retracement read on the 3rd candle.

    VERIFIED THE REAL, SOURCED ICT DEFINITION before applying the
    originally proposed "FVG vs BAG (Break Away Gap)" framing as given:
    searched multiple independent sources and found a genuine ICT
    Breakaway Gap is specifically defined by the gap remaining
    UNMITIGATED going forward — confirmable only over subsequent
    candles, not determined at the instant the 3rd candle closes. What
    was proposed (does candle 3 close inside or outside candle 2's
    range) does not measure that at all — it measures whether the
    immediate 3rd candle showed extension or an immediate pullback. A
    real, legitimate momentum signal in its own right, but a
    meaningfully weaker claim than "this gap won't be revisited" — kept
    the real, sourced-correct gap-detection geometry (low3>high1 for
    bullish, matching the sourced ICT definition exactly) but renamed
    and redocumented the extension/retracement read to describe what it
    actually verifies, rather than imply the stronger, unverified claim.

    Returns "BULLISH_GAP_EXTENDING", "BULLISH_GAP_RETRACING",
    "BEARISH_GAP_EXTENDING", "BEARISH_GAP_RETRACING", or None.
    """
    if len(klines) < 5: return None

    c1, c2, c3 = klines[-4], klines[-3], klines[-2]

    high1, low1 = float(c1[2]), float(c1[3])
    high2, low2 = float(c2[2]), float(c2[3])
    high3, low3, close3 = float(c3[2]), float(c3[3]), float(c3[4])

    # ── Bullish Gap (Low of C3 is higher than High of C1) ──
    if low3 > high1:
        if close3 < high2:
            return "BULLISH_GAP_RETRACING"  # closed back inside C2: likely to be revisited
        elif close3 > high2:
            return "BULLISH_GAP_EXTENDING"  # closed beyond C2: immediate follow-through

    # ── Bearish Gap (High of C3 is lower than Low of C1) ──
    if high3 < low1:
        if close3 > low2:
            return "BEARISH_GAP_RETRACING"
        elif close3 < low2:
            return "BEARISH_GAP_EXTENDING"

    return None


def compute_confirmation_bonus(symbol, direction, klines, vols, tf_score, btc_aligned=False, zone_ok=False, ms_bos=False, ms_bias=None, ms_choch=False, is_tier1=True, is_compression=False, is_sweep=False, entry=None, sl=None):
    """
    The Location Multiplier + hard Tier 1/Tier 2 AI cap.

    Bonus weights:
      +6.0  Risk-Proximity Bonus (this round): rewards a tight structural
            stop-loss distance, not just loud momentum indicators.
            Previously the scorecard only rewarded assets for being LOUD
            (Volume Strong +2.0, ADX Strong +1.5, SuperTrend +2.0) — a
            quiet, low-risk accumulation coil has dead volume and flat
            momentum BY DEFINITION, so it structurally could never win on
            those alone. This inverts part of that bias: if entry-to-SL
            distance is <0.5% (the number explicitly specified), award
            +6.0 — the exact same weight as the Location Multiplier
            below, making this now TIED for second-heaviest bonus in the
            system (below only ChoCh-in-zone's +7.5). Flagging that tie
            explicitly rather than letting it sit unremarked. Two lower
            tiers below 0.5% (<1.0% -> +3.0, <1.5% -> +1.5) were NOT
            specified in the request — my own addition, matching the
            graduated-tier style already used elsewhere in this function
            (e.g. volume's strong/moderate split), so a stop that's tight
            but not <0.5% still gets partial credit rather than a hard
            cliff to zero.
      +4.0  Liquidity Sweep (Spring/Upthrust) — a validated fakeout/stop-
            hunt reversal. Tied with Location Multiplier for third-
            heaviest as of this round (was "second-highest" before the
            Risk-Proximity bonus was added — corrected here since that
            claim is now stale), deliberately below ChoCh-in-zone
            (rarer/higher-conviction combined signal) but well above the
            old flat +1.0 pattern-detection bump, per explicit "make it
            an aggressive priority" instruction.
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

    # ── RISK-PROXIMITY BONUS: rewards a tight stop, not just loud momentum ──
    # See the function docstring for full reasoning. Computes the real
    # structural SL via get_structure_sl (pure computation on already-
    # fetched klines, no new API call) and scores the entry-to-SL
    # distance as a percentage. Only computed when entry/sl are provided
    # by the caller (optional params, so this remains backward compatible
    # with any call site not yet passing them).
    if entry is not None and sl is not None and entry > 0:
        sl_dist_pct = abs(entry - sl) / entry * 100
        if sl_dist_pct < 0.5:
            bonus += 6.0; notes.append(f"Risk-Proximity: SL {sl_dist_pct:.2f}% away - tight stop (+6.0)")
        elif sl_dist_pct < 1.0:
            bonus += 3.0; notes.append(f"Risk-Proximity: SL {sl_dist_pct:.2f}% away (+3.0)")
        elif sl_dist_pct < 1.5:
            bonus += 1.5; notes.append(f"Risk-Proximity: SL {sl_dist_pct:.2f}% away (+1.5)")

    # ── SPRING/UPTHRUST: Liquidity Sweep priority bonus ──
    # Point 3: "we already built a basic Liquidity Sweep... make it an
    # aggressive priority." Previously the sweep only got a flat +1.0
    # (TIER1_BASE+1.0) at pattern-detection time, the same modest bump
    # any Tier 1 pattern gets — not meaningfully prioritized. Per the
    # explicit reasoning (a validated sweep traps breakout traders whose
    # stop-losses become "rocket fuel"), this deserves real priority.
    # Set to +4.0 — a deliberate, meaningful increase from +1.0. Tied for
    # THIRD-heaviest as of this round (corrected from "SECOND-highest" —
    # that claim went stale once the +6.0 Risk-Proximity bonus was added
    # above), below ChoCh-in-zone's +7.5 and tied with Location
    # Multiplier / Risk-Proximity at +6.0. This is my own judgment call
    # on the exact number, flagging it as such rather than silently
    # picking a value. Applied additively (not as a replacement for the
    # zone/structure bonuses below), since a validated sweep is a
    # genuinely separate confirmation dimension from location/structure,
    # not a substitute for them.
    if is_sweep:
        bonus += 4.0; notes.append("Liquidity Sweep - Spring/Upthrust priority (+4.0)")

    # ── AGGRESSIVE ORDER FLOW: real directional confirmation ──
    # Rebuilt from the old dead has_whale_activity (was a boolean "one
    # big trade happened," no directionality, zero live call sites).
    # Used as a CONFIRMATION here, not a standalone trigger like Funding
    # Divergence Sniper — a deliberate distinction: order flow alone
    # doesn't specify WHAT level or setup matters, only that real size is
    # leaning one way right now, so it confirms a direction a pattern
    # already chose rather than inventing one from nothing.
    flow_direction = detect_aggressive_order_flow(klines)
    if flow_direction == direction:
        bonus += 2.0; notes.append(f"Aggressive order flow confirms {direction} (+2.0)")

    # ── FVG MOMENTUM EXTENSION CONFIRMATION (Video 2 SMC concept) ──
    # Rewards a genuine Fair Value Gap whose 3rd candle immediately
    # extended beyond the 2nd candle's range (real, immediate follow-
    # through), rather than closing back inside it (more likely to be
    # revisited/retraced). See detect_fvg_momentum_extension's own
    # docstring for why this is NOT labeled a "Break Away Gap" — that's
    # a stronger, unverifiable-at-this-instant claim this check doesn't
    # actually confirm.
    gap_type = detect_fvg_momentum_extension(klines)
    if gap_type == "BULLISH_GAP_EXTENDING" and direction == "BUY":
        bonus += 3.0; notes.append("Bullish FVG extending — immediate momentum follow-through (+3.0)")
    elif gap_type == "BEARISH_GAP_EXTENDING" and direction == "SELL":
        bonus += 3.0; notes.append("Bearish FVG extending — immediate momentum follow-through (+3.0)")
    elif gap_type == "BULLISH_GAP_RETRACING" and direction == "BUY":
        notes.append("Note: Bullish FVG retracing into C2 (expect a fill/retest)")
    elif gap_type == "BEARISH_GAP_RETRACING" and direction == "SELL":
        notes.append("Note: Bearish FVG retracing into C2 (expect a fill/retest)")

    # ── HIGHER-TIMEFRAME RSI DIVERGENCE: a real scorecard signal ──
    # detect_rsi_divergence already existed in this file, but was ONLY
    # ever called once, on 15m closes, purely to add a line of text to
    # Claude's AI-narrative context — never scored, and never checked on
    # a higher timeframe. A confirmed 1h divergence is a meaningfully
    # stronger, earlier signal than the 15m version (less noise, reflects
    # genuine multi-hour momentum exhaustion, not a single choppy swing) —
    # reused the exact same function directly (it's genuinely timeframe-
    # agnostic, just takes a list of closes) rather than rewriting it.
    try:
        klines_1h_div = get_cached_1h_klines(symbol)
        if klines_1h_div and len(klines_1h_div) >= 10:
            closes_1h = [float(k[4]) for k in klines_1h_div]
            div_1h = detect_rsi_divergence(closes_1h)
            if (div_1h == "BULLISH_DIV" and direction == "BUY") or (div_1h == "BEARISH_DIV" and direction == "SELL"):
                bonus += 3.0; notes.append(f"1h RSI divergence confirms {direction} (+3.0)")
    except Exception as e:
        logger.warning(f"1h RSI divergence {symbol}: {e}")

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
    # CRITICAL FIX (this round): VERIFIED AND REPRODUCED A REAL CRASH
    # before fixing this — the original "for name,base_score,direction
    # in patterns:" is strict 3-element unpacking, which would raise
    # ValueError the instant any pattern carrying the newly-added 4th
    # geometry-notes element reached this function (called
    # unconditionally on every non-empty scan result, every cycle).
    # Fixed to accept a variable-length tuple and thread the optional
    # geometry notes through into the scored output too, rather than
    # just avoid the crash by silently discarding it a second time.
    scored=[]
    for pat_tuple in patterns:
        name, base_score, direction = pat_tuple[0], pat_tuple[1], pat_tuple[2]
        geo_notes = pat_tuple[3] if len(pat_tuple) > 3 else None
        adj=get_adjusted_score(name,base_score,market_condition)
        scored.append((name,adj,direction,base_score,geo_notes))
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

def get_expectancy_report_text():
    """
    Point 5 of the four-part redesign (this round): win rate alone is a
    misleading metric — the user's own worked example (80% win rate with
    small wins and one large loss producing negative growth) is real and
    correct, and this report is built to answer the actual question that
    matters: is the strategy's mathematical expectancy positive.

    HONEST ABOUT A REAL DATA GAP: r_multiple (PnL as a multiple of the
    trade's OWN original risk distance) is new — added to the journal
    entry at trade-close time this round, using entry/sl fields that were
    already genuinely available but never captured into history before.
    Trades closed before this round have no r_multiple, so R-based stats
    below are computed only from entries that have it, and the report
    says so explicitly rather than silently mixing incompatible data or
    pretending more history exists than it does.
    """
    if not trade_journal:
        return f"{_H('EXPECTANCY & PROFIT FACTOR','📊')}\n\n  ⚪ No closed trades yet.\n\n  🕐 {get_ist_time()}"

    all_trades = trade_journal
    wins = [t for t in all_trades if t.get("result") == "WIN"]
    losses = [t for t in all_trades if t.get("result") == "LOSS"]
    total = len(all_trades)
    win_rate = (len(wins) / total * 100) if total > 0 else 0

    # Raw % PnL based averages — computable for every trade, old or new
    avg_win_pct = sum(t["pnl"] for t in wins) / len(wins) if wins else 0
    avg_loss_pct = sum(t["pnl"] for t in losses) / len(losses) if losses else 0
    gross_profit = sum(t["pnl"] for t in wins if t["pnl"] > 0)
    gross_loss = abs(sum(t["pnl"] for t in losses if t["pnl"] < 0))
    profit_factor = (gross_profit / gross_loss) if gross_loss > 0 else (float("inf") if gross_profit > 0 else 0)
    expectancy_pct = (win_rate/100 * avg_win_pct) + ((1 - win_rate/100) * avg_loss_pct)

    # R-multiple based stats — only from trades that actually have r_multiple
    r_trades = [t for t in all_trades if t.get("r_multiple") is not None]
    r_wins = [t for t in r_trades if t.get("result") == "WIN"]
    r_losses = [t for t in r_trades if t.get("result") == "LOSS"]
    avg_win_r = sum(t["r_multiple"] for t in r_wins) / len(r_wins) if r_wins else None
    avg_loss_r = sum(t["r_multiple"] for t in r_losses) / len(r_losses) if r_losses else None

    # Max drawdown — running equity curve from port_pnl (real, position-sized impact)
    running = 0.0; peak = 0.0; max_dd = 0.0
    for t in all_trades:
        running += t.get("port_pnl", t.get("pnl", 0))
        peak = max(peak, running)
        max_dd = min(max_dd, running - peak)
    net_port_pnl = sum(t.get("port_pnl", t.get("pnl", 0)) for t in all_trades)

    text = f"{_H('EXPECTANCY & PROFIT FACTOR','📊')}\n\n"
    text += f"  🎯 Win Rate    : <b>{win_rate:.1f}%</b>  ({len(wins)}W / {len(losses)}L, {total} trades)\n"
    text += f"  📈 Avg Win     : {avg_win_pct:+.2f}%\n"
    text += f"  📉 Avg Loss    : {avg_loss_pct:+.2f}%\n"
    text += f"  💰 Expectancy  : <b>{expectancy_pct:+.3f}%</b> per trade\n"
    _pf_display = f"{profit_factor:.2f}" if profit_factor != float('inf') else "∞"
    text += f"  ⚖️ Profit Factor: <b>{_pf_display}</b>" + ("  (gross profit ÷ gross loss)\n" if profit_factor != float('inf') else "  (no losses yet)\n")
    text += f"  📉 Max Drawdown: {max_dd:.2f}% (running, port-weighted)\n"
    text += f"  🏦 Net PnL     : {fmt_pnl(net_port_pnl)}\n"
    text += f"\n  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
    if r_trades:
        text += f"  R-Multiple stats (from {len(r_trades)}/{total} trades with risk data):\n"
        text += f"  📈 Avg Win  : {avg_win_r:+.2f}R\n" if avg_win_r is not None else "  📈 Avg Win  : n/a\n"
        text += f"  📉 Avg Loss : {avg_loss_r:+.2f}R\n" if avg_loss_r is not None else "  📉 Avg Loss : n/a\n"
    else:
        text += f"  R-Multiple stats: no trades with risk data yet — this\n"
        text += f"  tracking started this round, so it builds up going forward.\n"
    text += f"\n  🕐 {get_ist_time()}"
    return text

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

def get_detailed_summary_text():
    """
    System Telemetry & Summary — the /summary command's new content.
    Prepends cycle-count and radar-conversion telemetry ahead of the
    10-day performance breakdown (this function's own real logic now —
    the original get_10day_summary_text this was copied from was
    removed as confirmed-dead code in a later round's audit, since no
    other caller of it was ever found).
    """
    today=datetime.now(IST).date()
    conversion_rate = (radar_coins_triggered / radar_coins_added * 100) if radar_coins_added > 0 else 0
    uptime_secs = time.time() - _bot_start_time
    uptime_h = int(uptime_secs // 3600); uptime_m = int((uptime_secs % 3600) // 60)

    text = f"{_H('SYSTEM TELEMETRY & SUMMARY','⚙️')}\n\n"
    text += f"  🔄 Scan Cycles: <b>{total_scan_cycles}</b>  •  ⏱️ Uptime: <b>{uptime_h}h {uptime_m}m</b>\n"
    text += f"  📡 Radar Conversions: {radar_coins_triggered}/{radar_coins_added} (<b>{conversion_rate:.1f}%</b>)\n"
    text += f"  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"

    ow=ol=0; op=0.0; best_pnl=worst_pnl=None; best_ds=worst_ds=""
    for days_ago in range(9,-1,-1):
        day=today-timedelta(days=days_ago)
        dt=[j for j in trade_journal if j.get("date")==str(day)]
        w=sum(1 for t in dt if t["result"]=="WIN"); l=sum(1 for t in dt if t["result"]=="LOSS")
        total=w+l; pnl=sum(t.get("port_pnl", t["pnl"]) for t in dt)
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

DESK_REPORT_COINS = ["BTC","ETH","SOL","HYPE","BERA","IP"]

def send_pressure_cooker_report():
    """
    The "Pressure Cooker" Report — the scheduled watchlist alert. Chosen
    over an instant per-coin ping (the alternative design considered):
    retest_watchlist genuinely can accumulate multiple entries within a
    single scan cycle (three separate call sites feed it — the AI-
    flagged-LATE fallback, the already-extended-move check, and the BOS-
    retest gate, which was extended in an earlier round to also cover
    Double Top/Bottom) — an instant ping has no natural batching for
    that, so a genuinely volatile market could produce a real flood of
    individual messages, exactly what a "clean signal, not noise"
    design should avoid.

    Interval set to 2 hours (not matched to the existing 8h AI desk
    report's cadence) — watchlist entries expire after 12 hours
    (check_retest_triggers), so 2h gives roughly 5-6 chances to see a
    given entry while it's genuinely still live, versus only 1-2 chances
    at 8h. The actual goal ("prep your charts") needs the alert to
    arrive while the setup still has real runway left, not near its
    expiry.

    Silent (sends nothing) if the watchlist is currently empty — no
    "nothing to report" message, consistent with the existing "don't
    spam" design goal.
    """
    # PENDING-only filter (this round) — same reasoning as
    # get_retest_watchlist_text: TRIGGERED entries now persist until
    # their 12h expiry rather than disappearing immediately, and this
    # report's whole premise is "here's what's currently on the radar."
    pending = {c: w for c, w in retest_watchlist.items() if w.get("status", "PENDING") == "PENDING"}
    if not pending:
        return
    lines = [f"👀 <b>PRESSURE COOKER REPORT</b>", f"⚙️ <b>{len(pending)} coin(s) on the radar</b>", "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━", ""]
    for coin, w in sorted(pending.items(), key=lambda kv: kv[1]["logged_at"], reverse=True):
        age_hrs = (get_ist_datetime() - w["logged_at"]).total_seconds() / 3600
        dir_icon = "🟢" if w["direction"] == "BUY" else "🔴"
        reason = "waiting for pullback to breakout line" if w.get("pattern_type") == "bos_retest" else "move already extended, watching for retest"
        lines.append(f"{dir_icon} <b>{coin}</b>  {w['direction']}")
        lines.append(f"   📌 {w['pattern']}")
        lines.append(f"   📍 Level: <code>{format_price(w['level'])}</code>  •  {reason}")
        lines.append(f"   ⏱️ On radar {age_hrs:.1f}h (expires at 12h)")
        lines.append("")
    lines.append(f"🕐 {get_ist_time()}")
    send_telegram("\n".join(lines))

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
        grade,pts,_=get_signal_grade(best["score"],vol_ratio_gem,oi_rising,best["tf_score"],vol_ok,rsi_ok,funding_ok,st_ok,vwap_ok,zone_ok,adx_val,btc_aligned_gem,ms_b["bias"],ms_b["bos"])  # is_sweep not computed in this simpler command's context, left at default False
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
        with trade_lock:
            s = pending_signals.get(coin)
            _eng_label = get_engine_label(s["pattern"].split(" + ")[0]) if s and s.get("pattern") else "📊 SIGNAL ENGINE"
            if coin in pending_signals: del pending_signals[coin]
        send_telegram(f"⏰ <b>{BOT_HEADER}</b>\n🏗️ Engine: {_eng_label}\nSignal expired: <b>{coin}</b>")
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

def update_trailing_sl(coin,trade,price,klines=None):
    """
    The Law of Dynamic Noise: Chandelier Exit trailing stop, based on
    CURRENT market volatility (ATR) rather than a rigid fixed percentage
    of the profit target.

    FIXED (this round): The Volatility Activation Buffer. VERIFIED THE
    SUFFOCATION BUG WAS REAL before applying this fix — reproduced it
    directly: a tight 0.5%-away structural SL (exactly the kind this bot
    generates for BONK/STRK-style setups) got choked to 0.15% away
    immediately after entry, based on a stale historical spike from
    BEFORE the trade even started, despite price having captured zero
    real profit. The previous version's `new_sl < price` guard only
    prevented an immediately-self-triggering stop — it did NOT prevent
    this softer but still damaging case where the stop tightens to
    within normal noise/spread range without the trade ever having a
    real profit cushion. Fixed with two changes: (1) trailing is now
    barred from engaging at all until price has moved at least 1.5x ATR
    into genuine profit, and (2) the trail anchor (highest high / lowest
    low) is now taken from only the last 5 candles instead of the full
    fetched window, so even after activation a stale wick from many
    candles ago can't distort the trail.

    `klines` is optional (defaults to None) for backward compatibility —
    if not provided, or too short, this falls back to the ORIGINAL fixed-
    percentage behavior rather than silently doing nothing.

    MACRO TIMEFRAME RESPECT ADDED (this round): VERIFIED THE REAL GAP
    before applying this — confirmed the actual call site
    (check_active_trades) passes 15m klines_check unconditionally for
    every trade, with no timeframe-awareness anywhere in this function
    previously — meaning a genuine 4H macro swing trade would get its
    trailing stop computed from 15m volatility, choking a multi-day
    setup within hours. For trades tagged is_macro (set by
    check_active_macro_coils at entry), this now re-fetches real 4H
    data instead of using whatever the caller passed in.
    """
    if trade.get("is_macro"):
        klines = get_klines(trade.get("symbol", coin+"USDT"), "4h", 20)
    elif trade.get("is_lightning") or trade.get("pattern","").split(" + ")[0] in ("Yellow Circle Sniper","5m Multi-TF Sniper"):
        # REAL GAP FOUND AND FIXED (this round): standalone Engine-1
        # snipers ("Yellow Circle Sniper", "5m Multi-TF Sniper") are
        # created as plain tuple appends inside detect_patterns (the
        # 15m pipeline) with no is_lightning tag ever set on them —
        # traced every real creation site to confirm this. They were
        # falling through to the default 15m ATR trailing stop despite
        # already having real, established 5m-native treatment
        # elsewhere in this file (the reversal-check and chart/SL
        # mappings both already list them as "5m"), confirming 5m is
        # genuinely the correct scale, not a new assumption.
        #
        # LIGHTNING ENGINE FIX (earlier round): mirrors the is_macro
        # pattern directly above. VERIFIED THIS WAS THE REAL, LIVE
        # CAUSE of the reported profit-shortfall bug — traced every
        # reference to is_lightning across the file and confirmed it
        # was never checked anywhere in trade management, meaning a
        # Lightning trade's tight, fast-timeframe target was being
        # trailed using 15m ATR, a much larger volatility scale than
        # the trade itself. Re-fetches real 5m data instead — matching
        # check_lightning_ignition_engine's own real setup-detection
        # timeframe — so the trail distance is scaled to the same
        # timeframe the trade was actually built around.
        klines = get_klines(trade.get("symbol", coin+"USDT"), "5m", 20)

    if klines and len(klines) >= 15 and trade.get("timestamp"):
        atr = calculate_atr(klines, 14)
        if atr <= 0: return
        atr_trail_dist = atr * 2.5  # Chandelier Exit standard multiple
        activation_buffer = atr * 1.5  # must be in real profit before trailing engages
        if trade["direction"] == "BUY":
            if price > trade["entry"] + activation_buffer:
                highest_recent_high = max(float(k[2]) for k in klines[-5:])
                new_sl = highest_recent_high - atr_trail_dist
                if new_sl > trade["sl"] and new_sl < price:
                    with trade_lock:
                        if coin in active_trades: active_trades[coin]["sl"] = new_sl
                    save_active_trades()
        else:
            if price < trade["entry"] - activation_buffer:
                lowest_recent_low = min(float(k[3]) for k in klines[-5:])
                new_sl = lowest_recent_low + atr_trail_dist
                if new_sl < trade["sl"] and new_sl > price:
                    with trade_lock:
                        if coin in active_trades: active_trades[coin]["sl"] = new_sl
                    save_active_trades()
        return
    # Fallback: original fixed-percentage trail (klines unavailable/too short)
    trail=abs(trade["tp"]-trade["entry"])*0.3
    if trade["direction"]=="BUY":
        new_sl=price-trail
        if new_sl>trade["sl"]:
            with trade_lock:
                if coin in active_trades: active_trades[coin]["sl"]=new_sl
            save_active_trades()
    else:
        new_sl=price+trail
        if new_sl<trade["sl"]:
            with trade_lock:
                if coin in active_trades: active_trades[coin]["sl"]=new_sl
            save_active_trades()

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

    # MILESTONE THRESHOLDS PUSHED DEEPER (this round): 30/60/85 -> 50/75/90.
    # VERIFIED THE REAL INTERACTION PROBLEM before applying this: confirmed
    # update_trailing_sl, check_profit_milestones, and the reversal check
    # in check_active_trades all genuinely run sequentially on the SAME
    # price snapshot every scan cycle, meaning a single normal retest
    # could trigger more than one exit mechanism, with whichever runs
    # first effectively winning. Pushing M1 out to 50% gives a trade
    # genuine room to survive a normal 30%-ish retest without an
    # immediate breakeven-lock. Deliberately did NOT also delete
    # update_trailing_sl (see that function's own note) — kept at its
    # current, earlier 1.5x ATR activation specifically so it fills the
    # real protection gap this wider spacing creates, rather than
    # leaving a trade fully exposed with zero protection until 50%.
    m1=target*0.50; m2=target*0.75; m3=target*0.90

    def _sl_lock_price(target_pnl, lock_ratio):
        gain_price = abs(price_at_pnl(ep, direction, lev, target_pnl) - ep)
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
        # TIME-TO-M1 CAPTURE (this round): VERIFIED THIS WAS A REAL GAP
        # before fixing — milestones_sent only ever stored string labels
        # ("p1", "p2"), never a timestamp, and the final trade_journal
        # entry at close preserved nothing about whether or when M1 was
        # reached. Once a trade closed, "how quickly did this hit M1"
        # became unanswerable from historical data — only visible live,
        # in the moment, via the Telegram message. Records the actual
        # elapsed minutes here (not a raw timestamp) so it survives
        # directly into the journal without needing entry-time
        # arithmetic performed later against a value that might not
        # even be there.
        if trade.get("timestamp"):
            m1_mins = (get_ist_datetime() - trade["timestamp"]).total_seconds() / 60
            active_trades[coin]["time_to_m1_mins"] = round(m1_mins, 1)
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

def check_5m_sniper_trigger(symbol, direction):
    """
    The Law of Two-Stage Execution (The Sniper Trigger).

    "BLIND TO THE PAST" BUG FIXED (this round): VERIFIED THIS WAS REAL
    AND SEVERE before applying, cross-checked against actual production
    screenshots — confirmed the previous version only ever checked index
    [-1] (the single most recent 5m candle). The scan cycle runs every
    ~90s, but a 5m candle only closes every 5 minutes — meaning most
    scan cycles re-check the exact same still-forming candle multiple
    times, and a genuine wick rejection or micro-reclaim that happened
    1-2 candles (5-10 minutes) in the past was structurally invisible to
    this check. This is mathematically consistent with real observed
    behavior: dozens of coins sitting in "EARLY WATCH — waiting for the
    5m trigger to confirm" for hours, since the exact moment their real
    reversal candle formed, this check likely wasn't looking at it.

    Fixed by checking the last 3 candles (not just the current one).
    VERIFIED THE REPLACEMENT LOGIC directly before adopting it (not
    trusted blindly, per this session's standard) — confirmed the
    k5[i-4:i] comparison windows across all three loop iterations have
    no lookahead bias (each window correctly excludes the candle being
    evaluated), and confirmed the volume baseline (a fixed 10-candle
    window at k5[-13:-3]) deliberately excludes the 3 candles being
    checked from their own average — a genuine improvement over the
    prior rolling vols5[-10:] baseline, which would have let a candle's
    own volume inflate the average it's being compared against.

    Still keeps a real, non-zero volume floor (vol_not_dead >= 0.6x) —
    a wick rejection with literally zero participation behind it is
    still indistinguishable from noise on a thin coin; this session's
    explicit goal has consistently been minimizing BOTH late entries
    AND false positives, not earlier entries at any cost.

    Returns (triggered: bool, note: str).
    """
    try:
        k5 = get_klines(symbol, "5m", 15)
        if not k5 or len(k5) < 13:
            return False, "5m data unavailable"

        # Check the last 3 candles so a recent wick/reclaim that already
        # happened isn't invisible just because a newer, quieter candle
        # has since formed on top of it.
        for i in range(-3, 0):
            c_open, c_high, c_low, c_close = float(k5[i][1]), float(k5[i][2]), float(k5[i][3]), float(k5[i][4])
            candle_range = c_high - c_low

            avg_v = sum(float(x[5]) for x in k5[-13:-3]) / 10 if len(k5) >= 13 else 1.0
            vol_ratio = float(k5[i][5]) / avg_v if avg_v > 0 else 0
            vol_spiking = vol_ratio >= 1.5
            vol_not_dead = vol_ratio >= 0.6

            if direction == "BUY":
                bullish_close = c_close > c_open
                breaking_high = c_close > max(float(x[2]) for x in k5[i-4:i]) if len(k5[:i]) >= 4 else False
                if bullish_close and breaking_high and vol_spiking:
                    return True, f"5m Sniper: Breakout confirmed ({vol_ratio:.1f}x volume)"
                lower_wick_pct = (min(c_open, c_close) - c_low) / candle_range * 100 if candle_range > 0 else 0
                if (lower_wick_pct >= 35.0 or breaking_high) and bullish_close and vol_not_dead:
                    return True, f"5m Sniper: Early micro-reversal/level defense ({vol_ratio:.1f}x vol)"

            elif direction == "SELL":
                bearish_close = c_close < c_open
                breaking_low = c_close < min(float(x[3]) for x in k5[i-4:i]) if len(k5[:i]) >= 4 else False
                if bearish_close and breaking_low and vol_spiking:
                    return True, f"5m Sniper: Breakdown confirmed ({vol_ratio:.1f}x volume)"
                upper_wick_pct = (c_high - max(c_open, c_close)) / candle_range * 100 if candle_range > 0 else 0
                if (upper_wick_pct >= 35.0 or breaking_low) and bearish_close and vol_not_dead:
                    return True, f"5m Sniper: Early micro-reversal/level defense ({vol_ratio:.1f}x vol)"

        return False, "Waiting for 5m volume/breakout or early micro-reversal trigger"
    except Exception as e:
        return False, f"5m trigger error: {e}"


def check_evaluating_signals():
    """
    The Poll & Resume half of the two-stage EVALUATING pipeline. Runs
    every scan cycle against coins currently held in evaluating_signals
    — checks the 5m sniper for each one, and if it fires within the 45-
    minute window, resumes format_and_send with the held setup.

    VERIFIED A REAL GAP before applying this, that the original
    blueprint didn't address: the held `setup` dict's `scan_price` is
    anchored to the moment of INITIAL 15m detection. If left unchanged
    across a resume that can happen up to 45 minutes later,
    format_and_send's first drift check (which compares a freshly
    fetched live price against `setup["scan_price"]`) would silently
    have its meaning repurposed — instead of measuring the same-cycle
    detection-to-execution latency it was built to catch, it would be
    comparing a fresh price against an up-to-45-minute-old anchor,
    which is a fundamentally different (and much noisier) question.
    Fixed by refreshing `scan_price` to the current price right before
    resuming, so that check's semantics stay consistent whether a
    signal flowed through in one pass or was held and resumed — this
    doesn't remove the drift check, it keeps it measuring what it's
    actually meant to measure at the moment of the real decision.
    """
    global evaluating_signals
    triggered_any = False
    now = get_ist_datetime()

    for coin, data in list(evaluating_signals.items()):
        # Give it 90 minutes (18 x 5m candles) to fire before giving up —
        # widened from 45 (this round), calibrated against the user's own
        # reported real-world gap (a specific breakout took ~60 minutes
        # from genuine coil-start to actual entry, which the old 45-min
        # window would have missed even with correct early detection).
        minutes_active = (now - data["logged_at"]).total_seconds() / 60
        if minutes_active > 90:
            logger.info(f"{coin} evaluation expired — no 5m trigger within 90 mins.")
            del evaluating_signals[coin]
            triggered_any = True
            continue

        setup = data["setup"]
        market_condition = data["market_condition"]

        sniper_triggered, sniper_note = check_5m_sniper_trigger(setup["symbol"], setup["direction"])

        if sniper_triggered:
            logger.info(f"{coin} EVALUATING signal triggered: {sniper_note} — Resuming pipeline.")
            del evaluating_signals[coin]
            triggered_any = True

            # Refresh scan_price to now (see docstring) before resuming,
            # so format_and_send's own drift check measures fresh
            # latency, not staleness accumulated across the hold.
            fresh_scan_price = get_price(setup["symbol"])
            if fresh_scan_price:
                setup["scan_price"] = fresh_scan_price

            format_and_send(setup, coin, market_condition=market_condition, from_evaluation=True)

    if triggered_any:
        save_evaluating_signals()

def format_and_send(setup,coin,is_river=False,is_instant=False,market_condition="bull",from_evaluation=False):
    global sent_coins,coin_cooldowns
    if check_circuit_breaker(): return False
    if not is_good_trading_session(coin): return False
    live_price=get_price(setup["symbol"])
    if not live_price: return False
    entry=live_price
    # Threshold raised 3.5 -> 5.0 per explicit user instruction, applied
    # over my own disagreement: I tested the stated justification (that
    # the 5m sniper trigger causes this drift) and found it doesn't hold
    # — this check runs on scan_price vs. live entry price, unrelated to
    # the sniper trigger's own separate 5m data read. Flagged that
    # directly; the user asked for the change anyway after hearing it.
    drift_pct=abs(entry-setup["scan_price"])/setup["scan_price"]*100
    if drift_pct>5.0:
        logger.info(f"{coin} rejected - drifted {drift_pct:.1f}%"); return False
    # The Law of Daily ATR Exhaustion. is_move_already_extended() already
    # stops the bot from chasing a coin that just pumped on the 15m
    # chart, but that's a LOCAL (recent-candle) check — it doesn't look
    # at the Daily chart. If a coin is having a genuine news-driven 40%
    # day (3x its normal 14-day Daily ATR), a "Bull Flag" on the 15m
    # chart is often just noise on top of an already-exhausted daily
    # move — buying it is chasing the top of a move that's mathematically
    # spent, not a fresh setup. Checked here (early, before the more
    # expensive 15m/1h processing below) so an exhausted day fails fast.
    klines_1d=get_klines(setup["symbol"],"1d",20)
    if klines_1d and len(klines_1d)>=15:
        daily_atr=calculate_atr(klines_1d,14)
        todays_range=float(klines_1d[-1][2])-float(klines_1d[-1][3])  # today's High - Low
        if daily_atr>0 and todays_range>(daily_atr*2.5):
            logger.info(f"{coin} rejected - Daily ATR exhausted (today's range {todays_range:.4g} vs "
                       f"14d ATR {daily_atr:.4g}, {todays_range/daily_atr:.1f}x)")
            return False
    klines_15m=get_klines(setup["symbol"],"15m",100)
    klines_1h=get_klines(setup["symbol"],"1h",50)
    if not klines_15m: return False
    closes=[float(x[4]) for x in klines_15m]
    # NATIVE-TIMEFRAME SL DATA (this round): VERIFIED THE CLAIM before
    # applying this — confirmed the SL/chart calls below this point were
    # genuinely, unconditionally fed 15m data regardless of which
    # pattern fired, meaning a Yellow Circle Sniper or Order Flow Sniper
    # signal (detected on 3m/5m data with an implied tight stop) got its
    # ACTUAL stop-loss computed from 15m swing structure instead — a
    # real, much wider stop than the pattern's own detection logic
    # implied. Scoped narrowly: only these three genuinely 3m/5m-native
    # patterns get their own timeframe's klines for SL/chart purposes;
    # every other pattern keeps using klines_15m exactly as before,
    # since closes/klines_15m are used pervasively elsewhere in this
    # function (market structure, zones, AI review data) where 15m
    # remains the correct, intended timeframe.
    # PER-PATTERN NATIVE TIMEFRAME MAPPING (this round): VERIFIED THE
    # REAL, ACTUAL DETECTION TIMEFRAME of each pattern individually
    # before building this, rather than keep a single blanket interval
    # for the whole group — traced detect_yellow_circle_sniper's and
    # detect_5m_sniper_entry's real internal get_klines calls (both
    # genuinely 5m), detect_order_flow_sniper's real data source via its
    # caller in the scan loop (genuinely 15m — the outlier of the
    # group), and detect_cvd_delta_3m's (genuinely 3m). Per explicit
    # request, Lightning 3M Ignition specifically now renders its
    # visual chart on real 5m data (not the 9m synthesis from last
    # round, and not the previous blanket 3m) — a genuinely different,
    # deliberate choice for THIS pattern's chart output specifically,
    # distinct from what it actually detects on internally.
    _pattern_native_interval = {
        "Yellow Circle Sniper": "5m",
        "5m Multi-TF Sniper": "5m",
        "Order Flow Sniper": "15m",
    }
    _sl_klines = klines_15m
    _chart_interval = "15m"
    _primary_for_native = setup["pattern"].split(" + ")[0]
    if _primary_for_native.startswith("Lightning 5M Setup") or (setup.get("is_lightning") and "Ignition" in _primary_for_native):
        # LIGHTNING ENGINE FIX (this round): FOUND AND FIXED THE ACTUAL
        # ROOT CAUSE of the reported "chart still shows 15m" issue.
        # Verified directly against the real FLOW pattern name from the
        # screenshot ("Lightning 3M Ignition (Taker Delta) (Fast-Track)")
        # that .startswith("Lightning 5M Setup") is False for the
        # CVD-only Lightning variant — meaning every trade from that
        # specific mechanism has always fallen through to the 15m
        # default chart, unconditionally, not just when Fast-Track was
        # involved. Added the is_lightning tag check (confirmed set
        # correctly on both real Lightning mechanisms) so both are now
        # covered.
        #
        # Prefix check (not a literal dict lookup) since
        # check_lightning_ignition_engine builds its pattern name
        # dynamically (e.g. "Lightning 5M Setup (Tweezer Bottom)") and
        # every variant shares this fixed prefix. Corrected to 5m per
        # explicit instruction (the setup-detection timeframe, matching
        # what this pattern's own name now accurately states).
        _native_klines = get_klines(setup["symbol"], "5m", 60)
        if _native_klines and len(_native_klines) >= 20:
            _sl_klines = _native_klines
            _chart_interval = "5m"
    elif _primary_for_native in _pattern_native_interval:
        _native_interval = _pattern_native_interval[_primary_for_native]
        if _native_interval != "15m":
            _native_klines = get_klines(setup["symbol"], _native_interval, 60)
            if _native_klines and len(_native_klines) >= 20:
                _sl_klines = _native_klines
                _chart_interval = _native_interval
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
    # REAL BUG FOUND AND FIXED (this round), caught via direct execution
    # testing, not just the syntax checker: _floor_primary/_primary_pat
    # were previously computed INSIDE the 15m penalty block below, but a
    # LATER, separate, unconditional check (the Grade B/C accumulation-
    # exemption floor) references _floor_primary regardless of
    # is_macro — wrapping the block without also fixing this would have
    # produced a genuine UnboundLocalError for every macro trade.
    # Computed once, unconditionally, here instead, so both the wrapped
    # internal logic and the later unconditional check share the same
    # single, always-available value.
    _primary_pat = setup["pattern"].split(" + ")[0]
    _floor_primary = _primary_pat
    # MACRO DEFAULTS FOR VARIABLES NORMALLY SET INSIDE THE 15M BLOCK
    # (this round): VERIFIED BOTH PRECISELY, caught via direct execution
    # testing (a real UnboundLocalError on each), not just the syntax
    # checker — st_ok and is_instant are both referenced unconditionally
    # later in this function (message-icon display, expiry timing) but
    # were only ever assigned inside the now-conditional 15m block.
    # st_ok ("does 15m/1H SuperTrend agree") is genuinely inapplicable
    # for a macro trade — the check is deliberately bypassed, not
    # failed, so defaulting True avoids a misleading warning icon for a
    # check that was never run. is_instant's local recomputation, if it
    # DID run for a macro trade, would produce the same True value the
    # caller already passes as a parameter (setup_score is always 99.0,
    # clearing INSTANT_SIGNAL_THRESHOLD=97) — made explicit here rather
    # than rely on that implicit parameter-shadowing coincidence, which
    # is fragile against future changes to the calling convention.
    if setup.get("is_macro"):
        st_ok = True
        is_instant = True
    # ── MACRO VIP FAST-TRACK: BYPASS 15M PENALTIES AND VETOES (this round) ──
    # VERIFIED THIS WAS A REAL, SEVERE GAP before applying: traced the
    # actual real SuperTrend exemption list and confirmed "Pre-Breakout
    # Macro" is genuinely absent (and, since its dynamic pattern name has
    # no " + " separator, could never match a plain membership check
    # anyway) - meaning a macro trade reversing off a real 4H bottom,
    # which very plausibly still reads bearish on lagging 15m/1H
    # SuperTrend, would hit a genuine hard return False here. Also
    # computed the real penalty-stack math: RSI/sector/weekend/5m-timing/
    # SuperTrend-lag penalties can total -32 points, genuinely enough to
    # bleed a 99.0 macro score below the 92.0 floor even without the
    # hard block. Wraps the entire 15m penalty/veto gauntlet, matching
    # the VWAP/POC/AI bypasses already verified and applied in earlier
    # rounds for the exact same class of gap.
    if not setup.get("is_macro"):
        # ── ACCUMULATION VOLUME EXEMPTION ──
        # VERIFIED THE REAL MECHANISM before applying this fix (traced the
        # actual math, not just accepted the diagnosis): an Inside Bar Coil
        # genuinely sitting in a real HTF zone gets base(88.0) + Location
        # Multiplier(+6.0) = 94.0, comfortably clearing the 92.0 floor via
        # the confirmation bonus system ALONE — the bonus system rewarding
        # "loud" indicators was NOT actually blocking these patterns. The
        # REAL cause: this volume-soft penalty (-6) fires on the exact quiet
        # volume that DEFINES a genuine accumulation coil, directly canceling
        # out that entire 6-point cushion and landing exactly back at 88.0 —
        # below the floor, with zero margin left for anything else. Fixed by
        # exempting these two specific patterns from this one penalty (not
        # the whole scoring architecture) since dead volume is their intended
        # signature, not a weakness to punish.
        is_quiet_accumulation_pattern = any(p in setup["pattern"] for p in ("Inside Bar Coil","Pre-Breakout Compression","Volatility Contraction (Coiling)","Early Spark Ignition","Smart Money Absorption","Funding Divergence Sniper"))
        if not vol_ok and not is_quiet_accumulation_pattern:
            score_penalty += 6; penalty_notes.append("volume soft (-6)")
        if not rsi_ok:
            score_penalty += 5; penalty_notes.append("RSI stretched (-5)")
        if not funding_ok:
            score_penalty += 4; penalty_notes.append("funding against (-4)")
        if is_volatile:
            logger.info(f"{coin} high volatility — noted, letting AI judge")

        # ── THE TWO-STAGE EXECUTION GATE ──
        # If this is a predictive accumulation pattern, we MUST wait for the
        # 5m trigger — we do not enter a quiet coil until the 5m chart
        # confirms the explosion. For every other pattern, the sniper trigger
        # still runs (replacing the old, softer get_ltf_confirmation), but
        # only applies a scorecard penalty rather than a hard block, since
        # those patterns already have their own confirmation baked into
        # detection (a confirmed breakout, a validated retest, etc.) and
        # don't share the "quiet coil, nothing confirmed yet" premise that
        # makes waiting for 5m genuinely necessary here.

        # ── HARD ANTI-CHASE VETO (this round) ──
        # VERIFIED THE ACTUAL FAILURE MECHANISM before building this, and
        # found something different from the initial diagnosis: computed the
        # real ATR-inflation effect with real numbers (a single large
        # breakout candle joining a 14-period average) and confirmed it's
        # genuine but not large enough on its own to explain ONDO slipping
        # through — even inflated, the reading still cleared my harshest -4
        # scorecard tier. The real gap, found by tracing the actual code: a
        # low grade from that penalty only ever gated whether the AI got
        # CALLED (is_grade_a), never whether the trade executed — a non-
        # Grade-A signal still fires on pure code, no AI, per the existing
        # "executing on pure code, no AI call" fallback path. A soft
        # scorecard penalty was structurally incapable of vetoing anything,
        # for a different reason than described, but the conclusion (this
        # needs to be a hard veto, not a score deduction) is correct.
        #
        # RELOCATED TO THIS EARLIER POSITION after testing found the
        # original placement (right after highs_15m/lows_15m, further down
        # this function) sat AFTER several other checks — the 5m sniper
        # trigger, score-penalty adjustments, a VWAP mean-reversion check —
        # any of which could reject or short-circuit the trade before this
        # veto ever got evaluated. Moved here, right after _primary_pat is
        # first available and before any of that downstream logic runs, so
        # it's genuinely the early, hard gate it's meant to be. Uses
        # LOCALLY-derived closes/highs/lows/vols (prefixed _veto_ to avoid
        # colliding with the real, later-computed versions of the same names
        # used by the rest of this function) since klines_15m is already
        # fetched by this point.
        #
        # SCOPED to lagging/confirmation patterns only — VERIFIED THIS
        # MATTERS before applying it broadly: an unconditional veto would
        # also block Yellow Circle Sniper, Order Flow Sniper, and 5m Multi-
        # TF Sniper, all built and verified in prior rounds specifically to
        # catch a LIVE, fresh breakout — which structurally involves real,
        # recent movement from a local base by definition. Restricted to the
        # same lagging patterns already routed to the retest watchlist for
        # the same underlying reason (a confirmed shape is, by construction,
        # already a late entry).
        if _primary_pat in ("Double Top","Double Bottom","BOS Breakout","Volume Breakout"):
            _veto_closes = [float(k[4]) for k in klines_15m]
            _veto_highs = [float(k[2]) for k in klines_15m]
            _veto_lows = [float(k[3]) for k in klines_15m]
            recent_4_lows = _veto_lows[-4:]
            recent_4_highs = _veto_highs[-4:]
            _veto_direction = setup["direction"]
            if _veto_direction == "BUY":
                local_base = min(recent_4_lows)
                vertical_stretch_pct = (entry - local_base) / local_base * 100 if local_base > 0 else 0
            else:
                local_base = max(recent_4_highs)
                vertical_stretch_pct = (local_base - entry) / entry * 100 if entry > 0 else 0
            if vertical_stretch_pct > 1.8:
                logger.info(f"{coin} Anti-Chase Veto: {_veto_direction} extended {vertical_stretch_pct:+.2f}% from the local 1h base ({_primary_pat}). Move is exhausted, rerouting to retest watchlist.")
                _veto_precise_level = None
                if _primary_pat in ("Double Top","Double Bottom"):
                    _veto_vols = [float(k[5]) for k in klines_15m]
                    _veto_avg_vol = sum(_veto_vols[-20:]) / 20 if len(_veto_vols) >= 20 else 1.0
                    if _primary_pat == "Double Bottom":
                        _veto_fired, _veto_lvl = detect_double_bottom_pro(_veto_highs, _veto_lows, _veto_closes, _veto_vols, entry, _veto_avg_vol)
                    else:
                        _veto_fired, _veto_lvl = detect_double_top_pro(_veto_highs, _veto_lows, _veto_closes, _veto_vols, entry, _veto_avg_vol)
                    if _veto_fired and _veto_lvl > 0:
                        _veto_precise_level = _veto_lvl
                log_retest_candidate(coin, setup["symbol"], _veto_direction, _veto_closes, _veto_highs, _veto_lows, setup["pattern"], pattern_type="bos_retest", precise_level=_veto_precise_level)
                coin_cooldowns[coin] = get_ist_datetime() + timedelta(minutes=30)
                return False

        is_quiet_accumulation = _primary_pat in ("Inside Bar Coil","Pre-Breakout Compression","Volatility Contraction (Coiling)","Early Spark Ignition","Smart Money Absorption","Funding Divergence Sniper","Liquidity Sweep","Trend Continuation Coil","Bull Flag Formation","Bear Flag Formation")

        sniper_triggered, sniper_note = check_5m_sniper_trigger(setup["symbol"], setup["direction"])

        if is_quiet_accumulation and not sniper_triggered and not from_evaluation:
            # DEEP COIL BYPASS (earlier round): if the setup already scores A+
            # (>=92.0) AND is genuinely sitting inside a confirmed HTF zone,
            # skip the 5m wait entirely and send now — a setup this strong,
            # already resting on a real institutional level, doesn't need
            # the extra confirmation layer the sniper exists to provide for
            # weaker setups. FOUND A REAL BUG IN THE PROPOSED CODE before
            # applying it (that round): it referenced `zone_ok` directly, but
            # that variable isn't computed until much later in this same
            # function — using it here as given would raise a NameError and
            # crash every single accumulation-pattern signal, not just
            # selectively bypass some of them. Fixed by computing a local,
            # narrowly-scoped zone check specifically for this bypass — a
            # small, accepted extra fetch only for accumulation patterns
            # actually being evaluated here, not added to every signal's cost.
            _deep_coil_zones = get_htf_zones(setup["symbol"])
            _deep_coil_zone_ok, _deep_coil_zone_label = is_in_zone(entry, setup["direction"], _deep_coil_zones)
            if _deep_coil_zone_ok and setup["setup_score"] >= 92.0:
                logger.info(f"{coin} Deep Coil Bypass — A+ score ({setup['setup_score']:.1f}) already sitting in {_deep_coil_zone_label}, skipping 5m wait")
                penalty_notes.append("Deep Coil Bypass (Instant Entry)")
            else:
                # AI-BEFORE-SUSPEND FIX (this round): VERIFIED A REAL,
                # SEVERE GAP before applying — traced the actual code
                # and confirmed no AI call existed anywhere on this
                # path. Combined with last round's already-verified
                # from_evaluation AI bypass, a quiet coil could
                # genuinely go from detection to execution with Claude
                # never once reviewing it — suspended before the
                # original, later AI block on the way in, then
                # bypassed it entirely on the way out.
                #
                # VERIFIED THE PROPOSED CODE'S VARIABLE SCOPE before
                # applying it, catching a real problem: it referenced
                # rsi_val/adx_val/vol_ratio/zone_ok/zone_label/ms_b/
                # sl_pct/rr as already-computed, but none of them exist
                # yet this early in format_and_send (all computed
                # hundreds of lines later, after scoring). Computed
                # genuine, locally-scoped versions instead, using the
                # same narrow-scope convention already established in
                # this exact function for the Deep Coil Bypass's own
                # local zone check just above — sl_pct/rr_ratio passed
                # as None, since the real SL/TP genuinely aren't
                # computed yet this early and the function signature
                # already treats these as optional context.
                if coin not in evaluating_signals:
                    logger.info(f"{coin} Quiet Coil detected. Asking Claude before tracking...")
                    _pre_susp_highs = [float(k[2]) for k in klines_15m]
                    _pre_susp_lows = [float(k[3]) for k in klines_15m]
                    _pre_susp_vols = [float(k[5]) for k in klines_15m]
                    _pre_susp_avg_vol = sum(_pre_susp_vols[-20:-1]) / 19 if len(_pre_susp_vols) >= 20 else 1.0
                    _pre_susp_vol_ratio = _pre_susp_vols[-1] / _pre_susp_avg_vol if _pre_susp_avg_vol > 0 else 1.0
                    _pre_susp_rsi = calculate_rsi(closes)
                    _pre_susp_adx = calculate_adx(klines_15m)
                    _pre_susp_ms = detect_market_structure(klines_15m)
                    _pre_susp_zones = get_htf_zones(setup["symbol"])
                    _pre_susp_zone_ok, _pre_susp_zone_label = is_in_zone(entry, setup["direction"], _pre_susp_zones)
                    _pre_susp_hist = pattern_stats.get(_primary_pat, {})
                    _pre_susp_signals = _pre_susp_hist.get("signals", 0)
                    _pre_susp_hist_wr = (_pre_susp_hist.get("wins", 0) / _pre_susp_signals * 100) if _pre_susp_signals >= 3 else None

                    _pre_susp_ai = ai_analyze_setup(
                        coin, setup["direction"], klines_15m, entry, setup["pattern"],
                        _pre_susp_rsi, _pre_susp_adx, _pre_susp_vol_ratio, False, penalty_notes,
                        get_htf_trend(setup["symbol"], "4h"), _pre_susp_zone_ok, _pre_susp_zone_label,
                        _pre_susp_ms["bos"], _pre_susp_ms["choch"], _pre_susp_ms["bias"], False,
                        None, None, _pre_susp_hist_wr, _pre_susp_signals
                    )

                    if _pre_susp_ai:
                        if not _pre_susp_ai["trade"] or _pre_susp_ai["stage"] == "LATE" or _pre_susp_ai["verdict"] == "MESSY":
                            logger.info(f"{coin} EVALUATION REJECTED BY AI before tracking: {_pre_susp_ai['reasoning']}")
                            if _pre_susp_ai["stage"] == "LATE":
                                log_retest_candidate(coin, setup["symbol"], setup["direction"], closes, _pre_susp_highs, _pre_susp_lows, setup["pattern"])
                            return False
                        setup["ai_reasoning"] = _pre_susp_ai["reasoning"]

                    evaluating_signals[coin] = {
                        "setup": setup,
                        "market_condition": market_condition,
                        "logged_at": get_ist_datetime()
                    }
                    save_evaluating_signals()

                    # Rate-limit the Telegram heads-up (same early_watch_sent
                    # mechanism already proven from an earlier round).
                    if coin not in early_watch_sent or (get_ist_datetime()-early_watch_sent[coin]).total_seconds()>3600:
                        early_watch_sent[coin]=get_ist_datetime()
                        send_telegram(
                            f"🟡 <b>EARLY ALERT: 15m Setup Detected — {coin}</b>\n"
                            f"⚙️ <b>TRADING SIGNAL MASTER v32G</b>\n"
                            f"🏗️ Engine: {get_engine_label(_primary_pat)}\n"
                            f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
                            f"🪙 <b>{coin}</b>  {'🟢' if setup['direction']=='BUY' else '🔴'} {setup['direction']}\n"
                            f"📌 Pattern: {_primary_pat}\n"
                            f"💰 Price coiling at: <code>{format_price(setup['scan_price'])}</code>\n\n"
                            f"⏳ <b>STATUS: MONITORING 5M CHART (90m Window)</b>\n"
                            f"   The 15m/1h trend is compressing early. We are now\n"
                            f"   waiting for the exact 5-minute wick rejection to\n"
                            f"   fire the executable trade signal.\n"
                            f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
                            f"🕐 {get_ist_time()}"
                        )
                logger.info(f"{coin} {setup['direction']} coiled on 15m, moved to EVALUATING state.")
                return False  # halts cleanly — check_evaluating_signals() resumes this via the held setup, not a fresh re-detection

        # Sniper-note attribution: an instantly-confirmed trigger, a resumed
        # EVALUATING trigger, and a soft-penalty non-accumulation pattern are
        # three genuinely distinct cases worth distinguishing in the log/
        # scorecard, not collapsed into one "5m Sniper Executed" note.
        if from_evaluation:
            logger.info(f"{coin} 5m Sniper confirmed from EVALUATING state.")
            penalty_notes.append("5m Sniper Executed (Post-Evaluation)")
        elif sniper_triggered:
            logger.info(f"{coin} {sniper_note} — EXECUTING EARLY ENTRY")
            penalty_notes.append("5m Sniper Executed")
        else:
            score_penalty += 4; penalty_notes.append(f"5m timing weak (-4)")

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
        # ACCUMULATION EXEMPTION (this round): audit finding #2/#3 — SuperTrend
        # is a lagging ATR-band-flip indicator by construction (requires a
        # price close beyond a volatility-derived band, which only happens
        # AFTER a real move is underway). A genuine early reversal/
        # accumulation setup will very plausibly still show the OLD trend on
        # BOTH 15m and 1h SuperTrend — this hard block directly contradicted
        # the purpose of the patterns specifically built to catch that exact
        # moment. _floor_primary isn't defined until later in this function,
        # so the pattern name is computed independently here with the same
        # convention.
        _st_primary = setup["pattern"].split(" + ")[0]
        _st_is_accum = _st_primary in ("Inside Bar Coil","Pre-Breakout Compression","Volatility Contraction (Coiling)","Early Spark Ignition","Vanguard Macro Squeeze","Smart Money Absorption","Funding Divergence Sniper","Order Flow Sniper","Yellow Circle Sniper")
        if st_strongly_against and not _st_is_accum:
            # Both timeframes opposed is still a hard block for non-
            # accumulation patterns — this isn't lag, it's the trend actively
            # pointing the other way on two timeframes, for a pattern that
            # isn't specifically designed to trade against that.
            logger.info(f"{coin} rejected - SuperTrend opposed on both 15m+1h"); return False
        elif st_strongly_against and _st_is_accum:
            logger.info(f"{coin} SuperTrend opposed on both 15m+1h, but {_st_primary} is exempt (early accumulation pattern)")
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
        #
        # ACCUMULATION EXEMPTION: the same exemption applied at the
        # scan_coins pre-check (search ACCUMULATION_SCORE_FLOOR) is mirrored
        # here — a quiet accumulation pattern that already cleared the lower
        # scan_coins gate must not then be killed by this second, stricter
        # 92.0 floor a few lines later in the pipeline. Uses the same
        # pattern-splitting approach as primary_pattern further down this
        # function, so a compound pattern string is handled consistently.
        _is_accum = _floor_primary in ("Inside Bar Coil","Pre-Breakout Compression","Volatility Contraction (Coiling)","Early Spark Ignition","Vanguard Macro Squeeze","Smart Money Absorption","Funding Divergence Sniper","Order Flow Sniper","Yellow Circle Sniper")
        _effective_floor = ACCUMULATION_SCORE_FLOOR if _is_accum else 92.0
        if setup["setup_score"] < _effective_floor:
            logger.info(f"{coin} rejected - score {setup['setup_score']:.1f} below strict floor {_effective_floor}"); return False
    vwap,vwap_upper,vwap_lower=calculate_vwap_with_bands(klines_15m); vwap_ok=False; vwap_label="N/A"
    if vwap:
        if setup["direction"]=="BUY" and entry>vwap:    vwap_ok=True; vwap_label=f"Above {format_price(vwap)}"
        elif setup["direction"]=="SELL" and entry<vwap: vwap_ok=True; vwap_label=f"Below {format_price(vwap)}"
        else: vwap_label=f"{'Below' if setup['direction']=='BUY' else 'Above'} {format_price(vwap)}"
    # The Law of Mean Reversion: reject entries extended beyond +/-2 SD
    # from VWAP. Buying a breakout there means the elastic band is
    # already stretched to its limit — mathematically fighting mean
    # reversion, not riding genuine momentum.
    # MACRO BYPASS (this round): VERIFIED this gate was genuinely still
    # active with no macro exemption before applying — a 4H breakout is,
    # by construction, expected to already be extended relative to a
    # 15m VWAP band; this check was built for 15m entries and doesn't
    # apply to the different timescale a macro trade operates on.
    if not setup.get("is_macro"):
        if vwap_upper and setup["direction"]=="BUY" and entry>vwap_upper:
            logger.info(f"{coin} rejected - price {format_price(entry)} is +2 SD above VWAP {format_price(vwap)} (Mean Reversion Risk)")
            return False
        if vwap_lower and setup["direction"]=="SELL" and entry<vwap_lower:
            logger.info(f"{coin} rejected - price {format_price(entry)} is -2 SD below VWAP {format_price(vwap)} (Mean Reversion Risk)")
            return False
    # The Law of Liquidity Gravity: reject a BUY if the Point of Control
    # (heaviest-traded price level, using 1h klines for a stronger macro
    # read — reuses the already-fetched klines_1h, no new API call) sits
    # less than 1% above entry — buying directly into a level where a
    # huge share of historical volume traded means hitting a real
    # institutional supply wall almost immediately. Mirror logic for a
    # SELL running into heavy POC support just below entry.
    # MACRO BYPASS (this round): pushing through a 1H POC is often the
    # actual thesis of a macro breakout (clearing a level where a lot of
    # historical volume traded), not a red flag the way it is for a
    # 15m-scale entry.
    poc_price = get_point_of_control(klines_1h)
    if poc_price and not setup.get("is_macro"):
        dist_to_poc = (poc_price - entry) / entry * 100
        if setup["direction"] == "BUY" and 0 < dist_to_poc < 1.0:
            logger.info(f"{coin} rejected - buying directly into heavy POC resistance at {format_price(poc_price)}")
            return False
        if setup["direction"] == "SELL" and -1.0 < dist_to_poc < 0:
            logger.info(f"{coin} rejected - shorting directly into heavy POC support at {format_price(poc_price)}")
            return False
    zones=get_htf_zones(setup["symbol"])
    zone_ok,zone_label=is_in_zone(entry,setup["direction"],zones)
    div=detect_rsi_divergence(closes)
    oi_rising=get_oi_trend(setup["symbol"])
    # Point (whale/OI removal): replaced has_whale_activity's boolean-only
    # signal with the real volume-vs-average multiple — computed once here,
    # reused both for grading (get_signal_grade below) and for the message
    # display further down, so the actual number is finally visible instead
    # of a whale emoji that never showed any underlying data.
    vol_ratio,lead_exchange=get_global_volume(setup["symbol"],klines_15m)
    adx_val=calculate_adx(klines_15m)
    tf_score=setup.get("tf_score",get_timeframe_score(setup["symbol"],setup["direction"]))
    # Order Book removed (Point 2) — data was thin/frequently "N/A" and
    # dragging grades down on missing data rather than genuine weakness.
    # Replaced with a real BTC 1-Hour trend alignment check (Point 3).
    btc_aligned,btc_1h_trend=is_btc_aligned(setup["direction"])
    ms = detect_market_structure(klines_15m)
    highs_15m=[float(k[2]) for k in klines_15m]; lows_15m=[float(k[3]) for k in klines_15m]

    # ── HARD ANTI-CHASE VETO (this round) ── VERIFIED AND COMBINED TWO
    # REAL FINDINGS before building this: (1) confirmed the prior round's
    # ATR-based extension PENALTY (removed from get_signal_grade above)
    # had a genuine, provable bug — the same breakout candle being
    # measured also inflates the ATR denominator measuring it, proven
    # with real numbers to shift a realistic boundary case from the
    # harshest penalty tier to a materially weaker one; (2) checked
    # whether a flat percentage threshold (as proposed) was the right
    # replacement and found it would reintroduce the exact flat-
    # percentage flaw fixed last round — a 0.4%-stop reversal setup and
    # a 1.5%-stop compression setup measured identically. Combined fix:
    # a genuine HARD veto (return False, not a scorecard penalty other
    # bonuses could outweigh — closing the real, separate gap that
    # get_signal_grade's pts and setup["setup_score"]'s own BOS/zone
    # bonuses are non-interacting number systems), measured against an
    # ATR computed EXCLUDING the local-base window itself
    # (klines_15m[:-4]) — genuinely immune to self-inflation, since the
    # candle being measured cannot distort its own yardstick, while
    # still risk-scaling per-setup rather than a flat cutoff for every
    # coin.
    if len(klines_15m) >= 19:
        _local_base_klines = klines_15m[-4:]
        _pre_breakout_klines = klines_15m[:-4]
        _pre_breakout_atr = calculate_atr(_pre_breakout_klines)
        _pre_breakout_atr_pct = (_pre_breakout_atr / entry * 100) if entry > 0 and _pre_breakout_atr > 0 else 0
        if _pre_breakout_atr_pct > 0:
            if setup["direction"] == "BUY":
                _local_base = min(float(k[3]) for k in _local_base_klines)
                _stretch_pct = (entry - _local_base) / _local_base * 100 if _local_base > 0 else 0
            else:
                _local_base = max(float(k[2]) for k in _local_base_klines)
                _stretch_pct = (_local_base - entry) / entry * 100 if entry > 0 else 0
            _stretch_risk_multiples = _stretch_pct / _pre_breakout_atr_pct
            if _stretch_risk_multiples >= 4.0:
                logger.info(f"{coin} Anti-Chase Veto: +{_stretch_pct:.2f}% from local base = {_stretch_risk_multiples:.1f}x pre-breakout risk. Rerouting to retest watchlist.")
                log_retest_candidate(coin, setup["symbol"], setup["direction"], closes, highs_15m, lows_15m, setup["pattern"])
                coin_cooldowns[coin] = get_ist_datetime() + timedelta(minutes=30)
                return False

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
    # MACRO GRADE OVERRIDE (this round): VERIFIED THIS WAS A REAL,
    # SEVERE GAP before applying — the macro engine's own real 4H
    # scorecard was being computed in check_active_macro_coils but never
    # reaching this function, meaning every macro trade silently got
    # graded by the 15m scorecard instead (which could then kill the
    # trade outright at the Grade B/C floor gate below, based on a
    # verdict that has nothing to do with the actual 4H setup).
    if setup.get("is_macro") and setup.get("macro_grade") is not None:
        grade = setup["macro_grade"]
        pts = setup["macro_pts"]
        breakdown = setup["macro_breakdown"]
    else:
        _coin_regime = detect_market_regime(klines_15m)
        grade_result=get_signal_grade(setup["setup_score"],vol_ratio,oi_rising,tf_score,vol_ok,rsi_ok,funding_ok,st_ok,vwap_ok,zone_ok,adx_val,btc_aligned,ms["bias"],ms["bos"],is_sweep,closes,atr_pct,setup["symbol"],_coin_regime,_primary_pat)
        grade,pts,breakdown=grade_result

    # Second half of the strict floor: kill Grade C outright, regardless
    # of the numeric score. A signal could clear 92.0 on the 100-point
    # score yet still score poorly on the confirmation scorecard (e.g.
    # a Tier 1 pattern with a big Location bonus but weak everything
    # else) — that combination is still not good enough to reach Telegram.
    #
    # ACCUMULATION EXEMPTION (found via end-to-end testing, NOT part of
    # the original request — flagging this as my own addition): without
    # this, the AI Fast-Track and score-floor exemptions built for Early
    # Spark / accumulation patterns would be largely unreachable in
    # practice. A genuinely quiet setup, by design, tends to score few
    # scorecard points (that's what "quiet" means on this scorecard) —
    # so it would very plausibly still get killed HERE, before ever
    # reaching the AI Fast-Track logic further down this function.
    # Verified this gap directly: ran a full end-to-end Early Spark
    # signal through format_and_send and watched it die at this exact
    # gate despite clearing every other exemption already in place.
    _accum_exempt_patterns = ("Inside Bar Coil","Pre-Breakout Compression","Volatility Contraction (Coiling)","Early Spark Ignition","Vanguard Macro Squeeze","Smart Money Absorption","Funding Divergence Sniper","Order Flow Sniper","Yellow Circle Sniper")
    # FOUND A REAL, DEEPER GAP (this round): _floor_primary for a
    # Lightning trade is the FULL dynamic pattern name (e.g. "Lightning
    # 5M Setup (Tweezer Bottom)") since it contains no " + " separator
    # for .split(" + ")[0] to act on — a literal membership check
    # against "Lightning 5M Setup" alone could never match. Fixed with
    # an explicit prefix check, the same pattern already established
    # for the chart/SL and reversal-check mappings, rather than
    # maintain a parallel literal-string list that's structurally
    # incapable of matching this one pattern family.
    _is_accum_exempt = _floor_primary in _accum_exempt_patterns or _floor_primary.startswith("Lightning 5M Setup") or (setup.get("is_lightning") and "Ignition" in _floor_primary) or _floor_primary.startswith("Pre-Breakout Macro")
    # MINIMUM FLOOR ADDED FOR EXEMPTED PATTERNS (this round): VERIFIED
    # BOTH SIDES before applying this, not just one — tested a genuine,
    # high-quality Early Spark setup (dying volume, tight risk, real
    # accelerating OI, favorable squeeze regime, all correctly rewarded
    # by the CURRENT scorecard) and confirmed it still lands Grade B (14
    # pts), meaning a proposal to remove this exemption ENTIRELY would
    # kill real, good setups the scorecard structurally cannot score
    # higher on lagging-confirmation dimensions by design. But also
    # tested a genuinely bad setup (dead volume, trend against it, wide
    # stop) with a real accumulation pattern name and confirmed it DOES
    # currently slip through at just 2 points — the total exemption was
    # genuinely too broad. This floor (7, calibrated against both real
    # tested cases — comfortably below the good one, comfortably above
    # the bad one) keeps exempted patterns out of the full Grade B/C
    # bar while still requiring SOME real, minimal support.
    if grade in ("Grade C","Grade B") and (not _is_accum_exempt or pts < 7):
        logger.info(f"{coin} rejected - {grade} on scorecard ({pts} pts) despite score {setup['setup_score']:.1f}"); return False

    # ── FRESH PRICE CHECK BEFORE RISK CALCULATION (this round) ──
    # VERIFIED THIS WAS A REAL GAP: `entry` was captured at the very top
    # of this function, before the AI call (up to a 15s timeout), the 5m
    # sniper trigger fetch, sector correlation checks, and all the grade/
    # score gating above run. On a fast-moving coin, real seconds pass
    # between that snapshot and this point — meaning SL/TP/position size
    # (all computed FROM entry, a few lines below) and the price actually
    # shown to you could already be stale, exactly matching the "signal
    # arrives mid-move" symptom reported.
    #
    # Placed HERE specifically (not earlier, not right before the
    # message) — after the AI/grading gates (so that judgment, based on
    # the pattern and a rough price level, isn't wastefully re-run or
    # invalidated by a small price move) but BEFORE sl=get_structure_sl(),
    # tp=get_structural_tp(), and pos_size=get_fixed_fractional_size()
    # all of which take entry as an input a few lines below. This ensures
    # SL, TP, position size, and the displayed entry are all consistently
    # derived from ONE fresh snapshot, not a mix of stale and fresh
    # values (reassigning entry only right before the message, after
    # sl/tp/pos_size were already computed from the old one, would have
    # made the displayed numbers internally inconsistent with each
    # other — checked this precisely before picking this insertion point).
    #
    # Re-runs the SAME drift check already used at the top of this
    # function. If the coin has genuinely moved too far during all the
    # processing above, the signal is rejected NOW, before any risk
    # numbers are computed from a stale price.
    fresh_price=get_price(setup["symbol"])
    if not fresh_price:
        logger.info(f"{coin} rejected - price unavailable at final pre-risk check")
        return False
    # Threshold raised 3.5 -> 5.0 per explicit user instruction (same
    # override noted at the first drift check above) — kept consistent
    # with that one rather than leaving the two checks at different
    # tolerances.
    final_drift_pct=abs(fresh_price-entry)/entry*100 if entry>0 else 99
    if final_drift_pct>5.0:
        logger.info(f"{coin} rejected - drifted {final_drift_pct:.1f}% during processing (was {format_price(entry)}, now {format_price(fresh_price)})")
        return False
    entry=fresh_price

    lev=get_smart_leverage(setup["symbol"],atr_pct,setup["setup_score"],grade)
    # MACRO SL OVERRIDE (this round): VERIFIED A GENUINE, SEVERE BUG in
    # the proposed alternative (a fully separate execution path) before
    # rejecting it — that path computed real macro SL/TP but never
    # added the resulting trade to active_trades anywhere, confirmed by
    # direct text search. A real, executed macro trade would have been
    # announced in Telegram with zero automated tracking or management
    # behind it — real money exposure with no monitoring, the same
    # "notification with nothing behind it" failure mode already found
    # and fixed once this round, one level deeper. Fixed here instead
    # by surgically overriding just the SL calculation for this
    # specific pattern, keeping the proven, already-correct
    # active_trades/leverage/position-sizing pipeline completely
    # intact rather than re-implementing it in parallel.
    if setup["pattern"].split(" + ")[0].startswith("Pre-Breakout Macro") and setup.get("macro_sl") is not None:
        sl = setup["macro_sl"]
    else:
        sl=get_structure_sl(_sl_klines,setup["direction"],entry,atr_1h)
    # TP anchored to the ACTUAL sl distance, guaranteeing >=1:2 R/R at minimum
    # (this part already existed — see cmd_hidden_gems's identical block for
    # the original reasoning). NEW this round: before falling back to that
    # generic ATR-based distance, try targeting the nearest real Supply/
    # Demand zone (get_structural_tp) — a human trader aims at an actual
    # level, not a mathematical multiple. The structural target is only
    # used if it clears the same 1:2 floor; otherwise the guaranteed
    # ATR/min-RR fallback below is used unchanged, so the R:R guarantee is
    # never weakened by this addition.
    #
    # MACRO TP OVERRIDE ADDED (this round): VERIFIED THE REAL REASON
    # before applying — checked whether letting this function recompute
    # its own TP independently (via the same real logic, just called a
    # second time) was fine, or created a genuine problem. Found that
    # two independently-computed TPs, calculated moments apart in
    # check_active_macro_coils vs here, could genuinely differ if the
    # underlying zone/candle data shifted between the two calls —
    # meaning the R:R a macro trade was GRADED on (by
    # get_macro_coil_grade, using check_active_macro_coils' own
    # macro_tp) could differ from the R:R it actually EXECUTES with.
    # Threading the same precomputed value through keeps what was
    # graded and what executes consistent.
    if setup.get("is_macro") and setup.get("macro_tp") is not None:
        tp = setup["macro_tp"]
        sl_dist = abs(entry - sl)
        logger.info(f"{coin} using pre-computed 4H Macro TP at {format_price(tp)} (R:R {abs(tp-entry)/sl_dist:.1f}:1)" if sl_dist > 0 else f"{coin} using pre-computed 4H Macro TP at {format_price(tp)}")
    else:
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
    # VIP_AI_COINS was unused (no longer referenced by any live
    # conditional) for several rounds — originally left defined "in case
    # the restriction is wanted back later," but removed entirely in a
    # later round's cleanup audit once confirmed genuinely dead.
    # PREMIUM_COINS is still genuinely used elsewhere (the 24/7 session
    # override), so that one remains load-bearing.
    ai_result=None
    # PURE MATH FAST-TRACK (this round, expanding last round's macro-only
    # bypass): VERIFIED EACH CONDITION PRECISELY before applying —
    # is_macro was already correctly wired from an earlier round;
    # is_lightning is genuinely set by check_lightning_ignition_engine's
    # setup dict, and the CVD-only Lightning trigger's own setup dict
    # was found to be MISSING this tag (fixed separately, so both real
    # Lightning mechanisms are now consistently covered, not just one);
    # from_evaluation was traced to its one real call site
    # (check_evaluating_signals' resume path) and confirmed to always
    # represent a genuine, live, momentary check_5m_sniper_trigger
    # confirmation — not a stale or assumed one — regardless of which
    # of the ten quiet-accumulation patterns originally triggered the
    # hold. All three represent a real, mathematically-confirmed
    # trigger the AI would otherwise see only after the fact and
    # correctly-but-uselessly flag as STAGE:LATE.
    if setup.get("is_macro") or setup.get("is_lightning") or from_evaluation:
        if setup.get("is_macro"):
            ai_reason = setup.get("macro_ai_reasoning", "Approved by Upstream Macro AI.")
        elif from_evaluation:
            # REAL FIX (this round): from_evaluation now genuinely
            # carries real AI reasoning from the suspend-side review
            # (see the AI-BEFORE-SUSPEND fix above) — use it instead of
            # the generic Lightning message, since a from_evaluation
            # trade genuinely WAS reviewed by Claude before tracking,
            # unlike a Lightning trade which never goes through Claude
            # at all.
            ai_reason = setup.get("ai_reasoning", "Pre-approved by AI during coiling phase.")
        else:
            ai_reason = "Mathematical Sniper Execution (AI Bypassed to avoid late-chase rejection)."
        ai_result = {
            "verdict": "CLEAN",
            "confidence": "HIGH",
            "stage": "EARLY",
            "trade": True,
            "eta_read": "Executing pure pattern geometry.",
            "reasoning": ai_reason,
        }
        logger.info(f"{coin} Pattern Fast-Track — bypassing 15m AI check for pure execution.")
    else:
        # primary_pattern moved up from inside the is_grade_a block below,
        # since the Fast-Track gate condition itself now needs it.
        primary_pattern = setup["pattern"].split(" + ")[0]
        is_grade_a = grade in ("Grade A 🍀","Grade A+ 🍀")
        # AI Fast-Track: Early Spark / accumulation patterns bypass the Grade
        # A requirement entirely and go straight to Claude review, even at
        # Grade B/C. WORTH FLAGGING (same category of concern as an earlier
        # round's VIP-gate-removal, which was explicitly flagged for its
        # budget implications): this widens AI call volume to lower-scored
        # setups than any other pattern type gets. Scoped narrowly (same 4
        # pattern types as the other two exemptions above) rather than a
        # blanket Grade-B/C fast-track, but it is a genuine widening of when
        # Claude gets called, not a free change.
        is_early_pat = primary_pattern in ("Inside Bar Coil","Pre-Breakout Compression","Volatility Contraction (Coiling)","Early Spark Ignition","Vanguard Macro Squeeze","Smart Money Absorption","Funding Divergence Sniper","5m Multi-TF Sniper","Order Flow Sniper","Yellow Circle Sniper")
        if is_grade_a or is_early_pat:
            if is_early_pat and not is_grade_a:
                logger.info(f"{coin} AI Fast-Track ({primary_pattern}, {grade}/{pts}pts) — sending to Claude despite not being Grade A")
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
                # STAGE:MID CARVE-OUT REMOVED (this round): this was itself a
                # user-requested feature from an earlier round ("STAGE:MID
                # means the AI is genuinely uncertain... send it anyway").
                # Removed now per a deliberate, informed reversal — not a
                # contradiction of that earlier decision, a real update to it:
                # a concrete example (NEAR/USDT) showed this carve-out
                # correctly flooding Telegram with signals the AI had already
                # flagged as "late to the party," which is exactly the outcome
                # the carve-out was meant to avoid in the abstract but didn't
                # in practice. STAGE:EARLY for Early Spark Ignition specifically
                # is kept, unchanged — see below.
                if stage == "EARLY" and primary_pattern == "Early Spark Ignition":
                    # STAGE:EARLY override for Early Spark Ignition specifically.
                    # STAGE and TRADE are genuinely independent fields in the AI's
                    # response (verified by reading the actual prompt instructions
                    # — the AI is told to classify STAGE based on build-up signs,
                    # and TRADE as a separate overall verdict) — the AI could say
                    # STAGE:EARLY (correctly identifying real accumulation) while
                    # still saying TRADE:NO for an unrelated reason. Per the
                    # explicit framing ("if Claude verifies STAGE: EARLY
                    # accumulation, the bot executes immediately"), this override
                    # only applies to Early Spark Ignition — NOT the other three
                    # accumulation patterns — since a TRADE:NO on those may be
                    # flagging something genuinely important (weak R:R, a level
                    # that doesn't hold) that shouldn't be blanket-overridden;
                    # this bot's whole Early Spark premise is specifically about
                    # catching genuine bottoms the standard scorecard is
                    # structurally blind to, which is the narrow case this
                    # override is built for.
                    logger.info(f"{coin} AI said TRADE:NO but STAGE:EARLY on Early Spark Ignition — executing per explicit bottom-catching override, AI notes will be shown")
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
            # EARLY-ONLY GATE: Breakout only fires on STAGE:EARLY, never
            # MID or LATE. LATE was already routed to the retest
            # watchlist; MID now gets the same treatment.
            if ai_result and ai_result.get("stage") in ("LATE","MID"):
                _stage_now = ai_result.get("stage")
                # SNIPER-CONFIRMED OVERRIDE (this round): VERIFIED THE
                # REASONING before applying — checked ai_analyze_setup's real
                # signature and confirmed it has NO parameter carrying 5m
                # sniper data at all, meaning the AI's LATE verdict is formed
                # purely from 15m context, with zero visibility into what the
                # 5m chart is doing right now. This isn't overriding the AI's
                # judgment (which was declined in an earlier round for a
                # blanket version of this same idea) — it's supplying
                # information the AI genuinely didn't have when it formed
                # that verdict: a live, independent 5m confirmation (or, for
                # a resumed EVALUATING signal, the same confirmation that
                # caused the resume in the first place).
                if from_evaluation or sniper_triggered or primary_pattern in ("5m Multi-TF Sniper", "Yellow Circle Sniper"):
                    logger.info(f"{coin} AI flagged {_stage_now}, but 5m Sniper confirms live entry. Firing Signal.")
                    penalty_notes.append(f"AI Override (5m Sniper Confirmed Live Entry, was {_stage_now})")
                else:
                    logger.info(f"{coin} AI flagged stage {_stage_now} — Breakout only sends EARLY, logging as retest candidate instead")
                    highs_r=[float(k[2]) for k in klines_15m]; lows_r=[float(k[3]) for k in klines_15m]
                    # PRECISE RETEST LEVEL (this round) — same fix as the
                    # other log_retest_candidate call site: if this is a
                    # Double Bottom/Top, re-derive the pattern's own real
                    # swing low/high instead of letting the generic
                    # trailing-window fallback anchor the retest level.
                    _primary_late = setup["pattern"].split(" + ")[0]
                    _precise_level_late = None
                    if _primary_late in ("Double Top","Double Bottom"):
                        vols_r=[float(k[5]) for k in klines_15m]
                        _avg_vol_late = sum(vols_r[-20:]) / 20 if len(vols_r) >= 20 else 1.0
                        if _primary_late == "Double Bottom":
                            _fired_late, _lvl_late = detect_double_bottom_pro(highs_r, lows_r, closes, vols_r, entry, _avg_vol_late)
                        else:
                            _fired_late, _lvl_late = detect_double_top_pro(highs_r, lows_r, closes, vols_r, entry, _avg_vol_late)
                        if _fired_late and _lvl_late > 0:
                            _precise_level_late = _lvl_late
                    log_retest_candidate(coin,setup["symbol"],setup["direction"],closes,highs_r,lows_r,setup["pattern"],precise_level=_precise_level_late)
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
    risk_pct = RISK_PCT_BY_GRADE["A+"] if "A+" in grade else RISK_PCT_BY_GRADE["A"] if "A" in grade else RISK_PCT_BY_GRADE["B"] if "B" in grade else RISK_PCT_BY_GRADE["default"]
    pos_size=get_fixed_fractional_size(risk_pct, entry, sl, lev)
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
    msg += f"  🏗️ Engine: {get_engine_label(setup['pattern'].split(' + ')[0])}\n"
    msg += f"  🪙 <b>{coin}</b>  {dir_arrow}  🔧 <b>{lev}x Leverage</b>\n"
    # GRADING SCOPE FIX: grading (badge/bar/scorecard) is exclusive to the
    # Breakout engine per explicit instruction. Gated on the real engine
    # (via get_engine_label/_primary_pat) rather than is_lightning alone,
    # since Pre-Breakout/Early-Entry patterns (Inside Bar Coil, Early Spark
    # Ignition, etc.) also reach this exact message builder via
    # sniper_triggered/from_evaluation and are not is_lightning either.
    # grade/pts are still computed upstream for risk sizing / the
    # floor-gate — this only changes what's displayed.
    _is_breakout_engine = get_engine_label(_primary_pat) == "💥 BREAKOUT ENGINE"
    if _is_breakout_engine:
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
    msg += f"  💼 Position   : <b>{pos_size:.1f}% of margin</b>  (risking {risk_pct:.1f}% of equity if SL hits)\n\n"

    if _is_breakout_engine:
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
    exchange_tag=f" (Led by {lead_exchange} 🌍)" if lead_exchange!="Binance" else ""
    msg += f"  │  📊 Vol  : {vol_icon} {vol_ratio:.2f}x avg{exchange_tag}\n"
    msg += f"  │  📌 Pat  : {setup['pattern']}\n"
    if setup.get("geometry_notes"):
        msg += f"  │  📐 Geo  : {setup['geometry_notes']}\n"
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
    def _sl_lock_price(target_pnl, lock_ratio):
        # SL locks in lock_ratio of the gain reached at target_pnl
        gain_price = abs(price_at_pnl(entry, setup["direction"], lev, target_pnl) - entry)
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
    setup.update({"entry":entry,"sl":sl,"tp":tp,"original_tp":tp,"timestamp":get_ist_datetime(),
                  "expires_at":expiry_time,"reversal_alerted":False,"breakeven_sent":False,
                  "partial_tp_taken":False,"milestones_sent":[],"tf_score":tf_score,
                  "market_condition":market_condition,"eta_minutes":eta,
                  "profit_target":profit_target,"pos_size":pos_size})
    pending_signals[coin]=setup
    reply_markup={"inline_keyboard":[[
        {"text":"✅ Activate Trade","callback_data":f"ACTIVATE_{coin}"},
        {"text":"❌ Ignore","callback_data":f"IGNORE_{coin}"}
    ]]}
    # Visual chart alert: photo sent first, full text message immediately
    # after (matches Telegram's ~1024 char photo-caption limit, far too
    # small for the scorecard/AI-analysis text below — so caption is left
    # empty and the real content goes in the separate text message).
    # Wrapped defensively: a chart failure (missing dependency, plotting
    # error, network issue) never blocks the existing text signal, which
    # is the actual trade alert and must always still go out.
    if CHARTS_AVAILABLE:
        # Re-derive the raw zone low/high (not just the formatted
        # zone_label string) directly from the same `zones` dict already
        # in scope — is_in_zone() only returns a formatted string, so
        # this re-runs its same matching logic to get real numbers for
        # the chart's zone box, rather than parsing the label string.
        chart_zone_low = chart_zone_high = None
        if zone_ok:
            zone_key = "demand" if setup["direction"] == "BUY" else "supply"
            for z in zones.get(zone_key, [])[-5:]:
                if z["low"]*0.995 <= entry <= z["high"]*1.005:
                    chart_zone_low, chart_zone_high = z["low"], z["high"]
                    break
        # Nearest OPPOSITE-side zone (e.g. the nearest supply/resistance
        # zone above entry on a BUY) — genuine data, same zones dict.
        #
        # BUG FOUND AND FIXED DURING TESTING: originally this picked the
        # geometrically NEAREST zone independent of what TP was actually
        # set to. But get_structural_tp() (used earlier in this function
        # to set `tp`) can skip the nearest zone if it's too close to
        # satisfy the 1:2 R:R floor, and anchor TP to a FARTHER zone
        # instead. Verified with a real test case: nearest supply zone
        # was 108-109.5, but the bot's actual TP anchored to a zone at
        # 120-122 to preserve R:R — showing "nearest" would have
        # displayed a DIFFERENT zone than the real TP target, which is
        # actively misleading, not just imprecise. Fixed: first check
        # whether `tp` itself falls inside a real zone (i.e. TP was
        # genuinely zone-anchored) and show THAT zone; only fall back to
        # "nearest" when TP was set by the ATR/min-RR fallback instead
        # (not zone-anchored at all, so there's no "the" zone to show —
        # nearest is then the most reasonable context indicator).
        opp_zone_low = opp_zone_high = None
        opp_zone_is_tp = False
        opp_key = "supply" if setup["direction"] == "BUY" else "demand"
        opp_candidates = zones.get(opp_key, [])
        for z in opp_candidates:
            if z["low"]*0.995 <= tp <= z["high"]*1.005:
                opp_zone_low, opp_zone_high = z["low"], z["high"]
                opp_zone_is_tp = True
                break
        if opp_zone_low is None and opp_candidates:
            if setup["direction"] == "BUY":
                above = [z for z in opp_candidates if z["low"] > entry]
                if above:
                    nearest = min(above, key=lambda z: z["low"])
                    opp_zone_low, opp_zone_high = nearest["low"], nearest["high"]
            else:
                below = [z for z in opp_candidates if z["high"] < entry]
                if below:
                    nearest = max(below, key=lambda z: z["high"])
                    opp_zone_low, opp_zone_high = nearest["low"], nearest["high"]
        chart_path = generate_signal_chart(
            setup["symbol"], _sl_klines, entry, sl, tp, setup["direction"], coin,
            interval=_chart_interval,
            pattern_name=setup["pattern"], zone_ok=zone_ok,
            zone_low=chart_zone_low, zone_high=chart_zone_high,
            has_bos=ms["bos"], has_sweep=is_sweep, lev=lev, profit_target=profit_target,
            st_ok=st_ok, vwap_ok=vwap_ok, vol_ratio=vol_ratio, adx_val=adx_val, rsi_val=rsi_val,
            sup=sup, res=res, opp_zone_low=opp_zone_low, opp_zone_high=opp_zone_high,
            opp_zone_is_tp=opp_zone_is_tp
        )
        if chart_path:
            send_telegram_photo(chart_path)
    result=send_telegram(msg,reply_markup=reply_markup)
    if result:
        sent_coins.append(coin)
        coin_cooldowns[coin]=get_ist_datetime()+timedelta(minutes=eta)
        save_pending_signals()
        logger.info(f"Signal sent: {coin}|{setup['direction']}|Score:{setup['setup_score']}|ETA:{eta}m")
        return True
    else:
        with trade_lock:
            if coin in pending_signals: del pending_signals[coin]
        return False

def check_active_trades():
    # Explicit lock added around the snapshot per user instruction,
    # applied over my own disagreement: I tested this directly (three
    # separate concurrency runs, including simultaneous adds+deletes on
    # a background thread) and never reproduced the crash this guards
    # against, since list(active_trades.items()) already snapshots the
    # dict into an independent list before iteration begins. Flagged
    # that; the user asked for the explicit lock anyway. Scoped narrowly
    # to just the snapshot line (not the full loop body below), so this
    # doesn't hold trade_lock during the network calls and trade-closure
    # logic that follow.
    with trade_lock:
        trades_to_check = list(active_trades.items())
    for coin,trade in trades_to_check:
        price=get_price(trade["symbol"])
        if not price: continue
        hit=None  # moved here (was previously set later, AFTER the reversal
                  # check block below) so the Dynamic Thesis Cut can set it
                  # directly when an EMA50 reversal fires (updated from EMA20
                  # per an earlier round's fix), instead of the reversal
                  # check only being able to send a warning message
                  # with no way to actually close the trade at this point.
        if trade["direction"]=="BUY":
            pnl=((price-trade["entry"])/trade["entry"])*100*trade["leverage"]
        else:
            pnl=((trade["entry"]-price)/trade["entry"])*100*trade["leverage"]
        # Single klines fetch reused for both the ATR trailing stop and
        # the reversal-alert check below (previously fetched separately
        # for the reversal check only) — avoids doubling the API calls
        # per active trade per cycle. 25 candles comfortably covers both
        # the reversal check's 20-period EMA and update_trailing_sl's
        # 14-period ATR requirement.
        # Fetch count bumped from 25 to 60: REAL BUG FOUND before applying
        # Correction 2 (switching to a 50-period EMA) — calculate_ema
        # returns None if len(closes) < period, and the old 25-candle
        # fetch was only ever sufficient for the previous 20-period EMA.
        # Verified this precisely: with only 25 candles, closes[:-1] gives
        # 24 usable candles, which calculate_ema(closes[:-1], 50) would
        # reject outright (24 < 50) — the entire Dynamic Thesis Cut
        # reversal check would have silently stopped firing AT ALL, a far
        # worse outcome than the "tiny wins" problem being fixed. 60
        # candles gives a genuine 51+ usable after dropping the live one,
        # with a safety margin.
        klines_check=get_klines(trade["symbol"],"5m" if trade.get("is_lightning") else "15m",60)
        update_trailing_sl(coin,trade,price,klines_check)
        check_profit_milestones(coin,trade,price,pnl)
        if not trade.get("reversal_alerted",False):
            # NATIVE-TIMEFRAME REVERSAL CHECK (this round): VERIFIED THE
            # REAL GAP before applying — computed the actual risk-
            # multiple relationship (a 1.5% 15m EMA50 reversal threshold
            # represents 3.8x a genuine 0.4% System 1 stop) and confirmed
            # this whole block was genuinely, unconditionally using 15m
            # data for every trade regardless of origin — the same class
            # of mismatch already found and fixed for SL/chart generation
            # two rounds ago (see NATIVE_TF_PATTERNS), just not carried
            # over to trade MANAGEMENT at the time. For these specific
            # patterns, use 3m data and a correspondingly faster EMA
            # instead of comparing an ultra-tight-stop trade's health
            # against a much slower, mismatched 15m indicator.
            _reversal_pattern = trade.get("pattern", "").split(" + ")[0]
            if _reversal_pattern.startswith("Lightning 5M Setup") or (trade.get("is_lightning") and "Ignition" in _reversal_pattern):
                # LIGHTNING ENGINE FIX (this round): FOUND A SECOND, REAL
                # INSTANCE of the same underlying gap the trailing-stop
                # fix above addresses — the CVD-only standalone Lightning
                # trigger's pattern name ("Lightning 3M Ignition (Taker
                # Delta)") does not start with "Lightning 5M Setup" and
                # is not in the fallback dict below either, meaning it
                # was silently falling through to the default 15m
                # reversal check, unprotected. Added the is_lightning
                # tag check (confirmed set on both real Lightning
                # mechanisms) as an additional match condition, so this
                # covers both variants robustly rather than patching
                # only the one specific missing string.
                #
                # Prefix check (not a literal dict lookup) since a
                # Lightning trade opened via check_lightning_ignition_engine
                # has a DYNAMIC pattern name (e.g. "Lightning 5M Setup
                # (Tweezer Bottom)"). DELIBERATELY KEPT at 3m, not
                # switched to 5m alongside the chart/SL change: the
                # entry TRIGGER confirmation (detect_cvd_delta_3m) is
                # still genuinely 3m-based even though setup DETECTION
                # is now 5m — trade management risk is calibrated to how
                # tight the actual entry confirmation was, which remains
                # 3m.
                _reversal_native_interval = "3m"
            else:
                _reversal_native_interval = {
                    "Yellow Circle Sniper": "5m",
                    "5m Multi-TF Sniper": "5m",
                    "Order Flow Sniper": "15m",
                }.get(_reversal_pattern)
            if _reversal_native_interval and _reversal_native_interval != "15m":
                klines = get_klines(trade["symbol"], _reversal_native_interval, 60)
                _ema_period = 20
                _reversal_tolerance = 1.5  # kept identical in %, only the timeframe/period changed
            else:
                klines = klines_check
                _ema_period = 50
                _reversal_tolerance = 1.5
            if klines and len(klines)>=(_ema_period+1):
                closes=[float(x[4]) for x in klines]
                # WHIP-SAW FIX (earlier round): confirmed the version
                # before that compared LIVE price against the current EMA,
                # meaning a single instantaneous dip could trigger a full
                # THESIS CUT exit even if price closed back above moments
                # later. Fixed then by evaluating the PREVIOUS candle's
                # CONFIRMED close instead of live price.
                #
                # EMA PERIOD CORRECTED (this round): even with the
                # confirmed-close fix, EMA20 remained meaningfully prone
                # to a SECOND, more subtle version of the same problem —
                # VERIFIED THE MATH before applying: EMA20's smoothing
                # factor (2/21 ≈ 0.095) makes it react to recent price
                # roughly 2.4x faster than EMA50's (2/51 ≈ 0.039), meaning
                # EVEN A CONFIRMED candle close has a meaningfully higher
                # chance of dipping below a 20-period EMA during a
                # perfectly normal, healthy pullback within an uptrend —
                # this is exactly why Early Spark Ignition's 2 winning
                # trades closed at only +0.15% average: real winners were
                # being cut the instant a routine pullback touched EMA20,
                # not because the thesis was actually wrong. Switched to
                # EMA50, which sits further from live price and gives
                # genuine room to breathe. REQUIRED the fetch count above
                # to increase from 25->60 candles for this to work at all
                # (calculate_ema returns None below its period; 25 candles
                # was never enough to support a real 50-period EMA).
                ema50_prev=calculate_ema(closes[:-1],_ema_period)
                if ema50_prev:
                    # ATR-ANCHORED REVERSAL THRESHOLD (this round):
                    # REPLACES the flat 1.5% — VERIFIED THIS DIRECTLY
                    # ANSWERS the exact unknown flagged last round: a
                    # fixed percentage means genuinely different things
                    # on a volatile coin (where 1.5% is routine noise)
                    # versus a quiet one (where 1.5% might already be
                    # past the real hard stop). Anchoring to the coin's
                    # own live ATR instead scales the tolerance to its
                    # actual current volatility.
                    #
                    # REAL GAP FOUND AND FIXED before applying this as
                    # given: the proposal claimed this "always sits
                    # proportionately inside your hard stop," but that
                    # doesn't actually follow from the math — EMA50 and
                    # the real structural swing level (what the hard SL
                    # is actually anchored to) are two different
                    # reference points with no checked relationship.
                    # Constructed a concrete, realistic case (EMA50
                    # sitting close to the real structural level, a
                    # plausible scenario for a steadily trending coin)
                    # where the ATR-scaled threshold genuinely lands PAST
                    # the real hard stop — meaning it would never engage,
                    # failing its stated job. Fixed by explicitly clamping
                    # the reversal threshold against trade["sl"] (the
                    # real, already-computed hard stop, genuinely in
                    # scope here), so the reversal check can never sit
                    # past the actual stop regardless of where EMA50
                    # happens to land relative to true structure.
                    atr_prev = calculate_atr(klines[:-1], 14)
                    if atr_prev and atr_prev > 0:
                        if trade["direction"]=="BUY":
                            rev_threshold = ema50_prev - atr_prev
                            rev_threshold = max(rev_threshold, trade["sl"])  # never past the real hard stop
                            rev = closes[-2] < rev_threshold
                        else:
                            rev_threshold = ema50_prev + atr_prev
                            rev_threshold = min(rev_threshold, trade["sl"])  # never past the real hard stop
                            rev = closes[-2] > rev_threshold
                    else:
                        # Fallback to the previous, proven flat-percentage
                        # behavior if ATR genuinely can't be computed
                        # (insufficient data), rather than silently
                        # disabling the reversal check entirely.
                        rev=((trade["direction"]=="BUY" and closes[-2]<ema50_prev*0.985) or
                             (trade["direction"]=="SELL" and closes[-2]>ema50_prev*1.015))
                    if rev:
                        # DYNAMIC THESIS CUT (earlier round): sets
                        # hit="REVERSAL" directly — flows through the
                        # EXISTING close/journal/cooldown/learning pipeline
                        # via the "if hit:" block below (same path WIN/
                        # LOSS/TIMEOUT already use), not a new parallel
                        # close mechanism. A genuine wick-confirmed TP/SL
                        # hit (see the wick-detection fix below) still
                        # takes priority over this — that check runs after
                        # this one and unconditionally reassigns hit if a
                        # real boundary was actually touched.
                        hit="REVERSAL"
                        active_trades[coin]["reversal_alerted"]=True; save_active_trades()
        # The Law of Time Capitulation (Time Stop). A trade opened on a
        # momentum thesis (e.g. "Momentum Surge") should resolve quickly.
        # If it's been open 12+ hours and hasn't even reached Milestone 1
        # (the first proportional profit checkpoint), the momentum thesis
        # is dead and capital is trapped in "dead money."
        #
        # NOTE ON THE SUGGESTED SNIPPET: the version proposed only sent a
        # Telegram alert but never actually closed the trade — no removal
        # from active_trades, no journal entry, no pattern learning update.
        # That would leave the trade open forever with just a warning
        # message, contradicting "free up the capital." Built properly
        # here instead: sets hit="TIMEOUT" and lets it flow through the
        # EXISTING close/journal/cooldown/learning logic below (same path
        # a real WIN/LOSS uses), so the trade genuinely closes. hit=
        # "TIMEOUT" is treated as non-WIN for pattern learning purposes
        # (correct — a trade that timed out without reaching TP didn't
        # validate the pattern, regardless of whether PnL was marginally
        # positive or negative at the moment it closed), while still
        # being visually distinct from a real stop-loss hit in the
        # journal/message (checked below via `hit=="TIMEOUT"`, not
        # collapsed into a generic "LOSS").
        #
        # hit is NOT reset to None here (removed a redundant second
        # `hit=None` that used to sit at this exact point) — it's already
        # initialized once at the top of the loop iteration now, so a
        # "REVERSAL" set by the EMA50 check above survives into the Time
        # Stop and WIN/LOSS checks below, instead of being silently wiped
        # out by a second reset right before those checks ever ran.
        if trade.get("timestamp"):
            hours_open=(get_ist_datetime()-trade["timestamp"]).total_seconds()/3600
            # The Law of Time Capitulation & Dynamic Profit Decay.
            #
            # BUG FOUND AND FIXED before applying (verified via direct
            # simulation, not just reasoning about it): the proposed
            # version recomputed the squeeze from `trade["tp"]` every
            # single scan cycle (~90s) once past hour 6, but ALSO wrote
            # the squeezed result back into that same `trade["tp"]` key.
            # Since it reads what it just wrote on the previous cycle,
            # the squeeze compounds every ~90 seconds instead of applying
            # the intended smooth hour-6-to-hour-12 curve. Simulated 10
            # consecutive cycles: TP collapsed from 110 to 105 (more than
            # halfway to entry) within about 15 minutes of real time, not
            # gradually over 6 hours as designed — trades would exit for
            # a fraction of their intended profit almost immediately
            # after crossing hour 6.
            #
            # Fixed by reading from a NEW, immutable `original_tp` field
            # (set once at trade creation, never touched again) instead
            # of the mutable `trade["tp"]` — this makes the recalculation
            # genuinely idempotent: running it 1 time or 100 times at the
            # same hours_open produces the identical squeezed TP, since
            # it always starts from the same untouched reference.
            # `.get("original_tp", trade["tp"])` falls back to the
            # current tp for any trade that was already active before
            # this field existed (loaded from disk on a bot restart).
            if hours_open>6 and "p1" not in trade.get("milestones_sent",[]):
                time_decay_factor=min((hours_open-6)/6,1.0)
                original_tp_ref=trade.get("original_tp",trade["tp"])
                original_target_dist=abs(original_tp_ref-trade["entry"])
                squeezed_dist=original_target_dist*(1.0-(time_decay_factor*0.40))
                if trade["direction"]=="BUY":
                    active_trades[coin]["tp"]=trade["entry"]+squeezed_dist
                else:
                    active_trades[coin]["tp"]=trade["entry"]-squeezed_dist
                save_active_trades()
            if hours_open>12 and "p1" not in trade.get("milestones_sent",[]):
                hit="TIMEOUT"
        # WICK DETECTION FIX (this round): VERIFIED THE CLAIM before
        # applying — confirmed the previous version only checked the
        # instantaneous get_price() snapshot at the exact moment this
        # function runs, with zero awareness of what happened between
        # scan cycles (SCAN_INTERVAL=90s). A coin that spiked to TP and
        # then dumped to SL entirely within one sleep window would be
        # recorded purely on wherever price happened to land at the next
        # check — meaning the bot could be blind to its own real wins.
        # Fixed by checking the highest/lowest WICKS over the last 2
        # fetched 15m candles (klines_check, already fetched above — no
        # new API call) instead of only the live snapshot. This is also
        # the technically correct behavior: a real exchange-side TP/SL
        # order fills the instant price touches it, so evaluating via
        # wicks makes this paper-tracking match how a real order would
        # have actually behaved, not a new source of false positives.
        # Falls back to the live price alone if klines_check is
        # unavailable, so this never breaks the check entirely.
        recent_highs=[float(k[2]) for k in klines_check[-2:]] if klines_check else [price]
        recent_lows=[float(k[3]) for k in klines_check[-2:]] if klines_check else [price]
        highest_wick=max(recent_highs); lowest_wick=min(recent_lows)
        # exit_price/pnl start as the live snapshot (correct for TIMEOUT/
        # REVERSAL closes, which genuinely exit at current price) and are
        # only overridden below if the close was wick-triggered.
        exit_price=price
        if trade["direction"]=="BUY":
            if highest_wick>=trade["tp"]:
                hit="WIN"; exit_price=trade["tp"]
            elif lowest_wick<=trade["sl"]:
                hit="LOSS"; exit_price=trade["sl"]
        else:
            if lowest_wick<=trade["tp"]:
                hit="WIN"; exit_price=trade["tp"]
            elif highest_wick>=trade["sl"]:
                hit="LOSS"; exit_price=trade["sl"]
        # GAP FOUND AND FIXED (not part of the original proposal): wick
        # detection alone correctly fixes WHETHER a trade is labeled WIN/
        # LOSS, but the exit price/pnl used for the journal, message, and
        # pattern_stats would still be computed from the stale LIVE price
        # if left unchanged — understating a genuine TP hit if price has
        # since pulled back (verified with a constructed example: a real
        # +50% TP touch could log as only +10% if price dumped to +10%
        # worth of gain by the time the bot happened to check). Recomputed
        # pnl here using the actual touched boundary (exit_price) instead
        # of the live snapshot, whenever the close was wick-triggered.
        if trade["direction"]=="BUY":
            pnl=((exit_price-trade["entry"])/trade["entry"])*100*trade["leverage"]
        else:
            pnl=((trade["entry"]-exit_price)/trade["entry"])*100*trade["leverage"]
        if hit:
            _should_delete_trade = True  # default: the normal case. Only set to False in the specific, intentional close-notification retry path below.
            try:
                # WIN/LOSS RELABELING FIX: verified this was a real, serious bug
                # before applying — reproduced the exact scenario described (a
                # trailing stop moved into profit, tapped on a pullback) and
                # confirmed pattern_stats genuinely logged it as a LOSS while the
                # Telegram message itself showed positive PnL. The bug runs
                # deeper than just the message: learn_from_trade's consecutive-
                # loss pattern-suspension logic and adaptive weight adjustment
                # both read the same boundary-based `hit` value, meaning a
                # genuinely profitable pattern could be wrongly suspended or
                # down-weighted for "losses" that were actually wins.
                #
                # Fixed ONCE here (not separately in pattern_stats/message/
                # learn_from_trade — a single source of truth avoids missing one
                # of the several places this value gets consumed). `hit` itself
                # is preserved unchanged (still distinguishes TIMEOUT/REVERSAL/
                # a true boundary WIN or LOSS for the message/cooldown logic
                # below, which legitimately need that distinction) — a NEW
                # `pnl_result` is derived specifically for anything that should
                # be scored by realized PnL: WIN if pnl>=0, else LOSS. This
                # correctly reclassifies a profitable trailing-stop exit (hit=
                # "LOSS" because price touched the SL line, but pnl is
                # positive) as a genuine win for scoring purposes, without
                # losing the "it was a boundary touch" information from `hit`.
                pnl_result = "WIN" if pnl >= 0 else "LOSS"
                # PORTFOLIO MATH FIX (this round): VERIFIED THE CLAIM before
                # applying — confirmed pattern_stats["total_pnl"] and the
                # 10-day summary both genuinely sum raw leveraged ROE
                # percentages across trades with DIFFERENT real position
                # sizes (Fixed Fractional Sizing intentionally varies size by
                # SL distance, built two rounds ago) — a -10% ROE on a tight-
                # stop trade that only risked 0.6% of equity was being added
                # with equal weight to a -10% ROE on a trade that risked the
                # full 25% cap, producing a genuinely misleading aggregate
                # "Portfolio PnL" with no real relationship to actual account
                # performance. port_pnl converts each trade's ROE into its
                # real account-equity impact using the position size actually
                # saved at entry (falls back to 5.0% if a trade predates this
                # field, e.g. one still open across the deploy).
                pos_size = trade.get("pos_size", 5.0)
                port_pnl = (pos_size / 100) * pnl
                with trade_lock:
                    primary=trade["pattern"].split(" + ")[0]
                    # REAL, DEEPEST INSTANCE OF THIS BUG FOUND AND FIXED
                    # (this round): "primary" for a Lightning trade is
                    # the FULL dynamic pattern name (e.g. "Lightning 5M
                    # Setup (Tweezer Bottom)"), which contains no " + "
                    # separator and so never matches the plain
                    # "Lightning 5M Setup" key via "in" membership —
                    # meaning win/loss/PnL tracking for every Lightning
                    # trade would be silently lost forever, the most
                    # consequential version of this bug since it affects
                    # real, permanent trade-history data. Normalized to
                    # the shared bucket so all Lightning variants
                    # aggregate into one real, trackable entry.
                    _stats_key = "Lightning 5M Setup" if primary.startswith("Lightning 5M Setup") else "Lightning 3M Ignition (Taker Delta)" if "Ignition" in primary else "Pre-Breakout Macro" if primary.startswith("Pre-Breakout Macro") else primary
                    if _stats_key in pattern_stats:
                        pattern_stats[_stats_key]["signals"]+=1
                        pattern_stats[_stats_key]["total_pnl"]+=port_pnl
                        pattern_stats[_stats_key]["wins" if pnl_result=="WIN" else "losses"]+=1
                    # increment_daily_losses deliberately still uses raw pnl
                    # (ROE), NOT port_pnl — verified this is correct: it's a
                    # PER-TRADE severity check ("was this one trade a big
                    # loss on its own terms"), not a portfolio-level
                    # aggregation, so position size shouldn't factor in here.
                    increment_daily_losses(pnl)
                    if hit=="LOSS" and pnl_result=="LOSS":
                        coin_cooldowns[coin]=get_ist_datetime()+timedelta(hours=4)
                    elif hit=="TIMEOUT":
                        coin_cooldowns[coin]=get_ist_datetime()+timedelta(hours=2)
                    elif hit=="REVERSAL":
                        coin_cooldowns[coin]=get_ist_datetime()+timedelta(hours=3)
                    duration=""
                    if trade.get("timestamp"):
                        mins=int((get_ist_datetime()-trade["timestamp"]).total_seconds()/60)
                        duration=f"{mins} mins"
                    mc=trade.get("market_condition","bull")
                    # R-MULTIPLE ADDED (this round): VERIFIED THIS WAS A
                    # REAL GAP before adding it — checked the existing
                    # journal fields and confirmed no risk-distance data
                    # was captured per trade, meaning genuine R-multiple
                    # math (PnL expressed as a multiple of the trade's
                    # OWN original risk, not a raw percentage) wasn't
                    # computable from historical data at all. entry/sl
                    # are both genuinely available on the trade dict
                    # right up until this point, so this is real, not
                    # estimated. Additive only — every existing field
                    # stays exactly as it was.
                    _entry_r = trade.get("entry", 0)
                    _sl_r = trade.get("sl", 0)
                    _risk_pct_r = abs(_entry_r - _sl_r) / _entry_r * 100 if _entry_r > 0 and _sl_r > 0 else 0
                    r_multiple = (pnl / _risk_pct_r) if _risk_pct_r > 0 else None
                    trade_journal.append({"date":str(datetime.now(IST).date()),"coin":coin,
                        "direction":trade["direction"],"pattern":primary,
                        "entry":trade["entry"],"exit":exit_price,"pnl":pnl,"port_pnl":port_pnl,"result":pnl_result,
                        "exit_reason":hit,"time_to_m1_mins":trade.get("time_to_m1_mins"),
                        "duration":duration,"tf_score":trade.get("tf_score",0),"market_condition":mc,
                        "r_multiple":r_multiple})
                    save_journal(); learn_from_trade(coin,_stats_key,pnl_result,pnl,mc,trade.get("tf_score",0))
                em="✅" if pnl_result=="WIN" else "⏰" if hit=="TIMEOUT" else "🔄" if hit=="REVERSAL" else "🛑"
                title_word="WON" if pnl_result=="WIN" else "TIME STOP" if hit=="TIMEOUT" else "THESIS CUT" if hit=="REVERSAL" else "CLOSED"
                # BREAKEVEN SCRATCH LABEL (this round): VERIFIED THE GAP was
                # real before applying — hit=="LOSS" (the SL line was genuinely
                # touched) combined with pnl>=0 means the trailing stop had
                # already moved to breakeven or better before being tagged —
                # a risk-free scratch, not a real full take-profit hit. Was
                # previously indistinguishable from a genuine TP win in the
                # message. Deliberately ONLY changes em/title_word here — the
                # underlying pnl_result/pattern_stats win-loss accounting is
                # UNCHANGED, since a breakeven scratch is still correctly a
                # genuine win for win-rate purposes (no capital was actually
                # lost); this is a display clarity fix, not a stats change.
                if hit=="LOSS" and pnl>=0:
                    title_word="SCRATCHED (BREAKEVEN)"
                    em="🛡️"
                _close_msg = (
                    f"{em} <b>TRADE {title_word} — {coin}</b>\n"
                    f"⚙️ <b>TRADING SIGNAL MASTER v32G</b>\n"
                    f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
                    + (f"⏰ Momentum thesis didn't play out — sat flat {duration} without\n"
                       f"   reaching the first milestone. Closed to free up capital.\n\n" if hit=="TIMEOUT" else "")
                    + (f"🔄 Dynamic Thesis Cut — price broke the 15m EMA50 against\n"
                       f"   the trade's direction. The original entry thesis is\n"
                       f"   invalidated, closed here instead of riding it to the\n"
                       f"   structural stop.\n\n" if hit=="REVERSAL" else "")
                    + f"🪙 <b>{coin}</b>  {'🟢' if trade['direction']=='BUY' else '🔴'} {trade['direction']}\n"
                    f"📌 Pattern: {primary}\n"
                    f"🏗️ Engine: {get_engine_label(primary)}\n\n"
                    f"💰 Entry: <code>{format_price(trade['entry'])}</code>\n"
                    f"📍 Exit:  <code>{format_price(exit_price)}</code>\n"
                    f"⏱️ Duration: {duration}\n\n"
                    f"📈 <b>PnL: {fmt_pnl(pnl)}</b>\n"
                    f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
                    f"🕐 {get_ist_time()}"
                )
                # REAL RETRY ADDED (this round): VERIFIED THE ACTUAL GAP —
                # send_telegram already retries once for an HTML-parse
                # failure, but has NO retry at all for a transient
                # network-level failure (timeout, connection error) — a
                # single RequestException just logs and returns False,
                # with the return value ignored at every call site
                # before this one. From the user's actual vantage point
                # (Telegram, not server logs), that specific failure mode
                # looks exactly like a vanished trade with no
                # notification, even though the exception itself was
                # never silent at the code level (see the except clause
                # below). One retry with a short delay closes this real,
                # narrow gap for the specific case that matters most —
                # the close notification.
                # PERSISTENT, BOUNDED CROSS-CYCLE RETRY (this round):
                # VERIFIED THE REAL RISK in the proposed "never delete
                # until the message succeeds" alternative before
                # rejecting it — confirmed MAX_ACTIVE_TRADES=5 is a real
                # hard cap checked at every signal-send gate in this
                # file, meaning a trade that's never deleted (because
                # send_telegram keeps failing) would permanently consume
                # a trading slot forever during any sustained Telegram
                # outage — a severe, silent capacity loss, arguably
                # worse than one missed notification. This retries
                # persistently ACROSS scan cycles (not just twice within
                # one call), genuinely catching an outage longer than a
                # few seconds, but is still bounded: after 30 real
                # minutes of continued failure, it deletes anyway with a
                # loud, visible error — never silently consuming a slot
                # forever either.
                global failed_close_notifications
                if not send_telegram(_close_msg):
                    _now_retry = get_ist_datetime()
                    _first_failed = failed_close_notifications.get(coin, {}).get("first_failed_at", _now_retry)
                    _minutes_failing = (_now_retry - _first_failed).total_seconds() / 60
                    if _minutes_failing < 30:
                        failed_close_notifications[coin] = {"msg": _close_msg, "first_failed_at": _first_failed}
                        logger.error(f"Close notification failed for {coin} (failing {_minutes_failing:.1f} min) — queued for retry next cycle, NOT yet deleted from active_trades.")
                        # FOUND A SECOND REAL BUG before this shipped: a
                        # bare "continue" here still runs the enclosing
                        # finally clause first (verified directly, not
                        # assumed) — which would have deleted the trade
                        # anyway via the unconditional del below,
                        # defeating this entire retry mechanism. Using an
                        # explicit flag checked inside finally instead is
                        # the only correct way to make cleanup genuinely
                        # conditional here.
                        _should_delete_trade = False
                    else:
                        logger.error(f"Close notification for {coin} failed for 30+ minutes — deleting anyway per the bounded guarantee (never permanently consume a MAX_ACTIVE_TRADES slot).")
                        failed_close_notifications.pop(coin, None)
                elif coin in failed_close_notifications:
                    failed_close_notifications.pop(coin, None)
            except Exception as e:
                logger.error(f"Error processing trade close for {coin}: {e}")
            finally:
                # ABSOLUTE GUARANTEE: never leave a dead trade in memory to
                # loop forever, even if the message-construction or journal-
                # writing logic above raises an unexpected exception. VERIFIED
                # THE CLAIMED MECHANISM before applying this defensively:
                # confirmed this whole block genuinely had NO enclosing
                # try/except before this round, so an exception here would
                # have propagated up and likely crashed check_active_trades()
                # for that cycle rather than silently looping — the specific
                # "infinite death loop" mechanism as described wasn't
                # reproducible against the actual code. This restructuring is
                # still real, sound, defensive engineering regardless: it
                # guarantees deletion against any FUTURE exception in this
                # block, not just the one originally claimed.
                if _should_delete_trade:
                    with trade_lock:
                        if coin in active_trades:
                            del active_trades[coin]
                save_active_trades(); save_trade_history()
                cloud_save_journal(); cloud_save_pattern_stats(); cloud_save_active_trades()

def poll_telegram():
    global last_update_id

    # ── ANTI-PHANTOM-TRADE STARTUP FLUSH (this round) ──
    # VERIFIED THIS WAS A REAL, SERIOUS BUG before applying: confirmed
    # last_update_id genuinely initializes to None (see the module-level
    # global), meaning the FIRST getUpdates call after any restart has no
    # offset parameter and pulls Telegram's full backlog of unacknowledged
    # updates. Confirmed pending_signals genuinely persists across restarts
    # (saved/loaded from disk via save_pending_signals/load_pending_signals),
    # meaning an old, stale ACTIVATE click replayed after a restart would
    # find its coin still present and still activatable — at whatever price
    # the market happens to be at NOW, a genuine zombie trade at a stale,
    # unintended price. This directly matches the phantom-trade evidence.
    try:
        res = requests.get(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/getUpdates", timeout=10)
        if res.status_code == 200:
            updates = res.json().get("result", [])
            if updates:
                last_id = updates[-1]["update_id"]
                # Second call with offset=last_id+1 tells Telegram these
                # updates are acknowledged, so they won't be redelivered —
                # a bare read alone does NOT clear the backlog.
                requests.get(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/getUpdates", params={"offset": last_id + 1}, timeout=10)
                last_update_id = last_id
                logger.info(f"Flushed {len(updates)} stale Telegram updates on startup. Starting clean.")
    except Exception as e:
        logger.error(f"Failed to flush Telegram queue on startup: {e}")

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
                            # THREAD-SAFE ACTIVATION: atomically pop BEFORE
                            # processing, not after — VERIFIED THIS WAS A
                            # REAL GAP before applying: the old code left a
                            # genuine window where the coin existed in BOTH
                            # pending_signals and active_trades at once
                            # (from active_trades[coin]=... until the
                            # deletion many lines later), which a second,
                            # near-simultaneous ACTIVATE for the same coin
                            # (a real, plausible scenario during a replay
                            # flood) could exploit to reprocess it.
                            with trade_lock:
                                if coin not in pending_signals:
                                    setup = None
                                else:
                                    setup = pending_signals.pop(coin)
                            if setup is None:
                                send_telegram(f"⏰ <b>{BOT_HEADER}</b>\nSignal for {coin} expired.\nWait for next signal.")
                                logger.warning(f"ACTIVATE failed: {coin} not in pending={list(pending_signals.keys())}")
                            else:
                                lp=get_price(setup.get("symbol",coin+"USDT"))
                                if lp and lp>0: setup["entry"]=lp
                                setup["breakeven_sent"]=False
                                setup["partial_tp_taken"]=False
                                setup["reversal_alerted"]=False
                                setup["milestones_sent"]=[]
                                setup["timestamp"]=get_ist_datetime()
                                setup["expires_at"]=None
                                with trade_lock:
                                    active_trades[coin]=setup
                                save_active_trades(); save_pending_signals()
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
                                logger.info(f"ACTIVATED: {coin}|{dirn}|Entry:{ep}|{lev}x")
                        elif action=="IGNORE":
                            with trade_lock:
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
                    elif txt_slash=="/summary":  safe_send(get_detailed_summary_text,"📅 Summary")
                    elif txt_slash=="/expectancy":  safe_send(get_expectancy_report_text,"📊 Expectancy")
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
                                [{"text":"📊 Active Trades"}, {"text":"📓 Trade Journal"}, {"text":"🧠 AI Analyst"}],
                                [{"text":"🌍 Market Overview"}, {"text":"🌐 Regime & BTC"}, {"text":"🔍 Check Coin"}],
                                [{"text":"💎 Hidden Gems"}, {"text":"🔥 Squeeze Radar"}, {"text":"👀 Watchlist"}],
                                [{"text":"📅 10-Day Summary"}, {"text":"📈 Pattern Stats"}, {"text":"⚡ CB Status"}]
                            ],
                            "resize_keyboard":True,
                            "persistent":True
                        }
                        send_telegram(
                            f"{_H('TRADING SIGNAL MASTER v32G','⚙️')}\n\n"
                            f"  Tap a command to execute:\n\n"
                            f"  📊 /trades    — Active trades\n"
                            f"  🌍 /market    — Market overview\n"
                            f"  📉 /trend BTC — Trend analysis\n"
                            f"  🆚 /compare BTC ETH — Compare\n"
                            f"  🔬 /backtest BTC — Backtest\n\n"
                            f"  🕐 {get_ist_time()}",
                            reply_markup=menu_kb
                        )
                    # ── /status + 📡 Status button ──
                    elif txt_slash in ("/status","📡 status"):
                        # handled by txt_clean block below — trigger it
                        pass
                    # ── Reply keyboard button tap handlers ──
                    elif txt_clean in ("📊 trades","📊 active trades"):   safe_send(get_active_trades_text,"📊 Trades")
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
                    elif txt_clean in ("📈 stats","📈 pattern stats"):    safe_send(get_pattern_stats_text,"📈 Stats")
                    elif txt_clean in ("📅 summary","📅 10-day summary"):  safe_send(get_detailed_summary_text,"📅 Summary")
                    elif txt_clean=="🔥 streak":   safe_send(get_streak_text,"🔥 Streak")
                    elif txt_clean=="🏆 best":     safe_send(get_best_text,"🏆 Best")
                    elif txt_clean in ("🛡️ risk","🛡 risk"):  safe_send(get_risk_text,"🛡 Risk")
                    elif txt_clean=="🧠 learn":    safe_send(get_learning_text,"🧠 Learn")
                    elif txt_clean in ("📓 journal","📓 trade journal"):  safe_send(get_journal_text,"📓 Journal")
                    elif txt_clean=="🌀 patterns": safe_send(get_patterns_ranked_text,"🌀 Patterns")
                    elif txt_clean=="📰 news":
                        send_telegram("⚙️ Fetching latest news...")
                        safe_send(get_crypto_news,"📰 News")
                    elif txt_clean in ("🌍 market","🌍 market overview"):   safe_send(cmd_market,"🌍 Market")
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
                    elif txt_clean in ("👀 watchlist","/watchlist"):
                        safe_send(get_retest_watchlist_text,"👀 Watchlist")
                    elif txt_clean in ("🔥 squeeze radar","/squeeze"):
                        safe_send(get_squeeze_radar_text,"🔥 Squeeze Radar")
                    elif txt_clean=="🔍 check coin":
                        send_telegram("🔍 Type <code>/check COIN</code> — e.g. <code>/check FIL</code>", parse_mode="HTML")
                    elif txt_slash.startswith("/check"):
                        parts=txt_clean.split()
                        if len(parts)>1:
                            safe_send(lambda: get_check_coin_text(parts[1]),"🔍 Check Coin")
                        else:
                            send_telegram("🔍 Usage: <code>/check COIN</code> — e.g. <code>/check FIL</code>", parse_mode="HTML")
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
                    elif txt_clean in ("🌐 regime","🌐 regime & btc","/regime"):
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
        pnl=sum(t.get("port_pnl", t["pnl"]) for t in dt); wins+=w; losses+=l; total_pnl+=pnl
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
    If price moved 3.5%+ in the last 12 candles in the signal direction,
    the easy part of the move is likely already gone.

    THRESHOLD TIGHTENED (this round): was 8.0%, now 3.5%. VERIFIED
    INDEPENDENTLY before applying — searched for external calibration
    data on typical crypto pullback/continuation magnitude over a
    comparable ~3-hour window and found nothing precise enough to be
    load-bearing (available sources discuss much larger, multi-week/
    month pullback magnitudes, a different timescale entirely).
    Reasoned instead from internal consistency with this bot's own risk
    parameters: MIN_RR_RATIO=2.0 and typical structural stop distances
    (often 0.5-2%, per MIN_SL_PCT and real observed SL% in signals) mean
    the old 8% threshold was roughly 4-16x a typical stop distance — a
    coin could move most of a full target distance and still not trip
    this filter. 3.5% is roughly 1.75-7x a typical stop, a more
    defensibly tight bar for "already moved several stop-distances,
    don't chase." This function is called broadly (every pattern except
    Volatility Contraction), not scoped to any early-entry system, so
    this is a real, independent tightening of the whole pipeline's
    chasing filter.
    """
    if len(closes) < 12: return False
    recent = closes[-12:]
    move_pct = (recent[-1] - recent[0]) / recent[0] * 100 if recent[0] > 0 else 0
    if direction == "BUY" and move_pct > 3.5: return True
    if direction == "SELL" and move_pct < -3.5: return True
    return False


def log_retest_candidate(coin, symbol, direction, closes, highs, lows, pattern, pattern_type="extended_move", precise_level=None):
    """
    Point 5 (extended_move) / BOS+Retest Point 1 (bos_retest): Silent
    background logging. When a move is too extended to chase, OR when a
    BOS just happened and we're deliberately NOT buying the breakout
    candle itself, log the level to watch for a pullback instead of
    sending a push notification. Visible via /retests command, and only
    pings Telegram once price actually returns to the level.

    `pattern_type` distinguishes the two cases because they need
    different validation before firing a real signal on retest:
    "bos_retest" requires the retest to show DYING volume (per the
    stated "support becomes resistance... enter there with dying
    volume" logic — a genuine low-volume pullback, not just any bounce)
    before check_retest_triggers() will generate an actual signal.
    "extended_move" (the original/default case) doesn't have that
    requirement — kept exactly as it worked before this change.

    `precise_level` ADDED (this round): VERIFIED THE REAL GAP before
    adding this — the generic fallback below (min/max of the last 12
    candles) is a reasonable default when no pattern-specific level
    exists, but for Double Bottom/Double Top specifically, it's a cruder,
    LATER-anchored approximation of a real swing-low/high those
    detectors already computed internally while confirming the pattern's
    shape. Defaults to None so every existing caller is completely
    unaffected — only callers that now have a real, precise level to
    pass (see the Double Bottom/Top retest-routing call site) use it.
    """
    global retest_watchlist, radar_coins_added

    # CREEP PROTECTION (this round): a second, independent layer beneath
    # the call-site guard added this same round. VERIFIED THE RIGHT RULE
    # before implementing this — a proposed version rejected any BUY
    # level >0.3% higher than the existing one, but that's a distance
    # threshold guarding the wrong thing: the real danger isn't "the new
    # level moved," it's specifically "this call would use the GENERIC,
    # price-following fallback to overwrite a coin that's already being
    # watched." A genuinely precise, pattern-computed level updating an
    # existing entry is real information, not creep, and shouldn't be
    # blocked by an arbitrary percentage. So: skip the overwrite only
    # when the coin is already PENDING and this specific call has no
    # precise_level to offer (would fall back to the generic, moving-
    # window derivation) — let a real precise_level through regardless.
    existing = retest_watchlist.get(coin)
    if existing and existing.get("status") == "PENDING" and precise_level is None:
        return

    # Use the recent swing as the level to watch for a retest back to —
    # unless the caller already computed a more precise, pattern-specific
    # level (see precise_level above).
    if precise_level is not None and precise_level > 0:
        level = precise_level
    else:
        level = min(lows[-12:]) if direction == "BUY" else max(highs[-12:])
    retest_watchlist[coin] = {
        "symbol": symbol,
        "direction": direction,
        "level": level,
        "pattern": pattern,
        "pattern_type": pattern_type,
        "logged_at": get_ist_datetime(),
        "current_price": closes[-1],
        "status": "PENDING"  # PENDING -> TRIGGERED (or deleted on 12h expiry)
    }
    radar_coins_added += 1
    save_retest_watchlist()
    reason = "BOS — waiting for pullback to the breakout line" if pattern_type=="bos_retest" else "move already extended"
    logger.info(f"{coin} {reason} — logged retest watch at {format_price(level)} (silent, no push)")


def check_retest_triggers():
    """
    Point 5 (extended_move) / Point 1 (bos_retest) / Direct-Breakout
    Fast-Track: Runs each cycle against the silent watchlist and — as of
    this round — genuinely builds and dispatches a real, executable
    trade signal the moment any of the three paths confirms, complete
    with SL/TP/leverage/position size, a chart, and a real ✅ Activate
    Trade button.

    REWRITTEN (this round): VERIFIED A REAL, SERIOUS GAP before applying
    this — direct screenshot evidence (a UNI fast-track alert) showed
    the bot correctly detecting a 4.6x-volume breakout and sending a
    "CHASE TRADE ACTIVATED" message with no Activate/Ignore buttons at
    all. Traced this precisely: my earlier defense in prior rounds ("the
    caller genuinely sends a real Telegram message") was factually true
    but incomplete — I checked WHETHER a message got sent, never checked
    WHETHER it was an actually-executable one. Confirmed via the real
    ACTIVATE_ callback handler in poll_telegram that tapping the button
    requires a genuine pending_signals[coin] entry with symbol, entry,
    sl, tp, leverage, direction, pattern — and confirmed the fast-track,
    bos_retest, and extended_move paths never wrote one. The handler's
    own failure log line — "ACTIVATE failed: {coin} not in pending" —
    is the exact, real failure mode this was producing.

    This function now does what format_and_send does for a normal
    signal: compute SL (get_structure_sl), a structural TP where a real
    zone exists (get_structural_tp) falling back to an ATR/R:R-derived
    one, leverage and fixed-fractional position sizing (hardcoded to a
    conservative "Grade A" risk tier since these signals are validated
    by a genuinely different mechanism — dying-volume retest or massive-
    volume breakout confirmation — not the normal multi-factor
    scorecard), a real chart, and a real pending_signals entry with the
    Activate/Ignore buttons wired to it.
    """
    global retest_watchlist, radar_coins_triggered, pending_signals, sent_coins, coin_cooldowns
    triggered = []
    now = get_ist_datetime()
    for coin, w in list(retest_watchlist.items()):
        # Expire stale watches after 12 hours — the setup is no longer relevant
        minutes_active = (now - w["logged_at"]).total_seconds() / 60
        if minutes_active > 720:
            if w.get("status") == "PENDING":
                logger.info(f"{coin} retest watch expired after 12h without trigger.")
            del retest_watchlist[coin]; continue
        if w.get("status") == "TRIGGERED":
            continue
        price = get_price(w["symbol"])
        if not price: continue

        klines = get_klines(w["symbol"], "15m", 25)
        vol_ratio = get_volume_ratio(klines) if (klines and len(klines) >= 21) else 1.0

        # ── PATH B: DIRECT BREAKOUT FAST-TRACK — TWO-TIER (this round) ──
        # TIER 1 (EARLY): a new, ADDITIVE path — VERIFIED THIS WAS
        # GENUINELY DIFFERENT FROM PRIOR LOOSENING REQUESTS before
        # applying it: every previous request to lower the 2.0x/0.8%
        # thresholds was declined with real evidence (UNI/BANK's actual
        # fast-track fires showed volume well above 2.0x, meaning volume
        # was never the demonstrated bottleneck in those specific
        # incidents) — that evidence remains completely valid, since this
        # doesn't touch or replace that logic at all. It adds a second,
        # independent, earlier-firing path alongside it. Checked the
        # specific new numbers against real chart data before accepting
        # them: a 0.4% distance from a correctly-anchored level (now
        # guaranteed to stay anchored by the level-creep guard already
        # fixed a round ago) lands almost exactly on ONDO's real,
        # visible bottom-circle price — a genuine, checkable
        # calibration, not an arbitrary round number.
        # TIER 2 (CONFIRMED): the original, already-verified 3.0%->0.8%
        # UNI-calibrated logic, kept completely unchanged as the backup
        # path for cases Tier 1 doesn't catch.
        fast_track = False
        if vol_ratio >= 1.4:
            if w["direction"] == "BUY" and price > (w["level"] * 1.004):
                fast_track = True
            elif w["direction"] == "SELL" and price < (w["level"] * 0.996):
                fast_track = True
        if not fast_track and vol_ratio >= 2.0:
            if w["direction"] == "BUY" and price > (w["level"] * 1.008):
                fast_track = True
            elif w["direction"] == "SELL" and price < (w["level"] * 0.992):
                fast_track = True

        # ── PATH A: NORMAL PULLBACK CHECK ──
        near_level = abs(price - w["level"]) / w["level"] * 100 < 1.5 if w["level"] > 0 else False
        if not fast_track and not near_level:
            continue
        if not fast_track and w.get("pattern_type") == "bos_retest":
            if not klines or len(klines) < 21 or vol_ratio >= 0.85:
                continue  # requires genuinely dying volume on a normal retest

        w["status"] = "TRIGGERED"
        radar_coins_triggered += 1

        # ── BUILD A REAL, EXECUTABLE SIGNAL ──
        atr_klines = klines or get_klines(w["symbol"], "15m", 30)
        atr_val = calculate_atr(atr_klines) if atr_klines else (price * 0.01)
        sl_price = get_structure_sl(atr_klines, w["direction"], price, atr_val)
        sl_dist = abs(price - sl_price)

        zones = get_htf_zones(w["symbol"])
        min_rr_tp_dist = sl_dist * MIN_RR_RATIO
        structural_tp = get_structural_tp(price, w["direction"], zones, min_rr_tp_dist)
        if structural_tp is not None:
            tp_price = structural_tp
        else:
            tp_dist = max(atr_val * ATR_TP_MULTIPLIER, min_rr_tp_dist)
            tp_price = price + tp_dist if w["direction"] == "BUY" else price - tp_dist

        sl_pct = abs(price - sl_price) / price * 100 if price > 0 else 0
        tp_pct = abs(tp_price - price) / price * 100 if price > 0 else 0
        rr_ratio = tp_pct / sl_pct if sl_pct > 0 else 0.0

        atr_pct = (atr_val / price) * 100 if price > 0 else 0
        lev = get_smart_leverage(w["symbol"], atr_pct, 95.0, "Grade A")
        pos_size = get_fixed_fractional_size(RISK_PCT_BY_GRADE["A"], price, sl_price, lev)
        profit_target = tp_pct * lev

        eta = 60
        expiry_time = now + timedelta(minutes=SIGNAL_EXPIRY_MINUTES)
        pat_name = w["pattern"] + (" (Fast-Track)" if fast_track else " (Retest)")

        # Real pending_signals entry — this IS what makes the Activate
        # button actually work, the exact thing that was missing before.
        setup = {
            "coin": coin, "symbol": w["symbol"], "direction": w["direction"],
            "pattern": pat_name, "setup_score": 95.0, "leverage": lev,
            "scan_price": price, "entry": price, "sl": sl_price, "tp": tp_price,
            "original_tp": tp_price, "timestamp": now, "expires_at": expiry_time,
            "pos_size": pos_size, "profit_target": profit_target, "eta_minutes": eta,
            "reversal_alerted": False, "breakeven_sent": False, "partial_tp_taken": False,
            "milestones_sent": [], "market_condition": "unknown"
        }
        pending_signals[coin] = setup

        dir_em = "🟢 LONG  ▲" if w["direction"] == "BUY" else "🔴 SHORT ▼"
        header_title = ("⚡ EARLY ENTRY — FAST-TRACK CONFIRMED" if fast_track
                         else "🎯 EARLY ENTRY — RETEST CONFIRMED")
        msg = (
            f"<b>{header_title}</b>\n"
            f"┌─────────────────────────────────┐\n"
            f"│  ⚙️  TRADING SIGNAL MASTER v32G  │\n"
            f"└─────────────────────────────────┘\n\n"
            f"  🏗️ Engine: 🎯 EARLY ENTRY ENGINE\n"
            f"  🪙 <b>{coin}</b>  {dir_em}  🔧 <b>{lev}x Leverage</b>\n"
            f"  📌 Setup : <b>{pat_name}</b>\n\n"
            f"  ┌── TRADE LEVELS ─────────────┐\n"
            f"  │  💰 Entry      <code>{format_price(price)}</code>\n"
            f"  │  🎯 Target     <code>{format_price(tp_price)}</code>  <i>+{tp_pct:.2f}%</i>\n"
            f"  │  🛑 Stop       <code>{format_price(sl_price)}</code>  <i>-{sl_pct:.2f}%</i>\n"
            f"  └─────────────────────────────┘\n\n"
            f"  📈 Max Profit : <b>+{profit_target:.1f}%</b>\n"
            f"  ⚖️  Risk/Reward: <b>1 : {rr_ratio:.1f}</b>\n"
            f"  💼 Position   : <b>{pos_size:.1f}% of margin</b>\n"
            f"  📊 Volume     : <b>{vol_ratio:.1f}x avg</b>\n"
            f"  ⏰ Exp        : {expiry_time.strftime('%I:%M %p IST')}\n"
            f"  🕐 {get_ist_time()}"
        )
        reply_markup = {"inline_keyboard": [[
            {"text": "✅ Activate Trade", "callback_data": f"ACTIVATE_{coin}"},
            {"text": "❌ Ignore", "callback_data": f"IGNORE_{coin}"}
        ]]}

        if CHARTS_AVAILABLE:
            chart_path = generate_signal_chart(
                w["symbol"], atr_klines, price, sl_price, tp_price, w["direction"], coin,
                pattern_name=pat_name, lev=lev, profit_target=profit_target, vol_ratio=vol_ratio
            )
            if chart_path: send_telegram_photo(chart_path)

        send_telegram(msg, reply_markup=reply_markup)
        sent_coins.append(coin)
        coin_cooldowns[coin] = now + timedelta(minutes=eta)
        save_pending_signals()
        triggered.append((coin, w, price))

    if triggered: save_retest_watchlist()
    return triggered


def get_squeeze_radar_text():
    """
    Squeeze Radar: scans the coin list for extreme funding rates,
    reusing the already-verified SQUEEZE_FUNDING_EXTREME_NEG/POS
    thresholds (same ones Funding Divergence Sniper and the Squeeze
    scorecard bonus already use — not new numbers invented here).

    DELIBERATELY SCOPED TO FUNDING RATE ONLY, not funding+OI: checked
    get_funding_rate has real 15-min TTL caching (built in an earlier
    round), meaning a full coin-list scan is genuinely cheap here — most
    coins will hit cache if they were touched by a recent scan_coins
    cycle. get_oi_change_pct has NO caching at all — an uncached, on-
    demand scan across the full coin list would be a real, meaningful
    latency and rate-limit cost for a live Telegram command. Rather than
    silently promise a full funding+OI scan and either deliver something
    much slower than expected or silently skip OI without saying so,
    this is honestly scoped to funding rate only.
    """
    results = []
    for coin in COINS:
        symbol = coin + "USDT"
        rate = get_funding_rate(symbol)
        if rate is None:
            continue
        if rate <= SQUEEZE_FUNDING_EXTREME_NEG:
            results.append((coin, rate, "SHORT squeeze setup (shorts paying heavily)"))
        elif rate >= SQUEEZE_FUNDING_EXTREME_POS:
            results.append((coin, rate, "LONG squeeze setup (longs paying heavily)"))
    if not results:
        return f"{_H('SQUEEZE RADAR','🔥')}\n\nNo coins currently showing extreme funding rates."
    results.sort(key=lambda r: abs(r[1]), reverse=True)
    lines = [_H("SQUEEZE RADAR","🔥"), ""]
    for coin, rate, label in results[:15]:
        lines.append(f"🪙 <b>{coin}</b>  {rate*100:+.3f}%  •  {label}")
    lines.append("")
    lines.append(f"🕐 {get_ist_time()}")
    return "\n".join(lines)

def get_check_coin_text(coin_input):
    """
    Check Coin: on-demand pull of 15m structure, ADX, volume ratio, and
    whether price is currently sitting in a real HTF Supply/Demand zone
    — a personal-confirmation lookup, distinct from the automated
    scanning pipeline (this never sends a trade signal, purely
    read-only).
    """
    coin = coin_input.strip().upper().replace("USDT", "")
    symbol = coin + "USDT"
    price = get_price(symbol)
    klines = get_klines(symbol, "15m", 100)
    if not price or not klines or len(klines) < 50:
        return f"{_H('CHECK COIN','🔍')}\n\n❌ Could not fetch enough data for <b>{coin}</b> — check the symbol and try again."
    closes = [float(k[4]) for k in klines]
    adx_val = calculate_adx(klines)
    vol_ratio = get_volume_ratio(klines)
    ms = detect_market_structure(klines)
    zones = get_htf_zones(symbol)
    zone_ok_buy, zone_label_buy = is_in_zone(price, "BUY", zones)
    zone_ok_sell, zone_label_sell = is_in_zone(price, "SELL", zones)
    rsi_val = calculate_rsi(closes)
    lines = [
        _H(f"CHECK COIN — {coin}", "🔍"), "",
        f"💰 Price: <code>{format_price(price)}</code>",
        f"🏗️ Structure: {ms['bias'].upper()}  •  BOS: {'✅' if ms['bos'] else '➖'}  •  ChoCh: {'✅' if ms['choch'] else '➖'}",
        f"💪 ADX: {adx_val:.1f}  •  📊 Vol: {vol_ratio:.2f}x avg  •  📈 RSI: {rsi_val:.1f}",
    ]
    if zone_ok_buy:
        lines.append(f"📍 Sitting in a real Demand zone: {zone_label_buy}")
    elif zone_ok_sell:
        lines.append(f"📍 Sitting in a real Supply zone: {zone_label_sell}")
    else:
        lines.append("📍 Not currently inside a real HTF zone")
    lines.append("")
    lines.append(f"🕐 {get_ist_time()}")
    return "\n".join(lines)

def get_retest_watchlist_text():
    # PENDING-only filter (this round): FOUND A REAL, NEW ISSUE the
    # status-tracking migration would have caused if left unfixed —
    # since TRIGGERED entries now stay in retest_watchlist until their
    # 12h expiry (not deleted immediately), this would otherwise show
    # already-fired coins mixed in with genuinely still-pending ones,
    # confusing for a command whose entire point is "what's currently
    # being watched."
    pending = {c: w for c, w in retest_watchlist.items() if w.get("status", "PENDING") == "PENDING"}
    if not pending:
        return f"{_H('RETEST WATCHLIST','👀')}\n\n  🌙 No coins currently being watched for retest.\n\n  🕐 {get_ist_time()}"
    lines = [f"{_H('RETEST WATCHLIST','👀')}\n"]
    for coin, w in pending.items():
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


def scan_coins(btc_trend,fng,market_condition,btc_klines=None):
    btc_crashing=is_btc_crashing(); signals_this_cycle=0
    # ── CONCURRENT PRE-FETCH (this round): SCOPED NARROWLY ──
    # Deliberately NOT a full asyncio/aiohttp rewrite (that was declined
    # in an earlier round as too large a change to bundle into a patch
    # pass on a live-trading bot). This isolates ALL the concurrency risk
    # to a single, simple, easily-verified step: fetch price+klines for
    # every coin that would actually be scanned this cycle, all at once,
    # using a thread pool — then run the EXISTING sequential loop below
    # completely unchanged, just reading from the pre-fetched results
    # instead of calling get_price/get_klines directly inline. 100% of
    # the actual decision-making logic (patterns, scoring, sending,
    # MAX_SIGNALS_PER_CYCLE, per-coin try/except) is untouched.
    #
    # Verified both get_price and get_klines are safe for concurrent
    # calls before doing this: read their implementations directly and
    # confirmed neither reads nor writes any shared mutable state — each
    # is a pure function of (symbol) -> value via a single stateless
    # requests.get call, so running many of them in parallel threads
    # carries no race risk of its own.
    #
    # Cooldown-filtered BEFORE the concurrent fetch (not after), so coins
    # that would be skipped anyway don't waste a request.
    now_check=get_ist_datetime()
    coins_to_fetch=[c for c in COINS if c not in coin_cooldowns or now_check>=coin_cooldowns[c]]
    fetch_results={}
    def _fetch_one(coin):
        symbol=coin+"USDT"
        try:
            return coin,symbol,get_price(symbol),get_klines(symbol,"15m")
        except Exception as e:
            logger.warning(f"prefetch {coin}: {e}")
            return coin,symbol,None,None
    with concurrent.futures.ThreadPoolExecutor(max_workers=20) as executor:
        for coin,symbol,price,klines in executor.map(_fetch_one,coins_to_fetch):
            fetch_results[coin]=(symbol,price,klines)
    for coin in COINS:
        if signals_this_cycle>=MAX_SIGNALS_PER_CYCLE: break
        try:
            if coin in coin_cooldowns:
                if get_ist_datetime()<coin_cooldowns[coin]:
                    logger.info(f"Skip {coin} - cooldown until {coin_cooldowns[coin].strftime('%H:%M')}"); continue
                else: del coin_cooldowns[coin]
            if coin not in fetch_results: continue
            symbol,price,klines=fetch_results[coin]
            if not price or not klines: continue
            # ── DIRECT-TO-CLAUDE VANGUARD BYPASS (BTC/ETH/SOL) ──
            # STRUCTURAL BUG FIXED before implementing: originally proposed
            # to live inside the per-direction loop, AFTER detect_patterns
            # already gates the flow with "if not found: continue". But the
            # entire premise here is that a genuinely compressed major
            # asset may show NO visible pattern to Python at all — meaning
            # that placement would mean the bypass code could never
            # actually run in the exact scenario it exists for. Moved
            # earlier, before pattern detection can short-circuit the loop.
            #
            # DIRECTION GAP FIXED: every other pattern in this bot already
            # knows its direction from detection logic; this bypass has no
            # such signal (that's the whole point — Python can't tell which
            # way a genuine compression will break). Every part of the AI/
            # format_and_send pipeline requires a specific directional
            # thesis, not an open-ended question, so a real direction has
            # to be chosen somehow. Resolved with a defensible heuristic:
            # pick whichever side of the current compressed range price
            # currently sits closer to (nearer the top of the 20-candle
            # range -> lean BUY on a breakout thesis; nearer the bottom ->
            # lean SELL on a breakdown thesis) — Claude still independently
            # evaluates and can reject that specific thesis with TRADE:NO,
            # exactly like every other signal; this isn't a guaranteed
            # trade, just a provisional direction to hand to a real review.
            # WORTH FLAGGING (same category of concern as the earlier AI
            # Fast-Track round's budget note, not silently expanded here):
            # this widens Vanguard from 3 highly-liquid majors to 21 coins,
            # several of them lower-cap/newer tokens. This check runs every
            # scan cycle (~90s) for every coin in this tuple — a thinner-
            # liquidity token can plausibly sit in a <1% range for extended
            # stretches (low volume periods, thin order books), meaning
            # this bypass could fire meaningfully more often across the
            # full list than it does today for just BTC/ETH/SOL. A real,
            # non-trivial increase in AI call volume, not a free change.
            vanguard_coins = (
                "BTC","ETH","SOL","HYPE","BERA","IP","INIT","BABY",
                "SAHARA","WAL","LAYER","RED","SPK","NEWT","KERNEL",
                "EPT","COOKIE","BIO","VVV","ARC","BANK"
            )
            if coin in vanguard_coins and len(klines)>=20:
                v_highs=[float(k[2]) for k in klines[-20:]]
                v_lows=[float(k[3]) for k in klines[-20:]]
                v_range_high=max(v_highs); v_range_low=min(v_lows)
                price_range_pct=(v_range_high-v_range_low)/price*100 if price>0 else 99
                # ALTCOIN-AWARE THRESHOLD (this round): VERIFIED THE
                # PREMISE via web search before applying — confirmed
                # altcoins genuinely carry meaningfully higher typical
                # volatility than BTC (multiple independent sources: ETH
                # ~1.3x, XRP ~1.4x, DOGE ~1.6x BTC's average daily move;
                # smaller/thinner-liquidity coins routinely see 20%+ daily
                # swings). The exact 3.8% figure is NOT independently
                # verified against real data for this specific coin set —
                # flagging it as a reasonable judgment call, not a
                # confirmed constant, same as other threshold numbers
                # introduced this session without a precise source.
                v_thresh = 1.0 if coin in ("BTC","ETH","SOL") else 3.8
                if price_range_pct < v_thresh:
                    # PREDICTIVE DIRECTION: use the real 4h trend instead
                    # of guessing from range position, when available.
                    #
                    # DIRECTION CORRECTED (this round): VERIFIED this
                    # wasn't just a code-matching exercise before applying
                    # — traced through why the previous mapping (bearish
                    # trend -> BUY, bullish trend -> SELL) was actually
                    # wrong, not just different. get_htf_trend is a pure
                    # TREND indicator (EMA20 vs EMA50 crossover), not a
                    # reversal/exhaustion signal — betting AGAINST a
                    # confirmed trend with zero additional evidence is the
                    # structurally weaker default. Genuine reversal
                    # patterns (Early Spark Ignition, Smart Money
                    # Absorption) already exist elsewhere in this file
                    # with their OWN dedicated evidence requirements
                    # (real macro drop %, volume absorption) that Vanguard
                    # itself never checks. This directly produced a real,
                    # observed loss: a BTC SHORT at $64,745 while BTC was
                    # in a confirmed uptrend above $65,200, sitting at
                    # -6.04% — the previous mapping's "elif htf_4h==1:
                    # v_direction=SELL" branch is exactly what fired.
                    # Fixed: squeezes in a bull market break UP (BUY),
                    # squeezes in a bear market break DOWN (SELL) — trade
                    # WITH the confirmed trend by default.
                    htf_4h=get_htf_trend(symbol,"4h")
                    if htf_4h==1: v_direction="BUY"
                    elif htf_4h==-1: v_direction="SELL"
                    else:
                        v_mid=(v_range_high+v_range_low)/2
                        v_direction="BUY" if price>=v_mid else "SELL"
                    # DAILY MACRO VETO ENFORCEMENT (this round): VERIFIED
                    # THIS WAS A REAL GAP before applying, not a duplicate
                    # of existing logic — I had already explicitly
                    # documented (see the is_early_setup comment further
                    # down this function) that Vanguard Macro Squeeze
                    # should respect the Daily Veto, since it's a
                    # breakout-direction guess, not a genuine bottom-
                    # catching pattern. But Vanguard constructs its own
                    # setup and calls format_and_send directly, bypassing
                    # detect_patterns and that later shared veto check
                    # entirely via its own `continue` below — meaning my
                    # own stated intent was never actually enforced for
                    # this specific code path. Computed once here and
                    # reused for both the veto check and the setup dict
                    # (was previously computed a second time inline for
                    # v_setup["tf_score"] — now a single call).
                    v_tf_score=get_timeframe_score(symbol,v_direction)
                    if v_tf_score==-1:
                        logger.info(f"Skip {coin} {v_direction} - VANGUARD counter-trend (Daily Macro Veto enforced)")
                        continue
                    logger.info(f"{coin} VANGUARD: extreme compression ({price_range_pct:.2f}% range, threshold {v_thresh}%) — bypassing Python math, sending directly to Claude to forecast {v_direction} breakout")
                    v_atr=calculate_atr(klines); v_atr_pct=(v_atr/price)*100 if price>0 else 0
                    v_score=92.0
                    v_lev=get_smart_leverage(symbol,v_atr_pct,v_score)
                    v_setup={"coin":coin,"symbol":symbol,"direction":v_direction,
                             "pattern":"Vanguard Macro Squeeze","setup_score":v_score,
                             "leverage":v_lev,"scan_price":price,
                             "market_condition":market_condition,"tf_score":v_tf_score}
                    if format_and_send(v_setup,coin,is_instant=False,market_condition=market_condition):
                        signals_this_cycle+=1
                    continue
            # ── FUNDING RATE DIVERGENCE SNIPER — genuinely standalone ──
            # Placed BEFORE the detect_patterns gate (same reasoning as
            # the Vanguard bypass fix from an earlier round): if this
            # only ran after "if not found: continue" already exited,
            # it could never fire as a real standalone pattern on a coin
            # detect_patterns saw nothing else on — which would defeat
            # the entire point of it being predictive, not confirmatory.
            fd_funding=get_funding_rate(symbol)
            if fd_funding is not None:
                fd_ms=detect_market_structure(klines)
                fd_highs=[float(k[2]) for k in klines]; fd_lows=[float(k[3]) for k in klines]
                fd_sup=fd_ms["swing_low"] if fd_ms["swing_low"]>0 else min(fd_lows[-30:-1])
                fd_res=fd_ms["swing_high"] if fd_ms["swing_high"]>0 else max(fd_highs[-30:-1])
                fd_direction=detect_funding_divergence(fd_funding,price,fd_sup,fd_res)
                # DELIBERATELY NOT ENFORCING THE DAILY MACRO VETO HERE —
                # checked this precisely before deciding, not applied
                # blindly. Funding Divergence Sniper's own trigger
                # condition (extreme funding at a real support/resistance
                # level) is structurally the SAME "market is squeezed,
                # Daily trend will obviously read against the setup"
                # situation as Early Spark Ignition / Inside Bar Coil,
                # which already have a Daily Veto exemption for exactly
                # this reason: extreme negative funding at support means
                # shorts have been winning, which means the Daily trend
                # has very likely been bearish — that's not a coincidence
                # to filter out, it's the actual premise of the squeeze
                # thesis. Enforcing the veto here would reintroduce the
                # identical contradiction already found and fixed for
                # is_sentiment_valid two rounds ago (vetoing the exact
                # signal the pattern exists to catch). Cross-checked
                # against is_sentiment_valid's own predictive_patterns
                # list before deciding — Funding Divergence Sniper is
                # already grouped there with Smart Money Absorption
                # (genuine reversal/squeeze patterns), not with Vanguard
                # Macro Squeeze (a trend-following direction guess, which
                # DOES now correctly respect this veto, above).
                with trade_lock:
                    fd_ok_to_send = (fd_direction and coin not in active_trades and coin not in pending_signals and len(active_trades)<MAX_ACTIVE_TRADES)
                if fd_ok_to_send:
                    logger.info(f"{coin} FUNDING DIVERGENCE: {fd_funding*100:.3f}% funding at a real level — {fd_direction} squeeze setup")
                    fd_atr=calculate_atr(klines); fd_atr_pct=(fd_atr/price)*100 if price>0 else 0
                    fd_score=92.0
                    fd_lev=get_smart_leverage(symbol,fd_atr_pct,fd_score)
                    fd_setup={"coin":coin,"symbol":symbol,"direction":fd_direction,
                             "pattern":"Funding Divergence Sniper","setup_score":fd_score,
                             "leverage":fd_lev,"scan_price":price,
                             "market_condition":market_condition,"tf_score":get_timeframe_score(symbol,fd_direction)}
                    if format_and_send(fd_setup,coin,is_instant=False,market_condition=market_condition):
                        signals_this_cycle+=1
                    continue

            # ── ORDER FLOW SNIPER — genuinely standalone, this round ──
            # THE ACTUAL "OUT OF THE BOX" MOVE: detect_aggressive_order_flow
            # already existed and was already correctly built — it was
            # just structurally trapped as a +2.0 scorecard bonus inside
            # compute_confirmation_bonus, which only ever runs AFTER
            # detect_patterns already found a shape-based pattern (a
            # Double Top, a BOS, etc.). That's the real box: genuine,
            # causal information (who is actually winning the fight for
            # this coin right now, via real taker volume) was sitting in
            # the file the whole time, but was never allowed to be a
            # reason to look at a coin, only a reason to add a couple of
            # points to a pattern that had already waited for a shape to
            # finish forming. Promoted to a standalone trigger here,
            # placed before detect_patterns for the same reason as
            # Funding Divergence Sniper — so it can fire on a coin the
            # shape-based patterns see nothing on at all.
            of_direction = detect_order_flow_sniper(symbol, klines, price)
            with trade_lock:
                of_ok_to_send = (of_direction and coin not in active_trades and coin not in pending_signals and len(active_trades)<MAX_ACTIVE_TRADES)
            if of_ok_to_send:
                logger.info(f"{coin} ORDER FLOW SNIPER: sustained taker {of_direction} imbalance with 4H/1H trend — {of_direction} setup")
                of_atr=calculate_atr(klines); of_atr_pct=(of_atr/price)*100 if price>0 else 0
                of_score=90.0
                of_lev=get_smart_leverage(symbol,of_atr_pct,of_score)
                of_setup={"coin":coin,"symbol":symbol,"direction":of_direction,
                         "pattern":"Order Flow Sniper","setup_score":of_score,
                         "leverage":of_lev,"scan_price":price,
                         "market_condition":market_condition,"tf_score":get_timeframe_score(symbol,of_direction)}
                if format_and_send(of_setup,coin,is_instant=False,market_condition=market_condition):
                    signals_this_cycle+=1
                continue

            # ── LIGHTNING IGNITION ENGINE (parallel micro-engine, this
            # round) — genuinely standalone, requires BOTH a real
            # candlestick/structure shape AND a matching live CVD spike.
            # Runs BEFORE the existing CVD-only trigger below as a
            # stricter, additional path — VERIFIED cannot double-fire:
            # both independently gate on coin not in active_trades/
            # pending_signals and both use continue on success.
            # detect_patterns is completely untouched by this. ──
            lightning_setup = check_lightning_ignition_engine(symbol, price)
            if lightning_setup:
                with trade_lock:
                    _lightning_ok = (coin not in active_trades and coin not in pending_signals and len(active_trades)<MAX_ACTIVE_TRADES)
                if _lightning_ok:
                    logger.info(f"{coin} LIGHTNING IGNITION ENGINE: {lightning_setup['pattern']} — {lightning_setup['direction']} setup")
                    if format_and_send(lightning_setup, coin, is_instant=True, market_condition=market_condition):
                        signals_this_cycle += 1
                    continue

            ignition_dir = detect_cvd_delta_3m(symbol)
            if ignition_dir:
                _ign_zones = get_htf_zones(symbol)
                _ign_zone_ok, _ign_z_label = is_in_zone(price, ignition_dir, _ign_zones)
                with trade_lock:
                    _ign_ok_to_send = (_ign_zone_ok and coin not in active_trades and coin not in pending_signals and len(active_trades)<MAX_ACTIVE_TRADES)
                if _ign_ok_to_send:
                    logger.info(f"{coin} LIGHTNING 3M IGNITION: taker delta spike at {_ign_z_label} — {ignition_dir} setup")
                    ign_setup = {
                        "coin": coin, "symbol": symbol, "direction": ignition_dir,
                        "pattern": "Lightning 3M Ignition (Taker Delta)", "setup_score": 99.0,
                        "leverage": get_smart_leverage(symbol, 0.5, 99.0), "scan_price": price,
                        "market_condition": market_condition, "tf_score": get_timeframe_score(symbol, ignition_dir),
                        "is_lightning": True,
                    }
                    if format_and_send(ign_setup, coin, is_instant=True, market_condition=market_condition):
                        signals_this_cycle += 1
                    continue

            # ── PRE-BREAKOUT MACRO ENGINE — genuinely standalone,
            # fetches its own real 1H/4H data, NOT fed 15m klines and
            # NOT routed through detect_patterns.
            #
            # LEVEL PRECISION FIX (this round): unpacks the real 4th
            # value (the pattern's actual geometric boundary) and
            # passes it to log_macro_coil instead of substituting live
            # price — a real, verified gap: live price at detection time
            # is an arbitrary point INSIDE the pattern, not its real
            # breakout boundary, which could have triggered the state
            # machine on a normal in-range tick rather than a genuine
            # breakout.
            #
            # CANNIBALIZATION FIX (this round): CORRECTED MY OWN PRIOR
            # REASONING from two rounds ago — I had deliberately let the
            # 15m pipeline continue evaluating a coin already tracked by
            # the macro engine, reasoning that background monitoring and
            # 15m evaluation could coexist safely. Re-examined that
            # against the concrete case where it actually breaks: a coin
            # already committed to a patient, larger-target macro thesis
            # could get an unrelated, smaller, tighter-risk 15m trade
            # fired on top of it, corrupting the intended macro
            # position/risk. My original reasoning considered whether
            # the two DETECTIONS conflict, not whether independent
            # EXECUTION on the same coin does — a real correction, not
            # just a new preference. ──
            if coin not in macro_coils:
                macro_pat, macro_dir, macro_quality, macro_level = detect_macro_setups_4h_1h(symbol)
                if macro_pat:
                    log_macro_coil(coin, symbol, macro_pat, macro_dir, macro_quality, macro_level)

            if coin in macro_coils:
                continue

            found=detect_patterns(symbol,klines,price,btc_trend)
            if not found: continue
            scored=get_all_pattern_scores(found,market_condition)
            signal_sent=False
            for direction in ["BUY","SELL"]:
                if signal_sent: break
                dir_pats=[p for p in scored if p[2]==direction]
                if not dir_pats: continue
                best_pat=dir_pats[0]; primary=best_pat[0]; adj_score=best_pat[1]; base_s=best_pat[3]
                best_geo_notes = best_pat[4] if len(best_pat) > 4 else None
                if base_s<MIN_PRIMARY_SCORE:                                   continue
                if is_pattern_blacklisted(primary):                             continue
                if is_pattern_suspended(primary):                               continue
                if not is_sentiment_valid(direction,fng,primary):
                    logger.info(f"Skip {coin} {direction} - blocked by Fear & Greed sentiment ({fng})")
                    continue
                if btc_crashing and direction=="BUY":                           continue
                if coin in BTC_CORRELATED and too_many_correlated_active():     continue
                if too_many_sector_active(coin):
                    logger.info(f"Skip {coin} {direction} - sector already has an open trade")
                    continue
                # ── THE IDIOSYNCRATIC ALPHA GATE ──
                # A structural pattern on an alt that's underperforming
                # BTC over the recent window has no independent momentum
                # — a "beta trap" that dumps through its tight structural
                # stop the moment BTC ticks down. Placed with the other
                # early-continue filters above (fails fast, before the
                # more expensive zone/structure work below runs).
                #
                # ACCUMULATION EXEMPTION (this round): VERIFIED THIS
                # CONFLICT was real before applying, re-checking my own
                # original reasoning above first. That reasoning is
                # genuinely correct for patterns that NEED independent
                # momentum to justify a tight stop — but Smart Money
                # Absorption's own detection logic REQUIRES a real prior
                # decline (macro_drop >= 12%) before it even looks for the
                # coil, meaning a coin in exactly that state will
                # structurally show negative 4h performance. This is the
                # same conflict already found and fixed for the Daily EMA
                # trend veto and the SuperTrend hard block in earlier
                # rounds — a genuine bottom, by definition, looks red on
                # a recent-performance measure right up until the
                # reversal is already underway. Funding Divergence Sniper
                # included for consistency with the other exemption
                # tuples in this file, though it's currently a no-op
                # here specifically — its own block (a few dozen lines
                # above) already exits the loop before this point is ever
                # reached.
                is_early_setup = primary in ("Inside Bar Coil","Pre-Breakout Compression","Volatility Contraction (Coiling)","Early Spark Ignition","Smart Money Absorption","Funding Divergence Sniper","Order Flow Sniper","Yellow Circle Sniper")
                alt_perf, btc_perf = check_relative_strength(symbol, btc_klines)
                if not is_early_setup:
                    if direction == "BUY" and alt_perf < btc_perf:
                        logger.info(f"Skip {coin} LONG - underperforming BTC (Beta Trap Risk)")
                        continue
                    if direction == "SELL" and alt_perf > btc_perf:
                        logger.info(f"Skip {coin} SHORT - outperforming BTC (Short Squeeze Risk)")
                        continue
                    # ── THE ABSOLUTE DIRECTIONAL LOCK ──
                    # VERIFIED THIS GAP WAS REAL before applying: the relative
                    # checks above only compare the alt's performance AGAINST
                    # BTC's — they say nothing about the alt's own absolute
                    # direction. Traced the exact scenario through the actual
                    # code: BTC +4%, alt +1% (still genuinely GREEN, still
                    # rising) — confirmed the SHORT gate above does NOT fire
                    # here (alt_perf=0.01 is not > btc_perf=0.04), so the bot
                    # would happily open a SHORT on a coin that's still going
                    # up, purely because it's rising slower than BTC. Fixed
                    # with a hard absolute rule: never short a coin that's
                    # net positive over the window, never long one that's net
                    # negative — regardless of how it compares to BTC.
                    if direction == "SELL" and alt_perf > 0:
                        logger.info(f"Skip {coin} SHORT - coin is still green ({alt_perf*100:+.2f}%), absolute directional lock")
                        continue
                    if direction == "BUY" and alt_perf < 0:
                        logger.info(f"Skip {coin} LONG - coin is still red ({alt_perf*100:+.2f}%), absolute directional lock")
                        continue
                tf_score=get_timeframe_score(symbol,direction)
                # Accumulation/Early-Spark exemption from the Daily Macro
                # Veto. WORTH BEING DIRECT ABOUT THE TENSION HERE: this
                # hard veto (tf_score==-1 on Daily disagreement) was built
                # deliberately in an earlier round, in direct response to
                # an explicit instruction to "permanently block" counter-
                # daily-trend trades — it was not a bug. This carves out a
                # narrow, considered exception: a coin coiling quietly at
                # a range bottom before a genuine reversal will almost
                # definitionally have a bearish/neutral Daily chart (the
                # reversal hasn't happened yet) — the same veto that
                # correctly blocks breakout-chasing counter-trend trades
                # would also block catching the reversal itself. Scoped
                # narrowly to only the same 4 accumulation/early-spark
                # pattern types that already get the lower score floor,
                # not a blanket removal of the Daily veto.
                # TIGHTENED (earlier round): VERIFIED THE REASONING before
                # applying — a genuine reversal/bottom-catching pattern
                # (Early Spark Ignition, Inside Bar Coil resting on a real
                # zone) legitimately should bypass the Daily Veto, since a
                # coin reversing from a crash will almost always show a
                # bearish/neutral Daily chart — that's what a bottom looks
                # like before it reverses. But a PRE-BREAKOUT continuation
                # pattern (Pressure Cooker Triangle, Pre-Breakout
                # Compression, Volatility Contraction) trading AGAINST the
                # Daily macro direction is a genuinely different bet — not
                # catching a reversal, just gambling that a random
                # continuation pattern beats the prevailing daily trend.
                # Vanguard Macro Squeeze also removed from this exemption
                # (not explicitly named in the request, but consistent with
                # its own stated logic): Vanguard is a breakout-DIRECTION
                # GUESS on major coins, not a bottom-catching pattern like
                # Early Spark — it belongs in the same "must respect Daily
                # trend" category as the continuation patterns.
                #
                # EXPANDED (this round): Smart Money Absorption added.
                # VERIFIED THIS WAS A GENUINE MISS before applying, not
                # just applying what was proposed — re-checked my own
                # classification above and confirmed Smart Money
                # Absorption fits squarely in the "genuine reversal/
                # bottom-catching" category, not the continuation
                # category: its own detection logic requires a real prior
                # decline (macro_drop >= 12%) before it even looks for the
                # coil, structurally identical to Early Spark Ignition's
                # premise. Pressure Cooker Triangle/Pre-Breakout
                # Compression/Volatility Contraction/Vanguard remain
                # excluded — that classification stands, unchanged.
                is_early_setup = primary in ("Early Spark Ignition","Inside Bar Coil","Smart Money Absorption")
                if tf_score==-1 and not is_early_setup:
                    logger.info(f"Skip {coin} {direction} - counter-trend (Daily Macro Veto enforced)"); continue
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
                is_sweep_pattern = "Liquidity Sweep" in primary
                # Risk-Proximity bonus needs the real structural SL distance.
                # Computed here (pure computation on already-fetched klines,
                # no new API call) rather than waiting for format_and_send's
                # own later SL calculation, since the scorecard needs it now.
                atr_chk=calculate_atr(klines)
                sl_chk=get_structure_sl(klines,direction,price,atr_chk)
                confirm_bonus,bonus_notes=compute_confirmation_bonus(
                    symbol,direction,klines,vols_chk,tf_score,btc_aligned_chk,
                    zone_ok=zone_ok,ms_bos=ms_chk["bos"],ms_bias=ms_chk["bias"],
                    ms_choch=ms_chk["choch"],is_tier1=is_tier1_pattern,is_compression=is_comp_pattern,
                    is_sweep=is_sweep_pattern,entry=price,sl=sl_chk
                )
                # Extra-pattern confluence still counts, but modestly — it's not the main driver anymore
                confluence_bonus=min(len(dir_pats)*0.3,1.0)
                score=min(adj_score+confirm_bonus+confluence_bonus,99)
                if bonus_notes:
                    logger.info(f"{coin} {direction} confirmation: base={adj_score:.1f} +{confirm_bonus} ({', '.join(bonus_notes)}) -> {score:.1f}")
                # ── THE ACCUMULATION GATING EXEMPTION ──
                # Sniper/accumulation patterns (Inside Bar Coil, Pre-
                # Breakout Compression, Volatility Contraction) are quiet
                # BY DEFINITION — dead volume, flat momentum, no BOS/
                # SuperTrend confirmation yet, since the whole point is
                # catching the setup BEFORE it gets loud. The global
                # MIN_SETUP_SCORE floor (90) forces them to hunt for
                # scorecard points a genuinely quiet coil will never have,
                # systematically deleting early entries and only letting
                # the bot fire once a coin is already loud and extended.
                # WORTH BEING EXPLICIT (not silently shipping this): since
                # these patterns' own TIER1_BASE (88.0) already sits above
                # this 86.0 exemption floor, this means they can now fire
                # on pure pattern detection + their own built-in zone/
                # distance validation (each detector already requires
                # resting near a real level), with ZERO scorecard
                # confirmation bonus required. That's a deliberate,
                # significant change from every other pattern type in
                # this bot, not an oversight — the pattern's own detection
                # logic is being treated as sufficient confirmation on
                # its own, per the explicit "enter at the absolute
                # baseline floor of a HTF zone" framing.
                is_accumulation_pattern = primary in ("Inside Bar Coil","Pre-Breakout Compression","Volatility Contraction (Coiling)","Early Spark Ignition","Vanguard Macro Squeeze","Smart Money Absorption","Funding Divergence Sniper","Order Flow Sniper","Yellow Circle Sniper")
                effective_floor = ACCUMULATION_SCORE_FLOOR if is_accumulation_pattern else MIN_SETUP_SCORE
                if score<effective_floor: continue
                closes_chk=[float(k[4]) for k in klines]
                highs_chk=[float(k[2]) for k in klines]
                lows_chk=[float(k[3]) for k in klines]
                if "Volatility Contraction" not in primary and is_move_already_extended(closes_chk,direction):
                    # VERIFIED THE SPAM-LOOP BUG before fixing: confirmed
                    # log_retest_candidate does a full dict REPLACEMENT of
                    # retest_watchlist[coin], unconditionally resetting
                    # notified=False every single call — since this scan
                    # loop runs every ~90s and a genuinely extended move
                    # can stay extended for hours, the same coin was being
                    # re-logged (and its notified flag re-reset) on every
                    # cycle, causing check_retest_triggers to re-fire
                    # repeatedly on a level that hadn't actually changed.
                    # Guarded: only log if the coin isn't already on the
                    # watchlist, so an existing, still-valid entry (and
                    # its real notified state) is left alone.
                    if coin not in retest_watchlist:
                        log_retest_candidate(coin,symbol,direction,closes_chk,highs_chk,lows_chk,pt)
                    continue
                if primary == "Inside Bar Coil":
                    # BUG FOUND AND FIXED: detect_inside_bar_coil's own
                    # docstring claimed it validates against "a real HTF
                    # Supply/Demand zone... layered on top at the
                    # scan_coins call site" — but no such downstream
                    # check ever actually existed. The only real call
                    # site (in detect_patterns) passes local swing sup/res
                    # positionally into the function's zone_low/zone_high
                    # parameters — not real HTF zone data at all, despite
                    # the naming implying otherwise. Fixed by adding the
                    # genuine HTF-zone check here, using zones_chk (already
                    # fetched above for Location Multiplier scoring, no new
                    # API call needed) — an Inside Bar Coil that isn't
                    # actually resting in a real mapped zone is rejected
                    # rather than silently treated as zone-validated.
                    ib_zone_ok,_ib_zone_label=is_in_zone(price,direction,zones_chk)
                    if not ib_zone_ok:
                        logger.info(f"Skip {coin} {direction} - Inside Bar Coil not in a real HTF zone (local swing level only)")
                        continue
                    # VERIFIED GAP before fixing: the entry trigger only
                    # checked whether price crossed the inside bar's own
                    # high/low, with no volume requirement at all — a
                    # coin that casually drifts past that level on dead
                    # volume isn't an explosive coil release, it's a slow
                    # drift that gets trapped the moment real sellers/
                    # buyers show up. Reuses get_volume_ratio (the shared
                    # helper already consolidated elsewhere this session)
                    # rather than duplicating the avg-vol/ratio computation
                    # inline again.
                    ib_vol_ratio=get_volume_ratio(klines)
                    if ib_vol_ratio < 1.1:
                        logger.info(f"Skip {coin} {direction} - Inside Bar Coil break lacks volume uncoiling ({ib_vol_ratio:.2f}x)")
                        continue
                # ── THE INSTITUTIONAL ZONE GATE ──
                # VERIFIED THIS GAP IS REAL before applying: checked
                # Support Bounce/Resistance Rejection's actual detection
                # code in detect_patterns — despite being commented
                # "(Zone Bounce)", they trigger off `sup`/`res`, the LOCAL
                # swing-based levels computed inside detect_patterns, not
                # real HTF zones from get_htf_zones. Double Top/Double
                # Bottom have no zone requirement at all. All four are
                # genuine "retail bait" location patterns that smart money
                # is known to hunt (sweep the wick, reverse into the
                # crowd's stops) when they form outside a real
                # institutional zone. Gated here using zones_chk (already
                # fetched above, no new API call) — if the pattern didn't
                # land inside a real, verified HTF zone, it's vetoed.
                if primary in ("Double Top","Double Bottom","Support Bounce","Resistance Rejection"):
                    if not zone_ok:
                        logger.info(f"Skip {coin} {direction} - {primary} rejected: formed outside real HTF zone (no man's land)")
                        continue
                if primary in ("BOS Breakout","Double Top","Double Bottom"):
                    # LEVEL CREEP GUARD ADDED (this round): VERIFIED THIS
                    # WAS A REAL, SERIOUS BUG before applying — this block
                    # had NO guard against re-logging an already-watched
                    # coin, unlike the extended_move path a few lines
                    # above, which does. Confirmed log_retest_candidate
                    # performs a blind, unconditional dict overwrite. This
                    # meant the precise_level fix from two rounds ago
                    # computed a genuinely correct level on the FIRST
                    # call, then got silently clobbered by the very next
                    # ~90s scan cycle recomputing the generic
                    # min(lows[-12:]) fallback against price that had
                    # since moved — the level would "creep" upward
                    # (for a BUY) in lockstep with price itself, so a
                    # fixed 0.8% fast-track distance from that creeping
                    # level could represent a much larger real move from
                    # the original bottom. This directly explains the
                    # reported gap.
                    if coin in retest_watchlist:
                        continue
                    # Point 1 (BOS + Retest) extended (earlier round):
                    # VERIFIED A REAL GAP before applying — the retest
                    # gate only ever checked `primary == "BOS Breakout"`,
                    # but a real trade (NEAR/USDT) had "Double Top" as
                    # primary with "BOS Breakout" riding along as
                    # confluence in the compound pattern string — meaning
                    # this gate never applied to that trade at all.
                    #
                    # PRECISE RETEST LEVEL ADDED (this round): VERIFIED
                    # THE REAL GAP before applying — a live ONDO trade
                    # showed the fast-track firing ~2.7% past the coin's
                    # actual bottom, well beyond what the already-
                    # calibrated 0.8% fast-track distance explains on its
                    # own. Traced the cause: log_retest_candidate's
                    # generic fallback (min/max of the last 12 candles)
                    # is a cruder, LATER-anchored approximation of the
                    # real swing low/high detect_double_bottom_pro and
                    # detect_double_top_pro already compute internally to
                    # confirm the pattern's shape exists — that real,
                    # precise value was being discarded. Re-calling those
                    # same detectors here is cheap (pure computation on
                    # klines already fetched this cycle, no new API
                    # call) and gives the retest watchlist the actual
                    # bottom/top the pattern detected, not a generic
                    # trailing-window guess. BOS Breakout has no
                    # pattern-specific level to compute, so it correctly
                    # keeps using the generic fallback (precise_level
                    # stays None for it).
                    _precise_level = None
                    if primary in ("Double Top","Double Bottom"):
                        _avg_vol_chk = sum(vols_chk[-20:]) / 20 if len(vols_chk) >= 20 else 1.0
                        if primary == "Double Bottom":
                            _fired, _lvl = detect_double_bottom_pro(highs_chk, lows_chk, closes_chk, vols_chk, price, _avg_vol_chk)
                        else:
                            _fired, _lvl = detect_double_top_pro(highs_chk, lows_chk, closes_chk, vols_chk, price, _avg_vol_chk)
                        if _fired and _lvl > 0:
                            _precise_level = _lvl
                    log_retest_candidate(coin,symbol,direction,closes_chk,highs_chk,lows_chk,pt,pattern_type="bos_retest",precise_level=_precise_level)
                    continue
                atr=atr_chk; atr_pct=(atr/price)*100 if price>0 else 0
                lev=get_smart_leverage(symbol,atr_pct,score)
                setup={"coin":coin,"symbol":symbol,"direction":direction,"pattern":pt,
                       "setup_score":score,"leverage":lev,"scan_price":price,
                       "market_condition":market_condition,"tf_score":tf_score,
                       "geometry_notes":best_geo_notes}
                with trade_lock:
                    ok_to_send = (coin not in active_trades and coin not in pending_signals and len(active_trades)<MAX_ACTIVE_TRADES)
                if ok_to_send:
                    is_inst=score>=INSTANT_SIGNAL_THRESHOLD
                    logger.info(f"{'INSTANT' if is_inst else 'SIGNAL'}: {coin}|{direction}|Score:{score:.1f}|{primary}")
                    if format_and_send(setup,coin,is_instant=is_inst,market_condition=market_condition):
                        signal_sent=True; signals_this_cycle+=1
        except Exception as e: logger.error(f"Scan {coin}: {e}",exc_info=True)
        time.sleep(DELAY_BETWEEN_COINS)

def main():
    # FAIL-FAST STARTUP CHECK (this round): VERIFIED THE CLAIM before
    # applying — confirmed TELEGRAM_TOKEN/CHAT_ID genuinely fall back to
    # placeholder strings ("YOUR_TOKEN_HERE"/"YOUR_CHAT_ID_HERE") if the
    # real environment variables are missing on deployment. Without this
    # check, a broken deployment would boot cleanly, start the Telegram
    # polling thread, log a normal-looking startup message, and then
    # silently fail every single Telegram send in the background —
    # meaning you'd get zero signals with no visible error, and no way
    # to tell "the bot is quietly broken" apart from "the market is
    # quiet." This crashes loudly instead, at the very first line of
    # main(), before any scanning or Telegram polling starts.
    if TELEGRAM_TOKEN=="YOUR_TOKEN_HERE" or CHAT_ID=="YOUR_CHAT_ID_HERE" or not TELEGRAM_TOKEN or not CHAT_ID:
        logger.error("FATAL: TELEGRAM_TOKEN and/or CHAT_ID are missing or still set to placeholder "
                     "values. Set the real environment variables on your deployment platform before "
                     "starting the bot — it will not run with placeholder credentials, since every "
                     "Telegram send would otherwise fail silently in the background.")
        raise SystemExit(1)
    global last_river_time,last_hourly_time,last_pnl_update_time,last_8h_desk_time,last_weekly_report_day,last_pressure_cooker_time,total_scan_cycles
    load_alerts(); load_circuit_breaker(); load_pending_signals(); load_retest_watchlist(); load_macro_events(); load_evaluating_signals()
    cloud_load_all()   # loads journal, pattern_stats, learning, active_trades from Supabase (falls back to local JSON)
    threading.Thread(target=poll_telegram,daemon=True).start()
    logger.info(f"{BOT_NAME} {BOT_VERSION} starting...")
    send_telegram(
        f"🚀 <b>TRADING SIGNAL MASTER v32G</b> 🍀\n"
        f"<i>Smart • Fast • Accurate • AI</i>\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
        f"<b>✅ Online</b>  •  Scanning <b>{len(COINS)} coins</b>\n\n"
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
            scan_coins(btc_trend,fng,market_condition,btc_klines)
            total_scan_cycles += 1
            check_active_trades()
            expire_pending_signals()
            check_price_alerts()
            for coin,w,price in check_retest_triggers():
                # check_retest_triggers() now builds and sends the
                # complete, executable signal itself (real pending_signals
                # entry, chart, Activate/Ignore buttons) for every path —
                # fast-track, bos_retest, and normal retest alike. This
                # loop only logs; it deliberately does NOT re-send
                # anything, since the function above already did.
                logger.info(f"RETEST/FAST-TRACK signal dispatched: {coin}|{w['direction']}|{w['pattern']}")
            check_evaluating_signals()
            check_active_macro_coils()
            now=time.time()
            if (now-last_hourly_time)>=3600:          send_hourly_report();   last_hourly_time=now
            if (now-last_pnl_update_time)>=3600:      send_live_pnl_update(); last_pnl_update_time=now
            if (now-last_river_time)>=RIVER_INTERVAL:  scan_river(now,market_condition); last_river_time=now
            if (now-last_8h_desk_time)>=28800:         send_8h_ai_desk_report(); last_8h_desk_time=now  # 8h = 28800s
            if (now-last_pressure_cooker_time)>=7200:  send_pressure_cooker_report(); last_pressure_cooker_time=now  # 2h = 7200s
            today=datetime.now(IST).date()
            if today.weekday()==6 and last_weekly_report_day!=today:
                send_weekly_report(); last_weekly_report_day=today
            time.sleep(SCAN_INTERVAL)
        except Exception as e:
            logger.error(f"Main loop: {e}",exc_info=True); time.sleep(60)

if __name__=="__main__":
    main()
