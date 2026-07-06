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
NEWS_API_KEY   = os.getenv("NEWS_API_KEY", "")      # CryptoPanic API key (optional)

BINANCE_PRICE_URL   = "https://data-api.binance.vision/api/v3/ticker/price"
BINANCE_KLINE_URL   = "https://data-api.binance.vision/api/v3/klines"
BINANCE_AGG_URL     = "https://api.binance.com/api/v3/aggTrades"
BINANCE_FUNDING_URL = "https://fapi.binance.com/fapi/v1/fundingRate"
BINANCE_OI_URL      = "https://fapi.binance.com/futures/data/openInterestHist"

trade_lock = threading.Lock()
IST        = ZoneInfo("Asia/Kolkata")

COINS = list(dict.fromkeys([
    "BTC","ETH","BNB","SOL","XRP","DOGE","ADA","TRX","AVAX","SHIB",
    "DOT","LINK","BCH","NEAR","LTC","UNI","APT","ETC","HBAR","FIL",
    "ARB","VET","INJ","OP","ATOM","TIA","SUI","SEI","ALGO","EGLD",
    "FLOW","EOS","XTZ","AAVE","MKR","SNX","COMP","CRV","SUSHI","LDO",
    "CAKE","1INCH","DYDX","GMX","ENS","PENDLE","RNDR","FET","WLD","AR",
    "THETA","LPT","AKT","SAND","MANA","AXS","GALA","CHZ","APE","GMT",
    "ENJ","PEPE","WIF","JUP","PYTH","JTO","STRK","EIGEN","ETHFI","IO",
    "ONDO","CFX","METIS","ZETA","TRB","PIXEL","PORTAL","STPT","KAS","PIPPIN",
    "XAU","XAG","ZEC","LIT","TAO","PAXG","YFI","ICP","XMR","QNT",
    "DASH","NEO","ORCA"
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
    "BOS Breakout",
    # Sideways patterns
    "BB Lower Bounce","BB Upper Reject","Range Support","Range Resistance",
    "RSI Extreme Low","RSI Extreme High"
]}

last_update_id         = None
last_batch_time        = 0
last_river_time        = 0
last_hourly_time       = time.time()
last_pnl_update_time   = time.time() + 1800
last_weekly_report_day = None

SCAN_INTERVAL            = 90      # scan every 90 seconds (was 300 — 3x faster)
BATCH_INTERVAL           = 1800
RIVER_INTERVAL           = 900
MIN_SETUP_SCORE          = 90
MIN_PRIMARY_SCORE        = 90
INSTANT_SIGNAL_THRESHOLD = 97
MIN_PROFIT_TARGET        = 15.0
SIGNAL_EXPIRY_MINUTES    = 120
INSTANT_EXPIRY_MINUTES   = 30
DELAY_BETWEEN_COINS      = 0.10    # slightly faster between coins
MAX_SIGNALS_PER_CYCLE    = 3
MAX_ACTIVE_TRADES        = 5
ATR_SL_MULTIPLIER        = 2.5
ATR_TP_MULTIPLIER        = 5.0
MAX_DAILY_LOSSES         = 3
CIRCUIT_BREAKER_MIN_LOSS = -5.0
SCAN_CANDLE_TF           = "5m"    # 5m candles — 3x faster pattern detection vs 15m
PRE_SIGNAL_LOOKBACK      = 50      # candles for pre-signal detection
WHALE_TRADE_THRESHOLD    = 500000
ATR_VOLATILITY_RATIO     = 3.0
CONSEC_LOSS_SUSPEND      = 5
MIN_SIGNALS_TO_SUSPEND   = 15
SUSPEND_HOURS            = 12
ADX_MIN_TREND            = 21
ST_PERIOD                = 10
ST_MULTIPLIER            = 3.0
MIN_SL_PCT               = 0.02
DEAD_HOUR_START          = 2
DEAD_HOUR_END            = 7
BTC_CORRELATED           = ["ETH","BNB","SOL","AVAX","NEAR","APT","SUI"]
LEV_TIER_1               = ["BTC","ETH"]
LEV_TIER_2               = ["BNB","SOL","XRP","ADA","AVAX","DOT","LINK","LTC",
                             "NEAR","UNI","ATOM","APT","SUI","ARB","OP","INJ"]
LEV_TIER_3               = ["DOGE","SHIB","PEPE","WIF",
                             "APE","GMT","CHZ","GALA","SAND","MANA"]
BOT_VERSION = "v32G"
BOT_NAME    = "TRADING SIGNAL MASTER"
BOT_HEADER  = f"⚔️ {BOT_NAME} {BOT_VERSION}"

# ── Ghost of Yotei Theme ─────────────────────────────
YT_TOP = "刀 ━━━━━━━━━━━━━━━━━━━━━━━━━━━ 刀"
YT_BOT = "⛩ ━━━━━━━━━━━━━━━━━━━━━━━━━━━ ⛩"
YT_DIV = "─────────────────────────────"
YT_WIN = "🌸"; YT_LOSS = "🍂"

def _YH(title, icon=""):
    prefix = f"{icon}  " if icon else ""
    return YT_TOP+"\n   "+prefix+"<b>"+title+"</b>\n"+YT_BOT

def S(c="━",n=30): return c*n
def fmt_pnl(v):
    return f"{YT_WIN} <b>+{v:.2f}%</b>" if v>=0 else f"{YT_LOSS} <b>{v:.2f}%</b>"

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
            for key in ("timestamp","expires_at"):
                if isinstance(d.get(key),datetime):
                    dt=d[key]
                    if dt.tzinfo is None: dt=IST.localize(dt)
                    d[key]=dt.isoformat()
            # Strip non-JSON-serialisable values
            clean={}
            for k,v in d.items():
                if isinstance(v,(str,int,float,bool,list,dict,type(None))): clean[k]=v
                else: clean[k]=str(v)
            s[coin]=clean
        with open("pending_signals.json","w") as f: json.dump(s,f,indent=2)
        logger.info(f"Saved {len(s)} pending signals.")
    except Exception as e: logger.error(f"save_pending: {e}")

def load_pending_signals():
    global pending_signals
    try:
        if not os.path.exists("pending_signals.json"): return
        with open("pending_signals.json") as f: raw=f.read().strip()
        if not raw: return
        data=json.loads(raw)
        now=get_ist_datetime(); loaded=0
        for coin,sig in data.items():
            # Parse expires_at with timezone safety
            if sig.get("expires_at"):
                try:
                    exp=datetime.fromisoformat(sig["expires_at"])
                    if exp.tzinfo is None: exp=IST.localize(exp)
                    if now>exp: logger.info(f"Skip expired {coin}"); continue
                    sig["expires_at"]=exp
                except Exception as e:
                    logger.warning(f"expires_at {coin}: {e} — keeping")
                    sig["expires_at"]=None
            # Parse timestamp with timezone safety
            if sig.get("timestamp"):
                try:
                    ts=datetime.fromisoformat(sig["timestamp"])
                    if ts.tzinfo is None: ts=IST.localize(ts)
                    sig["timestamp"]=ts
                except Exception: sig["timestamp"]=get_ist_datetime()
            pending_signals[coin]=sig; loaded+=1
        logger.info(f"Loaded {loaded}/{len(data)} pending signals.")
        # Re-announce loaded signals with fresh buttons
        for coin,sig in list(pending_signals.items()):
            try:
                dirn=sig.get("direction","BUY")
                ep=sig.get("entry",sig.get("scan_price",0))
                tp=sig.get("tp",0); sl=sig.get("sl",0)
                exp=sig.get("expires_at")
                exp_str=exp.strftime("%I:%M %p IST") if isinstance(exp,datetime) else "N/A"
                dir_em="🌸 LONG" if dirn=="BUY" else "🍂 SHORT"
                reply_markup={"inline_keyboard":[[
                    {"text":"✅ Activate Trade","callback_data":f"ACTIVATE_{coin}"},
                    {"text":"❌ Ignore",        "callback_data":f"IGNORE_{coin}"}
                ]]}
                send_telegram(
                    f"🔄 <b>SIGNAL RESTORED: {coin}</b>\n"
                    f"{dir_em}  Entry: <code>{format_price(ep)}</code>\n"
                    f"TP: <code>{format_price(tp)}</code>  SL: <code>{format_price(sl)}</code>\n"
                    f"Expires: {exp_str}",
                    reply_markup=reply_markup
                )
            except Exception as e: logger.warning(f"Re-announce {coin}: {e}")
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
    payload={"chat_id":CHAT_ID,"text":text,"disable_web_page_preview":disable_web_page_preview}
    if parse_mode: payload["parse_mode"]=parse_mode  # omit if empty string
    if reply_markup: payload["reply_markup"]=reply_markup
    try:
        res=requests.post(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage",
                          json=payload,timeout=15)
        if res.status_code==200: return True
        logger.warning(f"Telegram [{res.status_code}]: {res.text[:200]}")
        # Retry as plain text if HTML parse error
        if "parse" in res.text.lower() or "can't parse" in res.text.lower() or "400" in str(res.status_code):
            payload2={"chat_id":CHAT_ID,"text":text,"disable_web_page_preview":True}
            if reply_markup: payload2["reply_markup"]=reply_markup
            res2=requests.post(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage",
                               json=payload2,timeout=15)
            return res2.status_code==200
        return False
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
    try:
        res=requests.get(BINANCE_PRICE_URL,params={"symbol":symbol},timeout=10)
        return float(res.json()["price"]) if res.status_code==200 else None
    except Exception as e:
        logger.warning(f"get_price {symbol}: {e}"); return None

def get_klines(symbol,interval,limit=100):
    try:
        res=requests.get(BINANCE_KLINE_URL,
                         params={"symbol":symbol,"interval":interval,"limit":limit},timeout=10)
        return res.json() if res.status_code==200 else []
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

def calculate_supertrend(klines,period=10,multiplier=3.0):
    if len(klines)<period+1: return None
    try:
        highs=[float(k[2]) for k in klines]; lows=[float(k[3]) for k in klines]
        closes=[float(k[4]) for k in klines]
        atr=calculate_atr(klines,period)
        hl2=(highs[-1]+lows[-1])/2
        upper=hl2+multiplier*atr; lower=hl2-multiplier*atr
        price=closes[-1]; prev=closes[-2] if len(closes)>1 else price
        if price>lower and prev>lower: return "BUY"
        if price<upper and prev<upper: return "SELL"
        return "BUY" if price>hl2 else "SELL"
    except Exception: return None

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


def get_orderbook_imbalance(symbol):
    """Audit Fix #2: Order book analysis — bid/ask imbalance and liquidity walls."""
    try:
        res = requests.get(
            "https://api.binance.com/api/v3/depth",
            params={"symbol": symbol, "limit": 20}, timeout=8
        )
        if res.status_code != 200: return None, "N/A"
        data = res.json()
        bids = [(float(p), float(q)) for p, q in data.get("bids", [])]
        asks = [(float(p), float(q)) for p, q in data.get("asks", [])]
        if not bids or not asks: return None, "N/A"
        bid_vol = sum(p * q for p, q in bids[:10])
        ask_vol = sum(p * q for p, q in asks[:10])
        total   = bid_vol + ask_vol
        if total == 0: return None, "N/A"
        imbalance = (bid_vol - ask_vol) / total  # +1 = all bids, -1 = all asks
        # Detect walls (single level > 20% of side total)
        bid_wall = any(p * q > bid_vol * 0.2 for p, q in bids[:10])
        ask_wall = any(p * q > ask_vol * 0.2 for p, q in asks[:10])
        label = ""
        if imbalance > 0.3:   label = "Strong Buy Pressure"
        elif imbalance > 0.1: label = "Mild Buy Pressure"
        elif imbalance < -0.3:label = "Strong Sell Pressure"
        elif imbalance < -0.1:label = "Mild Sell Pressure"
        else:                  label = "Balanced"
        if ask_wall and imbalance > 0: label += " ⚠️ Sell Wall"
        if bid_wall and imbalance < 0: label += " ⚠️ Buy Wall"
        return imbalance, label
    except Exception as e:
        logger.warning(f"orderbook {symbol}: {e}"); return None, "N/A"


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

    # ── Professional Bull Flag ──
    if detect_bull_flag(closes, highs, lows, vols, avg_vol) and alt_bull_ok:
        # BOS bonus
        score = 95 if ms["bos"] else 93
        p.append(("Bull Flag Break", score, "BUY"))

    # ── Professional Bear Flag ──
    if detect_bear_flag(closes, highs, lows, vols, avg_vol) and alt_bear_ok:
        score = 95 if ms["bos"] else 93
        p.append(("Bear Flag Break", score, "SELL"))

    # ── Breakout with structure confirmation ──
    if closes[-1] > max(highs[-20:-1]) and vols[-1] > avg_vol * 1.4:
        if alt_bull_ok:
            score = 93 if (ms["hh"] and ms["hl"]) else 90
            p.append(("Breakout", score, "BUY"))
    elif closes[-1] < min(lows[-20:-1]) and vols[-1] > avg_vol * 1.4:
        if alt_bear_ok:
            score = 93 if (ms["lh"] and ms["ll"]) else 90
            p.append(("Breakout", score, "SELL"))

    # ── Bullish Engulfing with structure ──
    if opens[-2] > closes[-2] and opens[-1] < closes[-2] and closes[-1] > opens[-2]:
        body_ratio = (closes[-1] - opens[-1]) / (opens[-2] - closes[-2]) if (opens[-2] - closes[-2]) > 0 else 0
        if body_ratio > 1.2 and alt_bull_ok:  # Must engulf by 20%
            score = 91 if ms_bias == "bullish" else 88
            p.append(("Bullish Engulfing", score, "BUY"))

    # ── Bearish Engulfing with structure ──
    elif opens[-2] < closes[-2] and opens[-1] > closes[-2] and closes[-1] < opens[-2]:
        body_ratio = (opens[-1] - closes[-1]) / (closes[-2] - opens[-2]) if (closes[-2] - opens[-2]) > 0 else 0
        if body_ratio > 1.2 and alt_bear_ok:
            score = 91 if ms_bias == "bearish" else 88
            p.append(("Bearish Engulfing", score, "SELL"))

    # ── EMA Trend with structure alignment ──
    if ema20 and ema50:
        if price > ema20 > ema50 and alt_bull_ok:
            score = 90 if ms_bias == "bullish" else 87
            p.append(("EMA Trend", score, "BUY"))
        elif price < ema20 < ema50 and alt_bear_ok:
            score = 90 if ms_bias == "bearish" else 87
            p.append(("EMA Trend", score, "SELL"))

    # ── Pullback to 20 EMA ──
    if ema20 and abs(price - ema20) / ema20 < 0.008:
        if price > ema50 and alt_bull_ok and ms_bias == "bullish":
            p.append(("Pullback to 20 EMA", 88, "BUY"))
        elif price < ema50 and alt_bear_ok and ms_bias == "bearish":
            p.append(("Pullback to 20 EMA", 88, "SELL"))

    # ── RSI Reversal (extreme only) ──
    if rsi < 28 and alt_bull_ok:   p.append(("RSI Reversal", 85, "BUY"))
    elif rsi > 72 and alt_bear_ok: p.append(("RSI Reversal", 85, "SELL"))

    # ── Momentum Surge ──
    mom = (closes[-1] - closes[-4]) / closes[-4] * 100 if len(closes) > 4 else 0
    if mom > 3.5 and vols[-1] > avg_vol * 1.2 and alt_bull_ok:
        p.append(("Momentum Surge", 90, "BUY"))
    elif mom < -3.5 and vols[-1] > avg_vol * 1.2 and alt_bear_ok:
        p.append(("Momentum Surge", 90, "SELL"))

    # ── Volume Spike ──
    if vols[-1] > avg_vol * 3.0:
        direction = "BUY" if closes[-1] > opens[-1] else "SELL"
        if (direction == "BUY" and alt_bull_ok) or (direction == "SELL" and alt_bear_ok):
            p.append(("Volume Spike", 88, direction))

    # ── Support Bounce with structure ──
    if price <= sup * 1.008 and closes[-1] > opens[-1] and alt_bull_ok:
        score = 92 if ms_bias == "bullish" else 88
        p.append(("Support Bounce", score, "BUY"))

    # ── Resistance Rejection with structure ──
    if price >= res * 0.992 and closes[-1] < opens[-1] and alt_bear_ok:
        score = 92 if ms_bias == "bearish" else 88
        p.append(("Resistance Rejection", score, "SELL"))

    # ── Professional Double Bottom ──
    if detect_double_bottom_pro(highs, lows, closes, vols, price, avg_vol) and alt_bull_ok:
        p.append(("Double Bottom", 93, "BUY"))

    # ── Professional Double Top ──
    if detect_double_top_pro(highs, lows, closes, vols, price, avg_vol) and alt_bear_ok:
        p.append(("Double Top", 93, "SELL"))

    # ── Volume Breakout ──
    if price > res and vols[-1] > avg_vol * 2.2 and alt_bull_ok:
        score = 94 if ms["bos"] else 91
        p.append(("Volume Breakout", score, "BUY"))

    # ── BOS Signal (pure structure break) ──
    if ms["bos"] and not ms["choch"]:
        if ms_bias == "bullish" and alt_bull_ok:
            p.append(("BOS Breakout", 92, "BUY"))
        elif ms_bias == "bearish" and alt_bear_ok:
            p.append(("BOS Breakout", 92, "SELL"))

    return p

def is_in_zone(price,direction,zones):
    key="demand" if direction=="BUY" else "supply"
    for zone in zones.get(key,[])[-5:]:
        if zone["low"]*0.995<=price<=zone["high"]*1.005:
            return True,f"{format_price(zone['low'])}-{format_price(zone['high'])}"
    return False,""

def detect_market_condition(btc_price, btc_klines):
    """
    Returns: 'bull', 'bear', 'sideways'
    Uses ADX + Bollinger Band width + EMA for reliable detection.
    """
    try:
        closes=[float(k[4]) for k in btc_klines]
        if len(closes)<50: return "sideways"
        e20=calculate_ema(closes,20); e50=calculate_ema(closes,50)
        adx=calculate_adx(btc_klines)

        # Bollinger Band width — narrow = sideways
        std=( sum((c-e20)**2 for c in closes[-20:])/20 )**0.5 if e20 else 0
        bb_upper=e20+2*std; bb_lower=e20-2*std
        bb_width=((bb_upper-bb_lower)/e20*100) if e20>0 else 5

        # Strong trend conditions
        if adx>=25 and e20 and e50:
            if e20>e50*1.015 and btc_price>e20: return "bull"
            if e20<e50*0.985 and btc_price<e20: return "bear"

        # Sideways: ADX weak OR BB narrow
        if adx<22 or bb_width<3.5: return "sideways"

        # Moderate trend
        if e20 and e50:
            if btc_price>e50: return "bull"
            if btc_price<e50: return "bear"
        return "sideways"
    except Exception: return "sideways"


def is_market_sideways(symbol, klines):
    """
    Per-coin sideways check. Returns True if the coin itself is ranging.
    Used to switch signal logic for individual coins.
    """
    try:
        closes=[float(k[4]) for k in klines]
        if len(closes)<30: return True
        adx=calculate_adx(klines)
        e20=calculate_ema(closes,20)
        std=(sum((c-e20)**2 for c in closes[-20:])/20)**0.5 if e20 else 0
        bb_width=((4*std)/e20*100) if e20>0 else 5
        return adx<22 or bb_width<3.0
    except Exception: return True


def get_sideways_signals(symbol, klines, price):
    """
    Sideways-specific signals: range trading, BB bounces, RSI mean reversion.
    Uses SHORTER TP targets (5-8% price move) since price is range-bound.
    Returns list of (pattern, score, direction) tuples.
    """
    signals=[]
    try:
        closes=[float(k[4]) for k in klines]
        highs=[float(k[2]) for k in klines]
        lows=[float(k[3]) for k in klines]
        if len(closes)<30: return signals
        e20=calculate_ema(closes,20)
        rsi=calculate_rsi(closes)
        std=(sum((c-e20)**2 for c in closes[-20:])/20)**0.5 if e20 else 0
        bb_upper=e20+2*std; bb_lower=e20-2*std
        bb_mid=e20

        # 1. Bollinger Band bounce — price touches lower band, RSI oversold
        if price<=bb_lower*1.005 and rsi<38:
            signals.append(("BB Lower Bounce",88,"BUY"))

        # 2. Bollinger Band rejection — price touches upper band, RSI overbought
        if price>=bb_upper*0.995 and rsi>62:
            signals.append(("BB Upper Reject",88,"SELL"))

        # 3. Range support bounce — near 20-bar low, RSI neutral-low
        range_low=min(lows[-20:]); range_high=max(highs[-20:])
        range_size=(range_high-range_low)/range_low*100 if range_low>0 else 0
        if range_size>2:  # only if there's a real range
            if price<=range_low*1.01 and rsi<42:
                signals.append(("Range Support",86,"BUY"))
            if price>=range_high*0.99 and rsi>58:
                signals.append(("Range Resistance",86,"SELL"))

        # 4. RSI mean reversion from extremes
        if rsi<25:  signals.append(("RSI Extreme Low",84,"BUY"))
        if rsi>75:  signals.append(("RSI Extreme High",84,"SELL"))

    except Exception as e: logger.warning(f"sideways signals {symbol}: {e}")
    return signals

def is_good_trading_session():
    hour=datetime.now(IST).hour
    if DEAD_HOUR_START<=hour<DEAD_HOUR_END:
        logger.info(f"Dead session {hour}:xx IST"); return False
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

def get_signal_grade(score, vol_strength, trend_strength, tf_score, rsi_15m, rsi_1h, rsi_4h,
                     funding_ok, st_ok, vwap_ok, zone_ok, adx_val, bos=False, ms_aligned=False):
    """
    Upgraded scoring — replaces whale/OI/orderbook with:
    - Volume Profile strength (real volume vs 20-bar avg)
    - Multi-timeframe RSI alignment (15m + 1h + 4h)
    - Trend Strength (ADX-based)
    - Funding rate direction
    - Market Structure (BOS, structure alignment)
    """
    breakdown=[]; pts=0

    # Score base points
    if score>=97:    pts+=3; breakdown.append(("🎯 Score ≥97",       3))
    elif score>=93:  pts+=2; breakdown.append(("🎯 Score ≥93",       2))
    elif score>=88:  pts+=1; breakdown.append(("🎯 Score ≥88",       1))
    else:                    breakdown.append(("🎯 Score",            0))

    # Volume Profile — is real money flowing?
    if vol_strength>=2.0:   pts+=3; breakdown.append(("📊 Volume 2x+",     3))
    elif vol_strength>=1.5: pts+=2; breakdown.append(("📊 Volume 1.5x",    2))
    elif vol_strength>=1.2: pts+=1; breakdown.append(("📊 Volume 1.2x",    1))
    else:                            breakdown.append(("📊 Volume",         0))

    # Multi-TF RSI alignment — all timeframes agree
    rsi_bull = rsi_15m>50 and rsi_1h>50 and rsi_4h>50
    rsi_bear = rsi_15m<50 and rsi_1h<50 and rsi_4h<50
    if rsi_bull or rsi_bear:
        pts+=3; breakdown.append(("📈 RSI 3-TF Aligned",  3))
    elif (rsi_15m>50)==(rsi_1h>50):
        pts+=1; breakdown.append(("📈 RSI 2-TF Aligned",  1))
    else:                            breakdown.append(("📈 RSI Conflicted",  0))

    # Trend Strength (ADX)
    if adx_val>=40:   pts+=3; breakdown.append(("💪 ADX Very Strong", 3))
    elif adx_val>=30: pts+=2; breakdown.append(("💪 ADX Strong",      2))
    elif adx_val>=22: pts+=1; breakdown.append(("💪 ADX Moderate",    1))
    else:                      breakdown.append(("💪 ADX Weak",        0))

    # TF alignment
    if tf_score==3:   pts+=2; breakdown.append(("📡 4h+1h Aligned",   2))
    elif tf_score==2: pts+=1; breakdown.append(("📡 4h Aligned",      1))
    else:                      breakdown.append(("📡 TF Weak",         0))

    # SuperTrend
    if st_ok:         pts+=2; breakdown.append(("🌀 SuperTrend ✓✓",  2))
    else:                      breakdown.append(("🌀 SuperTrend",      0))

    # VWAP
    if vwap_ok:       pts+=1; breakdown.append(("💧 VWAP OK",         1))
    else:                      breakdown.append(("💧 VWAP",            0))

    # Supply/Demand Zone
    if zone_ok:       pts+=2; breakdown.append(("📍 S/D Zone Hit",    2))
    else:                      breakdown.append(("📍 S/D Zone",        0))

    # Funding rate
    if funding_ok:    pts+=1; breakdown.append(("💸 Funding Aligned", 1))
    else:                      breakdown.append(("💸 Funding",         0))

    # Market structure
    if bos:           pts+=2; breakdown.append(("🔥 BOS Confirmed",   2))
    elif ms_aligned:  pts+=1; breakdown.append(("🏗️ Structure OK",    1))
    else:                      breakdown.append(("🏗️ Structure",       0))

    # Grade thresholds (max 22 pts)
    max_pts=22
    if pts>=18:  grade="Grade A+ 🍀"
    elif pts>=14: grade="Grade A 🍀"
    elif pts>=10: grade="Grade B"
    else:         grade="Grade C"
    return grade, pts, breakdown, max_pts

def get_position_size_pct(grade):
    g=grade[0] if isinstance(grade,tuple) else grade
    if "A+" in g: return 10.0
    elif "A 🍀" in g: return 7.0
    elif "B" in g: return 5.0
    else:          return 3.0

def is_volume_confirmed(klines):
    vols=[float(k[5]) for k in klines]
    # Require 1.5x average — filters out low-conviction moves
    return len(vols)>=20 and vols[-1]>sum(vols[-20:])/20*1.5

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

def get_funding_rate(symbol):
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
    try:
        res=requests.get(BINANCE_OI_URL,params={"symbol":symbol,"period":"15m","limit":5},timeout=10)
        if res.status_code==200 and len(res.json())>=2:
            d=res.json()
            return float(d[-1]["sumOpenInterest"])>float(d[-2]["sumOpenInterest"])
        return None
    except Exception as e:
        logger.warning(f"OI {symbol}: {e}"); return None

def has_whale_activity(symbol):
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

def get_timeframe_score(symbol,direction):
    di=1 if direction=="BUY" else -1
    h4=get_htf_trend(symbol,"4h"); h1=get_htf_trend(symbol,"1h")
    if h4!=0 and h4!=di: return -1
    score=0
    if h4==di: score+=2
    if h1==di: score+=1
    return score

def get_structure_sl(klines,direction,entry,atr):
    lows=[float(k[3]) for k in klines[-20:]]; highs=[float(k[2]) for k in klines[-20:]]
    min_dist=entry*MIN_SL_PCT
    if direction=="BUY":
        sl=min(min(lows)*0.998,entry-atr*ATR_SL_MULTIPLIER)
        return min(sl,entry-min_dist)
    sl=max(max(highs)*1.002,entry+atr*ATR_SL_MULTIPLIER)
    return max(sl,entry+min_dist)

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
    stats=pattern_stats.get(pattern_name,{})
    signals=stats.get("signals",0)
    if signals<5: return base_score
    overall_wr=(stats["wins"]/signals)*100
    mc_wr=stats.get(f"{market_condition}_wr",overall_wr)
    weight=stats.get("weight",1.0)
    if signals>=20:   pf=0.6
    elif signals>=10: pf=0.4
    else:             pf=0.2
    adjusted=(base_score*(1-pf)+mc_wr*pf)*weight
    return min(round(adjusted,1),99.0)

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
    icon = f"{emoji}  " if emoji else ""
    return YT_TOP+"\n   "+icon+"<b>"+title+"</b>\n"+YT_BOT

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
           f"  └─────────────────────────────┘\n")
    # If BTC trend, also show all active coin levels
    if coin=="BTC" and active_trades:
        text+=f"\n  {YT_DIV}\n  ⚔️ <b>Active Coin Levels</b>\n\n"
        for ac,t in active_trades.items():
            ap=get_price(t.get("symbol",ac+"USDT"))
            if not ap: continue
            a_sup,a_res,_=get_sr_levels(t.get("symbol",ac+"USDT"))
            a_res_d=abs(a_res-ap)/ap*100 if a_res>0 else 0
            a_sup_d=abs(ap-a_sup)/ap*100 if a_sup>0 else 0
            em=YT_WIN if t.get("direction")=="BUY" else YT_LOSS
            text+=(f"  {em} <b>{ac}</b>  <code>{format_price(ap)}</code>\n"
                   f"  🚧 Res: <code>{format_price(a_res)}</code> +{a_res_d:.2f}%\n"
                   f"  🛡 Sup: <code>{format_price(a_sup)}</code> -{a_sup_d:.2f}%\n\n")
    text+=f"  🕐 {get_ist_time()}"
    return text

def cmd_market():
    btc=get_price("BTCUSDT"); eth=get_price("ETHUSDT"); sol=get_price("SOLUSDT")
    bnb=get_price("BNBUSDT"); xrp=get_price("XRPUSDT")
    btc_klines=get_klines("BTCUSDT","1h",50); btc_trend="N/A"
    if btc_klines and len(btc_klines)>=50:
        closes=[float(k[4]) for k in btc_klines]
        e20=calculate_ema(closes,20); e50=calculate_ema(closes,50)
        btc_trend=get_trend_label(e20,e50,btc,"1h") if btc else "N/A"
    scan_list=["BTC","ETH","BNB","SOL","XRP","ADA","AVAX","DOT","LINK","NEAR",
               "INJ","SUI","APT","ARB","OP","ATOM","PEPE","WIF","DOGE"]
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
            symbol=coin+"USDT"; price=get_price(symbol); klines=get_klines(symbol,SCAN_CANDLE_TF,100)
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
            avg_vol_20 = sum(vols[-20:]) / 20
            curr_vol   = vols[-1]
            vol_ratio  = curr_vol / avg_vol_20 if avg_vol_20 > 0 else 0
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
        tp=entry+atr_1h*ATR_TP_MULTIPLIER if best["direction"]=="BUY" else entry-atr_1h*ATR_TP_MULTIPLIER
        ms_b=detect_market_structure(klines_15m)
        adx_val=calculate_adx(klines_15m)
        closes=[float(k[4]) for k in klines_15m]
        rsi_15m_b=calculate_rsi(closes)
        kl1h_b=get_klines(best["symbol"],"1h",50)
        kl4h_b=get_klines(best["symbol"],"4h",50)
        rsi_1h_b=calculate_rsi([float(k[4]) for k in kl1h_b]) if kl1h_b else rsi_15m_b
        rsi_4h_b=calculate_rsi([float(k[4]) for k in kl4h_b]) if kl4h_b else rsi_15m_b
        vols_b=[float(k[5]) for k in klines_15m]
        avg_vol_b=sum(vols_b[-20:])/20 if len(vols_b)>=20 else 1
        vol_str_b=vols_b[-1]/avg_vol_b if avg_vol_b>0 else 1.0
        vwap_b=calculate_vwap(klines_15m)
        vwap_ok_b=(entry>vwap_b if best["direction"]=="BUY" else entry<vwap_b) if vwap_b else False
        zones_b=detect_supply_demand_zones(klines_15m)
        zone_ok_b,_=is_in_zone(entry,best["direction"],zones_b)
        st_15m_b=calculate_supertrend(klines_15m,ST_PERIOD,ST_MULTIPLIER)
        st_ok_b=(st_15m_b==best["direction"])
        grade,pts,_,_=get_signal_grade(
            best["score"],vol_str_b,adx_val,best["tf_score"],
            rsi_15m_b,rsi_1h_b,rsi_4h_b,True,st_ok_b,vwap_ok_b,
            zone_ok_b,adx_val,ms_b["bos"],ms_b["bias"] in ("bullish","bearish")
        )
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

def get_sr_levels(symbol):
    klines=get_klines(symbol,"4h",50)
    if not klines or len(klines)<5: return 0,0,0
    highs=[float(k[2]) for k in klines]; lows=[float(k[3]) for k in klines]
    closes=[float(k[4]) for k in klines]
    pivot=(highs[-2]+lows[-2]+closes[-2])/3
    r1=2*pivot-lows[-2]; s1=2*pivot-highs[-2]
    ms=detect_market_structure(klines)
    if ms["swing_high"]>0: r1=(r1+ms["swing_high"])/2
    if ms["swing_low"]>0:  s1=(s1+ms["swing_low"])/2
    return s1,r1,pivot

def cmd_trade_suggestions():
    if not active_trades:
        return (_H("BATTLE COUNSEL","🔮")+"\n\n"
                f"  🌙 No open battles to counsel.\n\n"
                f"  🕐 {get_ist_time()}")
    text=_H("BATTLE COUNSEL","🔮")+"\n\n"
    for coin,t in active_trades.items():
        symbol=t.get("symbol",coin+"USDT")
        price=get_price(symbol)
        if not price: continue
        dirn=t.get("direction","BUY"); entry=t["entry"]
        tp=t["tp"]; sl=t["sl"]; lev=t.get("leverage",1)
        if dirn=="BUY": pnl=((price-entry)/entry)*100*lev
        else:           pnl=((entry-price)/entry)*100*lev
        dist_tp=abs(tp-price)/price*100
        dist_sl=abs(price-sl)/price*100
        tp_pct=abs(tp-entry)/entry*100
        progress=pnl/tp_pct*100 if tp_pct>0 else 0
        klines=get_klines(symbol,"1h",50); rsi=50; trend_label="N/A"; mom=0
        if klines and len(klines)>3:
            closes=[float(k[4]) for k in klines]
            rsi=calculate_rsi(closes)
            e20=calculate_ema(closes,20); e50=calculate_ema(closes,50)
            trend_label=get_trend_label(e20,e50,price,"1h")
            mom=(closes[-1]-closes[-4])/closes[-4]*100 if len(closes)>=4 else 0
        sup,res,_=get_sr_levels(symbol)
        is_near_tp=dist_tp<tp_pct*0.1
        trend_favours=("Up" in trend_label and dirn=="BUY") or ("Down" in trend_label and dirn=="SELL")
        rsi_extreme=(rsi>72 and dirn=="BUY") or (rsi<28 and dirn=="SELL")
        mom_fading=(mom<-1.5 and dirn=="BUY") or (mom>1.5 and dirn=="SELL")
        near_bad_level=((dirn=="BUY" and res>0 and abs(price-res)/price<0.015) or
                        (dirn=="SELL" and sup>0 and abs(price-sup)/price<0.015))
        is_near_sl=dist_sl<abs(entry-sl)/entry*100*0.15
        if pnl>=0 and is_near_tp:
            suggestion="🌸 TAKE PROFIT — target almost reached"
            detail=f"Price is {dist_tp:.1f}% from target."
        elif pnl>0 and (rsi_extreme or mom_fading or near_bad_level):
            suggestion="⚠️ WATCH OUT — momentum fading"
            detail="RSI extreme" if rsi_extreme else "Momentum reversing" if mom_fading else "Near key level"
        elif pnl<0 and is_near_sl:
            suggestion="🍂 EXIT NOW — SL almost hit"
            detail=f"Price is {dist_sl:.1f}% from your stop."
        elif pnl<0 and not trend_favours:
            suggestion="🌙 REVERSE RISK — trend against you"
            detail=f"1h trend: {trend_label}"
        elif trend_favours and not rsi_extreme and pnl>=0:
            suggestion="⚔️ HOLD — trend aligned"
            detail=f"{progress:.0f}% of the way to target."
        else:
            suggestion="📜 HOLD — no strong signal to act"
            detail="Market undecided. Maintain SL."
        dirn_em=YT_WIN+" LONG" if dirn=="BUY" else YT_LOSS+" SHORT"
        text+=(f"  {YT_DIV}\n"
               f"  🪙 <b>{coin}</b>  {dirn_em}  •  {fmt_pnl(pnl)}\n\n"
               f"  {suggestion}\n  ▸ {detail}\n\n"
               f"  ▸ Progress: {progress:.0f}%  RSI: {rsi:.1f}  Mom: {mom:+.2f}%\n"
               f"  ▸ Trend(1h): {trend_label}\n")
        if res>0: text+=f"  🚧 Resistance: <code>{format_price(res)}</code>\n"
        if sup>0: text+=f"  🛡 Support: <code>{format_price(sup)}</code>\n"
        text+="\n"
    text+=f"  {YT_BOT}\n  🕐 {get_ist_time()}"
    return text

watch_alerts_sent = {}   # coin -> timestamp of last watch alert

def check_and_send_watch_alert(coin, symbol, price, klines, direction):
    """Pre-signal Watch Alert — fires 5-15 min before actual signal."""
    global watch_alerts_sent
    if not klines or len(klines)<30: return
    now=get_ist_datetime()
    if coin in watch_alerts_sent:
        if (now-watch_alerts_sent[coin]).total_seconds()<1800: return
    closes=[float(k[4]) for k in klines]; highs=[float(k[2]) for k in klines]
    lows=[float(k[3]) for k in klines]; vols=[float(k[5]) for k in klines]
    avg_vol=sum(vols[-20:])/20 if len(vols)>=20 else 1
    rsi=calculate_rsi(closes); e20=calculate_ema(closes,20)
    std=(sum((c-e20)**2 for c in closes[-20:])/20)**0.5 if e20 else 0
    bb_upper=e20+2*std; bb_lower=e20-2*std
    adx=calculate_adx(klines); vol_ratio=vols[-1]/avg_vol if avg_vol>0 else 0
    recent_high=max(highs[-20:]); recent_low=min(lows[-20:])
    alert=None; dir_em="🟢 LONG" if direction=="BUY" else "🔴 SHORT"
    if (price>=recent_high*0.985 and direction=="SELL" and vol_ratio>=1.2):
        alert=f"📍 Approaching resistance <code>{format_price(recent_high)}</code> — vol {vol_ratio:.1f}x"
    elif (price<=recent_low*1.015 and direction=="BUY" and vol_ratio>=1.2):
        alert=f"📍 Approaching support <code>{format_price(recent_low)}</code> — vol {vol_ratio:.1f}x"
    elif rsi<38 and direction=="BUY":
        alert=f"📈 RSI oversold ({rsi:.0f}) — reversal forming"
    elif rsi>62 and direction=="SELL":
        alert=f"📉 RSI overbought ({rsi:.0f}) — reversal forming"
    elif price<=bb_lower*1.008 and direction=="BUY":
        alert=f"🎯 Near BB lower <code>{format_price(bb_lower)}</code> — watch for bounce"
    elif price>=bb_upper*0.992 and direction=="SELL":
        alert=f"🎯 Near BB upper <code>{format_price(bb_upper)}</code> — watch for rejection"
    elif vol_ratio>=2.5 and adx<25:
        alert=f"⚡ Volume spike {vol_ratio:.1f}x in quiet market — move incoming"
    if alert:
        watch_alerts_sent[coin]=now
        send_telegram(
            f"👁 <b>WATCH ALERT — {coin}</b>\n"
            f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
            f"  🪙 <b>{coin}</b>   {dir_em}\n"
            f"  💰 Price : <code>{format_price(price)}</code>\n\n"
            f"  {alert}\n\n"
            f"  RSI:{rsi:.0f}  ADX:{adx:.0f}  Vol:{vol_ratio:.1f}x\n"
            f"  ⏳ Signal may fire in 5-15 min — be ready!\n"
            f"  🕐 {get_ist_time()}"
        )
        logger.info(f"WATCH ALERT: {coin}|{direction}")

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

def format_and_send(setup,coin,is_river=False,is_instant=False,market_condition="bull"):
    global sent_coins,coin_cooldowns
    if check_circuit_breaker(): return False
    if not is_good_trading_session(): return False
    live_price=get_price(setup["symbol"])
    if not live_price: return False
    entry=live_price
    if abs(entry-setup["scan_price"])/setup["scan_price"]>0.02:
        logger.info(f"{coin} rejected - drifted"); return False
    klines_15m=get_klines(setup["symbol"],SCAN_CANDLE_TF,100)
    klines_1h=get_klines(setup["symbol"],"1h",50)
    if not klines_15m: return False
    closes=[float(x[4]) for x in klines_15m]
    atr_1h=calculate_atr(klines_1h) if len(klines_1h)>=15 else calculate_atr(klines_15m)
    atr_pct=(atr_1h/entry)*100 if entry>0 else 0
    vol_ok=is_volume_confirmed(klines_15m)
    rsi_ok=is_rsi_valid(closes,setup["direction"])
    funding_ok=is_funding_favorable(setup["symbol"],setup["direction"])
    if not vol_ok:
        logger.info(f"{coin} rejected - volume"); return False
    if not rsi_ok:
        logger.info(f"{coin} rejected - RSI"); return False
    if not is_volatility_normal(klines_15m):
        logger.info(f"{coin} rejected - volatility"); return False
    if not funding_ok:
        logger.info(f"{coin} rejected - funding"); return False
    st_15m=calculate_supertrend(klines_15m,ST_PERIOD,ST_MULTIPLIER)
    st_1h=calculate_supertrend(klines_1h,ST_PERIOD,ST_MULTIPLIER) if klines_1h else st_15m
    is_sideways_signal=setup.get("sideways_mode",False)
    if st_15m != setup["direction"] and not is_sideways_signal:
        logger.info(f"{coin} rejected - SuperTrend 15m ({st_15m})"); return False
    elif st_15m != setup["direction"] and is_sideways_signal:
        # For sideways: only allow if RSI confirms extreme reversal
        rsi_check=calculate_rsi([float(k[4]) for k in klines_15m])
        if setup["direction"]=="BUY" and rsi_check>35:
            logger.info(f"{coin} sideways BUY rejected - ST opposes and RSI {rsi_check:.0f} not oversold enough"); return False
        elif setup["direction"]=="SELL" and rsi_check<65:
            logger.info(f"{coin} sideways SELL rejected - ST opposes and RSI {rsi_check:.0f} not overbought enough"); return False
        logger.info(f"{coin} sideways signal — ST opposing but RSI {rsi_check:.0f} confirms extreme — allowing")
    st_ok=(st_15m==setup["direction"]) and (st_1h==setup["direction"])
    vwap=calculate_vwap(klines_15m); vwap_ok=False; vwap_label="N/A"
    if vwap:
        if setup["direction"]=="BUY" and entry>vwap:    vwap_ok=True; vwap_label=f"Above {format_price(vwap)}"
        elif setup["direction"]=="SELL" and entry<vwap: vwap_ok=True; vwap_label=f"Below {format_price(vwap)}"
        else: vwap_label=f"{'Below' if setup['direction']=='BUY' else 'Above'} {format_price(vwap)}"
    zones=detect_supply_demand_zones(klines_15m)
    zone_ok,zone_label=is_in_zone(entry,setup["direction"],zones)
    div=detect_rsi_divergence(closes)
    adx_val=calculate_adx(klines_15m)
    tf_score=setup.get("tf_score",get_timeframe_score(setup["symbol"],setup["direction"]))
    ms = detect_market_structure(klines_15m)
    highs_15m=[float(k[2]) for k in klines_15m]; lows_15m=[float(k[3]) for k in klines_15m]
    res = ms["swing_high"] if ms["swing_high"] > 0 else max(highs_15m[-30:-1])
    sup = ms["swing_low"]  if ms["swing_low"]  > 0 else min(lows_15m[-30:-1])

    # Multi-timeframe RSI
    rsi_15m=calculate_rsi(closes)
    closes_1h=[float(k[4]) for k in klines_1h] if klines_1h else closes
    rsi_1h=calculate_rsi(closes_1h)
    klines_4h=get_klines(setup["symbol"],"4h",50)
    closes_4h=[float(k[4]) for k in klines_4h] if klines_4h else closes_1h
    rsi_4h=calculate_rsi(closes_4h)

    # Volume profile strength
    vols=[float(k[5]) for k in klines_15m]
    avg_vol=sum(vols[-20:])/20 if len(vols)>=20 else 1
    vol_strength=vols[-1]/avg_vol if avg_vol>0 else 1.0

    # Compute grade with new signature
    grade,pts,breakdown,max_pts=get_signal_grade(
        setup["setup_score"], vol_strength, adx_val, tf_score,
        rsi_15m, rsi_1h, rsi_4h, funding_ok, st_ok, vwap_ok,
        zone_ok, adx_val, ms["bos"], ms["bias"] in ("bullish","bearish")
    )
    lev=get_smart_leverage(setup["symbol"],atr_pct,setup["setup_score"],grade)
    sl=get_structure_sl(klines_15m,setup["direction"],entry,atr_1h)
    tp=entry+atr_1h*ATR_TP_MULTIPLIER if setup["direction"]=="BUY" else entry-atr_1h*ATR_TP_MULTIPLIER
    profit_target=(abs(tp-entry)/entry)*100*lev
    if profit_target<MIN_PROFIT_TARGET:
        risk=abs(tp-entry)/entry
        if risk>0:
            needed=int(MIN_PROFIT_TARGET/(risk*100))+1
            if needed<=20: lev=needed; profit_target=(abs(tp-entry)/entry)*100*lev
            else: return False
    setup["leverage"]=lev
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
    is_sideways_signal=setup.get("sideways_mode",False)
    if is_sideways_signal: sig_type="🔀 SIDEWAYS SIGNAL"; cond_em="Sideways ➡️"
    elif is_instant: sig_type="⚡ INSTANT SIGNAL"; cond_em={"bull":"Bullish 📈","bear":"Bearish 📉","sideways":"Sideways ➡️"}.get(market_condition,"")
    elif is_river:   sig_type="🌊 RIVER SIGNAL";   cond_em={"bull":"Bullish 📈","bear":"Bearish 📉","sideways":"Sideways ➡️"}.get(market_condition,"")
    else:            sig_type="🔥 VERIFIED SETUP"; cond_em={"bull":"Bullish 📈","bear":"Bearish 📉","sideways":"Sideways ➡️"}.get(market_condition,"")
    dir_arrow="🟢 LONG  ▲" if setup["direction"]=="BUY" else "🔴 SHORT ▼"
    grade_em="🏆" if "A+" in grade else "🍀" if " A" in grade else "🥈" if "B" in grade else "🥉"
    cond_icon="📈" if market_condition=="bull" else "📉" if market_condition=="bear" else "➡️"

    # ASCII chart — visual price diagram
    def ascii_chart(entry, tp, sl, direction):
        levels=sorted([tp,entry,sl],reverse=True)
        chart_h=8
        p_max=max(tp,entry,sl)*1.002; p_min=min(tp,entry,sl)*0.998
        p_range=p_max-p_min if p_max>p_min else 1
        def pos(p): return int((p_max-p)/p_range*(chart_h-1))
        tp_row=pos(tp); entry_row=pos(entry); sl_row=pos(sl)
        lines=[]
        for r in range(chart_h):
            bar="│"
            if r==tp_row:    bar="🟢"; label=f" TP  {format_price(tp)}"
            elif r==entry_row: bar="🔵"; label=f" ENT {format_price(entry)}"
            elif r==sl_row:  bar="🔴"; label=f" SL  {format_price(sl)}"
            else: label=""
            lines.append(f"  {bar}{label}")
        return "\n".join(lines)

    chart=ascii_chart(entry,tp,sl,setup["direction"])

    # Score bars
    filled=min(int(setup["setup_score"]/10),10)
    score_bar="█"*filled+"░"*(10-filled)
    grade_filled=min(int(pts/max_pts*10),10)
    grade_bar="█"*grade_filled+"░"*(10-grade_filled)

    # Funding rate label
    funding_label="✅ Aligned" if funding_ok else "⚠️ Against"
    # Get funding rate value
    try:
        fr=requests.get(f"https://fapi.binance.com/fapi/v1/premiumIndex?symbol={setup['symbol']}",timeout=5)
        fr_val=float(fr.json().get("lastFundingRate",0))*100 if fr.status_code==200 else 0
        funding_detail=f"{fr_val:+.4f}%"
    except Exception: funding_detail="N/A"

    msg  = f"{'⚡' if is_instant else '🔀' if is_sideways_signal else '🔥'} <b>{sig_type}</b>\n"
    msg += f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
    msg += f"  🪙 <b>{coin}</b>  {dir_arrow}  🔧 <b>{lev}x Leverage</b>\n"
    msg += f"  {grade_em} <b>{grade}</b>  •  {pts}/{max_pts} pts\n"
    msg += f"  [{grade_bar}]\n"
    msg += f"  📊 Score: <b>{setup['setup_score']:.0f}/100</b>  [{score_bar}]\n"
    msg += f"  {cond_icon} Market: <b>{cond_em}</b>\n\n"

    # ASCII price chart
    msg += f"  ┌── PRICE MAP ────────────────┐\n"
    msg += chart+"\n"
    msg += f"  └─────────────────────────────┘\n\n"

    msg += f"  ┌── TRADE LEVELS ─────────────┐\n"
    msg += f"  │  💰 Entry      <code>{format_price(entry)}</code>\n"
    msg += f"  │  🎯 Target     <code>{format_price(tp)}</code>  <i>+{tp_pct:.2f}%</i>\n"
    msg += f"  │  🛑 Stop       <code>{format_price(sl)}</code>  <i>-{sl_pct:.2f}%</i>\n"
    res_dist=abs(res-entry)/entry*100; sup_dist=abs(entry-sup)/entry*100

    def _break_prob(dist_pct, favourable_dir):
        dist_score = max(0, 50 - dist_pct*8)
        mom_score = mom * 3 if favourable_dir else -mom * 3
        adx_score = (adx_val - 20) * 0.6
        vol_score = 8 if vol_strength>=1.5 else -4
        rsi_score = (rsi_15m - 50) * 0.4 if favourable_dir else (50 - rsi_15m) * 0.4
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
    msg += f"  │  📦 Vol  : {'✅' if vol_strength>=1.5 else '⚠️'} {vol_strength:.1f}x avg\n"
    msg += f"  │  📌 Pat  : {setup['pattern']}\n"
    msg += f"  │  📊 RSI  : {rsi_val:.1f}   ADX: {adx_val:.1f}   Mom: {mom:+.2f}%\n"
    if zone_ok: msg += f"  │  📍 Zone : ✅ {'Demand' if setup['direction']=='BUY' else 'Supply'}\n"
    if div=="BULLISH_DIV":   msg += f"  │  🔀 Div  : 🟢 Bullish RSI Divergence\n"
    elif div=="BEARISH_DIV": msg += f"  │  🔀 Div  : 🔴 Bearish RSI Divergence\n"
    bos_str = "  🔥BOS" if ms["bos"] else ""
    ms_bias_em="📈" if ms["bias"]=="bullish" else "📉" if ms["bias"]=="bearish" else "➡️"
    msg += f"  │  🏗️ MS   : {ms_bias_em} {ms['bias'].upper()}{bos_str}\n"
    msg += f"  │  💸 Fund : {funding_label}  {funding_detail}\n"
    msg += f"  │  📊 Vol  : {vol_strength:.1f}x avg\n"
    msg += f"  │  🕐 RSI  : 15m:{rsi_15m:.0f}  1h:{rsi_1h:.0f}  4h:{rsi_4h:.0f}\n"
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
        # Count partial TP as WIN — if Milestone 1 was reached, trade is already profitable
        milestones_hit=trade.get("milestones_sent",[])
        partial_win="p1" in milestones_hit or "p10" in milestones_hit
        hit=None
        if trade["direction"]=="BUY":
            if price>=trade["tp"]:   hit="WIN"
            elif price<=trade["sl"]:
                # If milestone 1 was reached, SL was moved to breakeven → still a win
                hit="WIN" if partial_win else "LOSS"
        else:
            if price<=trade["tp"]:   hit="WIN"
            elif price>=trade["sl"]:
                hit="WIN" if partial_win else "LOSS"
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
                close_note="via partial TP (breakeven SL)" if partial_win and pnl<=2 else ""
                trade_journal.append({"date":str(datetime.now(IST).date()),"coin":coin,
                    "direction":trade["direction"],"pattern":primary,
                    "entry":trade["entry"],"exit":price,"pnl":pnl,"result":hit,
                    "duration":duration,"tf_score":trade.get("tf_score",0),
                    "market_condition":mc,"close_note":close_note})
                save_journal(); learn_from_trade(coin,primary,hit,pnl,mc,trade.get("tf_score",0))
            em="✅" if hit=="WIN" else "🛑"
            close_reason=""
            if partial_win and hit=="WIN" and pnl<=5: close_reason="\n  📌 Counted as WIN — Milestone 1 was reached"
            # Deep trade feedback
            klines_close=get_klines(trade["symbol"],"1h",50)
            feedback=""
            if klines_close:
                closes_c=[float(k[4]) for k in klines_close]
                adx_c=calculate_adx(klines_close)
                rsi_c=calculate_rsi(closes_c)
                if hit=="LOSS":
                    if adx_c<22: feedback="⚠️ Market turned sideways after entry — trend faded."
                    elif rsi_c>70 and trade["direction"]=="BUY": feedback="⚠️ RSI was overbought at close — entry was late."
                    elif rsi_c<30 and trade["direction"]=="SELL": feedback="⚠️ RSI was oversold at close — entry was late."
                    else: feedback="⚠️ Stop loss hit — market moved against the setup."
                else:
                    if pnl>50: feedback="🌟 Excellent trade — strong momentum carried to target."
                    elif pnl>20: feedback="✅ Good trade — followed the plan."
                    else: feedback="✅ Trade completed — partial profit secured."
            send_telegram(
                f"{em} <b>TRADE {'WON' if hit=='WIN' else 'CLOSED'} — {coin}</b>\n"
                f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
                f"🪙 <b>{coin}</b>  {'🟢' if trade['direction']=='BUY' else '🔴'} {trade['direction']}\n"
                f"📌 Pattern: {primary}\n"
                f"🌐 Market: {mc.upper()}\n\n"
                f"💰 Entry: <code>{format_price(trade['entry'])}</code>\n"
                f"📍 Exit:  <code>{format_price(price)}</code>\n"
                f"⏱️ Duration: {duration}\n\n"
                f"📈 <b>PnL: {fmt_pnl(pnl)}</b>{close_reason}\n\n"
                f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
                f"💡 <b>Feedback:</b> {feedback}\n"
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
                    elif txt_slash=="/counsel": safe_send(cmd_trade_suggestions,"🔮 Counsel")
                    elif txt_slash=="/regime":  send_telegram("fetching..."); # handled by txt_clean below
                    elif txt_slash=="/feedback": pass  # handled by txt_clean below
                    elif txt_slash=="/quickstats":
                        total=len(trade_journal); wins=sum(1 for t in trade_journal if t.get("result")=="WIN")
                        wr=(wins/total*100) if total>0 else 0
                        today=str(datetime.now(IST).date())
                        td=[t for t in trade_journal if t.get("date")==today]
                        tw=sum(1 for t in td if t.get("result")=="WIN"); tl=sum(1 for t in td if t.get("result")=="LOSS")
                        tpnl=sum(t.get("pnl",0) for t in td)
                        btc=get_price("BTCUSDT"); fng=get_fear_greed_index()
                        send_telegram(
                            _H("QUICK STATS","📜")+"\n\n"
                            f"  ⚔️ Today: {tw}W / {tl}L  •  {fmt_pnl(tpnl)}\n"
                            f"  🗻 All Time: {total} trades  WR: <b>{wr:.1f}%</b>\n"
                            f"  ₿ BTC: <code>${format_price(btc) if btc else 'N/A'}</code>\n"
                            f"  😰 F&G: {fng}\n"
                            f"  ⚔️ Open: {len(active_trades)}/{MAX_ACTIVE_TRADES}\n"
                            f"  ⏳ Scouts: {len(pending_signals)}\n"
                            f"  🕐 {get_ist_time()}"
                        )
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
                                [{"text":"🌀 Patterns"}, {"text":"🌍 Market"},    {"text":"💎 Hidden Gems"}],
                                [{"text":"🔍 Scan"},     {"text":"📉 Trend BTC"}, {"text":"🔮 Counsel"}],
                                [{"text":"📊 Quick Stats"},{"text":"🌐 Regime"},  {"text":"📜 Feedback"}],
                            ],
                            "resize_keyboard":True,
                            "persistent":True
                        }
                        send_telegram(
                            f"{_H('TRADING SIGNAL MASTER v32G','⚙️')}\n\n"
                            f"  Tap a button or type a command:\n\n"
                            f"  📊 /trades    — Active trades\n"
                            f"  ⏳ /pending   — Pending signals\n"
                            f"  📈 /stats     — Pattern stats\n"
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
                        sess=is_good_trading_session(); cb=check_circuit_breaker()
                        btc_crash=is_btc_crashing()
                        send_telegram(
                            f"{_H('LIVE BOT STATUS','📡')}\n\n"
                            f"  {'✅' if sess else '🔴'} Session    : {'ACTIVE' if sess else 'DEAD (2-7AM IST)'}\n"
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
                    elif txt_clean in ("🔮 counsel","/counsel"):
                        safe_send(cmd_trade_suggestions,"🔮 Counsel")
                    elif txt_clean in ("🌐 regime","/regime"):
                        # Market Regime — clear bull/bear/sideways analysis
                        btc_p=get_price("BTCUSDT"); btc_k=get_klines("BTCUSDT","1h",50)
                        mc=detect_market_condition(btc_p,btc_k) if btc_p and btc_k else "unknown"
                        adx=calculate_adx(btc_k) if btc_k else 0
                        closes=[float(k[4]) for k in btc_k] if btc_k else []
                        e20=calculate_ema(closes,20); e50=calculate_ema(closes,50)
                        std=(sum((c-e20)**2 for c in closes[-20:])/20)**0.5 if e20 and closes else 0
                        bb_width=((4*std)/e20*100) if e20>0 else 0
                        rsi=calculate_rsi(closes) if closes else 50
                        fng=get_fear_greed_index()
                        regime_em="📈" if mc=="bull" else "📉" if mc=="bear" else "➡️"
                        advice=("Strong trend — bot will use breakout/momentum signals." if mc in ("bull","bear") and adx>25 else
                                "Weak trend — bot using range/mean-reversion signals." if mc=="sideways" else
                                "Mixed — bot filtering aggressively.")
                        send_telegram(
                            _H("MARKET REGIME","🌐")+"\n\n"
                            f"  {regime_em} Regime   : <b>{mc.upper()}</b>\n"
                            f"  💪 ADX     : {adx:.1f} ({'Strong' if adx>30 else 'Moderate' if adx>22 else 'Weak'})\n"
                            f"  📊 BB Width: {bb_width:.2f}% ({'Trending' if bb_width>4 else 'Ranging'})\n"
                            f"  📈 RSI(1h) : {rsi:.1f}\n"
                            f"  😰 F&G     : {fng}\n"
                            f"  ₿ BTC      : <code>${format_price(btc_p) if btc_p else 'N/A'}</code>\n\n"
                            f"  💡 {advice}\n\n"
                            f"  🕐 {get_ist_time()}"
                        )
                    elif txt_clean in ("📜 feedback","/feedback"):
                        # Deep trade feedback — last 5 trades analyzed
                        if not trade_journal:
                            send_telegram(_H("TRADE FEEDBACK","📜")+"\n\n  🌙 No trades recorded yet.")
                        else:
                            recent=trade_journal[::-1]  # ALL trades
                            text=_H("DEEP TRADE FEEDBACK","📜")+"\n\n"
                            wins=sum(1 for t in recent if t.get("result")=="WIN")
                            total=len(recent)
                            text+=f"  ALL {total} TRADES: {wins}W / {total-wins}L  WR: <b>{wr:.1f}%</b>\n\n"
                            for t in recent[:10]:  # show last 10 in detail
                                em="✅" if t.get("result")=="WIN" else "🔴"
                                mc_t=t.get("market_condition","?")
                                note=t.get("close_note","")
                                text+=(f"  {em} <b>{t.get('coin','?')}</b>  {t.get('direction','?')}\n"
                                       f"  ◆ {t.get('pattern','?')}  [{mc_t}]\n"
                                       f"  {fmt_pnl(t.get('pnl',0))}  ⏱️ {t.get('duration','?')}\n")
                                if note: text+=f"  📌 {note}\n"
                                text+="\n"
                            # Overall insight
                            all_wins=sum(1 for t in trade_journal if t.get("result")=="WIN")
                            all_total=len(trade_journal)
                            wr=(all_wins/all_total*100) if all_total>0 else 0
                            top_mc={}
                            for t in trade_journal:
                                mc_t=t.get("market_condition","?")
                                if mc_t not in top_mc: top_mc[mc_t]={"W":0,"L":0}
                                top_mc[mc_t]["W" if t.get("result")=="WIN" else "L"]+=1
                            text+=(f"  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
                                   f"  All-time WR: <b>{wr:.1f}%</b> ({all_total} trades)\n\n"
                                   f"  By market condition:\n")
                            for mc_t,r in top_mc.items():
                                ct=r["W"]+r["L"]; mwr=(r["W"]/ct*100) if ct>0 else 0
                                em2="📈" if mc_t=="bull" else "📉" if mc_t=="bear" else "➡️"
                                text+=f"  {em2} {mc_t}: {r['W']}W/{r['L']}L ({mwr:.0f}%)\n"
                            text+=f"\n  🕐 {get_ist_time()}"
                            send_telegram(text)
                    elif txt_clean in ("📊 quick stats","/quickstats"):
                        total=len(trade_journal); wins=sum(1 for t in trade_journal if t.get("result")=="WIN")
                        wr=(wins/total*100) if total>0 else 0
                        today=str(datetime.now(IST).date())
                        td=[t for t in trade_journal if t.get("date")==today]
                        tw=sum(1 for t in td if t.get("result")=="WIN"); tl=sum(1 for t in td if t.get("result")=="LOSS")
                        tpnl=sum(t.get("pnl",0) for t in td)
                        btc=get_price("BTCUSDT"); fng=get_fear_greed_index()
                        btc_k=get_klines("BTCUSDT","1h",50)
                        mc=detect_market_condition(btc,btc_k) if btc and btc_k else "unknown"
                        send_telegram(
                            _H("QUICK STATS","📜")+"\n\n"
                            f"  ⚔️ Today: {tw}W / {tl}L  •  {fmt_pnl(tpnl)}\n"
                            f"  🗻 All Time: {total} trades  WR: <b>{wr:.1f}%</b>\n\n"
                            f"  🌐 Regime: {mc.upper()}\n"
                            f"  ₿ BTC: <code>${format_price(btc) if btc else 'N/A'}</code>\n"
                            f"  😰 F&G: {fng}\n"
                            f"  ⚔️ Open: {len(active_trades)}/{MAX_ACTIVE_TRADES}\n"
                            f"  ⏳ Scouts: {len(pending_signals)}\n"
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
    global last_river_time
    try:
        if "RIVER" not in active_trades and "RIVER" not in pending_signals:
            price=get_price("RIVERUSDT"); klines=get_klines("RIVERUSDT","15m",100)
            if not price or not klines or len(klines)<50: return
            found=detect_patterns("RIVERUSDT",klines,price,1)+detect_patterns("RIVERUSDT",klines,price,-1)
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
                    setup={"coin":"RIVER","symbol":"RIVERUSDT","direction":best[2],"pattern":pt,
                           "setup_score":score,"leverage":get_smart_leverage("RIVERUSDT",atr_pct,score),
                           "scan_price":price}
                    format_and_send(setup,"RIVER",is_river=True,is_instant=score>=INSTANT_SIGNAL_THRESHOLD,market_condition=market_condition)
        last_river_time=now
    except Exception as e: logger.error(f"River: {e}",exc_info=True)

def scan_coins(btc_trend,fng,market_condition):
    btc_crashing=is_btc_crashing(); signals_this_cycle=0
    is_sideways_market=(market_condition=="sideways")
    if is_sideways_market:
        logger.info("Market is SIDEWAYS — using range/mean-reversion signals only")
    for coin in COINS:
        if signals_this_cycle>=MAX_SIGNALS_PER_CYCLE: break
        try:
            if coin in coin_cooldowns:
                if get_ist_datetime()<coin_cooldowns[coin]:
                    logger.info(f"Skip {coin} - cooldown"); continue
                else: del coin_cooldowns[coin]
            symbol=coin+"USDT"; price=get_price(symbol)
            klines=get_klines(symbol,SCAN_CANDLE_TF)
            if not price or not klines: continue

            coin_sideways=is_market_sideways(symbol,klines)

            if is_sideways_market or coin_sideways:
                # Use sideways-specific signals (range/BB/RSI reversion)
                found=get_sideways_signals(symbol,klines,price)
                if not found: continue
                # Lower score threshold for sideways — patterns are simpler
                best_pat=max(found,key=lambda x:x[1])
                if best_pat[1]<82: continue
                direction=best_pat[2]
                if btc_crashing and direction=="BUY": continue
                tf_score=get_timeframe_score(symbol,direction)
                if tf_score==-1: continue
                atr=calculate_atr(klines); atr_pct=(atr/price)*100 if price>0 else 0
                lev=max(get_smart_leverage(symbol,atr_pct,best_pat[1]),3)
                # Sideways TP: tighter — only 4-6% price move but enforces 20% leveraged
                min_price_move=(20/lev)  # price% needed for 20% leveraged
                tp_pct=max(min_price_move, min(atr_pct*2.5, 8.0))
                # Enforce min 20% leveraged TP
                if tp_pct*lev < 20:
                    logger.info(f"Skip {coin} sideways — TP only {tp_pct*lev:.1f}% leveraged (need 20%)")
                    continue
                setup={"coin":coin,"symbol":symbol,"direction":direction,
                       "pattern":best_pat[0],"setup_score":best_pat[1],
                       "leverage":lev,"scan_price":price,
                       "market_condition":"sideways","tf_score":tf_score,
                       "sideways_mode":True}
                if (coin not in active_trades and coin not in pending_signals
                        and len(active_trades)<MAX_ACTIVE_TRADES):
                    logger.info(f"SIDEWAYS SIGNAL: {coin}|{direction}|Score:{best_pat[1]}|{best_pat[0]}")
                    if format_and_send(setup,coin,is_instant=False,market_condition="sideways"):
                        signals_this_cycle+=1
            else:
                # Normal trend-following signals
                found=detect_patterns(symbol,klines,price,btc_trend)
                if not found: continue
                scored=get_all_pattern_scores(found,market_condition)
                signal_sent=False
                for direction in ["BUY","SELL"]:
                    if signal_sent: break
                    dir_pats=[p for p in scored if p[2]==direction]
                    if not dir_pats: continue
                    best_pat=dir_pats[0]; primary=best_pat[0]
                    adj_score=best_pat[1]; base_s=best_pat[3]
                    if base_s<MIN_PRIMARY_SCORE: continue
                    if is_pattern_blacklisted(primary): continue
                    if is_pattern_suspended(primary): continue
                    if not is_sentiment_valid(direction,fng): continue
                    if btc_crashing and direction=="BUY": continue
                    if coin in BTC_CORRELATED and too_many_correlated_active(): continue
                    tf_score=get_timeframe_score(symbol,direction)
                    if tf_score==-1: continue
                    extras=[p[0] for p in dir_pats[1:3]]
                    pt=primary+(" + "+" + ".join(extras) if extras else "")
                    confirm_bonus=min(len(dir_pats)*0.5,3.0)
                    score=min(adj_score+confirm_bonus,99)
                    # Watch alert: score building but not yet at threshold
                    if 80<=score<MIN_SETUP_SCORE and coin not in active_trades and coin not in pending_signals:
                        check_and_send_watch_alert(coin,symbol,price,klines,direction)
                    if score<MIN_SETUP_SCORE: continue
                    atr=calculate_atr(klines); atr_pct=(atr/price)*100 if price>0 else 0
                    lev=get_smart_leverage(symbol,atr_pct,score)
                    # ENFORCE MIN 20% LEVERAGED TP
                    # Check if ATR-based TP gives at least 20% leveraged return
                    projected_tp_pct=atr_pct*ATR_TP_MULTIPLIER
                    if projected_tp_pct*lev<20:
                        logger.info(f"Skip {coin} — TP only {projected_tp_pct*lev:.1f}% leveraged (need 20%)")
                        continue
                    setup={"coin":coin,"symbol":symbol,"direction":direction,"pattern":pt,
                           "setup_score":score,"leverage":lev,"scan_price":price,
                           "market_condition":market_condition,"tf_score":tf_score,
                           "sideways_mode":False}
                    if (coin not in active_trades and coin not in pending_signals
                            and len(active_trades)<MAX_ACTIVE_TRADES):
                        is_inst=score>=INSTANT_SIGNAL_THRESHOLD
                        logger.info(f"{'INSTANT' if is_inst else 'SIGNAL'}: {coin}|{direction}|Score:{score:.1f}|{primary}")
                        if format_and_send(setup,coin,is_instant=is_inst,market_condition=market_condition):
                            signal_sent=True; signals_this_cycle+=1
        except Exception as e: logger.error(f"Scan {coin}: {e}",exc_info=True)
        time.sleep(DELAY_BETWEEN_COINS)

def main():
    global last_batch_time,last_river_time,last_hourly_time,last_pnl_update_time,last_weekly_report_day
    load_alerts(); load_circuit_breaker(); load_pending_signals()
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
            now=time.time()
            if (now-last_hourly_time)>=3600:          send_hourly_report();   last_hourly_time=now
            if (now-last_pnl_update_time)>=3600:      send_live_pnl_update(); last_pnl_update_time=now
            if (now-last_river_time)>=RIVER_INTERVAL:  scan_river(now,market_condition); last_river_time=now
            today=datetime.now(IST).date()
            if today.weekday()==6 and last_weekly_report_day!=today:
                send_weekly_report(); last_weekly_report_day=today
            time.sleep(SCAN_INTERVAL)
        except Exception as e:
            logger.error(f"Main loop: {e}",exc_info=True); time.sleep(60)

if __name__=="__main__":
    main()
