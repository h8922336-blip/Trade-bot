"""
Predictive Pattern Diagnostic
==============================
Answers one specific question: "why didn't an early/predictive pattern
catch this coin before its confirmed breakout fired?" — using the REAL
detector functions extracted verbatim from main.py, not reimplemented
from memory. If this script says a pattern didn't fire, your live bot
genuinely wouldn't have fired it either, on the same data.

WHY THIS EXISTS: your bot has two genuinely different families of
pattern:
  - PREDICTIVE (7 patterns): detect a STATE (a coil, a compression, an
    absorption) with no confirmation required yet. These are the ones
    that get an EARLY ENTRY CHECKPOINT + 5m sniper wait.
  - CONFIRMATION (Double Bottom + Volume Breakout is one of these): by
    their own definition, these can only fire AFTER a real move has
    already printed on the 15m chart. No code change can make these
    "early" — the breakout is in their detection math.

For a coin like UNI that triggered a confirmation pattern, the real
question isn't "why was the signal late" (it structurally can't be
early) — it's "was there a predictive pattern that SHOULD have fired
on the coiling candles that came before it, and didn't?" This script
answers that directly, using your real code.

HOW TO USE THIS
----------------
This sandbox has no network access to fetch live Binance data, so this
script needs real candle data supplied to it. Two ways to get that:

1. RUN IT ON YOUR RAILWAY DEPLOYMENT (recommended): drop this file next
   to main.py, then run:
       python predictive_pattern_diagnostic.py UNIUSDT --live
   This calls your bot's own get_klines() (imported directly from
   main.py) to pull real, current candles — the exact same data your
   live bot sees.

2. FEED IT SAVED CANDLES: if you've exported klines from Binance,
   TradingView, or your own bot's logs into a CSV (columns: open_time,
   open, high, low, close, volume), run:
       python predictive_pattern_diagnostic.py UNIUSDT --csv path/to/file.csv
   This lets you replay a SPECIFIC historical window — e.g. the hour
   before UNI's Double Bottom fired — and see exactly what every
   predictive detector said at each point in time.

WHAT IT PRINTS
--------------
For every 15m candle in the window (or just the latest, by default):
  - Which of the 7 predictive patterns fired (if any)
  - For patterns that DIDN'T fire, the specific numeric reason why —
    e.g. "compression tightness 2.1% (needs <1.5%)" — not just "no"
  - Market structure context (bias, swing high/low) feeding into them
"""

import argparse
import csv
import sys

# ─────────────────────────────────────────────────────────────────────
# EXTRACTED VERBATIM FROM main.py — do not hand-edit these; if the bot
# changes, re-extract instead, so this diagnostic never silently drifts
# from what the live bot actually does.
# ─────────────────────────────────────────────────────────────────────

SQUEEZE_FUNDING_EXTREME_NEG = -0.0003   # -0.03% — shorts paying heavily, over-leveraged short side
SQUEEZE_FUNDING_EXTREME_POS = 0.0003    # +0.03% — mirror case for long-squeeze setups


def calculate_ema(closes,period):
    if len(closes)<period: return None
    k=2/(period+1); ema=sum(closes[:period])/period
    for p in closes[period:]: ema=p*k+ema*(1-k)
    return ema


def calculate_rsi(closes,period=14):
    """
    Wilder's Smoothing RSI (fixed from a plain SMA in an earlier round of
    the bot's own development — this IS the corrected version).
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
    except Exception:
        return 0.0
 def get_recent_swing_levels(klines, lookback=20):
    if len(klines) < lookback + 1:
        return 0, 0
    highs = [float(k[2]) for k in klines[-(lookback+1):-1]]
    lows  = [float(k[3]) for k in klines[-(lookback+1):-1]]
    if not highs or not lows:
        return 0, 0
    return max(highs), min(lows)


def detect_market_structure(klines):
    closes=[float(k[4]) for k in klines]; highs=[float(k[2]) for k in klines]; lows=[float(k[3]) for k in klines]
    swing_highs=[]; swing_lows=[]
    for i in range(5,len(klines)-5):
        if highs[i]==max(highs[i-5:i+6]): swing_highs.append((i,highs[i]))
        if lows[i]==min(lows[i-5:i+6]): swing_lows.append((i,lows[i]))
    bias="neutral"; bos=False; choch=False
    if len(swing_highs)>=2 and len(swing_lows)>=2:
        hh=swing_highs[-1][1]>swing_highs[-2][1]; hl=swing_lows[-1][1]>swing_lows[-2][1]
        lh=swing_highs[-1][1]<swing_highs[-2][1]; ll=swing_lows[-1][1]<swing_lows[-2][1]
        if hh and hl: bias="bullish"
        elif lh and ll: bias="bearish"
        last_sh=swing_highs[-1][1]; last_sl=swing_lows[-1][1]
        if closes[-1]>last_sh: bos=True
        elif closes[-1]<last_sl: bos=True
        if bias=="bullish" and closes[-1]<last_sl: choch=True
        elif bias=="bearish" and closes[-1]>last_sh: choch=True
        return {"bias":bias,"bos":bos,"choch":choch,"swing_high":last_sh,"swing_low":last_sl}
    return {"bias":"neutral","bos":False,"choch":False,"swing_high":max(highs[-20:]),"swing_low":min(lows[-20:])}


def detect_volatility_contraction(closes, highs, lows, vols, price):
    if len(closes) < 20: return None, 0
    recent_range = max(highs[-5:]) - min(lows[-5:])
    older_range = max(highs[-20:-5]) - min(lows[-20:-5])
    if older_range <= 0: return None, 0
    tightness = recent_range / older_range
    if tightness < 0.5:
        avg_vol_recent = sum(vols[-5:]) / 5
        avg_vol_older = sum(vols[-20:-5]) / 15
        if avg_vol_older > 0 and avg_vol_recent < avg_vol_older * 0.7:
            direction = "BUY" if closes[-1] >= (max(highs[-5:]) + min(lows[-5:])) / 2 else "SELL"
            return direction, tightness
    return None, tightness


def detect_pre_breakout_compression(closes, highs, lows, vols, price, sup, res, direction_bias):
    if len(closes) < 10 or sup <= 0 or res <= 0: return None, 0
    range_pct = (res - sup) / price * 100 if price > 0 else 99
    dist_to_res = (res - price) / price * 100 if price > 0 else 99
    dist_to_sup = (price - sup) / price * 100 if price > 0 else 99
    recent_vol = sum(vols[-5:]) / 5
    older_vol = sum(vols[-15:-5]) / 10 if len(vols) >= 15 else recent_vol
    quiet = older_vol > 0 and recent_vol < older_vol * 0.9
    if range_pct < 3.0 and quiet:
        if dist_to_res < 1.0 and direction_bias != "bearish":
            return "BUY", range_pct
        if dist_to_sup < 1.0 and direction_bias != "bullish":
            return "SELL", range_pct
    return None, range_pct


def detect_early_spark(closes, highs, lows, opens, vols, price):
    if len(closes) < 30: return None
    avg_vol_20 = sum(vols[-20:]) / 20 if len(vols) >= 20 else 1
    current_vol = vols[-1]
    lookback = min(len(lows), 96)
    recent_low = min(lows[-lookback:])
    recent_high = max(highs[-lookback:])
    dist_from_low_pct = (price - recent_low) / recent_low * 100 if recent_low > 0 else 99
    dist_from_high_pct = (recent_high - price) / price * 100 if price > 0 else 99
    volume_igniting = current_vol >= avg_vol_20 * 1.1
    if dist_from_low_pct <= 1.5 and volume_igniting and closes[-1] > opens[-1]:
        return "BUY"
    if dist_from_high_pct <= 1.5 and volume_igniting and closes[-1] < opens[-1]:
        return "SELL"
    return None


def detect_smart_money_absorption(closes, highs, lows, vols, price):
    if len(closes) < 40: return None
    macro_high = max(highs[-40:-10]); macro_low_region = min(lows[-40:-10])
    if macro_high <= 0: return None
    macro_drop = (macro_high - macro_low_region) / macro_high * 100
    if macro_drop < 12: return None
    recent_low = min(lows[-10:])
    recent_range_pct = (max(highs[-10:]) - recent_low) / price * 100 if price > 0 else 99
    if recent_range_pct > 2.5: return None
    dist_from_low = (price - recent_low) / recent_low * 100 if recent_low > 0 else 99
    if dist_from_low > 2.0: return None
    return "BUY"


def detect_pressure_triangle(highs, lows, closes, vols, price):
    if len(closes) < 20: return None
    recent_highs = highs[-15:]; recent_lows = lows[-15:]
    flat_top = max(recent_highs[-5:]) <= max(recent_highs[:5]) * 1.002
    rising_lows = recent_lows[-1] > recent_lows[0] * 1.001
    if flat_top and rising_lows:
        avg_vol = sum(vols[-15:]) / 15
        if avg_vol > 0 and vols[-1] >= avg_vol * 1.35:
            return "BUY"
    return None


def detect_funding_divergence(funding_rate, price, sup, res):
    if funding_rate is None: return None
    if sup <= 0 or res <= 0: return None
    near_support = (price - sup) / sup * 100 <= 1.0 if sup > 0 else False
    near_resistance = (res - price) / price * 100 <= 1.0 if price > 0 else False
    if funding_rate <= SQUEEZE_FUNDING_EXTREME_NEG and near_support:
        return "BUY"
    if funding_rate >= SQUEEZE_FUNDING_EXTREME_POS and near_resistance:
        return "SELL"
    return None


def detect_inside_bar_coil(closes, highs, lows, opens, vols, price, zone_low, zone_high, direction_bias):
    if len(closes) < 5 or zone_low <= 0 or zone_high <= 0: return None, 0, 0
    mother_high = highs[-3]; mother_low = lows[-3]
    inside1 = highs[-2] <= mother_high and lows[-2] >= mother_low
    inside2 = highs[-1] <= mother_high and lows[-1] >= mother_low
    if not (inside1 and inside2): return None, 0, 0
    in_zone = zone_low <= price <= zone_high
    if not in_zone: return None, 0, 0
    avg_vol = sum(vols[-10:]) / 10
    quiet = vols[-1] < avg_vol * 0.9 if avg_vol > 0 else False
    if not quiet: return None, 0, 0
    if direction_bias != "bearish":
        return "BUY", mother_high, mother_low
    if direction_bias != "bullish":
        return "SELL", mother_high, mother_low
    return None, 0, 0


def detect_liquidity_sweep(klines, highs, lows, closes, opens, sup, res, ms):
    if len(klines) < 5 or sup <= 0 or res <= 0: return None, 0
    for i in range(-3, 0):
        c_low = lows[i]; c_high = highs[i]; c_close = closes[i]; c_open = opens[i]
        if c_low < sup and c_close > sup and c_close > c_open:
            strength = (sup - c_low) / sup * 100 if sup > 0 else 0
            return "BUY", strength
        if c_high > res and c_close < res and c_close < c_open:
            strength = (c_high - res) / res * 100 if res > 0 else 0
            return "SELL", strength
    return None, 0
# ─────────────────────────────────────────────────────────────────────
# DIAGNOSTIC LOGIC (new — not extracted, this is the reporting layer)
# ─────────────────────────────────────────────────────────────────────

PATTERN_NAMES = [
    "Volatility Contraction (Coiling)", "Pre-Breakout Compression", "Early Spark Ignition",
    "Smart Money Absorption", "Pressure Cooker Triangle", "Inside Bar Coil", "Liquidity Sweep",
]


def run_all_detectors(klines, funding_rate=None):
    """
    Runs every real predictive detector against one klines window and
    returns a structured report: which fired, and a specific numeric
    reason for each one that didn't — not just "no."
    """
    closes = [float(k[4]) for k in klines]
    opens  = [float(k[1]) for k in klines]
    highs  = [float(k[2]) for k in klines]
    lows   = [float(k[3]) for k in klines]
    vols   = [float(k[5]) for k in klines]
    price  = closes[-1]

    ms = detect_market_structure(klines)
    sup = ms["swing_low"] if ms["swing_low"] > 0 else (min(lows[-30:-1]) if len(lows) >= 31 else min(lows))
    res = ms["swing_high"] if ms["swing_high"] > 0 else (max(highs[-30:-1]) if len(highs) >= 31 else max(highs))
    recent_high, recent_low = get_recent_swing_levels(klines, lookback=20)
    fresh_sup = recent_low if recent_low > 0 else sup
    fresh_res = recent_high if recent_high > 0 else res

    results = {}

    vcp_dir, vcp_tightness = detect_volatility_contraction(closes, highs, lows, vols, price)
    results["Volatility Contraction (Coiling)"] = {
        "fired": vcp_dir, "detail": f"tightness ratio {vcp_tightness:.2f} (needs <0.50, plus quiet volume)"
    }

    pbc_dir, pbc_range_pct = detect_pre_breakout_compression(closes, highs, lows, vols, price, fresh_sup, fresh_res, ms["bias"])
    results["Pre-Breakout Compression"] = {
        "fired": pbc_dir, "detail": f"range {pbc_range_pct:.2f}% of price (needs <3.0%, plus within 1.0% of a level, plus quiet volume)"
    }

    spark_dir = detect_early_spark(closes, highs, lows, opens, vols, price)
    lookback = min(len(lows), 96)
    dist_low = (price - min(lows[-lookback:])) / min(lows[-lookback:]) * 100 if min(lows[-lookback:]) > 0 else 99
    vol_ratio_spark = vols[-1] / (sum(vols[-20:])/20) if len(vols) >= 20 and sum(vols[-20:]) > 0 else 0
    results["Early Spark Ignition"] = {
        "fired": spark_dir, "detail": f"{dist_low:.2f}% off recent low (needs <=1.5%), volume {vol_ratio_spark:.2f}x avg (needs >=1.1x)"
    }

    sma_dir = detect_smart_money_absorption(closes, highs, lows, vols, price)
    if len(highs) >= 40:
        macro_high = max(highs[-40:-10])
        macro_drop = (macro_high - min(lows[-40:-10])) / macro_high * 100 if macro_high > 0 else 0
    else:
        macro_drop = 0
    results["Smart Money Absorption"] = {
        "fired": sma_dir, "detail": f"prior decline {macro_drop:.1f}% (needs >=12% before it even looks for a coil)"
    }

    triangle_dir = detect_pressure_triangle(highs, lows, closes, vols, price)
    results["Pressure Cooker Triangle"] = {
        "fired": triangle_dir, "detail": "needs a flat top + rising lows + a real volume tick on the final candle"
    }

    ib_dir, ib_high, ib_low = detect_inside_bar_coil(closes, highs, lows, opens, vols, price, fresh_sup, fresh_res, ms["bias"])
    results["Inside Bar Coil"] = {
        "fired": ib_dir, "detail": "needs the last 2 candles fully inside the prior candle's range, in a real zone, on quiet volume"
    }

    sweep_dir, sweep_strength = detect_liquidity_sweep(klines, highs, lows, closes, opens, sup, res, ms)
    results["Liquidity Sweep"] = {
        "fired": sweep_dir, "detail": f"needs a wick through a structural level that closes back inside it (strength if found: {sweep_strength:.2f}%)"
    }

    if funding_rate is not None:
        fd_dir = detect_funding_divergence(funding_rate, price, sup, res)
        results["Funding Divergence Sniper"] = {
            "fired": fd_dir, "detail": f"funding {funding_rate*100:.3f}% (needs <={SQUEEZE_FUNDING_EXTREME_NEG*100:.2f}% or >={SQUEEZE_FUNDING_EXTREME_POS*100:.2f}%, near a level)"
        }

    return results, ms, price


def print_report(coin, klines, funding_rate=None):
    results, ms, price = run_all_detectors(klines, funding_rate)
    print(f"\n{'='*70}")
    print(f"  {coin} — predictive pattern check at price {price}")
    print(f"  Market structure: bias={ms['bias']}  swing_high={ms['swing_high']}  swing_low={ms['swing_low']}")
    print(f"{'='*70}")
    any_fired = False
    for name, r in results.items():
        if r["fired"]:
            any_fired = True
            print(f"  🟢 FIRED: {name} -> {r['fired']}")
        else:
            print(f"  ⚪ no    : {name}  ({r['detail']})")
    print()
    if any_fired:
        print("  A predictive pattern WOULD have fired here — if your live bot")
        print("  didn't alert you at this point, check the Daily Macro Veto / Beta")
        print("  Trap gates in scan_coins, not the detectors themselves.")
    else:
        print("  No predictive pattern fires on this window. This means the coil")
        print("  genuinely didn't meet ANY of the 7 patterns' real thresholds at")
        print("  this point — worth checking the specific numbers above against")
        print("  what you expected, since that tells you exactly which threshold")
        print("  (if any) should be revisited, with a real number to discuss.")
    print()


def load_csv_klines(path):
    rows = []
    with open(path) as f:
        reader = csv.DictReader(f)
        for row in reader:
            rows.append([
                row.get("open_time", 0),
                float(row["open"]), float(row["high"]),
                float(row["low"]), float(row["close"]), float(row["volume"]),
            ])
    return rows


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("coin", help="e.g. UNIUSDT")
    ap.add_argument("--csv", help="path to a CSV of klines (open_time,open,high,low,close,volume)")
    ap.add_argument("--live", action="store_true", help="fetch live data via your bot's own get_klines() — run this ON your Railway deployment, next to main.py")
    ap.add_argument("--funding", type=float, default=None, help="current funding rate, e.g. -0.0004 (optional)")
    ap.add_argument("--window", type=int, default=1, help="how many recent candles to step through and report on (default: just the latest)")
    args = ap.parse_args()

    if args.csv:
        klines = load_csv_klines(args.csv)
    elif args.live:
        try:
            sys.path.insert(0, ".")
            from main import get_klines  # your bot's real fetch function
        except ImportError:
            print("Could not import get_klines from main.py — run this script in the same directory as your bot's main.py.")
            sys.exit(1)
        klines = get_klines(args.coin, "15m", 100)
        if not klines:
            print(f"get_klines returned no data for {args.coin} — check the symbol and your network.")
            sys.exit(1)
    else:
        print("Provide either --csv <file> or --live. See --help for details.")
        sys.exit(1)

    if len(klines) < 60:
        print(f"Only {len(klines)} candles available — most detectors need 40-96 candles of history for a meaningful check. Results below may be incomplete.")

    if args.window <= 1:
        print_report(args.coin, klines, args.funding)
    else:
        for step_back in range(args.window - 1, -1, -1):
            end = len(klines) - step_back
            if end < 60:
                print(f"Skipping candle -{step_back}: only {end} candles of history available there (need 60+).")
                continue
            print_report(f"{args.coin} @ candle -{step_back}", klines[:end], args.funding)


if __name__ == "__main__":
    main()
