import base64
import copy
import hashlib
import io
import json
import math
import os
import re
import threading
import time
from dataclasses import asdict, dataclass
from datetime import datetime
from datetime import time as dtime
from pathlib import Path
from types import SimpleNamespace

import numpy as np
import pandas as pd
import requests
import streamlit as st

IST = "Asia/Kolkata"
MASTER_URL = "https://margincalculator.angelbroking.com/OpenAPI_File/files/OpenAPIScripMaster.json"
CANDLE_KEYS = ("prev_O", "prev_H", "prev_L", "prev_C", "sig_O", "sig_H", "sig_L", "sig_C")
STORE_KEYS = CANDLE_KEYS + ("hist",)          # hist = last 5 candles [O,H,L,C] (oldest -> newest) saved with every entry


# ============================== 10 CANDLE PATTERNS (same as the Google Sheet formulas) ==============================
# Sheet columns: B=Open, C=High, D=Low, E=Close.  Each function gets the pattern's candles OLDEST -> NEWEST
# (k[0] = first / "row 2" candle ... k[-1] = latest closed candle) and returns True/False (Series for a whole DataFrame).
def _body(k):
    return (k.c - k.o).abs()


def _p_engulf(k):       # =IF(AND(B2>E2,B3<E3,B3<=E2,E3>=B2),"BULLISH ENGULFING ","")
    a, b = k
    return (a.o > a.c) & (b.o < b.c) & (b.o <= a.c) & (b.c >= a.o)


def _p_harami(k):       # =IF(AND(B3>E3,B4<E4,B4>E3,E4<B3),"BULLISH harami","")
    a, b = k
    return (a.o > a.c) & (b.o < b.c) & (b.o > a.c) & (b.c < a.o)


def _p_marubozu(k):     # =IF(AND(E2>B2,(B2-D2)<=0.05*(E2-B2),(C2-E2)<=0.05*(E2-B2)),"Bullish Marubozu","")
    (a,) = k
    return (a.c > a.o) & ((a.o - a.l) <= 0.05 * (a.c - a.o)) & ((a.h - a.c) <= 0.05 * (a.c - a.o))


def _p_hammer(k):       # =IF(AND((C2-D2)>=2*ABS(E2-B2),(MIN(B2,E2)-D2)>=2*ABS(E2-B2),(C2-MAX(B2,E2))<=0.1*ABS(E2-B2)),"HAMMER","")
    (a,) = k
    bd = _body(a)
    return ((a.h - a.l) >= 2 * bd) & ((np.minimum(a.o, a.c) - a.l) >= 2 * bd) & ((a.h - np.maximum(a.o, a.c)) <= 0.1 * bd)


def _p_inv_hammer(k):   # =IF(AND((C2-MAX(B2,E2))>=2*ABS(E2-B2),(C2-D2)>=2*ABS(E2-B2),(MIN(B2,E2)-D2)<=0.1*ABS(E2-B2)),"INVERTED HAMMER","")
    (a,) = k
    bd = _body(a)
    return ((a.h - np.maximum(a.o, a.c)) >= 2 * bd) & ((a.h - a.l) >= 2 * bd) & ((np.minimum(a.o, a.c) - a.l) <= 0.1 * bd)


def _p_morning(k):      # =IF(AND(E2<B2,ABS(E3-B3)<=0.5*ABS(E2-B2),E4>B4,E4>=B2-0.5*(B2-E2)),"MORNING STAR","")
    a, b, c = k
    return (a.c < a.o) & (_body(b) <= 0.5 * _body(a)) & (c.c > c.o) & (c.c >= a.o - 0.5 * (a.o - a.c))


def _p_piercing(k):     # =IF(AND(E2<B2,E3>B3,E3>B2-(B2-E2)/2,E3<B2),"PIERCING","")
    a, b = k
    return (a.c < a.o) & (b.c > b.o) & (b.c > a.o - (a.o - a.c) / 2) & (b.c < a.o)


def _p_rising3(k):      # =IF(AND(E2>B2, 3 small candles (body<=0.5*first body) inside first candle's high/low, E6>B6, E6>E2),...)
    a, b, c, d, e = k
    ok = a.c > a.o
    for m in (b, c, d):
        ok = ok & (_body(m) <= 0.5 * _body(a)) & (m.h <= a.h) & (m.l >= a.l)
    return ok & (e.c > e.o) & (e.c > a.c)


def _p_soldiers(k):     # =IF(AND(E2>B2,E3>B3,E4>B4,E3>E2,E4>E3,B3>=B2,B3<=E2,B4>=B3,B4<=E3),"THREE WHITE SOLDIERS","")
    a, b, c = k
    return ((a.c > a.o) & (b.c > b.o) & (c.c > c.o) & (b.c > a.c) & (c.c > b.c)
            & (b.o >= a.o) & (b.o <= a.c) & (c.o >= b.o) & (c.o <= b.c))


def _p_tweezer(k):      # =IF(AND(E2<B2,E3>B3,ABS(D3-D2)<=0.001*D2),"TWEEZER BOTTOM","")
    a, b = k
    return (a.c < a.o) & (b.c > b.o) & ((b.l - a.l).abs() <= 0.001 * a.l)


# (name, candles used, python check, Excel formula builder: rows -> formula)
PATTERN_DEFS = (
    ("Bullish Engulfing", 2, _p_engulf,
     lambda r: f'=IF(AND(B{r[0]}>E{r[0]},B{r[1]}<E{r[1]},B{r[1]}<=E{r[0]},E{r[1]}>=B{r[0]}),"BULLISH ENGULFING ","")'),
    ("Bullish Harami", 2, _p_harami,
     lambda r: f'=IF(AND(B{r[0]}>E{r[0]},B{r[1]}<E{r[1]},B{r[1]}>E{r[0]},E{r[1]}<B{r[0]}),"BULLISH harami","")'),
    ("Bullish Marubozu", 1, _p_marubozu,
     lambda r: f'=IF(AND(E{r[0]}>B{r[0]},(B{r[0]}-D{r[0]})<=0.05*(E{r[0]}-B{r[0]}),(C{r[0]}-E{r[0]})<=0.05*(E{r[0]}-B{r[0]})),"Bullish Marubozu","")'),
    ("Hammer", 1, _p_hammer,
     lambda r: f'=IF(AND((C{r[0]}-D{r[0]})>=2*ABS(E{r[0]}-B{r[0]}),(MIN(B{r[0]},E{r[0]})-D{r[0]})>=2*ABS(E{r[0]}-B{r[0]}),(C{r[0]}-MAX(B{r[0]},E{r[0]}))<=0.1*ABS(E{r[0]}-B{r[0]})),"HAMMER","")'),
    ("Inverted Hammer", 1, _p_inv_hammer,
     lambda r: f'=IF(AND((C{r[0]}-MAX(B{r[0]},E{r[0]}))>=2*ABS(E{r[0]}-B{r[0]}),(C{r[0]}-D{r[0]})>=2*ABS(E{r[0]}-B{r[0]}),(MIN(B{r[0]},E{r[0]})-D{r[0]})<=0.1*ABS(E{r[0]}-B{r[0]})),"INVERTED HAMMER","")'),
    ("Morning Star", 3, _p_morning,
     lambda r: f'=IF(AND(E{r[0]}<B{r[0]},ABS(E{r[1]}-B{r[1]})<=0.5*ABS(E{r[0]}-B{r[0]}),E{r[2]}>B{r[2]},E{r[2]}>=B{r[0]}-0.5*(B{r[0]}-E{r[0]})),"MORNING STAR","")'),
    ("Piercing", 2, _p_piercing,
     lambda r: f'=IF(AND(E{r[0]}<B{r[0]},E{r[1]}>B{r[1]},E{r[1]}>B{r[0]}-(B{r[0]}-E{r[0]})/2,E{r[1]}<B{r[0]}),"PIERCING","")'),
    ("Rising Three Methods", 5, _p_rising3,
     lambda r: (f'=IF(AND(E{r[0]}>B{r[0]},ABS(E{r[1]}-B{r[1]})<=0.5*ABS(E{r[0]}-B{r[0]}),ABS(E{r[2]}-B{r[2]})<=0.5*ABS(E{r[0]}-B{r[0]}),'
                f'ABS(E{r[3]}-B{r[3]})<=0.5*ABS(E{r[0]}-B{r[0]}),C{r[1]}<=C{r[0]},D{r[1]}>=D{r[0]},C{r[2]}<=C{r[0]},D{r[2]}>=D{r[0]},'
                f'C{r[3]}<=C{r[0]},D{r[3]}>=D{r[0]},E{r[4]}>B{r[4]},E{r[4]}>E{r[0]}),"RISING THREE METHODS","")')),
    ("Three White Soldiers", 3, _p_soldiers,
     lambda r: f'=IF(AND(E{r[0]}>B{r[0]},E{r[1]}>B{r[1]},E{r[2]}>B{r[2]},E{r[1]}>E{r[0]},E{r[2]}>E{r[1]},B{r[1]}>=B{r[0]},B{r[1]}<=E{r[0]},B{r[2]}>=B{r[1]},B{r[2]}<=E{r[1]}),"THREE WHITE SOLDIERS","")'),
    ("Tweezer Bottom", 2, _p_tweezer,
     lambda r: f'=IF(AND(E{r[0]}<B{r[0]},E{r[1]}>B{r[1]},ABS(D{r[1]}-D{r[0]})<=0.001*D{r[0]}),"TWEEZER BOTTOM","")'),
)
PATTERNS = tuple(d[0] for d in PATTERN_DEFS)

SL_PCT = 0.0
MAX_HOLD_DAYS = 1
TREND_LOOKBACK = 0
TWEEZER_TOL_PCT = 0.10
FUTURES_MARGIN_PCT = 10.0
BROKERAGE_PCT = 0.0
SLIPPAGE_PCT = 0.0
FRESH_SECONDS = 120
LIVE_AUTORESUME = True     # True = a LIVE file that was RUNNING continues by itself after an app restart / re-login (False = press Resume manually)
FUNDS_PAUSE_SEC = 0        # pause all entries after a funds rejection (0 = never pause; set 300 for 5 min)
REFRESH_SECONDS = 5

TIMEFRAMES = {
    "1 minute": ("ONE_MINUTE", 1),
    "3 minutes": ("THREE_MINUTE", 3),
    "5 minutes": ("FIVE_MINUTE", 5),
    "10 minutes": ("TEN_MINUTE", 10),
    "15 minutes": ("FIFTEEN_MINUTE", 15),
    "30 minutes": ("THIRTY_MINUTE", 30),
    "1 hour": ("ONE_HOUR", 60),
    "4 hours": ("FOUR_HOUR", 240),     # built from 1-hour candles (Angel One has no 4H interval)
    "1 day": ("ONE_DAY", 1440),
}

OWNER_ID = "owner"
# Absolute data root so saves survive cwd changes on Streamlit Cloud.
# Override with env DATA_DIR if needed. App reboot on free Cloud can still wipe disk.
_DATA_DIR = os.environ.get("DATA_DIR") or os.path.join(os.path.expanduser("~"), "paper_trading_data")
STRATEGIES_ROOT = os.path.join(_DATA_DIR, "strategies")
os.makedirs(STRATEGIES_ROOT, exist_ok=True)


# ============================== CONFIG ==============================
@dataclass
class Config:
    capital: float = 100000.0
    max_open: int = 5
    target_pct: float = 1.0
    sl_pct: float = SL_PCT
    max_hold: int = MAX_HOLD_DAYS
    tweezer_tol_pct: float = TWEEZER_TOL_PCT
    trend_lookback: int = TREND_LOOKBACK
    brokerage_pct: float = BROKERAGE_PCT
    slippage_pct: float = SLIPPAGE_PCT
    interval: str = "FIVE_MINUTE"
    tf_min: int = 5
    patterns: tuple = PATTERNS
    position_amount: float = 0.0
    size_mode: str = "amount"           # "amount" | "qty" | "equal" (equal weight)
    position_qty: int = 0               # used when size_mode == "qty" (shares; lots for NFO/MCX)
    n_stocks: int = 0                   # selected stocks - equal weight divides capital by this when no max-position limit
    no_limit: bool = False
    cloud_filter: str = ""              # optional Ichimoku cloud filter: "" (off) | "Above" | "Center" | "Below"
    cloud_exit: str = ""                # optional EXIT when a closed candle reaches the cloud: "" (off) | "Above" | "Below" | "Above,Below"
    # ---- LIVE (real orders) - all OFF / neutral for paper ----
    live: bool = False
    limit_buffer_pct: float = 0.1       # BUY limit = LTP +buffer%, SELL (exit) limit = LTP -buffer%
    max_daily_loss: float = 0.0         # Rs; day P&L <= -this  ->  kill switch
    max_order_value: float = 0.0        # Rs per order cap (0 = use amount per position)
    product: str = "INTRADAY"           # MIS

    @property
    def per_position(self):
        if self.size_mode == "equal":
            n = max(self.n_stocks, 1) if self.no_limit else max(self.max_open, 1)
            return self.capital / n
        return self.position_amount if self.position_amount > 0 else self.capital / self.max_open

    @property
    def size_text(self):
        if self.size_mode == "qty":
            return f"qty/position {int(self.position_qty)}"
        return ("equal weight " if self.size_mode == "equal" else "amount/position ") + f"{self.per_position:,.0f}"

    def size_qty(self, one_lot, lot, cash):
        """(qty the sizing rule alone allows, qty after the free-cash cap) - in shares (lots x lot size for NFO/MCX)."""
        if self.size_mode == "qty":
            n = max(int(self.position_qty), 0)
            n_cash = math.floor(max(cash, 0) / one_lot) if one_lot > 0 else 0
            return n * lot, min(n, n_cash) * lot
        return (math.floor(self.per_position / one_lot) * lot,
                math.floor(min(self.per_position, cash) / one_lot) * lot)


def _cfg_from_data(d):
    """Config from a saved config.json dict (paper and live files)."""
    return Config(
        capital=float(d.get("capital", 0) or 0),
        max_open=int(d.get("max_open", 5)),
        target_pct=float(d.get("target_pct", 1.0)),
        sl_pct=float(d.get("sl_pct", 0) or 0),
        interval=d.get("interval", "FIVE_MINUTE"),
        tf_min=int(d.get("tf_min", 5)),
        position_amount=float(d.get("position_amount") or 0),
        size_mode=str(d.get("size_mode") or "amount"),
        position_qty=int(d.get("position_qty") or 0),
        n_stocks=len(d.get("items") or []),
        no_limit=bool(d.get("no_limit", False)),
        cloud_filter=cloud_text(d.get("cloud_filter")),
        cloud_exit=",".join(k for k in cloud_list(d.get("cloud_exit")) if k in CLOUD_EXIT_OPTS),
        live=bool(d.get("live", False)),
        limit_buffer_pct=float(d.get("limit_buffer_pct", 0.1) or 0.1),
        max_daily_loss=float(d.get("max_daily_loss", 0) or 0),
        max_order_value=float(d.get("max_order_value", 0) or 0),
        product=str(d.get("product", "INTRADAY") or "INTRADAY"),
        max_hold=int(d.get("max_hold", MAX_HOLD_DAYS) or MAX_HOLD_DAYS),
        patterns=tuple(p for p in (d.get("patterns") or PATTERNS) if p in PATTERNS) or PATTERNS,
    )


# ============================== TIME ==============================
def now_ist():
    return pd.Timestamp.now(tz=IST).tz_localize(None)


def market_open(now, exchange="NSE"):
    start, end = (dtime(9, 0), dtime(23, 30)) if exchange == "MCX" else (dtime(9, 15), dtime(15, 30))
    return now.weekday() < 5 and start <= now.time() <= end


def exit_time(exchange):
    return dtime(23, 15) if exchange == "MCX" else dtime(15, 15)


def session_done(now):
    return now.weekday() < 5 and now.time() > dtime(15, 30)


# ============================== PATTERNS ==============================
def detect_patterns(df, cfg=None):
    """True/False per candle for every pattern: the pattern ENDS on that candle (its last candle)."""
    o, h, l, c = (df[x].astype(float) for x in ("open", "high", "low", "close"))

    def candle(sh):
        return SimpleNamespace(o=o.shift(sh), h=h.shift(sh), l=l.shift(sh), c=c.shift(sh))

    sig = pd.DataFrame(
        {name: fn([candle(n - 1 - j) for j in range(n)]) for name, n, fn, _ in PATTERN_DEFS},
        index=df.index,
    )
    lb = int(getattr(cfg, "trend_lookback", 0) or 0)
    if lb > 0:
        sig = sig.mul(c.shift(1) < c.shift(lb + 1), axis=0).astype(bool)
    return sig.fillna(False).astype(bool)


def classify_candles(r, only=None):
    """Re-check the candles saved with an entry (hist, or the old prev/sig pair) against the formulas."""
    hist = r.get("hist")
    if not isinstance(hist, (list, tuple)) or not hist:
        try:
            hist = [[r["prev_O"], r["prev_H"], r["prev_L"], r["prev_C"]],
                    [r["sig_O"], r["sig_H"], r["sig_L"], r["sig_C"]]]
        except (KeyError, TypeError):
            return None
    try:
        df = pd.DataFrame(hist, columns=["open", "high", "low", "close"]).astype(float)
    except (ValueError, TypeError):
        return None
    if df.empty or df.iloc[-1].isna().any():
        return None
    sig = detect_patterns(df)
    names = [n for n in (only or PATTERNS) if n in sig.columns and bool(sig[n].iat[-1])]
    return " + ".join(names) if names else "No pattern"


# ============================== ICHIMOKU CLOUD (optional entry filter) ==============================
CLOUD_OPTIONS = ("Above", "Center", "Below")      # last closed candle: above the cloud / inside the cloud / below the cloud
CLOUD_LABEL = {"Above": "Above cloud", "Center": "Center (inside cloud)", "Below": "Below cloud"}
CLOUD_BY_LABEL = {v: k for k, v in CLOUD_LABEL.items()}
LIVE_OPTS = ("Stop loss %", "Limit buffer %", "Max daily loss (Rs)", "Max order value (Rs)")   # Live settings dropdown
CLOUD_EXIT_OPTS = ("Above", "Below")               # Exit condition: exit when the candle reaches this side of the cloud


def cloud_list(v):
    """Saved cloud filter -> list of positions. Accepts '' / 'Above' / 'Above,Center' / a list."""
    parts = v if isinstance(v, (list, tuple, set)) else str(v or "").split(",")
    got = {str(x).strip() for x in parts}
    return [k for k in CLOUD_OPTIONS if k in got]


def cloud_text(v):
    """Canonical saved form: '' (filter off) or e.g. 'Above,Center'."""
    return ",".join(cloud_list(v))
CLOUD_MIN_BARS = 78                               # Senkou B needs 52 candles + the cloud is drawn 26 candles ahead
# calendar days of history to load when the cloud filter is ON (so the cloud has >= CLOUD_MIN_BARS candles)
CLOUD_DAYS = {"ONE_MINUTE": 5, "THREE_MINUTE": 5, "FIVE_MINUTE": 6, "TEN_MINUTE": 8, "FIFTEEN_MINUTE": 10,
              "THIRTY_MINUTE": 18, "ONE_HOUR": 35, "FOUR_HOUR": 130, "ONE_DAY": 160}


def ichimoku_cloud(df, tenkan=9, kijun=26, senkou_b=52, shift=26):
    """Standard Ichimoku (9, 26, 52, 26). Row t holds the cloud as DRAWN under candle t
       (Senkou A / B calculated `shift` candles earlier)."""
    h, l = df["high"].astype(float), df["low"].astype(float)

    def mid(n):
        return (h.rolling(n).max() + l.rolling(n).min()) / 2

    span_a = ((mid(tenkan) + mid(kijun)) / 2).shift(shift)
    span_b = mid(senkou_b).shift(shift)
    return pd.DataFrame({"span_a": span_a, "span_b": span_b,
                         "top": np.maximum(span_a, span_b), "bottom": np.minimum(span_a, span_b)}, index=df.index)


def cloud_position(df):
    """'Above' / 'Center' / 'Below' for the LAST candle's close vs the cloud, or None when there are too few candles."""
    if df is None or len(df) < CLOUD_MIN_BARS:
        return None
    last = ichimoku_cloud(df).iloc[-1]
    if pd.isna(last["top"]) or pd.isna(last["bottom"]):
        return None
    close = float(df["close"].iat[-1])
    return "Above" if close > last["top"] else "Below" if close < last["bottom"] else "Center"


# ============================== ANGEL ONE ==============================
def angel_login(api_key, client_id, mpin, totp_secret):
    try:
        import pyotp
        from SmartApi import SmartConnect
    except ImportError:
        return None, "Install first:  pip install smartapi-python pyotp"
    try:
        smart = SmartConnect(api_key=api_key.strip())
        otp = pyotp.TOTP(totp_secret.replace(" ", "").strip()).now()
        res = smart.generateSession(client_id.strip(), mpin.strip(), otp)
        if not res or not res.get("status"):
            return None, f"Login failed: {(res or {}).get('message', 'unknown error')}"
        return smart, None
    except Exception as ex:
        return None, f"Login error: {ex}"


def _to_ist_naive(series):
    return pd.to_datetime(series, utc=True).dt.tz_convert(IST).dt.tz_localize(None)


CANDLE_CALL_GAP = 0.6
_GAP_LOCK, _GAP_LAST = threading.Lock(), {}
QUOTE_BACKOFF = [0.0]


def _gap(kind, gap):
    """Minimum seconds between two calls of the same Angel API kind (all threads share it)."""
    with _GAP_LOCK:
        wait = _GAP_LAST.get(kind, 0.0) + gap - time.time()
        if wait > 0:
            time.sleep(wait)
        _GAP_LAST[kind] = time.time()


def _is_rate_err(msg):
    m = str(msg).lower()
    return "access rate" in m or "exceeding" in m or "too many" in m
_RATE_LOCK, _RATE_LAST = threading.Lock(), [0.0]


def _rate_wait():
    with _RATE_LOCK:
        wait = _RATE_LAST[0] + CANDLE_CALL_GAP - time.time()
        if wait > 0:
            time.sleep(wait)
        _RATE_LAST[0] = time.time()


def _candles(smart, item, interval, start, end):
    params = {
        "exchange": item["exchange"], "symboltoken": str(item["token"]), "interval": interval,
        "fromdate": start.strftime("%Y-%m-%d %H:%M"), "todate": end.strftime("%Y-%m-%d %H:%M"),
    }
    for _ in range(4):
        _rate_wait()
        try:
            res = smart.getCandleData(params)
        except Exception as ex_:
            res = None
            LAST_API_ERROR["candle"] = f"{type(ex_).__name__}: {ex_}"
        if res and res.get("status") and res.get("data") is not None:
            if not res["data"]:
                return pd.DataFrame()
            d = pd.DataFrame(res["data"], columns=["date", "open", "high", "low", "close", "volume"])
            d["date"] = _to_ist_naive(d["date"])
            return d
        time.sleep(6 if _is_rate_err(LAST_API_ERROR.get("candle", "")) else 3)
    return pd.DataFrame()


def _resample_4h(d, exchange):
    """1-hour candles -> 4-hour candles aligned to the session start (NSE/BSE/NFO 09:15, MCX 09:00)."""
    sh, sm = (9, 0) if exchange == "MCX" else (9, 15)
    d = d.sort_values("date").copy()
    day = d["date"].dt.normalize()
    mins = (d["date"] - day).dt.total_seconds() // 60 - (sh * 60 + sm)
    d["_g"], d["_d"] = (mins // 240).astype(int), day
    out = d.groupby(["_d", "_g"], sort=True).agg(
        date=("date", "first"), open=("open", "first"), high=("high", "max"),
        low=("low", "min"), close=("close", "last"), volume=("volume", "sum"),
    ).reset_index(drop=True)
    return out


def candle_end(ts, tf, exchange):
    """When a candle that starts at ts is complete. 4H / day candles end at the market close, not ts + tf."""
    end = ts + tf
    if tf >= pd.Timedelta(minutes=240):
        close = ts.normalize() + (pd.Timedelta(hours=23, minutes=30) if exchange == "MCX"
                                  else pd.Timedelta(hours=15, minutes=30))
        end = min(end, close)
    return end


def fetch_candles(smart, item, interval, now, cloud=False):
    def days(default):                      # cloud filter ON -> load enough history for the Ichimoku cloud
        return max(default, CLOUD_DAYS.get(interval, default)) if cloud else default

    if interval == "FOUR_HOUR":
        d = _candles(smart, item, "ONE_HOUR", now - pd.Timedelta(days=days(45)), now)
        if not d.empty:
            d = _resample_4h(d, item["exchange"])
    elif interval == "ONE_DAY":
        d = _candles(smart, item, "ONE_DAY", now - pd.Timedelta(days=days(90)), now)
    else:
        d = _candles(smart, item, interval, now - pd.Timedelta(days=days(5)), now)
    return d[["date", "open", "high", "low", "close"]] if not d.empty else d


def fetch_bars(smart, item, since, now):
    d = _candles(smart, item, "ONE_MINUTE", since, now)
    return d.set_index("date")[["open", "high", "low", "close"]] if not d.empty else d


def fetch_ltp(smart, item):
    try:
        _gap("ltp", 0.2)
        res = smart.ltpData(item["exchange"], item["tradingsymbol"], str(item["token"]))
        return float(res["data"]["ltp"])
    except Exception:
        return None


LAST_API_ERROR = {"quote": "", "bulk": ""}


def _quote_from(d):
    ltp = float(d["ltp"])
    return {"ts": time.time(),
        "open": float(d.get("open", ltp)), "high": float(d.get("high", ltp)),
        "low": float(d.get("low", ltp)), "close": float(d.get("close", ltp)), "ltp": ltp,
    }


def fetch_quote(smart, item):
    try:
        _gap("ltp", 0.2)
        res = smart.ltpData(item["exchange"], item["tradingsymbol"], str(item["token"]))
        d = (res or {}).get("data")
        if not d:
            LAST_API_ERROR["quote"] = str((res or {}).get("message") or res)
            return None
        return _quote_from(d)
    except Exception as ex:
        LAST_API_ERROR["quote"] = f"{type(ex).__name__}: {ex}"
        return None


QUOTE_CHUNK = 50          # Angel getMarketData accepts max 50 tokens per request -> send big lists in chunks


def fetch_quotes_bulk(smart, items):
    """{token: quote}. Any number of stocks (sent in chunks of 50). Returns None only when NOTHING came back
       (failed / rate limited) - the caller must NOT hammer per-item calls."""
    if time.time() < QUOTE_BACKOFF[0]:
        LAST_API_ERROR["bulk"] = "rate limited - waiting"
        return None
    out = {}
    try:
        by_ex = {}
        for it in items:
            by_ex.setdefault(it["exchange"], []).append(str(it["token"]))
        reqs = [{ex: toks[i:i + QUOTE_CHUNK]} for ex, toks in by_ex.items() for i in range(0, len(toks), QUOTE_CHUNK)]
        for req in reqs:
            _gap("bulk", 1.2)
            res = smart.getMarketData("OHLC", req)
            fetched = ((res or {}).get("data") or {}).get("fetched") or []
            if not fetched:
                msg = str((res or {}).get("message") or res)[:200]
                LAST_API_ERROR["bulk"] = msg
                if _is_rate_err(msg):
                    QUOTE_BACKOFF[0] = time.time() + 4
                    break                      # stop now, keep what we already got
                continue                       # other chunks may still work
            for r in fetched:
                try:
                    out[str(r["symbolToken"])] = _quote_from(r)
                except (KeyError, TypeError, ValueError):
                    continue
    except Exception as ex:
        msg = f"{type(ex).__name__}: {ex}"
        LAST_API_ERROR["bulk"] = msg
        if _is_rate_err(msg):
            QUOTE_BACKOFF[0] = time.time() + 4
    return out or None


# ============================== LIVE ORDER HELPERS ==============================
ORDER_FINAL = ("complete", "rejected", "cancelled")
LIVE_KEYS = ("live", "sl_pct", "limit_buffer_pct", "max_daily_loss", "max_order_value", "product", "max_hold")
PRODUCT_LABEL = {"INTRADAY": "Intraday (MIS)", "DELIVERY": "Delivery (CNC)", "MARGIN": "Margin",
                 "CARRYFORWARD": "Carry Forward (NRML)"}
PRODUCTS_BY_EXCHANGE = {
    "NSE": ["INTRADAY", "DELIVERY", "MARGIN"], "BSE": ["INTRADAY", "DELIVERY", "MARGIN"],
    "NFO": ["INTRADAY", "CARRYFORWARD"], "MCX": ["INTRADAY", "CARRYFORWARD"],
}
_OB_LOCK, _OB_LAST = threading.Lock(), [0.0]


def round_tick(price, tick, up):
    """Round a price to the exchange tick. up=True -> next tick up, up=False -> tick down."""
    tick = float(tick) if tick and float(tick) > 0 else 0.05
    n = price / tick
    n = math.ceil(n - 1e-9) if up else math.floor(n + 1e-9)
    return round(max(n, 1) * tick, 2)


def _ostat(row):
    r = row or {}
    return str(r.get("orderstatus") or r.get("status") or "").strip().lower()


def _ofilled(row):
    try:
        return int(float((row or {}).get("filledshares") or 0))
    except (TypeError, ValueError):
        return 0


def _oavg(row, default):
    try:
        v = float((row or {}).get("averageprice") or 0)
        return v if v > 0 else float(default)
    except (TypeError, ValueError):
        return float(default)


def order_book_map(smart):
    """{orderid: row} from Angel One order book (max 1 call / 1.1 s). None = could not read."""
    with _OB_LOCK:
        wait = _OB_LAST[0] + 1.1 - time.time()
        if wait > 0:
            time.sleep(wait)
        try:
            res = smart.orderBook()
        except Exception as ex:
            LAST_API_ERROR["order"] = f"{type(ex).__name__}: {ex}"
            _OB_LAST[0] = time.time()
            return None
        _OB_LAST[0] = time.time()
    if not isinstance(res, dict) or not res.get("status"):
        LAST_API_ERROR["order"] = str((res or {}).get("message") if isinstance(res, dict) else res)[:200]
        return None
    return {str(r.get("orderid")): r for r in (res.get("data") or [])}


def place_live_order(smart, item, side, qty, price, product="INTRADAY"):
    """LIMIT order (market / IOC are not allowed for algo orders). Returns (order_id, error)."""
    params = {
        "variety": "NORMAL", "tradingsymbol": item["tradingsymbol"], "symboltoken": str(item["token"]),
        "transactiontype": side, "exchange": item["exchange"], "ordertype": "LIMIT",
        "producttype": product, "duration": "DAY", "price": f"{price:.2f}",
        "squareoff": "0", "stoploss": "0", "quantity": str(int(qty)),
    }
    try:
        # placeOrderFullResponse gives Angel One's real reply (message + errorcode); plain placeOrder hides it
        full = getattr(smart, "placeOrderFullResponse", None)
        res = full(params) if callable(full) else smart.placeOrder(params)
    except Exception as ex:
        return None, f"{type(ex).__name__}: {ex}"
    if isinstance(res, dict):
        oid = (res.get("data") or {}).get("orderid") if res.get("status") else None
        if oid:
            return str(oid), None
        msg = f"{res.get('message') or 'no message'} (errorcode {res.get('errorcode') or '-'})"
        return None, msg[:220]
    if res:
        return str(res), None
    return None, ("no order id returned by SmartAPI - Angel One blocked / failed the order "
                  "(static IP not registered? API key without trading permission?)")


def fetch_broker_funds(smart):
    """Available margin (Rs) in the Angel One account (RMS). None = could not read (caller must not block on it)."""
    try:
        _gap("rms", 1.1)
        res = smart.rmsLimit()
        d = (res or {}).get("data") or {}
        for k in ("net", "availablecash"):
            v = d.get(k)
            if v not in (None, ""):
                return float(v)
    except Exception as ex:
        LAST_API_ERROR["order"] = f"funds: {type(ex).__name__}: {ex}"
    return None


def fetch_circuit(smart, item):
    """(lower, upper) circuit price of a stock from the FULL quote, or None. An order outside this band is REJECTED."""
    try:
        _gap("bulk", 1.2)
        res = smart.getMarketData("FULL", {item["exchange"]: [str(item["token"])]})
        row = (((res or {}).get("data") or {}).get("fetched") or [None])[0] or {}
        lo, hi = float(row.get("lowerCircuit") or 0), float(row.get("upperCircuit") or 0)
        if lo > 0 or hi > 0:
            return lo, hi
    except Exception as ex:
        LAST_API_ERROR["order"] = f"circuit: {type(ex).__name__}: {ex}"
    return None


def reject_text(row):
    """Why Angel One / the exchange rejected an order (order book 'text' field)."""
    r = row or {}
    return str(r.get("text") or r.get("rejectionreason") or r.get("message") or "no reason given").strip()[:160]


def cancel_order(smart, order_id):
    try:
        smart.cancelOrder(str(order_id), "NORMAL")
        return True
    except Exception:
        return False


def wait_order(smart, order_id, timeout):
    """Poll the order book until the order is complete / rejected / cancelled or timeout. Returns last row (or None)."""
    end, row = time.time() + timeout, None
    while True:
        book = order_book_map(smart)
        if book is not None:
            row = book.get(str(order_id), row)
            if row is not None and _ostat(row) in ORDER_FINAL:
                return row
        if time.time() >= end:
            return row


def _fail_note(*engines):
    n = sum(int(getattr(e, "exit_failed", 0) or 0) for e in engines)
    return (f"  ⚠️ {n} LIVE position(s) EXIT FAILED - Square off manually in the Angel One app!" if n else "")


# ============================== INSTRUMENTS ==============================
NIFTY50_FALLBACK = (
    "ADANIENT ADANIPORTS APOLLOHOSP ASIANPAINT AXISBANK BAJAJ-AUTO BAJFINANCE BAJAJFINSV BEL BHARTIARTL CIPLA "
    "COALINDIA DRREDDY EICHERMOT ETERNAL GRASIM HCLTECH HDFCBANK HDFCLIFE HEROMOTOCO HINDALCO HINDUNILVR ICICIBANK "
    "INDUSINDBK INFY ITC JIOFIN JSWSTEEL KOTAKBANK LT M&M MARUTI NESTLEIND NTPC ONGC POWERGRID RELIANCE SBILIFE "
    "SBIN SHRIRAMFIN SUNPHARMA TATACONSUM TATAMOTORS TATASTEEL TCS TECHM TITAN TRENT ULTRACEMCO WIPRO"
).split()


@st.cache_data(ttl=86400, show_spinner=False)
def nifty50():
    try:
        r = requests.get(
            "https://niftyindices.com/IndexConstituent/ind_nifty50list.csv",
            headers={"User-Agent": "Mozilla/5.0"}, timeout=15,
        )
        r.raise_for_status()
        syms = pd.read_csv(io.StringIO(r.text))["Symbol"].str.strip().tolist()
        if len(syms) >= 40:
            return syms
    except Exception:
        pass
    return list(NIFTY50_FALLBACK)


MASTER_CACHE = "scrip_master_cache.pkl"


@st.cache_resource(ttl=86400, show_spinner=False)
def load_master():
    if os.path.exists(MASTER_CACHE) and pd.Timestamp(os.path.getmtime(MASTER_CACHE), unit="s").date() == pd.Timestamp.now().date():
        try:
            cached = pd.read_pickle(MASTER_CACHE)
            if "tick_size" in cached.columns:
                return cached
        except Exception:
            pass
    df = pd.DataFrame(requests.get(MASTER_URL, timeout=120).json())
    df.columns = [c.strip().lower() for c in df.columns]
    keep = [c for c in ("exch_seg", "symbol", "name", "token", "lotsize", "instrumenttype", "expiry", "tick_size") if c in df.columns]
    df = df[keep]
    try:
        df.to_pickle(MASTER_CACHE)
    except Exception:
        pass
    return df


def search_item(smart, exchange, text):
    cache = st.session_state.setdefault("search_cache", {})
    key = f"{exchange}:{text}"
    if key not in cache:
        cache[key] = None
        try:
            rows = (smart.searchScrip(exchange, text) or {}).get("data") or []
            rows = [r for r in rows if r["tradingsymbol"].upper() in (text, text + "-EQ")] or rows
            if rows:
                r = rows[0]
                cache[key] = {
                    "symbol": r["tradingsymbol"].replace("-EQ", ""),
                    "tradingsymbol": r["tradingsymbol"],
                    "token": r["symboltoken"], "exchange": exchange, "lot": 1,
                }
        except Exception:
            pass
    return cache[key]


SENSEX30 = set(
    "ADANIPORTS ASIANPAINT AXISBANK BAJFINANCE BAJAJFINSV BHARTIARTL ETERNAL HCLTECH HDFCBANK HINDUNILVR ICICIBANK "
    "INFY ITC KOTAKBANK LT M&M MARUTI NESTLEIND NTPC POWERGRID RELIANCE SBIN SUNPHARMA TATAMOTORS TATASTEEL TCS "
    "TECHM TITAN TRENT ULTRACEMCO".split()
)
MCX_MAIN = set(("GOLD GOLDM GOLDPETAL GOLDGUINEA SILVER SILVERM SILVERMIC CRUDEOIL CRUDEOILM NATURALGAS NATGASMINI "
                "COPPER ZINC ZINCMINI ALUMINIUM ALUMINI LEAD LEADMINI NICKEL").split())
NFO_INDEX = {"NIFTY", "BANKNIFTY", "FINNIFTY", "MIDCPNIFTY"}


NSE_INDEX_FILES = {          # niftyindices.com constituent CSVs
    "Nifty 50": "ind_nifty50list", "Nifty Next 50": "ind_niftynext50list", "Nifty 100": "ind_nifty100list",
    "Nifty Bank": "ind_niftybanklist", "Nifty IT": "ind_niftyitlist", "Nifty Midcap 100": "ind_niftymidcap100list",
    "Nifty Auto": "ind_niftyautolist", "Nifty Pharma": "ind_niftypharmalist", "Nifty FMCG": "ind_niftyfmcglist",
    "Nifty Metal": "ind_niftymetallist", "Nifty Financial Services": "ind_niftyfinancelist",
}
MCX_GROUPS = {
    "Bullion": {"GOLD", "GOLDM", "GOLDPETAL", "GOLDGUINEA", "SILVER", "SILVERM", "SILVERMIC"},
    "Energy": {"CRUDEOIL", "CRUDEOILM", "NATURALGAS", "NATGASMINI"},
    "Base Metals": {"COPPER", "ZINC", "ZINCMINI", "ALUMINIUM", "ALUMINI", "LEAD", "LEADMINI", "NICKEL"},
}


def index_options(exchange):
    """Names for the 'Index' box under Exchange."""
    if exchange == "NSE":
        return list(NSE_INDEX_FILES)
    if exchange == "BSE":
        return ["Sensex 30"]
    if exchange == "NFO":
        return ["Index futures", "Nifty 50 stock futures"]
    return list(MCX_GROUPS)


@st.cache_data(ttl=86400, show_spinner=False)
def nse_index_members(index):
    """Symbols of one NSE index ([] when the download fails)."""
    if index == "Nifty 50":
        return nifty50()
    f = NSE_INDEX_FILES.get(index)
    if not f:
        return []
    try:
        r = requests.get(f"https://niftyindices.com/IndexConstituent/{f}.csv",
                         headers={"User-Agent": "Mozilla/5.0"}, timeout=15)
        r.raise_for_status()
        return [x.strip() for x in pd.read_csv(io.StringIO(r.text))["Symbol"].astype(str) if x.strip()]
    except Exception:
        return []


def index_members(exchange, index):
    """Upper-case names of the chosen indices (tuple of names; None / empty -> the exchange's default list)."""
    if not index:
        if exchange == "NFO":
            return NFO_INDEX | set(nifty50())
        if exchange == "MCX":
            return MCX_MAIN
        return set(SENSEX30) if exchange == "BSE" else {x.upper() for x in nifty50()}
    out = set()
    for ix in index:
        if exchange == "NSE":
            out |= {x.upper() for x in nse_index_members(ix)}
        elif exchange == "BSE":
            out |= set(SENSEX30)
        elif exchange == "NFO":
            out |= NFO_INDEX if ix == "Index futures" else set(nifty50())
        else:
            out |= set(MCX_GROUPS.get(ix, MCX_MAIN))
    return out


def exchange_list(df, exchange, index=None):
    index = tuple(index) if index else None
    d = df[df["exch_seg"] == exchange].copy()
    nm = d["name"].fillna("").str.upper()
    sy = d["symbol"].fillna("").str.upper()
    base = index_members(exchange, index)
    if exchange == "NSE":
        d = d[sy.str.endswith("-EQ") & nm.isin(base)]
        d["label"] = d["name"]
    elif exchange == "BSE":
        d = d[nm.isin(SENSEX30) | sy.isin(SENSEX30)]
        d["label"] = d["name"].where(nm.isin(SENSEX30), d["symbol"])
    else:
        itype = d["instrumenttype"].fillna("") if "instrumenttype" in d else pd.Series("", index=d.index)
        if exchange == "NFO" and not index:
            base = NFO_INDEX | set(nifty50())
        d = d[itype.str.startswith("FUT") & nm.isin(base)]
        d["exp"] = pd.to_datetime(d["expiry"], format="%d%b%Y", errors="coerce")
        d = d[d["exp"] >= pd.Timestamp.now().normalize()].sort_values("exp")
        d = d.drop_duplicates("name")
        d["label"] = d["symbol"]
    return d.drop_duplicates("label").sort_values("label")


@st.cache_data(ttl=3600, show_spinner=False)
def exchange_list_cached(exchange, index=None):
    return exchange_list(load_master(), exchange, tuple(index) if index else None)


def no_dim():
    st.markdown(
        """<style>
        [data-stale="true"], .stale-element, [data-testid="stElementContainer"][data-stale="true"],
        [data-testid="stSidebar"] [data-stale="true"] { opacity: 1 !important; transition: none !important; }
        </style>""",
        unsafe_allow_html=True,
    )


def to_item(row, exchange):
    try:
        lot = max(int(float(row.get("lotsize") or 1)), 1) if exchange in ("NFO", "MCX") else 1
    except ValueError:
        lot = 1
    try:
        tick = float(row.get("tick_size") or 5) / 100.0          # master gives tick in paise
        tick = tick if tick > 0 else 0.05
    except (TypeError, ValueError):
        tick = 0.05
    return {
        "symbol": row["label"], "tradingsymbol": row["symbol"], "token": row["token"],
        "exchange": exchange, "lot": lot, "tick": tick,
    }


# ============================== STRATEGY PATHS ==============================
def _safe_name(name: str) -> str:
    """Folder / file name safe for disk (no path tricks)."""
    name = re.sub(r"[^\w\s\-]", "", name.strip())
    name = re.sub(r"\s+", "_", name)
    return name[:80] or "unnamed"


def user_strategies_root(uid: str) -> str:
    """Per-user folder under absolute DATA_DIR (always absolute path)."""
    if uid == OWNER_ID:
        root = STRATEGIES_ROOT
    else:
        root = os.path.join(_DATA_DIR, "users", uid, "strategies")
    os.makedirs(root, exist_ok=True)
    return root


def strategy_dir(uid: str, folder: str, file: str) -> str:
    return os.path.join(user_strategies_root(uid), _safe_name(folder), _safe_name(file))


def folder_mode_of(fp: str) -> str:
    """'live' or 'paper' (marker file .mode; older folders: live if any file inside is live)."""
    mf = os.path.join(fp, ".mode")
    try:
        if os.path.exists(mf):
            v = open(mf).read().strip().lower()
            if v in ("live", "paper"):
                return v
        for fname in os.listdir(fp):
            cp = os.path.join(fp, fname, "config.json")
            if os.path.exists(cp) and _read_json(cp).get("live"):
                return "live"
    except Exception:
        pass
    return "paper"


def list_strategies(uid: str, mode: str = None) -> dict:
    """
    Returns {folder: [{file, path, running, exchange, tf_label, capital, ...}, ...]}
    """
    root = user_strategies_root(uid)
    out = {}
    if not os.path.isdir(root):
        return out
    for folder in sorted(os.listdir(root)):
        fp = os.path.join(root, folder)
        if not os.path.isdir(fp) or folder.startswith("."):
            continue
        files = []
        for fname in sorted(os.listdir(fp)):
            fpath = os.path.join(fp, fname)
            if not os.path.isdir(fpath) or fname.startswith("."):
                continue
            cfg_path = os.path.join(fpath, "config.json")
            if not os.path.exists(cfg_path):
                continue
            meta = {"file": fname, "path": fpath, "folder": folder}
            try:
                meta.update(_read_json(cfg_path))
            except Exception:
                pass
            eng = _get_engine_by_path(uid, fpath)
            meta["running"] = bool(eng.running) if eng else False     # real state only (same as inside the file page)
            meta["was_running"] = False
            if not meta["running"]:
                # run_config.json still says "running" after an app restart / crash, but nothing is running now
                rf = os.path.join(fpath, "run_config.json")
                if os.path.exists(rf):
                    try:
                        meta["was_running"] = bool(_read_json(rf).get("running"))
                    except Exception:
                        pass
            files.append(meta)
        if mode:                                   # keep Paper and Live completely apart
            files = [m for m in files if bool(m.get("live")) == (mode == "live")]
            if not files and folder_mode_of(fp) != mode:
                continue
        out[folder] = files          # empty folders are kept
    return out


def create_folder(uid: str, name: str, mode: str = "paper") -> str:
    """Create an (empty) folder for 'paper' or 'live'. Raises ValueError if the name belongs to the other mode."""
    safe = _safe_name(name)
    fp = os.path.join(user_strategies_root(uid), safe)
    if os.path.isdir(fp) and folder_mode_of(fp) != mode:
        raise ValueError(f"'{safe}' a {folder_mode_of(fp).upper()} folder with this name already exists - please use a different name.")
    os.makedirs(fp, exist_ok=True)
    mf = os.path.join(fp, ".mode")
    if not os.path.exists(mf):
        with open(mf, "w") as f:
            f.write(mode)
    return safe


def save_strategy_config(uid: str, folder: str, file: str, data: dict) -> str:
    """Create folder/file and write config.json. Returns absolute strategy path."""
    path = strategy_dir(uid, folder, file)
    os.makedirs(path, exist_ok=True)
    data = dict(data)
    data["folder"] = _safe_name(folder)
    data["file"] = _safe_name(file)
    data["updated"] = str(now_ist())
    cfg_path = os.path.join(path, "config.json")
    with open(cfg_path, "w") as f:
        json.dump(data, f, indent=1, default=str)
    # verify write
    if not os.path.exists(cfg_path):
        raise RuntimeError(f"Failed to save config at {cfg_path}")
    return path


def load_strategy_config(path: str) -> dict:
    cfg_path = os.path.join(path, "config.json")
    if os.path.exists(cfg_path):
        try:
            return _read_json(cfg_path)
        except Exception:
            pass
    return {}


def delete_strategy(uid: str, folder: str, file: str):
    path = strategy_dir(uid, folder, file)
    if load_strategy_config(path).get("live"):
        return                                   # LIVE strategies are never deleted (real trade record)
    eng = _get_engine_by_path(uid, path)
    if eng and eng.running:
        eng.stop()
    import shutil
    if os.path.isdir(path):
        shutil.rmtree(path, ignore_errors=True)


# ============================== STATE ==============================
def _read_json(path, default=None):
    """json.load that survives an empty / half-written / missing file."""
    try:
        with open(path) as f:
            data = json.load(f)
        return data if isinstance(data, type(default if default is not None else {})) else (default if default is not None else {})
    except Exception:
        return default if default is not None else {}


def load_state(path):
    s = {}
    if os.path.exists(path):
        try:
            with open(path) as f:
                s = json.load(f)
            if not isinstance(s, dict):
                raise ValueError("state is not a dict")
        except Exception:
            try:                                  # keep the broken file for inspection, start clean
                os.replace(path, path + ".corrupt")
            except OSError:
                pass
            s = {}
    for k in ("open", "closed", "handled", "log", "signals"):
        s.setdefault(k, [])
    s.setdefault("slot_last", {})
    s.setdefault("orders", [])
    stale = [p for p in s["open"] if p.get("pending")]
    if stale:                                   # nothing can be in flight at load time -> leftover from a crash
        s["open"] = [p for p in s["open"] if not p.get("pending")]
        for p in stale:
            s["log"].append(f"{now_ist():%Y-%m-%d %H:%M:%S}  CRITICAL {p['symbol']}: pending BUY order "
                            f"{p.get('entry_order_id') or '-'} found after restart - check Angel One app")
    s["_path"] = path
    s.pop("waiting", None)
    for g in s["signals"]:
        if str(g.get("status", "")).startswith(("WAITING", "EXPIRED")):
            g["status"] = "SKIPPED (positions were full)"
    return s


def save_state(state, path=None):
    path = path or state.get("_path")
    if not path:
        return
    tmp = f"{path}.{threading.get_ident()}.tmp"        # write whole file, then swap -> never a half-written json
    with open(tmp, "w") as f:
        json.dump({k: v for k, v in state.items() if not k.startswith("_")}, f, indent=1, default=str)
    os.replace(tmp, path)


def add_log(state, now, msg):
    state["log"].append(f"{pd.Timestamp(now):%Y-%m-%d %H:%M:%S}  {msg}")
    state["log"] = state["log"][-200:]


def _fill_slots(state):
    used = {p["slot"] for p in state["open"] if p.get("slot")}
    for p in sorted([p for p in state["open"] if not p.get("slot")], key=lambda p: str(p.get("entry_time"))):
        n = 1
        while n in used:
            n += 1
        p["slot"] = n
        used.add(n)


def _pick_slot(state, now):
    _fill_slots(state)
    used = {p["slot"] for p in state["open"]}
    today = f"{pd.Timestamp(now):%Y-%m-%d}"
    last = state.setdefault("slot_last", {})
    fresh = [
        (str(v.get("exit_time", "")), int(k))
        for k, v in last.items()
        if int(k) not in used and str(v.get("exit_time", ""))[:10] == today
    ]
    if fresh:
        slot = min(fresh)[1]
        return slot, last[str(slot)]
    n = 1
    while n in used:
        n += 1
    return n, None


# ============================== PATTERN OUTLOOK ==============================
def predict_patterns(done, forming, ltp, cfg):
    lb = cfg.trend_lookback
    if len(done) < lb + 2:
        return "Not enough candles"
    sel = [p for p in cfg.patterns if p in PATTERNS]
    p = done.iloc[-1]
    po, pc, pl = float(p["open"]), float(p["close"]), float(p["low"])
    parts = []
    if pc < po and (lb == 0 or pc < float(done["close"].iloc[-1 - lb])):
        if "Bullish Engulfing" in sel:
            parts.append(f"Engulfing if close > {po:.2f}")
        if "Bullish Harami" in sel:
            parts.append(f"Harami if open > {pc:.2f} and close < {po:.2f}")
        if "Tweezer Bottom" in sel:
            parts.append(f"Tweezer if low ~ {pl:.2f}")
    others = [n for n in sel if n not in ("Bullish Engulfing", "Bullish Harami", "Tweezer Bottom")]
    if others:
        parts.append(f"{len(others)} more pattern(s) checked when the candle closes")
    return ("WATCH: " + " | ".join(parts)) if parts else "No setup"


# ============================== EXIT ==============================
def _check_exit(pos, bars):
    sl, tg = pos.get("stop_loss"), pos["target"]
    entry_min = pd.Timestamp(pos["entry_time"]).floor("min")       # the entry minute still has pre-entry prices
    since = max(pd.Timestamp(pos["last_checked"]), entry_min + pd.Timedelta(minutes=1))
    for ts, r in bars[bars.index >= since].iterrows():
        if sl:
            if r["open"] <= sl:
                return float(r["open"]), ts, "SL (gap)"
            if r["low"] <= sl:
                return sl, ts, "SL"
        if tg and r["open"] >= tg:
            return float(r["open"]), ts, "Target (gap)"
        if tg and r["high"] >= tg:
            return tg, ts, "Target"
    return None


def _close(state, cfg, pos, raw_px, when, reason):
    exit_px = raw_px * (1 - cfg.slippage_pct / 100)
    qty = pos["qty"]
    pnl = (exit_px - pos["entry"]) * qty - cfg.brokerage_pct / 100 * (pos["entry"] + exit_px) * qty
    risk = (pos["entry"] - pos["stop_loss"]) * qty if pos.get("stop_loss") else 0
    if pos.get("virtual"):
        reason = f"{reason} (tracking only, no order)"
    done = {k: pos[k] for k in ("symbol", "exchange", "pattern", "signal_date", "entry_time",
                                "entry", "stop_loss", "target", "qty")}
    if pos.get("virtual"):
        done["virtual"] = True
    done.update({k: pos[k] for k in STORE_KEYS + ("signal_close",) if k in pos})
    done.update({
        "exit_time": str(pd.Timestamp(when).floor("s")), "exit": round(exit_px, 2),
        "reason": reason, "pnl": round(pnl, 2),
        "r_multiple": round(pnl / risk, 2) if risk > 0 else None,
    })
    _fill_slots(state)
    slot = pos.get("slot")
    done["slot"] = slot
    state["closed"].append(done)
    state["open"] = [p for p in state["open"] if p is not pos]
    if slot:
        state.setdefault("slot_last", {})[str(slot)] = {
            "symbol": pos["symbol"], "reason": reason, "exit_time": done["exit_time"],
        }
    add_log(
        state, now_ist(),
        f"CLOSED {pos['symbol']} @ {exit_px:.2f}  {reason}  (candle {pd.Timestamp(when):%H:%M})  P&L {pnl:,.2f}"
        f"{f'  (position #{slot} is free now)' if slot else ''}",
    )


def check_exits(state, cfg, now, bars_fn, ignore_hours=False):
    for pos in list(state["open"]):
        if pos.get("live"):
            continue                      # live positions are managed with real orders (_manage_live)
        try:
            bars = bars_fn(pos, pd.Timestamp(pos["last_checked"]))
        except Exception as ex:
            add_log(state, now, f"price error {pos['symbol']}: {ex}")
            continue
        if bars is None or bars.empty:
            continue
        hit = _check_exit(pos, bars)
        if hit:
            _close(state, cfg, pos, hit[0], hit[1], hit[2])
            continue
        pos.setdefault("last_price", float(bars["close"].iloc[-1]))
        pos["last_checked"] = str(bars.index[-1])
        held = int(np.busday_count(pos["entry_time"][:10], str(now.date()))) + 1
        if held >= cfg.max_hold and (ignore_hours or now.time() >= exit_time(pos["exchange"])):
            _close(state, cfg, pos, pos["last_price"], now, "Time exit")


# ============================== ENGINE ==============================
def margin_factor(exchange):
    return FUTURES_MARGIN_PCT / 100 if exchange in ("NFO", "MCX") else 1.0


def candle_boundary(now, exchange, tf_min):
    start = now.normalize() + (pd.Timedelta(hours=9) if exchange == "MCX" else pd.Timedelta(hours=9, minutes=15))
    if now < start:
        return start
    step = pd.Timedelta(minutes=tf_min)
    return start + ((now - start) // step) * step


class Engine:
    GRACE = 4
    EXIT_EVERY = 15
    QUOTE_EVERY = 1.5

    def __init__(self, uid, strategy_path):
        self.uid = uid
        self.strategy_path = strategy_path
        os.makedirs(strategy_path, exist_ok=True)
        self.state_file = os.path.join(strategy_path, "live_state.json")
        self.run_file = os.path.join(strategy_path, "run_config.json")
        self.lock = threading.RLock()
        self.thread = None
        self.stop_evt = threading.Event()
        self.qthread = None
        self.state = load_state(self.state_file)
        self.smart = self.cfg = None
        self.creds, self.client_id, self.login_time = None, "", 0.0
        self.items, self.exchange, self.ignore = [], "NSE", False
        self._clear_runtime()

    def _clear_runtime(self):
        self.cache, self.quotes, self.rows = {}, {}, []
        self.quote_errors, self.cycle_errors = [], []
        self.status, self.last_update, self.last_exit_check = "", None, 0.0
        self.pending, self.kill, self.exit_failed = 0, False, 0
        self.reject_until, self.pause_until = {}, 0.0      # per-stock / all-entries cooldown after a REJECTED order

    @property
    def running(self):
        return self.thread is not None and self.thread.is_alive() and not self.stop_evt.is_set()

    def set_login(self, smart, creds, client_id):
        self.smart, self.creds, self.client_id, self.login_time = smart, creds, client_id, time.time()

    def _save_run_config(self, running):
        if self.cfg is None:
            return
        try:
            with open(self.run_file, "w") as f:
                json.dump(
                    {
                        "running": running, "exchange": self.exchange, "ignore": self.ignore,
                        "items": self.items, "cfg": asdict(self.cfg),
                    },
                    f, default=str,
                )
        except Exception:
            pass

    def try_autoresume(self, shared_smart=None, shared_creds=None, shared_client_id=""):
        try:
            if not os.path.exists(self.run_file):
                return
            rc = _read_json(self.run_file)
            if not rc.get("running"):
                return
            if (rc.get("cfg") or {}).get("live") and not LIVE_AUTORESUME:
                with self.lock:
                    add_log(self.state, now_ist(), "LIVE strategy NOT auto-resumed after restart - open Live tab and press Start "
                                                   "(check Angel One for open positions / orders first)")
                self.status = "Live strategy was running before restart - press Start manually"
                return
            smart = shared_smart
            creds = shared_creds
            if smart is None:
                creds = env_creds()
                if not creds:
                    return
                smart, err = angel_login(*creds)
                if err:
                    self.status = f"Auto-resume login failed: {err}"
                    return
            cd = rc["cfg"]
            cd["patterns"] = tuple(cd.get("patterns", PATTERNS))
            self.set_login(smart, creds or shared_creds, (shared_client_id or (creds[1] if creds else "")).strip().upper())
            self.start(smart, Config(**cd), rc["items"], rc["exchange"], rc.get("ignore", False))
            with self.lock:
                if cd.get("live"):
                    add_log(self.state, now_ist(), f"LIVE auto-resumed after restart - {len(self.state['open'])} open position(s) kept "
                                                   "(check Angel One for open positions / orders)")
                else:
                    add_log(self.state, now_ist(), "Auto-resumed after restart")
        except Exception as ex:
            self.status = f"Auto-resume failed: {ex}"

    def start(self, smart, cfg, items, exchange, ignore_hours=False):
        self.stop()
        with self.lock:
            self.smart, self.cfg, self.items = smart, cfg, list(items)      # no stock-count limit (quotes are fetched in chunks of 50)
            self.exchange, self.ignore = exchange, ignore_hours
            self._clear_runtime()
            self.status = "Starting..."
            self.stop_evt = threading.Event()
            self.thread = threading.Thread(target=self._loop, args=(self.stop_evt,), daemon=True)
            self.qthread = threading.Thread(target=self._quote_loop, args=(self.stop_evt,), daemon=True)
            self.thread.start()
            self.qthread.start()
        self._save_run_config(True)

    def stop(self):
        self.stop_evt.set()
        for t in (self.thread, self.qthread):
            if t is not None and t.is_alive() and t is not threading.current_thread():
                t.join(timeout=2)
        self.thread = self.qthread = None
        self.status = "Stopped"
        self._save_run_config(False)

    @property
    def has_run(self):
        """True once this file was started before (this session or earlier) -> Resume is possible."""
        return self.cfg is not None or os.path.exists(self.run_file)

    def resume(self, smart, cfg, items, exchange, ignore_hours=False):
        """Start again after Stop: same file, open positions + closed trades are kept."""
        self.start(smart, cfg, items, exchange, ignore_hours)
        with self.lock:
            add_log(self.state, now_ist(), f"RESUMED - {len(self.state['open'])} open position(s) kept")
            save_state(self.state)

    def delete_closed(self, idx, expect=None):
        """Delete ONE closed trade (paper only). expect = the trade dict the user selected (safety re-match)."""
        keys = ("symbol", "entry_time", "exit_time")
        with self.lock:
            c = self.state["closed"]
            if expect is not None and not (0 <= idx < len(c) and all(c[idx].get(k) == expect.get(k) for k in keys)):
                idx = next((i for i, t in enumerate(c) if all(t.get(k) == expect.get(k) for k in keys)), -1)
            if 0 <= idx < len(c):
                c.pop(idx)
                save_state(self.state)
                return True
        return False

    def reset_all(self):
        self.stop()
        with self.lock:
            if os.path.exists(self.state_file):
                os.remove(self.state_file)
            self.state = load_state(self.state_file)
            self._clear_runtime()

    def close_now(self, key):
        with self.lock:
            target = next((p for p in self.state["open"] if f"{p['exchange']}:{p['symbol']}" == key), None)
        if target is None:
            return
        if target.get("pending"):
            return                                    # BUY order still in flight - the engine finishes it in a few seconds
        if target.get("live"):
            self._exit_live(target, "Manual exit")
            return
        with self.lock:
            _close(self.state, self.cfg or Config(), target, target["last_price"], now_ist(), "Manual exit")
            save_state(self.state)

    def manual_buy(self, it):
        """OPTIONAL manual BUY of one stock: same amount / target / SL as this file's pattern entries
           (paper = virtual position, LIVE = real LIMIT BUY + target SELL). Needs the strategy to be running."""
        cfg, smart = self.cfg, self.smart
        if cfg is None or smart is None or not self.running:
            return False, "Start the strategy first - only then will the manual Buy go through"
        now = now_ist()
        ex, sym = it["exchange"], it["symbol"]
        if not (self.ignore or market_open(now, ex)):
            return False, "Market is closed - an order cannot be placed now"

        def blocked():
            if self.kill:
                return "kill switch active (max daily loss)"
            if cfg.live and time.time() < self.pause_until:
                return "entries paused (broker margin/funds rejection)"
            if cfg.live and time.time() < self.reject_until.get(sym, 0):
                return "paused after a rejected order on this stock"
            if any(p["exchange"] == ex and p["symbol"] == sym for p in self.state["open"]):
                return "already in position"
            n_open = len([x for x in self.state["open"] if not x.get("pending")]) + self.pending
            if not cfg.no_limit and n_open >= cfg.max_open:
                return f"positions full {n_open}/{cfg.max_open}"
            return None

        with self.lock:
            b = blocked()
        if b:
            return False, f"Could not place Buy: {b}"
        ltp = fetch_ltp(smart, it)
        if ltp is None:
            return False, "Price (LTP) not available - please try again in a little while"
        ctime = now.floor("min")
        rec = {"time": str(now.floor("s")), "symbol": sym, "exchange": ex, "pattern": "Manual BUY",
               "candle": str(ctime), "status": "ENTERED"}
        with self.lock:
            b = blocked()
            if b:
                return False, f"Could not place Buy: {b}"
            if not cfg.live:
                self._enter(it, rec, ctime, ltp, now)
                return rec["status"] == "ENTERED", rec["status"]
            self.pending += 1
        try:
            self._enter_live(it, rec, ctime, ltp, now)
        except Exception as ex_:
            with self.lock:
                add_log(self.state, now, f"ERROR manual live entry {sym}: {ex_} - check the order in the Angel One app")
                self.state["open"] = [x for x in self.state["open"] if not (x.get("pending") and x["symbol"] == sym)]
                save_state(self.state)
            return False, f"Error: {ex_} - check in the Angel One app"
        finally:
            with self.lock:
                self.pending -= 1
        return rec.get("status") == "ENTERED", str(rec.get("status"))

    def manual_buy_all(self, items):
        """OPTIONAL bulk BUY: one BUY for every stock of the file (same amount / target / SL as pattern entries);
           stops when positions are full. Meant to run in a background thread (one LTP call per stock)."""
        ok_n, why = 0, []
        for it in items:
            if not self.running:
                break
            done, msg = self.manual_buy(it)
            if done:
                ok_n += 1
                continue
            why.append(f"{it['symbol']}: {msg}")
            if any(x in msg for x in ("positions full", "kill switch", "Market close", "Strategy Start", "paused")):
                break
        with self.lock:
            add_log(self.state, now_ist(),
                    f"BUY ALL: {ok_n}/{len(items)} entered" + (f" - {'; '.join(why[:3])}" if why else ""))
            save_state(self.state)
        return ok_n

    def manual_sell_all(self):
        """OPTIONAL bulk SELL: closes every open position of this file; the strategy keeps running."""
        with self.lock:
            keys = [f"{p['exchange']}:{p['symbol']}" for p in self.state["open"] if not p.get("pending")]
        for k in keys:
            self.close_now(k)
        with self.lock:
            add_log(self.state, now_ist(), f"SELL ALL: {len(keys)} position(s) closed")
            save_state(self.state)
        return len(keys)

    def delete_position(self, key):
        with self.lock:
            self.state["open"] = [p for p in self.state["open"] if f"{p['exchange']}:{p['symbol']}" != key]
            save_state(self.state)

    def update_config(self, cfg):
        """Change target %, max positions, amount, capital (and LIVE SL %, limit buffer, max daily loss,
           max order value) of a RUNNING strategy - no restart, positions untouched.
           New values are used immediately: the engine reads self.cfg every cycle (~1-3 s).
           LIVE: a new SL % is also applied to the already-open live positions (software SL),
           and a changed max-daily-loss limit is checked against today's P&L right away."""
        with self.lock:
            old = self.cfg
            self.cfg = cfg
            if old is not None and (cfg.cloud_filter != old.cloud_filter or cfg.cloud_exit != old.cloud_exit):
                for c in self.cache.values():       # reload candles at the next cycle (cloud needs a longer history)
                    c["b"] = None
            if cfg.live and old is not None:
                now = now_ist()
                if cfg.sl_pct != old.sl_pct:
                    for p in self.state["open"]:
                        if p.get("live"):
                            p["stop_loss"] = round(float(p["entry"]) * (1 - cfg.sl_pct / 100), 2) if cfg.sl_pct > 0 else None
                    add_log(self.state, now, f"SL changed {old.sl_pct}% -> {cfg.sl_pct}% (applied to open live positions)")
                    save_state(self.state)
                if cfg.max_daily_loss != old.max_daily_loss:
                    day = self._day_pnl()
                    if cfg.max_daily_loss > 0 and day <= -cfg.max_daily_loss:
                        self.kill = True
                        add_log(self.state, now, f"KILL SWITCH: new max daily loss {cfg.max_daily_loss:,.0f} already hit "
                                                 f"(day P&L {day:,.0f}) - closing all live positions")
                    elif self.kill:
                        self.kill = False
                        add_log(self.state, now, f"Kill switch released - max daily loss changed to {cfg.max_daily_loss:,.0f}")
                    else:
                        add_log(self.state, now, f"Max daily loss changed to {cfg.max_daily_loss:,.0f}")
        self._save_run_config(self.running)

    def exit_all(self, reason="Manual exit (Exit)"):
        """EXIT = stop the strategy (no new entries) and close every open position at its last price.
           Returns how many positions were closed. Works even if the strategy is already stopped."""
        self.stop()
        self.exit_failed = 0
        with self.lock:
            cfg = self.cfg or Config()
            positions = [p for p in self.state["open"] if not p.get("pending")]
        n = 0
        for p in positions:
            if p.get("live"):
                if self._exit_live(p, reason):          # real SELL orders (outside the lock)
                    n += 1
            else:
                with self.lock:
                    _close(self.state, cfg, p, p.get("last_price") or p["entry"], now_ist(), reason)
                n += 1
        with self.lock:
            save_state(self.state)
        try:                                              # a stopped file must not be auto-resumed after a restart
            if os.path.exists(self.run_file):
                with open(self.run_file) as f:
                    rc = json.load(f)
                rc["running"] = False
                with open(self.run_file, "w") as f:
                    json.dump(rc, f, default=str)
        except Exception:
            pass
        return n

    def exit_selected(self, keys, reason="Manual exit (selected)"):
        """Close ONLY the chosen open positions (keys = 'EXCH:SYMBOL'). The strategy keeps running.
           Returns how many positions were closed."""
        keys = set(keys)
        self.exit_failed = 0
        with self.lock:
            cfg = self.cfg or Config()
            positions = [p for p in self.state["open"]
                         if not p.get("pending") and f"{p['exchange']}:{p['symbol']}" in keys]
        n = 0
        for p in positions:
            if p.get("live"):
                if self._exit_live(p, reason):              # real SELL order (outside the lock)
                    n += 1
            else:
                with self.lock:
                    _close(self.state, cfg, p, p.get("last_price") or p["entry"], now_ist(), reason)
                n += 1
        with self.lock:
            save_state(self.state)
        return n

    def snapshot(self):
        with self.lock:
            return {
                "state": copy.deepcopy(self.state), "rows": list(self.rows),
                "errors": list(self.quote_errors) + list(self.cycle_errors),
                "status": self.status, "last_update": self.last_update, "running": self.running,
                "cfg": self.cfg, "exchange": self.exchange,
            }

    # ---------------------------- LIVE (real orders) ----------------------------
    def _day_pnl(self):
        today = f"{now_ist():%Y-%m-%d}"
        realized = sum(float(t.get("pnl") or 0) for t in self.state["closed"]
                       if str(t.get("exit_time", ""))[:10] == today and not t.get("virtual"))
        unreal = sum((float(p.get("last_price") or p["entry"]) - float(p["entry"])) * float(p["qty"])
                     for p in self.state["open"] if not p.get("pending") and not p.get("virtual"))
        return realized + unreal

    def _note_reject(self, sym, reason, now):
        """A broker rejection must not be repeated every candle (each one is a 'rejected' line in Angel One's history)."""
        low = str(reason).lower()
        if "ab4036" in low or "cautionary" in low:
            # Exchange cautionary listing (ASM/GSM etc): Angel One blocks API orders until the client accepts the
            # risk disclosure in the Angel One app/web. Retrying every candle is useless -> skip this stock today.
            left = max(int((pd.Timestamp(now).normalize() + pd.Timedelta(days=1) - pd.Timestamp(now)).total_seconds()), 60)
            with self.lock:
                self.reject_until[sym] = time.time() + left
                add_log(self.state, now, f"{sym}: CAUTIONARY LISTING (AB4036) - skipped for today. Place one manual BUY for this "
                                         "stock in the Angel One app and accept the risk acknowledgement; API orders can work after that")
            return
        funds = any(w in low for w in ("margin", "fund", "insufficient", "limit exceed"))
        with self.lock:
            if funds:
                if FUNDS_PAUSE_SEC > 0:
                    self.pause_until = time.time() + FUNDS_PAUSE_SEC
                    add_log(self.state, now, f"Entries PAUSED {FUNDS_PAUSE_SEC // 60} min - broker says not enough margin/funds")
                else:
                    add_log(self.state, now, f"{sym}: broker rejected - not enough margin/funds (no pause, next signal will retry)")
            else:
                self.reject_until[sym] = time.time() + 1800
                add_log(self.state, now, f"{sym}: no new orders for 30 min after rejection")

    def _live_skip(self, rec, now, why):
        with self.lock:
            rec["status"] = f"SKIPPED ({why})"
            self.state["signals"] = (self.state["signals"] + [rec])[-200:]
            add_log(self.state, now, f"SKIPPED {rec['symbol']}: {why}  ({rec['pattern']})")
            save_state(self.state)

    def _enter_live(self, it, rec, ctime, price, now):
        """BUY limit (INTRADAY) -> wait for fill -> resting SELL limit at target."""
        cfg, smart = self.cfg, self.smart
        ex, sym = it["exchange"], it["symbol"]
        tf = pd.Timedelta(minutes=cfg.tf_min)
        tick = float(it.get("tick") or 0.05)
        lot, mf = int(it.get("lot", 1)), margin_factor(ex)
        buy_px = round_tick(price * (1 + cfg.limit_buffer_pct / 100), tick, True)
        with self.lock:
            cash = (cfg.capital + sum(t["pnl"] for t in self.state["closed"] if not t.get("virtual"))
                    - sum(p["entry"] * p["qty"] * p.get("mf", 1.0) for p in self.state["open"] if not p.get("virtual")))
        bf = fetch_broker_funds(smart)                 # real Angel One margin - app capital may be higher than the account
        if bf is not None:
            cash = min(cash, bf)
        circ = fetch_circuit(smart, it)                # (lower, upper) - orders outside the band are rejected
        est_tgt = round_tick(buy_px * (1 + cfg.target_pct / 100), tick, True) if cfg.target_pct > 0 else None
        if circ:                                        # only a warning - the broker decides, order goes anyway
            lo_c, hi_c = circ
            if (est_tgt and hi_c > 0 and est_tgt > hi_c) or (lo_c > 0 and buy_px < lo_c):
                with self.lock:
                    add_log(self.state, now, f"WARN {sym}: price/target outside circuit band {lo_c:.2f}-{hi_c:.2f} - sending order anyway")
        one_lot = buy_px * lot * mf
        unit = "share" if ex in ("NSE", "BSE") else "lot"
        qty_amt, qty = cfg.size_qty(one_lot, lot, cash)                 # qty_amt = what the sizing rule alone allows
        if cfg.max_order_value > 0:
            qty = min(qty, math.floor(cfg.max_order_value / (buy_px * lot)) * lot)
        if qty < 1 and qty_amt >= 1:
            # Funds are low but amount/position is fine: do NOT pre-skip. Send the real order and let
            # Angel One decide - a margin rejection then shows as "rejected" in the Angel One order history.
            qty_cap = qty_amt
            if cfg.max_order_value > 0:
                qty_cap = min(qty_cap, math.floor(cfg.max_order_value / (buy_px * lot)) * lot)
            if qty_cap >= 1:
                qty = qty_cap
                with self.lock:
                    add_log(self.state, now, f"{sym}: free cash {cash:,.0f} < {one_lot:,.0f} - sending the order anyway, "
                                             "broker will accept or reject")
        if qty < 1:
            # say the REAL blocker (the old text always blamed amount/position)
            why = []
            if qty_amt < 1:
                why.append(f"1 {unit} needs {one_lot:,.0f} > {cfg.size_text}")
            if cfg.max_order_value > 0 and math.floor(cfg.max_order_value / (buy_px * lot)) < 1:
                why.append(f"1 {unit} costs {buy_px * lot:,.0f} > max order value {cfg.max_order_value:,.0f}")
            if qty_amt >= 1 and cash < one_lot:
                bf_txt = f" (Angel One funds {bf:,.0f})" if bf is not None else ""
                why.append(f"not enough funds: free cash {cash:,.0f}{bf_txt} < {one_lot:,.0f} needed")
            why_txt = "; ".join(why) or "quantity 0"
            if qty_amt >= 1:                    # strategy amount is fine -> still show it in Live positions (tracking only)
                return self._enter_virtual(it, rec, ctime, price, now, qty_amt, mf, why_txt)
            return self._live_skip(rec, now, f"{why_txt} (no order sent)")
        # ---- every check passed -> the entry shows in Live positions FIRST (like paper trading) ----
        with self.lock:
            slot, replaced = _pick_slot(self.state, now)
            pos = {
                "slot": slot, "live": True, "pending": True, "order_status": "SENDING BUY ORDER...", "tick": tick,
                "symbol": sym, "tradingsymbol": it["tradingsymbol"], "token": it["token"], "exchange": ex,
                "pattern": rec["pattern"], "signal_date": str(ctime), "signal_close": str(candle_end(ctime, tf, ex)),
                "entry_time": str(now.floor("s")), "entry": round(buy_px, 2), "stop_loss": None,
                "target": est_tgt, "qty": int(qty), "mf": mf,
                "entry_order_id": None, "tgt_order_id": None,
                "product": cfg.product, "tgt_day": f"{now:%Y-%m-%d}",
                "last_price": price, "last_checked": str(now.floor("min")),
                **{k: rec[k] for k in STORE_KEYS if k in rec},
            }
            self.state["open"].append(pos)
            add_log(self.state, now, f"LIVE ENTRY SIGNAL {sym} @ {buy_px:.2f} qty {qty} ({rec['pattern']}) "
                                     f"-> position #{slot}, sending BUY order")
            save_state(self.state)
        # ---- then the order ----
        oid, err = place_live_order(smart, it, "BUY", qty, buy_px, cfg.product)
        if not oid:
            self._note_reject(sym, err, now)
            return self._drop_pending(pos, rec, now, "REJECTED", err)
        with self.lock:
            pos["entry_order_id"] = oid
            pos["order_status"] = f"BUY PLACED ({oid})"
            save_state(self.state)
        row = wait_order(smart, oid, 10)
        if _ostat(row) == "rejected":
            why = reject_text(row)
            self._note_reject(sym, why, now)
            return self._drop_pending(pos, rec, now, "REJECTED", why)
        if _ostat(row) != "complete":
            cancel_order(smart, oid)
            row = wait_order(smart, oid, 5) or row
        if row is None:
            with self.lock:
                add_log(self.state, now, f"CRITICAL {sym}: BUY order {oid} status UNKNOWN - check in the Angel One app!")
            return self._drop_pending(pos, rec, now, "UNKNOWN", f"order {oid} status unknown - check Angel One app")
        filled = _ofilled(row)
        if filled < 1:
            if _ostat(row) == "rejected":
                why = reject_text(row)
                self._note_reject(sym, why, now)
                return self._drop_pending(pos, rec, now, "REJECTED", why)
            return self._drop_pending(pos, rec, now, "CANCELLED", f"BUY not filled @ {buy_px:.2f}")
        entry = _oavg(row, buy_px)
        tgt = round_tick(entry * (1 + cfg.target_pct / 100), tick, True) if cfg.target_pct > 0 else None
        if tgt and circ and circ[1] > 0 and tgt > circ[1]:
            tgt = round_tick(circ[1], tick, False)     # never send a target above the upper circuit (would be rejected)
        t_oid, t_err = place_live_order(smart, it, "SELL", filled, tgt, cfg.product) if tgt else (None, None)
        with self.lock:
            pos.update({
                "pending": False, "entry": round(entry, 2), "qty": int(filled), "target": tgt, "tgt_order_id": t_oid,
                "stop_loss": round(entry * (1 - cfg.sl_pct / 100), 2) if cfg.sl_pct > 0 else None,
                "order_status": ("FILLED - target order placed" if t_oid
                                 else "FILLED - software target" if tgt else "FILLED - exit on cloud / SL / time"),
            })
            rec["status"] = "ENTERED"
            self.state["signals"] = (self.state["signals"] + [rec])[-200:]
            self._log_order(pos, now, "BUY", "FILLED", f"filled {filled} @ {entry:.2f}", oid)
            add_log(self.state, now,
                    f"LIVE ENTRY {sym} @ {entry:.2f}  qty {filled}  TGT {(f'{tgt:.2f}' if tgt else 'none')}  order {oid}  "
                    f"({rec['pattern']})  -> position #{pos['slot']}")
            if tgt and not t_oid:
                self._log_order(pos, now, "SELL (target)", "REJECTED", str(t_err), "-")
                add_log(self.state, now, f"WARN {sym}: target order failed ({t_err}) - software target will be used")
            save_state(self.state)

    def _enter_virtual(self, it, rec, ctime, price, now, qty, mf, why):
        """Signal is valid but a real order is not possible (funds / order-value cap).
           Entry still shows in Live positions and is tracked like paper trading (target / SL / time exit),
           NO order is sent to Angel One and it does not touch cash or the kill switch."""
        cfg = self.cfg
        tf = pd.Timedelta(minutes=cfg.tf_min)
        ex, sym = it["exchange"], it["symbol"]
        tick = float(it.get("tick") or 0.05)
        entry = round_tick(price, tick, True)
        tgt = round_tick(entry * (1 + cfg.target_pct / 100), tick, True) if cfg.target_pct > 0 else None
        with self.lock:
            slot, _ = _pick_slot(self.state, now)
            self.state["open"].append({
                "slot": slot, "virtual": True, "tick": tick,
                "order_status": f"TRACKING ONLY - no order sent ({why})",
                "symbol": sym, "tradingsymbol": it["tradingsymbol"], "token": it["token"], "exchange": ex,
                "pattern": rec["pattern"], "signal_date": str(ctime), "signal_close": str(candle_end(ctime, tf, ex)),
                "entry_time": str(now.floor("s")), "entry": round(entry, 2),
                "stop_loss": round(entry * (1 - cfg.sl_pct / 100), 2) if cfg.sl_pct > 0 else None,
                "target": tgt, "qty": int(qty), "mf": mf,
                "last_price": price, "last_checked": str(now.floor("min")),
                **{k: rec[k] for k in STORE_KEYS if k in rec},
            })
            rec["status"] = f"ENTERED - tracking only, no order ({why})"
            self.state["signals"] = (self.state["signals"] + [rec])[-200:]
            add_log(self.state, now, f"TRACKING ENTRY {sym} @ {entry:.2f} qty {qty} TGT {(f'{tgt:.2f}' if tgt else 'none')} "
                                     f"({rec['pattern']}) -> position #{slot}; no real order: {why}")
            save_state(self.state)

    def _log_order(self, pos, now, side, status, reason, oid):
        """Order status list shown under Live positions (call with the lock held)."""
        orders = self.state.setdefault("orders", [])
        orders.append({"time": str(now.floor("s")), "symbol": pos["symbol"], "side": side, "qty": pos["qty"],
                       "price": pos["entry"], "status": status, "reason": reason, "order_id": oid or "-"})
        self.state["orders"] = orders[-100:]

    def _drop_pending(self, pos, rec, now, status, why):
        """BUY rejected / cancelled / unknown: it never became a real position - remove it from Live positions."""
        with self.lock:
            self.state["open"] = [x for x in self.state["open"] if x is not pos]
            rec["status"] = f"{status} ({why})"
            self.state["signals"] = (self.state["signals"] + [rec])[-200:]
            self._log_order(pos, now, "BUY", status, why, pos.get("entry_order_id"))
            add_log(self.state, now, f"BUY {status} {pos['symbol']}: {why}  ({rec['pattern']})")
            save_state(self.state)

    def _exit_live(self, p, reason, evt=None):
        """Cancel resting target, SELL limit near LTP (escalating buffer), then record the close. True = closed."""
        cfg, smart = self.cfg or Config(), self.smart
        now = now_ist()
        if smart is None:
            with self.lock:
                add_log(self.state, now, f"CRITICAL {p['symbol']}: no Angel login - cannot exit")
            self.exit_failed += 1
            return False
        tick = float(p.get("tick") or 0.05)
        p.setdefault("orig_qty", int(p["qty"]))
        fills = p.setdefault("exit_fills", [])

        def remaining():
            return p["orig_qty"] - sum(int(q) for q, _ in fills)

        toid = p.get("tgt_order_id")
        if toid and p.get("tgt_day") not in (None, f"{now:%Y-%m-%d}"):
            p["tgt_order_id"] = toid = None            # yesterday's DAY order has already expired
        if toid:
            cancel_order(smart, toid)
            row = wait_order(smart, toid, 4)
            if row is None or _ostat(row) not in ORDER_FINAL:
                with self.lock:
                    add_log(self.state, now, f"CRITICAL {p['symbol']}: target order {toid} state unknown - exit postponed")
                p["exit_retry_at"] = time.time() + 15
                self.exit_failed += 1
                return False
            f = _ofilled(row)
            if f > 0:
                fills.append((f, _oavg(row, p["target"])))
            p["tgt_order_id"] = None
        base = max(cfg.limit_buffer_pct, 0.05)
        circ = fetch_circuit(smart, p)
        for attempt in range(3):
            if remaining() <= 0 or (evt is not None and evt.is_set()):
                break
            q = self.quotes.get((p["exchange"], p["symbol"])) or {}
            ltp = q.get("ltp") or p.get("last_price") or p["entry"]
            px = round_tick(ltp * (1 - base * (2 ** attempt) / 100), tick, False)
            if circ:
                if circ[0] > 0 and px < circ[0]:
                    px = round_tick(circ[0], tick, True)
                if circ[1] > 0 and px > circ[1]:
                    px = round_tick(circ[1], tick, False)
            oid, err = place_live_order(smart, p, "SELL", remaining(), px, p.get("product") or cfg.product)
            if not oid:
                with self.lock:
                    add_log(self.state, now, f"WARN {p['symbol']}: SELL order rejected ({err})")
                continue
            row = wait_order(smart, oid, 8)
            if _ostat(row) == "rejected":
                with self.lock:
                    add_log(self.state, now, f"WARN {p['symbol']}: SELL REJECTED by Angel One: {reject_text(row)} - retry in 30s")
                break                          # same order again = another rejected line; wait and retry
            if _ostat(row) != "complete":
                cancel_order(smart, oid)
                row = wait_order(smart, oid, 5) or row
            if row is None:
                with self.lock:
                    add_log(self.state, now, f"CRITICAL {p['symbol']}: SELL {oid} status UNKNOWN - check Angel One app")
                p["exit_retry_at"] = time.time() + 30
                self.exit_failed += 1
                return False
            f = _ofilled(row)
            if f > 0:
                fills.append((f, _oavg(row, px)))
        if remaining() > 0:
            p["exit_retry_at"] = time.time() + 30
            self.exit_failed += 1
            with self.lock:
                add_log(self.state, now, f"CRITICAL {p['symbol']}: EXIT NOT COMPLETE ({remaining()} left) - "
                                         "Square off manually in the Angel One app")
                save_state(self.state)
            return False
        avg = sum(int(q) * float(px_) for q, px_ in fills) / p["orig_qty"]
        p["qty"] = p["orig_qty"]
        with self.lock:
            if any(x is p for x in self.state["open"]):
                _close(self.state, cfg, p, avg, now_ist(), reason)
                save_state(self.state)
        return True

    def _cloud_exits(self, evt):
        """Cloud exit: when the last CLOSED candle of an open position's stock REACHES the chosen side of the
           Ichimoku cloud (Above / Below), that position exits. 'Reaches' = the side changed to the chosen one.
           The candle the position was entered on only records the starting side, so e.g. entry above the cloud
           with exit 'Above' does not exit instantly - it exits when price leaves and comes back above."""
        cfg = self.cfg
        want = [k for k in cloud_list(cfg.cloud_exit) if k in CLOUD_EXIT_OPTS]
        if not want:
            return
        with self.lock:
            positions = [p for p in self.state["open"] if not p.get("pending")]
        for p in positions:
            if evt.is_set():
                return
            if p.get("exit_retry_at", 0) > time.time():
                continue
            key = (p["exchange"], p["symbol"])
            done = (self.cache.get(key) or {}).get("done")
            if done is None or len(done) < CLOUD_MIN_BARS:
                continue
            ctime = str(done["date"].iat[-1])
            if p.get("cloud_t") == ctime:                       # this candle was already judged
                continue
            pos, prev = cloud_position(done), p.get("cloud_pos")
            p["cloud_t"], p["cloud_pos"] = ctime, pos
            if pos is None or prev is None or pos == prev or pos not in want:
                continue
            reason = f"Cloud exit ({pos} cloud)"
            with self.lock:
                add_log(self.state, now_ist(), f"{p['symbol']}: candle closed {pos} cloud - exiting")
            if p.get("live"):
                if not self._exit_live(p, reason, evt):
                    p["cloud_t"], p["cloud_pos"] = None, prev    # exit failed -> try again
            else:
                q = self.quotes.get(key) or {}
                px = float(q.get("ltp") or p.get("last_price") or done["close"].iat[-1])
                with self.lock:
                    if any(x is p for x in self.state["open"]):
                        _close(self.state, cfg, p, px, now_ist(), reason)
                        save_state(self.state)

    def _manage_live(self, evt):
        """Every cycle: target filled? SL / software target / time exit / kill switch."""
        cfg, smart = self.cfg, self.smart
        now = now_ist()
        with self.lock:
            live_pos = [p for p in self.state["open"] if p.get("live") and not p.get("pending")]
            day = self._day_pnl()
        if cfg.max_daily_loss > 0 and day <= -cfg.max_daily_loss and not self.kill:
            self.kill = True
            with self.lock:
                add_log(self.state, now, f"KILL SWITCH: day P&L {day:,.0f} <= -{cfg.max_daily_loss:,.0f} - "
                                         "no new entries, closing all live positions")
        if not live_pos:
            return
        stale = [p["symbol"] for p in live_pos
                 if (self.quotes.get((p["exchange"], p["symbol"])) or {}).get("ts", time.time()) < time.time() - 20]
        if stale and time.time() - getattr(self, "_stale_warned", 0) > 60:
            self._stale_warned = time.time()
            with self.lock:
                add_log(self.state, now, "WARN price STALE (>20s) for " + ", ".join(stale) +
                        " - SL may not trigger (Angel API rate limit?). Target order is still on the exchange.")
        book = order_book_map(smart)
        for p in live_pos:
            if evt.is_set():
                return
            oid = p.get("tgt_order_id")
            if oid and book is not None:
                row = book.get(str(oid))
                st_ = _ostat(row)
                if st_ == "complete":
                    with self.lock:
                        if any(x is p for x in self.state["open"]):
                            _close(self.state, cfg, p, _oavg(row, p["target"]), now_ist(), "Target")
                            save_state(self.state)
                    continue
                if st_ in ("rejected", "cancelled"):
                    p["tgt_order_id"] = None
                    with self.lock:
                        add_log(self.state, now, f"WARN {p['symbol']}: target order {oid} {st_} - software target / SL / time exit active")
                elif row is None and p.get("tgt_day") not in (None, f"{now:%Y-%m-%d}"):
                    p["tgt_order_id"] = None           # target placed on an earlier day = expired (DAY order)
                    with self.lock:
                        add_log(self.state, now, f"{p['symbol']}: yesterday's target order expired - will re-place")
            prod = p.get("product") or cfg.product
            if p.get("target") and (not p.get("tgt_order_id")) and prod != "INTRADAY" and not p.get("exit_fills") \
                    and p.get("rearm_at", 0) <= time.time() and float(p.get("last_price") or 0) < p["target"]:
                n_oid, n_err = place_live_order(smart, p, "SELL", p["qty"], p["target"], prod)
                p["rearm_at"] = time.time() + (600 if n_oid else 120)
                if n_oid:
                    p["tgt_order_id"], p["tgt_day"] = n_oid, f"{now:%Y-%m-%d}"
                with self.lock:
                    add_log(self.state, now, f"{p['symbol']}: target order re-placed @ {p['target']:.2f} ({n_oid})"
                            if n_oid else f"WARN {p['symbol']}: target re-place failed ({n_err})")
            if p.get("exit_retry_at", 0) > time.time():
                continue
            ltp = float(p.get("last_price") or p["entry"])
            sl = p.get("stop_loss")
            reason = None
            if self.kill:
                reason = "Kill switch"
            elif sl and ltp <= sl:
                reason = "SL"
            elif p.get("target") and not p.get("tgt_order_id") and ltp >= p["target"]:
                reason = "Target (software)"
            elif now.time() >= exit_time(p["exchange"]) and (
                    (p.get("product") or cfg.product) == "INTRADAY"
                    or int(np.busday_count(p["entry_time"][:10], str(now.date()))) + 1 >= cfg.max_hold):
                reason = "Time exit"
            if reason:
                self._exit_live(p, reason, evt)

    def _loop(self, evt):
        while not evt.is_set():
            t0 = time.time()
            try:
                self._cycle(evt)
            except Exception as ex:
                with self.lock:
                    self.cycle_errors = [f"engine error: {ex}"]
            evt.wait(max(1.0, 3.0 - (time.time() - t0)))

    def _quote_loop(self, evt):
        while not evt.is_set():
            t0 = time.time()
            try:
                cfg, now = self.cfg, now_ist()
                if cfg is None:
                    evt.wait(1)
                    continue
                live_ok = self.ignore or market_open(now, self.exchange)
                B = candle_boundary(now, self.exchange, cfg.tf_min)
                errs = []
                self._refresh_quotes(self.items, live_ok, errs, evt, B)
                if evt.is_set():
                    return
                with self.lock:
                    self.quote_errors = errs
                self._build_rows(None, B, pd.Timedelta(minutes=cfg.tf_min), live_ok, final=False, persist=False)
            except Exception as ex:
                with self.lock:
                    self.quote_errors = [f"price error: {ex}"]
            evt.wait(max(0.2, self.QUOTE_EVERY - (time.time() - t0)))

    def _candle_due(self, key, B, now, live_ok):
        c = self.cache.get(key)
        if c is None:
            return True
        if c.get("retry_at") is not None:
            return time.time() >= c["retry_at"]
        if c["b"] == B or not live_ok:
            return False
        return now >= B + pd.Timedelta(seconds=self.GRACE)

    def _refresh_quotes(self, items, live_ok, errors, evt, B):
        got = fetch_quotes_bulk(self.smart, items)
        if got is None:                      # failed / rate limited: keep last prices, retry later
            errors.append(f"Angel API: {LAST_API_ERROR['bulk'][:90] or 'no reply'} - using last known prices, will retry")
            return
        fallback_left = 3                    # max 3 single-quote calls per cycle (rate limit safe)
        for it in items:
            if evt.is_set():
                return
            key = (it["exchange"], it["symbol"])
            q = got.get(str(it["token"]))
            if q is None and fallback_left > 0:
                fallback_left -= 1
                q = fetch_quote(self.smart, it)
            if not q:
                errors.append(f"{it['symbol']}: no live price")
                continue
            with self.lock:
                self.quotes[key] = q
                c = self.cache.get(key)
                if c:
                    f = c.get("forming")
                    if live_ok and (f is None or f.get("b") != B):
                        if f is not None and f.get("close") is not None:
                            c["roll"] = {"b": B, "close": f["close"]}
                        f = c["forming"] = {
                            "open": q["ltp"], "high": q["ltp"], "low": q["ltp"],
                            "close": q["ltp"], "b": B,
                        }
                    if f:
                        f["high"], f["low"] = max(f["high"], q["ltp"]), min(f["low"], q["ltp"])
                        f["close"] = q["ltp"]
        with self.lock:
            for p in self.state["open"]:
                q = self.quotes.get((p["exchange"], p["symbol"]))
                if q:
                    p["last_price"] = q["ltp"]

    def _build_rows(self, errors, B, tf, live_ok, final=True, persist=True):
        cfg = self.cfg
        with self.lock:
            open_keys = {(p["exchange"], p["symbol"]) for p in self.state["open"]}
            rows = []
            for it in self.items:
                key = (it["exchange"], it["symbol"])
                q, c = self.quotes.get(key), self.cache.get(key)
                row = {
                    "symbol": it["symbol"], "open": None, "high": None, "low": None, "ltp": None,
                    "prev_close": None, "change_%": None, "updated": f"{now_ist():%H:%M:%S}",
                    "position": "IN POSITION" if key in open_keys else "-",
                    **({"cloud": (c or {}).get("cloud") or "-"} if cfg.cloud_filter else {}),
                    "pattern_outlook": "Loading candles...",
                }
                if q:
                    row["ltp"] = q["ltp"]
                if c and c.get("done") is not None and len(c["done"]):
                    d, f = c["done"], c.get("forming")
                    if live_ok and f:
                        o, h, l, pc = f["open"], f["high"], f["low"], float(d["close"].iat[-1])
                        r = c.get("roll")
                        if c.get("b") != B and r and r["b"] == B:
                            pc = r["close"]
                    elif len(d) > 1:
                        o, h, l = (float(d[k].iat[-1]) for k in ("open", "high", "low"))
                        pc = float(d["close"].iat[-2])
                    else:
                        o = h = l = pc = None
                    if o is not None:
                        row.update({
                            "open": round(o, 2), "high": round(h, 2), "low": round(l, 2),
                            "prev_close": round(pc, 2),
                            "change_%": round((q["ltp"] / pc - 1) * 100, 2) if q and pc else None,
                        })
                if c and c.get("done") is not None:
                    row["pattern_outlook"] = predict_patterns(
                        c["done"], c.get("forming"), q["ltp"] if q else None, cfg
                    )
                rows.append(row)
            self.rows, self.last_update = rows, now_ist()
            if errors is not None:
                self.cycle_errors = list(errors)
            if final:
                self.status = (
                    "Waiting for the next candle (" + f"{(B + tf):%H:%M}" + ")"
                    if live_ok
                    else "Market closed - prices only, no entry / exit"
                )
            if persist:
                save_state(self.state)

    def _cycle(self, evt):
        if self.creds and time.time() - self.login_time > 8 * 3600:
            sm, err = angel_login(*self.creds)
            if sm is not None:
                self.smart, self.login_time = sm, time.time()
        cfg, items, smart, exch = self.cfg, self.items, self.smart, self.exchange
        if cfg is None or smart is None:
            return
        now = now_ist()
        live_ok = self.ignore or market_open(now, exch)
        tf = pd.Timedelta(minutes=cfg.tf_min)
        B = candle_boundary(now, exch, cfg.tf_min)
        errors = []

        due = [it for it in items if self._candle_due((it["exchange"], it["symbol"]), B, now, live_ok)]
        if due:
            from concurrent.futures import ThreadPoolExecutor
            counter = [0]

            def load_one(it):
                if evt.is_set():
                    return
                try:
                    self._load_candles(it, B, tf, live_ok)
                except Exception as ex:
                    errors.append(f"{it['symbol']}: {ex}")
                counter[0] += 1
                self.status = f"Loading candles {counter[0]}/{len(due)}"

            self.status = f"Loading candles 0/{len(due)}"
            with ThreadPoolExecutor(max_workers=3) as pool:
                list(pool.map(load_one, due))
            if evt.is_set():
                return

        if cfg.cloud_exit and live_ok:
            self._cloud_exits(evt)
            if evt.is_set():
                return

        if cfg.live and live_ok:
            self.status = "LIVE: managing orders / SL / target"
            self._manage_live(evt)
            if evt.is_set():
                return

        if live_ok and time.time() - self.last_exit_check >= self.EXIT_EVERY:
            with self.lock:
                snap = [dict(p) for p in self.state["open"] if not p.get("live")]
            bars_map = {}
            for p in snap:
                if evt.is_set():
                    return
                self.status = f"Checking exit {p['symbol']}"
                try:
                    bars_map[(p["exchange"], p["symbol"])] = fetch_bars(
                        smart, p, pd.Timestamp(p["last_checked"]), now_ist()
                    )
                except Exception as ex:
                    errors.append(f"{p['symbol']}: exit check failed ({ex})")
            with self.lock:
                check_exits(
                    self.state, cfg, now_ist(),
                    lambda it, since: bars_map.get((it["exchange"], it["symbol"])),
                    self.ignore,
                )
                save_state(self.state)
            self.last_exit_check = time.time()

        self._build_rows(errors, B, tf, live_ok, final=True)

    def _load_candles(self, it, B, tf, live_ok):
        cfg = self.cfg
        key = (it["exchange"], it["symbol"])
        df = fetch_candles(self.smart, it, cfg.interval, now_ist(), bool(cfg.cloud_filter or cfg.cloud_exit))
        if df is None or df.empty:
            fails = self.cache.get(key, {}).get("fails", 0) + 1
            with self.lock:
                self.cache[key] = {
                    "b": None if fails < 3 else B, "done": None, "forming": None, "tries": 0,
                    "fails": fails if fails < 3 else 0,
                    "retry_at": time.time() + 20 if fails < 3 else None,
                }
            raise RuntimeError(f"no candle data (try {fails})")
        nowf = now_ist()
        mask = df["date"].map(lambda t: candle_end(t, tf, it["exchange"])) <= nowf
        done, run = df[mask].reset_index(drop=True), df[~mask]
        forming = None if run.empty else {**{k: float(run.iloc[-1][k]) for k in ("open", "high", "low")}, "b": B}
        tries = self.cache.get(key, {}).get("tries", 0) + 1
        lag = (tf < pd.Timedelta(minutes=240) and live_ok and not done.empty
               and done["date"].iat[-1] < B - tf and tries < 3)
        with self.lock:
            self.cache[key] = {
                "b": None if lag else B, "done": done, "forming": forming,
                "tries": tries if lag else 0, "roll": self.cache.get(key, {}).get("roll"),
                "cloud": cloud_position(done) if cfg.cloud_filter else None,
            }
        if not lag:
            self._try_entry(it, done)

    def _skip(self, rec, now, key, why):
        state = self.state
        state["handled"] = (state["handled"] + [key])[-2000:]
        rec["status"] = f"SKIPPED ({why})"
        state["signals"] = (state["signals"] + [rec])[-200:]
        add_log(state, now, f"SKIPPED {rec['symbol']}: {why}  ({rec['pattern']})")
        save_state(state)

    def _enter(self, it, rec, ctime, price, now):
        cfg, state = self.cfg, self.state
        ex, sym = it["exchange"], it["symbol"]
        tf = pd.Timedelta(minutes=cfg.tf_min)
        entry = price * (1 + cfg.slippage_pct / 100)
        lot = int(it.get("lot", 1))
        mf = margin_factor(ex)
        cash = (
            cfg.capital + sum(t["pnl"] for t in state["closed"])
            - sum(p["entry"] * p["qty"] * p.get("mf", 1.0) for p in state["open"])
        )
        one_lot = entry * lot * mf
        _, qty = cfg.size_qty(one_lot, lot, cash)
        if qty < 1:
            unit = "share" if ex in ("NSE", "BSE") else "lot"
            rec["status"] = f"SKIPPED (1 {unit} needs {one_lot:,.0f} > {cfg.size_text})"
            add_log(
                state, now,
                f"SKIPPED {sym}: 1 {unit} needs {one_lot:,.0f} (price {entry:.2f}"
                f"{f' x lot {lot} x margin {mf * 100:g}%' if unit == 'lot' else ''}) but {cfg.size_text}, "
                f"free cash {cash:,.0f}",
            )
        else:
            slot, replaced = _pick_slot(state, now)
            state["open"].append({
                "slot": slot,
                "symbol": sym, "tradingsymbol": it["tradingsymbol"], "token": it["token"], "exchange": ex,
                "pattern": rec["pattern"], "signal_date": str(ctime), "signal_close": str(candle_end(ctime, tf, ex)),
                "entry_time": str(now.floor("s")),
                "entry": round(entry, 2),
                "stop_loss": round(entry * (1 - cfg.sl_pct / 100), 2) if cfg.sl_pct > 0 else None,
                "target": round(entry * (1 + cfg.target_pct / 100), 2) if cfg.target_pct > 0 else None,
                "qty": int(qty), "mf": mf,
                "last_price": price, "last_checked": str(now.floor("min")),
                **{k: rec[k] for k in STORE_KEYS if k in rec},
            })
            rec["status"] = "ENTERED"
            where = f"position #{slot}" + ("" if cfg.no_limit else f"/{cfg.max_open}")
            if replaced:
                where += (
                    f", took the place of {replaced['symbol']} "
                    f"({replaced['reason']} {str(replaced['exit_time'])[11:]})"
                )
            add_log(
                state, now,
                f"ENTRY {sym} @ {entry:.2f}  qty {qty}  "
                f"TGT {(f'{entry * (1 + cfg.target_pct / 100):.2f}' if cfg.target_pct > 0 else 'none (cloud exit)')}  "
                f"({rec['pattern']})  -> {where}",
            )
        state["signals"] = (state["signals"] + [rec])[-200:]
        save_state(state)

    def _try_entry(self, it, done):
        cfg, smart = self.cfg, self.smart
        now = now_ist()
        ex, sym = it["exchange"], it["symbol"]
        if not (self.ignore or market_open(now, ex)):
            return
        if len(done) < cfg.trend_lookback + 3:
            return
        sig = detect_patterns(done, cfg)
        names = [p for p in cfg.patterns if p in sig.columns and bool(sig[p].iat[-1])]
        if not names:
            return
        tf = pd.Timedelta(minutes=cfg.tf_min)
        ctime = done["date"].iat[-1]
        if tf >= pd.Timedelta(minutes=240):
            if not self.ignore and now - candle_end(ctime, tf, ex) > pd.Timedelta(days=4):
                return                      # 4H / day signal: valid until the next session(s), not only 2 minutes
        elif not self.ignore and now - (ctime + tf) > min(2 * tf, pd.Timedelta(seconds=FRESH_SECONDS)):
            return
        key = f"{ex}:{sym}|{ctime}"
        with self.lock:
            if key in self.state["handled"]:
                return
        pv, sg = done.iloc[-2], done.iloc[-1]
        candles = {
            f"{p}_{k}": round(float(c[n]), 2)
            for p, c in (("prev", pv), ("sig", sg))
            for k, n in (("O", "open"), ("H", "high"), ("L", "low"), ("C", "close"))
        }
        hist = [[round(float(x[n]), 4) for n in ("open", "high", "low", "close")] for _, x in done.tail(5).iterrows()]
        rec = {
            "time": str(now.floor("s")), "symbol": sym, "exchange": ex,
            "pattern": "+".join(names), "candle": str(ctime), **candles, "hist": hist, "status": "ENTERED",
        }
        if cfg.cloud_filter:                    # optional Ichimoku cloud filter: only the chosen side of the cloud enters
            cpos = cloud_position(done)
            rec["cloud"] = cpos or "n/a"
            if cpos not in cloud_list(cfg.cloud_filter):
                with self.lock:
                    self._skip(rec, now, key, f"cloud {cpos or 'not ready, need ' + str(CLOUD_MIN_BARS) + ' candles'}"
                                              f" - filter needs {' / '.join(cloud_list(cfg.cloud_filter))}")
                return

        def blocked():
            st_ = self.state
            if self.kill:
                return "skip", "kill switch active (max daily loss)"
            if cfg.live and time.time() < self.pause_until:
                return "skip", "entries paused (broker margin/funds rejection)"
            if cfg.live and time.time() < self.reject_until.get(sym, 0):
                return "skip", "paused after a rejected order on this stock"
            # 15:15 / 23:15 is the INTRADAY square-off time. Delivery / Margin / Carry-forward LIVE files have no
            # square-off, so they may enter until the market closes (15:30 / 23:30 - market_open() already checks that).
            carry = cfg.live and cfg.product != "INTRADAY"
            if not self.ignore and not carry and now.time() >= exit_time(ex):
                return "skip", (f"no new entries after {exit_time(ex):%H:%M} "
                                f"[{'LIVE ' + str(cfg.product) if cfg.live else 'PAPER'} - only LIVE Delivery/Margin/NRML enters after this]")
            if any(p["exchange"] == ex and p["symbol"] == sym for p in st_["open"]):
                return "skip", "already in position"
            n_open = len([x for x in st_["open"] if not x.get("pending")]) + self.pending   # in-flight entry counted once
            if n_open >= cfg.max_open:
                return "skip", f"positions full {n_open}/{cfg.max_open}"
            return None

        def handle(b):
            self._skip(rec, now, key, b[1])

        with self.lock:
            b = blocked()
            if b:
                handle(b)
                return
        ltp_ = fetch_ltp(smart, it)
        if ltp_ is None and cfg.live:
            return                         # LIVE: never send a real order on a stale candle close - retry next cycle
        price = ltp_ or float(done["close"].iat[-1])
        with self.lock:
            b = blocked()
            if b:
                handle(b)
                return
            self.state["handled"] = (self.state["handled"] + [key])[-2000:]
            if not cfg.live:
                self._enter(it, rec, ctime, price, now)
                return
            self.pending += 1
        try:                                   # LIVE: real orders, outside the lock
            self._enter_live(it, rec, ctime, price, now)
        except Exception as ex_:
            with self.lock:
                add_log(self.state, now, f"ERROR live entry {sym}: {ex_} - check the order in the Angel One app")
                # a half-finished entry must not stay in Live positions as 'pending' forever
                self.state["open"] = [x for x in self.state["open"] if not (x.get("pending") and x["symbol"] == sym)]
                save_state(self.state)
        finally:
            with self.lock:
                self.pending -= 1


# ============================== ENGINE REGISTRY ==============================
def env_creds():
    c = tuple(os.getenv(k, "").strip() for k in ("ANGEL_API_KEY", "ANGEL_CLIENT_ID", "ANGEL_MPIN", "ANGEL_TOTP_SECRET"))
    if all(c):
        return c
    try:
        a = st.secrets["angel"]
        c = tuple(str(a.get(k, "")).strip() for k in ("api_key", "client_id", "mpin", "totp_secret"))
        if all(c):
            return c
    except Exception:
        pass
    return None


def owner_email():
    v = os.getenv("OWNER_EMAIL", "").strip().lower()
    if not v:
        try:
            v = str(st.secrets["access_control"]["owner_email"]).strip().lower()
        except Exception:
            v = ""
    return v


def current_uid():
    em = (st.session_state.get("access_email") or "").strip().lower()
    if not em:
        return None
    if em == owner_email():
        return OWNER_ID
    return "u_" + hashlib.sha256(em.encode()).hexdigest()[:16]


@st.cache_resource
def _engine_registry():
    return {"lock": threading.Lock(), "map": {}}


@st.cache_resource
def _login_cache():
    """Server-memory Angel sessions per uid.
    Survives page refresh / laptop sleep while the Streamlit process is alive.
    Cleared only on explicit Logout or full app restart."""
    return {"lock": threading.Lock(), "map": {}}


def save_login(uid, smart, creds, client_id):
    if not uid or smart is None:
        return
    cache = _login_cache()
    with cache["lock"]:
        cache["map"][uid] = {
            "smart": smart,
            "creds": creds,
            "client_id": client_id or "",
            "login_time": time.time(),
        }
        cache.setdefault("out", set()).discard(uid)


def load_login(uid):
    if not uid:
        return None
    cache = _login_cache()
    with cache["lock"]:
        return cache["map"].get(uid)


def clear_login(uid):
    if not uid:
        return
    cache = _login_cache()
    with cache["lock"]:
        cache["map"].pop(uid, None)


def mark_logged_out(uid, flag=True):
    """Logout = the BROWSER leaves. Engines keep running; this flag only stops a refresh from re-attaching silently."""
    if not uid:
        return
    cache = _login_cache()
    with cache["lock"]:
        out = cache.setdefault("out", set())
        (out.add if flag else out.discard)(uid)


def is_logged_out(uid):
    cache = _login_cache()
    with cache["lock"]:
        return uid in cache.setdefault("out", set())


LOGIN_DIR = os.path.join(_DATA_DIR, "saved_logins")


def _login_fernet():
    """Encryption for saved API logins. None when the 'cryptography' package is missing.
       Key = env LOGIN_KEY (recommended) or an auto-created key file next to the saved logins."""
    try:
        from cryptography.fernet import Fernet
    except Exception:
        return None
    try:
        os.makedirs(LOGIN_DIR, exist_ok=True)
        raw = os.getenv("LOGIN_KEY", "").strip().encode()
        if raw:
            return Fernet(base64.urlsafe_b64encode(hashlib.sha256(raw).digest()))
        kp = os.path.join(LOGIN_DIR, ".key")
        if not os.path.exists(kp):
            with open(kp, "wb") as fh:
                fh.write(Fernet.generate_key())
            try:
                os.chmod(kp, 0o600)
            except OSError:
                pass
        with open(kp, "rb") as fh:
            return Fernet(fh.read().strip())
    except Exception:
        return None


def _login_file(uid):
    return os.path.join(LOGIN_DIR, f"{_safe_name(str(uid))}.bin")


def _read_creds_store(uid):
    """{'last': CLIENT_ID, 'logins': {CLIENT_ID: (api_key, client_id, mpin, totp)}} - every saved Angel login of this user."""
    empty = {"last": "", "logins": {}}
    f = _login_fernet()
    if not uid or f is None or not os.path.exists(_login_file(uid)):
        return empty
    try:
        with open(_login_file(uid), "rb") as fh:
            data = json.loads(f.decrypt(fh.read()).decode())
        if isinstance(data, list):                       # old format: one login only
            c = tuple(str(x) for x in data)
            return {"last": c[1].upper(), "logins": {c[1].upper(): c}} if len(c) == 4 and all(c) else empty
        logins = {}
        for cid, c in (data.get("logins") or {}).items():
            c = tuple(str(x) for x in c)
            if len(c) == 4 and all(c):
                logins[str(cid).upper()] = c
        last = str(data.get("last") or "").upper()
        return {"last": last if last in logins else next(iter(logins), ""), "logins": logins}
    except Exception:
        return empty


def _write_creds_store(uid, store):
    f = _login_fernet()
    if not uid or f is None:
        return False
    try:
        os.makedirs(LOGIN_DIR, exist_ok=True)
        payload = {"v": 2, "last": store["last"], "logins": {k: list(v) for k, v in store["logins"].items()}}
        with open(_login_file(uid), "wb") as fh:
            fh.write(f.encrypt(json.dumps(payload).encode()))
        try:
            os.chmod(_login_file(uid), 0o600)
        except OSError:
            pass
        return True
    except Exception:
        return False


def save_creds_disk(uid, creds):
    """Add / update this Client ID in the saved list (other saved IDs stay) and make it the last used."""
    store = _read_creds_store(uid)
    c = tuple(str(x).strip() for x in creds)
    cid = c[1].upper()
    store["logins"][cid] = c
    store["last"] = cid
    return _write_creds_store(uid, store)


def list_creds_disk(uid):
    """Saved Client IDs, last used first."""
    store = _read_creds_store(uid)
    ids = list(store["logins"])
    if store["last"] in ids:
        ids.remove(store["last"])
        ids.insert(0, store["last"])
    return ids


def load_creds_disk(uid, cid=None):
    store = _read_creds_store(uid)
    return store["logins"].get((cid or store["last"] or "").upper())


def forget_creds_disk(uid, cid=None):
    """cid given -> remove only that saved login; no cid -> remove all."""
    store = _read_creds_store(uid)
    if cid:
        store["logins"].pop(str(cid).upper(), None)
        if store["last"] == str(cid).upper():
            store["last"] = next(iter(store["logins"]), "")
    if cid and store["logins"]:
        _write_creds_store(uid, store)
        return
    try:
        os.remove(_login_file(uid))
    except OSError:
        pass


def get_strategy_engine(uid, strategy_path):
    """One Engine per (user, strategy folder/file)."""
    reg = _engine_registry()
    key = f"{uid}::{strategy_path}"
    with reg["lock"]:
        eng = reg["map"].get(key)
        if eng is None:
            eng = reg["map"][key] = Engine(uid, strategy_path)
        return eng


def _get_engine_by_path(uid, strategy_path):
    reg = _engine_registry()
    key = f"{uid}::{strategy_path}"
    with reg["lock"]:
        return reg["map"].get(key)


def share_login_to_engines(uid, smart, creds, client_id):
    """Push Angel login to all engines of this user (so any file can Start)."""
    reg = _engine_registry()
    with reg["lock"]:
        for k, eng in reg["map"].items():
            if k.startswith(f"{uid}::"):
                eng.set_login(smart, creds, client_id)


def autoresume_all(uid, smart, creds, client_id):
    """After login / restart: resume any file that was RUNNING."""
    root = user_strategies_root(uid)
    if not os.path.isdir(root):
        return
    for folder in os.listdir(root):
        fp = os.path.join(root, folder)
        if not os.path.isdir(fp):
            continue
        for fname in os.listdir(fp):
            fpath = os.path.join(fp, fname)
            if not os.path.isdir(fpath):
                continue
            run_file = os.path.join(fpath, "run_config.json")
            if not os.path.exists(run_file):
                continue
            try:
                rc = _read_json(run_file)
                if not rc.get("running"):
                    continue
            except Exception:
                continue
            eng = get_strategy_engine(uid, fpath)
            if not eng.running:
                threading.Thread(
                    target=eng.try_autoresume,
                    args=(smart, creds, client_id),
                    daemon=True,
                ).start()


# ============================== ACCESS CONTROL ==============================
ACCESS_APPS_SCRIPT_URL = (
    "https://script.google.com/macros/s/AKfycbw5oSPyD4bjUN6bL8YqsWH94kHo_HvRWszcLecpLDm1wZDO7p6F34nmDSwN-w5SUWo63g/exec"
)


def _get_access_secret():
    try:
        return str(st.secrets["access_control"]["request_secret"]).strip()
    except Exception:
        return ""


def _access_call(action, name="", email=""):
    secret = _get_access_secret()
    if not secret:
        return {
            "status": "ERROR",
            "message": "Access secret is missing. Add [access_control] request_secret in Streamlit Secrets.",
        }
    payload = {
        "action": action, "name": name.strip(), "email": email.strip().lower(),
        "secret": secret, "requested_time": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
    }
    try:
        response = requests.post(ACCESS_APPS_SCRIPT_URL, json=payload, timeout=15)
        if response.status_code != 200:
            return {"status": "ERROR", "message": f"Access server returned HTTP {response.status_code}."}
        try:
            return response.json()
        except Exception:
            return {"status": "ERROR", "message": "Invalid response received from access server."}
    except requests.RequestException as exc:
        return {"status": "ERROR", "message": f"Could not contact access server: {exc}"}


def _valid_access_email(email):
    return bool(re.match(r"^[^@\s]+@[^@\s]+\.[^@\s]+$", email.strip()))


def _saved_email():
    return (st.session_state.get("access_email") or str(st.query_params.get("e", ""))).strip().lower()


def access_request_page():
    st.title("🔐 Request Access")
    st.caption("Administrator approval is required before using the Live Paper Trading application.")
    saved_email = _saved_email()
    saved_name = st.session_state.get("access_name", "")
    if saved_email:
        result = _access_call("check_access", email=saved_email)
        status = str(result.get("status", "")).upper()
        if status == "APPROVED":
            st.session_state["access_email"] = saved_email
            st.session_state["access_granted"] = True
            st.rerun()
        elif status == "PENDING":
            st.info("⏳ Your access request is pending admin approval.")
        elif status == "REJECTED":
            st.error("❌ Your access request was rejected by the administrator.")
        elif status == "ERROR":
            st.warning(result.get("message", "Unable to check access status."))

    with st.form("access_request_form"):
        name = st.text_input("Name", value=saved_name, placeholder="Enter your name")
        email = st.text_input("Email ID", value=saved_email, placeholder="Enter your email address")
        submitted = st.form_submit_button("Request Access", type="primary", use_container_width=True)
    if not submitted:
        return
    name, email = name.strip(), email.strip().lower()
    if not name:
        st.error("Please enter your name.")
        return
    if not _valid_access_email(email):
        st.error("Please enter a valid email address.")
        return
    st.session_state["access_name"] = name
    st.session_state["access_email"] = email
    st.query_params["e"] = email
    check = _access_call("check_access", email=email)
    status = str(check.get("status", "NEW")).upper()
    if status == "APPROVED":
        st.session_state["access_granted"] = True
        st.rerun()
    if status == "PENDING":
        st.info("⏳ This email already has a pending access request.")
        return
    if status == "REJECTED":
        st.error("❌ This email was rejected by the administrator.")
        return
    if status == "ERROR":
        st.error(check.get("message", "Could not check access status."))
        return
    result = _access_call("request_access", name=name, email=email)
    result_status = str(result.get("status", "ERROR")).upper()
    if result_status == "APPROVED":
        st.session_state["access_granted"] = True
        st.rerun()
    elif result_status == "PENDING":
        st.success("✅ Access request submitted successfully. Please wait for administrator approval.")
    elif result_status == "REJECTED":
        st.error("❌ Access was rejected by the administrator.")
    else:
        st.error(result.get("message", "Could not submit the access request."))
    st.caption("After approval, refresh this page. The Angel One login will then appear.")


def access_gate():
    ss = st.session_state
    if ss.get("access_granted", False):
        em = ss.get("access_email", "")
        if em and st.query_params.get("e") != em:
            st.query_params["e"] = em
        return True
    email = _saved_email()
    if email:
        result = _access_call("check_access", email=email)
        if str(result.get("status", "")).upper() == "APPROVED":
            ss["access_email"] = email
            ss["access_granted"] = True
            st.query_params["e"] = email
            return True
    access_request_page()
    return False


# ============================== UI HELPERS ==============================
def excel_check_frame(entries):
    """Every entry's last candles + the 10 sheet formulas (each formula sits on the first row of its own candles)."""
    rows = []
    rec = sorted([e for e in entries if all(k in e for k in CANDLE_KEYS)], key=lambda e: str(e.get("entry_time")))
    r = 2                                                   # sheet row (row 1 = header)
    for e in rec:
        hist = e.get("hist")
        if not isinstance(hist, (list, tuple)) or not hist:
            hist = [[e["prev_O"], e["prev_H"], e["prev_L"], e["prev_C"]], [e["sig_O"], e["sig_H"], e["sig_L"], e["sig_C"]]]
        m = len(hist)
        block = [[""] * len(PATTERN_DEFS) for _ in range(m)]
        for j, (_n, n, _fn, xl) in enumerate(PATTERN_DEFS):
            if m >= n:
                first = m - n                               # pattern = the last n candles, ending on the signal candle
                block[first][j] = xl([r + first + q for q in range(n)])
        for i, (o_, h_, l_, c_) in enumerate(hist):
            last = i == m - 1
            label = (f"{e['symbol']} SIGNAL candle {e.get('signal_date', '')} to {e.get('signal_close', '?')} "
                     f"(entry {e.get('entry_time', '')})") if last else f"{e['symbol']} candle {i + 1}/{m}"
            rows.append([label, o_, h_, l_, c_, *block[i], e.get("pattern", "") if last else ""])
        r += m
    return pd.DataFrame(rows, columns=["candle", "Open", "High", "Low", "Close", *[d[0] for d in PATTERN_DEFS], "App pattern"])


def log_frame(lines, n=100):
    rows = []
    for ln in reversed(lines[-n:]):
        t, _, msg = ln.partition("  ")
        parts = msg.split(" ", 2)
        if parts[0] in ("ENTRY", "CLOSED", "SKIPPED") and len(parts) >= 2:
            ev, sym, rest = parts[0], parts[1].rstrip(":"), (parts[2] if len(parts) > 2 else "")
        else:
            ev, sym, rest = "INFO", "", msg
        rows.append({"time": t, "event": ev, "symbol": sym, "details": rest})
    return pd.DataFrame(rows, columns=["time", "event", "symbol", "details"])


def _frames(engine):
    snap = engine.snapshot()
    state, cfg = snap["state"], snap["cfg"] or Config()
    open_df, closed_df = pd.DataFrame(state["open"]), pd.DataFrame(state["closed"])
    if not closed_df.empty:
        old_pat = closed_df["pattern"] if "pattern" in closed_df.columns else [None] * len(closed_df)
        closed_df["pattern"] = [classify_candles(r, only=[x.strip() for x in re.split(r"\+", str(p))] if isinstance(p, str) and p else None) or p
                                for r, p in zip(closed_df.to_dict("records"), old_pat)]
        order = [
            "slot", "symbol", "exchange", "signal_date", "signal_close", *CANDLE_KEYS, "pattern",
            "entry_time", "entry", "qty", "exit_time", "exit", "reason", "pnl", "r_multiple",
        ]
        closed_df = closed_df[[c for c in order if c in closed_df.columns]].rename(
            columns={"slot": "position", "signal_date": "signal_candle_start", "signal_close": "signal_candle_close"}
        )
        closed_df["pnl_%"] = ((closed_df["exit"] / closed_df["entry"] - 1) * 100).round(2)
    if not open_df.empty:
        _fill_slots(state)
        open_df = pd.DataFrame(state["open"]).rename(columns={"slot": "position"}).sort_values("position")
        open_df["live_price"] = open_df["last_price"].round(2)
        open_df["PnL"] = ((open_df["last_price"] - open_df["entry"]) * open_df["qty"]).round(2)
        open_df["PnL_%"] = ((open_df["last_price"] / open_df["entry"] - 1) * 100).round(2)
        if "pending" in open_df.columns:              # order not filled yet -> no P&L
            mask = open_df["pending"].fillna(False).astype(bool)
            open_df.loc[mask, ["PnL", "PnL_%"]] = 0.0
        if "order_status" in open_df.columns:
            open_df["order_status"] = open_df["order_status"].fillna("")
    return snap, state, cfg, open_df, closed_df


def _csv_button(label, df, name, key):
    empty = df is None or df.empty
    st.download_button(
        label, b"" if empty else df.to_csv(index=False).encode(),
        f"{name}_{now_ist():%Y%m%d}.csv", "text/csv", key=key, disabled=empty,
    )


# ============================== LIVE SECTIONS (per engine) ==============================
def live_top(engine, exchange, tf_label):
    snap, state, cfg, open_df, closed_df = _frames(engine)
    if snap["running"]:
        exchange = snap["exchange"]
        tf_label = next((k for k, v in TIMEFRAMES.items() if v[1] == cfg.tf_min), tf_label)
    now = now_ist()
    hrs = "9:00-23:30" if exchange == "MCX" else "9:15-15:30"
    mkt = (
        f"{exchange} market OPEN" if market_open(now, exchange)
        else f"{exchange} market CLOSED (entry/exit run {hrs} IST, Mon-Fri)"
    )
    upd = f"{snap['last_update']:%H:%M:%S}" if snap["last_update"] is not None else "-"
    st.write(
        f"**{'RUNNING' if snap['running'] else 'STOPPED'}**  |  {mkt}  |  now {now:%H:%M:%S} IST  |  "
        f"prices updated {upd}  |  timeframe: {tf_label or '-'}  |  per position: {cfg.size_text}"
    )
    if snap["running"]:
        st.caption(f"Engine: {snap['status']}")

    realized = float(closed_df["pnl"].sum()) if not closed_df.empty else 0.0
    unreal = float(open_df["PnL"].sum()) if not open_df.empty else 0.0
    win = (closed_df["pnl"] > 0).mean() * 100 if not closed_df.empty else 0.0
    m = st.columns(5)
    m[0].metric("Open positions", f"{len(open_df)} / {'no limit' if cfg.no_limit else cfg.max_open}")
    m[1].metric("Closed trades", len(closed_df))
    m[2].metric("Realized P&L", f"{realized:,.0f}")
    invested = float((open_df["entry"] * open_df["qty"]).sum()) if not open_df.empty else 0.0
    m[3].metric("Unrealized P&L", f"{unreal:,.0f}", f"{unreal / invested * 100:.2f}%" if invested else None)
    m[4].metric("Win rate (closed)", f"{win:.0f}%")

    st.subheader("1. Monitoring - live data + pattern outlook")
    mon_df = pd.DataFrame(snap["rows"])
    if mon_df.empty:
        st.write("Once started, live data + pattern outlook will appear here.")
    else:
        st.caption(
            f"ltp = live price (every second) | open / high / low = running {tf_label or 'timeframe'} candle | "
            "prev_close = previous candle close | change_% = ltp vs previous candle close | "
            "pattern_outlook changes only when a candle closes"
        )
        if mon_df["ltp"].isna().all() and snap["errors"]:
            st.warning("Live price not received: " + " | ".join(snap["errors"][:3]))
        st.dataframe(
            mon_df, use_container_width=True, hide_index=True,
            column_config={"pattern_outlook": st.column_config.TextColumn("pattern_outlook", width="large")},
        )


def live_mid(engine):
    snap, state, cfg, open_df, closed_df = _frames(engine)
    _csv_button("Download monitoring CSV", pd.DataFrame(snap["rows"]), "monitoring", "dl_monitor")
    st.subheader("2. Signals")
    sig_df = pd.DataFrame(state["signals"]).drop(columns=["hist"], errors="ignore")
    if sig_df.empty:
        st.write("No signals yet (patterns will appear here when a candle closes).")
    else:
        st.dataframe(sig_df.iloc[::-1], use_container_width=True, hide_index=True)
    _csv_button("Download signals CSV", sig_df, "signals", "dl_signals")
    if snap["errors"]:
        with st.expander(f"{len(snap['errors'])} warning(s)"):
            st.write("\n".join(snap["errors"]))


def live_positions(engine):
    snap, state, cfg, open_df, closed_df = _frames(engine)
    st.subheader("3. Live positions (entered, waiting for exit)")
    cols = [c for c in ["position", "symbol", "exchange", "pattern", "entry_time", "entry", "order_status",
                        "live_price", "PnL", "PnL_%"] if c in open_df.columns]
    pid = hashlib.md5(str(getattr(engine, "run_file", id(engine))).encode()).hexdigest()[:8]
    mode_key, gen_key = f"lpmode_{pid}", f"lpgen_{pid}"
    if open_df.empty:
        st.write("No open positions.")
        st.session_state[mode_key] = False
    else:
        gen = st.session_state.get(gen_key, 0)                 # bump = fresh boxes
        recs = open_df.to_dict("records")
        keys = [f"{r['exchange']}:{r['symbol']}" for r in recs]
        pend = {k: bool(r.get("pending")) for k, r in zip(keys, recs)}
        ck = {k: f"lpck_{pid}_{k}_{gen}" for k in keys}
        on = bool(st.session_state.get(mode_key, False))

        def _toggle():
            now_on = not st.session_state.get(mode_key, False)
            st.session_state[mode_key] = now_on
            if now_on:                                        # opening: every position starts ticked
                for k_ in keys:
                    if not pend[k_]:
                        st.session_state[ck[k_]] = True

        def _all():
            for k_ in keys:
                st.session_state[ck[k_]] = not pend[k_]

        def _none():
            for k_ in keys:
                st.session_state[ck[k_]] = False

        if not on:
            st.button("Exit all", key=f"lp_exitall_{pid}", on_click=_toggle,
                      help="Clicking this shows a checkbox for every position (all ticked by default). "
                           "Untick the ones you do not want to exit and click 'Exit selected'.")
            st.dataframe(open_df[cols], use_container_width=True, hide_index=True)
        else:
            chosen = [k for k in keys if not pend[k] and st.session_state.get(ck[k])]
            c1, c2, c3, c4 = st.columns([2.2, 1.2, 1, 1])
            if c1.button(f"Exit selected ({len(chosen)})", key=f"lp_go_{pid}", type="primary",
                         use_container_width=True, disabled=not chosen):
                n = engine.exit_selected(chosen, "Manual exit (selected)")
                st.session_state[mode_key] = False
                st.session_state[gen_key] = gen + 1
                st.session_state["flash"] = (f"Exit selected: {n} of {len(chosen)} position(s) closed." + _fail_note(engine))
                st.rerun()
            c2.button("Select all", key=f"lp_all_{pid}", on_click=_all, type="tertiary", use_container_width=True)
            c3.button("Clear", key=f"lp_clr_{pid}", on_click=_none, type="tertiary", use_container_width=True)
            c4.button("✖ Cancel", key=f"lp_cancel_{pid}", on_click=_toggle, use_container_width=True)
            w = [0.5, 0.9, 1.6, 2.2, 1.2, 1.2, 1.2, 1.0]
            with st.container(height=min(460, 42 * len(recs) + 48)):
                for col, label in zip(st.columns(w), ("✔", "Pos", "Symbol", "Pattern", "Entry", "Live", "PnL", "PnL %")):
                    col.caption(f"**{label}**")
                for k, r in zip(keys, recs):
                    rc = st.columns(w)
                    rc[0].checkbox("select", key=ck[k], label_visibility="collapsed", disabled=pend[k])
                    rc[1].caption(str(r.get("position", "")))
                    rc[2].caption(str(r.get("symbol", "")) + (" (pending)" if pend[k] else ""))
                    rc[3].caption(str(r.get("pattern", "")))
                    rc[4].caption(str(r.get("entry", "")))
                    rc[5].caption(str(r.get("live_price", "")))
                    rc[6].caption(str(r.get("PnL", "")))
                    rc[7].caption(str(r.get("PnL_%", "")))
    orders = state.get("orders") or []
    if orders:
        st.caption("Angel One order status (latest first): FILLED / REJECTED / CANCELLED + reason")
        st.dataframe(pd.DataFrame(orders[-30:][::-1]), use_container_width=True, hide_index=True)


def live_bottom(engine):
    snap, state, cfg, open_df, closed_df = _frames(engine)
    cols = [c for c in ["position", "symbol", "exchange", "pattern", "entry_time", "entry", "live_price", "PnL", "PnL_%"] if c in open_df.columns]
    _csv_button("Download live positions CSV", open_df[cols] if not open_df.empty else open_df, "live_positions", "dl_open")

    st.subheader("4. Closed trades (exited)")
    show = ["position", "symbol", "exchange", "pattern", "entry_time", "entry", "qty", "exit_time", "exit", "reason", "pnl", "pnl_%", "r_multiple"]
    if closed_df.empty:
        st.write("No closed trades.")
    else:
        st.dataframe(
            closed_df[[c for c in show if c in closed_df.columns]].rename(columns={"pnl": "PnL"}).iloc[::-1],
            use_container_width=True, hide_index=True,
        )
    _csv_button("Download closed trades CSV", closed_df, "closed_trades", "dl_closed")

    st.subheader("5. Logs")
    log_df = log_frame(state["log"])
    if log_df.empty:
        st.write("No events yet.")
    else:
        st.dataframe(log_df, use_container_width=True, hide_index=True)
    _csv_button("Download logs CSV", log_df, "logs", "dl_log")

    st.subheader("6. Excel check")
    if st.toggle("Show Excel check (appears only when clicked)", key="show_excel_check"):
        check_df = excel_check_frame(state["open"] + state["closed"])
        if check_df.empty:
            st.write("Appears here after an entry is made (no candle data for older entries).")
        else:
            st.caption(
                "Open the CSV in Excel. B=Open, C=High, D=Low, E=Close. F-O = your 10 formulas, P = pattern reported by the app."
            )
            st.dataframe(check_df.iloc[:, :5], use_container_width=True, hide_index=True)
        _csv_button("Download Excel check CSV (open + closed entries)", check_df, "excel_check", "dl_check")


# ============================== PAGES ==============================
def _connect_and_finish(creds, page=None, save=False):
    """Angel login with creds. Success -> session stored + rerun (never returns). Failure -> returns the error text."""
    with st.spinner("Connecting to Angel One..."):
        smart, err = angel_login(*creds)
    if err:
        return err
    if page is not None:
        page.empty()
    st.title("Connected")
    with st.spinner("Loading Angel One stock list..."):
        try:
            load_master()
        except Exception:
            pass
    uid = current_uid()
    creds = tuple(c.strip() for c in creds)
    cid = creds[1].upper()
    if save:
        save_creds_disk(uid, creds)
    save_login(uid, smart, creds, cid)          # survives refresh (server memory)
    share_login_to_engines(uid, smart, creds, cid)
    st.session_state.smart = smart
    st.session_state.client_id = cid
    st.session_state.creds = creds
    for k in ("no_autologin", "login_new", "saved_login_failed", "saved_login_err"):
        st.session_state.pop(k, None)
    autoresume_all(uid, smart, creds, cid)
    st.rerun()


def login_page():
    no_dim()
    ss = st.session_state
    if env_creds() and not owner_email():
        st.warning(
            "An Angel login (ANGEL_*) is saved on the server, but OWNER_EMAIL is not set, so auto login "
            "will not work for anyone. Please set OWNER_EMAIL (or secrets [access_control] owner_email)."
        )
    uid = current_uid()
    ids = list_creds_disk(uid) if uid else []              # every saved Client ID, last used first

    if ids and not ss.get("login_new"):
        # Saved logins exist -> auto connect the last used one; the API form only comes back on "New login".
        auto = (not ss.get("no_autologin") and not ss.get("saved_login_failed") and not is_logged_out(uid))
        if auto:
            page = st.empty()
            with page.container():
                st.title("Angel One Login")
                st.info(f"Auto-connecting with the saved login ({ids[0]})...")
            err = _connect_and_finish(load_creds_disk(uid, ids[0]), page, save=True)
            ss["saved_login_failed"], ss["saved_login_err"] = True, err
            st.rerun()
        st.title("Angel One Login")
        if ss.get("saved_login_err"):
            st.error(f"Saved login could not connect: {ss['saved_login_err']}")
        st.caption(f"Saved logins: **{len(ids)}**. Select the one you want and click Connect. "
                   "To enter a new ID, click **New login**.")
        if ss.get("saved_pick_cid") not in ids:
            ss["saved_pick_cid"] = ids[0]
        cid = st.selectbox("Saved Client ID", ids, key="saved_pick_cid")
        sel = load_creds_disk(uid, cid)
        b1, b2, b3 = st.columns(3)
        if b1.button(f"Connect ({cid})", type="primary", use_container_width=True):
            err = _connect_and_finish(sel, save=True)
            ss["saved_login_failed"], ss["saved_login_err"] = True, err
            st.rerun()
        if b2.button("New login", use_container_width=True):
            ss["login_new"] = True
            st.rerun()
        if b3.button(f"Forget {cid}", use_container_width=True, help="Removes only this ID from the saved list"):
            forget_creds_disk(uid, cid)
            for k in ("saved_login_failed", "saved_login_err", "saved_pick_cid"):
                ss.pop(k, None)
            st.rerun()
        return

    can_save = _login_fernet() is not None
    page = st.empty()
    with page.container():
        st.title("Angel One Login")
        if ids and st.button("← Saved logins", key="back_saved"):
            ss.pop("login_new", None)
            st.rerun()
        st.caption("The login is saved encrypted on the server only if Save is ticked (it will appear in the list next time). "
                   "Tick Save for each ID. Otherwise nothing is saved to disk.")
        with st.form("login"):
            mine = current_uid() == OWNER_ID
            api_key = st.text_input("API Key", value=os.getenv("ANGEL_API_KEY", "") if mine else "")
            client_id = st.text_input("Client ID", value=os.getenv("ANGEL_CLIENT_ID", "") if mine else "")
            mpin = st.text_input("MPIN", type="password")
            totp_secret = st.text_input("TOTP Secret Key", type="password")
            save_it = st.checkbox("Save login (next time auto connect)", value=False, disabled=not can_save)
            if not can_save:
                st.caption("To use Save: run `pip install cryptography` and restart the app.")
            go = st.form_submit_button("Connect", type="primary")
    if not go:
        return
    if not all([api_key, client_id, mpin, totp_secret]):
        st.error("Please fill in all 4 fields.")
        return
    err = _connect_and_finish((api_key, client_id, mpin, totp_secret), page, save=save_it and can_save)
    st.error(err)


def _set_nav(page="home", folder="", file=""):
    """Keep page in query params so refresh / new tab with same URL stays on page.
       Email (access) is already in ?e= — that alone prevents access re-request."""
    st.session_state["page"] = page
    qp = dict(st.query_params)
    if st.session_state.get("access_email"):
        qp["e"] = st.session_state["access_email"]
    qp["p"] = page
    if page in ("file", "builder") and folder and file:
        qp["folder"] = folder
        qp["file"] = file
    else:
        qp.pop("folder", None)
        qp.pop("file", None)
    st.query_params.from_dict(qp)


def strategy_pnl(uid, path):
    """P&L of one file: live from its engine if it is in memory, otherwise from its saved state."""
    eng = _get_engine_by_path(uid, path)
    if eng is not None:
        with eng.lock:
            op, cl = list(eng.state["open"]), list(eng.state["closed"])
    else:
        s = load_state(os.path.join(path, "live_state.json"))
        op, cl = s["open"], s["closed"]
    realized = sum(float(t.get("pnl") or 0) for t in cl)
    unreal = sum((float(p.get("last_price") or p["entry"]) - float(p["entry"])) * float(p["qty"]) for p in op)
    return {"open": len(op), "closed": len(cl), "realized": realized, "unrealized": unreal,
            "total": realized + unreal}


def _money(x):
    s = f"{x:+,.2f}"
    return f":green[{s}]" if x > 0 else f":red[{s}]" if x < 0 else f"{x:,.2f}"


def _pnl_sum(uid, paths):
    """Added-up P&L of one file (paths=[p]) or a whole folder (paths=[p1, p2, ...])."""
    tot = {"open": 0, "closed": 0, "realized": 0.0, "unrealized": 0.0}
    for p in paths:
        s = strategy_pnl(uid, p)
        for k in tot:
            tot[k] += s[k]
    tot["total"] = tot["realized"] + tot["unrealized"]
    return tot


def _pnl_inline(uid, paths, capital=None):
    """Compact P&L block for a file (paths=[p]) or a folder (many paths)."""
    t = _pnl_sum(uid, paths)
    try:
        pct = f" ({t['total'] / float(capital) * 100:+.2f}%)" if capital else ""
    except (TypeError, ValueError):
        pct = ""
    st.markdown(f"Open **{t['open']}** · Closed **{t['closed']}** · Realized {_money(t['realized'])}  \n"
                f"Unrealized {_money(t['unrealized'])} · **Total** {_money(t['total'])}{pct}")


def _folder_cap(files):
    cap = 0.0
    for m in files:
        try:
            cap += float(m.get("capital") or 0)
        except (TypeError, ValueError):
            pass
    return cap


def _overall_panel(uid):
    """Live P&L of ALL files together."""
    files = [m for fl in list_strategies(uid).values() for m in fl]
    tot = {"open": 0, "closed": 0, "realized": 0.0, "unrealized": 0.0}
    cap = 0.0
    for m in files:
        p = strategy_pnl(uid, m["path"])
        for k in tot:
            tot[k] += p[k]
        try:
            cap += float(m.get("capital") or 0)
        except (TypeError, ValueError):
            pass
    total = tot["realized"] + tot["unrealized"]
    c = st.columns(5)
    c[0].metric("Strategies running", f"{sum(1 for m in files if m.get('running'))} / {len(files)}")
    c[1].metric("Open positions", tot["open"])
    c[2].metric("Realized P&L", f"{tot['realized']:,.0f}")
    c[3].metric("Unrealized P&L", f"{tot['unrealized']:,.0f}")
    c[4].metric("Total P&L", f"{total:,.0f}", f"{total / cap * 100:.2f}%" if cap else None)


def top_nav(active):
    """Top menu: Strategy | Paper Trading."""
    st.markdown(
        """<style>
        [data-testid="stSidebar"], [data-testid="stSidebarCollapsedControl"],
        [data-testid="collapsedControl"] { display: none !important; }
        </style>""",
        unsafe_allow_html=True,
    )
    cols = st.columns([1.8, 2.0, 3.4])
    for col, (key, label) in zip(cols[:2], (("home", "📁 My Strategies"), ("builder", "🛠 Strategy Builder"))):
        if col.button(label, key=f"nav_{key}", use_container_width=True,
                      type="primary" if active == key else "secondary"):
            st.session_state.pop("edit_open", None)
            if key == "builder":
                st.session_state.pop("builder_active", None)      # back to the empty builder form
            st.session_state["nav_from"] = key
            _set_nav(key)
            st.rerun()
    st.divider()


def _go_file(folder, meta, edit=False, src="home"):
    if edit:
        st.session_state["edit_open"] = f"{folder}/{meta['file']}"
    else:
        st.session_state.pop("edit_open", None)
    if meta.get("live") and not edit:                 # live files open in the Strategy Builder run view
        st.session_state["builder_active"] = {"folder": folder, "file": meta["file"], "path": meta["path"]}
        st.session_state["nav_from"] = "builder"
        _set_nav("builder", folder, meta["file"])
        st.rerun()
    st.session_state["nav_from"] = src
    st.session_state["active_strategy"] = {"folder": folder, "file": meta["file"], "path": meta["path"]}
    _set_nav("file", folder, meta["file"])
    st.rerun()


def _account_footer(uid):
    """Connected / Logout / Exit ALL - tiny expander at the very bottom (no sidebar)."""
    st.write("")
    with st.expander("⚙️ Account"):
        st.write(f"Connected: **{st.session_state.get('client_id', '-')}**")
        _reg = _engine_registry()
        with _reg["lock"]:
            n_running = sum(1 for k, e in _reg["map"].items() if k.startswith(f"{uid}::") and e.running)
        if n_running:
            st.caption(f"{n_running} strategy RUNNING - it keeps running in the background even after Logout / closing the browser. "
                       "To stop a file, click its **Stop** button.")
        if st.button("Logout (strategies keep running)", key="acct_logout"):
            # Only this browser logs out. Engines are NOT stopped and keep their Angel login in server memory.
            mark_logged_out(uid, True)
            clear_login(uid)                     # next visit must enter API key again
            for k in ("smart", "client_id", "creds", "active_strategy"):
                st.session_state.pop(k, None)
            st.session_state["no_autologin"] = True
            st.rerun()
        st.markdown("**Exit ALL**")
        gen = st.session_state.get("exit_gen", 0)
        st.caption("Closes all open positions of all strategies at the last price and stops all strategies.")
        exit_ok = st.checkbox("Confirm", key=f"exit_all_ok_{gen}")
        if st.button("Exit ALL", type="primary", disabled=not exit_ok, key=f"exit_all_btn_{gen}"):
            closed_n = stopped_n = 0
            for fl in list_strategies(uid).values():
                for m in fl:
                    eng = get_strategy_engine(uid, m["path"])
                    was_running = eng.running
                    closed_n += eng.exit_all("Manual exit (Exit ALL)")
                    stopped_n += 1 if was_running else 0
            st.session_state["flash"] = (f"Exit ALL: {closed_n} position(s) closed, {stopped_n} strategy stopped."
                                         + _fail_note(*[get_strategy_engine(uid, m["path"]) for fl in list_strategies(uid).values() for m in fl]))
            st.session_state["exit_gen"] = gen + 1        # new, un-ticked Confirm box
            st.rerun()


def strategy_page():
    """MY STRATEGIES tab: create folders, see every folder -> its files (stored here)."""
    uid = current_uid()
    no_dim()
    top_nav("home")
    st.title("My Strategies")
    frag = getattr(st, "fragment", None) or st.experimental_fragment
    vpick = st.radio("View", ["📈 Paper", "🔴 Live"], horizontal=True, key="ms_mode", label_visibility="collapsed")
    vmode = "live" if "Live" in vpick else "paper"

    flash = st.session_state.pop("flash", None)
    if flash:
        st.success(flash)

    # ----- search + create folder (like the reference) -----
    s1, s2 = st.columns([3, 4])
    with s1:
        q = st.text_input("Search", placeholder="🔍 Search folder / strategy...", key="ms_search",
                          label_visibility="collapsed").strip().lower()
    with s2:
        with st.form("new_folder_form", clear_on_submit=True):
            f1, f2 = st.columns([3, 1.2])
            fname = f1.text_input("Folder name", placeholder="Enter new folder name",
                                  label_visibility="collapsed")
            make = f2.form_submit_button("📁＋ Create", type="primary", use_container_width=True)
    if make:
        if not fname or not fname.strip():
            st.error("Please enter a folder name.")
        else:
            try:
                safe = create_folder(uid, fname, vmode)
            except ValueError as ex_:
                st.error(str(ex_))
            else:
                st.session_state["flash"] = (f"{vmode.upper()} folder '{safe}' created. To create a file, go to the Strategy Builder "
                                             f"tab (select Mode: {vmode.title()} and choose this folder).")
                st.rerun()

    strategies = list_strategies(uid, vmode)
    if not strategies:
        st.info(f"No {vmode.title()} folder yet. Type a folder name above and click **Create**.")
        return

    shown = {}
    for folder, files in strategies.items():
        if not q or q in folder.lower():
            shown[folder] = files
        else:
            hit = [m for m in files if q in m["file"].lower()]
            if hit:
                shown[folder] = hit
    if not shown:
        st.info("No folder / strategy matches the search.")
        return

    for folder, files in shown.items():
        all_files = strategies[folder]
        f_paths = [m["path"] for m in all_files]
        f_cap = _folder_cap(all_files)
        n_run = sum(1 for m in all_files if m.get("running"))
        f_run = 2 if n_run else None
        f_has_open = any(strategy_pnl(uid, pth)["open"] > 0 for pth in f_paths)

        with st.expander(f"📁 {folder}   ·   Running {n_run}   ·   Total {len(all_files)}", expanded=bool(q)):
            # ----- folder P&L (tracked inside the folder) + Exit folder (tick files in the rows below) -----
            ef_on_key = f"efmode_{folder}"
            ef_gen = st.session_state.get(f"efgen_{folder}", 0)          # bump = fresh un-ticked boxes
            ck = {m["file"]: f"efck_{folder}_{m['file']}_{ef_gen}" for m in all_files}
            ef_on = bool(st.session_state.get(ef_on_key, False))

            def _ef_toggle(k=ef_on_key, ck=ck):
                on_ = not st.session_state.get(k, False)
                st.session_state[k] = on_
                if on_:                                   # opening: every file starts ticked
                    for k_ in ck.values():
                        st.session_state[k_] = True

            def _ef_all(ck=ck):
                for k_ in ck.values():
                    st.session_state[k_] = True

            def _ef_clear(ck=ck):
                for k_ in ck.values():
                    st.session_state[k_] = False

            if all_files:
                fa, fb = st.columns([4, 2])
                with fa:
                    st.caption("**Folder P&L**")
                    frag(run_every=f_run)(_pnl_inline)(uid, f_paths, f_cap)
                with fb:
                    st.button("✖ Cancel" if ef_on else "Exit folder", key=f"exitfolder_{folder}",
                              on_click=_ef_toggle, use_container_width=True,
                              help="Clicking this shows a checkbox next to each file below; tick the files you want and click Exit now")
                st.divider()
            else:
                st.caption("No files in this folder. Create a file in the Paper Trading tab.")

            # ----- files table -----
            if files:
                w = ([0.5] if ef_on else []) + [2.4, 2.0, 1.2, 3.2, 0.8, 0.9, 0.8]
                hc = st.columns(w)
                for col, label in zip(hc, (("✔",) if ef_on else ()) + ("Name & details", "Instruments", "Status", "P&L", "Edit", "Exit", "Del" if vmode == "paper" else "")):
                    col.caption(f"**{label}**")
            for meta in files:
                running = meta.get("running", False)
                has_open = strategy_pnl(uid, meta["path"])["open"] > 0
                capital = meta.get("capital", "-")
                syms = [i.get("symbol", "") for i in meta.get("items", [])]
                inst = ", ".join(syms[:3]) + (f" +{len(syms) - 3}" if len(syms) > 3 else "")
                r = st.columns(w)
                if ef_on:
                    with r[0]:
                        st.checkbox("select", key=ck[meta["file"]], label_visibility="collapsed")
                    r = r[1:]
                with r[0]:
                    # click file name = open the file ( type="tertiary" needs Streamlit 1.46+ )
                    if st.button(f"📄 {meta['file']}", key=f"sopen_{folder}_{meta['file']}",
                                 type="tertiary", help="Click to open the file"):
                        _go_file(folder, meta, False, "home")
                    st.caption(f"{meta.get('exchange', '-')} · {meta.get('tf_label', '-')} · capital {capital}"
                               + (f" · {PRODUCT_LABEL.get(meta.get('product', 'INTRADAY'), '')}" if meta.get("live") else ""))
                with r[1]:
                    st.caption(inst or "-")
                with r[2]:
                    st.caption(("🟢 Running" if running else "⚪ Stopped") + ("  🔴 LIVE" if meta.get("live") else ""))
                    if not running and meta.get("was_running"):
                        st.caption("⚠️ was running before the restart - not running now (click Resume)")
                with r[3]:
                    frag(run_every=2 if running else None)(_pnl_inline)(uid, [meta["path"]], capital)
                with r[4]:
                    if st.button("✏️", key=f"sedit_{folder}_{meta['file']}", help="Edit settings",
                                 use_container_width=True):
                        _go_file(folder, meta, True, "home")
                with r[5]:
                    if st.button("Exit", key=f"sexit_{folder}_{meta['file']}", use_container_width=True,
                                 help="Closes all open positions of this file and stops the strategy"):
                        _eng = get_strategy_engine(uid, meta["path"])
                        n = _eng.exit_all("Manual exit (Exit)")
                        st.session_state["flash"] = (f"{folder} / {meta['file']}: {n} position(s) closed, "
                                                     "strategy stopped." + _fail_note(_eng))
                        st.rerun()
                with r[6]:
                    if vmode == "live":
                        pass                                  # live: no delete option at all
                    elif st.button("🗑", key=f"sdel_{folder}_{meta['file']}", help="Delete file",
                                   use_container_width=True):
                        if running:
                            st.warning("Stop first, then delete.")
                        elif has_open:
                            st.warning("There are open positions - Exit them first, then delete.")
                        else:
                            delete_strategy(uid, folder, meta["file"])
                            st.rerun()
            if ef_on and all_files:
                chosen = [m for m in all_files if st.session_state.get(ck[m["file"]])]
                _sp, xr = st.columns([6, 2.2])
                with xr:
                    if st.button("Exit now", key=f"efnow_{folder}", type="primary",
                                 use_container_width=True, disabled=not chosen):
                        closed_n = 0
                        engs = []
                        for m in chosen:
                            eng_ = get_strategy_engine(uid, m["path"])
                            engs.append(eng_)
                            closed_n += eng_.exit_all("Manual exit (Exit folder)")
                        st.session_state[f"efgen_{folder}"] = ef_gen + 1
                        st.session_state[ef_on_key] = False
                        st.session_state["flash"] = (f"{folder}: {len(chosen)} file(s) exited, {closed_n} position(s) closed, "
                                                     "selected files stopped." + _fail_note(*engs))
                        st.rerun()
                    g1, g2 = st.columns(2)
                    g1.button("Select all", key=f"efall_{folder}", on_click=_ef_all, type="tertiary",
                              use_container_width=True)
                    g2.button("Clear", key=f"efclr_{folder}", on_click=_ef_clear, type="tertiary",
                              use_container_width=True)
            if vmode == "paper" and not all_files and st.button("Delete folder", key=f"delfolder_{folder}"):
                import shutil
                shutil.rmtree(os.path.join(user_strategies_root(uid), folder), ignore_errors=True)
                st.rerun()


def _ui_css():
    """ONE style block per form: popover pickers look like the dropdowns, labels / sections line up."""
    st.markdown(
        "<style>"
        "div[data-testid='stElementContainer']:has(> div[data-testid='stMarkdown'] style){display:none}"
        "div[data-testid='stPopover'] button{display:flex;justify-content:space-between;align-items:center;"
        "width:100%;min-height:auto;text-align:left;border-radius:.5rem;border:1px solid transparent;"
        "background:rgba(128,128,128,.16);background:color-mix(in srgb,currentColor 10%,transparent);"
        "color:inherit;font-weight:400;transition:border-color .15s}"
        "div[data-testid='stPopover'] button:hover{border-color:var(--primary-color,#ff4b4b)}"
        "div[data-testid='stPopover'] button > div{flex:1;text-align:left}"
        "div[data-testid='stPopover'] button p{text-align:left;margin:0}"
        "div[data-testid='stPopoverBody']{border-radius:.75rem;box-shadow:0 10px 28px rgba(0,0,0,.30);"
        "min-width:min(34rem,90vw)}"
        "div[data-testid='stPopoverBody'] div[data-testid='stHorizontalBlock']{flex-wrap:nowrap !important;gap:.5rem}"
        "div[data-testid='stPopoverBody'] div[data-testid='stColumn'],"
        "div[data-testid='stPopoverBody'] div[data-testid='column']{min-width:0 !important}"
        ".fld-l{font-size:.875rem;line-height:1.4;margin:0 0 .3rem 0;opacity:.92}"
        ".sec-h{display:flex;align-items:center;gap:.55rem;font-weight:600;font-size:1.05rem;margin:0 0 .6rem 0}"
        ".sec-h i{display:inline-block;width:.32rem;height:1.15rem;border-radius:3px;background:var(--primary-color,#ff4b4b)}"
        ".sec-h small{font-weight:400;opacity:.6;font-size:.8rem}"
        "div[data-testid='stVerticalBlockBorderWrapper']{border-radius:.9rem}"
        "</style>",
        unsafe_allow_html=True,
    )


def _lbl(text, help=None):
    """Field label drawn the same way for every control (so rows line up)."""
    tip = f" title=\"{help}\"" if help else ""
    st.markdown(f"<div class='fld-l'{tip}>{text}{' &#9432;' if help else ''}</div>", unsafe_allow_html=True)


def _section(title, sub=""):
    st.markdown(f"<div class='sec-h'><i></i>{title}" + (f" <small>{sub}</small>" if sub else "") + "</div>",
                unsafe_allow_html=True)


def _stock_picker(label, labels, key, default=None, button_label="Select stocks"):
    """Stock picker: dropdown-style button -> tick-box list; small 'Select all' / 'Clear' on its right side."""
    big = len(labels) > 300                      # huge lists (NFO etc.) keep the normal multiselect
    ck = {lb: f"{key}__ck_{lb}" for lb in labels}
    if big:
        all_key = f"{key}__all"
        if key not in st.session_state:
            st.session_state[key] = [x for x in (default or []) if x in labels]
    else:
        dset = set(default or [])
        for lb, k_ in ck.items():
            if k_ not in st.session_state:
                st.session_state[k_] = lb in dset

    def _sel_all():
        if big:
            st.session_state[all_key] = True
        else:
            for k_ in ck.values():
                st.session_state[k_] = True

    def _clear():
        if big:
            st.session_state[all_key] = False
            st.session_state[key] = []
        else:
            for k_ in ck.values():
                st.session_state[k_] = False

    if big:
        _lbl(label)
        n_big = len(labels) if st.session_state.get(all_key) else len(st.session_state.get(key, []))
        with st.popover(f"{button_label} · {n_big} selected" if n_big else button_label, use_container_width=True):
            lst, side = st.columns([6, 1.4])
            with lst:
                if st.session_state.get(all_key):
                    st.success(f"✅ All {len(labels)} selected")
                else:
                    st.multiselect(label, labels, key=key, label_visibility="collapsed")
            with side:
                st.button("Select all", key=f"{key}__btn_all", on_click=_sel_all, type="tertiary", use_container_width=True)
                st.button("Clear", key=f"{key}__btn_clr", on_click=_clear, type="tertiary", use_container_width=True)
        return list(labels) if st.session_state.get(all_key) else list(st.session_state.get(key, []))
    _lbl(label)
    n_sel = sum(1 for k_ in ck.values() if st.session_state.get(k_))
    with st.popover(f"{button_label} · {n_sel} selected" if n_sel else button_label, use_container_width=True):
        lst, side = st.columns([6, 1.4])
        with lst:
            with st.container(height=min(320, 38 * len(labels) + 12)):
                for lb in labels:
                    st.checkbox(lb, key=ck[lb])
        with side:
            st.button("Select all", key=f"{key}__btn_all", on_click=_sel_all, type="tertiary", use_container_width=True)
            st.button("Clear", key=f"{key}__btn_clr", on_click=_clear, type="tertiary", use_container_width=True)
    return [lb for lb in labels if st.session_state.get(ck[lb])]


SIZE_LABELS = {"amount": "Amount", "qty": "Qty", "equal": "Equal weight"}


def _equal_amt(capital, max_open, no_limit, n_items):
    """Equal weight = capital / max positions (or / number of selected stocks when there is no limit)."""
    n = n_items if no_limit else max_open
    return round(float(capital) / n, 2) if capital and n else None


def _sizing_inputs(c_mode, c_val, capital, max_open, no_limit, n_items, key,
                   cur_mode="amount", default_amt=None, cur_qty=None):
    """Dropdown (Amount / Qty / Equal weight) + the value box for the chosen option.
       Returns (size_mode, amount, qty). amount = Rs per position (equal weight: auto-calculated)."""
    keys = list(SIZE_LABELS)
    pick = c_mode.selectbox("Position", [SIZE_LABELS[k] for k in keys],
                            index=keys.index(cur_mode) if cur_mode in keys else 0, key=f"{key}_size_mode",
                            help="Amount = Rs per position | Qty = quantity per position "
                                 "(shares; lots for NFO/MCX) | Equal weight = capital / max positions "
                                 "(if no limit: capital / number of selected stocks)")
    mode = keys[[SIZE_LABELS[k] for k in keys].index(pick)]
    eq = _equal_amt(capital, max_open, no_limit, n_items)
    if mode == "qty":
        q = c_val.number_input("Qty", min_value=1, value=int(cur_qty) if cur_qty else None,
                               step=1, placeholder="Qty", key=f"{key}_size_qty")
        return mode, float(eq or 0), (int(q) if q else None)
    if mode == "equal":
        c_val.text_input("Capital / positions (auto)", value=f"{eq:,.2f}" if eq else "", disabled=True)
        return mode, eq, 0
    amt = c_val.number_input("Amount", min_value=1.0,
                             value=float(default_amt) if default_amt else None, step=1000.0, placeholder="Amount")
    return mode, amt, 0


def _paper_form(uid):
    """Mode (Paper / Live) + Folder Name + File Name + Exchange / Stocks / Capital ... + Start."""
    _ui_css()
    mode_pick = st.radio("Mode", ["📈 Paper Trading", "🔴 Live Trading"], horizontal=True,
                         key="bd_mode", label_visibility="collapsed")
    live = mode_pick.startswith("🔴")
    st.caption("You can switch Paper / Live above after selecting Exchange, stocks and capital."
               if not live else "🔴 LIVE = real orders (INTRADAY, LIMIT). Fill in the Live settings below.")
    gen = st.session_state.get("pt_gen", 0)
    smart = st.session_state.get("smart")
    NEWF = "＋ New folder..."
    folders = list(list_strategies(uid, "live" if live else "paper").keys())
    opts = folders + [NEWF]
    if st.session_state.get("pt_folder") not in opts:
        st.session_state.pop("pt_folder", None)

    with st.container(border=True):
        c1, c2 = st.columns(2)
        pick = c1.selectbox("Folder Name", opts, index=None, placeholder="Select or create a folder", key="pt_folder")
        new_folder = ""
        if pick == NEWF:
            new_folder = c1.text_input("New folder name", key=f"pt_newfolder_{gen}", placeholder="e.g. Pattern Scalping")
        file_name = c2.text_input("File Name", key=f"pt_file_{gen}", placeholder="e.g. NSE morning")
        folder = (new_folder if pick == NEWF else pick) or ""

        try:
            master = load_master()
        except Exception as ex:
            master = None
            st.warning(f"Could not load the stock list ({ex}).")

        e1, e2, e3 = st.columns(3)
        exchange = e1.selectbox("Exchange", ["NSE", "BSE", "NFO", "MCX"], key="pt_exchange")
        capital = e2.number_input("Capital", min_value=10000.0, value=None, step=10000.0, placeholder="Capital")
        tf_label = e3.selectbox("Candle timeframe", list(TIMEFRAMES), index=None, placeholder="Select timeframe")
        product, hold_days = "INTRADAY", 1
        if live:                                            # Order type sits on top, above Entry / Exit condition
            o1, _o2, _o3 = st.columns(3)
            popts = PRODUCTS_BY_EXCHANGE.get(exchange, ["INTRADAY"])
            product = o1.selectbox("Order type (Product)", popts, format_func=lambda k: PRODUCT_LABEL[k],
                                   key=f"live_product_{exchange}")
        with st.container(border=True):
            _section("Entry condition", "index, stocks, candle patterns, position size")
            ix1, _ix2, _ix3 = st.columns(3)
            with ix1:
                index_pick = _stock_picker("Index", index_options(exchange), f"pt_index_{exchange}",
                                           button_label="Select index")
            with _ix2:
                _lbl("Buy / Sell (optional)", help="Buy all = when you click Start, immediately Buy all selected stocks "
                                                   "(up to max positions). Sell all = all positions already open in this file "
                                                   "are closed.")
                buy_mode = st.selectbox("Buy / Sell (optional)", ["Buy all stocks", "Sell all (close open positions)"],
                                        index=None, placeholder="Not needed", key=f"pt_buysell_{exchange}",
                                        label_visibility="collapsed")

            items = []
            if master is not None:
                inst = exchange_list_cached(exchange, index_pick)
                labels = inst["label"].tolist()
                by_label = inst.set_index("label")
                if index_pick and not labels:
                    st.warning("Could not download the selected index list (internet / niftyindices.com). Try a different index.")
                ix_name = " + ".join(index_pick) if len(index_pick) <= 2 else f"{len(index_pick)} indices"
                picked = _stock_picker(f"{ix_name or exchange} stocks ({len(labels)})", labels,
                                       f"pt_stocks_{exchange}_{'+'.join(index_pick) or 'all'}",
                                       default=labels if index_pick else None)
                typed = st.text_input("Or type names (comma separated)", key="pt_typed")
                names, miss = list(picked), []
                for t in [x.strip().upper() for x in typed.split(",") if x.strip()]:
                    hit = inst[(inst["label"].str.upper() == t) | (inst["symbol"].str.upper() == t)
                               | (inst["name"].str.upper() == t)]
                    if hit.empty:
                        miss.append(t)
                    elif hit.iloc[0]["label"] not in names:
                        names.append(hit.iloc[0]["label"])
                if miss:
                    st.warning("Not found in " + exchange + ": " + ", ".join(miss))
                items = [to_item({**by_label.loc[n].to_dict(), "label": n}, exchange) for n in names]
                st.caption(f"✅ Total {len(items)} stocks selected (of {len(labels)} in the chosen index list) - "
                           "all stocks will appear in Monitoring.")
            else:
                typed = st.text_input("Type names (comma separated)", key="pt_typed2")
                miss = []
                for t in [x.strip().upper() for x in typed.split(",") if x.strip()]:
                    it = search_item(smart, exchange, t) if smart else None
                    if it:
                        items.append(it)
                    else:
                        miss.append(t)
                if miss:
                    st.warning("Not found: " + ", ".join(miss))
            picked_pats = _stock_picker(f"Candle patterns ({len(PATTERNS)})", list(PATTERNS), "pt_patterns",
                                        default=list(PATTERNS), button_label="Select candle patterns")
            cl1, _cl2, _cl3 = st.columns(3)
            with cl1:
                cloud_sel = _stock_picker("Ichimoku cloud (optional) - select one or more",
                                          [CLOUD_LABEL[k] for k in CLOUD_OPTIONS], f"pt_cloud_{gen}",
                                          button_label="Select cloud position (optional)")
            cloud_pick = cloud_text([CLOUD_BY_LABEL[x] for x in cloud_sel])      # '' = filter off

            NO_LIMIT = "Select max (no limit)"
            m1, m2, m3 = st.columns(3)
            max_pick = m1.selectbox("Max open positions", [NO_LIMIT] + list(range(1, 26)) + [30, 40, 50], index=0)
            no_limit = max_pick == NO_LIMIT
            max_open = 10 ** 6 if no_limit else int(max_pick)
            size_mode, position_amount, position_qty = _sizing_inputs(
                m2, m3, capital, max_open, no_limit, len(items), "pt",
                default_amt=None if (no_limit or not capital) else round(capital / max_open, 2))

        sl_pct = buf_pct = max_loss = max_oval = None
        live_ok_box = True
        with st.container(border=True):
            _section("Exit condition", "target, cloud, hold days")
            x1, x2, x3 = st.columns(3)
            target_pct = x1.number_input("Target (%) - optional", min_value=0.01, value=None,
                                         step=0.01, format="%.2f", placeholder="Empty = no target",
                                         help="You can give Target only, Cloud exit only, or both. "
                                              "If both are set, whichever is hit first triggers the exit.")
            with x2:
                cx_sel = _stock_picker("Cloud exit (optional)", [CLOUD_LABEL[k] for k in CLOUD_EXIT_OPTS],
                                       f"pt_cloudx_{gen}", button_label="Select cloud exit (optional)")
            if live and product != "INTRADAY":
                hold_days = x3.number_input("Max hold (days)", min_value=1, value=5, step=1,
                                            help="After this many days, time exit at 15:15 (MCX 23:15)")
            cloud_exit_pick = cloud_text([CLOUD_BY_LABEL[x] for x in cx_sel])      # '' = off
            if live and product != "INTRADAY":
                st.warning("⚠️ Non-intraday product: the position is held overnight. **Stop loss is software-based only** "
                           "(not on the exchange) - SL works only while the app / computer / internet is ON. "
                           "The target order is re-placed every morning.")
        if live:
            st.markdown("**🔴 LIVE settings**  ·  Order type: LIMIT  ·  BUY (long) only")
            lc = st.columns([1.5, 1, 1, 1, 1])
            with lc[0]:
                lo_sel = _stock_picker("Stop loss & risk settings (optional)", list(LIVE_OPTS), f"pt_liveopt_{gen}",
                                       button_label="Select options")
            slots = iter(lc[1:])
            if LIVE_OPTS[0] in lo_sel:
                sl_pct = next(slots).number_input("Stop loss (%)", min_value=0.01, value=None, step=0.01,
                                                  format="%.2f", placeholder="SL %", key=f"pt_sl_{gen}",
                                                  help="Empty = no stop loss (only target / time exit)")
            if LIVE_OPTS[1] in lo_sel:
                buf_pct = next(slots).number_input("Limit buffer (%)", min_value=0.01, value=0.10, step=0.01,
                                                   format="%.2f", key=f"pt_buf_{gen}",
                                                   help="BUY limit = LTP + buffer, exit SELL limit = LTP - buffer. Not selected = 0.10%")
            if LIVE_OPTS[2] in lo_sel:
                max_loss = next(slots).number_input("Max daily loss (Rs)", min_value=1.0, value=None, step=500.0,
                                                    placeholder="Kill switch Rs", key=f"pt_mdl_{gen}")
            if LIVE_OPTS[3] in lo_sel:
                max_oval = next(slots).number_input("Max order value (Rs)", min_value=0.0, value=None, step=5000.0,
                                                    placeholder="Rs per order", key=f"pt_mov_{gen}")
            st.caption("Have you registered a static IP (Angel One SmartAPI)? On the first day, test with 1 stock and a small amount.")
            live_ok_box = st.checkbox("This is a REAL order with real money. I understand the risk.", key="live_confirm")

        # is this folder/file already there / running?
        path = strategy_dir(uid, folder, file_name) if folder.strip() and file_name.strip() else None
        eng = _get_engine_by_path(uid, path) if path else None
        is_running = bool(eng and eng.running)
        exists = bool(path and os.path.exists(os.path.join(path, "config.json")))
        if exists and not is_running:
            st.caption("This folder / file already exists - clicking Start will overwrite its settings.")
        if is_running:
            st.caption("This file is already RUNNING. Click the file name in My Strategies to view it.")

        if buy_mode and live:
            st.warning("Clicking Start will send REAL orders: " + (
                "BUY for all selected stocks (up to max positions)." if buy_mode.startswith("Buy")
                else "SELL for all positions currently open in this file."))
        start = st.button("▶ Start LIVE" if live else "▶ Start", type="primary",
                          disabled=is_running or not live_ok_box, key=f"pt_start_{gen}")

    if start:
        missing = [n for n, v in (("Folder Name", folder.strip()), ("File Name", file_name.strip()),
                                  ("Capital", capital), ("Candle timeframe", tf_label),
                                  (SIZE_LABELS[size_mode], position_qty if size_mode == "qty" else position_amount))
                   if not v]
        if missing:
            st.error("Fill: " + ", ".join(missing))
        elif not target_pct and not cloud_exit_pick:
            st.error("Exit condition: provide Target % or Cloud exit - at least one of the two.")
        elif not items:
            st.error("Please select stocks.")
        elif not picked_pats:
            st.error("Please select candle patterns.")
        elif smart is None:
            st.error("Not logged in to Angel One.")
        else:
            interval, tf_min = TIMEFRAMES[tf_label]
            data = {
                "exchange": exchange, "items": items, "capital": float(capital),
                "tf_label": tf_label, "interval": interval, "tf_min": tf_min,
                "max_open": int(max_open), "no_limit": no_limit,
                "position_amount": float(position_amount or 0), "size_mode": size_mode,
                "position_qty": int(position_qty or 0), "target_pct": float(target_pct or 0),
                "patterns": list(picked_pats), "cloud_filter": cloud_pick, "cloud_exit": cloud_exit_pick,
            }
            if live:
                data.update({"live": True, "sl_pct": float(sl_pct or 0), "limit_buffer_pct": float(buf_pct or 0.1),
                             "max_daily_loss": float(max_loss or 0), "max_order_value": float(max_oval or 0),
                             "product": product, "max_hold": int(hold_days) if product != "INTRADAY" else 1})
            try:
                create_folder(uid, folder, "live" if live else "paper")
            except ValueError as ex_:
                st.error(str(ex_))
                return
            spath = save_strategy_config(uid, folder, file_name, data)
            engine = get_strategy_engine(uid, spath)
            if engine.smart is None:
                engine.set_login(smart, st.session_state.get("creds"), st.session_state.get("client_id", ""))
            cfg = _cfg_from_data(data)
            engine.start(engine.smart or smart, cfg, items, exchange, False)
            if buy_mode and buy_mode.startswith("Buy"):    # optional: BUY every selected stock (background, 1 LTP call each)
                threading.Thread(target=engine.manual_buy_all, args=(list(items),), daemon=True).start()
                st.session_state["flash"] = "Buy all started - see Logs / Live positions."
            elif buy_mode:                                 # optional: SELL = close this file's open positions
                n_sold = engine.manual_sell_all()
                st.session_state["flash"] = (f"Sell all: {n_sold} position(s) closed." if n_sold
                                             else "Sell all: there is no open position in this file.")
            sf, sn = _safe_name(folder), _safe_name(file_name)
            st.session_state["pt_gen"] = gen + 1            # fresh boxes next time
            st.session_state.pop("pt_folder", None)
            st.session_state.pop("live_confirm", None)
            st.session_state["builder_active"] = {"folder": sf, "file": sn, "path": spath}
            _set_nav("builder", sf, sn)
            st.rerun()


def edit_settings_panel(uid, folder, file_name, path, engine, cfg_data):
    """Edit settings expander - used by My Strategies (file_dashboard) AND Strategy Builder (_run_view).
       Works while RUNNING or STOPPED, paper or live. Saved to config.json, so Stop -> Start keeps the new values."""
    exchange = cfg_data.get("exchange", "NSE")
    tf_label = cfg_data.get("tf_label", "-")
    capital = cfg_data.get("capital", 0)
    max_open = cfg_data.get("max_open", 5)
    no_limit = cfg_data.get("no_limit", False)
    target_pct = cfg_data.get("target_pct", 1.0)
    items = cfg_data.get("items", [])
    position_amount = cfg_data.get("position_amount", 0)
    _ui_css()
    with st.expander("Edit settings (can be changed even while running)",
                     expanded=st.session_state.get("edit_open") == f"{folder}/{file_name}"):
        open_now_ = engine.snapshot()["state"]["open"]
        has_open_pos = bool(open_now_)
        if engine.running:
            st.caption("")
        smart = st.session_state.get("smart")
        try:
            master = load_master()
        except Exception:
            master = None
        is_live = bool(cfg_data.get("live"))
        EXS = ["NSE", "BSE", "NFO", "MCX"]
        r1, r2, r3 = st.columns(3)
        new_ex = r1.selectbox("Exchange", EXS, disabled=has_open_pos, index=EXS.index(exchange) if exchange in EXS else 0)
        new_capital = r2.number_input("Capital", min_value=10000.0, value=float(capital), step=10000.0)
        tf_keys = list(TIMEFRAMES)
        tf_idx = tf_keys.index(tf_label) if tf_label in tf_keys else 2
        new_tf = r3.selectbox("Candle timeframe", tf_keys, index=tf_idx)
        if has_open_pos:
            st.caption("Exchange cannot be changed while positions are open (you can change it after all positions exit).")

        cur_prod = str(cfg_data.get("product") or "INTRADAY")
        new_prod, new_hold = "INTRADAY", 1
        if is_live:                                         # Order type sits on top, above Entry / Exit condition
            o1, _o2, _o3 = st.columns(3)
            popts = PRODUCTS_BY_EXCHANGE.get(new_ex, ["INTRADAY"])
            new_prod = o1.selectbox("Order type (Product)", popts,
                                    index=popts.index(cur_prod) if cur_prod in popts else 0,
                                    format_func=lambda k: PRODUCT_LABEL[k],
                                    key=f"edit_product_{folder}_{file_name}_{new_ex}",
                                    help="If changed, positions that are open now stay in the old product; "
                                         "the new product applies to new entries only.")

        new_items = []
        bs_mode = None
        with st.container(border=True):
            _section("Entry condition", "index, stocks, candle patterns, position size")
            if master is not None:
                ex_ix1, ex_ix2 = st.columns(2)
                with ex_ix1:
                    edit_index = _stock_picker("Index", index_options(new_ex), f"edit_index_{folder}_{file_name}_{new_ex}",
                                               button_label="Select index")
                with ex_ix2:
                    _lbl("Buy / Sell (optional)", help="Applied when you click Save settings: Buy all = Buy all stocks, "
                                                       "Sell all = close all open positions.")
                    bs_mode = st.selectbox("Buy / Sell (optional)", ["Buy all stocks", "Sell all (close open positions)"],
                                           index=None, placeholder="Not needed", key=f"edit_buysell_{folder}_{file_name}",
                                           label_visibility="collapsed")
                inst = exchange_list_cached(new_ex, edit_index)
                labels = inst["label"].tolist()
                by_label = inst.set_index("label")
                current_syms = [it["symbol"] for it in items if it.get("exchange") == new_ex]
                default_pick = labels if edit_index else [x for x in current_syms if x in labels]
                if edit_index and not labels:
                    st.warning("Could not download the selected index list (internet / niftyindices.com). Try a different index.")
                ex_name = " + ".join(edit_index) if len(edit_index) <= 2 else f"{len(edit_index)} indices"
                picked = _stock_picker(f"{ex_name or new_ex} stocks", labels,
                                       f"edit_stocks_{new_ex}_{'+'.join(edit_index) or 'all'}",
                                       default=default_pick)
                new_items = [to_item({**by_label.loc[n].to_dict(), "label": n}, new_ex) for n in picked]
                st.caption(f"✅ Total {len(new_items)} stocks selected (of {len(labels)} in the chosen index list) - "
                           "all stocks will appear in Monitoring.")
            cur_pats = [p for p in (cfg_data.get("patterns") or PATTERNS) if p in PATTERNS] or list(PATTERNS)
            new_pats = _stock_picker(f"Candle patterns ({len(PATTERNS)})", list(PATTERNS),
                                     f"edit_patterns_{folder}_{file_name}", default=cur_pats,
                                     button_label="Select candle patterns")
            ec1, _ec2, _ec3 = st.columns(3)
            with ec1:
                cloud_sel_e = _stock_picker("Ichimoku cloud (optional)",
                                            [CLOUD_LABEL[k] for k in CLOUD_OPTIONS], f"edit_cloud_{folder}_{file_name}",
                                            default=[CLOUD_LABEL[k] for k in cloud_list(cfg_data.get("cloud_filter"))],
                                            button_label="Select cloud position (optional)")
            new_cloud = cloud_text([CLOUD_BY_LABEL[x] for x in cloud_sel_e])      # '' = filter off
            NO_LIMIT = "Select max (no limit)"
            max_opts = [NO_LIMIT] + list(range(1, 26)) + [30, 40, 50]
            cur_max = NO_LIMIT if no_limit else (max_open if max_open in max_opts else 5)
            q1, q2, q3 = st.columns(3)
            max_pick = q1.selectbox("Max open positions", max_opts,
                                    index=max_opts.index(cur_max) if cur_max in max_opts else 0)
            new_no_limit = max_pick == NO_LIMIT
            new_max = 10 ** 6 if new_no_limit else int(max_pick)
            new_mode, new_amt, new_qty = _sizing_inputs(
                q2, q3, new_capital, new_max, new_no_limit, len(new_items or items), f"edit_{folder}_{file_name}",
                cur_mode=cfg_data.get("size_mode") or "amount",
                default_amt=float(position_amount) if position_amount else float(round(new_capital / max(new_max, 1), 2)),
                cur_qty=cfg_data.get("position_qty") or None)

        new_sl = 0.0
        with st.container(border=True):
            _section("Exit condition", "target, cloud, hold days")
            x1, x2, x3 = st.columns(3)
            new_tgt = x1.number_input("Target (%) - optional", min_value=0.01,
                                      value=float(target_pct) if target_pct else None, step=0.01, format="%.2f",
                                      placeholder="Empty = no target")
            with x2:
                cx_sel_e = _stock_picker("Cloud exit (optional)", [CLOUD_LABEL[k] for k in CLOUD_EXIT_OPTS],
                                         f"edit_cloudx_{folder}_{file_name}",
                                         default=[CLOUD_LABEL[k] for k in cloud_list(cfg_data.get("cloud_exit"))
                                                  if k in CLOUD_EXIT_OPTS],
                                         button_label="Select cloud exit (optional)")
            if is_live:
                if new_prod != "INTRADAY":
                    new_hold = x3.number_input("Max hold (days)", min_value=1, step=1,
                                               value=int(cfg_data.get("max_hold") or 5) if cur_prod != "INTRADAY" else 5,
                                               key=f"edit_hold_{folder}_{file_name}",
                                               help="After this many days, time exit at 15:15 (MCX 23:15)")
            new_cloud_exit = cloud_text([CLOUD_BY_LABEL[x] for x in cx_sel_e])     # '' = off
            if is_live and new_prod != "INTRADAY":
                st.warning("⚠️ Non-intraday product: the position is held overnight. **Stop loss is software-based only** "
                           "(not on the exchange) - SL works only while the app / computer / internet is ON.")

        if is_live:
            st.markdown("**🔴 LIVE settings** (applied immediately when you Save)")
            cur_sl_ = float(cfg_data.get("sl_pct") or 0)
            cur_buf_ = float(cfg_data.get("limit_buffer_pct") or 0.1)
            cur_mdl_ = float(cfg_data.get("max_daily_loss") or 0)
            cur_mov_ = float(cfg_data.get("max_order_value") or 0)
            cur_sel_ = [LIVE_OPTS[i] for i, on_ in enumerate((cur_sl_ > 0, abs(cur_buf_ - 0.1) > 1e-9,
                                                                cur_mdl_ > 0, cur_mov_ > 0)) if on_]
            ek_ = f"{folder}_{file_name}"
            lc = st.columns([1.5, 1, 1, 1, 1])
            with lc[0]:
                lo_sel_e = _stock_picker("Stop loss & risk settings (optional)", list(LIVE_OPTS), f"edit_liveopt_{ek_}",
                                         default=cur_sel_, button_label="Select options")
            slots = iter(lc[1:])
            new_sl, new_buf, new_mdl, new_mov = 0.0, None, None, None        # not selected = off / default
            if LIVE_OPTS[0] in lo_sel_e:
                new_sl = next(slots).number_input("Stop loss (%)", min_value=0.01, value=cur_sl_ or None, step=0.01,
                                                  format="%.2f", placeholder="SL %", key=f"edit_sl_{ek_}")
            if LIVE_OPTS[1] in lo_sel_e:
                new_buf = next(slots).number_input("Limit buffer (%)", min_value=0.01, value=cur_buf_, step=0.01,
                                                   format="%.2f", key=f"edit_buf_{ek_}")
            if LIVE_OPTS[2] in lo_sel_e:
                new_mdl = next(slots).number_input("Max daily loss (Rs)", min_value=1.0, value=cur_mdl_ or None,
                                                   step=500.0, placeholder="Kill switch Rs", key=f"edit_mdl_{ek_}")
            if LIVE_OPTS[3] in lo_sel_e:
                new_mov = next(slots).number_input("Max order value (Rs)", min_value=0.0, value=cur_mov_ or None,
                                                   step=5000.0, placeholder="Rs per order", key=f"edit_mov_{ek_}")
        bs_ok = True
        if bs_mode and is_live:
            st.warning("Clicking Save will send REAL orders.")
            bs_ok = st.checkbox("Real orders will be sent - confirm", key=f"edit_bs_confirm_{folder}_{file_name}")
        if st.button("Save settings", key="edit_save", disabled=not bs_ok):
            if (new_mode == "qty" and not new_qty) or (new_mode != "qty" and not new_amt):
                st.error("Please enter a position size value.")
                return
            if not new_tgt and not new_cloud_exit:
                st.error("Exit condition: provide Target % or Cloud exit - at least one of the two.")
                return
            interval, tf_min = TIMEFRAMES[new_tf]
            data = {
                "exchange": new_ex,
                "items": new_items or items,
                "capital": float(new_capital),
                "tf_label": new_tf,
                "interval": interval,
                "tf_min": tf_min,
                "max_open": int(new_max),
                "no_limit": new_no_limit,
                "position_amount": float(new_amt or 0),
                "size_mode": new_mode,
                "position_qty": int(new_qty or 0),
                "target_pct": float(new_tgt or 0),
                "patterns": list(new_pats) or cur_pats,
                "cloud_filter": new_cloud,
                "cloud_exit": new_cloud_exit,
            }
            if not new_pats:
                st.warning("Nothing selected - the old candle patterns stay as they are.")
            # a stock that still has an OPEN position stays in the list until that position exits
            final_items = list(new_items or items)
            have = {(it.get("exchange"), it["symbol"]) for it in final_items}
            open_keys = {(p["exchange"], p["symbol"]) for p in open_now_}
            kept = [it for it in items if (it.get("exchange"), it["symbol"]) in open_keys
                    and (it.get("exchange"), it["symbol"]) not in have]
            final_items += kept
            data["items"] = final_items
            for _k in LIVE_KEYS:                       # keep live settings of a live file
                if _k in cfg_data:
                    data[_k] = cfg_data[_k]
            if is_live:                                # edited live values -> config.json (survives Stop / Start)
                data.update({"sl_pct": float(new_sl or 0), "limit_buffer_pct": float(new_buf or 0.1),
                             "max_daily_loss": float(new_mdl or 0), "max_order_value": float(new_mov or 0),
                             "product": new_prod, "max_hold": int(new_hold) if new_prod != "INTRADAY" else 1})
            changes = _edit_changes(cfg_data, data)
            save_strategy_config(uid, folder, file_name, data)
            with engine.lock:                               # Logs: exactly what was edited
                add_log(engine.state, now_ist(), "EDIT settings: " + ("; ".join(changes) if changes else "no change"))
                save_state(engine.state)
            msg = "Settings saved." + (f" Changed: {len(changes)} item(s) - see Logs." if changes else " (nothing changed)")
            if kept:
                msg += " Open position(s) in " + ", ".join(it["symbol"] for it in kept) + " will stay in the list until they exit."
            if engine.running:
                new_cfg = _cfg_from_data({**cfg_data, **data})
                same_watch = (new_ex == exchange and int(tf_min) == int(cfg_data.get("tf_min", 5))
                              and {(i.get("exchange"), i["symbol"]) for i in final_items}
                              == {(i.get("exchange"), i["symbol"]) for i in items})
                smart_ = engine.smart or st.session_state.get("smart")
                if same_watch:
                    engine.update_config(new_cfg)                    # numbers only -> instant, no restart
                    msg += " Applied to the running strategy immediately."
                elif smart_ is None:
                    msg += " (Not logged in to Angel - not applied to the running strategy; Stop and Start again.)"
                else:
                    engine.start(smart_, new_cfg, final_items, new_ex, False)   # open positions are kept
                    msg += " Strategy restarted (open positions are unchanged)."
            if bs_mode == "Buy all stocks":
                if engine.running:
                    threading.Thread(target=engine.manual_buy_all, args=(list(final_items),), daemon=True).start()
                    msg += " Buy all started."
                else:
                    msg += " To place Buy all, Start the strategy (it is not running)."
            elif bs_mode:
                msg += f" Sell all: {engine.manual_sell_all()} position(s) closed."
            st.session_state.pop("edit_open", None)
            st.session_state["flash"] = msg
            st.rerun()




def _edit_changes(old, new):
    """Human readable list of what changed between the old config dict and the saved one."""
    def num(v):
        try:
            return float(v or 0)
        except (TypeError, ValueError):
            return v

    def size(d):
        m = d.get("size_mode") or "amount"
        if m == "qty":
            return f"qty {int(d.get('position_qty') or 0)}"
        return ("equal weight " if m == "equal" else "amount ") + f"{float(d.get('position_amount') or 0):,.0f}"

    out = []
    for label, k, dflt in (("Exchange", "exchange", ""), ("Timeframe", "tf_label", ""), ("Capital", "capital", 0),
                           ("Target %", "target_pct", 0), ("Stop loss %", "sl_pct", 0),
                           ("Limit buffer %", "limit_buffer_pct", 0), ("Max daily loss", "max_daily_loss", 0),
                           ("Max order value", "max_order_value", 0), ("Order type", "product", "INTRADAY"),
                           ("Max hold days", "max_hold", 0)):
        if k not in new:
            continue
        o, n = old.get(k, dflt), new.get(k, dflt)
        if num(o) != num(n) if isinstance(dflt, (int, float)) else str(o or dflt) != str(n or dflt):
            out.append(f"{label}: {o if o not in (None, '') else dflt} -> {n}")
    mo = "no limit" if old.get("no_limit") else old.get("max_open")
    mn = "no limit" if new.get("no_limit") else new.get("max_open")
    if mo != mn:
        out.append(f"Max positions: {mo} -> {mn}")
    if size(old) != size(new):
        out.append(f"Position size: {size(old)} -> {size(new)}")
    co, cn = old.get("cloud_filter") or "off", new.get("cloud_filter") or "off"
    if co != cn:
        out.append(f"Cloud filter: {co} -> {cn}")
    xo, xn = old.get("cloud_exit") or "off", new.get("cloud_exit") or "off"
    if xo != xn:
        out.append(f"Cloud exit: {xo} -> {xn}")
    po, pn = list(old.get("patterns") or PATTERNS), list(new.get("patterns") or PATTERNS)
    if set(po) != set(pn):
        add, rem = [x for x in pn if x not in po], [x for x in po if x not in pn]
        out.append("Patterns: " + "; ".join(([f"+{', '.join(add)}"] if add else []) + ([f"-{', '.join(rem)}"] if rem else [])))
    so = {str(i.get("symbol")) for i in old.get("items") or []}
    sn = {str(i.get("symbol")) for i in new.get("items") or []}
    if so != sn:
        add, rem = sorted(sn - so), sorted(so - sn)
        def short(L):
            return ", ".join(L[:6]) + (f" +{len(L) - 6} more" if len(L) > 6 else "")
        out.append("Stocks: " + "; ".join(([f"added {len(add)} ({short(add)})"] if add else [])
                                          + ([f"removed {len(rem)} ({short(rem)})"] if rem else [])))
    return out


def manage_trades_panel(engine, live):
    """Close / delete ONE trade at a time. Paper: delete open or closed trades one by one. Live: close only."""
    snap = engine.snapshot()["state"]
    open_now, closed = snap["open"], snap["closed"]
    if not open_now and (live or not closed):
        return
    with st.expander("Manage positions / trades"):
        if open_now:
            keys = [f"{p['exchange']}:{p['symbol']}" for p in open_now]
            sel = st.selectbox("Open position", keys, key="mg_open")
            m1, m2 = st.columns(2)
            if m1.button("Close now", use_container_width=True, key="mg_close"):
                engine.close_now(sel)
                st.rerun()
            if (not live) and m2.button("Delete this open position (no record)", use_container_width=True, key="mg_del_open"):
                engine.delete_position(sel)
                st.rerun()
        if closed and not live:
            order = list(range(len(closed) - 1, -1, -1))          # newest first
            def _lbl(i):
                t = closed[i]
                return (f"{t.get('symbol')} | {str(t.get('entry_time', ''))[:16]} -> {str(t.get('exit_time', ''))[:16]} | "
                        f"P&L {float(t.get('pnl') or 0):,.2f} | {t.get('reason', '')}")
            i = st.selectbox("Closed trade", order, format_func=_lbl, key="mg_closed")
            if st.button("Delete this closed trade", use_container_width=True, key="mg_del_closed"):
                engine.delete_closed(i, closed[i])
                st.rerun()


def _run_view(uid, folder, file_name, path, live=False):
    """After Start: only Start / Stop + the full live result of this file."""
    cfg_data = load_strategy_config(path)
    if not cfg_data:
        st.error("Config for this file was not found.")
        return
    engine = get_strategy_engine(uid, path)
    if st.session_state.get("smart") and engine.smart is None:
        engine.set_login(st.session_state.smart, st.session_state.get("creds"),
                         st.session_state.get("client_id", ""))
    exchange = cfg_data.get("exchange", "NSE")
    tf_label = cfg_data.get("tf_label", "-")

    st.subheader(f"📁 {folder}  /  📄 {file_name}")
    ok_live = True
    if live:
        st.warning(f"🔴 LIVE - real orders ({PRODUCT_LABEL.get(cfg_data.get('product', 'INTRADAY'), 'Intraday')} / LIMIT). "
                   "After Stop, SL / target are not managed; "
                   "if there are open positions, use **Exit**.")
        ok_live = st.checkbox("Real orders will be sent - confirm", key="live_run_confirm")
    has_run = engine.has_run
    bcols = st.columns([1, 1, 1, 1, 3])
    start = bcols[0].button("▶ Start", type="primary", use_container_width=True,
                            disabled=engine.running or has_run or not ok_live, key="run_start",
                            help="First start of this file")
    need_ok = live and engine.cfg is None            # after an app restart a live file must be confirmed again
    resume = bcols[1].button("⏯ Resume", use_container_width=True,
                             disabled=engine.running or not has_run or (need_ok and not ok_live), key="run_resume",
                             help="Continue again after Stop - open positions and closed trades stay as they are")
    stop = bcols[2].button("⏹ Stop", use_container_width=True, disabled=not engine.running, key="run_stop")
    exit_btn = bcols[3].button("Exit", use_container_width=True, key="run_exit",
                               help="Stops the strategy and closes all open positions "
                                    + ("(real SELL orders)" if live else "(paper)"))
    if stop:
        engine.stop()
        n_open = len(engine.snapshot()["state"]["open"])
        if live and n_open:
            st.session_state["flash"] = (f"Stopped. ⚠️ {n_open} live position(s) open - SL / target are not being managed now. "
                                         "Click Resume, click Exit, or check the Angel One app.")
        else:
            st.session_state["flash"] = "Stopped. You can Resume."
        st.rerun()
    if exit_btn:
        n = engine.exit_all("Manual exit (Live Exit)" if live else "Manual exit (Exit)")
        st.session_state["flash"] = f"Exit: {n} position(s) closed, strategy stopped." + (_fail_note(engine) if live else "")
        st.rerun()
    if start or resume:
        smart = engine.smart or st.session_state.get("smart")
        if smart is None:
            st.error("Not logged in to Angel One.")
        elif not cfg_data.get("items"):
            st.error("No stocks in this file.")
        else:
            cfg = _cfg_from_data(cfg_data)
            (engine.resume if resume else engine.start)(smart, cfg, cfg_data["items"], exchange, False)
            st.rerun()

    edit_settings_panel(uid, folder, file_name, path, engine, cfg_data)

    frag = getattr(st, "fragment", None) or st.experimental_fragment
    fast = 1 if engine.running else None
    slow = 3 if engine.running else None

    @frag(run_every=fast)
    def _top():
        live_top(engine, exchange, tf_label)

    @frag(run_every=slow)
    def _mid():
        live_mid(engine)

    @frag(run_every=fast)
    def _pos():
        live_positions(engine)

    @frag(run_every=slow)
    def _bot():
        live_bottom(engine)

    _top()
    _mid()
    _pos()
    _bot()


def builder_page():
    """STRATEGY BUILDER: pick Paper / Live on top, fill Folder, File, Exchange, Stocks, Capital... -> Start."""
    uid = current_uid()
    no_dim()
    top_nav("builder")
    st.title("Strategy Builder")

    flash = st.session_state.pop("flash", None)
    if flash:
        st.success(flash)

    akey = "builder_active"
    active = st.session_state.get(akey)
    if not active:                       # refresh keeps you on the same running file (URL)
        qf = str(st.query_params.get("folder", "")).strip()
        qn = str(st.query_params.get("file", "")).strip()
        if qf and qn:
            pth = strategy_dir(uid, qf, qn)
            if os.path.exists(os.path.join(pth, "config.json")):
                active = {"folder": _safe_name(qf), "file": _safe_name(qn), "path": pth}
                st.session_state[akey] = active
    live = False
    if active:
        cfgd = load_strategy_config(active["path"])
        if not cfgd:                                     # file was deleted
            st.session_state.pop(akey, None)
            active = None
        else:
            live = bool(cfgd.get("live"))

    if active:
        _run_view(uid, active["folder"], active["file"], active["path"], live=live)
    else:
        _paper_form(uid)


def file_dashboard():
    """One strategy file: Start/Stop + live tables. Edit settings only when STOPPED."""
    uid = current_uid()
    active = st.session_state.get("active_strategy")
    # restore from URL if session lost (refresh / other tab)
    if not active:
        qf = str(st.query_params.get("folder", "")).strip()
        qn = str(st.query_params.get("file", "")).strip()
        if qf and qn:
            path = strategy_dir(uid, qf, qn)
            if os.path.exists(os.path.join(path, "config.json")):
                active = {"folder": _safe_name(qf), "file": _safe_name(qn), "path": path}
                st.session_state["active_strategy"] = active
    if not active:
        _set_nav("home")
        st.rerun()
        return

    path = active["path"]
    folder, file_name = active["folder"], active["file"]
    cfg_data = load_strategy_config(path)
    if not cfg_data:
        st.error("Config for this file was not found.")
        if st.button("Back"):
            _set_nav("home")
            st.rerun()
        return

    engine = get_strategy_engine(uid, path)
    if st.session_state.get("smart") and engine.smart is None:
        engine.set_login(
            st.session_state.smart,
            st.session_state.get("creds"),
            st.session_state.get("client_id", ""),
        )

    no_dim()
    _from = st.session_state.get("nav_from", "home")
    if _from not in ("home", "builder"):
        _from = "home"
    top_nav(_from)
    if st.button("← Back to " + ("Strategy Builder" if _from == "builder" else "My Strategies")):
        st.session_state.pop("edit_open", None)
        st.session_state.pop("active_strategy", None)
        _set_nav(_from)
        st.rerun()

    st.title(f"{folder} / {file_name}")
    flash = st.session_state.pop("flash", None)
    if flash:
        st.success(flash)

    # Start / Stop
    is_live_file = bool(cfg_data.get("live"))
    c1, c2, c3, c4, c5 = st.columns([1, 1, 1, 1, 3])
    start_clicked = c1.button("Start", type="primary", use_container_width=True,
                              disabled=engine.running or is_live_file or engine.has_run)
    resume_clicked = c2.button("Resume", use_container_width=True,
                               disabled=engine.running or is_live_file or not engine.has_run,
                               help="Continue after Stop - positions / trades stay as they are")
    if cfg_data.get("live"):
        st.warning("🔴 LIVE file - Start / Exit only from the **Strategy Builder** tab (click the file name in My Strategies). A Live file cannot be deleted.")
        if st.button("➡ Open in Strategy Builder (Start / Resume)", key="open_in_builder"):
            _go_file(folder, {"file": file_name, "path": path, "live": True}, False, "home")
    if c3.button("Stop", use_container_width=True, disabled=not engine.running):
        engine.stop()
        st.rerun()
    if c4.button("Exit", use_container_width=True, disabled=is_live_file,
                 help="Stops the strategy and closes all open positions"):
        n = engine.exit_all("Manual exit (Exit)")
        st.session_state["flash"] = f"Exit: {n} position(s) closed, strategy stopped."
        st.rerun()
    c5.write(f"Status: **{'RUNNING' if engine.running else 'STOPPED'}**")

    # Summary bar
    exchange = cfg_data.get("exchange", "NSE")
    tf_label = cfg_data.get("tf_label", "-")
    capital = cfg_data.get("capital", 0)
    max_open = cfg_data.get("max_open", 5)
    no_limit = cfg_data.get("no_limit", False)
    target_pct = cfg_data.get("target_pct", 1.0)
    items = cfg_data.get("items", [])
    position_amount = cfg_data.get("position_amount", 0)
    _sm = cfg_data.get("size_mode") or "amount"
    size_txt = (f"qty/pos {int(cfg_data.get('position_qty') or 0)}" if _sm == "qty"
                else f"{'equal weight' if _sm == 'equal' else 'amount/pos'} {position_amount:,.0f}")
    st.info(
        f"**{exchange}**  |  {tf_label}  |  capital {capital:,.0f}  |  "
        f"max positions {'no limit' if no_limit else max_open}  |  "
        f"{size_txt}  |  {('target ' + str(target_pct) + '%') if target_pct else 'no target'}  |  "
        f"{'cloud exit ' + str(cfg_data.get('cloud_exit')).replace(',', ' / ') + '  |  ' if cfg_data.get('cloud_exit') else ''}"
        f"stocks {len(items)}"
    )

    if start_clicked or resume_clicked:
        if not items:
            st.error("No stocks in this file. Edit settings and add stocks.")
        elif engine.smart is None and st.session_state.get("smart") is None:
            st.error("Not logged in to Angel One.")
        else:
            interval = cfg_data.get("interval", "FIVE_MINUTE")
            tf_min = cfg_data.get("tf_min", 5)
            cfg = _cfg_from_data(cfg_data)
            smart = engine.smart or st.session_state.smart
            (engine.resume if resume_clicked else engine.start)(smart, cfg, items, exchange, False)
            st.rerun()

    # Edit settings (also while RUNNING) - same panel is used in Strategy Builder
    edit_settings_panel(uid, folder, file_name, path, engine, cfg_data)

    if cfg_data.get("live"):
        st.caption("LIVE file: no delete / reset (real trade record).")

    # Live fragments
    frag = getattr(st, "fragment", None) or st.experimental_fragment
    fast = 1 if engine.running else None
    slow = 3 if engine.running else None

    @frag(run_every=fast)
    def _top():
        live_top(engine, exchange, tf_label)

    @frag(run_every=slow)
    def _mid():
        live_mid(engine)

    @frag(run_every=fast)
    def _pos():
        live_positions(engine)

    @frag(run_every=slow)
    def _bot():
        live_bottom(engine)

    _top()
    _mid()
    _pos()
    _bot()


def main_router():
    """After login: Strategy tab / Paper Trading tab / create file / file page."""
    page = st.session_state.get("page") or str(st.query_params.get("p", "home"))
    if page == "file":
        file_dashboard()
    elif page in ("builder", "paper", "live"):
        builder_page()
        _account_footer(current_uid())
    else:
        strategy_page()
        _account_footer(current_uid())


# ============================== ENTRY ==============================
st.set_page_config(page_title="Live Paper Trading", layout="wide", initial_sidebar_state="collapsed")

if not access_gate():
    st.stop()

uid = current_uid()
_ss = st.session_state

# Keep email in URL so refresh / laptop wake does not ask access again
_em = (_ss.get("access_email") or str(st.query_params.get("e", ""))).strip().lower()
if _em:
    _ss["access_email"] = _em
    _ss["access_granted"] = True
    if st.query_params.get("e") != _em:
        st.query_params["e"] = _em

# Restore Angel session on refresh — do NOT ask API key again.
# 1) dedicated login cache  2) fallback: any engine still holding smart
# Cleared only by Logout button or full app/server restart.
if "smart" not in _ss and not _ss.get("no_autologin") and uid and not is_logged_out(uid):
    cached = load_login(uid)
    if cached and cached.get("smart") is not None:
        _ss.smart = cached["smart"]
        _ss.client_id = cached.get("client_id") or "connected"
        if cached.get("creds"):
            _ss.creds = cached["creds"]
        share_login_to_engines(uid, _ss.smart, _ss.get("creds"), _ss.client_id)
    else:
        reg = _engine_registry()
        with reg["lock"]:
            for k, eng in reg["map"].items():
                if k.startswith(f"{uid}::") and eng.smart is not None:
                    _ss.smart = eng.smart
                    _ss.client_id = eng.client_id or "connected"
                    if eng.creds:
                        _ss.creds = eng.creds
                    save_login(uid, eng.smart, eng.creds, eng.client_id)
                    break

# Restore active strategy + page from URL (refresh keeps you on same file page)
if "active_strategy" not in _ss or not _ss.get("page"):
    _p = str(st.query_params.get("p", "") or "")
    _f = str(st.query_params.get("folder", "") or "")
    _n = str(st.query_params.get("file", "") or "")
    if _p:
        _ss["page"] = _p
    if _p == "file" and _f and _n and uid:
        _path = strategy_dir(uid, _f, _n)
        if os.path.exists(os.path.join(_path, "config.json")):
            _ss["active_strategy"] = {"folder": _f, "file": _n, "path": _path}

# auto-login for owner only (server-saved ANGEL_* secrets)
if "smart" not in _ss and not _ss.get("no_autologin") and uid == OWNER_ID:
    _creds = env_creds()
    if _creds:
        with st.spinner("Angel One login..."):
            _sm, _err = angel_login(*_creds)
        if _sm is not None:
            cid = _creds[1].strip().upper()
            save_login(uid, _sm, _creds, cid)
            share_login_to_engines(uid, _sm, _creds, cid)
            _ss.smart = _sm
            _ss.client_id = cid
            _ss.creds = _creds
            autoresume_all(uid, _sm, _creds, cid)
        else:
            st.warning(f"Auto login failed: {_err}")

if "smart" not in st.session_state:
    login_page()
else:
    # Push login onto any new engines created after login
    if uid and _ss.get("smart"):
        share_login_to_engines(uid, _ss.smart, _ss.get("creds"), _ss.get("client_id", ""))
    main_router()