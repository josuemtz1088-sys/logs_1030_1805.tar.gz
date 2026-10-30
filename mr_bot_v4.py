#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
mr_bot_v4.py — v5.0 Chainlink Trend Follow (Multi-Asset)
=================================================================
Trend-following strategy for Polymarket BTC/ETH/SOL 5-min up/down binary markets.

KEY INSIGHT (v5.0):
  Polymarket resolves using CHAINLINK DATA STREAMS, not Binance spot.
  Mean reversion FAILED (2% win rate over 80 cycles) because:
    1. Binance ≠ Chainlink — different prices at resolution boundaries
    2. Intra-window overreactions on Binance DON'T REVERT on Chainlink
  Trend following on Chainlink data = 98% win rate in backtests.

STRATEGY v5.0:
  1. Record Chainlink "price to beat" at window start (same as Polymarket UI)
  2. Monitor BOTH Chainlink (truth) and Binance (fast) during window
  3. When Chainlink confirms strong directional move → buy WITH the trend
  4. Token price is mid-range (0.55-0.75) but win rate is very high
  5. Hold to expiry — Chainlink direction almost always persists

DATA SOURCES:
  ⛓️ Chainlink on POLYGON — resolution oracle (30s updates, our TRUTH source)
  📊 Binance spot — fast confirmation + order flow signals
  📕 Binance order book — imbalance confirmation
  🕯️ Binance 1-min klines — RSI, momentum, candle patterns

ENTRY FILTERS:
  - Chainlink delta from "price to beat" > MIN_CL_DELTA ($30)
  - Binance direction AGREES with Chainlink
  - Bid/ask imbalance confirms direction
  - Candle momentum supports direction
  - Token price range (entry at 0.50-0.75 for trend follow)
  - Enough time left in window (>60s)
  - ONE position at a time, no re-entry

EXITS:
  - HOLD TO EXPIRY (default — 98% win rate means almost always correct)
  - TP if token reaches 0.90+ (take profit, don't wait for $1 resolution)
  - Emergency sell only if Chainlink REVERSES strongly against us

MULTI-ASSET:
  ASSET=btc → btcusdt, slug btc-updown-5m-
  ASSET=eth → ethusdt, slug eth-updown-5m-
  ASSET=sol → solusdt, slug sol-updown-5m-
"""

import os, sys, ssl, json, time, threading, traceback, requests, urllib.parse, fcntl
import hmac, hashlib, base64
from datetime import datetime, timezone, date
from collections import deque
from typing import Optional, Tuple, Any, List, Dict

import websocket
"""Read-only post-loss guards for CB/FLOW/TW. No trading/order APIs."""
import threading, time
from collections import deque
import requests

class BinancePerpCVD:
    URL = "https://fapi.binance.com/fapi/v1/aggTrades"
    def __init__(self, symbol="BTCUSDT", poll_sec=1.0):
        self.symbol=symbol; self.poll_sec=max(.5,float(poll_sec))
        self.lock=threading.Lock(); self.rows=deque(maxlen=100000)
        self.last_id=None; self.last_ts=0.; self.errors=0; self.started_at=None
        self.stop_event=threading.Event(); self.thread=None
    def start(self):
        if not self.thread or not self.thread.is_alive():
            self.thread=threading.Thread(target=self._run,name="PerpCVD",daemon=True); self.thread.start()
    def _poll(self):
        p={"symbol":self.symbol,"limit":1000}
        if self.last_id is not None: p["fromId"]=self.last_id+1
        r=requests.get(self.URL,params=p,timeout=4); r.raise_for_status(); data=r.json()
        if not isinstance(data,list): raise ValueError("Invalid Futures aggTrades response")
        if self.last_id is None:
            if data:
                self.last_id=max(int(x["a"]) for x in data)
                self.started_at=time.time()
            return
        points=[]
        # Drain multiple pages so a busy second cannot silently lose >1000 aggTrades.
        for page in range(5):
            for x in data:
                aid=int(x["a"])
                if aid<=self.last_id: continue
                ts=int(x["T"])/1000.; q=float(x["q"])
                points.append((ts,-q if bool(x["m"]) else q,aid))
            if len(data)<1000: break
            next_id=max(int(x["a"]) for x in data)+1
            r=requests.get(self.URL,params={"symbol":self.symbol,"limit":1000,"fromId":next_id},timeout=4)
            r.raise_for_status(); data=r.json()
            if not isinstance(data,list): raise ValueError("Invalid Futures aggTrades response")
            if not data: break
        points.sort()
        with self.lock:
            for ts,q,aid in points:
                self.rows.append((ts,q)); self.last_ts=max(self.last_ts,ts)
                self.last_id=max(self.last_id or aid,aid)
    def _run(self):
        while not self.stop_event.is_set():
            t=time.time()
            try: self._poll()
            except Exception: self.errors+=1
            self.stop_event.wait(max(.1,self.poll_sec-(time.time()-t)))
    def cvd(self,seconds=30,now=None):
        now=time.time() if now is None else float(now)
        with self.lock: rows=list(self.rows); last=self.last_ts; started=self.started_at
        if not rows or started is None or now-started<seconds-3 or now-last>3 or rows[0][0]>now-seconds+3: return None
        return sum(q for ts,q in rows if now-seconds<=ts<=now)

def ds_velocity(series,seconds,now=None):
    if not series: return None
    now=time.time() if now is None else float(now)
    pts=sorted((float(t),float(v)) for t,v in series if float(t)<=now)
    if len(pts)<2: return None
    et,ev=pts[-1]; target=et-float(seconds)
    starts=[(t,v) for t,v in pts if t<=target]
    if not starts or now-et>6: return None
    st,sv=starts[-1]
    if target-st>8 or et-st<seconds-1: return None
    return ev-sv

class PostLossGuard:
    def __init__(self,logger=None):
        self.perp=BinancePerpCVD(symbol=BINANCE_SYMBOL); self.logger=logger or (lambda x:None)
        self.hist={k:deque(maxlen=2) for k in ("CB","FLOW","TW")}
        self.lock=threading.Lock()
    def start(self): self.perp.start()
    def evaluate(self,strategy,side,spot_series,slug=None,now=None,ds_series=None):
        name=str(strategy).upper()
        if name not in self.hist: return False,{"reason":"NOT_APPLICABLE"}
        now=time.time() if now is None else float(now)
        d=1 if str(side).upper() in ("UP","UPWARD") else -1
        # vel_15/30/60 son velocidades de Binance spot; TW además usa DS vel_30.
        snap={"ts":now,"slug":slug,"side":str(side).upper(),
              "vel_15s":ds_velocity(spot_series,15,now),
              "vel_30s":ds_velocity(spot_series,30,now),
              "vel_60s":ds_velocity(spot_series,60,now),
              "ds_vel_30s":ds_velocity(ds_series,30,now) if ds_series is not None else None,
              "cvd_perp_30s":self.perp.cvd(30,now)}
        required={"CB":("vel_15s","vel_30s","vel_60s"),
                  "FLOW":("vel_15s","cvd_perp_30s"),
                  "TW":("vel_15s","ds_vel_30s","cvd_perp_30s")}[name]
        missing=[k for k in required if snap[k] is None]
        with self.lock:
            h=self.hist[name]; h.append(snap); prev=h[-2] if len(h)>1 else None
        adv=lambda k,x: x is not None and x*d<0
        if missing: blocked,reason=True,"INSUFFICIENT_DATA"
        elif name=="CB":
            blocked=all(adv(k,snap[k]) for k in required)
            reason="CB_TRIPLE_VELOCITY_ADVERSE" if blocked else "CLEAR"
        elif prev is None or prev.get("slug") != slug or prev.get("side") != str(side).upper() or now-prev["ts"]>6 or now<=prev["ts"]:
            blocked,reason=False,"WAITING_FOR_SECOND_SAMPLE"
        else:
            blocked=all(adv(k,snap[k]) and adv(k,prev[k]) for k in required)
            reason=name+"_PERSISTENT_ADVERSE" if blocked else "CLEAR"
        record={"kind":"POST_LOSS_GUARD","strategy":name,"blocked":blocked,
                "reason":reason,"missing":missing,**snap}
        try: self.logger(record)
        except Exception: pass
        return blocked,record
from eth_account import Account
from py_clob_client_v2.client import ClobClient

try:
    from web3 import Web3
    HAS_WEB3 = True
except ImportError:
    HAS_WEB3 = False
    print("⚠️ web3 not installed — auto-claim disabled")

# Registro en vivo a Google Sheets (tolerante a fallos: si no está
# configurado o falla, el bot sigue operando normalmente).
try:
    from sheets_logger import sheets_logger
except Exception as _e:
    print(f"📊 Sheets: módulo no disponible ({_e}) — registro a Sheets desactivado")
    class _NoSheets:
        enabled = False
        def log_buy(self, *a, **k): pass
        def update_outcome(self, *a, **k): pass
    sheets_logger = _NoSheets()

# ================================================================
#  MULTI-ASSET CONFIG
# ================================================================
ASSET = os.getenv("ASSET", "btc").lower()
ASSET_CONFIG = {
    "btc": {"symbol": "BTCUSDT", "symbol_lower": "btcusdt", "slug_prefix": "btc-updown-5m-",
            "chainlink_default": "1"},
    "eth": {"symbol": "ETHUSDT", "symbol_lower": "ethusdt", "slug_prefix": "eth-updown-5m-",
            "chainlink_default": "0"},
    "sol": {"symbol": "SOLUSDT", "symbol_lower": "solusdt", "slug_prefix": "sol-updown-5m-",
            "chainlink_default": "0"},
}
if ASSET not in ASSET_CONFIG:
    print(f"❌ Unknown ASSET={ASSET}. Use btc/eth/sol"); sys.exit(1)

_AC = ASSET_CONFIG[ASSET]
BINANCE_SYMBOL = _AC["symbol"]
BINANCE_SYMBOL_LOWER = _AC["symbol_lower"]

# ================================================================
#  ENDPOINTS
# ================================================================
WS_URL = os.getenv("WS_URL", "wss://ws-subscriptions-clob.polymarket.com/ws/market")
CLOB_HOST = os.getenv("CLOB_HOST", "https://clob.polymarket.com")
GAMMA_HOST = os.getenv("GAMMA_HOST", "https://gamma-api.polymarket.com")

BINANCE_WS_URL = os.getenv("BINANCE_WS_URL", f"wss://stream.binance.com:9443/ws/{BINANCE_SYMBOL_LOWER}@aggTrade")
BINANCE_REST_PRICE = os.getenv("BINANCE_REST_PRICE", f"https://api.binance.com/api/v3/ticker/price?symbol={BINANCE_SYMBOL}")
BINANCE_DEPTH_WS_URL = os.getenv("BINANCE_DEPTH_WS_URL", f"wss://stream.binance.com:9443/ws/{BINANCE_SYMBOL_LOWER}@depth20@100ms")
BINANCE_DEPTH_REST = os.getenv("BINANCE_DEPTH_REST", f"https://api.binance.com/api/v3/depth?symbol={BINANCE_SYMBOL}&limit=100")
BINANCE_KLINE_WS_URL = f"wss://stream.binance.com:9443/ws/{BINANCE_SYMBOL_LOWER}@kline_1m"
BINANCE_KLINE_REST = f"https://api.binance.com/api/v3/klines?symbol={BINANCE_SYMBOL}"

BASE_SLUG_PREFIX = os.getenv("BASE_SLUG_PREFIX", _AC["slug_prefix"])
WINDOW_SECONDS = int(os.getenv("WINDOW_SECONDS", "300"))
CHAIN_ID = int(os.getenv("CHAIN_ID", "137"))

# ================================================================
#  ENV / FLAGS
# ================================================================
DEBUG_RAW = os.getenv("DEBUG_RAW", "0") == "1"
DRY_RUN = os.getenv("DRY_RUN", "1") in ("1", "true", "TRUE", "on", "ON")

# ANTI-SLIPPAGE (2026-06-19): precio máximo de ask al que se permite EJECUTAR
# una compra. Si entre la aprobación del filtro y el envío de la orden el ask
# sube por encima de este valor, la compra se aborta. Evita comprar a $0.99
# (zona económicamente perdedora) cuando el filtro aprobó a $0.98.
# Default 0.985 = permite hasta justo antes de $0.99. Pon 0 para desactivar.
SLIPPAGE_GUARD_MAX = float(os.getenv("SLIPPAGE_GUARD_MAX", "0.985"))

ORDER_SIGNATURE_TYPE = int(os.getenv("SIGNATURE_TYPE", os.getenv("ORDER_SIGNATURE_TYPE", "2")))
BALANCE_SIG_AUTODETECT = os.getenv("BALANCE_SIG_AUTODETECT", "1") in ("1", "true", "TRUE", "on", "ON")
BALANCE_SIG_TRY = os.getenv("BALANCE_SIG_TRY", "0,1,2").strip()
USDC_DECIMALS = int(os.getenv("USDC_DECIMALS", "6"))
BALANCE_IS_BASE_UNITS = os.getenv("BALANCE_IS_BASE_UNITS", "auto").lower()
BALANCE_EVERY_SEC = float(os.getenv("BALANCE_EVERY_SEC", "15"))
BALANCE_FALLBACK_USDC = float(os.getenv("BALANCE_FALLBACK_USDC", "10.0"))
BALANCE_PRINT = os.getenv("BALANCE_PRINT", "1") in ("1", "true", "TRUE", "on", "ON")

# ================================================================
#  SIZING — Progressive Martingale-Lite
# ================================================================
USE_BALANCE_PCT = float(os.getenv("USE_BALANCE_PCT", "0.15"))
MIN_TRADE_USDC = float(os.getenv("MIN_TRADE_USDC", "1.00"))
MAX_TRADE_USDC     = float(os.getenv("MAX_TRADE_USDC",     "999.0"))  # cap absoluto; el real es MAX_TRADE_BAL_PCT × balance # sin cap fijo — se usa % del balance
MAX_TRADE_BAL_PCT  = float(os.getenv("MAX_TRADE_BAL_PCT",  "0.35"))  # máx 35% del balance por trade
# El cap real es: min(MAX_TRADE_USDC, balance × MAX_TRADE_BAL_PCT)
# Con 35%, el peor caso (mart 3× + VERY HIGH 2×) = base×6 ≈ 34% del balance → siempre sobrevivible

# ── MODO SALDO TOTAL (2026-10-15) ────────────────────────────────────────
# Cuando FULL_BALANCE_MODE=1 el bot apuesta el saldo disponible × FULL_BAL_PCT
# hasta un tope fijo BET_HARD_CAP. Plan: rampa usando el saldo total y, al
# superar el tope, apuesta fija = BET_HARD_CAP para siempre, sin tocar el env.
# Se mantiene el bloqueo por confianza (conf==0) como filtro de calidad, pero
# se omiten los multiplicadores que REDUCEN el tamaño (confianza<1 y book_risk)
# porque la intención es usar el saldo completo. Con FULL_BALANCE_MODE=0 todo
# se comporta como antes.
FULL_BALANCE_MODE = os.getenv("FULL_BALANCE_MODE", "0") == "1"
FULL_BAL_PCT      = float(os.getenv("FULL_BAL_PCT", "0.98"))   # fracción del saldo a usar (deja colchón)
BET_HARD_CAP      = float(os.getenv("BET_HARD_CAP", "1000.0")) # tope fijo de apuesta

MAX_ORDERS_PER_MARKET = int(os.getenv("MAX_ORDERS_PER_MARKET", "1"))  # 1 compra por ciclo
ORDER_COOLDOWN_SEC = float(os.getenv("ORDER_COOLDOWN_SEC", "60"))

# Progressive sizing: base $5, +$5 per consecutive loss, reset on win
PROGRESSIVE_SIZING = os.getenv("PROGRESSIVE_SIZING", "1") == "1"
PROG_BASE_USDC = float(os.getenv("PROG_BASE_USDC", "2.00"))    # Base bet size inicial
BAL_SCALE_THRESH   = float(os.getenv("BAL_SCALE_THRESH",   "0.30"))  # escalar al +30% balance
BAL_SCALE_BASE_PCT = float(os.getenv("BAL_SCALE_BASE_PCT", "0.30"))  # base sube 30% (= ratio constante)
BAL_SCALE_INIT     = float(os.getenv("BAL_SCALE_INIT",     "35.0"))  # balance de referencia inicial
PROG_STEP_USDC = float(os.getenv("PROG_STEP_USDC", "5.00"))    # Increment per loss
PROG_MAX_USDC = float(os.getenv("PROG_MAX_USDC", "25.00"))     # Safety cap (5 losses max)
PROG_MAX_LOSSES = int(os.getenv("PROG_MAX_LOSSES", "2"))        # Pause after N consecutive losses
PROG_PAUSE_SEC = float(os.getenv("PROG_PAUSE_SEC", "3600"))     # Pause duration (1 hour)
MARTINGALE_MULT  = float(os.getenv("MARTINGALE_MULT",    "3.0")) # 3× tras primera pérdida
MARTINGALE_LIMIT = int(os.getenv("MARTINGALE_LIMIT",     "2"))   # max pérdidas consecutivas

# ================================================================
#  CONFIDENCE-BASED SIZING — v5.5
#  El tamaño de la apuesta escala según el nivel de confianza
#  de las señales detectadas. Tres niveles:
#    HIGH   (≥80%) → multiplica el bet base por CONF_HIGH_MULT
#    MEDIUM (≥55%) → multiplica por CONF_MED_MULT
#    LOW    (<55%) → multiplica por CONF_LOW_MULT (puede ser <1 para reducir)
#
#  Para TF: confianza = función de CL delta y número de confirmaciones
#  Para PR: confianza = función del total_reversal_score normalizado
# ================================================================
CONF_SIZING_ENABLED   = os.getenv("CONF_SIZING_ENABLED", "1") == "1"
# ── 5 niveles de confianza — v5.6 ────────────────────────────────
# Multiplicadores sobre PROG_BASE_USDC. Con base=$4:
#   VERY_HIGH → $4 × 2.0 = $8.00  (máx)
#   HIGH      → $4 × 1.625 = $6.50
#   MEDIUM    → $4 × 1.25  = $5.00
#   ACCEPTABLE→ $4 × 0.875 = $3.50
#   LOW       → $4 × 0.625 = $2.50 (mín)
CONF_VERYHIGH_MULT    = float(os.getenv("CONF_VERYHIGH_MULT",    "2.000"))  # VERY HIGH → 2×
CONF_HIGH_MULT        = float(os.getenv("CONF_HIGH_MULT",        "1.625"))  # HIGH      → 1.625×
CONF_MED_MULT         = float(os.getenv("CONF_MED_MULT",         "1.250"))  # MEDIUM    → 1.25×
CONF_ACCEPT_MULT      = float(os.getenv("CONF_ACCEPT_MULT",      "0.875"))  # ACCEPTABLE→ 0.875×
CONF_LOW_MULT         = float(os.getenv("CONF_LOW_MULT",         "0.625"))  # LOW       → 0.625×
# Umbrales
CONF_VERYHIGH_THRESHOLD = float(os.getenv("CONF_VERYHIGH_THRESHOLD", "0.82"))
CONF_HIGH_THRESHOLD     = float(os.getenv("CONF_HIGH_THRESHOLD",     "0.65"))
CONF_MED_THRESHOLD      = float(os.getenv("CONF_MED_THRESHOLD",      "0.48"))
CONF_ACCEPT_THRESHOLD   = float(os.getenv("CONF_ACCEPT_THRESHOLD",   "0.32"))

MIN_BOOK_LIQ_TOP3 = float(os.getenv("MIN_BOOK_LIQ_TOP3", "60"))
MAX_SPREAD = float(os.getenv("MAX_SPREAD", "0.15"))
DIAG_EVERY_SEC = float(os.getenv("DIAG_EVERY_SEC", "3"))
WS_SILENT_RECONNECT_SEC = float(os.getenv("WS_SILENT_RECONNECT_SEC", "15"))
WS_OPEN_GRACE_SEC = float(os.getenv("WS_OPEN_GRACE_SEC", "8"))
WS_PING_TEXT_EVERY_SEC = float(os.getenv("WS_PING_TEXT_EVERY_SEC", "10"))
PRICE_EPS_TICKS = int(os.getenv("PRICE_EPS_TICKS", "1"))
REQUIRE_BOOK_FOR_TRADE = os.getenv("REQUIRE_BOOK_FOR_TRADE", "1") == "1"
SKIP_DUMMY_BOOK = os.getenv("SKIP_DUMMY_BOOK", "1") in ("1", "true", "TRUE", "on", "ON")
MARKET_SCAN_LOOKAHEAD = int(os.getenv("MARKET_SCAN_LOOKAHEAD", "8"))
MARKET_SCAN_LOOKBACK = int(os.getenv("MARKET_SCAN_LOOKBACK", "4"))

TELEGRAM_BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID", "").strip()

SELL_GRACE_SEC = float(os.getenv("SELL_GRACE_SEC", "10"))
SELL_RETRY_COOLDOWN_SEC = float(os.getenv("SELL_RETRY_COOLDOWN_SEC", "3"))
SELL_MAX_RETRIES = int(os.getenv("SELL_MAX_RETRIES", "50"))
SELL_USE_LIMIT_FALLBACK = os.getenv("SELL_USE_LIMIT_FALLBACK", "1") == "1"
SELL_LIMIT_DISCOUNT = float(os.getenv("SELL_LIMIT_DISCOUNT", "0.02"))
SELL_EMERGENCY_SEC = float(os.getenv("SELL_EMERGENCY_SEC", "30"))

CYCLE_LOG_FILE = os.getenv("CYCLE_LOG_FILE", "cycle_log_mr.txt")
TRADES_LOG_FILE = os.getenv("TRADES_LOG_FILE", "trades_log.jsonl")
SIGNALS_LOG_FILE = os.getenv("SIGNALS_LOG_FILE", "signals_log.jsonl")

# NUEVO 2026-07-03: registro del MOTIVO cuando una señal aprobada NO se ejecuta.
# El signals_log registra la aprobación (FAST_TRACK_BUY), pero no por qué la
# compra a veces no ocurre. Este helper escribe una línea con decision=
# "NOT_EXECUTED" y el motivo exacto (exec_status), para diagnóstico posterior.
def log_exec_status(slug, side, status, detail="", extra=None):
    """Registra en signals_log por qué una señal aprobada no se ejecutó."""
    if os.getenv("LOG_ALL_SIGNALS", "1") != "1":
        return
    try:
        entry = {
            "ts": time.time(),
            "slug": slug or (S.slug if 'S' in globals() else ""),
            "side": side,
            "decision": "NOT_EXECUTED",
            "exec_status": status,     # ej: "BALANCE_LOW", "WAIT_AFTER_LOSS", etc.
            "exec_detail": detail,
            "reject_category": status, # categoría uniforme para análisis (= exec_status)
        }
        if extra:
            entry.update(extra)
        with open(SIGNALS_LOG_FILE, "a") as f:
            f.write(json.dumps(entry) + "\n")
    except Exception:
        pass

# ================================================================
#  MEAN REVERSION PARAMETERS
# ================================================================
MIN_OVERREACTION = float(os.getenv("MIN_OVERREACTION", "0.0008"))
IDEAL_OVERREACTION = float(os.getenv("IDEAL_OVERREACTION", "0.0015"))
MAX_ENTRY_PRICE = float(os.getenv("MAX_ENTRY_PRICE", "0.20"))
MIN_ENTRY_PRICE = float(os.getenv("MIN_ENTRY_PRICE", "0.08"))
NO_ENTRY_BEFORE_SEC = float(os.getenv("NO_ENTRY_BEFORE_SEC", "180"))
NO_ENTRY_AFTER_LEFT = float(os.getenv("NO_ENTRY_AFTER_LEFT", "300"))

REQUIRE_PULLBACK = os.getenv("REQUIRE_PULLBACK", "0") == "1"
MIN_PULLBACK_PCT = float(os.getenv("MIN_PULLBACK_PCT", "0.30"))
MIN_PEAK_MOVE = float(os.getenv("MIN_PEAK_MOVE", "0.0012"))

TP_PCT = float(os.getenv("TP_PCT", "0.25"))
USE_FIXED_SL = os.getenv("USE_FIXED_SL", "0") == "1"
SL_DELTA = float(os.getenv("SL_DELTA", "0.25"))
TRAIL_ACTIVATE_PCT = float(os.getenv("TRAIL_ACTIVATE_PCT", "0.40"))
TRAIL_OFFSET = float(os.getenv("TRAIL_OFFSET", "0.03"))

MAX_HOLD_SEC = int(os.getenv("MAX_HOLD_SEC", "270"))
EXIT_NEAR_END_SEC = int(os.getenv("EXIT_NEAR_END_SEC", "30"))

MIN_BALANCE_TO_TRADE = float(os.getenv("MIN_BALANCE_TO_TRADE", "2.0"))
MAX_ADVERSE_MOVE = float(os.getenv("MAX_ADVERSE_MOVE", "0.0020"))

# Macro trend
USE_MACRO_TREND_FILTER = os.getenv("USE_MACRO_TREND_FILTER", "0") == "1"
MACRO_TREND_WINDOWS = int(os.getenv("MACRO_TREND_WINDOWS", "3"))
MACRO_TREND_MIN_MOVE = float(os.getenv("MACRO_TREND_MIN_MOVE", "0.0003"))
# v5.10: Extended whipsaw detection — wider window than 3-window alternation check
WHIPSAW_LOOKBACK = int(os.getenv("WHIPSAW_LOOKBACK", "6"))
WHIPSAW_RATIO = float(os.getenv("WHIPSAW_RATIO", "0.60"))
# v5.10: EAT-FLOW — net order consumption rate as entry confirmation
EAT_FLOW_WINDOW_SEC = int(os.getenv("EAT_FLOW_WINDOW_SEC", "10"))
EAT_FLOW_MIN_RATE = float(os.getenv("EAT_FLOW_MIN_RATE", "0"))  # 0=disabled, >0=require min eat rate confirming direction
KLINE_PREFILL_COUNT = int(os.getenv("KLINE_PREFILL_COUNT", "6"))
KLINE_INTERVAL = os.getenv("KLINE_INTERVAL", "")

# Binance depth
USE_BINANCE_DEPTH = os.getenv("USE_BINANCE_DEPTH", "1") == "1"
WALL_MIN_BTC = float(os.getenv("WALL_MIN_BTC", "3.0"))
DEPTH_RANGE_USD = float(os.getenv("DEPTH_RANGE_USD", "200"))
MIN_BOOK_SCORE = float(os.getenv("MIN_BOOK_SCORE", "25"))
DEPTH_REST_REFRESH_SEC = float(os.getenv("DEPTH_REST_REFRESH_SEC", "5"))

# Candle analysis
USE_CANDLE_ANALYSIS = os.getenv("USE_CANDLE_ANALYSIS", "1") == "1"
CANDLE_BUFFER_SIZE = int(os.getenv("CANDLE_BUFFER_SIZE", "30"))
CANDLE_REJECTION_RATIO = float(os.getenv("CANDLE_REJECTION_RATIO", "2.0"))
CANDLE_DOJI_BODY_PCT = float(os.getenv("CANDLE_DOJI_BODY_PCT", "0.10"))
CANDLE_STRONG_BODY_PCT = float(os.getenv("CANDLE_STRONG_BODY_PCT", "0.70"))
CANDLE_TREND_LOOKBACK = int(os.getenv("CANDLE_TREND_LOOKBACK", "5"))
CANDLE_BLOCK_ON_REJECTION = os.getenv("CANDLE_BLOCK_ON_REJECTION", "0") == "1"
CANDLE_BLOCK_ON_INDECISION = os.getenv("CANDLE_BLOCK_ON_INDECISION", "0") == "1"

# Bid/ask imbalance filter for entry
IMB_UP_MIN = float(os.getenv("IMB_UP_MIN", "0.4"))
IMB_DN_MAX = float(os.getenv("IMB_DN_MAX", "2.5"))

# Chainlink — NOW ON POLYGON (30s updates, same as Polymarket oracle!)
CHAINLINK_ENABLED = os.getenv("USE_CHAINLINK_PRICE", "1") == "1"  # v5.0: always ON
CHAINLINK_POLL_SEC = float(os.getenv("CHAINLINK_POLL_SEC", "10"))  # Poll faster for fresher data
# Polygon Chainlink aggregators (BTC, ETH, SOL)
CHAINLINK_POLYGON_CONTRACTS = {
    "btc": "0xc907E116054Ad103354f2D350FD2514433D57F6f",  # BTC/USD on Polygon
    "eth": "0xF9680D99D6C9589e2a93a78A04A279e509205945",  # ETH/USD on Polygon
    "sol": "0x4b531A318B0e44B549F3b2f824721b3D0d51930A",   # SOL/USD on Polygon (verify)
}
CHAINLINK_CONTRACT = os.getenv("CHAINLINK_CONTRACT", CHAINLINK_POLYGON_CONTRACTS.get(ASSET, "0xc907E116054Ad103354f2D350FD2514433D57F6f"))
CHAINLINK_RPCS = [
    os.getenv("POLYGON_RPC", "https://polygon-bor.publicnode.com"),
    "https://polygon.drpc.org",
    "https://1rpc.io/matic",
]

# v5.0: Trend follow parameters
MIN_CL_DELTA_USD = float(os.getenv("MIN_CL_DELTA_USD", "20"))  # Min Chainlink delta to enter
CL_CONFIRM_COUNT = int(os.getenv("CL_CONFIRM_COUNT", "2"))      # Need N consecutive CL reads confirming direction
TF_MAX_ENTRY_PRICE = float(os.getenv("TF_MAX_ENTRY_PRICE", "0.80"))  # Trend follow: we buy winning-direction token
TF_MIN_ENTRY_PRICE = float(os.getenv("TF_MIN_ENTRY_PRICE", "0.65"))  # v5.9: subido de 0.50 → token barato = mercado no confirma
TF_TP_PRICE = float(os.getenv("TF_TP_PRICE", "0.93"))          # v5.8: Take profit if token > 0.93
TF_EMERGENCY_CL_REVERSE_USD = float(os.getenv("TF_EMERGENCY_CL_REVERSE_USD", "50"))  # CL reversed vs our entry → bail
TF_SL_PCT = float(os.getenv("TF_SL_PCT", "0.40"))            # v5.8: Stop-loss — cortar si token cae X% desde entry
TF_SL_GRACE_SEC = float(os.getenv("TF_SL_GRACE_SEC", "90"))  # v5.8: Gracia antes de activar SL (evitar fake-outs)
TF_MIN_WIN_CHG = float(os.getenv("TF_MIN_WIN_CHG", "0.0008"))  # v5.9: BTC debe haberse movido >= 0.08% del open para entrar

# v5.9: PTB Shift Mode — captura repricing lag cuando PTB cambia mid-cycle
PTB_SHIFT_ENABLED      = os.getenv("PTB_SHIFT_ENABLED", "1") == "1"
PTB_SHIFT_MIN_DIFF     = float(os.getenv("PTB_SHIFT_MIN_DIFF",     "20"))   # PTB debe moverse >= $20 para activar
PTB_SHIFT_WINDOW_SEC   = float(os.getenv("PTB_SHIFT_WINDOW_SEC",   "120"))  # edge válido por 120s después del shift
PTB_SHIFT_FAST_ENTRY   = float(os.getenv("PTB_SHIFT_FAST_ENTRY",   "30"))   # NO_ENTRY_BEFORE_SEC reducido a 30s
PTB_SHIFT_TP_PRICE     = float(os.getenv("PTB_SHIFT_TP_PRICE",     "0.85")) # TP más bajo — repricing es rápido
PTB_SHIFT_POLL_SEC     = float(os.getenv("PTB_SHIFT_POLL_SEC",     "10"))   # cada cuánto buscar PTB override mid-cycle

# ================================================================
#  v5.9: STINK BID MODE — "Moon Dev" strategy
#  Coloca limit BUY a precio bajo en AMBOS lados (UP y DN).
#  Si un flash crash llena una, cancela la otra y toma profit.
#  Riesgo: $STINK_BID_USDC por ciclo. Ganancia: hasta 30x.
# ================================================================
USE_STINK_BID          = os.getenv("USE_STINK_BID", "0") == "1"
STINK_BID_PRICE        = float(os.getenv("STINK_BID_PRICE",      "0.03"))  # precio del limit bid
STINK_BID_USDC         = float(os.getenv("STINK_BID_USDC",       "1.00"))  # USDC por lado (total = 2×)
STINK_TP_PRICE         = float(os.getenv("STINK_TP_PRICE",       "0.40"))  # TP para vender si sube
STINK_EMERGENCY_SEC    = float(os.getenv("STINK_EMERGENCY_SEC",  "30"))    # emergency exit X sec antes del fin
STINK_POLL_SEC         = float(os.getenv("STINK_POLL_SEC",       "3"))     # cada cuánto revisar fills
STINK_HOLD_TO_EXPIRY   = os.getenv("STINK_HOLD_TO_EXPIRY", "0") == "1"    # si True, no TP — espera resolución
STINK_CANCEL_AFTER_SEC = float(os.getenv("STINK_CANCEL_AFTER_SEC", "450")) # cancelar bids no llenados después de 7.5min

# v5.9: Trading hours filter — solo operar durante golden hours
# Formato: "HH-HH,HH-HH" en UTC. Vacío = 24/7.
# Golden hours de @0xbobaaa: 09:00 y 23:00 UTC (open/close de mercados)
# Ejemplo: "08-11,22-01" = 08:00-11:00 y 22:00-01:00 UTC
TRADING_HOURS_UTC = os.getenv("TRADING_HOURS_UTC", "")  # vacío = sin restricción

USE_TREND_FOLLOW = os.getenv("USE_TREND_FOLLOW", "1") == "1"    # v5.0 mode
# Legacy MR mode (can be toggled back)
USE_MEAN_REVERSION = os.getenv("USE_MEAN_REVERSION", "0") == "1"

# ================================================================
#  v5.2: PEAK REVERSION MODE
#  Buy the cheap token at maximum divergence from PTB, sell on reversion.
#  Entry: spot diverges >= MIN_PEAK_DIVERGENCE_USD from PTB, token ask <= PR_MAX_ENTRY_PRICE
#  Exit:  sell token when it recovers PR_TP_PCT (e.g. 40%) from entry price
#         OR when spot reverts PR_REVERT_PCT (e.g. 60%) back toward PTB
#         OR emergency: divergence keeps growing past PR_MAX_DIVERGENCE_USD
# ================================================================
USE_PEAK_REVERSION = os.getenv("USE_PEAK_REVERSION", "0") == "1"

# ================================================================
#  v5.13: WHALE ACCUMULATION MODE
#  Buy BOTH sides early (split), then reinforce winning side as CL confirms.
#  Phase 1 (60-120s):  Split buy — UP + DN at ~50¢
#  Phase 2 (150-240s): Reinforce winner when CL delta ≥ threshold
#  Phase 3 (250-280s): Final push with strong CL confirmation
# ================================================================
USE_WHALE_ACCUM = os.getenv("USE_WHALE_ACCUM", "0") == "1"
WHALE_BUDGET         = float(os.getenv("WHALE_BUDGET",         "30"))
WHALE_PHASE1_PCT     = float(os.getenv("WHALE_PHASE1_PCT",     "0.65"))
WHALE_PHASE2_PCT     = float(os.getenv("WHALE_PHASE2_PCT",     "0.20"))
WHALE_PHASE3_PCT     = float(os.getenv("WHALE_PHASE3_PCT",     "0.15"))
WHALE_P1_START       = int(os.getenv("WHALE_P1_START",         "60"))
WHALE_P1_END         = int(os.getenv("WHALE_P1_END",           "120"))
WHALE_P2_START       = int(os.getenv("WHALE_P2_START",         "150"))
WHALE_P2_END         = int(os.getenv("WHALE_P2_END",           "240"))
WHALE_P3_START       = int(os.getenv("WHALE_P3_START",         "250"))
WHALE_P3_END         = int(os.getenv("WHALE_P3_END",           "280"))
WHALE_P2_CL_DELTA    = float(os.getenv("WHALE_P2_CL_DELTA",   "30"))
WHALE_P3_CL_DELTA    = float(os.getenv("WHALE_P3_CL_DELTA",   "60"))
WHALE_P1_MAX_PRICE   = float(os.getenv("WHALE_P1_MAX_PRICE",  "0.60"))
WHALE_P2_MAX_PRICE   = float(os.getenv("WHALE_P2_MAX_PRICE",  "0.75"))
WHALE_P3_MAX_PRICE   = float(os.getenv("WHALE_P3_MAX_PRICE",  "0.90"))
WHALE_MAX_CHAIN_AGE  = float(os.getenv("WHALE_MAX_CHAIN_AGE",  "18"))
WHALE_SHARES         = float(os.getenv("WHALE_SHARES",         "30"))  # fixed shares per order (like the whale)

# ================================================================
#  v5.15: MOMENTUM STRADDLE — Lean into CL direction + hedge opposite
#  Buys MOMENTUM_RATIO:1 on CL side vs hedge side.
#  Example: ratio=2, shares=20 → 20sh momentum + 10sh hedge per round.
# ================================================================
USE_COPY_TRADING     = os.getenv("USE_COPY_TRADING", "0") == "1"
STRADDLE_SHARES      = float(os.getenv("STRADDLE_SHARES", "20"))        # momentum side shares per round
STRADDLE_RATIO       = float(os.getenv("STRADDLE_RATIO", "2"))          # momentum:hedge ratio (2 = 20:10)
STRADDLE_INTERVAL    = float(os.getenv("STRADDLE_INTERVAL", "15"))      # buy every N seconds
STRADDLE_START_SEC   = float(os.getenv("STRADDLE_START_SEC", "30"))     # start buying at Ns elapsed
STRADDLE_END_SEC     = float(os.getenv("STRADDLE_END_SEC", "270"))      # stop buying at Ns elapsed
STRADDLE_MAX_BUDGET  = float(os.getenv("STRADDLE_MAX_BUDGET", "100"))   # max total $ per window
STRADDLE_MAX_PRICE   = float(os.getenv("STRADDLE_MAX_PRICE", "0.90"))   # don't buy single side > 90¢
STRADDLE_TP_USD      = float(os.getenv("STRADDLE_TP_USD", "40"))        # take profit at $40 profit → sell ALL
STRADDLE_MIN_CL      = float(os.getenv("STRADDLE_MIN_CL", "10"))       # min CL delta to pick direction

# ================================================================
#  v5.16: ASYMMETRIC TIMING — Phase 1 momentum + Phase 2 conditional hedge
#  Phase 1: buy momentum side only until N shares accumulated OR max time
#  Phase 2: only buy hedge if opposite side drops BELOW threshold (cheap hedge)
#  This limits loss when CL wrong, boosts profit when CL right.
# ================================================================
STRADDLE_ASYMMETRIC       = os.getenv("STRADDLE_ASYMMETRIC", "0") == "1"   # enable asymmetric mode
STRADDLE_PHASE1_SHARES    = float(os.getenv("STRADDLE_PHASE1_SHARES", "80"))  # target shares in phase 1
STRADDLE_PHASE1_MAX_SEC   = float(os.getenv("STRADDLE_PHASE1_MAX_SEC", "120"))# max time in phase 1 (sec)
STRADDLE_HEDGE_MAX_PRICE  = float(os.getenv("STRADDLE_HEDGE_MAX_PRICE", "0.30")) # only buy hedge ≤ this
STRADDLE_HEDGE_SHARES     = float(os.getenv("STRADDLE_HEDGE_SHARES", "20"))   # shares per hedge round

# ================================================================
#  v5.17: MERGE PAIRS — Convert UP+DN pairs → USDC instantly via CTF
#  When avg combined cost < 1.00, merge = profit realized immediately.
#  Replicates the "Combinar" strategy observed from top traders.
# ================================================================
STRADDLE_MERGE_ENABLED    = os.getenv("STRADDLE_MERGE_ENABLED", "1") == "1"    # enable merge
STRADDLE_MERGE_MIN_PAIRS  = float(os.getenv("STRADDLE_MERGE_MIN_PAIRS", "20")) # min pairs to trigger merge
STRADDLE_MERGE_MAX_COMBINED = float(os.getenv("STRADDLE_MERGE_MAX_COMBINED", "0.98")) # only merge if avg combined ≤ this (profit ≥ 2%)

# ================================================================
#  v5.18 PATCH 3: Anti-piramidación
#  MAX_SAME_SIDE: límite duro de rondas consecutivas en el mismo lado.
#  CL_STABILITY_SEC: ventana para detectar CL Δ inestable (sign flips).
#  VETO_ON_CANDLE: 1=bloquear rondas R2+ si forming candle contradice momentum.
# ================================================================
STRADDLE_MAX_SAME_SIDE      = int(os.getenv("STRADDLE_MAX_SAME_SIDE", "2"))
STRADDLE_CL_STABILITY_SEC   = float(os.getenv("STRADDLE_CL_STABILITY_SEC", "45"))
STRADDLE_VETO_ON_CANDLE     = os.getenv("STRADDLE_VETO_ON_CANDLE", "1") == "1"

# ================================================================
#  v5.18 PATCH 4: Merge dinámico (profit tras gas)
#  MERGE_GAS_COST_USD: estimación de costo de gas por tx de merge (MATIC × precio).
#  MERGE_MIN_NET_PROFIT: profit mínimo NET (después de restar gas) para ejecutar.
# ================================================================
STRADDLE_MERGE_GAS_COST_USD     = float(os.getenv("STRADDLE_MERGE_GAS_COST_USD", "0.02"))
STRADDLE_MERGE_MIN_NET_PROFIT   = float(os.getenv("STRADDLE_MERGE_MIN_NET_PROFIT", "0.50"))

# ================================================================
#  v5.18 HOTFIX PATCH 1: Drift-sync resistente a lag RPC
#  POST_BUY_COOLDOWN_SEC: desactiva drift-sync durante N segundos tras un BUY
#                        (la blockchain tarda 2-5s en propagar balance al RPC).
#  LARGE_DRIFT_CONFIRMATIONS: N ticks consecutivos con large drift antes de actuar.
#                             Filtra falsos positivos por lag transitorio del RPC.
# ================================================================
STRADDLE_POST_BUY_COOLDOWN_SEC   = float(os.getenv("STRADDLE_POST_BUY_COOLDOWN_SEC", "15"))
STRADDLE_LARGE_DRIFT_CONFIRMATIONS = int(os.getenv("STRADDLE_LARGE_DRIFT_CONFIRMATIONS", "2"))

# Entry thresholds
PR_MIN_PEAK_DIVERGENCE_USD = float(os.getenv("PR_MIN_PEAK_DIVERGENCE_USD", "30"))  # min $ move from PTB to consider entry
PR_MAX_ENTRY_PRICE         = float(os.getenv("PR_MAX_ENTRY_PRICE",         "0.40")) # token must be cheap (e.g. ≤$0.25)
PR_MIN_ENTRY_PRICE         = float(os.getenv("PR_MIN_ENTRY_PRICE",         "0.05")) # floor — avoid near-zero tokens
PR_MAX_DIVERGENCE_USD      = float(os.getenv("PR_MAX_DIVERGENCE_USD",      "80"))   # above this → trend too strong, skip
PR_CONFIRM_REVERSAL_PCT    = float(os.getenv("PR_CONFIRM_REVERSAL_PCT",    "0.12")) # spot must have pulled back ≥8% of peak before buying
PR_MIN_ELAPSED_SEC         = float(os.getenv("PR_MIN_ELAPSED_SEC",         "45"))   # wait at least N seconds into window

# Exit thresholds
PR_TP_PCT                  = float(os.getenv("PR_TP_PCT",                  "0.40")) # target: token +40% from entry price
PR_TP_DELTA                = float(os.getenv("PR_TP_DELTA",                "0.99")) # or token reaches this absolute price
PR_REVERT_PCT              = float(os.getenv("PR_REVERT_PCT",              "0.60")) # sell if spot reverted 60% of the peak move
PR_TRAIL_ACTIVATE_PCT      = float(os.getenv("PR_TRAIL_ACTIVATE_PCT",      "0.25")) # activate trail after +25%
PR_TRAIL_OFFSET            = float(os.getenv("PR_TRAIL_OFFSET",            "0.04")) # trail steps back 4 ticks from peak
PR_EMERGENCY_GROW_PCT      = float(os.getenv("PR_EMERGENCY_GROW_PCT",      "0.30")) # bail if divergence keeps growing 30% past entry divergence

# Daily risk caps
DAILY_LOSS_LIMIT_USDC = float(os.getenv("DAILY_LOSS_LIMIT_USDC", "3.0"))
DAILY_PROFIT_TARGET_USDC = float(os.getenv("DAILY_PROFIT_TARGET_USDC", "0"))
LOSS_COOLDOWN_SEC = float(os.getenv("LOSS_COOLDOWN_SEC", "7200"))

# On-chain
# v2 MIGRATION (2026-04-28): contratos actualizados a V2
# V1 contratos (ya inactivos):
#   CTF_EXCHANGE_V1     = 0x4bFb41d5B3570DeFd03C39a9A4D8dE6Bd8B8982E
#   NEG_RISK_V1         = 0xC5d563A36AE78145C45a50134d48A1215220f80a
#   USDC_E              = 0x2791Bca1f2de4661ED88A30C99A7a9449Aa84174 (deprecated colateral)
CONDITIONAL_TOKENS_ADDR = "0x4D97DCd97eC945f40cF65F87097ACe5EA0476045"  # CTF (sin cambio)
USDC_E_LEGACY = "0x2791Bca1f2de4661ED88A30C99A7a9449Aa84174"            # USDC.e (legacy, ya no es colateral)
# v2 MIGRATION: pUSD es el nuevo colateral. Lectura del balance va aquí ahora.
PUSD_ADDR = os.getenv("PUSD_ADDR", "0xC011a7E12a19f7B1f670d46F03B03f3342E82DFB")  # pUSD proxy
USDC_POLYGON = PUSD_ADDR  # CRITICAL: el bot lee USDC_POLYGON como balance source — apuntar a pUSD
CTF_EXCHANGE_ADDR = "0xE111180000d2663C0091e4f400237545B87B996B"        # V2
NEG_RISK_CTF_EXCHANGE = "0xe2222d279d744050d28e00520010520000310F59"    # V2
NEG_RISK_ADAPTER = "0xd91E80cF2E7be2e162c6513ceD06f1dD0dA35296"          # sin cambio
COLLATERAL_ONRAMP = "0x93070a847efEf7F70739046A929D47a521F5B8ee"         # nuevo: USDC.e → pUSD wrap
EXCHANGE_CONTRACTS = [CTF_EXCHANGE_ADDR, NEG_RISK_CTF_EXCHANGE, NEG_RISK_ADAPTER]
POLYGON_RPC = os.getenv("POLYGON_RPC", "https://polygon-bor.publicnode.com")
AUTO_CLAIM_ENABLED = os.getenv("AUTO_CLAIM_ENABLED", "1") == "1"
AUTO_APPROVE_ENABLED = os.getenv("AUTO_APPROVE_ENABLED", "1") == "1"

API_CREDS = None
SIGNER_ADDRESS = None
FUNDER_ADDRESS = None


# ================================================================
#  STRUCTURED TRADE LOG
# ================================================================
def log_trade(action, side, price, size, usdc, reason, pnl=None):
    """Append a JSON line to trades_log.jsonl."""
    try:
        btc_price = spot_tracker.latest()
        win_chg = spot_tracker.change_since_window_start()
        imb = binance_depth.imbalance()
        rsi_val, _ = candle_analyzer.rsi()
        score, _ = binance_depth.book_score(side) if side else (0, "")
        bal = S.last_known_balance
        entry = {
            "ts": time.time(),
            "slug": S.slug or "",
            "asset": ASSET,
            "action": action,
            "side": side,
            "price": round(price, 4) if price else None,
            "size": round(size, 2) if size else None,
            "usdc": round(usdc, 2) if usdc else None,
            "reason": reason,
            "btc_price": round(btc_price, 2) if btc_price else None,
            "win_chg": round(win_chg, 6) if win_chg is not None else None,
            "imbalance": round(imb, 2),
            "rsi": round(rsi_val, 0) if rsi_val is not None else None,
            "pnl": round(pnl, 4) if pnl is not None else None,
            "balance": round(bal, 2) if bal is not None else None,
            "book_score": round(score, 0),
        }
        with open(TRADES_LOG_FILE, "a") as f:
            f.write(json.dumps(entry) + "\n")
    except Exception as e:
        print(f"⚠️ Trade log error: {e}")


# ================================================================
#  STATISTICAL SIGNAL LOGGER — frecuencia relativa / probabilidad empírica
# ================================================================
CHEAP_TOKEN_LOG = os.getenv("CHEAP_TOKEN_LOG", "cheap_tokens_log.jsonl")
CHEAP_TOKEN_THRESH = float(os.getenv("CHEAP_TOKEN_THRESH", "0.35"))  # registrar tokens ≤ 0.35


def log_cheap_token_observation(side: str, token_price: float, cl_dir: str,
                                 cl_delta: float, cl_count: int, reason_blocked: str):
    """
    Registra cuando el bot detecta un token barato (≤ 0.35) aunque no entre.
    Objetivo: acumular datos para determinar si los tokens baratos con CL fuerte
    son oportunidades ganadoras o trampas.

    Campos registrados:
    - token_price: precio del token (≤ 0.35 = barato, potencial +143% al TP de 0.85)
    - cl_dir/delta: dirección y fuerza de Chainlink
    - ptb: precio de apertura del ciclo
    - btc_now: precio BTC actual
    - cycle_elapsed/left: timing dentro del ciclo
    - reason_blocked: por qué el bot no entró
    - would_win: se llenará en el cierre del ciclo (None al registrar)
    """
    try:
        btc_now   = spot_tracker.latest() or 0
        ptb       = chainlink_feed.price_to_beat() or 0
        rsi_val, _ = candle_analyzer.rsi()
        imb       = binance_depth.imbalance()
        elapsed, left = None, None
        if S.end_time:
            secs_left = (S.end_time - now_utc()).total_seconds()
            elapsed   = WINDOW_SECONDS - int(secs_left)
            left      = int(secs_left)
        potential_margin = (0.85 - token_price) / token_price * 100 if token_price > 0 else 0

        entry = {
            "ts":               time.time(),
            "slug":             S.slug or "",
            "side":             side,
            "token_price":      round(token_price, 4),
            "potential_margin": round(potential_margin, 1),
            "cl_dir":           cl_dir,
            "cl_delta":         round(cl_delta, 2),
            "cl_count":         cl_count,
            "ptb":              round(ptb, 2),
            "btc_now":          round(btc_now, 2),
            "rsi":              round(rsi_val, 0) if rsi_val is not None else None,
            "imbalance":        round(imb, 2),
            "elapsed_s":        elapsed,
            "left_s":           left,
            "reason_blocked":   reason_blocked,
            "would_win":        None,  # se actualizará al cerrar el ciclo
        }
        with open(CHEAP_TOKEN_LOG, "a") as f:
            f.write(json.dumps(entry) + "\n")
        print(f"👀 CHEAP_TOKEN obs: {side} @ {token_price:.2f} "
              f"(margen potencial +{potential_margin:.0f}%) | {reason_blocked[:40]}")
    except Exception as e:
        print(f"⚠️ cheap token log error: {e}")
_state_mode = "stink" if os.getenv("USE_STINK_BID","0") == "1" else \
              ("hf" if float(os.getenv("TF_MAX_ENTRY_PRICE","0.85")) <= 0.60 else \
              f"{os.getenv('WINDOW_SECONDS','900')}s")
POSITION_STATE_FILE = os.getenv("POSITION_STATE_FILE", f"position_state_{_state_mode}.json")


def save_position_state():
    """
    Persiste el estado de la posición abierta en disco.
    Se llama inmediatamente después de cada compra.
    Si el bot muere o se reinicia, esta información permite
    retomar el seguimiento de la posición sin perderla.
    """
    if not S.position_token:
        return
    state = {
        "ts":                    time.time(),
        "slug":                  S.slug or "",
        "end_time":              S.end_time.isoformat() if S.end_time else None,
        "position_token":        S.position_token,
        "position_label":        S.position_label,
        "position_size":         S.position_size,
        "entry_price":           S.entry_price,
        "entry_ts":              S.entry_ts,
        "peak_price":            S.peak_price,
        "trail_active":          S.trail_active,
        "entry_win_chg":         S.entry_win_chg,
        "entry_cl_delta":        S.entry_cl_delta,
        "is_trend_follow":       S.is_trend_follow,
        "is_peak_reversion":     S.is_peak_reversion,
        "pr_entry_divergence_usd": S.pr_entry_divergence_usd,
        "pr_peak_divergence_usd":  S.pr_peak_divergence_usd,
        "pr_spot_ptb":             S.pr_spot_ptb,
        "pr_peak_trail":           S.pr_peak_trail,
        "pr_trail_active":         S.pr_trail_active,
        "tokens":                S.tokens,
        "condition_id":          S.condition_id,
        "consecutive_losses":    S.consecutive_losses,
        "cycles_to_wait":         S.cycles_to_wait,
        "cycles_waited":           S.cycles_waited,
        "loss_pause_until":      S.loss_pause_until,
        "dynamic_base":          S.dynamic_base,
        "dynamic_base_next_lvl": S.dynamic_base_next_lvl,
    }
    try:
        with open(POSITION_STATE_FILE, "w") as f:
            json.dump(state, f, indent=2)
        print(f"💾 Posición guardada: {S.position_label} @ {S.entry_price:.2f} ({S.slug})")
    except Exception as e:
        print(f"⚠️ Error guardando posición: {e}")


def clear_position_state():
    """Borra el archivo de estado al cerrar la posición."""
    try:
        import os as _os
        if _os.path.exists(POSITION_STATE_FILE):
            _os.remove(POSITION_STATE_FILE)
    except Exception:
        pass
    # Persistir dynamic_base en archivo separado para que sobreviva al reinicio
    _save_sizing_state()


SIZING_STATE_FILE = os.getenv("SIZING_STATE_FILE", "sizing_state.json")

def _save_sizing_state():
    """Guarda dynamic_base y pausa en archivo separado — sobrevive al clear de posición."""
    if S.dynamic_base <= 0 and not S.paused_by_telegram:
        return
    try:
        with open(SIZING_STATE_FILE, "w") as f:
            json.dump({
                "dynamic_base":          S.dynamic_base,
                "dynamic_base_next_lvl": S.dynamic_base_next_lvl,
                "paused_by_telegram":    S.paused_by_telegram,
                "ts":                    time.time(),
            }, f)
    except Exception:
        pass

def _load_sizing_state():
    """Restaura dynamic_base y estado de pausa al arrancar."""
    try:
        if not os.path.exists(SIZING_STATE_FILE):
            return
        with open(SIZING_STATE_FILE) as f:
            d = json.load(f)
        base = float(d.get("dynamic_base", 0))
        nxt  = float(d.get("dynamic_base_next_lvl", 0))
        if base > 0 and S.dynamic_base <= 0:
            S.dynamic_base          = base
            S.dynamic_base_next_lvl = nxt
            print(f"💾 Base dinámica restaurada: ${base:.4f} (próximo escalado ${nxt:.2f})")
        if d.get("paused_by_telegram"):
            S.paused_by_telegram = True
            print(f"⏸️ Bot arrancó en STAND-BY (pausa activa antes del reinicio)")
            print(f"   Envía 'start' por Telegram para reanudar operación")
    except Exception:
        pass


def restore_position_state() -> bool:
    """
    Al arrancar, verifica si hay una posición abierta del ciclo anterior.
    Si existe y el mercado aún no cerró, restaura el estado en S y
    permite que maybe_exit_position retome el seguimiento.

    Retorna True si se restauró una posición activa.
    """
    try:
        import os as _os
        if not _os.path.exists(POSITION_STATE_FILE):
            return False
        with open(POSITION_STATE_FILE) as f:
            state = json.load(f)
    except Exception:
        return False

    # Verificar que el mercado aún no cerró
    end_time_str = state.get("end_time")
    if not end_time_str:
        return False
    try:
        from datetime import datetime, timezone
        end_dt = datetime.fromisoformat(end_time_str)
        if now_utc() >= end_dt:
            # El ciclo ya cerró mientras el WS estaba caído.
            # Necesitamos saber si ganamos o perdimos para actualizar consecutive_losses.
            slug     = state.get("slug", "")
            ep       = state.get("entry_price", 0.0)
            size     = state.get("position_size", 0.0)
            consec   = state.get("consecutive_losses", 0)
            dyn_base = state.get("dynamic_base", 0.0)
            dyn_next = state.get("dynamic_base_next_lvl", 0.0)

            print(f"⚠️ Posición {slug} expiró mientras WS estaba caído — verificando resultado on-chain...")
            won, payout = _check_resolution_onchain()

            if won is True:
                print(f"✅ Posición expirada fue WIN (payout=${payout:.2f}) — reseteando consecutive_losses")
                tg_send(f"✅ Posición {state.get('position_label','?')} expirada: WIN (payout=${payout:.2f}) | consecutive_losses→0")
                # Restaurar solo martingale/base, reset losses
                S.consecutive_losses    = 0
                S.loss_pause_until      = 0.0
                S.dynamic_base          = dyn_base
                S.dynamic_base_next_lvl = dyn_next
            elif won is False:
                new_consec = consec + 1
                print(f"❌ Posición expirada fue LOSS — consecutive_losses: {consec}→{new_consec}")
                tg_send(f"❌ Posición {state.get('position_label','?')} expirada: LOSS | consecutive_losses→{new_consec}")
                S.consecutive_losses    = new_consec
                S.loss_pause_until      = state.get("loss_pause_until", 0.0)
                S.dynamic_base          = dyn_base
                S.dynamic_base_next_lvl = dyn_next
                if new_consec >= MARTINGALE_LIMIT:
                    S.loss_pause_until  = time.time() + PROG_PAUSE_SEC
                    print(f"🛑 Límite de {MARTINGALE_LIMIT} pérdidas → pausa {PROG_PAUSE_SEC/60:.0f} min")
                    tg_send(f"🛑 {MARTINGALE_LIMIT} pérdidas consecutivas (incl. expirada) → pausa {PROG_PAUSE_SEC/60:.0f} min")
            else:
                # No se pudo verificar — mantener estado anterior por seguridad
                print(f"⚠️ No se pudo verificar resultado on-chain — manteniendo consecutive_losses={consec}")
                S.consecutive_losses    = consec
                S.loss_pause_until      = state.get("loss_pause_until", 0.0)
                S.dynamic_base          = dyn_base
                S.dynamic_base_next_lvl = dyn_next

            clear_position_state()
            return False  # no hay posición activa que reconectar
    except Exception:
        return False

    # Restaurar estado en S
    S.slug                      = state.get("slug")
    S.position_token            = state.get("position_token")
    S.position_label            = state.get("position_label")
    S.position_size             = state.get("position_size", 0.0)
    S.entry_price               = state.get("entry_price", 0.0)
    S.entry_ts                  = state.get("entry_ts", 0.0)
    S.peak_price                = state.get("peak_price", 0.0)
    S.trail_active              = state.get("trail_active", False)
    S.entry_win_chg             = state.get("entry_win_chg", 0.0)
    S.entry_cl_delta            = state.get("entry_cl_delta")
    S.is_trend_follow           = state.get("is_trend_follow", False)
    S.is_peak_reversion         = state.get("is_peak_reversion", False)
    S.pr_entry_divergence_usd   = state.get("pr_entry_divergence_usd", 0.0)
    S.pr_peak_divergence_usd    = state.get("pr_peak_divergence_usd", 0.0)
    S.pr_spot_ptb               = state.get("pr_spot_ptb", 0.0)
    S.pr_peak_trail             = state.get("pr_peak_trail", 0.0)
    S.pr_trail_active           = state.get("pr_trail_active", False)
    S.tokens                    = state.get("tokens", [])
    S.condition_id              = state.get("condition_id")
    S.end_time                  = end_dt
    S.orders_sent               = 1  # ya hay una posición abierta

    # Restaurar estado de martingale y base dinámica
    S.consecutive_losses        = state.get("consecutive_losses", 0)
    S.cycles_to_wait            = state.get("cycles_to_wait", 0)
    S.cycles_waited             = state.get("cycles_waited", 0)
    S.loss_pause_until          = state.get("loss_pause_until", 0.0)
    S.dynamic_base              = state.get("dynamic_base", 0.0)
    S.dynamic_base_next_lvl     = state.get("dynamic_base_next_lvl", 0.0)
    if S.consecutive_losses > 0:
        dyn = S.dynamic_base if S.dynamic_base > 0 else PROG_BASE_USDC
        print(f"⚡ Martingale restaurado: {S.consecutive_losses} pérdida(s) → próxima base ${dyn * MARTINGALE_MULT:.2f}")

    secs_left = (end_dt - now_utc()).total_seconds()
    print(f"♻️  POSICIÓN RESTAURADA: {S.position_label} @ {S.entry_price:.2f} | "
          f"size={S.position_size:.2f} | slug={S.slug} | "
          f"quedan {secs_left:.0f}s")
    tg_send(f"♻️ Bot reiniciado con posición abierta: "
            f"{S.position_label} @ {S.entry_price:.2f} | "
            f"quedan {secs_left:.0f}s | {S.slug}")
    return True

def _reject_category(decision: str) -> str:
    """
    (2026-10-19) Deriva una CATEGORÍA corta y estructurada a partir del texto de
    'decision', para poder agrupar/contar los rechazos fácilmente en el análisis
    (ej: cuántos por PRICE_MAX, RSI, MACD, IMBALANCE...).
    IMPORTANTE: NO evalúa ni modifica ningún filtro. Solo clasifica el motivo que
    el filtro YA decidió y que ya viene escrito en 'decision'. Es puramente de
    etiquetado para el log.
    """
    d = (decision or "").upper()
    if d.startswith(("FAST_TRACK_BUY", "MULTI_ROUND_BUY", "BUY")):
        return "BUY"
    if "R1_CAPTURED" in d:                      return "R1_CAPTURED"
    if "QUIET_HOUR" in d:                       return "QUIET_HOUR"
    if "FT_PRICE_MAX" in d:                     return "PRICE_MAX"
    if "FT_PRICE_MIN" in d:                     return "PRICE_MIN"
    if "MR_MIN" in d or "MR_PRICE" in d:        return "MR_PRICE_MIN"
    if "RSI" in d:                              return "RSI"
    if "MACD" in d:                             return "MACD"
    if "IMB" in d:                              return "IMBALANCE"
    if "DOJI" in d:                             return "DOJI"
    if "ATR" in d:                              return "ATR"
    if "VELOCID" in d or "VELOCITY" in d:       return "VELOCITY"
    if "BN_CHG" in d or "BN_CHANGE" in d:       return "BN_CHANGE"
    if "CANDLE" in d or "VELA" in d:            return "CANDLE"
    if "CONFIAN" in d or "CONFIDENCE" in d:     return "CONFIDENCE"
    if "DÉBIL" in d or "DEBIL" in d or "CL WEAK" in d:  return "CL_WEAK"
    if "DIVERGENC" in d:                        return "DIVERGENCE"
    if "BALANCE" in d:                          return "BALANCE_LOW"
    if "WAIT_AFTER_LOSS" in d or "ESPERANDO" in d:      return "WAIT_AFTER_LOSS"
    if "PENDING" in d:                          return "PENDING_RESOLUTION"
    if "SLIPPAGE" in d:                         return "ANTI_SLIPPAGE"
    if "FAST_TRACK_REJECT" in d:                return "FT_REJECT_OTHER"
    if "MULTI_ROUND_ABORT" in d:                return "MR_ABORT_OTHER"
    return "OTHER"


def log_signal_entry(signal: str, side: str, entry_price: float,
                     elapsed: float, left: float, decision: str = "BUY",
                     btc_open: float = None):
    """
    Registra el contexto completo de cada señal evaluada (compremos o no).

    decision: qué hizo el bot con esta señal. Ejemplos:
      "FAST_TRACK_BUY"           — compró vía fast-track
      "MULTI_ROUND_BUY"          — compró vía multi-round
      "FAST_TRACK_REJECT: ..."   — fast-track rechazó (con razón)
      "MULTI_ROUND_ABORT: ..."   — multi-round abortó (con razón)
      "QUIET_HOUR_SKIP"          — skip por hora problemática
      "R1_CAPTURED"              — capturado, esperando R2

    Al cerrarse el mercado, se actualiza con el outcome real llamando
    a update_signal_outcome() — INCLUSO para señales no compradas, lo que
    permite backtest exacto: ¿qué señales rechazadas habrían ganado?

    Campos capturados:
      Señales técnicas    — RSI, MACD, EMA, BB, volumen, patrón
      Order book          — imbalance, depth_mom, wall, MM state
      Contexto de mercado — PTB, divergencia, CL delta, elapsed
      Temporales (NEW)    — velocity_30s/60s, distance_to_strike, atr
      Resultado           — pnl, exit_reason, won (se completa al cerrar)

    Con suficientes muestras, P(won | combinación_señales) converge
    a la probabilidad real de que esa combinación prediga el outcome.
    """
    try:
        now        = time.time()
        btc        = spot_tracker.latest() or 0
        ptb        = chainlink_feed.price_to_beat() or 0
        cl_price   = chainlink_feed.price() or 0
        cl_delta   = chainlink_feed.cl_delta_usd() or 0
        cl_dir, _, cl_cnt = chainlink_feed.cl_direction()
        win_chg    = spot_tracker.change_since_window_start() or 0
        div_usd    = win_chg * btc
        peak_usd   = abs(spot_tracker.peak_move_from_window()) * (btc or 1)
        imb        = binance_depth.imbalance()
        depth_mom  = binance_depth.depth_momentum(30) or 0
        bid_v, ask_v, _ = binance_depth.raw_imbalance()

        # NUEVO (2026-06-03): datos temporales para mejores filtros
        # Velocidad del movimiento — distingue movimientos sostenidos de spikes
        try:
            atr_val = compute_atr(14)
        except Exception:
            atr_val = None
        # Distancia al strike (precio de apertura del mercado 5min)
        # btc_open viene del cycle_log; si no, usamos PTB como proxy del strike
        strike = btc_open if btc_open else ptb
        dist_to_strike = (btc - strike) if (btc and strike) else None
        dist_to_strike_pct = (dist_to_strike / strike * 100) if (dist_to_strike is not None and strike) else None
        # Last candle (vela previa cerrada)
        try:
            last_c = candle_analyzer.last_candle(include_current=False)
            last_candle_type = last_c.get('type', '') if last_c else ''
        except Exception:
            last_candle_type = ''
        # Forming candle (vela en progreso)
        try:
            forming_c = candle_analyzer._current_candle
            forming_type = forming_c.get('type', '') if forming_c else ''
        except Exception:
            forming_type = ''

        # NUEVO (2026-06-09): 8 campos DINÁMICOS para detectar losses limpios
        # (reversiones de último momento que los indicadores estáticos no captan).
        try:
            velocity_30s = spot_tracker.velocity(30.0)
        except Exception:
            velocity_30s = None
        try:
            velocity_60s = spot_tracker.velocity(60.0)
        except Exception:
            velocity_60s = None
        try:
            accel = spot_tracker.acceleration(30.0)
        except Exception:
            accel = None
        # momentum_fading: el precio se mueve a favor del side pero desacelerando
        # (velocity en dirección del trade pero accel en contra)
        momentum_fading = None
        try:
            if velocity_30s is not None and accel is not None:
                if side == "UP":
                    # subiendo pero desacelerando, o ya cayendo
                    momentum_fading = (velocity_30s <= 0) or (accel < 0 and abs(accel) > abs(velocity_30s) * 0.5)
                else:  # DN
                    momentum_fading = (velocity_30s >= 0) or (accel > 0 and abs(accel) > abs(velocity_30s) * 0.5)
        except Exception:
            momentum_fading = None
        try:
            range_pos = spot_tracker.range_position()
        except Exception:
            range_pos = None
        try:
            tick_dir = spot_tracker.tick_direction(10)
        except Exception:
            tick_dir = None
        # NUEVO 2026-06-26: strike_crosses — cuántas veces BTC cruzó el strike
        # durante el ciclo. Mide el "chop" (indecisión) que precede reversiones.
        strike_crosses = None
        try:
            _strike = chainlink_feed.price_to_beat()
            if _strike is not None:
                strike_crosses = spot_tracker.strike_crosses(_strike)
        except Exception:
            strike_crosses = None
        # Orderbook de Polymarket: imbalance entre el lado comprado y el opuesto
        pm_book_imb = None
        pm_opp_pressure = None
        try:
            if len(S.tokens) >= 2:
                up_tok, dn_tok = S.tokens[0], S.tokens[1]
                up_book = S.book.get(up_tok, {})
                dn_book = S.book.get(dn_tok, {})
                # Liquidez total (top3) de cada lado
                up_liq = (safe_float(up_book.get("bid_top3"), 0) or 0) + (safe_float(up_book.get("ask_top3"), 0) or 0)
                dn_liq = (safe_float(dn_book.get("bid_top3"), 0) or 0) + (safe_float(dn_book.get("ask_top3"), 0) or 0)
                # Lado comprado vs opuesto
                if side == "UP":
                    my_liq, opp_liq = up_liq, dn_liq
                else:
                    my_liq, opp_liq = dn_liq, up_liq
                # imbalance: liquidez opuesta / liquidez propia (>1 = más presión contraria)
                if my_liq > 0:
                    pm_book_imb = opp_liq / my_liq
                pm_opp_pressure = opp_liq
        except Exception:
            pm_book_imb = None
            pm_opp_pressure = None

        # Indicadores técnicos
        rsi_v, _       = candle_analyzer.rsi()
        # FIX 2026-06-04: usar MACD(3/15/3) — params cortos para velas 1min en
        # ventanas de 5min. El MACD estándar (12/26/9) necesita 35 velas que
        # nunca hay en 5min, por eso siempre salía None.
        macd_v, macd_s, _ = candle_analyzer.macd(fast=3, slow=15, signal=3)
        macd_hist      = (macd_v - macd_s) if (macd_v is not None and macd_s is not None) else None
        ema_cross, _   = candle_analyzer.ema_cross()
        ef9            = candle_analyzer.ema(9)
        ef21           = candle_analyzer.ema(21)
        bb, _          = candle_analyzer.bollinger()
        vol_surge, vol_ratio, _ = candle_analyzer.volume_surge()
        mom_score, _   = candle_analyzer.momentum_score()
        pat_score, pat_reason = candle_analyzer.chart_patterns(side)
        rev_score, rev_reason = candle_analyzer.reversal_score(side)

        # Wall
        wall_side  = "UP" if win_chg < 0 else "DN"
        wp, ws, wd = binance_depth.nearest_wall(wall_side)
        wall_dist  = abs(btc - wp) if wp else None

        # MM
        mm_sc  = mm_tracker.score(S.tokens[0] if side == "UP" else S.tokens[1]) \
                 if len(S.tokens) == 2 else 0
        mm_st  = mm_tracker.state(S.tokens[0] if side == "UP" else S.tokens[1]) \
                 if len(S.tokens) == 2 else "NEUTRAL"

        entry = {
            # Identificación
            "ts":           now,
            "slug":         S.slug or "",
            "asset":        ASSET,
            "signal":       signal,
            "side":         side,
            "decision":     decision,
            "reject_category": _reject_category(decision),
            "entry_price":  round(entry_price, 4),
            "elapsed_s":    round(elapsed, 0),
            "left_s":       round(left, 0),
            "window_s":     WINDOW_SECONDS,

            # Contexto de mercado
            "btc":          round(btc, 2),
            "ptb":          round(ptb, 2),
            "cl_price":     round(cl_price, 2),
            "cl_delta":     round(cl_delta, 2),
            "cl_dir":       cl_dir,
            "cl_confirms":  cl_cnt,
            "div_usd":      round(div_usd, 2),
            "peak_usd":     round(peak_usd, 2),

            # Order book Binance
            "imb":          round(imb, 3),
            "depth_mom":    round(depth_mom, 3),
            "bid_vol":      round(bid_v, 2),
            "ask_vol":      round(ask_v, 2),
            "wall_dist":    round(wall_dist, 2) if wall_dist is not None else None,
            "wall_size":    round(ws, 2) if ws else None,

            # MM Polymarket
            "mm_score":     mm_sc,
            "mm_state":     mm_st,

            # Indicadores técnicos
            "rsi":          round(rsi_v, 1) if rsi_v is not None else None,
            "macd_hist":    round(macd_hist, 2) if macd_hist is not None else None,
            "ema_cross":    ema_cross,
            "ema9_vs_21":   round(ef9 - ef21, 2) if (ef9 and ef21) else None,
            "bb_pct_b":     round(bb["pct_b"], 3) if bb else None,
            "bb_width":     round(bb["width"], 5) if bb else None,
            "vol_surge":    vol_surge,
            "vol_ratio":    round(vol_ratio, 2),
            "candle_mom":   round(mom_score, 3),
            "pattern":      pat_reason if pat_score > 0 else None,
            "pat_score":    pat_score,
            "rev_score":    rev_score,

            # NUEVO (2026-06-03): datos temporales y de contexto
            "last_candle":  last_candle_type,
            "forming":      forming_type,
            "atr":          round(atr_val, 2) if atr_val is not None else None,
            "dist_strike":  round(dist_to_strike, 2) if dist_to_strike is not None else None,
            "dist_strike_pct": round(dist_to_strike_pct, 4) if dist_to_strike_pct is not None else None,
            "btc_open":     round(strike, 2) if strike else None,

            # NUEVO (2026-06-09): 8 campos dinámicos para detectar reversiones tardías
            "velocity_30s":   round(velocity_30s, 4) if velocity_30s is not None else None,
            "velocity_60s":   round(velocity_60s, 4) if velocity_60s is not None else None,
            "accel":          round(accel, 4) if accel is not None else None,
            "momentum_fading": momentum_fading,
            "range_pos":      round(range_pos, 3) if range_pos is not None else None,
            "tick_dir":       tick_dir,
            "strike_crosses": strike_crosses,
            "pm_book_imb":    round(pm_book_imb, 3) if pm_book_imb is not None else None,
            "pm_opp_pressure": round(pm_opp_pressure, 2) if pm_opp_pressure is not None else None,

            # Resultado — se completa al cerrar posición/mercado
            "outcome_ts":   None,
            "exit_reason":  None,
            "exit_price":   None,
            "pnl":          None,
            "won":          None,
            "hold_sec":     None,
        }
        with open(SIGNALS_LOG_FILE, "a") as f:
            f.write(json.dumps(entry) + "\n")
        # Registro en vivo a Google Sheets — SOLO compras reales (no rechazos/evals)
        if decision == "BUY":
            try:
                sheets_logger.log_buy(entry)
            except Exception:
                pass  # nunca interrumpir el flujo por el Sheet
    except Exception as e:
        print(f"⚠️ Signal log error: {e}")


def update_signal_outcome(slug: str, side: str, exit_reason: str,
                          exit_price: float, pnl: float, hold_sec: float):
    """
    Actualiza el último registro de signals_log.jsonl para este slug/side
    con el resultado real. Lee el archivo, actualiza la última entrada
    coincidente, y reescribe.
    """
    try:
        lines_out = []
        updated   = False
        with open(SIGNALS_LOG_FILE, "r") as f:
            raw_lines = f.readlines()

        # Recorrer en reversa para actualizar solo la entrada más reciente
        for i in range(len(raw_lines) - 1, -1, -1):
            line = raw_lines[i].strip()
            if not line:
                lines_out.insert(0, raw_lines[i])
                continue
            try:
                rec = json.loads(line)
            except Exception:
                lines_out.insert(0, raw_lines[i])
                continue

            if (not updated and
                    rec.get("slug") == slug and
                    rec.get("side") == side and
                    rec.get("outcome_ts") is None):
                rec["outcome_ts"]  = time.time()
                rec["exit_reason"] = exit_reason
                rec["exit_price"]  = round(exit_price, 4) if exit_price else None
                rec["pnl"]         = round(pnl, 4)
                rec["won"]         = pnl > 0
                rec["hold_sec"]    = round(hold_sec, 1)
                lines_out.insert(0, json.dumps(rec) + "\n")
                updated = True
            else:
                lines_out.insert(0, raw_lines[i])

        with open(SIGNALS_LOG_FILE, "w") as f:
            f.writelines(lines_out)
    except Exception as e:
        print(f"⚠️ Signal outcome update error: {e}")


# ================================================================
#  CYCLE LOGGER
# ================================================================
class CycleLog:
    def __init__(self):
        self.reset()

    def reset(self):
        self.slug = ""
        self.market_title = ""
        self.start_ts = time.time()
        self.end_time_str = ""
        self.btc_open: Optional[float] = None
        self.btc_close: Optional[float] = None
        self.btc_low: Optional[float] = None
        self.btc_high: Optional[float] = None
        self.balance_start: Optional[float] = None
        self.balance_end: Optional[float] = None
        self.trades: List[Dict] = []
        self.signals_seen: Dict[str, int] = {"REVERT_UP": 0, "REVERT_DN": 0, "NONE": 0}
        self.pnl_cycle: float = 0.0
        self.rejections: List[str] = []
        self.signal_hits: List[str] = []

    def record_market_open(self, slug, title, end_time, price, balance):
        self.reset()
        self.slug = slug
        self.market_title = title
        self.end_time_str = str(end_time) if end_time else "?"
        self.btc_open = price
        self.btc_high = price
        self.btc_low = price
        self.balance_start = balance

    def record_btc_tick(self, price):
        if price is None:
            return
        if self.btc_high is None or price > self.btc_high:
            self.btc_high = price
        if self.btc_low is None or price < self.btc_low:
            self.btc_low = price
        self.btc_close = price

    def record_signal(self, side):
        self.signals_seen[side] = self.signals_seen.get(side, 0) + 1

    def record_rejection(self, signal, reason, price, win_chg, imb, up_bid, up_ask, dn_bid, dn_ask):
        ts_str = datetime.now(timezone.utc).strftime("%H:%M:%S")
        btc_str = f"${price:,.0f}" if price else "N/A"
        win_str = f"{win_chg:+.5f}" if win_chg is not None else "N/A"
        line = (f"  [{ts_str}] REJECTED {signal} | {reason} | BTC={btc_str} win_chg={win_str} "
                f"| imb={imb:.2f} | UP={up_bid}/{up_ask} DN={dn_bid}/{dn_ask}")
        self.rejections.append(line)

    def record_signal_hit(self, signal, reason, price, win_chg, imb):
        ts_str = datetime.now(timezone.utc).strftime("%H:%M:%S")
        btc_str = f"${price:,.0f}" if price else "N/A"
        win_str = f"{win_chg:+.5f}" if win_chg is not None else "N/A"
        line = f"  [{ts_str}] SIGNAL {signal} | {reason} | BTC={btc_str} win_chg={win_str} | imb={imb:.2f}"
        self.signal_hits.append(line)

    def record_buy(self, side, price, usdc, btc, slug):
        self.trades.append({"action": "BUY", "side": side, "price": price,
                            "usdc": usdc, "btc": btc, "reason": "", "ts": time.time()})

    def record_sell(self, reason, price, entry_price, size, pnl, btc):
        self.trades.append({"action": "SELL", "side": "", "price": price,
                            "entry": entry_price, "size": size, "pnl": pnl,
                            "btc": btc, "reason": reason, "ts": time.time()})
        self.pnl_cycle += pnl

    def write_cycle_summary(self, balance_end):
        self.balance_end = balance_end
        self.btc_close = spot_tracker.latest() or self.btc_close
        elapsed = time.time() - self.start_ts
        ts_now = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
        lines = []
        lines.append(f"{'='*70}")
        lines.append(f"CYCLE CLOSED: {ts_now}")
        lines.append(f"  Market: {self.market_title}")
        lines.append(f"  Slug:   {self.slug}")
        lines.append(f"  End:    {self.end_time_str}")
        lines.append(f"  Duration: {elapsed:.0f}s")
        strategy = "v5.0 TF (Chainlink Trend Follow)" if USE_TREND_FOLLOW else "v4.0 MR (Smart Hold)"
        lines.append(f"  Strategy: {strategy} | Asset: {ASSET.upper()}")
        lines.append(f"")
        if self.btc_open and self.btc_close:
            lines.append(f"  {ASSET.upper()}: open=${self.btc_open:,.2f}  close=${self.btc_close:,.2f}  "
                         f"high=${self.btc_high:,.2f}  low=${self.btc_low:,.2f}  "
                         f"chg=${self.btc_close - self.btc_open:+,.2f}")
        if self.balance_start:
            lines.append(f"  Balance: start=${self.balance_start:.2f}  end=${self.balance_end:.2f}  "
                         f"chg=${self.balance_end - self.balance_start:+.2f}")
        else:
            lines.append(f"  Balance: end=${self.balance_end:.2f}")
        lines.append(f"  Signals: REVERT_UP={self.signals_seen.get('REVERT_UP',0)} "
                     f"REVERT_DN={self.signals_seen.get('REVERT_DN',0)} "
                     f"NONE={self.signals_seen.get('NONE',0)}")
        lines.append(f"  Trades: {len(self.trades)}  PnL: ${self.pnl_cycle:+.2f}")
        trend_dir, trend_cnt = macro_trend_direction()
        lines.append(f"  Macro trend: {trend_dir or 'none'} ({trend_cnt} windows)" if trend_dir
                     else f"  Macro trend: none ({len(S.window_history)} windows tracked)")
        lines.append(f"")
        if self.signal_hits:
            lines.append(f"  --- Signals ({len(self.signal_hits)}) ---")
            for s in self.signal_hits[-10:]:
                lines.append(s)
            if len(self.signal_hits) > 10:
                lines.append(f"  ... and {len(self.signal_hits)-10} more")
        if self.rejections:
            lines.append(f"  --- Rejections ({len(self.rejections)}) ---")
            for r in self.rejections[-10:]:
                lines.append(r)
            if len(self.rejections) > 10:
                lines.append(f"  ... and {len(self.rejections)-10} more")
        if self.trades:
            lines.append(f"  --- Trades ---")
            for t in self.trades:
                ts_str = datetime.fromtimestamp(t["ts"], tz=timezone.utc).strftime("%H:%M:%S")
                if t["action"] == "BUY":
                    btc_s = f"${t['btc']:,.0f}" if t.get("btc") else "N/A"
                    lines.append(f"  [{ts_str}] BUY {t['side']} @ {t['price']:.2f} | ${t['usdc']:.2f} | BTC={btc_s}")
                else:
                    btc_s = f"${t['btc']:,.0f}" if t.get("btc") else "N/A"
                    lines.append(f"  [{ts_str}] SELL {t['reason']} @ {t['price']:.2f} | "
                                 f"entry={t.get('entry',0):.2f} | pnl=${t['pnl']:+.2f} | BTC={btc_s}")
        else:
            lines.append(f"  (no trades this cycle)")
        lines.append(f"{'='*70}")
        lines.append(f"")
        summary = "\n".join(lines)
        try:
            with open(CYCLE_LOG_FILE, "a") as f:
                f.write(summary)
        except Exception as e:
            print(f"⚠️ Failed to write cycle log: {e}")
        print(summary)


cycle_log = CycleLog()


# ================================================================
#  CHAINLINK PRICE FEED
# ================================================================
CHAINLINK_CALL_DATA = "0xfeaf968c"  # latestRoundData()

# ABI selectors para Chainlink AggregatorV3
# getRoundData(uint80): 0x9a6fc8f5
# latestRoundData():    0xfeaf968c
# Ambas retornan: (roundId, answer, startedAt, updatedAt, answeredInRound)

def get_ptb_from_binance_candle(market_open_ts: float) -> Optional[float]:
    """
    Estima el PTB usando el precio de cierre de la vela de Binance 1m
    justo ANTES del epoch del ciclo (minuto 14, 29, 44 ó 59 de cada hora).

    Lógica:
      - El ciclo abre en X:00, X:15, X:30 o X:45
      - La última vela 1m cerrada antes del epoch es X-1min
      - Binance y Chainlink tienen diferencia histórica pequeña ($2-10)
      - Aplicamos el offset BN-CL promedio para estimar el PTB real

    Ventaja: Binance actualiza cada segundo, Chainlink cada ~28s.
    El cierre de vela Binance es el precio más cercano al open del ciclo.
    """
    if not market_open_ts or market_open_ts <= 0:
        return None
    try:
        # Pedir las últimas 3 velas 1m — queremos la que cerró justo antes del epoch
        url = f"https://api.binance.com/api/v3/klines?symbol={BINANCE_SYMBOL}&interval=1m&limit=4"
        resp = requests.get(url, timeout=5)
        resp.raise_for_status()
        klines = resp.json()

        # Filtrar las velas cerradas antes del epoch del mercado
        # k[0] = open_time_ms, k[6] = close_time_ms
        candidates = []
        for k in klines:
            close_ts = k[6] / 1000.0  # cierre de vela en unix
            close_price = float(k[4])  # precio de cierre
            if close_ts <= market_open_ts:
                candidates.append((close_ts, close_price))

        if not candidates:
            return None

        # La más reciente antes del epoch
        candidates.sort(key=lambda x: x[0], reverse=True)
        bn_close_ts, bn_close_price = candidates[0]
        diff_s = market_open_ts - bn_close_ts

        # Ajuste BN→CL: históricamente CL está $2-5 por debajo de BN en momentos de lag
        # Usamos el spread actual BN-CL del chainlink_feed para corregir
        cl_now = chainlink_feed.price()
        bn_now = spot_tracker.latest()
        if cl_now and bn_now and bn_now > 0:
            bn_cl_offset = cl_now - bn_now  # negativo = CL por debajo de BN
        else:
            bn_cl_offset = 0.0

        ptb_estimate = bn_close_price + bn_cl_offset
        print(f"📊 PTB Binance candle: BN cierre=${bn_close_price:,.2f} "
              f"(t-{diff_s:.0f}s del epoch) + offset={bn_cl_offset:+.2f} "
              f"→ PTB estimado=${ptb_estimate:,.2f}")
        return ptb_estimate

    except Exception as e:
        print(f"⚠️ PTB Binance candle fallback: {e}")
        return None


def get_ptb_for_timestamp(target_ts: float) -> Optional[float]:
    """
    Consulta on-chain el precio exacto de Chainlink en el timestamp
    de apertura del mercado — igual que Polymarket.

    Polymarket usa getRoundData para encontrar el round cuyo updatedAt
    es el más cercano (anterior) al epoch del slug.

    Estrategia:
      1. Obtener latestRoundData() → roundId actual
      2. Buscar hacia atrás en los rounds hasta encontrar el round
         cuyo updatedAt <= target_ts y el siguiente > target_ts
      3. Ese es el precio que Polymarket usó como PTB

    Chainlink en Polygon actualiza ~cada 28s → necesitamos buscar
    ~(now - target_ts) / 28 rounds hacia atrás.
    """
    if not target_ts or target_ts <= 0:
        return None

    # Selector getRoundData(uint80 roundId) = 0x9a6fc8f5
    GET_ROUND_DATA = "0x9a6fc8f5"

    def call_rpc(data: str) -> Optional[str]:
        for rpc in CHAINLINK_RPCS:
            try:
                resp = requests.post(rpc, json={
                    "jsonrpc": "2.0", "method": "eth_call",
                    "params": [{"to": CHAINLINK_CONTRACT, "data": data}, "latest"],
                    "id": 1
                }, timeout=5)
                result = resp.json().get("result", "")
                if result and len(result) > 10:
                    return result
            except Exception:
                continue
        return None

    def parse_round(result: str):
        """Parse (roundId, answer, startedAt, updatedAt, answeredInRound)"""
        if not result or len(result) < 330:
            return None
        try:
            round_id   = int(result[2:66],   16)
            answer     = int(result[66:130],  16)
            updated_at = int(result[194:258], 16)
            price      = answer / 1e8
            if price < 1000:  # sanidad
                return None
            return round_id, price, updated_at
        except Exception:
            return None

    # Paso 1: obtener round actual
    latest_result = call_rpc("0xfeaf968c")
    if not latest_result:
        return None
    parsed = parse_round(latest_result)
    if not parsed:
        return None

    current_round_id, current_price, current_updated_at = parsed

    # Si el round actual ya es anterior al target, el PTB es el precio actual
    if current_updated_at <= target_ts:
        return current_price

    # Paso 2: estimar cuántos rounds atrás está el target
    # Polygon Chainlink ≈ 30s por round
    time_diff   = max(0, current_updated_at - target_ts)
    rounds_back = int(time_diff / 30) + 3  # +3 de margen

    # Paso 3: buscar el round correcto
    # Buscamos en ventana amplia: desde rounds_back-3 hasta rounds_back+10
    # para asegurarnos de capturar el último round <= target_ts
    target_round = max(1, current_round_id - rounds_back)
    best_price     = None
    best_round_id  = None
    best_updated   = 0
    best_diff      = float('inf')

    for offset in range(-3, 15):  # ventana amplia hacia ambos lados
        rid = target_round + offset
        if rid <= 0:
            continue

        # Encode getRoundData(uint80 roundId)
        rid_hex = format(rid, '064x')
        data    = GET_ROUND_DATA + rid_hex

        result = call_rpc(data)
        if not result:
            continue
        parsed = parse_round(result)
        if not parsed:
            continue

        _, price, updated_at = parsed

        # Polymarket usa el ÚLTIMO round cuyo updatedAt <= target_ts
        # Es decir: el round más reciente que ya existía cuando abrió el mercado.
        # NO el más cercano en valor absoluto — un round posterior al epoch NO es el PTB.
        if updated_at <= target_ts:
            diff = target_ts - updated_at  # diff siempre >= 0 aquí
            if diff < best_diff:
                best_diff     = diff
                best_updated  = updated_at
                best_price    = price
                best_round_id = rid

    if best_price:
        diff = abs(best_updated - target_ts)
        print(f"⛓️  PTB on-chain exacto: ${best_price:,.2f} "
              f"(round={best_round_id} t±{diff:.0f}s del open)")
        return best_price

    return None


class ChainlinkFeed:
    """
    v5.0: Polls Chainlink aggregator on POLYGON every 15s.
    Polygon Chainlink updates ~every 30s (not hourly like ETH mainnet).
    This is the TRUTH SOURCE for Polymarket resolution.

    v5.7: Añade suscripción WS a eventos AnswerUpdated on-chain.
    Cada update del oráculo emite AnswerUpdated(current, roundId, updatedAt)
    con el timestamp EXACTO del bloque — mismo que usa Polymarket para el PTB.
    """
    # latestRoundData() selector
    CALL_DATA = "0xfeaf968c"

    # ABI mínimo para el evento AnswerUpdated
    ANSWER_UPDATED_ABI = [{
        "anonymous": False,
        "inputs": [
            {"indexed": True,  "name": "current",   "type": "int256"},
            {"indexed": True,  "name": "roundId",   "type": "uint256"},
            {"indexed": False, "name": "updatedAt", "type": "uint256"},
        ],
        "name": "AnswerUpdated",
        "type": "event",
    }]

    # WebSocket RPCs de Polygon (para eventos on-chain)
    WS_RPCS = [
        "wss://polygon-bor.publicnode.com",
        "wss://polygon.drpc.org",
        "wss://1rpc.io/matic",
    ]

    def __init__(self):
        self.lock = threading.Lock()
        self._price: Optional[float] = None
        self._updated_at: float = 0.0
        self._on_chain_updated_at: float = 0.0  # Chainlink's own timestamp
        self._running = False
        self._thread: Optional[threading.Thread] = None
        self._rpc_index = 0
        self._fail_count = 0
        self._spread_history = deque(maxlen=60)
        self._price_history = deque(maxlen=1800)  # 30 min de historia para PTB sync
        self._cl_delta_history = deque(maxlen=120)  # historial de deltas para detectar momentum
        self._event_thread: Optional[threading.Thread] = None  # v5.7: WS events
        self._pending_ptb:  Optional[tuple] = None  # (price, ts) capturado al cierre del ciclo anterior

        # v5.0: Price to beat (Chainlink price at window start)
        self._price_to_beat: Optional[float] = None
        self._price_to_beat_ts: float = 0.0
        self._cl_direction_count: int = 0
        self._cl_last_direction: Optional[str] = None
        self._last_confirmed_on_chain_ts: float = 0.0

        # v5.6: Snapshot programado — captura el PTB en el momento exacto del open
        # Se programa con schedule_ptb_snapshot(open_ts) antes de que abra el mercado
        self._snapshot_at_ts: float = 0.0   # timestamp unix del open a capturar
        self._snapshot_done: bool  = False   # ya capturado este ciclo

    def schedule_ptb_snapshot(self, open_ts: float):
        """
        Programa la captura del PTB en el timestamp exacto de apertura.
        Llamar ANTES de que abra el mercado (ej: al final del ciclo anterior).
        El _run_loop lo capturará en el poll más cercano a ese timestamp.
        """
        with self.lock:
            self._snapshot_at_ts = open_ts
            self._snapshot_done  = False
        print(f"⛓️  PTB snapshot programado para t={open_ts:.0f} "
              f"({datetime.fromtimestamp(open_ts, tz=timezone.utc).strftime('%H:%M:%S')} UTC)")

    def start(self):
        if self._running or not CHAINLINK_ENABLED:
            return
        self._running = True
        self._poll_once()
        self._thread = threading.Thread(target=self._run_loop, daemon=True)
        self._thread.start()
        # v5.7: suscripción a eventos AnswerUpdated on-chain para PTB exacto
        self._event_thread = threading.Thread(target=self._subscribe_events, daemon=True)
        self._event_thread.start()
        p = self._price
        print(f"⛓️ Chainlink POLYGON started: ${p:,.2f}" if p else "⛓️ Chainlink: waiting...")

    def stop(self):
        self._running = False

    def _subscribe_events(self):
        """
        v5.7: Suscripción WebSocket al evento AnswerUpdated del contrato Chainlink.

        Cada vez que el oráculo actualiza su precio emite:
          AnswerUpdated(int256 current, uint256 roundId, uint256 updatedAt)

        El campo `updatedAt` es el timestamp EXACTO del bloque on-chain —
        el mismo que usa Polymarket para fijar el PTB. Al guardarlo en
        _price_history reemplazamos el timestamp de poll por el timestamp real,
        eliminando la diferencia de $20-40 en el PTB.
        """
        try:
            from web3 import Web3
        except ImportError:
            print("⚠️ web3 no disponible — evento AnswerUpdated desactivado")
            return

        while self._running:
            connected = False
            for ws_rpc in self.WS_RPCS:
                try:
                    w3 = Web3(Web3.WebsocketProvider(ws_rpc, websocket_timeout=30))
                    if not w3.is_connected():
                        continue

                    contract = w3.eth.contract(
                        address=Web3.to_checksum_address(CHAINLINK_CONTRACT),
                        abi=self.ANSWER_UPDATED_ABI
                    )

                    print(f"⛓️ Chainlink AnswerUpdated WS conectado: {ws_rpc}")
                    connected = True

                    # Suscribirse a logs del evento
                    event_filter = contract.events.AnswerUpdated.create_filter(
                        from_block='latest'
                    )

                    while self._running:
                        try:
                            for event in event_filter.get_new_entries():
                                args       = event.get("args", {})
                                price_raw  = args.get("current", 0)
                                updated_at = args.get("updatedAt", 0)
                                price      = price_raw / 1e8

                                min_price = {"btc": 10000, "eth": 100, "sol": 1}.get(ASSET, 1)
                                if price > min_price and updated_at > 0:
                                    with self.lock:
                                        self._price                  = price
                                        self._updated_at             = time.time()
                                        self._on_chain_updated_at    = float(updated_at)
                                        # Guardar con timestamp on-chain exacto
                                        self._price_history.append((float(updated_at), price))

                            time.sleep(1)
                        except Exception:
                            break  # Reconectar

                    break  # Salir del loop de RPCs si conectó

                except Exception as e:
                    continue  # Probar siguiente RPC

            if not connected:
                # Chainlink AnswerUpdated WS es opcional — ahora usamos Polymarket RTDS.
                # Solo logear el primer fallo, luego silencio para no contaminar el log.
                if not hasattr(self, '_cl_ws_warned'):
                    self._cl_ws_warned = True
                    print("⚠️ Chainlink AnswerUpdated WS no disponible (usando RTDS como fuente principal)")
                time.sleep(60)  # retry menos frecuente

    def price(self) -> Optional[float]:
        with self.lock:
            return self._price

    def age_sec(self) -> float:
        return time.time() - self._updated_at if self._updated_at > 0 else 9999

    def on_chain_age(self) -> float:
        """Age of the Chainlink on-chain timestamp (not our poll time)."""
        return time.time() - self._on_chain_updated_at if self._on_chain_updated_at > 0 else 9999

    # === v5.0: Price to Beat ===
    def record_price_to_beat(self, market_open_ts: float = 0.0,
                             market_data: Optional[dict] = None):
        """
        Fija el PTB usando el precio EXACTO de Polymarket.

        Estrategia (en orden de precisión):
          0. _price_history RTDS con ts más cercano al epoch del slug
             → timestamps exactos de Chainlink vía Polymarket RTDS
          1. _pending_ptb capturado en el watchdog al cierre del ciclo anterior
          2. getRoundData on-chain: consulta el round exacto
          3. _price_history general: mejor aproximación local
          4. Precio actual: último recurso
        """
        best_price = None
        source_str = "precio actual (fallback)"

        # ── Fuente 0: _pending_ptb — latestRoundData capturado al cierre ─────
        # Se captura con una sola llamada RPC exactamente cuando el ciclo cierra.
        # Es el round más reciente en ese instante = PTB exacto de Polymarket.
        if self._pending_ptb is not None:
            ptb_price, ptb_ts = self._pending_ptb
            self._pending_ptb = None
            age = abs(time.time() - ptb_ts)
            if ptb_price > 1000 and age < 120:
                best_price = ptb_price
                source_str = f"latestRound al cierre (t+{age:.0f}s) ✅"

        # ── Fuente 1: getRoundData on-chain — búsqueda por timestamp ─────────
        if best_price is None and market_open_ts > 0:
            try:
                onchain_price = get_ptb_for_timestamp(market_open_ts)
                if onchain_price:
                    best_price = onchain_price
                    source_str = "on-chain getRoundData"
            except Exception as e:
                print(f"⚠️ PTB on-chain query failed: {e}")

        # ── Fuente 2: RTDS Binance spot como aproximación ─────────────────────
        if best_price is None and market_open_ts > 0:
            rtds_price, rtds_ts = polymarket_rtds.get_price_at(market_open_ts)
            if rtds_price and rtds_price > 1000:
                best_price = rtds_price
                diff_s     = (rtds_ts or 0) - market_open_ts
                source_str = f"RTDS Binance spot {diff_s:+.1f}s (approx)"

        # ── Fuente 3: Binance candle close + offset BN→CL ─────────────────────
        if best_price is None and market_open_ts > 0:
            try:
                bn_ptb = get_ptb_from_binance_candle(market_open_ts)
                if bn_ptb and bn_ptb > 1000:
                    best_price = bn_ptb
                    source_str = "Binance candle close + offset BN→CL"
            except Exception as e:
                print(f"⚠️ PTB Binance candle failed: {e}")

        # ── Fuente 4: precio actual ───────────────────────────────────────────
        if best_price is None:
            with self.lock:
                best_price = self._price
            source_str = "precio actual (sin historia)"

        with self.lock:
            self._price_to_beat            = best_price
            self._price_to_beat_ts         = time.time()
            self._cl_direction_count       = 0
            self._cl_last_direction        = None
            self._last_confirmed_on_chain_ts = self._on_chain_updated_at

        ptb = self._price_to_beat
        if ptb:
            print(f"⛓️  PRICE TO BEAT: ${ptb:,.2f} ({source_str})")

    def price_to_beat(self) -> Optional[float]:
        with self.lock:
            return self._price_to_beat

    def _update_from_rtds(self, price: float, ts: float):
        """
        Llamado por PolymarketRTDS en cada mensaje.
        Actualiza precio actual y añade a _price_history para que
        cl_delta() y cl_direction() usen datos frescos de Chainlink.
        """
        with self.lock:
            self._price               = price
            self._updated_at          = time.time()
            self._on_chain_updated_at = ts
            self._price_history.append((ts, price))

    def cl_delta_usd(self) -> Optional[float]:
        """Current Chainlink price minus price-to-beat in USD."""
        with self.lock:
            if self._price is None or self._price_to_beat is None:
                return None
            delta = self._price - self._price_to_beat
            # Registrar historial de deltas para momentum
            self._cl_delta_history.append((time.time(), delta))
            return delta

    def cl_delta_momentum(self, window_sec: int = 60) -> Optional[str]:
        """
        Detecta si el delta de CL está creciendo o decreciendo.

        Compara el delta actual con el de hace `window_sec` segundos.
        Si el movimiento está perdiendo fuerza = DECELERATING = riesgo de reversión.

        Datos: pérdidas puras tenían CL delta $100-$149 = overextended.
        Si además está decelerando, la probabilidad de reversa sube mucho.

        Returns: 'ACCELERATING' | 'DECELERATING' | 'FLAT' | None
        """
        with self.lock:
            history = list(self._cl_delta_history)

        if len(history) < 4:
            return None

        now_ts = time.time()
        # Delta actual (promedio últimos 3 puntos)
        recent = [d for ts, d in history if now_ts - ts <= 10]
        if not recent:
            return None
        current_delta = sum(recent) / len(recent)

        # Delta de hace window_sec segundos
        old = [d for ts, d in history if window_sec + 10 >= now_ts - ts >= window_sec - 10]
        if not old:
            return None
        old_delta = sum(old) / len(old)

        # Comparar magnitudes (sin importar signo — nos interesa si se achica)
        current_mag = abs(current_delta)
        old_mag     = abs(old_delta)

        if old_mag < 5:  # demasiado pequeño para comparar
            return 'FLAT'

        ratio = current_mag / old_mag
        if ratio > 1.10:
            return 'ACCELERATING'
        elif ratio < 0.85:
            return 'DECELERATING'
        else:
            return 'FLAT'

    def cl_direction(self) -> Tuple[Optional[str], float, int]:
        """
        Returns (direction, delta_usd, consecutive_count).
        direction: "UP" if current CL > price_to_beat, "DN" if below, None if no data.
        """
        with self.lock:
            if self._price is None or self._price_to_beat is None:
                return None, 0.0, 0
            delta = self._price - self._price_to_beat
            direction = "UP" if delta >= 0 else "DN"
            return direction, delta, self._cl_direction_count

    def spread_vs_binance(self, binance_price: Optional[float]) -> Optional[float]:
        cl = self.price()
        if cl is None or binance_price is None:
            return None
        return cl - binance_price

    def record_spread(self, binance_price: Optional[float]):
        spread = self.spread_vs_binance(binance_price)
        if spread is not None:
            with self.lock:
                self._spread_history.append((time.time(), spread))

    def avg_spread(self) -> Optional[float]:
        with self.lock:
            if not self._spread_history:
                return None
            return sum(s for _, s in self._spread_history) / len(self._spread_history)

    def _run_loop(self):
        while self._running:
            time.sleep(CHAINLINK_POLL_SEC)
            self._poll_once()
            # ── Snapshot automático del PTB ──────────────────────────────
            # Si hay un snapshot programado y el timestamp ya llegó, captura
            # el precio actual como PTB — es el precio más cercano al open real
            with self.lock:
                snap_ts   = self._snapshot_at_ts
                snap_done = self._snapshot_done
                now_ts    = time.time()

            if snap_ts > 0 and not snap_done and now_ts >= snap_ts:
                with self.lock:
                    if not self._snapshot_done and self._price:
                        self._price_to_beat        = self._price
                        self._price_to_beat_ts     = now_ts
                        self._cl_direction_count   = 0
                        self._cl_last_direction    = None
                        self._last_confirmed_on_chain_ts = self._on_chain_updated_at
                        self._snapshot_done        = True
                        diff = now_ts - snap_ts
                        print(f"⛓️  PRICE TO BEAT: ${self._price:,.2f} "
                              f"(snapshot automático t+{diff:.0f}s del open ✅)")

    def _poll_once(self):
        for _ in range(len(CHAINLINK_RPCS)):
            rpc = CHAINLINK_RPCS[self._rpc_index % len(CHAINLINK_RPCS)]
            try:
                resp = requests.post(rpc, json={
                    "jsonrpc": "2.0", "method": "eth_call",
                    "params": [{"to": CHAINLINK_CONTRACT, "data": CHAINLINK_CALL_DATA}, "latest"],
                    "id": 1
                }, timeout=5)
                result = resp.json().get("result", "")
                if result and len(result) > 130:
                    answer = int(result[66:130], 16)
                    # Parse updatedAt (4th word, offset 194-258)
                    updated_at = 0
                    if len(result) > 258:
                        updated_at = int(result[194:258], 16)
                    price = answer / 1e8

                    # Validate price (BTC > 10k, SOL > 1, ETH > 100)
                    min_price = {"btc": 10000, "eth": 100, "sol": 1}.get(ASSET, 1)
                    if price > min_price:
                        with self.lock:
                            self._price = price
                            self._updated_at = time.time()
                            if updated_at > 0:
                                self._on_chain_updated_at = updated_at
                            # FIX PTB: guardar el timestamp ON-CHAIN (updated_at) en lugar
                            # del tiempo de poll del bot (time.time()).
                            # Polymarket usa el precio del oráculo en el epoch del mercado —
                            # ese epoch es un timestamp on-chain, no un tiempo de poll.
                            # Al buscar el PTB correcto necesitamos comparar timestamps del
                            # mismo tipo: on-chain vs on-chain.
                            history_ts = updated_at if updated_at > 0 else time.time()
                            self._price_history.append((history_ts, price))

                            # FIX: Only count as a new confirmation if the on-chain
                            # updatedAt timestamp is newer than the last one we counted.
                            # This prevents polling the same oracle round twice and
                            # counting it as two separate "confirmations".
                            is_new_round = (updated_at > 0 and
                                            updated_at > self._last_confirmed_on_chain_ts)

                            if self._price_to_beat is not None and is_new_round:
                                delta = price - self._price_to_beat
                                new_dir = "UP" if delta >= 0 else "DN"
                                if new_dir == self._cl_last_direction:
                                    self._cl_direction_count += 1
                                else:
                                    self._cl_last_direction = new_dir
                                    self._cl_direction_count = 1
                                self._last_confirmed_on_chain_ts = updated_at

                        self._fail_count = 0
                        return
            except Exception:
                pass
            self._rpc_index += 1
        self._fail_count += 1
        if self._fail_count % 4 == 1:
            print(f"⚠️ Chainlink Polygon: {self._fail_count} consecutive poll failures")

    def diag_string(self, binance_price=None) -> str:
        p = self.price()
        if p is None:
            return "⛓️ CL=N/A"
        age = self.age_sec()
        on_chain = self.on_chain_age()
        spread = self.spread_vs_binance(binance_price)
        spread_str = f" vs_BN=${spread:+.0f}" if spread is not None else ""
        ptb = self.price_to_beat()
        delta = self.cl_delta_usd()
        delta_str = f" Δptb=${delta:+.0f}" if delta is not None else ""
        direction, _, count = self.cl_direction()
        dir_str = f" {direction}x{count}" if direction else ""
        stale = " ⚠️STALE" if on_chain > 60 else ""
        return f"⛓️ CL=${p:,.0f}{spread_str}{delta_str}{dir_str}{stale} (chain_age={on_chain:.0f}s)"


chainlink_feed = ChainlinkFeed()


class PolymarketRTDS:
    """
    Fuente primaria de precio Chainlink para el PTB.
    Se suscribe a wss://ws-live-data.polymarket.com → topic crypto_prices_chainlink.
    Misma fuente que usa la UI de Polymarket — sin autenticación.

    Diseño minimalista (basado en ejemplo de referencia):
      - Thread dedicado mantiene la conexión permanente con auto-reconexión
      - Guarda (precio, ts_unix) de cada mensaje en un deque con historia de 10 min
      - get_price_at(target_ts) → precio más cercano ANTES del epoch objetivo
      - init_market() llama directamente a get_price_at(epoch) para el PTB
    """
    RTDS_URL = "wss://ws-live-data.polymarket.com"

    ASSET_SYMBOL = {
        "btc": "btcusdt",
        "eth": "ethusdt",
        "sol": "solusdt",
        "xrp": "xrpusdt",
        "bnb": "bnbusdt",
        "doge": "dogeusdt",
    }

    def __init__(self):
        self._lock    = threading.Lock()
        self._history = deque(maxlen=600)   # ~10 min a 1 msg/seg
        self._price   = None                # último precio recibido
        self._ts      = 0.0                 # timestamp on-chain del último msg
        self._symbol  = self.ASSET_SYMBOL.get(ASSET.lower(), "btc/usd")
        self._connected = False
        self._thread  = None

    # ── API pública ───────────────────────────────────────────────────────

    def start(self):
        """Arranca el thread de conexión en background."""
        if self._thread and self._thread.is_alive():
            return
        self._thread = threading.Thread(target=self._run, name="PolyRTDS", daemon=True)
        self._thread.start()

    def latest(self):
        """(precio, ts_unix) del último mensaje recibido."""
        with self._lock:
            return self._price, self._ts

    def get_price_at(self, target_ts: float, max_diff_sec: float = 120.0):
        """
        Devuelve el precio más reciente con ts ESTRICTAMENTE MENOR al epoch.
        Polymarket usa el último precio del ciclo anterior — el precio
        que llegó justo antes de que abriera el nuevo ciclo (ts < epoch).

        Si el bot arrancó después del epoch (RTDS sin historia previa),
        devuelve None para que el fallback on-chain tome el control.
        """
        with self._lock:
            history = list(self._history)

        if not history:
            return None, None

        # Candidatos: todos con ts ESTRICTAMENTE antes del epoch
        candidates = [(ts, px) for ts, px in history if ts < target_ts]

        if candidates:
            candidates.sort(key=lambda x: x[0])
            best_ts, best_px = candidates[-1]
            if (target_ts - best_ts) <= max_diff_sec:
                return best_px, best_ts

        # Sin datos antes del epoch — el bot arrancó tarde.
        # Devolver None para que on-chain getRoundData tome el control.
        return None, None

    def is_connected(self):
        with self._lock:
            return self._connected

    # ── Thread interno ───────────────────────────────────────────────────

    def _run(self):
        symbol = self._symbol

        def on_open(ws):
            with self._lock:
                self._connected = True
                self._msg_count = 0
            # Sin filtro de symbol — dejar que lleguen todos los mensajes
            # y filtrar client-side. El filtro server-side puede estar
            # bloqueando los mensajes si el formato es incorrecto.
            sub = json.dumps({
                "action": "subscribe",
                "subscriptions": [{
                    "topic": "crypto_prices",
                    "type": "*"
                }]
            })
            ws.send(sub)
            print(f"🔗 Polymarket RTDS conectado — suscrito a crypto_prices (sin filtro)")

        def on_message(ws, msg):
            if not msg or not msg.strip():
                return
            try:
                data = json.loads(msg)
            except Exception:
                return

            if "crypto_prices" not in data.get("topic", ""):
                return

            payload   = data.get("payload", {})
            # Filtrar por symbol — Polymarket envía "btcusdt", "solusdt", etc.
            msg_sym = (payload.get("symbol") or "").lower()
            if msg_sym and symbol not in msg_sym:
                return

            value = payload.get("value") or payload.get("price") or data.get("value")
            ts_ms = (payload.get("timestamp") or data.get("timestamp") or 0)

            if not value:
                return
            price = float(value)
            if price < 1:
                return

            # Detectar ms vs segundos
            if ts_ms:
                ts_f = float(ts_ms)
                ts = ts_f / 1000.0 if ts_f > 1e12 else ts_f if ts_f > 1e9 else time.time()
            else:
                ts = time.time()

            with self._lock:
                first = len(self._history) == 0
                self._price = price
                self._ts    = ts
                self._history.append((ts, price))
            if first:
                print(f"📡 RTDS {symbol}: ${price:,.2f} "
                      f"({datetime.fromtimestamp(ts, tz=timezone.utc).strftime('%H:%M:%S')} UTC) ✅")
            # NO actualizamos chainlink_feed — RTDS entrega Binance spot (1/seg),
            # no precios de Chainlink (~28s). Mantenerlos separados evita que
            # el CL delta y PTB se contaminen con precios de Binance.

        def on_error(ws, err):
            print(f"⚠️ Polymarket RTDS error: {err}")

        def on_close(ws, code, reason):
            with self._lock:
                self._connected = False
            print(f"🔗 Polymarket RTDS desconectado ({code})")

        while True:
            try:
                ws = websocket.WebSocketApp(
                    self.RTDS_URL,
                    on_open=on_open,
                    on_message=on_message,
                    on_error=on_error,
                    on_close=on_close,
                )
                ws.run_forever(
                    sslopt={"cert_reqs": ssl.CERT_NONE},
                    ping_interval=15,
                    ping_timeout=10,
                    reconnect=5,   # reconexión automática nativa cada 5s
                )
            except Exception as e:
                print(f"⚠️ Polymarket RTDS reconectando: {e}")
            time.sleep(3)


polymarket_rtds = PolymarketRTDS()


class SpotTracker:
    def __init__(self):
        self.lock = threading.Lock()
        self.prices = deque(maxlen=3600)
        self.connected = False
        self.window_start_price: Optional[float] = None
        self.window_start_ts: float = 0.0
        self._stop = False
        self._thread: Optional[threading.Thread] = None
        self._peak_move: float = 0.0
        self._window_high: Optional[float] = None  # máximo BTC desde apertura del ciclo
        self._window_low:  Optional[float] = None  # mínimo BTC desde apertura del ciclo

    def start(self):
        self._stop = False
        self._seed_from_rest()
        self._thread = threading.Thread(target=self._run_loop, daemon=True)
        self._thread.start()

    def stop(self):
        self._stop = True

    def record_window_start(self):
        with self.lock:
            if self.prices:
                self.window_start_price = self.prices[-1][1]
                self._window_high = self.prices[-1][1]
                self._window_low  = self.prices[-1][1]
            else:
                self.window_start_price = None
                self._window_high = None
                self._window_low  = None
            self.window_start_ts = time.time()
            self._peak_move = 0.0

    def latest(self) -> Optional[float]:
        with self.lock:
            return self.prices[-1][1] if self.prices else None

    def change_since_window_start(self) -> Optional[float]:
        with self.lock:
            if self.window_start_price is None or not self.prices:
                return None
            current = self.prices[-1][1]
            return (current - self.window_start_price) / self.window_start_price

    def abs_change_since_window_start(self) -> Optional[float]:
        with self.lock:
            if self.window_start_price is None or not self.prices:
                return None
            return self.prices[-1][1] - self.window_start_price

    def peak_move_from_window(self) -> float:
        chg = self.change_since_window_start()
        if chg is not None and abs(chg) > abs(self._peak_move):
            self._peak_move = chg
        return self._peak_move

    def range_exhaustion(self, direction: str) -> Optional[float]:
        """
        Mide qué fracción del rango interno del ciclo ya fue consumida
        en la dirección indicada (UP o DN).

        Lógica:
          Si direction=UP: exhaustion = (precio_actual - open) / (high - open)
          Si direction=DN: exhaustion = (open - precio_actual) / (open - low)

        exhaustion=0.0 → BTC apenas se movió en esa dirección desde el open
        exhaustion=1.0 → BTC llegó al máximo/mínimo del ciclo en esa dirección
        exhaustion>1.0 → BTC rompió el high/low previo (tendencia real)

        Datos empíricos (17 ciclos):
          CL_REVERSE avg exhaustion = 71%  → BTC ya en el pico de la oscilación
          TF_TP      avg exhaustion = 37%  → BTC aún tiene recorrido
          Threshold 65% bloquea 3/5 pérdidas y 0/12 wins.

        Returns: 0.0-1.0+ (o None si no hay suficientes datos)
        """
        with self.lock:
            if (self.window_start_price is None
                    or self._window_high is None
                    or self._window_low is None
                    or not self.prices):
                return None
            current = self.prices[-1][1]
            op      = self.window_start_price
            hi      = self._window_high
            lo      = self._window_low

        if direction == "UP":
            up_range = hi - op
            if up_range < 5:     # rango demasiado pequeño para ser relevante
                return None
            return (current - op) / up_range
        else:  # DN
            dn_range = op - lo
            if dn_range < 5:
                return None
            return (op - current) / dn_range

    def is_reverting(self) -> Tuple[bool, float]:
        peak = self.peak_move_from_window()
        current = self.change_since_window_start()
        if peak is None or current is None or abs(peak) < 0.0001:
            return False, 0.0
        if peak > 0 and current < peak:
            rev = (peak - current) / peak
            return rev > 0.1, rev
        elif peak < 0 and current > peak:
            rev = (current - peak) / abs(peak)
            return rev > 0.1, rev
        return False, 0.0

    def velocity(self, window_sec: float = 30.0) -> Optional[float]:
        """
        (2026-06-09, fix 2026-06-26) Velocidad del precio en USD/segundo durante
        los últimos `window_sec` segundos. Positivo = subiendo, negativo = bajando.

        FIX 2026-06-26: antes dividía por window_sec NOMINAL aunque el past_px
        encontrado fuera de un dt distinto (el primer tick que cruza el umbral
        puede estar a 35-45s, no exactamente 30). Ahora divide por el dt REAL
        entre now y el tick usado, dando la pendiente correcta.
        """
        with self.lock:
            if len(self.prices) < 2:
                return None
            now_ts = self.prices[-1][0]
            now_px = self.prices[-1][1]
            # Buscar el precio de hace window_sec segundos (el primero que cruza)
            target_ts = now_ts - window_sec
            past_px = None
            past_ts = None
            for ts, px in reversed(self.prices):
                if ts <= target_ts:
                    past_px = px
                    past_ts = ts
                    break
            if past_px is None:
                # No hay suficiente historia; usar el más antiguo disponible
                past_ts, past_px = self.prices[0]
            # Dividir por el dt REAL (no el nominal) para la pendiente correcta
            dt = now_ts - past_ts
            if dt < 5:
                return None
            return (now_px - past_px) / dt

    def acceleration(self, window_sec: float = 30.0) -> Optional[float]:
        """
        (2026-06-09) Cambio de velocidad: velocidad reciente vs velocidad previa.
        Positivo = el movimiento acelera. Negativo = se desacelera (fading).

        Compara velocidad de [0, window] contra [window, 2*window].
        """
        with self.lock:
            if len(self.prices) < 3:
                return None
            now_ts = self.prices[-1][0]
            now_px = self.prices[-1][1]

            def px_at(target_ts):
                for ts, px in reversed(self.prices):
                    if ts <= target_ts:
                        return px
                return None

            mid_px = px_at(now_ts - window_sec)
            old_px = px_at(now_ts - 2 * window_sec)
            if mid_px is None or old_px is None:
                return None
            vel_recent = (now_px - mid_px) / window_sec
            vel_prev = (mid_px - old_px) / window_sec
            return vel_recent - vel_prev

    def range_position(self) -> Optional[float]:
        """
        (2026-06-09) Posición del precio actual DENTRO del rango del ciclo.
        0.0 = en el mínimo del ciclo, 1.0 = en el máximo del ciclo.

        Útil para reversión: si compraste DN pero range_position sube hacia
        el strike (el precio rebota desde el mínimo), señal de reversión.
        """
        with self.lock:
            if (self._window_high is None or self._window_low is None
                    or not self.prices):
                return None
            current = self.prices[-1][1]
            hi = self._window_high
            lo = self._window_low
            rng = hi - lo
            if rng < 1:  # rango muy pequeño
                return 0.5
            return (current - lo) / rng

    def tick_direction(self, n: int = 10) -> Optional[int]:
        """
        (2026-06-09) Suma de la dirección de los últimos n ticks.
        +n = todos los ticks subieron, -n = todos bajaron, 0 = equilibrio.

        Microestructura: detecta hacia dónde empuja el precio en los últimos
        segundos, antes de que se refleje en indicadores más lentos.
        """
        with self.lock:
            if len(self.prices) < n + 1:
                return None
            recent = list(self.prices)[-(n + 1):]
            direction = 0
            for i in range(1, len(recent)):
                if recent[i][1] > recent[i-1][1]:
                    direction += 1
                elif recent[i][1] < recent[i-1][1]:
                    direction -= 1
            return direction

    def strike_crosses(self, strike: float) -> Optional[int]:
        """
        (2026-06-26) Cuenta cuántas veces el precio CRUZÓ el strike (PTB) durante
        el ciclo actual. Mide el "chop": un mercado que cruza el strike muchas
        veces está indeciso y es más propenso a reversiones tardías.

        El texto del "reloj" intentaba detectar el chop por HORA (no funcionó,
        los losses estaban dispersos). Esto lo mide DIRECTAMENTE en cada ciclo.

        0-1 cruces = tendencia limpia. 4+ cruces = mercado choppy/indeciso.
        """
        with self.lock:
            if strike is None or len(self.prices) < 3:
                return None
            crosses = 0
            prev_side = None
            for ts, px in self.prices:
                side = 1 if px >= strike else -1
                if prev_side is not None and side != prev_side:
                    crosses += 1
                prev_side = side
            return crosses

    def has_data(self, min_window_sec: int) -> bool:
        with self.lock:
            if len(self.prices) < 5:
                return False
            return (self.prices[-1][0] - self.prices[0][0]) >= (min_window_sec * 0.5)

    def _seed_from_rest(self):
        try:
            r = requests.get(BINANCE_REST_PRICE, timeout=5)
            p = float(r.json().get("price", 0))
            if p > 0:
                with self.lock:
                    self.prices.append((time.time(), p))
                print(f"🟢 {ASSET.upper()} seed: ${p:,.2f}")
        except Exception as e:
            print(f"⚠️ REST seed failed: {e}")

    def _run_loop(self):
        while not self._stop:
            try:
                self._connect_ws()
            except Exception as e:
                print(f"⚠️ Binance WS error: {e}")
            if not self._stop:
                time.sleep(2)

    def _connect_ws(self):
        def on_open(ws):
            self.connected = True
            print(f"🟢 Binance {ASSET.upper()} WS connected")

        def on_message(ws, message):
            try:
                data = json.loads(message)
                p = float(data.get("p", 0))
                t = float(data.get("T", 0)) / 1000.0
                if p > 0 and t > 0:
                    with self.lock:
                        if self.prices and (t - self.prices[-1][0]) < 0.3:
                            return
                        self.prices.append((t, p))
                        # Actualizar high/low del ciclo actual
                        if self._window_high is None or p > self._window_high:
                            self._window_high = p
                        if self._window_low is None or p < self._window_low:
                            self._window_low = p
            except Exception:
                pass

        def on_error(ws, error):
            self.connected = False

        def on_close(ws, code, msg):
            self.connected = False

        ws = websocket.WebSocketApp(
            BINANCE_WS_URL, on_open=on_open, on_message=on_message,
            on_error=on_error, on_close=on_close,
        )
        ws.run_forever(sslopt={"cert_reqs": ssl.CERT_NONE}, ping_interval=20, ping_timeout=10)


spot_tracker = SpotTracker()


# ================================================================
#  SENTIMENT / FRAGILITY TRACKER — v5.8
#  Señales "invisibles" que predicen reversiones:
#    1. Fear & Greed Index (Alternative.me) — sesgo diario
#    2. Funding Rate (Binance Futures)     — crowding indicator
#    3. Open Interest velocity             — trend exhaustion
#    4. CL staleness vs Binance gap        — stale entry detection
# ================================================================
SENT_FG_CACHE_SEC       = float(os.getenv("SENT_FG_CACHE_SEC",       "3600"))  # cache FG 1h
SENT_FUNDING_CACHE_SEC  = float(os.getenv("SENT_FUNDING_CACHE_SEC",  "1800"))  # cache funding 30min
SENT_OI_CACHE_SEC       = float(os.getenv("SENT_OI_CACHE_SEC",       "300"))   # cache OI 5min
SENT_FG_GREED_THRESH    = int(os.getenv("SENT_FG_GREED_THRESH",      "75"))    # FG >= 75 = extreme greed
SENT_FG_FEAR_THRESH     = int(os.getenv("SENT_FG_FEAR_THRESH",       "25"))    # FG <= 25 = extreme fear
SENT_FR_HIGH_THRESH     = float(os.getenv("SENT_FR_HIGH_THRESH",     "0.0005"))  # funding rate alta
SENT_FR_NEGATIVE_THRESH = float(os.getenv("SENT_FR_NEGATIVE_THRESH", "0.0003"))  # funding negativo
SENT_OI_DROP_THRESH     = float(os.getenv("SENT_OI_DROP_THRESH",     "0.02"))    # OI drop > 2%
SENT_CL_STALE_SEC       = float(os.getenv("SENT_CL_STALE_SEC",       "45"))     # CL > 45s = stale
SENT_CL_BN_GAP_USD      = float(os.getenv("SENT_CL_BN_GAP_USD",      "30"))     # CL-BN gap for stale

class SentimentTracker:
    """Tracks macro sentiment signals for reversal risk assessment."""

    def __init__(self):
        self.fear_greed: int = 50           # neutral default
        self.funding_rate: float = 0.0
        self.oi_change_pct: float = 0.0
        self._last_oi_value: Optional[float] = None
        self._last_fg_ts: float = 0.0
        self._last_fr_ts: float = 0.0
        self._last_oi_ts: float = 0.0

    def _fetch_fear_greed(self) -> int:
        """Fetch Fear & Greed Index from Alternative.me (daily, cached 1h)."""
        now = time.time()
        if now - self._last_fg_ts < SENT_FG_CACHE_SEC:
            return self.fear_greed
        try:
            resp = requests.get(
                "https://api.alternative.me/fng/?limit=1", timeout=10)
            data = resp.json()
            val = int(data["data"][0]["value"])
            if 0 <= val <= 100:
                self.fear_greed = val
                self._last_fg_ts = now
                print(f"  [sentiment] Fear & Greed: {val} "
                      f"({'GREED' if val >= 60 else 'FEAR' if val <= 40 else 'NEUTRAL'})")
        except Exception as e:
            if self._last_fg_ts == 0:
                print(f"  [sentiment] FG fetch error: {str(e)[:60]}")
        return self.fear_greed

    def _fetch_funding_rate(self) -> float:
        """Fetch Binance Futures funding rate (8h cycle, cached 30min)."""
        now = time.time()
        if now - self._last_fr_ts < SENT_FUNDING_CACHE_SEC:
            return self.funding_rate
        try:
            url = (f"https://fapi.binance.com/fapi/v1/fundingRate"
                   f"?symbol={BINANCE_SYMBOL}&limit=1")
            resp = requests.get(url, timeout=10)
            data = resp.json()
            if data and isinstance(data, list):
                fr = float(data[0]["fundingRate"])
                self.funding_rate = fr
                self._last_fr_ts = now
                pct = fr * 100
                print(f"  [sentiment] Funding rate: {pct:+.4f}% "
                      f"({'HIGH' if fr > SENT_FR_HIGH_THRESH else 'NEG' if fr < -SENT_FR_NEGATIVE_THRESH else 'NORMAL'})")
        except Exception as e:
            if self._last_fr_ts == 0:
                print(f"  [sentiment] Funding fetch error: {str(e)[:60]}")
        return self.funding_rate

    def _fetch_oi_change(self) -> float:
        """Fetch Binance Futures open interest change (cached 5min)."""
        now = time.time()
        if now - self._last_oi_ts < SENT_OI_CACHE_SEC:
            return self.oi_change_pct
        try:
            url = (f"https://fapi.binance.com/fapi/v1/openInterest"
                   f"?symbol={BINANCE_SYMBOL}")
            resp = requests.get(url, timeout=10)
            data = resp.json()
            current_oi = float(data["openInterest"])
            if self._last_oi_value is not None and self._last_oi_value > 0:
                self.oi_change_pct = (
                    (current_oi - self._last_oi_value) / self._last_oi_value
                )
            self._last_oi_value = current_oi
            self._last_oi_ts = now
        except Exception as e:
            if self._last_oi_ts == 0:
                print(f"  [sentiment] OI fetch error: {str(e)[:60]}")
        return self.oi_change_pct

    def reversal_risk_adjustment(self, direction: str) -> Tuple[float, str]:
        """
        v5.8: Computes confidence adjustment based on sentiment signals.

        Returns (adjustment, reason_str) where adjustment is in [-0.15, +0.08].
        Negative = higher reversal risk → lower confidence.
        Positive = sentiment supports direction → slight confidence boost.
        """
        adj = 0.0
        reasons = []

        # ── 1. Fear & Greed ──────────────────────────────────────────
        fg = self._fetch_fear_greed()

        if direction == "UP" and fg >= SENT_FG_GREED_THRESH:
            # Extreme greed + buying UP = contrarian risk
            penalty = -0.05 * min(1.0, (fg - SENT_FG_GREED_THRESH) / 20.0)
            adj += penalty
            reasons.append(f"FG={fg}(greed){penalty:+.2f}")
        elif direction == "DN" and fg >= SENT_FG_GREED_THRESH:
            # Extreme greed + buying DN = correction likely → boost
            boost = 0.03 * min(1.0, (fg - SENT_FG_GREED_THRESH) / 20.0)
            adj += boost
            reasons.append(f"FG={fg}(greed_DN){boost:+.2f}")
        elif direction == "DN" and fg <= SENT_FG_FEAR_THRESH:
            # Extreme fear + buying DN = contrarian risk (bounce likely)
            penalty = -0.05 * min(1.0, (SENT_FG_FEAR_THRESH - fg) / 20.0)
            adj += penalty
            reasons.append(f"FG={fg}(fear){penalty:+.2f}")
        elif direction == "UP" and fg <= SENT_FG_FEAR_THRESH:
            # Extreme fear + buying UP = bounce play → boost
            boost = 0.03 * min(1.0, (SENT_FG_FEAR_THRESH - fg) / 20.0)
            adj += boost
            reasons.append(f"FG={fg}(fear_UP){boost:+.2f}")

        # ── 2. Funding Rate ──────────────────────────────────────────
        fr = self._fetch_funding_rate()

        if direction == "UP" and fr > SENT_FR_HIGH_THRESH:
            # High positive funding = longs crowded → UP fragile
            penalty = -0.06 * min(1.0, fr / 0.001)
            adj += penalty
            reasons.append(f"FR={fr*100:+.3f}%(crowded_L){penalty:+.2f}")
        elif direction == "DN" and fr < -SENT_FR_NEGATIVE_THRESH:
            # High negative funding = shorts crowded → DN fragile
            penalty = -0.06 * min(1.0, abs(fr) / 0.001)
            adj += penalty
            reasons.append(f"FR={fr*100:+.3f}%(crowded_S){penalty:+.2f}")
        elif direction == "UP" and fr < -SENT_FR_NEGATIVE_THRESH:
            # Negative funding + UP = shorts paying → UP has room
            boost = 0.04 * min(1.0, abs(fr) / 0.001)
            adj += boost
            reasons.append(f"FR={fr*100:+.3f}%(shorts_pay){boost:+.2f}")
        elif direction == "DN" and fr > SENT_FR_HIGH_THRESH:
            # Positive funding + DN = longs paying → DN has room
            boost = 0.04 * min(1.0, fr / 0.001)
            adj += boost
            reasons.append(f"FR={fr*100:+.3f}%(longs_pay){boost:+.2f}")

        # ── 3. OI Change ─────────────────────────────────────────────
        oi = self._fetch_oi_change()

        if oi < -SENT_OI_DROP_THRESH:
            # OI dropping = traders exiting → trend weakening
            penalty = -0.04 * min(1.0, abs(oi) / 0.05)
            adj += penalty
            reasons.append(f"OI={oi*100:+.1f}%(exit){penalty:+.2f}")
        elif oi > SENT_OI_DROP_THRESH:
            # OI rising = new conviction entering → small boost
            boost = 0.02 * min(1.0, oi / 0.05)
            adj += boost
            reasons.append(f"OI={oi*100:+.1f}%(enter){boost:+.2f}")

        # ── 4. CL Staleness ──────────────────────────────────────────
        cl_age = chainlink_feed.on_chain_age()
        bn_price = spot_tracker.latest()
        cl_price = chainlink_feed.price()

        if cl_age > SENT_CL_STALE_SEC and bn_price and cl_price:
            gap_usd = abs(bn_price - cl_price)
            if gap_usd > SENT_CL_BN_GAP_USD:
                penalty = -0.05 * min(1.0, gap_usd / 60.0)
                adj += penalty
                reasons.append(f"CL_STALE={cl_age:.0f}s,gap=${gap_usd:.0f}{penalty:+.2f}")

        # Clamp total adjustment
        adj = max(-0.15, min(0.08, adj))
        reason_str = " | ".join(reasons) if reasons else "neutral"

        return adj, reason_str

    def diag_string(self) -> str:
        """One-line diagnostic for print_diag."""
        fg = self.fear_greed
        fr_pct = self.funding_rate * 100
        oi_pct = self.oi_change_pct * 100
        return (f"FG={fg} FR={fr_pct:+.3f}% OI_chg={oi_pct:+.1f}%")


sentiment_tracker = SentimentTracker()


def resolution_price() -> Optional[float]:
    """Get price Polymarket uses for resolution (Chainlink if fresh, else Binance)."""
    cl_price = chainlink_feed.price()
    cl_age = chainlink_feed.age_sec()
    if CHAINLINK_ENABLED and cl_price and cl_age < 30:
        return cl_price
    bn_price = spot_tracker.latest()
    if bn_price is None:
        return cl_price
    avg_spread = chainlink_feed.avg_spread()
    if avg_spread is not None and CHAINLINK_ENABLED:
        return bn_price + avg_spread
    return bn_price


# ================================================================
#  CANDLE ANALYZER (1-min Binance Klines)
# ================================================================
class CandleAnalyzer:
    def __init__(self, buffer_size=30):
        self.candles = deque(maxlen=buffer_size)
        self._ws = None
        self._thread = None
        self._running = False
        self._current_candle = None

    def start(self):
        if self._running:
            return
        self._running = True
        self._thread = threading.Thread(target=self._run_ws, daemon=True)
        self._thread.start()
        self._prefill_rest()
        print(f"🕯️ CandleAnalyzer started (buffer={CANDLE_BUFFER_SIZE}, prefill={len(self.candles)})")

    def _prefill_rest(self):
        try:
            url = f"{BINANCE_KLINE_REST}&interval=1m&limit={CANDLE_BUFFER_SIZE}"
            resp = requests.get(url, timeout=10)
            data = resp.json()
            for k in data[:-1]:
                candle = self._parse_rest_kline(k)
                if candle:
                    self.candles.append(candle)
        except Exception as e:
            print(f"⚠️ Candle prefill error: {e}")

    def _parse_rest_kline(self, k):
        try:
            o, h, l, c, vol = float(k[1]), float(k[2]), float(k[3]), float(k[4]), float(k[5])
            return self._classify({"open": o, "high": h, "low": l, "close": c,
                                   "volume": vol, "ts": k[0] / 1000.0})
        except Exception:
            return None

    def _classify(self, candle):
        o, h, l, c = candle["open"], candle["high"], candle["low"], candle["close"]
        full_range = h - l
        if full_range < 0.01:
            candle.update({"type": "DOJI", "direction": "NEUTRAL", "body_pct": 0.0,
                           "upper_wick_pct": 0.0, "lower_wick_pct": 0.0})
            return candle
        body = abs(c - o)
        body_pct = body / full_range
        direction = "UP" if c >= o else "DN"
        if direction == "UP":
            upper_wick, lower_wick = h - c, o - l
        else:
            upper_wick, lower_wick = h - o, c - l
        upper_wick_pct = upper_wick / full_range
        lower_wick_pct = lower_wick / full_range
        candle.update({"direction": direction, "body_pct": body_pct,
                       "upper_wick_pct": upper_wick_pct, "lower_wick_pct": lower_wick_pct,
                       "body": body, "upper_wick": upper_wick, "lower_wick": lower_wick})
        if body_pct < CANDLE_DOJI_BODY_PCT:
            candle["type"] = "DOJI"
        elif upper_wick >= body * CANDLE_REJECTION_RATIO and upper_wick_pct > 0.5:
            candle["type"] = "REJECTION_UP"
        elif lower_wick >= body * CANDLE_REJECTION_RATIO and lower_wick_pct > 0.5:
            candle["type"] = "REJECTION_DN"
        elif body_pct < 0.3 and lower_wick_pct > 0.6:
            candle["type"] = "HAMMER"
        elif body_pct < 0.3 and upper_wick_pct > 0.6:
            candle["type"] = "SHOOTING_STAR"
        elif body_pct >= CANDLE_STRONG_BODY_PCT:
            candle["type"] = f"STRONG_{'BULL' if direction == 'UP' else 'BEAR'}"
        else:
            candle["type"] = "BULL" if direction == "UP" else "BEAR"
        return candle

    def _run_ws(self):
        while self._running:
            try:
                ws = websocket.WebSocketApp(
                    BINANCE_KLINE_WS_URL,
                    on_message=self._on_message,
                    on_error=lambda ws, e: None,
                    on_close=lambda ws, code, msg: None,
                )
                ws.run_forever(sslopt={"cert_reqs": ssl.CERT_NONE}, ping_interval=20, ping_timeout=10)
            except Exception:
                pass
            if self._running:
                time.sleep(3)

    def _on_message(self, ws, msg):
        try:
            data = json.loads(msg)
            k = data.get("k", {})
            candle = {"open": float(k["o"]), "high": float(k["h"]),
                      "low": float(k["l"]), "close": float(k["c"]),
                      "volume": float(k["v"]), "ts": k["t"] / 1000.0}
            self._current_candle = self._classify(candle)
            if k.get("x", False):
                self.candles.append(self._current_candle)
                self._current_candle = None
        except Exception:
            pass

    def last_candle(self, include_current=False):
        if include_current and self._current_candle:
            return self._current_candle
        return self.candles[-1] if self.candles else None

    def last_n(self, n=5):
        return list(self.candles)[-n:] if len(self.candles) >= n else list(self.candles)

    def is_rejection(self, direction):
        if not self.candles:
            return False, "no candles"
        candles_to_check = []
        if self._current_candle:
            candles_to_check.append(self._current_candle)
        if self.candles:
            candles_to_check.append(self.candles[-1])
        for c in candles_to_check:
            if direction == "UP" and c["type"] in ("REJECTION_UP", "SHOOTING_STAR"):
                return True, f"🕯️ {c['type']}: wick={c.get('upper_wick_pct',0)*100:.0f}%"
            if direction == "DN" and c["type"] in ("REJECTION_DN", "HAMMER"):
                return True, f"🕯️ {c['type']}: wick={c.get('lower_wick_pct',0)*100:.0f}%"
        return False, ""

    def is_indecision(self, lookback=3):
        recent = self.last_n(lookback)
        if len(recent) < lookback:
            return False, "not enough candles"
        doji_count = sum(1 for c in recent if c["type"] == "DOJI")
        if doji_count >= lookback - 1:
            return True, f"🕯️ INDECISION: {doji_count}/{lookback} dojis"
        return False, ""

    def momentum_score(self):
        recent = self.last_n(5)
        if not recent:
            return 0.0, "no candles"
        score = 0.0
        weights = [0.1, 0.15, 0.2, 0.25, 0.3]
        for i, c in enumerate(recent):
            w = weights[i] if i < len(weights) else 0.2
            if c["direction"] == "UP":
                val = c.get("body_pct", 0.5)
            elif c["direction"] == "DN":
                val = -c.get("body_pct", 0.5)
            else:
                val = 0.0
            if c["type"] == "REJECTION_UP":
                val -= 0.3
            elif c["type"] == "REJECTION_DN":
                val += 0.3
            score += val * w
        score = max(-1.0, min(1.0, score))
        return score, f"candle_mom={score:+.2f}"

    def rsi(self, period=14) -> Tuple[Optional[float], str]:
        candles = list(self.candles)
        if len(candles) < period + 1:
            return None, "not enough candles for RSI"
        closes = [c["close"] for c in candles[-(period + 1):]]
        gains, losses = [], []
        for i in range(1, len(closes)):
            delta = closes[i] - closes[i - 1]
            gains.append(max(0, delta))
            losses.append(max(0, -delta))
        avg_gain = sum(gains) / period
        avg_loss = sum(losses) / period
        if avg_loss < 0.001:
            rsi_val = 100.0
        else:
            rs = avg_gain / avg_loss
            rsi_val = 100 - (100 / (1 + rs))
        label = "OVERSOLD" if rsi_val < 30 else ("OVERBOUGHT" if rsi_val > 70 else "NEUTRAL")
        return rsi_val, f"RSI={rsi_val:.0f}({label})"

    def bollinger(self, period=20, num_std=2.0) -> Tuple[Optional[dict], str]:
        candles = list(self.candles)
        if len(candles) < period:
            return None, "not enough candles for Bollinger"
        closes = [c["close"] for c in candles[-period:]]
        current_price = closes[-1]
        mean = sum(closes) / len(closes)
        variance = sum((p - mean) ** 2 for p in closes) / len(closes)
        std = variance ** 0.5
        upper = mean + (num_std * std)
        lower = mean - (num_std * std)
        width = (upper - lower) / mean if mean > 0 else 0
        band_range = upper - lower
        pct_b = (current_price - lower) / band_range if band_range > 0.01 else 0.5
        result = {"upper": upper, "lower": lower, "middle": mean,
                  "std": std, "width": width, "pct_b": pct_b, "price": current_price}
        if pct_b > 1.0:
            label = "ABOVE_UPPER"
        elif pct_b < 0.0:
            label = "BELOW_LOWER"
        elif width < 0.001:
            label = "SQUEEZE"
        else:
            label = f"%B={pct_b:.2f}"
        return result, f"BB({label} w={width:.4f})"

    def technical_confirmation(self, buy_direction) -> Tuple[bool, bool, str]:
        """Check RSI + Bollinger for entry confirmation. Returns (confirmed, squeeze, reason)."""
        reasons = []
        confirmed = False
        rsi_val, rsi_reason = self.rsi()
        if rsi_val is not None:
            reasons.append(rsi_reason)
            if buy_direction == "UP" and rsi_val < 35:
                confirmed = True
                reasons.append("✅RSI_OVERSOLD")
            elif buy_direction == "DN" and rsi_val > 65:
                confirmed = True
                reasons.append("✅RSI_OVERBOUGHT")
        bb, bb_reason = self.bollinger()
        if bb is not None:
            reasons.append(bb_reason)
            if bb["width"] < 0.0008:
                return False, True, f"BB_SQUEEZE: width={bb['width']:.5f} | " + " | ".join(reasons)
            if buy_direction == "UP" and bb["pct_b"] < 0.05:
                confirmed = True
                reasons.append("✅BB_BELOW_LOWER")
            elif buy_direction == "DN" and bb["pct_b"] > 0.95:
                confirmed = True
                reasons.append("✅BB_ABOVE_UPPER")
        return confirmed, False, " | ".join(reasons)

    def entry_filter(self, buy_direction):
        """
        Candle-based entry filter. Uses trend direction, momentum, RSI, and
        Bollinger Bands to block entries that go AGAINST clear market direction.
        Returns (allow, reason).
        """
        if not USE_CANDLE_ANALYSIS or not self.candles:
            return True, "candle_analysis_off"
        reasons = []
        opposite = "DN" if buy_direction == "UP" else "UP"

        # --- TREND DIRECTION FILTER (new v4.3) ---
        # If last 5 candles strongly favor one direction, don't bet against it
        recent = self.last_n(5)
        if len(recent) >= 4:
            bulls = sum(1 for c in recent if c["direction"] == "UP")
            bears = sum(1 for c in recent if c["direction"] == "DN")
            # 4/5 or 5/5 candles in one direction = strong trend
            if buy_direction == "DN" and bulls >= 4:
                return False, f"CANDLE_TREND_BLOCK: {bulls}/5 bullish candles — don't buy DN"
            if buy_direction == "UP" and bears >= 4:
                return False, f"CANDLE_TREND_BLOCK: {bears}/5 bearish candles — don't buy UP"

        # --- FORMING CANDLE FILTER (new v4.3) ---
        # If the currently forming candle strongly opposes our direction, block
        if self._current_candle:
            forming = self._current_candle.get("type", "")
            if buy_direction == "DN" and forming in ("STRONG_BULL",):
                mom, _ = self.momentum_score()
                if mom > 0.15:
                    return False, f"FORMING_BLOCK: {forming} + mom={mom:+.2f} — don't buy DN"
            if buy_direction == "UP" and forming in ("STRONG_BEAR",):
                mom, _ = self.momentum_score()
                if mom < -0.15:
                    return False, f"FORMING_BLOCK: {forming} + mom={mom:+.2f} — don't buy UP"

        # --- RSI DIRECTIONAL FILTER (new v4.3) ---
        rsi_val, rsi_reason = self.rsi()
        if rsi_val is not None:
            # RSI > 65: price pumped hard. Buying DN is risky if momentum still up.
            # RSI < 35: price dumped hard. Buying UP is risky if momentum still down.
            # But MR logic already wants to buy AGAINST the move, so only block extremes
            if buy_direction == "UP" and rsi_val < 20:
                # Extremely oversold + we want to buy UP = that's actually good for MR
                reasons.append(f"✅RSI_OVERSOLD({rsi_val:.0f})")
            elif buy_direction == "DN" and rsi_val > 80:
                reasons.append(f"✅RSI_OVERBOUGHT({rsi_val:.0f})")
            elif buy_direction == "UP" and rsi_val > 65:
                return False, f"RSI_BLOCK: RSI={rsi_val:.0f} > 65 — overbought, don't buy UP"
            elif buy_direction == "DN" and rsi_val < 35:
                return False, f"RSI_BLOCK: RSI={rsi_val:.0f} < 35 — oversold, don't buy DN"
            else:
                reasons.append(f"RSI={rsi_val:.0f}")

        # Rejection of opposite direction = support (good)
        rej_support, rej_reason = self.is_rejection(opposite)
        if rej_support:
            reasons.append(f"✅ {rej_reason}")

        # Momentum
        mom, mom_reason = self.momentum_score()
        reasons.append(mom_reason)

        # Block on rejection of our direction (if enabled)
        if CANDLE_BLOCK_ON_REJECTION:
            rejected, rej_r = self.is_rejection(buy_direction)
            if rejected:
                return False, f"CANDLE_REJECT: {rej_r}"
        if CANDLE_BLOCK_ON_INDECISION:
            indecisive, ind_r = self.is_indecision()
            if indecisive:
                return False, f"CANDLE_INDECISION: {ind_r}"
        return True, " | ".join(reasons)

    def diag_string(self):
        if not self.candles:
            return "🕯️ no candles"
        last = self.candles[-1]
        mom, _ = self.momentum_score()
        parts = [f"🕯️ last={last['type']}"]
        if self._current_candle:
            parts.append(f"forming={self._current_candle['type']}")
        parts.append(f"mom={mom:+.2f}")
        recent = self.last_n(5)
        bulls = sum(1 for c in recent if c["direction"] == "UP")
        bears = sum(1 for c in recent if c["direction"] == "DN")
        parts.append(f"5c={bulls}↑{bears}↓")
        rsi_val, _ = self.rsi()
        if rsi_val is not None:
            parts.append(f"RSI={rsi_val:.0f}")
        bb, _ = self.bollinger()
        if bb is not None:
            parts.append(f"BB%={bb['pct_b']:.2f}")
        macd_val, macd_sig, _ = self.macd()
        if macd_val is not None:
            parts.append(f"MACD={macd_val-macd_sig:+.1f}")
        ema_cross, ema_r = self.ema_cross()
        if ema_cross != 0:
            parts.append(f"EMA={'X↑' if ema_cross>0 else 'X↓'}")
        return " ".join(parts)

    # ================================================================
    #  v5.3: NUEVOS INDICADORES TÉCNICOS
    # ================================================================

    def ema(self, period: int) -> Optional[float]:
        """Exponential Moving Average sobre closes."""
        candles = list(self.candles)
        if len(candles) < period:
            return None
        closes = [c["close"] for c in candles]
        k = 2.0 / (period + 1)
        ema_val = closes[0]
        for price in closes[1:]:
            ema_val = price * k + ema_val * (1 - k)
        return ema_val

    def macd(self, fast: int = 12, slow: int = 26,
             signal: int = 9) -> Tuple[Optional[float], Optional[float], str]:
        """
        MACD = EMA(fast) - EMA(slow)
        Signal = EMA(MACD, signal_period)
        Histograma = MACD - Signal

        Para ventanas de 5 min con velas de 1 min necesitamos al menos
        slow+signal candles. Con buffer=30 tenemos suficiente.
        Retorna (macd_line, signal_line, reason).
        """
        candles = list(self.candles)
        if len(candles) < slow + signal:
            return None, None, "not enough candles for MACD"

        closes = [c["close"] for c in candles]

        def _ema_series(data, n):
            k = 2.0 / (n + 1)
            result = [data[0]]
            for p in data[1:]:
                result.append(p * k + result[-1] * (1 - k))
            return result

        ema_fast   = _ema_series(closes, fast)
        ema_slow   = _ema_series(closes, slow)
        macd_line  = [f - s for f, s in zip(ema_fast, ema_slow)]
        sig_line   = _ema_series(macd_line, signal)
        hist       = macd_line[-1] - sig_line[-1]

        direction = "BULL_X" if hist > 0 and macd_line[-2] - sig_line[-2] <= 0 else (
                    "BEAR_X" if hist < 0 and macd_line[-2] - sig_line[-2] >= 0 else
                    ("BULL" if hist > 0 else "BEAR"))
        reason = f"MACD={macd_line[-1]:+.1f} sig={sig_line[-1]:+.1f} hist={hist:+.1f}({direction})"
        return macd_line[-1], sig_line[-1], reason

    def ema_cross(self, fast: int = 9, slow: int = 21) -> Tuple[int, str]:
        """
        Cruce de EMAs cortas (9/21 periodos sobre velas de 1 min).
        Retorna: +1 = cruce alcista (fast cruzó arriba slow)
                 -1 = cruce bajista
                  0 = sin cruce reciente
        """
        candles = list(self.candles)
        if len(candles) < slow + 2:
            return 0, "not enough candles for EMA cross"

        closes = [c["close"] for c in candles]
        k_f    = 2.0 / (fast + 1)
        k_s    = 2.0 / (slow + 1)
        ef, es = closes[0], closes[0]
        prev_ef, prev_es = ef, es
        for i, p in enumerate(closes[1:], 1):
            prev_ef, prev_es = ef, es
            ef = p * k_f + ef * (1 - k_f)
            es = p * k_s + es * (1 - k_s)

        gap     = ef - es
        prev_gap = prev_ef - prev_es
        reason  = f"EMA{fast}={ef:.1f} EMA{slow}={es:.1f} gap={gap:+.2f}"

        if prev_gap <= 0 and gap > 0:
            return +1, f"EMA_CROSS_UP {reason}"
        if prev_gap >= 0 and gap < 0:
            return -1, f"EMA_CROSS_DN {reason}"
        return 0, f"EMA_NO_CROSS {reason} ({'above' if gap>0 else 'below'})"

    def volume_surge(self, lookback: int = 10,
                     threshold: float = 1.8) -> Tuple[bool, float, str]:
        """
        Detecta volumen anormalmente alto vs la media reciente.
        Alto volumen en una vela de reversión = señal fuerte.
        Retorna (is_surge, ratio, reason).
        """
        candles = list(self.candles)
        if len(candles) < lookback + 1:
            return False, 0.0, "not enough candles for volume"
        vols     = [c.get("volume", 0) for c in candles[-(lookback + 1):]]
        avg_vol  = sum(vols[:-1]) / lookback if lookback > 0 else 1
        last_vol = vols[-1]
        if avg_vol < 0.001:
            return False, 0.0, "zero avg volume"
        ratio  = last_vol / avg_vol
        surge  = ratio >= threshold
        reason = f"VOL={last_vol:.0f} avg={avg_vol:.0f} ratio={ratio:.1f}x{'🔥' if surge else ''}"
        return surge, ratio, reason

    def chart_patterns(self, buy_direction: str) -> Tuple[int, str]:
        """
        Detecta patrones de gráfico sobre las últimas velas:

        PARA BUY_DIRECTION="UP" (esperamos rebote alcista):
          - Doble suelo (W): dos mínimos similares con pico intermedio
          - Triángulo ascendente: mínimos subiendo, máximos planos
          - Hammer / Pin bar alcista en suelo

        PARA BUY_DIRECTION="DN" (esperamos caída):
          - Doble techo (M): dos máximos similares con valle intermedio
          - Triángulo descendente: máximos bajando, mínimos planos
          - Shooting star / Pin bar bajista en techo

        Retorna (score 0-3, descripción).
        Scores:
          3 = patrón mayor claro (doble techo/suelo)
          2 = patrón moderado (triángulo, pin bar confirmado)
          1 = señal débil (indicio)
          0 = sin patrón
        """
        candles = list(self.candles)
        if len(candles) < 6:
            return 0, "not enough candles for patterns"

        closes = [c["close"] for c in candles]
        highs  = [c["high"]  for c in candles]
        lows   = [c["low"]   for c in candles]
        n      = len(candles)

        # ── Encontrar pivotes locales (máximos y mínimos) ────────────────
        def find_pivots(series, mode="high", window=2):
            pivots = []
            for i in range(window, len(series) - window):
                if mode == "high":
                    if series[i] == max(series[i-window:i+window+1]):
                        pivots.append((i, series[i]))
                else:
                    if series[i] == min(series[i-window:i+window+1]):
                        pivots.append((i, series[i]))
            return pivots

        pivot_highs = find_pivots(highs, "high", window=2)
        pivot_lows  = find_pivots(lows,  "low",  window=2)
        tol         = 0.0003   # 0.03% tolerancia de precio para "mismo nivel"

        # ── PATRÓN 1: Doble techo (M) / Doble suelo (W) ─────────────────
        if buy_direction == "DN" and len(pivot_highs) >= 2:
            # Doble techo: dos máximos cercanos en precio
            h1_i, h1_p = pivot_highs[-2]
            h2_i, h2_p = pivot_highs[-1]
            diff = abs(h1_p - h2_p) / max(h1_p, h2_p)
            if diff < tol and h2_i > h1_i:
                # Confirmar que entre los dos picos hubo un valle
                mid_lows = lows[h1_i:h2_i] if h2_i > h1_i else []
                if mid_lows and min(mid_lows) < min(h1_p, h2_p) * 0.9997:
                    return 3, (f"DOUBLE_TOP H1={h1_p:.1f} H2={h2_p:.1f} "
                               f"diff={diff*100:.2f}%")

        if buy_direction == "UP" and len(pivot_lows) >= 2:
            # Doble suelo: dos mínimos cercanos en precio
            l1_i, l1_p = pivot_lows[-2]
            l2_i, l2_p = pivot_lows[-1]
            diff = abs(l1_p - l2_p) / max(l1_p, l2_p)
            if diff < tol and l2_i > l1_i:
                mid_highs = highs[l1_i:l2_i] if l2_i > l1_i else []
                if mid_highs and max(mid_highs) > max(l1_p, l2_p) * 1.0003:
                    return 3, (f"DOUBLE_BOTTOM L1={l1_p:.1f} L2={l2_p:.1f} "
                               f"diff={diff*100:.2f}%")

        # ── PATRÓN 2: Triángulo ascendente / descendente ─────────────────
        if len(candles) >= 8:
            recent_h = highs[-8:]
            recent_l = lows[-8:]
            # Triángulo ascendente: mínimos subiendo, máximos planos → alcista
            low_slope  = (recent_l[-1] - recent_l[0]) / 8
            high_range = max(recent_h) - min(recent_h)
            if buy_direction == "UP":
                if low_slope > 0 and high_range / max(recent_h) < 0.001:
                    return 2, (f"ASCENDING_TRIANGLE lows_slope={low_slope:+.2f} "
                               f"highs_range={high_range:.1f}")
            # Triángulo descendente: máximos bajando, mínimos planos → bajista
            high_slope = (recent_h[-1] - recent_h[0]) / 8
            low_range  = max(recent_l) - min(recent_l)
            if buy_direction == "DN":
                if high_slope < 0 and low_range / max(recent_l) < 0.001:
                    return 2, (f"DESCENDING_TRIANGLE highs_slope={high_slope:+.2f} "
                               f"lows_range={low_range:.1f}")

        # ── PATRÓN 3: Cabeza y hombros (simplificado) ────────────────────
        # Necesita al menos 3 picos (hombro izq, cabeza, hombro der)
        if buy_direction == "DN" and len(pivot_highs) >= 3:
            sh_l_i, sh_l = pivot_highs[-3]
            head_i, head  = pivot_highs[-2]
            sh_r_i, sh_r  = pivot_highs[-1]
            # Cabeza > ambos hombros, hombros aprox iguales
            hombros_diff = abs(sh_l - sh_r) / max(sh_l, sh_r)
            if head > sh_l and head > sh_r and hombros_diff < 0.002:
                return 3, (f"HEAD_SHOULDERS head={head:.1f} "
                           f"shldr={sh_l:.1f}/{sh_r:.1f}")

        if buy_direction == "UP" and len(pivot_lows) >= 3:
            sh_l_i, sh_l = pivot_lows[-3]
            head_i, head  = pivot_lows[-2]
            sh_r_i, sh_r  = pivot_lows[-1]
            hombros_diff  = abs(sh_l - sh_r) / max(sh_l, sh_r)
            if head < sh_l and head < sh_r and hombros_diff < 0.002:
                return 3, (f"INV_HEAD_SHOULDERS head={head:.1f} "
                           f"shldr={sh_l:.1f}/{sh_r:.1f}")

        # ── PATRÓN 4: Pin bar (mecha larga = rechazo puntual) ────────────
        last_c = candles[-1]
        if last_c.get("type") in ("HAMMER", "REJECTION_DN") and buy_direction == "UP":
            wick_pct = last_c.get("lower_wick_pct", 0)
            return 2, f"PIN_BAR_BULL wick={wick_pct*100:.0f}%"
        if last_c.get("type") in ("SHOOTING_STAR", "REJECTION_UP") and buy_direction == "DN":
            wick_pct = last_c.get("upper_wick_pct", 0)
            return 2, f"PIN_BAR_BEAR wick={wick_pct*100:.0f}%"

        # ── Indicio débil: DOJI después de movimiento extremo ────────────
        if last_c.get("type") == "DOJI":
            return 1, "DOJI_EXHAUSTION (weak reversal hint)"

        return 0, "no_chart_pattern"

    def reversal_score(self, buy_direction: str) -> Tuple[int, str]:
        """
        Puntuación integrada de señales técnicas de reversión (0-12).
        Combina: RSI, MACD, EMA cross, Bollinger, volumen, patrones.
        Diseñado como CONFIRMACIÓN, no como filtro exclusivo.

        Scoring:
          RSI extremo (>70 o <30)           → +2
          RSI cruzando de extremo           → +1
          MACD cruce en dirección favorable → +2  (cruce = señal más fuerte)
          MACD histograma a favor           → +1
          EMA cross favorable               → +2
          BB: precio en/fuera de banda      → +1
          Volumen surge en vela clave       → +1
          Patrón de gráfico                 → +0/+1/+2/+3
        """
        parts  = []
        score  = 0

        # ── RSI ──────────────────────────────────────────────────────────
        rsi_val, rsi_reason = self.rsi()
        if rsi_val is not None:
            if buy_direction == "UP":
                if rsi_val < 25:
                    score += 2; parts.append(f"RSI_EXTREME_LOW={rsi_val:.0f}(+2)")
                elif rsi_val < 35:
                    score += 1; parts.append(f"RSI_OVERSOLD={rsi_val:.0f}(+1)")
                elif rsi_val > 55:
                    parts.append(f"RSI_HIGH={rsi_val:.0f}(0)")  # advertencia, no suma
            else:  # DN
                if rsi_val > 75:
                    score += 2; parts.append(f"RSI_EXTREME_HIGH={rsi_val:.0f}(+2)")
                elif rsi_val > 65:
                    score += 1; parts.append(f"RSI_OVERBOUGHT={rsi_val:.0f}(+1)")
                elif rsi_val < 45:
                    parts.append(f"RSI_LOW={rsi_val:.0f}(0)")

        # ── MACD ─────────────────────────────────────────────────────────
        macd_val, macd_sig, macd_reason = self.macd()
        if macd_val is not None and macd_sig is not None:
            hist      = macd_val - macd_sig
            candles_l = list(self.candles)
            if len(candles_l) >= 2:
                closes  = [c["close"] for c in candles_l]
                k_f     = 2.0 / 13; k_s = 2.0 / 27
                ef, es  = closes[0], closes[0]
                for p in closes[1:-1]:
                    ef = p * k_f + ef * (1 - k_f)
                    es = p * k_s + es * (1 - k_s)
                prev_hist = (ef - es) - macd_sig  # approx prev histogram

                if buy_direction == "UP":
                    if hist > 0 and prev_hist <= 0:
                        score += 2; parts.append(f"MACD_CROSS_UP(+2)")
                    elif hist > 0:
                        score += 1; parts.append(f"MACD_BULL hist={hist:+.1f}(+1)")
                    elif hist < 0:
                        parts.append(f"MACD_BEAR hist={hist:+.1f}(0)")
                else:
                    if hist < 0 and prev_hist >= 0:
                        score += 2; parts.append(f"MACD_CROSS_DN(+2)")
                    elif hist < 0:
                        score += 1; parts.append(f"MACD_BEAR hist={hist:+.1f}(+1)")
                    elif hist > 0:
                        parts.append(f"MACD_BULL hist={hist:+.1f}(0)")

        # ── EMA Cross ────────────────────────────────────────────────────
        ema_cross_val, ema_reason = self.ema_cross()
        if buy_direction == "UP" and ema_cross_val > 0:
            score += 2; parts.append(f"EMA_CROSS_UP(+2)")
        elif buy_direction == "UP" and ema_cross_val == 0:
            ef9  = self.ema(9)
            ef21 = self.ema(21)
            if ef9 and ef21 and ef9 > ef21:
                score += 1; parts.append(f"EMA_UP_TREND ef9>ef21(+1)")
        elif buy_direction == "DN" and ema_cross_val < 0:
            score += 2; parts.append(f"EMA_CROSS_DN(+2)")
        elif buy_direction == "DN" and ema_cross_val == 0:
            ef9  = self.ema(9)
            ef21 = self.ema(21)
            if ef9 and ef21 and ef9 < ef21:
                score += 1; parts.append(f"EMA_DN_TREND ef9<ef21(+1)")

        # ── Bollinger Bands ───────────────────────────────────────────────
        bb, bb_reason = self.bollinger()
        if bb is not None:
            if buy_direction == "UP" and bb["pct_b"] < 0.05:
                score += 1; parts.append(f"BB_BELOW_LOWER pctB={bb['pct_b']:.2f}(+1)")
            elif buy_direction == "DN" and bb["pct_b"] > 0.95:
                score += 1; parts.append(f"BB_ABOVE_UPPER pctB={bb['pct_b']:.2f}(+1)")

        # ── Volumen ───────────────────────────────────────────────────────
        vol_surge, vol_ratio, vol_reason = self.volume_surge(lookback=10, threshold=1.6)
        if vol_surge:
            score += 1; parts.append(f"VOL_SURGE {vol_ratio:.1f}x(+1)")

        # ── Patrones de gráfico ───────────────────────────────────────────
        pat_score, pat_reason = self.chart_patterns(buy_direction)
        score += pat_score
        if pat_score > 0:
            parts.append(f"PATTERN:{pat_reason}(+{pat_score})")

        reason_str = " | ".join(parts) if parts else "no_signals"
        return score, reason_str


candle_analyzer = CandleAnalyzer(buffer_size=CANDLE_BUFFER_SIZE)


# ================================================================
#  v5.6: NUEVOS INDICADORES — ATR, Stochastic RSI, Market Session
# ================================================================

# ── ATR se calcula sobre las velas de CandleAnalyzer ────────────
def compute_atr(period: int = 14) -> Optional[float]:
    """
    Average True Range — mide volatilidad real.
    TR = max(H-L, |H-Cprev|, |L-Cprev|)
    ATR = media de TR en N periodos.
    Usado para hacer el umbral PR_MIN_PEAK_DIVERGENCE_USD dinámico.
    """
    candles = list(candle_analyzer.candles)
    if len(candles) < period + 1:
        return None
    candles = candles[-(period + 1):]
    trs = []
    for i in range(1, len(candles)):
        h = candles[i]["high"]
        l = candles[i]["low"]
        c_prev = candles[i-1]["close"]
        tr = max(h - l, abs(h - c_prev), abs(l - c_prev))
        trs.append(tr)
    return sum(trs) / len(trs) if trs else None


def compute_stoch_rsi(rsi_period: int = 14, stoch_period: int = 14) -> Optional[Tuple[float, float]]:
    """
    Stochastic RSI — aplica el oscilador estocástico sobre el RSI.
    Más sensible que el RSI puro para detectar puntos de giro.
    Retorna (K, D) en rango 0-100:
      K < 20 = oversold extremo (fuerte señal de rebote)
      K > 80 = overbought extremo (fuerte señal de techo)
    """
    candles = list(candle_analyzer.candles)
    needed = rsi_period + stoch_period + 1
    if len(candles) < needed:
        return None

    closes = [c["close"] for c in candles]

    # Calcular serie RSI
    def _rsi_series(prices, period):
        rsi_vals = []
        for i in range(period, len(prices)):
            window = prices[i - period:i + 1]
            gains  = [max(0, window[j] - window[j-1]) for j in range(1, len(window))]
            losses = [max(0, window[j-1] - window[j]) for j in range(1, len(window))]
            ag = sum(gains) / period
            al = sum(losses) / period
            if al < 0.001:
                rsi_vals.append(100.0)
            else:
                rs = ag / al
                rsi_vals.append(100 - (100 / (1 + rs)))
        return rsi_vals

    rsi_series = _rsi_series(closes, rsi_period)
    if len(rsi_series) < stoch_period:
        return None

    # Aplicar estocástico sobre la serie RSI
    k_values = []
    for i in range(stoch_period - 1, len(rsi_series)):
        window = rsi_series[i - stoch_period + 1:i + 1]
        low_rsi  = min(window)
        high_rsi = max(window)
        denom    = high_rsi - low_rsi
        k = ((rsi_series[i] - low_rsi) / denom * 100) if denom > 0.01 else 50.0
        k_values.append(k)

    if not k_values:
        return None

    k = k_values[-1]
    d = sum(k_values[-3:]) / min(3, len(k_values))  # D = SMA(3) de K
    return round(k, 1), round(d, 1)


def compute_market_session() -> Tuple[str, float]:
    """
    Sesión de mercado según hora UTC.
    BTC tiene comportamientos estadísticamente diferentes por sesión:

    Asiática  (00-08 UTC): bajo volumen, movimientos caprichosos, reversiones
                           menos predecibles → penaliza confianza
    Europea   (08-13 UTC): volumen creciente, tendencias más limpias
    NY        (13-21 UTC): máximo volumen institucional, mejores reversiones
    NY/Asia   (21-24 UTC): volumen decreciente, spread mayor

    Retorna (nombre_sesion, score 0.0-1.0)
    """
    hora_utc = datetime.now(timezone.utc).hour
    if 13 <= hora_utc < 21:
        return "NY",      1.0   # sesión óptima
    elif 8 <= hora_utc < 13:
        return "EUR",     0.80  # buena sesión
    elif 21 <= hora_utc < 24:
        return "NY/ASIA", 0.60  # volumen bajando
    else:  # 0-8 UTC
        return "ASIA",    0.40  # volumen bajo, menos predecible


# ================================================================
#  v5.6: TRADE FLOW TRACKER — volumen real ejecutado bid vs ask
# ================================================================
class TradeFlowTracker:
    """
    Monitorea el WebSocket de aggTrade de Binance para calcular
    el flujo real de órdenes en los últimos N segundos.

    A diferencia del order book (intención), esto mide EJECUCIÓN:
      - trade con m=True  → market sell (ejecutó contra bids) → presión bajista
      - trade con m=False → market buy  (ejecutó contra asks) → presión alcista

    buy_ratio > 0.65 cuando el spot bajó → compradores absorbiendo la caída
                                          → señal fuerte de reversión UP
    """
    def __init__(self):
        self.lock   = threading.Lock()
        self._trades: deque = deque(maxlen=2000)  # (ts, side, qty)
        self._stop  = False
        self._thread: Optional[threading.Thread] = None
        self.connected = False

    def start(self):
        self._stop   = False
        self._thread = threading.Thread(target=self._run, daemon=True)
        self._thread.start()

    def stop(self):
        self._stop = True

    def _run(self):
        while not self._stop:
            try:
                self._connect()
            except Exception:
                pass
            if not self._stop:
                time.sleep(2)

    def _connect(self):
        def on_open(ws):
            self.connected = True
            print(f"🌊 TradeFlow {ASSET.upper()} WS connected")

        def on_message(ws, msg):
            try:
                d    = json.loads(msg)
                ts   = d["T"] / 1000.0
                qty  = float(d["q"])
                # m=True → buyer is MM (market sell) → presión bajista
                # m=False → buyer es aggressor (market buy) → presión alcista
                side = "SELL" if d.get("m") else "BUY"
                with self.lock:
                    self._trades.append((ts, side, qty))
            except Exception:
                pass

        def on_error(ws, e):
            self.connected = False

        def on_close(ws, *a):
            self.connected = False

        ws = websocket.WebSocketApp(
            BINANCE_WS_URL,  # ya usa @aggTrade por defecto
            on_open=on_open, on_message=on_message,
            on_error=on_error, on_close=on_close,
        )
        ws.run_forever(sslopt={"cert_reqs": ssl.CERT_NONE},
                       ping_interval=20, ping_timeout=10)

    def flow(self, window_sec: int = 30) -> Tuple[Optional[float], str]:
        """
        Calcula buy_ratio = volumen comprador / volumen total en los últimos N segundos.
        buy_ratio > 0.5 → más compras que ventas (presión alcista)
        buy_ratio < 0.5 → más ventas que compras (presión bajista)
        """
        now = time.time()
        cutoff = now - window_sec
        with self.lock:
            recent = [(ts, side, qty) for ts, side, qty in self._trades if ts >= cutoff]

        if not recent:
            return None, "no trade data"

        buy_vol  = sum(qty for _, side, qty in recent if side == "BUY")
        sell_vol = sum(qty for _, side, qty in recent if side == "SELL")
        total    = buy_vol + sell_vol
        if total < 0.001:
            return None, "zero volume"

        ratio = buy_vol / total
        label = ("BUY_DOM" if ratio > 0.65 else
                 "SELL_DOM" if ratio < 0.35 else "NEUTRAL")
        return round(ratio, 3), f"FLOW={ratio:.2f}({label}) buy={buy_vol:.1f} sell={sell_vol:.1f}"

    def reversal_score(self, cheap_direction: str, window_sec: int = 30) -> Tuple[int, str]:
        """
        Puntúa el trade flow como señal de reversión (0-2).
        Si compramos UP (spot bajó), queremos que los trades sean mayoritariamente BUY
        (compradores absorbiendo la caída).
        Si compramos DN (spot subió), queremos que sean mayoritariamente SELL.
        """
        ratio, desc = self.flow(window_sec)
        if ratio is None:
            return 0, "no flow data"

        if cheap_direction == "UP":
            # Compramos UP → necesitamos presión compradora real
            if ratio > 0.65:
                return 2, f"FLOW_BUY_DOM {desc} → soporte UP"
            elif ratio > 0.55:
                return 1, f"FLOW_BUY_SLIGHT {desc}"
            elif ratio < 0.35:
                return -1, f"FLOW_SELL_DOM {desc} → presión bajista"
        else:
            # Compramos DN → necesitamos presión vendedora real
            if ratio < 0.35:
                return 2, f"FLOW_SELL_DOM {desc} → resistencia DN"
            elif ratio < 0.45:
                return 1, f"FLOW_SELL_SLIGHT {desc}"
            elif ratio > 0.65:
                return -1, f"FLOW_BUY_DOM {desc} → presión alcista"

        return 0, f"FLOW_NEUTRAL {desc}"


    def eat_rate(self, window_sec: int = 10) -> Tuple[float, str, str]:
        """
        v5.10: EAT-FLOW/s — net order consumption rate per second.
        Measures how aggressively market orders are eating through the book.

        Returns: (rate, direction, description)
          rate > 0 → asks being eaten (bullish aggression, BTC moving UP)
          rate < 0 → bids being eaten (bearish aggression, BTC moving DN)
          abs(rate) → intensity (BTC/sec consumed)

        Unlike flow() which gives a ratio, eat_rate gives absolute volume/sec
        which better captures "conviction" — a burst of 5 BTC/sec selling
        is much stronger signal than a trickle of 0.1 BTC/sec.
        """
        now = time.time()
        cutoff = now - window_sec
        with self.lock:
            recent = [(ts, side, qty) for ts, side, qty in self._trades if ts >= cutoff]

        if not recent or window_sec <= 0:
            return 0.0, "FLAT", "no data"

        buy_vol  = sum(qty for _, side, qty in recent if side == "BUY")
        sell_vol = sum(qty for _, side, qty in recent if side == "SELL")
        net = buy_vol - sell_vol  # positive = buying pressure
        rate = net / window_sec

        if rate > 0.05:
            direction = "BUY_EAT"
            label = f"EAT={rate:+.2f}/s asks consumed"
        elif rate < -0.05:
            direction = "SELL_EAT"
            label = f"EAT={rate:+.2f}/s bids consumed"
        else:
            direction = "FLAT"
            label = f"EAT={rate:+.2f}/s balanced"

        return round(rate, 3), direction, label


trade_flow = TradeFlowTracker()


# ================================================================
#  BINANCE DEPTH TRACKER
# ================================================================
class BinanceDepth:
    def __init__(self):
        self.lock = threading.Lock()
        self.bids: List[Tuple[float, float]] = []
        self.asks: List[Tuple[float, float]] = []
        self.connected = False
        self._stop = False
        self._thread: Optional[threading.Thread] = None
        self.last_update_ts: float = 0.0
        self._ema_imbalance: float = 1.0
        self._ema_alpha: float = 0.08
        self._imb_history: deque = deque(maxlen=600)

    def start(self):
        self._stop = False
        self._seed_from_rest()
        self._thread = threading.Thread(target=self._run_loop, daemon=True)
        self._thread.start()

    def stop(self):
        self._stop = True

    def imbalance(self) -> float:
        with self.lock:
            return self._ema_imbalance

    def raw_imbalance(self) -> Tuple[float, float, float]:
        with self.lock:
            price = spot_tracker.latest() or 67000
            bid_vol = self._sum_volume(self.bids, price, DEPTH_RANGE_USD, "bid")
            ask_vol = self._sum_volume(self.asks, price, DEPTH_RANGE_USD, "ask")
            ratio = bid_vol / ask_vol if ask_vol > 0 else 99.0
            return bid_vol, ask_vol, ratio

    def bid_walls(self) -> List[Tuple[float, float]]:
        with self.lock:
            return [(p, q) for p, q in self.bids if q >= WALL_MIN_BTC]

    def ask_walls(self) -> List[Tuple[float, float]]:
        with self.lock:
            return [(p, q) for p, q in self.asks if q >= WALL_MIN_BTC]

    def depth_momentum(self, window_sec: int = 30) -> Optional[float]:
        now = time.time()
        with self.lock:
            if len(self._imb_history) < 5:
                return None
            current = self._ema_imbalance
            target_ts = now - window_sec
            past_imb = None
            for ts, imb in self._imb_history:
                if ts <= target_ts:
                    past_imb = imb
                else:
                    break
            if past_imb is None:
                oldest_ts = self._imb_history[0][0]
                if (now - oldest_ts) < (window_sec * 0.3):
                    return None
                past_imb = self._imb_history[0][1]
            return current - past_imb

    def nearest_wall(self, direction: str) -> Tuple[Optional[float], Optional[float], str]:
        with self.lock:
            if direction == "UP":
                walls = [(p, q) for p, q in self.bids if q >= WALL_MIN_BTC]
                if walls:
                    best = max(walls, key=lambda x: x[0])
                    return best[0], best[1], f"BID_WALL ${best[0]:,.0f} ({best[1]:.1f}BTC)"
                return None, None, "no bid walls"
            elif direction == "DN":
                walls = [(p, q) for p, q in self.asks if q >= WALL_MIN_BTC]
                if walls:
                    best = min(walls, key=lambda x: x[0])
                    return best[0], best[1], f"ASK_WALL ${best[0]:,.0f} ({best[1]:.1f}BTC)"
                return None, None, "no ask walls"
        return None, None, "unknown"

    def cumulative_depth(self, direction: str, levels: int = 5) -> Tuple[float, str]:
        with self.lock:
            if direction == "UP":
                sorted_levels = sorted(self.bids, key=lambda x: x[0], reverse=True)[:levels]
            else:
                sorted_levels = sorted(self.asks, key=lambda x: x[0])[:levels]
            total = sum(q for _, q in sorted_levels)
            return total, f"CUM_{direction}({levels}L)={total:.1f}BTC"

    def book_score(self, direction: str) -> Tuple[float, str]:
        score = 0.0
        reasons = []
        bid_vol, ask_vol, _ = self.raw_imbalance()
        # 1. WALL (0-40)
        wall_price, wall_size, wall_desc = self.nearest_wall(direction)
        if wall_price is not None:
            wall_pts = min(40, wall_size * 5)
            score += wall_pts
            reasons.append(f"WALL={wall_pts:.0f}({wall_desc})")
        # 2. CUMULATIVE DEPTH (0-30)
        cum_vol, _ = self.cumulative_depth(direction, levels=5)
        opp_vol, _ = self.cumulative_depth("DN" if direction == "UP" else "UP", levels=5)
        if opp_vol > 0:
            depth_ratio = cum_vol / opp_vol
        else:
            depth_ratio = cum_vol * 10 if cum_vol > 0 else 0
        depth_pts = min(30, depth_ratio * 7.5) if depth_ratio > 1.0 else 0
        if depth_pts > 0:
            score += depth_pts
            reasons.append(f"DEPTH={depth_pts:.0f}")
        # 3. VOLUME DOMINANCE (0-15)
        if direction == "UP":
            vol_ratio = bid_vol / ask_vol if ask_vol > 0.1 else bid_vol * 5
        else:
            vol_ratio = ask_vol / bid_vol if bid_vol > 0.1 else ask_vol * 5
        vol_pts = min(15, max(0, (vol_ratio - 1.0) * 7.5))
        if vol_pts > 0:
            score += vol_pts
            reasons.append(f"VOL={vol_pts:.0f}")
        # 4. MOMENTUM (0-15)
        mom = self.depth_momentum(60)
        if mom is not None:
            if (direction == "UP" and mom > 0) or (direction == "DN" and mom < 0):
                mom_pts = min(15, abs(mom) * 5)
                score += mom_pts
                reasons.append(f"MOM={mom_pts:.0f}")
        reason_str = " | ".join(reasons) if reasons else "no signals"
        return score, f"SCORE={score:.0f}/100 [{reason_str}]"

    def has_wall_support(self, direction: str) -> Tuple[bool, str]:
        score, reason = self.book_score(direction)
        min_score = MIN_BOOK_SCORE
        if score >= min_score:
            return True, reason
        return False, f"WEAK {reason} (need {min_score:.0f})"

    def _sum_volume(self, levels, current_price, range_usd, side):
        total = 0.0
        for price, qty in levels:
            if side == "bid" and price >= (current_price - range_usd):
                total += qty
            elif side == "ask" and price <= (current_price + range_usd):
                total += qty
        return total

    def _update_book(self, bids_raw, asks_raw):
        new_bids = []
        new_asks = []
        for b in (bids_raw or []):
            try:
                p, q = float(b[0]), float(b[1])
                if q > 0:
                    new_bids.append((p, q))
            except (IndexError, ValueError):
                pass
        for a in (asks_raw or []):
            try:
                p, q = float(a[0]), float(a[1])
                if q > 0:
                    new_asks.append((p, q))
            except (IndexError, ValueError):
                pass
        new_bids.sort(key=lambda x: x[0], reverse=True)
        new_asks.sort(key=lambda x: x[0])
        price = spot_tracker.latest() or 67000
        bid_vol = self._sum_volume(new_bids, price, DEPTH_RANGE_USD, "bid")
        ask_vol = self._sum_volume(new_asks, price, DEPTH_RANGE_USD, "ask")
        raw_ratio = bid_vol / ask_vol if ask_vol > 0 else 99.0
        with self.lock:
            self.bids = new_bids
            self.asks = new_asks
            self.last_update_ts = time.time()
            clamped = max(0.05, min(20.0, raw_ratio))
            self._ema_imbalance = self._ema_alpha * clamped + (1 - self._ema_alpha) * self._ema_imbalance
            self._imb_history.append((time.time(), self._ema_imbalance))

    def _seed_from_rest(self):
        try:
            r = requests.get(BINANCE_DEPTH_REST, timeout=5)
            data = r.json()
            self._update_book(data.get("bids", []), data.get("asks", []))
            print(f"🟢 Binance depth seeded: imbalance={self.imbalance():.2f}")
        except Exception as e:
            print(f"⚠️ Depth REST seed failed: {e}")

    def _rest_refresh_loop(self):
        while not self._stop:
            time.sleep(DEPTH_REST_REFRESH_SEC)
            try:
                r = requests.get(BINANCE_DEPTH_REST, timeout=3)
                if r.status_code == 200:
                    self._update_book(r.json().get("bids", []), r.json().get("asks", []))
            except Exception:
                pass

    def _run_loop(self):
        threading.Thread(target=self._rest_refresh_loop, daemon=True).start()
        while not self._stop:
            try:
                self._connect_ws()
            except Exception as e:
                print(f"⚠️ Depth WS error: {e}")
            if not self._stop:
                time.sleep(2)

    def _connect_ws(self):
        def on_open(ws):
            self.connected = True
            print("🟢 Binance depth WS connected")

        def on_message(ws, message):
            try:
                data = json.loads(message)
                bids = data.get("bids") or data.get("b")
                asks = data.get("asks") or data.get("a")
                if bids is not None and asks is not None:
                    self._update_book(bids, asks)
            except Exception:
                pass

        def on_error(ws, error):
            self.connected = False

        def on_close(ws, code, msg):
            self.connected = False

        ws = websocket.WebSocketApp(
            BINANCE_DEPTH_WS_URL, on_open=on_open, on_message=on_message,
            on_error=on_error, on_close=on_close,
        )
        ws.run_forever(sslopt={"cert_reqs": ssl.CERT_NONE}, ping_interval=20, ping_timeout=10)


binance_depth = BinanceDepth()


# ================================================================
#  v5.3: MM TRACKER — Market Maker Activity Detection
# ================================================================
#
#  Lo que ves en la imagen de Polymarket:
#    - UP ask 99.9¢ × 186 acciones  (thin ask = MM listo para vender caro)
#    - Bids acumulados 99¢→95¢ con $3k-$5k por nivel (pared de liquidez)
#    - Spread de 0.9¢ = MM activo manteniendo mercado
#
#  Comportamientos detectables:
#
#  MM_ACCUMULATE: El MM está comprando silenciosamente.
#    Señales en el libro de Polymarket:
#    - Bids del token se engrosaron sin movimiento de spot (absorción silenciosa)
#    - Spread se comprimió (MM acercó bid hacia ask)
#    - Liquidez acumulada en bids creció > X USDC en la última lectura
#
#  MM_DISTRIBUTE: El MM está vendiendo / descargando posición.
#    Señales:
#    - Asks del token se engrosaron
#    - Spread se amplió (MM alejó bid)
#    - Ask wall grande apareció cerca del precio actual
#
#  MM_SPOOF: El MM pone una pared grande y la retira.
#    Señales:
#    - Pared de bid/ask > MM_WALL_USDC apareció y desapareció en < MM_SPOOF_SEC
#    - Precio no se movió con la pared (pared era falsa)
#
#  Uso en Peak Reversion:
#    Si cheap_direction == "UP" y MM_ACCUMULATE en token UP → +2 puntos
#    (el MM está acumulando el token barato = señal fuerte de reversión)
#
class MMTracker:
    """
    Rastrea la actividad del market maker en el libro de órdenes de Polymarket.
    Analiza el WS feed que ya recibe el bot para inferir comportamiento MM.
    """

    def __init__(self):
        self.lock = threading.Lock()
        # Historial de snapshots del libro por token: deque de (ts, bid_liq, ask_liq, spread)
        self._history: Dict[str, deque] = {}
        # Paredes detectadas: token → deque de (ts, side, price, usdc)
        self._walls: Dict[str, deque] = {}
        # Estado actual del tracker por token
        self._state: Dict[str, str] = {}   # "ACCUMULATE" / "DISTRIBUTE" / "NEUTRAL"
        self._mm_score: Dict[str, int] = {}  # -3 a +3 por token
        self._reversal_hint: Dict[str, bool] = {}  # True = MM virando contra tendencia spot

        # Parámetros (leídos de env en primera llamada)
        self._wall_usdc     = float(os.getenv("MM_WALL_USDC",       "500"))   # pared significativa en USDC
        self._spoof_sec     = float(os.getenv("MM_SPOOF_SEC",        "8"))    # segundos para detectar spoof
        self._liq_window    = float(os.getenv("MM_LIQ_WINDOW_SEC",   "30"))   # ventana de análisis
        self._spread_comp   = float(os.getenv("MM_SPREAD_COMPRESS",  "0.005"))# spread comprimido (< 0.5¢)
        self._accum_delta   = float(os.getenv("MM_ACCUM_DELTA_USDC", "200"))  # crecimiento bid liq para acumulación

    def _ensure_token(self, token_id: str):
        if token_id not in self._history:
            self._history[token_id]       = deque(maxlen=120)
            self._walls[token_id]         = deque(maxlen=30)
            self._state[token_id]         = "NEUTRAL"
            self._mm_score[token_id]      = 0
            self._reversal_hint[token_id] = False

    def update(self, token_id: str, bid: Optional[float], ask: Optional[float],
               bid_liq: float, ask_liq: float):
        """
        Llamar en cada tick del WS con bid/ask actuales y liquidez top-3.
        bid_liq / ask_liq = USDC en los primeros 3 niveles del libro de Polymarket.
        """
        if bid is None or ask is None:
            return
        with self.lock:
            self._ensure_token(token_id)
            now    = time.time()
            spread = ask - bid
            snap   = (now, bid_liq, ask_liq, spread, bid, ask)
            self._history[token_id].append(snap)

            # Detectar paredes nuevas (liquidez > MM_WALL_USDC en un nivel)
            if bid_liq >= self._wall_usdc:
                self._walls[token_id].append((now, "BID", bid, bid_liq))
            if ask_liq >= self._wall_usdc:
                self._walls[token_id].append((now, "ASK", ask, ask_liq))

            self._analyze(token_id)

    def _analyze(self, token_id: str):
        """Analiza historial reciente y actualiza state/score. Llamar con lock tomado."""
        hist = self._history[token_id]
        if len(hist) < 4:
            return

        now    = time.time()
        window = [s for s in hist if now - s[0] <= self._liq_window]
        if len(window) < 3:
            return

        # Métricas recientes
        latest     = window[-1]
        oldest_w   = window[0]
        _, bid_liq_now, ask_liq_now, spread_now, bid_now, ask_now = latest
        _, bid_liq_old, ask_liq_old, spread_old, _, _             = oldest_w

        bid_delta  = bid_liq_now - bid_liq_old   # positivo = más liquidez en bids
        ask_delta  = ask_liq_now - ask_liq_old
        spread_avg = sum(s[3] for s in window) / len(window)

        score = 0
        signals = []

        # ── Señal 1: Absorción silenciosa (bid creció, spread comprimido) ────
        if bid_delta > self._accum_delta and spread_now < self._spread_comp:
            score += 2
            signals.append(f"SILENT_ACCUM bid+{bid_delta:.0f}USDC sprd={spread_now:.4f}")
        elif bid_delta > self._accum_delta * 0.5:
            score += 1
            signals.append(f"BID_GROWING +{bid_delta:.0f}USDC")

        # ── Señal 2: Distribución (ask creció, spread ampliado) ─────────────
        if ask_delta > self._accum_delta and spread_now > spread_avg * 1.5:
            score -= 2
            signals.append(f"DISTRIBUTING ask+{ask_delta:.0f}USDC sprd_wide={spread_now:.4f}")
        elif ask_delta > self._accum_delta * 0.5:
            score -= 1
            signals.append(f"ASK_GROWING +{ask_delta:.0f}USDC")

        # ── Señal 3: Spoof detection (pared apareció y desapareció) ─────────
        walls = self._walls[token_id]
        recent_walls = [w for w in walls if now - w[0] <= self._spoof_sec * 3]
        bid_walls_gone = sum(1 for w in recent_walls
                             if w[1] == "BID" and now - w[0] > self._spoof_sec
                             and bid_liq_now < w[3] * 0.3)
        ask_walls_gone = sum(1 for w in recent_walls
                             if w[1] == "ASK" and now - w[0] > self._spoof_sec
                             and ask_liq_now < w[3] * 0.3)
        if bid_walls_gone > 0:
            # Bid wall desapareció → era spoof alcista → presión real es bajista
            score -= 1
            signals.append(f"BID_SPOOF_DETECTED ({bid_walls_gone} walls gone)")
        if ask_walls_gone > 0:
            score += 1
            signals.append(f"ASK_SPOOF_DETECTED ({ask_walls_gone} walls gone)")

        # ── Señal 4: Spread muy comprimido = MM activo, espera dirección ────
        if spread_now < self._spread_comp * 0.5:
            score = max(score, 1) if score >= 0 else score
            signals.append(f"TIGHT_SPREAD {spread_now:.4f} (MM active)")

        # Clampear score
        score = max(-3, min(3, score))
        self._mm_score[token_id]  = score
        self._state[token_id]     = ("ACCUMULATE" if score > 0 else
                                     "DISTRIBUTE" if score < 0 else "NEUTRAL")

    def score(self, token_id: str) -> int:
        """Score MM: +3=fuerte acumulación, -3=fuerte distribución, 0=neutral."""
        with self.lock:
            return self._mm_score.get(token_id, 0)

    def state(self, token_id: str) -> str:
        with self.lock:
            return self._state.get(token_id, "NEUTRAL")

    def reversal_hint(self, token_id: str, cheap_direction: str,
                      spot_peak_direction: str) -> Tuple[bool, str]:
        """
        Devuelve (True, razón) si el comportamiento MM sugiere reversión.

        Lógica:
          Si spot fue UP (spot_peak_direction="UP") → el token UP está caro,
          el token DN está barato. Queremos comprar DN.
          Si el MM está ACUMULANDO el token DN → señal fuerte: el MM sabe que
          el precio va a subir de vuelta → DN va a recuperar → reversión.

          Si spot fue DN → token UP barato.
          Si MM acumula UP → reversión alcista probable.
        """
        with self.lock:
            self._ensure_token(token_id)
            sc    = self._mm_score.get(token_id, 0)
            state = self._state.get(token_id, "NEUTRAL")

        # MM acumulando el token barato = señal de reversión fuerte
        if cheap_direction == "UP" and sc > 0:
            return True, f"MM_ACCUM_UP score={sc} state={state}"
        if cheap_direction == "DN" and sc > 0:
            return True, f"MM_ACCUM_DN score={sc} state={state}"

        # MM distribuyendo el token barato = confirma que el movimiento continúa (NO reversar)
        if cheap_direction == "UP" and sc < 0:
            return False, f"MM_DIST_UP (score={sc}) — MM selling cheap side, no reversal"
        if cheap_direction == "DN" and sc < 0:
            return False, f"MM_DIST_DN (score={sc}) — MM selling cheap side, no reversal"

        return False, f"MM_NEUTRAL (score={sc})"

    def diag_str(self, tokens: list) -> str:
        parts = []
        with self.lock:
            for tok in tokens[:2]:
                sc    = self._mm_score.get(tok, 0)
                state = self._state.get(tok, "?")
                label = tok[-6:] if len(tok) > 6 else tok
                bar   = ("+" * sc if sc > 0 else "-" * abs(sc)) or "="
                parts.append(f"{label}:{state[:5]}({bar})")
        return "MM[" + " | ".join(parts) + "]" if parts else "MM[no data]"


mm_tracker = MMTracker()


class S:
    slug: Optional[str] = None
    end_time = None
    start_time = None
    tokens: List[str] = []
    tick = 0.01
    book: Dict[str, Dict[str, Any]] = {}

    last_diag_ts = 0.0
    last_balance_ts = 0.0
    last_ws_msg_ts = 0.0
    ws_open_ts = 0.0

    last_known_balance: Optional[float] = None
    last_known_allowance: Optional[float] = None
    last_balance_src: str = ""
    last_balance_sig_used: Optional[int] = None

    orders_sent = 0
    last_order_ts = 0.0
    last_buy_fail_ts = 0.0  # FIX BUY-RETRY ANTI-CHASE (2026-04-26)

    position_token: Optional[str] = None
    position_label: Optional[str] = None
    position_size: float = 0.0
    entry_price: float = 0.0
    entry_ts: float = 0.0
    peak_price: float = 0.0
    trail_active: bool = False

    last_sell_fail_ts: float = 0.0
    sell_fail_count: int = 0

    # MULTI-ROUND CONFIRMATION (2026-05-05): 
    # Validar señal entre DOS rounds DISTINTOS de Chainlink (no entre lecturas DIAG).
    # Round 1: primera vez que se detecta señal válida → guardar
    # Round 2: cuando Chainlink hace nuevo update (cl_price cambia) → comparar
    # Validar: CL Δ creció + precio token subió proporcionalmente.
    confirm_signal: Optional[str] = None      # "TREND_UP" o "TREND_DN" — señal en seguimiento
    confirm_cl_price: Optional[float] = None  # precio CL del round en que se detectó (para detectar new round)
    confirm_cl_delta: Optional[float] = None  # CL Δ inicial
    confirm_side_price: Optional[float] = None  # precio del lado en lectura inicial
    confirm_time_left: Optional[float] = None  # segundos restantes en lectura inicial
    confirm_slug: Optional[str] = None        # slug del mercado actual (reset al cambiar mercado)

    # FIX 2026-06-04: snapshot del precio Chainlink EXACTO al cierre del mercado,
    # usado por _check_resolution_onchain para determinar win/loss real comparando
    # con el PTB de apertura (en vez del precio actual ya movido).
    _cl_close_snapshot: Optional[float] = None

    day_utc: Optional[date] = None
    pnl_usdc: float = 0.0
    trading_enabled: bool = True
    paused_by_telegram: bool = False   # pausa manual via Telegram ("pausa"/"start")
    trading_disabled_ts: float = 0.0

    overreaction_detected: bool = False
    _pullback_info: str = ""
    overreaction_direction: str = ""
    overreaction_magnitude: float = 0.0
    entry_win_chg: float = 0.0
    entry_cl_delta: Optional[float] = None  # v5.0: CL delta at entry
    is_trend_follow: bool = False  # v5.0: True if entered via TF signal
    is_peak_reversion: bool = False  # v5.2: True if entered via PR signal

    # v5.2: Peak Reversion tracking
    pr_entry_divergence_usd: float = 0.0   # $ divergence from PTB at time of entry
    pr_peak_divergence_usd:  float = 0.0   # maximum $ divergence seen before entry
    pr_spot_ptb:             float = 0.0   # spot PTB at window start (Binance)
    pr_peak_trail:           float = 0.0   # peak token price seen since entry (for trail)
    pr_trail_active:         bool  = False

    window_history: List[Tuple] = []
    condition_id: Optional[str] = None

    # Progressive sizing state
    consecutive_losses: int = 0
    _balance_at_last_loss: Optional[float] = None  # balance al ocurrir la última pérdida
    _pending_resolution: bool = False   # posición cerró sin confirmar resultado — esperar claim
    _pending_resolution_bal: float = 0.0  # balance al momento de quedar pendiente
    cycles_to_wait: int = 0    # ciclos restantes de espera tras pérdida antes de entrar
    cycles_waited:  int = 0    # ciclos ya esperados en el bloqueo actual
    cl_reverse_count: int = 0        # cuántas veces revirtió CL en el ciclo actual
    last_cl_reverse_dir: Optional[str] = None  # dirección de la última reversión
    dynamic_base: float = 0.0        # base actual (sube 30% cada +30% balance)
    dynamic_base_next_lvl: float = 0.0  # balance necesario para próximo escalado
    loss_pause_until: float = 0.0  # timestamp when pause ends
    ptb_override: Optional[float] = None    # PTB manual enviado por Telegram
    ptb_override_until: float = 0.0         # ventana de espera activa hasta este ts
    tg_last_update_id: int = 0              # último update_id procesado de Telegram

    # v5.9: PTB shift tracking
    ptb_shift_ts: float = 0.0               # timestamp del último PTB shift mid-cycle
    ptb_shift_delta: float = 0.0            # magnitud del último shift ($)
    ptb_override_diff: float = 0.0          # diff del override al inicio del ciclo
    is_ptb_shift_entry: bool = False        # True si entró por PTB shift (TP más rápido)

    # v5.13: Whale accumulation state
    whale_p1_done: bool = False
    whale_p2_done: bool = False
    whale_p3_done: bool = False
    whale_p1_last_try: float = 0.0
    whale_p2_last_try: float = 0.0
    whale_p3_last_try: float = 0.0
    whale_spent_up: float = 0.0
    whale_spent_dn: float = 0.0
    whale_buys: list = []  # [(phase, side, price, amount, ts)]

    # v5.15: Straddle state
    straddle_last_buy_ts: float = 0.0
    straddle_rounds: int = 0        # buy-both-sides rounds this window
    straddle_spent_up: float = 0.0
    straddle_spent_dn: float = 0.0
    straddle_shares_up: float = 0.0
    straddle_shares_dn: float = 0.0
    straddle_sold_up: bool = False   # already took profit on UP
    straddle_sold_dn: bool = False   # already took profit on DN
    straddle_merged_profit: float = 0.0  # realized profit from merges this window
    # v5.18 PATCH 3: state para anti-piramidación (inicializado perezoso via hasattr/setattr)
    cl_delta_history: List[Tuple[float, float]] = []   # [(ts, cl_delta), ...] últimos 60s
    last_buy_side: Optional[str] = None                # "UP" | "DN" | None del último BUY exitoso
    # v5.18 HOTFIX PATCH 1: evitar falsos positivos de "Large drift" por lag RPC
    last_successful_buy_ts: float = 0.0                # timestamp del último BUY exitoso
    large_drift_strikes: int = 0                       # contador de ticks consecutivos con large drift


# ================================================================
#  HELPERS
# ================================================================
def safe_float(x, default=None):
    try:
        return float(x)
    except Exception:
        return default


def now_utc():
    return datetime.now(timezone.utc)


def parse_iso_z(s):
    if not s:
        return None
    if isinstance(s, (int, float)):
        try:
            return datetime.fromtimestamp(float(s), tz=timezone.utc)
        except Exception:
            return None
    if not isinstance(s, str):
        return None
    if s.endswith("Z"):
        s = s[:-1] + "+00:00"
    try:
        return datetime.fromisoformat(s).astimezone(timezone.utc)
    except Exception:
        return None


def round_down_to_window_epoch(ts):
    return ts - (ts % WINDOW_SECONDS)


def compute_slug(epoch_bucket):
    return f"{BASE_SLUG_PREFIX}{epoch_bucket}"


def tg_send(text):
    if not (TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID):
        return
    # ----------------------------------------------------------------
    # NOTIFICATION FILTER (2026-04-30)
    # Solo deja pasar mensajes en TG_ALLOW_TRIGGERS.
    # Para reactivar TODOS los mensajes: export TG_VERBOSE=1
    # ----------------------------------------------------------------
    TG_VERBOSE = os.getenv("TG_VERBOSE", "0") == "1"
    if not TG_VERBOSE:
        TG_ALLOW_TRIGGERS = [
            "TF BUY",                # 🚀 TF BUY UP/DN — compra ejecutada
            "Bot SNIPER listo",      # 1 mensaje al arrancar
            "PTB watcher aplicado",  # 🤖 PTB watcher aplicado
            "Bot REANUDADO",         # ▶️ Bot REANUDADO
            "Bot en STAND-BY",       # ⏸️ Bot en STAND-BY
            "PTB actualizado",       # ✅ PTB actualizado a $...
            "Nuevo ciclo",           # 🕐 Nuevo ciclo | inicio de cada mercado
        ]
        if not any(trig in text for trig in TG_ALLOW_TRIGGERS):
            return  # silenciar todo lo demás
    try:
        base = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"
        params = {"chat_id": TELEGRAM_CHAT_ID, "text": text, "disable_web_page_preview": "true"}
        requests.get(base + "?" + urllib.parse.urlencode(params), timeout=8)
    except Exception:
        pass


PTB_OVERRIDE_WINDOW_SEC = float(os.getenv("PTB_OVERRIDE_WINDOW_SEC", "30"))  # segundos esperando respuesta


def tg_get_updates() -> list:
    """Obtiene mensajes nuevos del bot de Telegram (long poll corto)."""
    if not (TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID):
        return []
    try:
        url    = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/getUpdates"
        params = {
            "offset":  S.tg_last_update_id + 1,
            "timeout": 2,   # poll corto — no bloqueante
            "limit":   10,
        }
        r = requests.get(url, params=params, timeout=5)
        data = r.json()
        updates = data.get("result", [])
        if updates:
            S.tg_last_update_id = updates[-1]["update_id"]
        return updates
    except Exception:
        return []


def tg_check_ptb_override(after_ts: float) -> Optional[float]:
    """
    Revisa si el usuario respondió con un precio de PTB.
    SOLO acepta mensajes cuyo timestamp sea posterior a after_ts —
    evita que respuestas de ciclos anteriores contaminen el PTB actual.
    """
    updates = tg_get_updates()
    for upd in updates:
        msg = upd.get("message") or upd.get("edited_message", {})
        if not msg:
            continue
        # Solo mensajes del chat correcto
        chat_id = str(msg.get("chat", {}).get("id", ""))
        if chat_id != str(TELEGRAM_CHAT_ID):
            continue
        # Solo mensajes enviados DESPUÉS de que abrió este ciclo
        msg_ts = msg.get("date", 0)
        if msg_ts <= after_ts:
            continue  # mensaje viejo — ignorar
        text = (msg.get("text") or "").strip().replace(",", "").replace("$", "")
        try:
            val = float(text)
            if 10_000 <= val <= 200_000:
                return val
        except (ValueError, TypeError):
            pass
    return None


def wait_for_ptb_override(default_ptb: float, cycle_open_str: str) -> float:
    """
    Espera PTB_OVERRIDE_WINDOW_SEC segundos por una respuesta.
    Acepta el PTB desde dos fuentes:
      1. Mensaje de Telegram del usuario
      2. Archivo /tmp/ptb_override.txt escrito por ptb_watcher
    """
    if not (TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID):
        return default_ptb

    PTB_FILE = "/tmp/ptb_override.txt"

    # Limpiar archivo anterior para este ciclo
    try:
        import os as _os
        if _os.path.exists(PTB_FILE):
            _os.remove(PTB_FILE)
    except Exception:
        pass

    request_ts = int(time.time())
    deadline   = time.time() + PTB_OVERRIDE_WINDOW_SEC
    print(f"⏳ Esperando confirmación PTB por {PTB_OVERRIDE_WINDOW_SEC:.0f}s "
          f"(responde con el precio correcto o ignora)")

    while time.time() < deadline:
        # Fuente 1: archivo escrito por ptb_watcher
        try:
            import os as _os
            if _os.path.exists(PTB_FILE):
                with open(PTB_FILE) as f:
                    val = float(f.read().strip())
                if 10_000 <= val <= 200_000:
                    diff = val - default_ptb
                    print(f"✅ PTB override (watcher): ${val:,.2f} "
                          f"(diff={diff:+.2f} vs predeterminado ${default_ptb:,.2f})")
                    tg_send(f"🤖 PTB watcher aplicado: ${val:,.2f} "
                            f"(diff={diff:+.2f} vs calculado ${default_ptb:,.2f})")
                    _os.remove(PTB_FILE)
                    return val
        except Exception:
            pass

        # Fuente 2: mensaje manual de Telegram
        override = tg_check_ptb_override(after_ts=request_ts)
        if override is not None:
            diff = override - default_ptb
            print(f"✅ PTB override recibido: ${override:,.2f} "
                  f"(diff={diff:+.2f} vs predeterminado ${default_ptb:,.2f})")
            tg_send(f"✅ PTB actualizado a ${override:,.2f} "
                    f"(diff={diff:+.2f} vs calculado ${default_ptb:,.2f})")
            return override

        time.sleep(3)

    print(f"⏱️ Sin respuesta — usando PTB predeterminado: ${default_ptb:,.2f}")
    return default_ptb


_last_ptb_poll_ts = 0.0

def check_mid_cycle_ptb():
    """
    v5.9: PTB Shift Detection — revisa si el watcher envió un PTB nuevo mid-cycle.

    Cuando Polymarket recalcula el PTB durante un ciclo (o el watcher captura
    un PTB diferente), los tokens no se reprecian instantáneamente. Esto crea
    una ventana de 10-60 segundos donde el token está subvaluado vs el nuevo PTB.

    El bot detecta el shift, recalcula CL delta, y puede entrar inmediatamente
    para capturar el repricing (PTB_SHIFT fast-track en pick_signal_trend_follow).
    """
    global _last_ptb_poll_ts
    if not PTB_SHIFT_ENABLED:
        return

    now = time.time()
    if now - _last_ptb_poll_ts < PTB_SHIFT_POLL_SEC:
        return
    _last_ptb_poll_ts = now

    PTB_FILE = "/tmp/ptb_override.txt"
    try:
        if not os.path.exists(PTB_FILE):
            return
        with open(PTB_FILE) as f:
            val = float(f.read().strip())
        if not (10_000 <= val <= 200_000):
            return

        current_ptb = chainlink_feed.price_to_beat()
        if current_ptb is None:
            return

        diff = val - current_ptb
        abs_diff = abs(diff)

        if abs_diff < 5:  # ruido — ignorar
            return

        # Aplicar el nuevo PTB
        old_ptb = current_ptb
        with chainlink_feed.lock:
            chainlink_feed._price_to_beat = val
            chainlink_feed._price_to_beat_ts = now
        os.remove(PTB_FILE)

        # Registrar el shift
        S.ptb_shift_ts = now
        S.ptb_shift_delta = abs_diff
        S.ptb_override_diff = abs_diff

        print(f"⚡ PTB SHIFT mid-cycle: ${old_ptb:,.0f} → ${val:,.0f} (diff=${diff:+.0f})")
        tg_send(f"⚡ PTB shift: ${old_ptb:,.0f}→${val:,.0f} (${diff:+.0f})")

    except Exception:
        pass


def http_get_json(url, params=None, timeout=10):
    r = requests.get(url, params=params, timeout=timeout)
    r.raise_for_status()
    return r.json()


def tg_check_commands():
    """
    Revisa mensajes de Telegram buscando comandos de control del bot.
    Llamar desde el watchdog loop cada ~10s.

    Comandos reconocidos (case-insensitive):
      "pausa" | "pause" | "stop"  → bot entra en stand-by, no abre nuevas posiciones
      "start" | "resume" | "go"   → bot sale del stand-by y reanuda operación normal

    Si hay una posición abierta al pausar, la sigue monitoreando hasta que cierre.
    """
    if not (TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID):
        return

    updates = tg_get_updates()
    for upd in updates:
        msg = upd.get("message") or upd.get("edited_message", {})
        if not msg:
            continue
        chat_id = str(msg.get("chat", {}).get("id", ""))
        if chat_id != str(TELEGRAM_CHAT_ID):
            continue
        text = (msg.get("text") or "").strip().lower()
        if not text:
            continue

        if text in ("pausa", "pause", "stop", "pausar"):
            if not S.paused_by_telegram:
                S.paused_by_telegram = True
                _save_sizing_state()  # persistir pausa
                pos_info = (f" | Posición abierta en {S.position_label} — la sigo monitoreando"
                            if S.position_token else " | Sin posición abierta")
                print(f"⏸️ BOT PAUSADO por Telegram{pos_info}")
                tg_send(
                    f"⏸️ Bot en STAND-BY\n"
                    f"No abriré nuevas posiciones hasta que digas 'start'.\n"
                    + (f"Posición actual {S.position_label} @ {S.entry_price:.2f} sigue activa."
                       if S.position_token else "Sin posición activa.")
                )

        elif text in ("start", "resume", "go", "continuar", "reanudar"):
            if S.paused_by_telegram:
                S.paused_by_telegram = False
                _save_sizing_state()  # persistir reanudación
                print(f"▶️ BOT REANUDADO por Telegram")
                tg_send(
                    f"▶️ Bot REANUDADO — buscando señales normalmente.\n"
                    f"Balance: ${S.last_known_balance:.2f}" if S.last_known_balance else
                    f"▶️ Bot REANUDADO — buscando señales normalmente."
                )


def clamp_price(p, tick, lo, hi):
    tick = tick or 0.01
    p = max(lo + PRICE_EPS_TICKS * tick, min(hi - PRICE_EPS_TICKS * tick, p))
    steps = round(p / tick)
    p2 = steps * tick
    p2 = max(lo + PRICE_EPS_TICKS * tick, min(hi - PRICE_EPS_TICKS * tick, p2))
    return float(f"{p2:.6f}")


def is_within_trading_hours() -> bool:
    """
    v5.9: Check if current UTC hour is within TRADING_HOURS_UTC ranges.
    Format: "HH-HH,HH-HH" e.g. "08-11,22-01"
    Range "22-01" wraps around midnight (22,23,0).
    Empty string = always allowed (24/7).
    """
    if not TRADING_HOURS_UTC:
        return True
    current_hour = now_utc().hour
    for rng in TRADING_HOURS_UTC.split(","):
        rng = rng.strip()
        if "-" not in rng:
            continue
        parts = rng.split("-")
        try:
            start_h = int(parts[0])
            end_h = int(parts[1])
        except ValueError:
            continue
        if start_h <= end_h:
            if start_h <= current_hour < end_h:
                return True
        else:  # wraps midnight: e.g. 22-02 = 22,23,0,1
            if current_hour >= start_h or current_hour < end_h:
                return True
    return False


def daily_rollover():
    d = now_utc().date()
    if S.day_utc != d:
        S.day_utc = d
        S.pnl_usdc = 0.0
        S.trading_enabled = True


def maybe_disable_trading():
    if not S.trading_enabled and LOSS_COOLDOWN_SEC > 0 and S.trading_disabled_ts > 0:
        elapsed = time.time() - S.trading_disabled_ts
        if elapsed >= LOSS_COOLDOWN_SEC:
            S.trading_enabled = True
            S.pnl_usdc = 0.0
            S.trading_disabled_ts = 0.0
            msg = f"🔄 Trading RESUMED after {LOSS_COOLDOWN_SEC/3600:.1f}h cooldown."
            print(msg)
            tg_send(msg)
            return
    if DAILY_LOSS_LIMIT_USDC > 0 and S.pnl_usdc <= -abs(DAILY_LOSS_LIMIT_USDC):
        if S.trading_enabled:
            S.trading_disabled_ts = time.time()
            msg = f"🛑 Trading OFF: loss limit ${DAILY_LOSS_LIMIT_USDC:.0f}. pnl={S.pnl_usdc:.2f}"
            print(msg)
            tg_send(msg)
        S.trading_enabled = False
    if DAILY_PROFIT_TARGET_USDC > 0 and S.pnl_usdc >= abs(DAILY_PROFIT_TARGET_USDC):
        if S.trading_enabled:
            S.trading_disabled_ts = time.time()
            msg = f"✅ Trading OFF: daily profit target. pnl={S.pnl_usdc:.2f}"
            print(msg)
            tg_send(msg)
        S.trading_enabled = False


# ================================================================
#  GAMMA MARKET FETCH
# ================================================================
def gamma_get_market_by_slug(slug):
    url1 = f"{GAMMA_HOST}/markets/slug/{slug}"
    try:
        data = http_get_json(url1, timeout=10)
        if isinstance(data, dict) and data.get("slug"):
            return data
    except Exception:
        pass
    url2 = f"{GAMMA_HOST}/markets"
    try:
        data = http_get_json(url2, params={"slug": slug}, timeout=10)
        if isinstance(data, list) and data and isinstance(data[0], dict):
            return data[0]
    except Exception:
        pass
    return None


def extract_token_ids(market):
    v = market.get("clobTokenIds")
    if isinstance(v, str):
        try:
            arr = json.loads(v)
            if isinstance(arr, list) and len(arr) >= 2:
                return [str(arr[0]), str(arr[1])]
        except Exception:
            pass
    if isinstance(v, list) and len(v) >= 2:
        return [str(v[0]), str(v[1])]
    for k in ("tokens", "outcomes"):
        vv = market.get(k)
        if isinstance(vv, list):
            ids = []
            for item in vv:
                if isinstance(item, dict):
                    for kk in ("clobTokenId", "clob_token_id", "token_id", "tokenId"):
                        if kk in item:
                            ids.append(str(item[kk]))
                            break
            if len(ids) >= 2:
                return ids[:2]
    return None


def market_tick(market):
    t = safe_float(market.get("orderPriceMinTickSize"), None)
    return t if t and t > 0 else 0.01


def market_title(market):
    return market.get("question") or market.get("title") or "(unknown)"


def market_end_time(market):
    return parse_iso_z(market.get("endDate") or market.get("end_date") or
                       market.get("closeTime") or market.get("close_time"))


def find_active_btc_15m_market():
    """
    Busca el mercado BTC 15m activo por slug exacto.
    La Gamma API no soporta filtrado por tags/groupSlug para estos mercados —
    la única forma confiable es construir el slug del epoch actual y buscarlo.
    Intenta el epoch actual y los dos adyacentes como fallback.
    """
    base_epoch = round_down_to_window_epoch(int(time.time()))
    for offset in [0, 1, -1, 2]:
        epoch = base_epoch + offset * WINDOW_SECONDS
        slug  = compute_slug(epoch)
        try:
            m = gamma_get_market_by_slug(slug)
            if not m:
                continue
            if not m.get("active"):
                print(f"⏭️ {slug}: active=False")
                continue
            if not extract_token_ids(m):
                print(f"⏭️ {slug}: sin clobTokenIds")
                continue
            if m.get("closed"):
                print(f"⏭️ {slug}: closed=True")
                continue
            print(f"✅ Mercado activo: {slug} (cierra {m.get('endDate','?')})")
            return m
        except Exception as e:
            print(f"⚠️ find_market error [{slug}]: {e}")
            continue
    return None


# ================================================================
#  L2 BALANCE / SIGNING
# ================================================================
def _creds_get(obj, key):
    if obj is None:
        return None
    if isinstance(obj, dict):
        return obj.get(key)
    if hasattr(obj, key):
        return getattr(obj, key)
    return None


def extract_l2_creds():
    if API_CREDS is None:
        raise RuntimeError("API_CREDS not ready.")
    api_key = _creds_get(API_CREDS, "api_key") or _creds_get(API_CREDS, "apiKey") or _creds_get(API_CREDS, "key")
    secret = _creds_get(API_CREDS, "api_secret") or _creds_get(API_CREDS, "apiSecret") or _creds_get(API_CREDS, "secret")
    passphrase = _creds_get(API_CREDS, "api_passphrase") or _creds_get(API_CREDS, "apiPassphrase") or _creds_get(API_CREDS, "passphrase")
    if not (api_key and secret and passphrase):
        raise RuntimeError("API_CREDS incomplete.")
    return str(api_key), str(secret), str(passphrase)


def _decode_secret(secret_str):
    s = secret_str.replace("-", "+").replace("_", "/")
    s = "".join(ch for ch in s if ch.isalnum() or ch in "+/=")
    return base64.b64decode(s)


def _b64url_from_b64(b64):
    return b64.replace("+", "-").replace("/", "_")


def build_poly_hmac_signature(secret_b64, timestamp, method, request_path_only, body=None):
    msg = f"{timestamp}{method.upper()}{request_path_only}"
    if body is not None:
        msg += body
    key = _decode_secret(secret_b64)
    digest = hmac.new(key, msg.encode("utf-8"), hashlib.sha256).digest()
    sig_b64 = base64.b64encode(digest).decode("utf-8")
    return _b64url_from_b64(sig_b64)


def l2_signed_get_balance(poly_address, query):
    api_key, secret, passphrase = extract_l2_creds()
    ts = int(time.time())
    path_only = "/balance-allowance"
    sig = build_poly_hmac_signature(secret, ts, "GET", path_only, None)
    headers = {
        "POLY_ADDRESS": poly_address, "POLY_SIGNATURE": sig,
        "POLY_TIMESTAMP": str(ts), "POLY_API_KEY": api_key,
        "POLY_PASSPHRASE": passphrase, "Content-Type": "application/json",
    }
    url = CLOB_HOST + path_only + "?" + query
    r = requests.get(url, headers=headers, timeout=10)
    if r.status_code >= 400:
        raise RuntimeError(f"GET {path_only}?{query} -> HTTP {r.status_code}: {r.text[:250]}")
    return r.json()


def _extract_balance_allowance(j):
    if isinstance(j, dict) and "balance" in j:
        return safe_float(j.get("balance"), None), safe_float(j.get("allowance"), None)
    if isinstance(j, dict) and isinstance(j.get("data"), dict) and "balance" in j["data"]:
        return safe_float(j["data"].get("balance"), None), safe_float(j["data"].get("allowance"), None)
    return None, None


def to_usdc_units(x):
    if x is None:
        return None
    if BALANCE_IS_BASE_UNITS in ("1", "true", "yes"):
        return x / (10 ** USDC_DECIMALS)
    if BALANCE_IS_BASE_UNITS in ("0", "false", "no"):
        return x
    # FIX 3: auto-detect base units.
    # Bug: threshold was 1_000_000 — a balance of $544,312 raw units = $0.54 USDC
    # but was NOT being converted because 544312 < 1_000_000.
    # Real USDC balances on Polymarket are rarely above $500.
    # If value >= 10_000 it's almost certainly base units (micro-USDC), convert it.
    return x / (10 ** USDC_DECIMALS) if x >= 10_000 else x


def maybe_update_balance():
    if time.time() - S.last_balance_ts < BALANCE_EVERY_SEC:
        return
    S.last_balance_ts = time.time()
    addrs = []
    if FUNDER_ADDRESS:
        addrs.append(FUNDER_ADDRESS)
    if SIGNER_ADDRESS and SIGNER_ADDRESS not in addrs:
        addrs.append(SIGNER_ADDRESS)
    if BALANCE_SIG_AUTODETECT:
        sigs = [int(x.strip()) for x in BALANCE_SIG_TRY.split(",") if x.strip().isdigit()]
        if ORDER_SIGNATURE_TYPE not in sigs:
            sigs.insert(0, ORDER_SIGNATURE_TYPE)
    else:
        sigs = [ORDER_SIGNATURE_TYPE]
    best = None
    for sig in sigs:
        q = f"asset_type=COLLATERAL&signature_type={sig}"
        for addr in addrs:
            try:
                j = l2_signed_get_balance(addr, q)
                bal_raw, allow_raw = _extract_balance_allowance(j)
                if bal_raw is None:
                    continue
                bal = to_usdc_units(float(bal_raw))
                allow = to_usdc_units(float(allow_raw)) if allow_raw is not None else None
                src = f"/balance-allowance?{q} | addr={addr}"
                if best is None or bal > best[0]:
                    best = (bal, allow, src, sig)
            except Exception:
                continue
    if best is not None:
        bal, allow, src, sig = best
        S.last_known_balance = bal
        S.last_known_allowance = allow
        S.last_balance_src = src
        S.last_balance_sig_used = sig
        if BALANCE_PRINT:
            print(f"💰 balance={bal:.4f} USDC | allowance={allow} | sig={sig}")
        return
    if S.last_known_balance is None:
        S.last_known_balance = BALANCE_FALLBACK_USDC
        S.last_known_allowance = None
        S.last_balance_src = "fallback"


def compute_trade_usdc():
    bal = S.last_known_balance if S.last_known_balance is not None else BALANCE_FALLBACK_USDC
    raw = bal * USE_BALANCE_PCT
    return float(f"{max(MIN_TRADE_USDC, min(MAX_TRADE_USDC, raw)):.4f}")


# ================================================================
#  ORDERBOOK HANDLING
# ================================================================
def _lvl_price(lvl):
    if isinstance(lvl, dict):
        return safe_float(lvl.get("price"), None)
    if isinstance(lvl, (list, tuple)) and len(lvl) >= 1:
        return safe_float(lvl[0], None)
    return None


def _lvl_size(lvl):
    if isinstance(lvl, dict):
        return safe_float(lvl.get("size"), 0.0)
    if isinstance(lvl, (list, tuple)) and len(lvl) >= 2:
        return safe_float(lvl[1], 0.0)
    return 0.0


def fetch_rest_book(token_id):
    try:
        r = requests.get(f"{CLOB_HOST}/book?token_id={token_id}", timeout=10)
        data = r.json()
        handle_one_book(token_id, data.get("bids", []), data.get("asks", []))
        bid, ask = best_bid_ask(token_id)
        print(f"📖 REST book {token_id[:12]}...: bid={bid} ask={ask}")
    except Exception as e:
        print(f"⚠️ REST book fetch failed: {e}")


def _kline_interval_str() -> str:
    if KLINE_INTERVAL:
        return KLINE_INTERVAL
    mapping = {60: "1m", 180: "3m", 300: "5m", 900: "15m", 1800: "30m", 3600: "1h"}
    return mapping.get(WINDOW_SECONDS, f"{WINDOW_SECONDS // 60}m")


def fetch_binance_klines(limit: int = 6) -> List[Tuple[float, float, float, float]]:
    interval = _kline_interval_str()
    url = f"{BINANCE_KLINE_REST}&interval={interval}&limit={limit + 1}"
    try:
        resp = requests.get(url, timeout=10)
        resp.raise_for_status()
        raw = resp.json()
        closed = raw[:-1] if len(raw) > limit else raw
        result = []
        for k in closed[-limit:]:
            o = float(k[1])
            c = float(k[4])
            frac = (c - o) / o if o > 0 else 0.0
            result.append((int(k[0]) / 1000, o, c, frac))
        return result
    except Exception as e:
        print(f"⚠️ Binance klines fetch failed: {e}")
        return []


def prefill_window_history():
    if KLINE_PREFILL_COUNT <= 0:
        print("📊 Kline prefill disabled")
        return
    interval = _kline_interval_str()
    print(f"📊 Prefilling macro trend ({interval}, last {KLINE_PREFILL_COUNT})...")
    candles = fetch_binance_klines(KLINE_PREFILL_COUNT)
    if not candles:
        print("⚠️ No klines received")
        return
    for open_ts, o, c, frac in candles:
        epoch_bucket = int(open_ts) - (int(open_ts) % WINDOW_SECONDS)
        slug = f"{BASE_SLUG_PREFIX}{epoch_bucket}"
        S.window_history.append((slug, o, c, frac))
        direction = "UP" if frac > 0 else "DN"
        dt_str = datetime.fromtimestamp(open_ts, tz=timezone.utc).strftime("%H:%M")
        print(f"   {dt_str} | {direction} {frac:+.5f} | open=${o:.0f} close=${c:.0f}")
    if len(S.window_history) > 10:
        S.window_history = S.window_history[-10:]
    trend_dir, trend_cnt = macro_trend_direction()
    if trend_dir:
        print(f"🔴 MACRO TREND at startup: {trend_dir} ({trend_cnt} windows)")
    else:
        print(f"✅ No macro trend at startup ({len(S.window_history)} windows)")


def complete_signals_outcome(slug: str, winning_side: str, frac: float):
    """
    (2026-06-03) Completa el outcome de TODAS las señales loggeadas de un slug
    cuando el mercado se resuelve — incluyendo las que NO se compraron.

    Esto permite backtest exacto: para cada señal evaluada (comprada o rechazada),
    sabemos si el lado que el bot quería habría ganado o no.

    winning_side: "UP" o "DN" (quién ganó el mercado)
    frac: el movimiento fraccional de BTC (para referencia)
    """
    if os.getenv("LOG_ALL_SIGNALS", "1") != "1":
        return
    try:
        with open(SIGNALS_LOG_FILE, "r") as f:
            raw_lines = f.readlines()
    except FileNotFoundError:
        return

    out = []
    updated = 0
    for raw in raw_lines:
        line = raw.strip()
        if not line:
            out.append(raw)
            continue
        try:
            rec = json.loads(line)
        except Exception:
            out.append(raw)
            continue
        # Solo completar señales de este slug que aún no tienen outcome
        if rec.get("slug") == slug and rec.get("won") is None:
            side = rec.get("side")
            won = (side == winning_side)
            rec["outcome_ts"] = time.time()
            rec["won"] = won
            rec["market_winning_side"] = winning_side
            rec["market_frac"] = round(frac, 6)
            # Si no fue comprada (decision no es *_BUY), exit_reason refleja eso
            if rec.get("exit_reason") is None:
                rec["exit_reason"] = "NOT_BOUGHT"
                rec["pnl"] = 0.0  # no se compró, PnL real = 0
            # Actualizar Google Sheets SOLO para compras reales
            if rec.get("decision") == "BUY":
                try:
                    sheets_logger.update_outcome(slug, won, rec.get("pnl", 0.0) or 0.0)
                except Exception:
                    pass
            updated += 1
            out.append(json.dumps(rec) + "\n")
        else:
            out.append(raw)

    if updated:
        try:
            with open(SIGNALS_LOG_FILE, "w") as f:
                f.writelines(out)
        except Exception as e:
            print(f"⚠️ complete_signals_outcome write error: {e}")


def _record_window_to_history():
    if S.slug and cycle_log.btc_open and cycle_log.btc_close:
        frac = (cycle_log.btc_close - cycle_log.btc_open) / cycle_log.btc_open
        S.window_history.append((S.slug, cycle_log.btc_open, cycle_log.btc_close, frac))
        if len(S.window_history) > 10:
            S.window_history = S.window_history[-10:]
        direction = "UP" if frac > 0 else "DN"
        print(f"📊 Window: {S.slug} {ASSET.upper()} {direction} {frac:+.5f} | history={len(S.window_history)}")
        # NUEVO: completar outcome de todas las señales loggeadas de este mercado
        complete_signals_outcome(S.slug, direction, frac)


def macro_trend_direction() -> Tuple[Optional[str], int]:
    if not USE_MACRO_TREND_FILTER or len(S.window_history) < MACRO_TREND_WINDOWS:
        return None, 0
    recent = S.window_history[-MACRO_TREND_WINDOWS:]
    up_count = sum(1 for _, _, _, frac in recent if frac > MACRO_TREND_MIN_MOVE)
    dn_count = sum(1 for _, _, _, frac in recent if frac < -MACRO_TREND_MIN_MOVE)
    if up_count >= MACRO_TREND_WINDOWS:
        return "UP", up_count
    elif dn_count >= MACRO_TREND_WINDOWS:
        return "DN", dn_count
    return None, 0


def init_market(market):
    _record_window_to_history()

    # ── v5.10: Ghost position detection ──────────────────────────
    # If a position from the previous market was never sold/resolved,
    # determine WIN/LOSS from window history and log it properly.
    if S.position_token and S.position_label and S.entry_price > 0:
        ghost_cost = S.entry_price * S.position_size
        ghost_won = None
        if S.window_history:
            last_slug, _, _, last_frac = S.window_history[-1]
            if (S.position_label == "UP" and last_frac > 0) or \
               (S.position_label == "DN" and last_frac < 0):
                ghost_won = True
            else:
                ghost_won = False
        btc_now = spot_tracker.latest() if 'spot_tracker' in dir() else None
        btc_str = f"${btc_now:,.0f}" if btc_now else "N/A"
        if ghost_won is True:
            msg = (f"👻 GHOST WIN | {S.position_label} @ {S.entry_price:.2f} | "
                   f"sz={S.position_size:.1f} | auto-redeemed | {ASSET.upper()}={btc_str}")
            print(msg)
            tg_send(msg)
            if S.consecutive_losses > 0:
                S.consecutive_losses = 0
        elif ghost_won is False:
            gross = -ghost_cost
            S.pnl_usdc += gross
            S.consecutive_losses += 1
            msg = (f"👻 GHOST LOSS | {S.position_label} @ {S.entry_price:.2f} | "
                   f"pnl={gross:+.2f} | day={S.pnl_usdc:+.2f} | {ASSET.upper()}={btc_str}")
            print(msg)
            tg_send(msg)
            log_trade("SELL", S.position_label, 0.0, S.position_size,
                      0.0, "GHOST_RESOLVED_LOSS", pnl=gross)
        else:
            print(f"⚠️ GHOST POSITION: {S.position_label} @ {S.entry_price:.2f} — "
                  f"could not determine outcome (no window history)")
        clear_position_state()
    # ── End ghost position detection ─────────────────────────────

    daily_rollover()
    S.slug = market.get("slug")
    S.end_time = market_end_time(market)
    S.tick = market_tick(market)
    toks = extract_token_ids(market) or []
    S.tokens = toks
    if S.end_time:
        S.start_time = datetime.fromtimestamp(
            S.end_time.timestamp() - WINDOW_SECONDS, tz=timezone.utc)
    else:
        S.start_time = None
    S.book = {t: {"best_bid": None, "best_ask": None, "bid_top3": 0.0, "ask_top3": 0.0} for t in S.tokens}
    S.orders_sent = 0
    S.last_order_ts = 0.0
    S.last_buy_fail_ts = 0.0  # FIX BUY-RETRY ANTI-CHASE — reset cada ciclo
    S.cl_reverse_count = 0  # reset al iniciar ciclo
    S.ptb_shift_ts = 0.0          # v5.9: reset PTB shift tracking
    S.ptb_shift_delta = 0.0
    S.ptb_override_diff = 0.0
    S.is_ptb_shift_entry = False
    # v5.13: Whale accumulation reset
    if USE_WHALE_ACCUM:
        # Print summary of previous window if there were buys
        if S.whale_buys:
            total = S.whale_spent_up + S.whale_spent_dn
            buys_str = " | ".join(f"P{p}{s}@{pr:.2f}${a:.2f}" for p, s, pr, a, _ in S.whale_buys)
            d = chainlink_feed.cl_delta_usd()
            print(f"\n{'='*60}")
            print(f"  🐋 WHALE SUMMARY: {S.slug}")
            print(f"  UP: ${S.whale_spent_up:.2f} | DN: ${S.whale_spent_dn:.2f} | Total: ${total:.2f}")
            print(f"  Buys: {buys_str}")
            print(f"  Final CL delta: ${d:+.0f}" if d else "  Final CL delta: N/A")
            print(f"{'='*60}\n")
        S.whale_p1_done = False
        S.whale_p2_done = False
        S.whale_p3_done = False
        S.whale_p1_last_try = 0.0
        S.whale_p2_last_try = 0.0
        S.whale_p3_last_try = 0.0
        S.whale_spent_up = 0.0
        S.whale_spent_dn = 0.0
        S.whale_buys = []
    # v5.15: Straddle reset per window
    if USE_COPY_TRADING:
        if S.straddle_rounds > 0:
            total = S.straddle_spent_up + S.straddle_spent_dn
            avg_up = S.straddle_spent_up / S.straddle_shares_up if S.straddle_shares_up > 0 else 0
            avg_dn = S.straddle_spent_dn / S.straddle_shares_dn if S.straddle_shares_dn > 0 else 0
            combined = avg_up + avg_dn
            edge = (1.0 - combined) * 100 if combined > 0 else 0
            # Remaining unsold positions — these will settle at expiry
            payout_up = S.straddle_shares_up  # $1/share if UP wins
            payout_dn = S.straddle_shares_dn  # $1/share if DN wins
            # P&L if remaining position wins/loses, PLUS already realized (merge+TP) profit
            pnl_if_up = (payout_up - total) + S.straddle_merged_profit
            pnl_if_dn = (payout_dn - total) + S.straddle_merged_profit
            print(f"\n{'='*60}")
            print(f"  📋 MOMENTUM STRADDLE SUMMARY: {S.slug}")
            print(f"  Rounds: {S.straddle_rounds} | UP=${S.straddle_spent_up:.2f} ({S.straddle_shares_up:.0f}sh @{avg_up:.2f}) | DN=${S.straddle_spent_dn:.2f} ({S.straddle_shares_dn:.0f}sh @{avg_dn:.2f})")
            if total > 0:
                print(f"  Combined: {combined:.3f} | Edge: {edge:+.1f}% | Remaining invested: ${total:.2f}")
            if S.straddle_merged_profit != 0:
                print(f"  💰 REALIZED profit (merge+TP): ${S.straddle_merged_profit:+.2f}")
            print(f"  If UP wins: ${pnl_if_up:+.2f} | If DN wins: ${pnl_if_dn:+.2f}")
            print(f"{'='*60}\n")

            # Schedule auto-claim
            # v5.18 FIX D2: usar SIEMPRE el balance on-chain real, no el tracker.
            # Antes solo ajustábamos cuando on-chain > tracker (caso desincronización
            # por lag RPC). Pero el caso más común es que después de un TP queden
            # residuos pequeños (0.04, 0.33, 1.8 shares) en el proxy wallet por floor
            # de int(). El tracker queda en 0 pero on-chain tiene shares — el código
            # antiguo NO programaba claim y los residuos se quedaban perdidos.
            if AUTO_CLAIM_ENABLED and S.condition_id and len(S.tokens) == 2:
                total_shares = S.straddle_shares_up + S.straddle_shares_dn
                if not DRY_RUN:
                    try:
                        up_id_c, dn_id_c = S.tokens
                        real_up_c = query_conditional_token_balance(up_id_c) or 0
                        real_dn_c = query_conditional_token_balance(dn_id_c) or 0
                        onchain_total = real_up_c + real_dn_c
                        # Reportar discrepancias en cualquier dirección
                        if abs(onchain_total - total_shares) > 0.05:
                            label = "residuo post-TP" if total_shares < 0.5 else "ajuste"
                            print(f"  🔧 Auto-claim {label}: tracker={total_shares:.2f}sh, "
                                  f"on-chain={onchain_total:.2f}sh (UP={real_up_c:.2f}, DN={real_dn_c:.2f})")
                        # Usar SIEMPRE el on-chain como verdad
                        total_shares = onchain_total
                    except Exception as _e:
                        pass  # si falla la query, seguir con tracker
                # Programar claim si hay cualquier balance redimible (≥ $0.10 ≈ 0.10 shares)
                if total_shares >= 0.10:
                    print(f"  ⏳ Scheduling auto-claim for {S.condition_id[:16]}... ({total_shares:.2f} shares)")
                    schedule_claim(S.condition_id, f"STRADDLE_{S.slug}", total_shares)
        S.straddle_last_buy_ts = 0.0
        S.straddle_rounds = 0
        S.straddle_spent_up = 0.0
        S.straddle_spent_dn = 0.0
        S.straddle_shares_up = 0.0
        S.straddle_shares_dn = 0.0
        S.straddle_sold_up = False
        S.straddle_sold_dn = False
        S.straddle_merged_profit = 0.0
        # v5.18 PATCH 3: reset state anti-piramidación
        S.cl_delta_history = []
        S.last_buy_side = None
        # v5.18 HOTFIX PATCH 1: reset state cooldown/strikes drift-sync
        S.last_successful_buy_ts = 0.0
        S.large_drift_strikes = 0
    S.position_token = None
    S.position_label = None
    S.position_size = 0.0
    S.entry_price = 0.0
    S.entry_ts = 0.0
    S.peak_price = 0.0
    S.trail_active = False
    S.last_diag_ts = 0.0
    S.last_balance_ts = 0.0
    S.ws_open_ts = 0.0
    S.last_ws_msg_ts = 0.0
    S.overreaction_detected = False
    S._pullback_info = ""
    S.overreaction_direction = ""
    S.overreaction_magnitude = 0.0
    S.sell_fail_count = 0
    S.last_sell_fail_ts = 0.0

    # ── Contador de ciclos de espera post-pérdida ─────────────────────────
    if PROGRESSIVE_SIZING and S.cycles_to_wait > 0:
        S.cycles_to_wait -= 1
        S.cycles_waited  += 1
        if S.cycles_to_wait == 0:
            dyn = S.dynamic_base if S.dynamic_base > 0 else PROG_BASE_USDC
            print(f"▶️ Espera terminada ({S.cycles_waited} ciclos) — próxima entrada con base normal ${dyn:.2f}")
            tg_send(f"▶️ Espera terminada — entrando con base normal ${dyn:.2f}")
        else:
            print(f"⏸️ Esperando... {S.cycles_to_wait} ciclo(s) restantes")
            tg_send(f"⏸️ Ciclos de espera restantes: {S.cycles_to_wait}")
    # Si el ciclo anterior cerró sin confirmar el resultado (RESOLVED_UNKNOWN),
    # el bot espera hasta que el balance cambie antes de entrar con martingale.
    # Esto evita que un 3× se aplique cuando el resultado real aún no se sabe.
    if PROGRESSIVE_SIZING and S._pending_resolution and S.consecutive_losses > 0:
        bal_now = S.last_known_balance or 0.0
        bal_ref = S._pending_resolution_bal
        if bal_now > bal_ref + 0.50:
            # Balance subió → el claim se realizó → era un WIN
            print(f"✅ Balance subió ${bal_now-bal_ref:.2f} — claim confirmado → reset martingale a base")
            tg_send(f"✅ Claim confirmado — martingale reseteado a base. Balance: ${bal_now:.2f}")
            S.consecutive_losses = 0
            S._pending_resolution = False
            S._pending_resolution_bal = 0.0
        elif bal_now < bal_ref - 0.50:
            # Balance bajó → ya se procesó la pérdida → continuar con martingale
            print(f"❌ Balance bajó ${bal_ref-bal_now:.2f} — resultado era LOSS → martingale continúa")
            S._pending_resolution = False
            S._pending_resolution_bal = 0.0
        else:
            # Balance sin cambios → resultado aún no reflejado → BLOQUEAR entrada
            print(f"⏸️ PENDING_RESOLUTION activo — balance sin cambios (${bal_now:.2f}) "
                  f"→ no entraré hasta confirmar resultado")
            tg_send(f"⏸️ Esperando claim — no entrando en nuevos trades hasta ver cambio en balance (${bal_now:.2f})")
            # NO bloqueamos aquí — el bloqueo real está en maybe_enter_position
    S.condition_id = market.get("conditionId") or market.get("condition_id") or None
    if S.condition_id:
        print(f"📋 condition_id: {S.condition_id[:16]}...")
    spot_tracker.record_window_start()
    market_open_ts = S.start_time.timestamp() if S.start_time else 0.0
    chainlink_feed.record_price_to_beat(market_open_ts=market_open_ts,
                                        market_data=market)
    for tid in S.tokens:
        fetch_rest_book(tid)
    bal = S.last_known_balance if S.last_known_balance is not None else BALANCE_FALLBACK_USDC
    cycle_log.record_market_open(
        slug=S.slug or "", title=market_title(market),
        end_time=S.end_time, price=spot_tracker.latest(), balance=bal)

    # ── Telegram: nuevo ciclo con PTB para verificación manual ───────────
    ptb        = chainlink_feed.price_to_beat()
    btc_now    = spot_tracker.latest()
    end_str    = S.end_time.strftime("%H:%M UTC") if S.end_time else "?"
    slug_short = (S.slug or "").replace(f"{ASSET}-updown-{WINDOW_SECONDS//60}m-", "")
    ptb_str    = f"${ptb:,.2f}" if ptb else "?"
    btc_str2   = f"${btc_now:,.2f}" if btc_now else "?"
    diff_str   = f"\n📏 {ASSET.upper()} vs PTB: {btc_now - ptb:+.2f}" if (btc_now and ptb) else ""
    market_url = f"https://polymarket.com/event/{S.slug}" if S.slug else ""

    tg_send(
        f"🕐 Nuevo ciclo | {slug_short} → cierra {end_str}\n"
        f"⛓️ PTB: {ptb_str} | {ASSET.upper()}: {btc_str2}{diff_str}\n"
        f"💰 Balance: ${bal:.2f}\n"
        f"🔗 {market_url}\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"💬 Responde con el PTB correcto en {PTB_OVERRIDE_WINDOW_SEC:.0f}s para corregirlo\n"
        f"   (o ignora para usar {ptb_str})"
    )

    # Esperar respuesta manual — si el usuario envía un número lo usa como PTB
    # v5.14: Skip PTB wait for copy trading — not needed
    if ptb and not USE_COPY_TRADING:
        confirmed_ptb = wait_for_ptb_override(ptb, end_str)
        if confirmed_ptb != ptb:
            chainlink_feed._price_to_beat    = confirmed_ptb
            chainlink_feed._price_to_beat_ts = time.time()
            print(f"⛓️  PTB OVERRIDE aplicado: ${confirmed_ptb:,.2f}")


def handle_one_book(asset, bids, asks):
    if asset not in S.book:
        return
    if bids:
        bid_prices = [(_lvl_price(b), b) for b in bids if _lvl_price(b) is not None]
        if bid_prices:
            bid_prices.sort(key=lambda x: x[0], reverse=True)
            best_bid = bid_prices[0][0]
            bid3 = sum(_lvl_size(bp[1]) for bp in bid_prices[:3])
        else:
            best_bid, bid3 = None, 0.0
    else:
        best_bid, bid3 = None, 0.0
    if asks:
        ask_prices = [(_lvl_price(a), a) for a in asks if _lvl_price(a) is not None]
        if ask_prices:
            ask_prices.sort(key=lambda x: x[0])
            best_ask = ask_prices[0][0]
            ask3 = sum(_lvl_size(ap[1]) for ap in ask_prices[:3])
        else:
            best_ask, ask3 = None, 0.0
    else:
        best_ask, ask3 = None, 0.0
    S.book[asset]["best_bid"] = best_bid
    S.book[asset]["best_ask"] = best_ask
    S.book[asset]["bid_top3"] = bid3
    S.book[asset]["ask_top3"] = ask3


def extract_books(obj):
    if obj is None:
        return
    if isinstance(obj, list):
        for it in obj:
            extract_books(it)
        return
    if not isinstance(obj, dict):
        return
    if "data" in obj and isinstance(obj["data"], (dict, list)):
        extract_books(obj["data"])
    asset = obj.get("asset_id") or obj.get("assetId") or obj.get("token_id") or obj.get("tokenId")
    bids = obj.get("bids")
    asks = obj.get("asks")
    if asset and isinstance(bids, list) and isinstance(asks, list):
        handle_one_book(str(asset), bids, asks)


def best_bid_ask(token_id):
    b = S.book.get(token_id, {})
    return safe_float(b.get("best_bid"), None), safe_float(b.get("best_ask"), None)


def is_dummy_001_099(bid, ask):
    return (bid is not None and ask is not None and
            abs(bid - 0.01) < 1e-9 and abs(ask - 0.99) < 1e-9)


def book_liq_ok(token_id, check_side: str = "both") -> Tuple[bool, str]:
    """
    Verifica que el libro de órdenes del token tenga liquidez suficiente.

    Para TF compramos el token ganador (ask side) — verificamos ask_top3.
    Para PR compramos el token barato — verificamos ask_top3.
    'both' = verificación combinada (bid+ask).

    TF_ASK_MIN_LIQ: liquidez mínima en los top 3 asks para ejecutar sin slippage.
    Si ask_top3 < umbral, el fill será parcial o a precio malo.
    """
    b           = S.book.get(token_id, {})
    bid3        = safe_float(b.get("bid_top3"), 0)
    ask3        = safe_float(b.get("ask_top3"), 0)
    total       = bid3 + ask3

    TF_ASK_MIN  = float(os.getenv("TF_ASK_MIN_LIQ",   "30"))   # mín USDC en ask side
    BOTH_MIN    = float(os.getenv("MIN_BOOK_LIQ_TOP3", "60"))   # mín combinado

    if check_side == "ask":
        if ask3 < TF_ASK_MIN:
            return False, f"ASK liquidez insuficiente: ${ask3:.0f} < ${TF_ASK_MIN:.0f}"
        return True, f"ask_liq=${ask3:.0f} ✅"
    else:
        if total < BOTH_MIN:
            return False, f"liquidez insuficiente: ${total:.0f} < ${BOTH_MIN:.0f}"
        return True, f"liq=${total:.0f} ✅"


# ================================================================
#  MEAN REVERSION SIGNAL
# ================================================================
def window_timing():
    if S.end_time is None:
        return None, None
    secs_left = (S.end_time - now_utc()).total_seconds()
    secs_elapsed = float(WINDOW_SECONDS) - secs_left
    return secs_elapsed, secs_left


def pick_signal_trend_follow() -> Tuple[str, str]:
    """
    v5.0: Trend following using Chainlink as truth source.
    When Chainlink confirms a strong move from "price to beat",
    buy WITH that direction (the winning-direction token).
    Returns: ("TREND_UP"|"TREND_DN"|"NONE", reason_string)
    """
    elapsed, left = window_timing()
    if elapsed is None or left is None:
        return "NONE", "no timing data"

    # ── v5.9: PTB Shift fast-track ────────────────────────────────
    # Cuando el PTB cambia mid-cycle, los tokens están temporalmente
    # subvaluados. Se reduce el delay de entrada para capturar el repricing.
    ptb_shift_age = time.time() - S.ptb_shift_ts
    ptb_shift_active = (PTB_SHIFT_ENABLED
                        and ptb_shift_age < PTB_SHIFT_WINDOW_SEC
                        and S.ptb_shift_delta >= PTB_SHIFT_MIN_DIFF)

    entry_delay = PTB_SHIFT_FAST_ENTRY if ptb_shift_active else NO_ENTRY_BEFORE_SEC
    # SHADOW 2026-10-25: solo durante la evaluación en sombra (nunca en la real) se
    # permite evaluar antes de NO_ENTRY_BEFORE_SEC. _SHADOW_CTX["active"] es False
    # siempre fuera de shadow_tick(), así que la lógica real no cambia.
    if _SHADOW_CTX["active"]:
        entry_delay = 0.0

    if elapsed < entry_delay:
        if ptb_shift_active:
            return "NONE", f"PTB_SHIFT waiting ({elapsed:.0f}s/{entry_delay:.0f}s) — fast-track"
        return "NONE", f"waiting ({elapsed:.0f}s/{entry_delay:.0f}s)"
    # Need at least 60s left to get fills and resolve
    if left < NO_ENTRY_AFTER_LEFT:
        return "NONE", f"too late ({left:.0f}s left)"

    # === CHAINLINK DIRECTION (truth source) ===
    cl_dir, cl_delta, cl_count = chainlink_feed.cl_direction()
    if cl_dir is None:
        return "NONE", "no Chainlink data"

    abs_delta = abs(cl_delta)
    ptb = chainlink_feed.price_to_beat()
    cl_now = chainlink_feed.price()

    if abs_delta < MIN_CL_DELTA_USD:
        return "NONE", f"CL delta too small: ${cl_delta:+.0f} (need >${MIN_CL_DELTA_USD:.0f})"

    # ── ATR Gate — v5.6: no entrar si el mercado no tiene energía ─────────
    #
    # RESOLVED_LOSS ocurre cuando BTC apenas se mueve en 15 minutos.
    # Ciclo 1773823500: BTC_chg=+$5 → TF_UP @ $8 → expiró sin TP → -$8
    # Ciclo 1773817200: BTC_chg=-$7 → segunda entrada → expiró sin TP → -$5
    #
    # El ATR mide cuánto se mueve BTC en promedio por vela de 1 minuto.
    # Si ATR < umbral mínimo, el mercado está lateral y el token difícilmente
    # llegará al TP en los 15 minutos restantes.
    #
    # Regla: ATR debe ser >= ATR_MIN_USD para entrar.
    # Default: $30 (si BTC no mueve $30/min en promedio, mercado plano)
    #
    # También verificamos que el CL delta sea >= ATR * ATR_CL_RATIO
    # para confirmar que el movimiento actual es significativo vs la volatilidad
    # normal del mercado.
    ATR_MIN_USD    = float(os.getenv("ATR_MIN_USD",    "25"))   # ATR mínimo para entrar
    ATR_CL_RATIO   = float(os.getenv("ATR_CL_RATIO",   "0.8"))  # CL delta debe ser >= ratio × ATR
    atr_val = compute_atr(14)
    if atr_val is not None:
        if atr_val < ATR_MIN_USD:
            return "NONE", (f"ATR_BLOCK: mercado plano ATR=${atr_val:.0f} < ${ATR_MIN_USD:.0f} "
                            f"— alto riesgo RESOLVED_LOSS")
        if abs_delta < atr_val * ATR_CL_RATIO:
            return "NONE", (f"ATR_BLOCK: CL delta ${abs_delta:.0f} < {ATR_CL_RATIO:.1f}× ATR=${atr_val:.0f} "
                            f"— movimiento insuficiente vs volatilidad")

    # Need at least CL_CONFIRM_COUNT consecutive reads in same direction
    if cl_count < CL_CONFIRM_COUNT:
        return "NONE", f"CL not confirmed: {cl_dir}x{cl_count} (need {CL_CONFIRM_COUNT})"

    # ── v5.9: WIN_CHG FILTER — BTC debe haberse movido del open ──────────
    # Datos de 9 trades: Wins avg |win_chg|=0.001148 ($82), Losses avg=0.000570 ($40).
    # Trade #5 entró con win_chg=-0.000011 → BTC NO se había movido = moneda al aire.
    # Filtro: |win_chg| >= 0.0008 bloquea 4/6 losses, 0/3 wins.
    # SKIP durante PTB shift — el edge es del repricing, no del movimiento de BTC.
    bn_chg = spot_tracker.change_since_window_start()
    if bn_chg is not None and TF_MIN_WIN_CHG > 0 and not ptb_shift_active:
        abs_win_chg = abs(bn_chg)
        if abs_win_chg < TF_MIN_WIN_CHG:
            dollar_moved = abs_win_chg * (spot_tracker.latest() or 70000)
            return "NONE", (f"WIN_CHG_FILTER: |win_chg|={abs_win_chg:.6f} (${dollar_moved:.0f}) "
                            f"< {TF_MIN_WIN_CHG:.4f} — BTC no se ha movido lo suficiente del open")

    # === BINANCE CONFIRMATION (v5.0.3 — enhanced divergence check) ===
    # Two checks:
    # 1. If BN strongly disagrees with CL direction → skip (CL might be stale)
    # 2. If BN is REVERSING against CL → extra danger signal
    # bn_chg already read above in WIN_CHG filter
    bn_price = spot_tracker.latest() or 70000
    bn_delta_usd = 0.0
    if bn_chg is not None:
        bn_delta_usd = bn_chg * bn_price
        # Check 1: Strong BN disagreement (BN moved $15+ opposite to CL)
        MIN_BN_CONFIRM_USD = float(os.getenv("MIN_BN_CONFIRM_USD", "25"))
        if abs(bn_delta_usd) >= MIN_BN_CONFIRM_USD:
            bn_dir = "UP" if bn_chg > 0 else "DN"
            if bn_dir != cl_dir:
                return "NONE", f"BN disagrees: BN={bn_dir}(${bn_delta_usd:+.0f}) vs CL={cl_dir}(${cl_delta:+.0f})"
        # Check 2: CL-BN divergence — if CL says DN but BN is already bouncing UP $10+, CL is stale
        BN_CL_DIVERGE_USD = float(os.getenv("BN_CL_DIVERGE_USD", "25"))
        cl_now = chainlink_feed.price() or 0
        bn_now = bn_price
        if cl_now > 0 and bn_now > 0:
            cl_bn_gap = bn_now - cl_now  # positive = BN higher than CL
            if cl_dir == "DN" and cl_bn_gap > BN_CL_DIVERGE_USD:
                return "NONE", f"BN-CL DIVERGE: BN>${cl_now:,.0f} by ${cl_bn_gap:+.0f} but CL says DN — CL stale?"
            if cl_dir == "UP" and cl_bn_gap < -BN_CL_DIVERGE_USD:
                return "NONE", f"BN-CL DIVERGE: BN<{cl_now:,.0f} by ${cl_bn_gap:+.0f} but CL says UP — CL stale?"

    # === IMBALANCE CONFIRMATION ===
    imb = binance_depth.imbalance()
    # === IMB FILTER (relaxed for TF — only block extreme opposition) ===
    TF_IMB_UP_MIN = 0.15   # Much more relaxed than MR (was 0.4)
    TF_IMB_DN_MAX = 7.0    # Much more relaxed than MR (was 2.5)
    if cl_dir == "UP" and imb < TF_IMB_UP_MIN:
        return "NONE", f"IMB_FILTER: imb={imb:.2f} < {TF_IMB_UP_MIN} (extreme selling, don't buy UP)"
    if cl_dir == "DN" and imb > TF_IMB_DN_MAX:
        return "NONE", f"IMB_FILTER: imb={imb:.2f} > {TF_IMB_DN_MAX} (extreme buying, don't buy DN)"

    # === CANDLE/RSI CONFIRMATION (informational for TF — RSI confirms trend, doesn't block) ===
    candle_ok, candle_reason = candle_analyzer.entry_filter(cl_dir)
    # In TF mode: RSI_BLOCK from MR is WRONG — high RSI confirms UP, low RSI confirms DN
    # So we ignore candle_ok for blocking, only log as info
    candle_str = f"ℹ️{candle_reason}" if not candle_ok else candle_reason

    # === REGIME FILTER — detect whipsaw markets ===
    # If last 3+ windows alternate direction (UP→DN→UP or DN→UP→DN), market is indecisive
    if len(S.window_history) >= 3:
        recent_dirs = []
        for _, _, _, frac in S.window_history[-3:]:
            if frac > MACRO_TREND_MIN_MOVE:
                recent_dirs.append("UP")
            elif frac < -MACRO_TREND_MIN_MOVE:
                recent_dirs.append("DN")
            else:
                recent_dirs.append("FLAT")
        # Alternating = whipsaw (UP-DN-UP or DN-UP-DN)
        if (len(recent_dirs) == 3
            and recent_dirs[0] != "FLAT" and recent_dirs[1] != "FLAT" and recent_dirs[2] != "FLAT"
            and recent_dirs[0] != recent_dirs[1] and recent_dirs[1] != recent_dirs[2]):
            return "NONE", f"REGIME: whipsaw detected ({recent_dirs[0]}→{recent_dirs[1]}→{recent_dirs[2]}) — sitting out"

    # v5.10: Extended whipsaw — check direction-change frequency over WHIPSAW_LOOKBACK windows
    # Catches choppy markets where directions flip >60% of the time even if not strictly alternating
    if len(S.window_history) >= WHIPSAW_LOOKBACK:
        _ws_dirs = []
        for _, _, _, _ws_frac in S.window_history[-WHIPSAW_LOOKBACK:]:
            if _ws_frac > MACRO_TREND_MIN_MOVE:
                _ws_dirs.append("UP")
            elif _ws_frac < -MACRO_TREND_MIN_MOVE:
                _ws_dirs.append("DN")
            else:
                _ws_dirs.append("FLAT")
        _ws_changes = sum(1 for _i in range(1, len(_ws_dirs))
                         if _ws_dirs[_i] != _ws_dirs[_i-1]
                         and _ws_dirs[_i] != "FLAT" and _ws_dirs[_i-1] != "FLAT")
        _ws_max = len(_ws_dirs) - 1
        _ws_ratio = _ws_changes / _ws_max if _ws_max > 0 else 0
        if _ws_ratio >= WHIPSAW_RATIO:
            return "NONE", (f"WHIPSAW_EXT: {_ws_changes}/{_ws_max} direction changes "
                           f"in {WHIPSAW_LOOKBACK} windows ({_ws_ratio:.0%}) — choppy market")

    # === FIX 2: WHIPSAW_BLOCK — bloquear re-entrada en la MISMA dirección tras CL_REVERSE ===
    # Datos: 18:34 UP CL_REVERSE → 18:37 DN CL_REVERSE = -$9 (mismo ciclo, misma dirección)
    # PERO: 3 ciclos tuvieron CL_REVERSE seguido de win en dirección OPUESTA
    # → Solo bloquear si cl_dir == dirección que ya revirtió, no la contraria
    MAX_CL_REVERSES = int(os.getenv("MAX_CL_REVERSES_PER_CYCLE", "1"))
    if S.cl_reverse_count >= MAX_CL_REVERSES:
        last_rev_dir = getattr(S, 'last_cl_reverse_dir', None)
        if last_rev_dir is None or cl_dir == last_rev_dir:
            return "NONE", (f"WHIPSAW_BLOCK: {S.cl_reverse_count} CL_REVERSE(s) en {last_rev_dir or '?'} "
                            f"— no re-entrar en misma dirección")

    # === FIX 4: RSI AGOTAMIENTO — CL puede revertir si el activo está sobreextendido ===
    # En TF modo tendencia, RSI extremo indica que el movimiento actual está agotado
    # DN con RSI<30: precio ya cayó demasiado → CL probable rebote = REVERSE
    # UP con RSI>70: precio ya subió demasiado → CL probable caída = REVERSE
    # Datos: 15:02 RSI=15 DN → CL_REVERSE $106; 15:47 RSI=34 DN → CL_REVERSE $100
    TF_RSI_EXHAUST_DN = int(os.getenv("TF_RSI_EXHAUST_DN", "30"))  # no comprar DN si RSI < 30
    TF_RSI_EXHAUST_UP = int(os.getenv("TF_RSI_EXHAUST_UP", "68"))  # no comprar UP si RSI >= 68
    rsi_val, _ = candle_analyzer.rsi()
    if rsi_val is not None:
        if cl_dir == "DN" and rsi_val < TF_RSI_EXHAUST_DN:
            return "NONE", (f"RSI_EXHAUSTION: RSI={rsi_val:.0f} < {TF_RSI_EXHAUST_DN} "
                            f"oversold — DN puede revertir")
        if cl_dir == "UP" and rsi_val > TF_RSI_EXHAUST_UP:
            return "NONE", (f"RSI_EXHAUSTION: RSI={rsi_val:.0f} > {TF_RSI_EXHAUST_UP} "
                            f"overbought — UP puede revertir")

    # === FIX: BOOK_SCORE MÍNIMO ===
    # Chequeo doble: CLOB de Polymarket + Binance depth
    # CLOB: liquidez del order book de Polymarket (bid_top3 + ask_top3)
    # Binance depth: confirma que hay mercado real detrás de la señal
    MIN_TF_BOOK_SCORE = float(os.getenv("MIN_TF_BOOK_SCORE", "20"))
    tok_dir = S.tokens[0] if cl_dir == "UP" else (S.tokens[1] if len(S.tokens) > 1 else None)
    if tok_dir:
        b = S.book.get(tok_dir, {})
        book_score = safe_float(b.get("bid_top3"), 0) + safe_float(b.get("ask_top3"), 0)
        if book_score < MIN_TF_BOOK_SCORE:
            return "NONE", (f"BOOK_THIN: book_score={book_score:.0f} < {MIN_TF_BOOK_SCORE:.0f} "
                            f"— liquidez insuficiente, mercado indeciso")

    # Binance depth: si el order book de Binance también está vacío, señal débil
    bn_score, _ = binance_depth.book_score(cl_dir) if cl_dir else (0, "")
    MIN_BN_BOOK = float(os.getenv("MIN_BN_BOOK_SCORE", "5"))
    if bn_score < MIN_BN_BOOK:
        return "NONE", (f"BN_BOOK_THIN: Binance depth={bn_score:.0f} < {MIN_BN_BOOK:.0f} "
                        f"— sin respaldo en Binance")

    # === FIX: CL DELTA DECELERATING ===
    # Si CL llegó a $75+ pero está perdiendo momentum → probable reversión
    # Pérdidas puras: $100-$149 overextended. Si además decelera = doble señal de alerta
    TF_CL_DECEL_MIN_DELTA = float(os.getenv("TF_CL_DECEL_MIN_DELTA", "75"))
    if abs_delta >= TF_CL_DECEL_MIN_DELTA:
        momentum = chainlink_feed.cl_delta_momentum(window_sec=60)
        if momentum == 'DECELERATING':
            return "NONE", (f"CL_DECEL: delta=${abs_delta:.0f} pero decelerando "
                            f"— CL perdiendo fuerza, riesgo reversión")

    # === FIX: RANGE EXHAUSTION — BTC ya consumió >65% del rango en dirección CL ===
    # Si BTC ya subió/bajó la mayor parte de su rango desde el open del ciclo,
    # está en el pico de la oscilación y CL puede revertir.
    #
    # Datos empíricos (17 ciclos):
    #   CL_REVERSE avg exhaustion=71% (máx=100%) — BTC ya en el pico
    #   TF_TP      avg exhaustion=37% (máx=65%)  — BTC aún tiene recorrido
    #   Threshold 65%: bloquea 3/5 pérdidas puras y 0/12 wins ← precisión perfecta
    #
    # exhaustion > 1.0 = BTC rompió el high/low previo = TENDENCIA REAL → no bloquear
    TF_RANGE_EXHAUST_THRESH = float(os.getenv("TF_RANGE_EXHAUST_THRESH", "0.65"))
    exhaustion = spot_tracker.range_exhaustion(cl_dir)
    if exhaustion is not None and 0 < exhaustion <= 1.0:
        if exhaustion >= TF_RANGE_EXHAUST_THRESH:
            return "NONE", (f"RANGE_EXHAUST: BTC consumió {exhaustion:.0%} del rango "
                            f"en dirección {cl_dir} — probable reversión")
    if cl_now > 0 and bn_price > 0:
        cl_bn_gap_abs = abs(bn_price - cl_now)
        # FIX: use same BN_CL_DIVERGE_USD env var as divergence check above (not hardcoded 40)
        regime_gap_limit = float(os.getenv("BN_CL_DIVERGE_USD", "25"))
        if cl_bn_gap_abs > regime_gap_limit:
            return "NONE", f"REGIME: CL-BN gap too wide (${cl_bn_gap_abs:.0f} > ${regime_gap_limit:.0f}) — CL unreliable"

    # Determine signal
    target_signal = f"TREND_{cl_dir}"
    confidence = "STRONG" if abs_delta >= MIN_CL_DELTA_USD * 2 else "MODERATE"

    # Book score (informational, not blocking for trend follow)
    score, score_detail = binance_depth.book_score(cl_dir)

    ptb_shift_str = f" | ⚡PTB_SHIFT ${S.ptb_shift_delta:.0f}" if ptb_shift_active else ""
    reason = (f"{confidence} | CL {cl_dir} ${cl_delta:+.0f} (ptb=${ptb:,.0f}→${cl_now:,.0f}) | "
              f"x{cl_count} confirms | imb={imb:.2f} | SCORE={score:.0f} | {candle_str}{ptb_shift_str}")

    if not _SHADOW_CTX["active"]:   # SHADOW: la evaluación en sombra no registra hits reales
        cycle_log.record_signal_hit(target_signal, reason, spot_tracker.latest(),
                                     spot_tracker.change_since_window_start() or 0, imb)
    return target_signal, reason


def pick_signal_peak_reversion() -> Tuple[str, str]:
    """
    v5.2: PEAK REVERSION STRATEGY
    ─────────────────────────────
    Logic:
      1. Monitor how far Binance spot has moved from the window's price-to-beat (PTB).
      2. When that divergence is large (>= PR_MIN_PEAK_DIVERGENCE_USD) but not runaway
         (< PR_MAX_DIVERGENCE_USD), and the spot has started pulling back
         (>= PR_CONFIRM_REVERSAL_PCT of the peak move has reversed), buy the CHEAP
         token (the one the market just priced very low).
      3. Exit when the token recovers PR_TP_PCT (e.g. 40%) — this is the cheap→fair
         repricing we expect as spot reverts toward PTB.

    Cheap token = the one the market is penalizing because spot moved against it.
      - Spot moved UP  → DN token is cheap → buy DN
      - Spot moved DN  → UP token is cheap → buy UP
    """
    elapsed, left = window_timing()
    if elapsed is None or left is None:
        return "NONE", "no timing"
    if elapsed < PR_MIN_ELAPSED_SEC:
        return "NONE", f"too early ({elapsed:.0f}s < {PR_MIN_ELAPSED_SEC:.0f}s)"

    # Solo entrar en los primeros 5 minutos de la ventana
    # → quedan > 10 minutos para que ocurra la reversión
    PR_MAX_ENTRY_ELAPSED = float(os.getenv("PR_MAX_ENTRY_ELAPSED_SEC", "300"))  # 5 min
    if elapsed > PR_MAX_ENTRY_ELAPSED:
        return "NONE", f"PR window closed ({elapsed:.0f}s > {PR_MAX_ENTRY_ELAPSED:.0f}s — solo primeros 5min)"

    if left < NO_ENTRY_AFTER_LEFT:
        return "NONE", f"too late ({left:.0f}s left)"

    # ── Spot divergence from PTB ──────────────────────────────────────────
    spot_now = spot_tracker.latest()
    spot_ptb = spot_tracker.window_start_price
    if spot_now is None or spot_ptb is None or spot_ptb == 0:
        return "NONE", "no spot data"

    divergence_usd = spot_now - spot_ptb          # positive = UP, negative = DN
    abs_div        = abs(divergence_usd)
    peak_move      = spot_tracker.peak_move_from_window()  # signed, tracks max excursion
    abs_peak       = abs(peak_move) * (spot_ptb or 97000)  # convert fraction → USD

    # Update peak tracker on state for diagnostics
    S.pr_spot_ptb            = spot_ptb
    S.pr_peak_divergence_usd = abs_peak

    # ── Gate 1: divergence big enough to make cheap token worthwhile ─────
    if abs_div < PR_MIN_PEAK_DIVERGENCE_USD:
        return "NONE", (f"divergence too small: ${abs_div:.0f} "
                        f"(need >${PR_MIN_PEAK_DIVERGENCE_USD:.0f})")

    # ── Gate 2: not a runaway trend ───────────────────────────────────────
    if abs_div > PR_MAX_DIVERGENCE_USD:
        return "NONE", (f"divergence too large (trend?): ${abs_div:.0f} "
                        f"(max ${PR_MAX_DIVERGENCE_USD:.0f})")

    # ── Gate 3: spot must have STARTED reverting before we buy ───────────
    # We don't want to buy at the exact peak — we want confirmation it's turning.
    # peak_move is the max-ever excursion; divergence_usd is current.
    # If they're the same, price is still at the peak → wait.
    # revert_pct = how much of the peak has already recovered.
    if abs(peak_move) < 0.0001:
        return "NONE", "no peak yet"

    current_frac = (spot_now - spot_ptb) / spot_ptb if spot_ptb > 0 else 0
    revert_pct = 0.0
    if peak_move > 0 and current_frac < peak_move:       # was UP, pulled back
        revert_pct = (peak_move - current_frac) / peak_move
    elif peak_move < 0 and current_frac > peak_move:     # was DN, bounced
        revert_pct = (current_frac - peak_move) / abs(peak_move)

    if revert_pct < PR_CONFIRM_REVERSAL_PCT:
        return "NONE", (f"waiting for reversal confirmation: "
                        f"{revert_pct*100:.1f}% < {PR_CONFIRM_REVERSAL_PCT*100:.0f}% "
                        f"(peak=${abs_peak:.0f} now=${abs_div:.0f})")

    # ── Gate 3.5: CHAINLINK confirma la misma dirección de reversión ─────
    #
    # v5.4: DOS FUENTES DE CONFIRMACIÓN
    # Fuente 1 (ya chequeada): spot Binance divergió y está revirtiendo
    # Fuente 2 (esta gate):    Chainlink también apunta a la misma reversión
    #
    # La reversión es creíble cuando AMBAS fuentes coinciden.
    # CL_REVERT_MIN_USD: Chainlink debe haber movido al menos N dólares
    #   en la dirección del movimiento del spot para confirmar que no es ruido.
    # Si CL está en sentido opuesto al spot → el spot puede seguir yendo en esa dirección
    #   (CL es más lento pero más confiable → si CL no confirma, esperamos)
    #
    if CHAINLINK_ENABLED:
        cl_price = chainlink_feed.price()
        cl_ptb   = chainlink_feed.price_to_beat()
        CL_REVERT_MIN_USD = float(os.getenv("CL_REVERT_MIN_USD", "20"))
        USE_CL_CONFIRM_PR = os.getenv("USE_CL_CONFIRM_PR", "1") == "1"

        if USE_CL_CONFIRM_PR and cl_price and cl_ptb and cl_ptb > 0:
            cl_delta_from_ptb = cl_price - cl_ptb   # positivo = CL subió vs PTB

            # Si spot bajó (peak_move < 0) → esperamos que CL también haya bajado
            # y que la reversión del spot coincida con CL empezando a subir hacia PTB
            # Si spot subió (peak_move > 0) → esperamos que CL también haya subido
            # y que spot esté revirtiendo hacia abajo con CL confirmando

            # Dirección del movimiento del spot
            spot_went_up = peak_move > 0   # spot subió desde PTB

            if spot_went_up:
                # Compramos DN (spot subió → DN barato)
                # Queremos: CL también subió (confirma el movimiento) Y
                #           CL delta no sea extremo (o esté revirtiendo también)
                if cl_delta_from_ptb < -CL_REVERT_MIN_USD:
                    # CL bajó fuerte mientras spot subió — divergencia CL/BN grande
                    # Posible: CL es la verdad y spot es el que se va a corregir
                    # En este caso DN es correcto — CL apoya la reversión
                    pass  # OK — CL confirma que el precio "real" es más bajo → DN gana
                elif cl_delta_from_ptb > CL_REVERT_MIN_USD * 2:
                    # CL también subió fuerte — ambas fuentes dicen UP
                    # Comprar DN sería apostar contra AMBAS fuentes → skip
                    return "NONE", (f"CL_BLOCK: CL también sube (Δ=${cl_delta_from_ptb:+.0f}) "
                                    f"mientras spot sube — no comprar DN")
            else:
                # spot_went_down → compramos UP (spot bajó → UP barato)
                # Queremos: CL también bajó o está neutral cerca de PTB
                if cl_delta_from_ptb > CL_REVERT_MIN_USD:
                    # CL subió mientras spot bajó — CL dice UP ya
                    pass  # OK — CL apoya la reversión UP
                elif cl_delta_from_ptb < -CL_REVERT_MIN_USD * 2:
                    # CL también bajó fuerte — ambas fuentes dicen DN
                    # Comprar UP sería apostar contra ambas → skip
                    return "NONE", (f"CL_BLOCK: CL también baja (Δ=${cl_delta_from_ptb:+.0f}) "
                                    f"mientras spot baja — no comprar UP")
    #
    # Buscamos evidencia de que el precio NO va a seguir en esa dirección.
    # Dos señales fuertes:
    #   A) Muro grande del lado contrario al movimiento (absorbe presión)
    #   B) Imbalance virando: más bids cuando el precio bajó, más asks cuando subió
    #
    imb = binance_depth.imbalance()
    cheap_direction = "UP" if peak_move < 0 else "DN"   # token que vamos a comprar

    # A) Muro de soporte: si spot bajó, queremos un BID WALL que frene la caída
    #    Si spot subió, queremos un ASK WALL que frene la subida
    wall_side   = "UP" if peak_move < 0 else "DN"   # "UP" = buscamos bids, "DN" = asks
    wall_price, wall_size, wall_desc = binance_depth.nearest_wall(wall_side)
    has_wall    = wall_price is not None
    wall_score  = 0
    wall_reason = "no wall"
    if has_wall:
        spot_distance = abs(spot_now - wall_price)
        spot_pct      = spot_distance / spot_now if spot_now else 1.0
        # Muro cercano (<0.15% del spot) y grande (>= WALL_MIN_BTC) = señal fuerte
        if spot_pct < 0.0015:
            wall_score  = 2    # muro muy cercano
            wall_reason = f"WALL_CLOSE {wall_desc} dist={spot_distance:.0f}"
        else:
            wall_score  = 1    # muro existe pero lejos
            wall_reason = f"WALL_FAR {wall_desc}"

    # B) Imbalance momentum: ¿el ratio bid/ask está cambiando a favor de reversión?
    #    depth_momentum > 0 cuando los bids crecen vs antes (bullish pressure growing)
    #    depth_momentum < 0 cuando los asks crecen vs antes (bearish pressure growing)
    depth_mom  = binance_depth.depth_momentum(window_sec=30)
    imb_score  = 0
    imb_reason = f"imb={imb:.2f}"
    if depth_mom is not None:
        imb_reason += f" mom={depth_mom:+.2f}"
        if cheap_direction == "UP":
            # Compramos UP (spot bajó) → queremos bids aumentando (depth_mom > 0)
            if depth_mom > 0.10:
                imb_score = 2   # bids creciendo fuerte → soporte confirmado
                imb_reason += " ↑BIDS_GROWING"
            elif depth_mom > 0:
                imb_score = 1
        else:
            # Compramos DN (spot subió) → queremos asks aumentando (depth_mom < 0)
            if depth_mom < -0.10:
                imb_score = 2   # asks creciendo fuerte → resistencia confirmada
                imb_reason += " ↓ASKS_GROWING"
            elif depth_mom < 0:
                imb_score = 1

    # Bloqueo extremo: imbalance totalmente opuesto sin muro
    if cheap_direction == "UP" and imb < IMB_UP_MIN and wall_score == 0:
        return "NONE", f"IMB_BLOCK: imb={imb:.2f} < {IMB_UP_MIN} y sin muro — no hay soporte"
    if cheap_direction == "DN" and imb > IMB_DN_MAX and wall_score == 0:
        return "NONE", f"IMB_BLOCK: imb={imb:.2f} > {IMB_DN_MAX} y sin muro — no hay resistencia"

    # ── Gate 4b: MM Tracker — comportamiento del market maker ────────────
    #
    # El MM del libro de Polymarket es el árbitro real del precio del token.
    # Si el MM está ACUMULANDO el token barato cuando el spot se alejó del PTB,
    # es la señal más fuerte de que el token va a recuperar.
    #
    # Scores:
    #   +2 = MM acumulando activamente el token cheap
    #   +1 = MM neutral pero tight spread (listo para moverse)
    #    0 = sin señal clara
    #   (negativo bloquea si MM está distribuyendo el token cheap)
    #
    mm_score_val = 0
    mm_reason    = "MM=N/A"
    if len(S.tokens) == 2:
        cheap_token_id = S.tokens[0] if cheap_direction == "UP" else S.tokens[1]
        mm_hint, mm_reason = mm_tracker.reversal_hint(
            cheap_token_id, cheap_direction,
            spot_peak_direction="UP" if peak_move > 0 else "DN")
        raw_mm = mm_tracker.score(cheap_token_id)

        if mm_hint and raw_mm >= 2:
            mm_score_val = 2    # señal fuerte
        elif mm_hint and raw_mm >= 1:
            mm_score_val = 1    # señal moderada
        elif raw_mm < -1:
            # MM está distribuyendo el token barato = NO es buena señal de reversión
            return "NONE", f"MM_DISTRIBUTING: {mm_reason} — MM vendiendo token barato"
    #
    # reversal_score() combina todos los indicadores en un score 0-12.
    # Lo usamos como CONFIRMACIÓN (suma puntos al score total),
    # no como filtro excluyente — excepto si hay tendencia fuerte opuesta.
    #
    tech_score  = 0
    tech_reason = "candle_analysis_off"
    if USE_CANDLE_ANALYSIS and candle_analyzer.candles:
        tech_score, tech_reason = candle_analyzer.reversal_score(cheap_direction)

        # Bloqueo único: vela fuerte tendencial CON momentum alto = no reversión
        if candle_analyzer.candles:
            last_c   = candle_analyzer.last_candle(include_current=True)
            mom_val, _ = candle_analyzer.momentum_score()
            if last_c:
                bad_bull = (cheap_direction == "DN" and
                            last_c.get("type") == "STRONG_BULL" and mom_val > 0.25)
                bad_bear = (cheap_direction == "UP" and
                            last_c.get("type") == "STRONG_BEAR" and mom_val < -0.25)
                if bad_bull:
                    return "NONE", f"TREND_BLOCK STRONG_BULL mom={mom_val:+.2f} — no comprar DN"
                if bad_bear:
                    return "NONE", f"TREND_BLOCK STRONG_BEAR mom={mom_val:+.2f} — no comprar UP"
    elif not USE_CANDLE_ANALYSIS:
        tech_score  = 2   # sin análisis = neutral, no penaliza
        tech_reason = "candle_analysis_off"

    # ── Puntuación total de reversión ─────────────────────────────────────
    # wall_score    : 0-2  (muro de order book Binance)
    # imb_score     : 0-2  (depth momentum / imbalance Binance)
    # mm_score_val  : 0-2  (comportamiento MM en libro Polymarket)  ← NUEVO
    # tech_score    : 0-12 (MACD, EMA, RSI, Bollinger, volumen, patrones)
    #
    # tech_score normalizado a 0-4. Total posible: ~10.
    tech_normalized      = min(4, tech_score // 3)
    total_reversal_score = wall_score + imb_score + mm_score_val + tech_normalized
    PR_MIN_REVERSAL_SCORE = int(os.getenv("PR_MIN_REVERSAL_SCORE", "2"))

    if total_reversal_score < PR_MIN_REVERSAL_SCORE:
        return "NONE", (f"REVERSAL_SCORE_LOW: {total_reversal_score}/{PR_MIN_REVERSAL_SCORE} "
                        f"[wall={wall_score} imb={imb_score} mm={mm_score_val} tech={tech_score}→{tech_normalized}] "
                        f"| {wall_reason} | {imb_reason} | {mm_reason} | {tech_reason}")

    # ── Señal confirmada ──────────────────────────────────────────────────
    signal     = "PEAK_REVERT_UP" if cheap_direction == "UP" else "PEAK_REVERT_DN"
    confidence = ("STRONG"   if total_reversal_score >= 6 else
                  "MODERATE" if total_reversal_score >= 3 else "WEAK")
    reason = (f"{confidence} total={total_reversal_score} "
              f"[wall={wall_score} imb={imb_score} mm={mm_score_val} tech={tech_score}] | "
              f"peak=${abs_peak:.0f} now=${abs_div:.0f} "
              f"rev={revert_pct*100:.1f}% | "
              f"{wall_reason} | {imb_reason} | {mm_reason} | {tech_reason}")

    cycle_log.record_signal_hit(signal, reason,
                                spot_now, spot_tracker.change_since_window_start() or 0, imb)
    return signal, reason


def pick_signal() -> Tuple[str, str]:
    """
    Mean reversion signal detection (legacy v4.x).
    Returns: ("REVERT_UP"|"REVERT_DN"|"NONE", reason_string)
    """
    elapsed, left = window_timing()
    if elapsed is not None and elapsed < NO_ENTRY_BEFORE_SEC:
        return "NONE", f"waiting ({elapsed:.0f}s/{NO_ENTRY_BEFORE_SEC:.0f}s)"
    if left is not None and left < NO_ENTRY_AFTER_LEFT:
        return "NONE", f"too late ({left:.0f}s left)"

    win_chg = spot_tracker.change_since_window_start()
    if win_chg is None:
        return "NONE", "no window data"

    abs_chg = abs(win_chg)
    price = spot_tracker.latest()
    dollar_chg = abs(win_chg * (price or 67000))

    # RSI+BB can reduce overreaction threshold
    _pre_token = "UP" if win_chg < 0 else "DN"
    tech_confirmed, tech_squeeze, tech_reason = candle_analyzer.technical_confirmation(_pre_token)

    if tech_squeeze:
        return "NONE", f"BB_SQUEEZE: {tech_reason}"

    effective_min = MIN_OVERREACTION
    if tech_confirmed:
        effective_min = MIN_OVERREACTION * 0.75

    if abs_chg < effective_min:
        return "NONE", f"move too small ({win_chg:+.5f}=${dollar_chg:.0f}, need {effective_min:.5f})"

    S.overreaction_detected = True
    S.overreaction_magnitude = win_chg

    if win_chg > 0:
        S.overreaction_direction = "UP"
        target_signal = "REVERT_DN"
        token_label = "DN"
    else:
        S.overreaction_direction = "DN"
        target_signal = "REVERT_UP"
        token_label = "UP"

    imb = binance_depth.imbalance()
    up_bid, up_ask = best_bid_ask(S.tokens[0]) if len(S.tokens) >= 2 else (None, None)
    dn_bid, dn_ask = best_bid_ask(S.tokens[1]) if len(S.tokens) >= 2 else (None, None)

    # Anti-trend pre-entry filter (too large move = real trend)
    MAX_PRE_ENTRY_MOVE = float(os.getenv("MAX_PRE_ENTRY_MOVE", "0.0080"))
    if abs_chg > MAX_PRE_ENTRY_MOVE:
        reason = f"move too large ({win_chg:+.5f}=${dollar_chg:.0f}, max={MAX_PRE_ENTRY_MOVE:.5f})"
        cycle_log.record_rejection(target_signal, reason, price, win_chg, imb, up_bid, up_ask, dn_bid, dn_ask)
        return "NONE", reason

    # Macro trend filter
    trend_dir, trend_count = macro_trend_direction()
    if trend_dir is not None:
        if (trend_dir == "UP" and target_signal == "REVERT_DN") or \
           (trend_dir == "DN" and target_signal == "REVERT_UP"):
            reason = f"MACRO TREND {trend_dir} ({trend_count}w) — blocking {target_signal}"
            cycle_log.record_rejection(target_signal, reason, price, win_chg, imb, up_bid, up_ask, dn_bid, dn_ask)
            return "NONE", reason

    # Bid/ask imbalance filter
    if token_label == "UP" and imb < IMB_UP_MIN:
        reason = f"IMB_FILTER: imb={imb:.2f} < {IMB_UP_MIN} (heavy selling, bounce unlikely)"
        cycle_log.record_rejection(target_signal, reason, price, win_chg, imb, up_bid, up_ask, dn_bid, dn_ask)
        return "NONE", reason
    if token_label == "DN" and imb > IMB_DN_MAX:
        reason = f"IMB_FILTER: imb={imb:.2f} > {IMB_DN_MAX} (heavy buying, pullback unlikely)"
        cycle_log.record_rejection(target_signal, reason, price, win_chg, imb, up_bid, up_ask, dn_bid, dn_ask)
        return "NONE", reason

    # Pullback entry (optional)
    if REQUIRE_PULLBACK:
        peak = spot_tracker.peak_move_from_window()
        abs_peak = abs(peak)
        if abs_peak < MIN_PEAK_MOVE:
            reason = f"peak too small ({peak:+.5f}, need {MIN_PEAK_MOVE:.5f})"
            cycle_log.record_rejection(target_signal, reason, price, win_chg, imb, up_bid, up_ask, dn_bid, dn_ask)
            return "NONE", reason
        pullback_pct = (abs_peak - abs_chg) / abs_peak if abs_peak > 0 else 0
        if pullback_pct < MIN_PULLBACK_PCT:
            reason = f"pullback={pullback_pct:.0%} (need {MIN_PULLBACK_PCT:.0%})"
            cycle_log.record_rejection(target_signal, reason, price, win_chg, imb, up_bid, up_ask, dn_bid, dn_ask)
            return "NONE", reason
        S._pullback_info = f"PULLBACK={pullback_pct:.0%}"

    # Candle analysis filter
    candle_ok, candle_reason = candle_analyzer.entry_filter(token_label)
    if not candle_ok:
        cycle_log.record_rejection(target_signal, candle_reason, price, win_chg, imb, up_bid, up_ask, dn_bid, dn_ask)
        return "NONE", candle_reason

    # ALL FILTERS PASSED
    confidence = "STRONG" if abs_chg >= IDEAL_OVERREACTION else "MODERATE"
    reason = (f"{confidence} | {ASSET.upper()} {S.overreaction_direction} ${dollar_chg:.0f} "
              f"({win_chg:+.5f}) → buy {token_label} | imb={imb:.2f} | {candle_reason}"
              f"{' | ' + tech_reason if tech_confirmed else ''}")
    cycle_log.record_signal_hit(target_signal, reason, price, win_chg, imb)
    return target_signal, reason


# ================================================================
#  ORDERS
# ================================================================
def _enrich_order_response(resp, side):
    """v5.18 PATCH 2: Extrae actual_shares y actual_usdc del order response.
    Polymarket devuelve takingAmount/makingAmount que representan los valores reales
    ejecutados on-chain, distintos de los valores requested por el bot.
    """
    if not isinstance(resp, dict):
        return resp
    try:
        taking = float(resp.get("takingAmount", 0) or 0)
        making = float(resp.get("makingAmount", 0) or 0)
        if side == "BUY":
            # En BUY: makingAmount=USDC pagado, takingAmount=shares recibidas
            resp["actual_shares"] = taking
            resp["actual_usdc"]   = making
        else:  # SELL
            # En SELL: makingAmount=shares vendidas, takingAmount=USDC recibidos
            resp["actual_shares"] = making
            resp["actual_usdc"]   = taking
    except (ValueError, TypeError):
        pass
    return resp


def post_market_order(client, token_id, side, amount):
    """v5.18 PATCH 5: intenta IOC/FAK primero (llena parcial), fallback a FOK.
    v5.18 PATCH 2: devuelve resp enriquecido con actual_shares / actual_usdc.

    FIX 2026-06-19 (anti-slippage): para órdenes BUY, re-valida el ask ACTUAL
    justo antes de ejecutar. Si el precio subió por encima del techo permitido
    (FT_PRICE_MAX + margen), aborta la compra. Esto evita el bug donde el filtro
    aprobaba a $0.98 pero la orden se llenaba a $0.99 (2s después) por slippage,
    metiéndose en la zona económicamente perdedora.
    """
    if DRY_RUN:
        # Estimación razonable para DRY_RUN
        est_shares = amount / 0.5
        return True, {"status": "DRY_RUN", "orderID": "dry_run",
                      "actual_shares": est_shares, "actual_usdc": amount}

    # ALERTA (2026-10-19): registrar en signals_log Y avisar por Telegram cuando
    # una orden NO se ejecuta (captura el motivo real de EJECUCIÓN, no solo filtros).
    def _notify_fail(_reason, _status="ORDER_FAIL", do_log=True):
        if do_log:
            # SOLO LOGGING (2026-10-21): captura el book de Polymarket (UP/DN) y el
            # monto intentado al momento del fallo, para análisis. Lecturas de solo
            # lectura ya usadas en otras partes. NO toca filtros ni el flujo de compra.
            _extra = {}
            try:
                if getattr(S, "tokens", None) and len(S.tokens) >= 2:
                    _ub, _ua = best_bid_ask(S.tokens[0])
                    _db, _da = best_bid_ask(S.tokens[1])
                    _extra = {"attempted_usdc": round(amount, 2),
                              "pm_up_bid": _ub, "pm_up_ask": _ua,
                              "pm_dn_bid": _db, "pm_dn_ask": _da}
            except Exception:
                _extra = {}
            try:
                log_exec_status(S.slug, side, _status, str(_reason), extra=_extra)
            except Exception:
                pass
        try:
            tg_send(f"❌ Orden {side} NO ejecutada | {S.slug or '?'} | motivo: {_reason}")
        except Exception:
            pass

    # EJECUCIÓN: MERCADO con FALLBACK a LÍMITE (2026-10-19). Causa confirmada
    # leyendo el código del cliente: create_market_order → calculate_market_price
    # → get_order_book (consulta REST). Si esa consulta vuelve con asks vacíos en
    # ese instante (aunque el WebSocket SÍ muestre libro), lanza "no match". Es un
    # problema de la consulta REST, NO del tamaño ni de libro delgado.
    # Arreglo: si la orden de MERCADO falla sin llenar, colocar una orden LÍMITE FAK
    # al ask que el WebSocket ya conoce. create_order NO consulta get_order_book, así
    # que evita la consulta REST rota. IMPORTANTE:
    #   - Los filtros (fast_track_check) ya corrieron ANTES de llamar aquí; esto NO
    #     los toca ni los salta.
    #   - El anti-slippage se re-valida en CADA intento. La LÍMITE usa el ask (ya
    #     <= guard) como precio tope: una orden límite NUNCA llena por encima de su
    #     precio → es inherentemente anti-slippage.
    #   - FAK llena lo que cruza al instante y mata el resto (sin órdenes colgadas).
    #   - El fallback SOLO se intenta cuando el mercado NO llenó nada y de forma
    #     limpia ("no match"/UNMATCHED/REJECTED) → sin riesgo de doble compra.
    _MAX_TRIES   = max(1, int(os.getenv("ORDER_RETRY_NO_MATCH", "3")))
    _RETRY_DELAY = float(os.getenv("ORDER_RETRY_DELAY_SEC", "1.0"))
    # BUY: reintentar hasta que falten _RETRY_UNTIL_LEFT seg del cierre (la señal
    # fast-track ya fue aprobada). SELL/otros: mantener _MAX_TRIES intentos.
    _RETRY_UNTIL_LEFT = 10.0
    # TOPE: no reintentar más de _RETRY_MAX_SEC seg. Los datos (2026-10-21) muestran
    # que si el libro del lado ganador está vacío, sigue vacío todo el tramo tardío
    # → insistir 77 veces no llena. Un burst corto basta por si aparece liquidez.
    _RETRY_MAX_SEC = float(os.getenv("ORDER_RETRY_MAX_SEC", "8"))
    _last_fail   = "sin intento"
    _last_status = "ORDER_UNMATCHED"

    _attempt = 0
    _retry_t0 = time.time()
    while True:
        _attempt += 1
        # ANTI-SLIPPAGE: re-chequear el ask actual antes de CADA intento
        if side == "BUY" and SLIPPAGE_GUARD_MAX > 0:
            try:
                bid_now, ask_now = best_bid_ask(token_id)
                if ask_now is not None and ask_now > SLIPPAGE_GUARD_MAX:
                    print(f"  🛑 ANTI-SLIPPAGE: ask=${ask_now:.3f} > techo ${SLIPPAGE_GUARD_MAX:.3f} "
                          f"al momento de ejecutar — compra ABORTADA (evita zona perdedora)")
                    try:
                        log_exec_status(S.slug, S.position_label or "?", "ANTI_SLIPPAGE",
                                        f"ask ${ask_now:.3f} > guard ${SLIPPAGE_GUARD_MAX:.3f}",
                                        extra={"ask_at_exec": round(ask_now, 4)})
                    except Exception:
                        pass
                    _notify_fail(f"anti-slippage: ask {ask_now:.3f} > {SLIPPAGE_GUARD_MAX:.3f}", do_log=False)
                    return False, f"slippage guard: ask {ask_now:.3f} > {SLIPPAGE_GUARD_MAX:.3f}"
            except Exception:
                # Si no se puede leer el book, continuar (no bloquear por error de lectura)
                pass

        _market_clean_nofill = False   # solo hacer fallback límite si el mercado no llenó NADA de forma limpia

        # ---- 1) Orden de MERCADO (toma lo mejor del libro) ----
        try:
            from py_clob_client_v2.clob_types import MarketOrderArgs, OrderType
            from py_clob_client_v2.order_builder.constants import BUY, SELL
            order_side = BUY if side == "BUY" else SELL
            args = MarketOrderArgs(token_id=token_id, amount=amount, side=order_side)
            signed = client.create_market_order(args)

            # Intentar IOC (Polymarket lo llama FAK = Fill-And-Kill)
            resp = None
            order_type_used = "FOK"
            try:
                if hasattr(OrderType, "FAK"):
                    resp = client.post_order(signed, OrderType.FAK)
                    order_type_used = "FAK"
                else:
                    resp = client.post_order(signed, OrderType.FOK)
            except Exception as ioc_err:
                # Si FAK falla por cliente viejo u otro motivo, fallback a FOK
                try:
                    resp = client.post_order(signed, OrderType.FOK)
                    order_type_used = "FOK(fallback)"
                except Exception:
                    raise ioc_err

            print(f"📋 Order response (MERCADO {side}, {order_type_used}, intento {_attempt}/{_MAX_TRIES}): {resp}")
            resp = _enrich_order_response(resp, side)

            if isinstance(resp, dict):
                status = resp.get("status", "").upper()
                if status == "MATCHED":
                    return True, resp            # llenó (total o parcial) → éxito
                elif status in ("UNMATCHED", "REJECTED"):
                    _last_fail, _last_status = f"MERCADO {status}: {resp}", f"ORDER_{status}"
                    _market_clean_nofill = True  # nada se llenó, limpio
                elif resp.get("orderID"):
                    return True, resp
                else:
                    # DELAYED / desconocido: ambiguo (podría llenarse) → NO fallback/reintento
                    _notify_fail(f"respuesta ambigua: {resp}", "ORDER_UNKNOWN")
                    return False, f"Unknown/ambiguous response: {resp}"
            else:
                _notify_fail(f"respuesta desconocida: {resp}", "ORDER_UNKNOWN")
                return False, f"Unknown response: {resp}"
        except Exception as e:
            # "no match"/"no orderbook" = consulta REST vacía, nada se llenó → limpio.
            _es = str(e).lower()
            print(f"❌ orden MERCADO exception ({side}, intento {_attempt}/{_MAX_TRIES}): {e}")
            _last_fail, _last_status = f"mercado excepción: {e}", "ORDER_EXCEPTION"
            if "no match" in _es or "no orderbook" in _es or "no order book" in _es:
                _market_clean_nofill = True

        # ---- 2) FALLBACK: orden LÍMITE FAK al ask del WebSocket (evita get_order_book) ----
        if side == "BUY" and _market_clean_nofill:
            try:
                import math as _math
                from py_clob_client_v2.clob_types import OrderArgs, OrderType as _OT
                from py_clob_client_v2.order_builder.constants import BUY as _BUYc
                if hasattr(_OT, "FAK"):   # FAK = llena y mata resto; sin FAK NO arriesgamos GTC colgada
                    try:
                        _blim, _alim = best_bid_ask(token_id)
                    except Exception:
                        _alim = None
                    # el ask ya pasó el anti-slippage (<= guard); la límite nunca llena por encima
                    if _alim is not None and _alim > 0 and (SLIPPAGE_GUARD_MAX <= 0 or _alim <= SLIPPAGE_GUARD_MAX + 1e-9):
                        _lp = round(float(_alim), 2)
                        _sz = int(_math.ceil(amount / _lp)) if _lp > 0 else 0
                        if _sz >= 1:
                            _largs = OrderArgs(price=_lp, size=_sz, side=_BUYc, token_id=token_id)
                            _lsigned = client.create_order(_largs)
                            _lresp = client.post_order(_lsigned, _OT.FAK)
                            print(f"📋 Order response (LÍMITE-fallback BUY @${_lp:.2f} x{_sz}, intento {_attempt}/{_MAX_TRIES}): {_lresp}")
                            _lresp = _enrich_order_response(_lresp, side)
                            if isinstance(_lresp, dict):
                                _ls = (_lresp.get("status") or "").upper()
                                if _ls == "MATCHED":
                                    return True, _lresp      # el fallback llenó → éxito
                                _last_fail = f"LÍMITE {_ls or '??'}: {_lresp}"
                                _last_status = f"ORDER_{_ls}" if _ls else "ORDER_UNMATCHED"
            except Exception as _le:
                print(f"❌ LÍMITE-fallback exception ({side}, intento {_attempt}/{_MAX_TRIES}): {_le}")
                _last_fail, _last_status = f"límite excepción: {_le}", "ORDER_EXCEPTION"

        # ¿Reintentar? BUY: mientras quede tiempo del ciclo (corta a _RETRY_UNTIL_LEFT
        # seg del cierre). SELL/otros: hasta _MAX_TRIES intentos.
        try:
            _tl = (S.end_time - now_utc()).total_seconds() if S.end_time else 0.0
        except Exception:
            _tl = 0.0
        _retry_elapsed = time.time() - _retry_t0
        _keep = (side == "BUY" and _tl > _RETRY_UNTIL_LEFT and _retry_elapsed < _RETRY_MAX_SEC) or \
                (side != "BUY" and _attempt < _MAX_TRIES)
        if not _keep:
            break
        print(f"  🔁 Reintento {_attempt + 1} en {_RETRY_DELAY:.1f}s "
              f"(quedan {_tl:.0f}s | fallo: {str(_last_fail)[:45]})")
        try:
            time.sleep(_RETRY_DELAY)
        except Exception:
            pass

    # Agotados los intentos sin llenar
    _notify_fail(f"tras {_attempt} intentos (mercado+límite): {_last_fail}", _last_status)
    return False, _last_fail


def post_limit_sell(client, token_id, price, size):
    if DRY_RUN:
        return True, {"status": "DRY_RUN", "orderID": "dry_run"}
    try:
        from py_clob_client_v2.clob_types import OrderArgs, OrderType
        from py_clob_client_v2.order_builder.constants import SELL
        price_str = float(f"{price:.2f}")
        args = OrderArgs(price=price_str, size=size, side=SELL, token_id=token_id)
        signed = client.create_order(args)
        resp = client.post_order(signed, orderType=OrderType.GTC)
        print(f"📋 Limit SELL response: {resp}")
        if isinstance(resp, dict):
            status = resp.get("status", "").upper()
            if status in ("MATCHED", "LIVE") or resp.get("orderID"):
                return True, resp
            elif status in ("UNMATCHED", "REJECTED"):
                return False, f"Limit SELL {status}: {resp}"
        return False, f"Unknown limit response: {resp}"
    except Exception as e:
        print(f"❌ Limit SELL exception: {e}")
        return False, e


# ================================================================
#  STINK BID MODE — Limit BUY + cancel + monitor fills
# ================================================================
def post_limit_buy(client, token_id, price, usdc_amount):
    """Place a GTC limit BUY order at a low price."""
    import math
    size = math.ceil(usdc_amount / price)  # ceil to ensure total >= $1 minimum
    if DRY_RUN:
        oid = f"dry_stink_{token_id[:8]}_{int(time.time())}"
        print(f"  🎯 [DRY] STINK BID: {size} shares @ ${price:.2f} = ${usdc_amount:.2f}")
        return True, {"orderID": oid, "status": "LIVE"}
    try:
        from py_clob_client_v2.clob_types import OrderArgs, OrderType
        from py_clob_client_v2.order_builder.constants import BUY
        price_str = float(f"{price:.2f}")
        args = OrderArgs(price=price_str, size=size, side=BUY, token_id=token_id)
        signed = client.create_order(args)
        resp = client.post_order(signed, orderType=OrderType.GTC)
        print(f"  📋 STINK BID response: {resp}")
        if isinstance(resp, dict):
            status = (resp.get("status") or "").upper()
            if status in ("LIVE", "MATCHED") or resp.get("orderID"):
                return True, resp
            return False, f"STINK BID {status}: {resp}"
        return False, f"Unknown: {resp}"
    except Exception as e:
        print(f"  ❌ STINK BID exception: {e}")
        return False, e


def cancel_order(client, order_id):
    """Cancel an order by ID."""
    if DRY_RUN:
        print(f"  🗑️ [DRY] Cancel order {order_id[:16]}...")
        return True
    try:
        # v2 MIGRATION: client.cancel() → client.cancel_order()
        resp = client.cancel_order(order_id)
        print(f"  🗑️ Cancel response: {resp}")
        return True
    except Exception as e:
        print(f"  ❌ Cancel exception: {e}")
        return False


def cancel_all_orders(client):
    """Cancel all open orders."""
    if DRY_RUN:
        print(f"  🗑️ [DRY] Cancel all orders")
        return True
    try:
        resp = client.cancel_all()
        print(f"  🗑️ Cancel all response: {resp}")
        return True
    except Exception as e:
        print(f"  ❌ Cancel all exception: {e}")
        return False


def get_order_fills(client, order_id):
    """Check if an order has been filled. Returns (filled: bool, fill_size: float)."""
    if DRY_RUN:
        return False, 0.0
    try:
        order = client.get_order(order_id)
        if isinstance(order, dict):
            size_matched = float(order.get("size_matched", 0) or 0)
            status = (order.get("status") or "").upper()
            filled = size_matched > 0 or status == "MATCHED"
            return filled, size_matched
        return False, 0.0
    except Exception as e:
        return False, 0.0


def run_stink_bid_cycle(client, market):
    """
    v5.9: STINK BID MODE — Moon Dev strategy.

    1. Al inicio del ciclo, coloca limit BUY en AMBOS tokens a STINK_BID_PRICE
    2. Monitorea fills cada STINK_POLL_SEC
    3. Si un lado se llena: cancela el otro, coloca TP
    4. Emergency exit STINK_EMERGENCY_SEC antes del cierre
    5. Al final del ciclo, cancela todo pendiente
    """
    if len(S.tokens) != 2:
        print("  ⚠️ Stink: necesita 2 tokens (UP/DN)")
        return

    up_id, dn_id = S.tokens
    end_dt = S.end_time
    if not end_dt:
        return

    shares_per_side = round(STINK_BID_USDC / STINK_BID_PRICE, 2)
    total_risk = STINK_BID_USDC * 2

    print(f"\n  {'='*60}")
    print(f"  🎯 STINK BID MODE — {S.slug}")
    print(f"  {'='*60}")
    print(f"  Bid price: {STINK_BID_PRICE:.2f} | Shares/side: {shares_per_side:.0f}")
    print(f"  Risk: ${total_risk:.2f} | TP: {STINK_TP_PRICE:.2f}")
    print(f"  Hold to expiry: {'YES' if STINK_HOLD_TO_EXPIRY else 'NO (TP sell)'}")

    # ── Place stink bids on both sides ─────────────────────────
    up_ok, up_resp = post_limit_buy(client, up_id, STINK_BID_PRICE, STINK_BID_USDC)
    dn_ok, dn_resp = post_limit_buy(client, dn_id, STINK_BID_PRICE, STINK_BID_USDC)

    up_order_id = up_resp.get("orderID") if isinstance(up_resp, dict) else None
    dn_order_id = dn_resp.get("orderID") if isinstance(dn_resp, dict) else None

    if not up_ok and not dn_ok:
        print("  ❌ No se pudo colocar ningún stink bid")
        return

    placed = []
    if up_ok and up_order_id:
        placed.append(("UP", up_order_id, up_id))
    if dn_ok and dn_order_id:
        placed.append(("DN", dn_order_id, dn_id))

    print(f"  ✅ Stink bids colocados: {[p[0] for p in placed]}")
    tg_send(f"🎯 Stink bids: UP+DN @ ${STINK_BID_PRICE:.2f} | ${total_risk:.2f} riesgo | {S.slug}")

    # ── Monitor fills ──────────────────────────────────────────
    filled_side = None
    filled_token_id = None
    filled_size = 0.0
    tp_order_id = None
    bids_placed_ts = time.time()
    bids_cancelled = False  # v5.9: True when unfilled bids are cancelled after timeout

    while True:
        now = time.time()
        secs_left = (end_dt - now_utc()).total_seconds()

        # Emergency: cancel everything and exit
        if secs_left <= STINK_EMERGENCY_SEC:
            print(f"  ⏰ STINK EMERGENCY: {secs_left:.0f}s left — canceling & selling")
            cancel_all_orders(client)
            if filled_side and filled_size > 0:
                # Try to sell whatever we have
                bid, _ = best_bid_ask(filled_token_id)
                if bid and bid > 0.01:
                    sell_price = clamp_price(float(bid), S.tick or 0.01, 0.01, 0.99)
                    ok, _, _ = _execute_sell(client, filled_token_id, sell_price,
                                            filled_size, "STINK_EMERGENCY")
                    if ok:
                        pnl = (sell_price * filled_size) - STINK_BID_USDC
                        print(f"  💰 STINK EMERGENCY SELL: {filled_side} @ {sell_price:.2f} | pnl={pnl:+.2f}")
                        tg_send(f"🎯 Stink emergency sell {filled_side} @ {sell_price:.2f} | pnl={pnl:+.2f}")
            break

        # v5.9: Cancel unfilled bids after STINK_CANCEL_AFTER_SEC (default 7.5 min)
        # Fills después de la mitad del ciclo probablemente son porque BTC ya
        # definió dirección → el token no va a recuperarse → fill "muerto".
        if not filled_side and not bids_cancelled and (now - bids_placed_ts) >= STINK_CANCEL_AFTER_SEC:
            print(f"  ⏱️ STINK TIMEOUT: {STINK_CANCEL_AFTER_SEC:.0f}s sin fill — cancelando bids")
            cancel_all_orders(client)
            bids_cancelled = True
            tg_send(f"⏱️ Stink bids cancelados (sin fill en {STINK_CANCEL_AFTER_SEC:.0f}s)")

        # If bids cancelled and no fill, just wait for cycle end
        if bids_cancelled and not filled_side:
            if int(now) % 60 == 0:
                print(f"  🎯 Stink: bids cancelados, esperando cierre ({secs_left:.0f}s)")
            time.sleep(STINK_POLL_SEC)
            continue

        # Check for fills
        if not filled_side:
            for label, oid, tid in placed:
                is_filled, fill_sz = get_order_fills(client, oid)
                if is_filled and fill_sz > 0:
                    filled_side = label
                    filled_token_id = tid
                    filled_size = fill_sz
                    pnl_potential = fill_sz * (1.0 - STINK_BID_PRICE)
                    print(f"  ⚡ STINK FILLED: {label} | {fill_sz:.0f} shares @ {STINK_BID_PRICE:.2f}")
                    print(f"  💎 Potential: +${pnl_potential:.2f} if resolves to $1")
                    tg_send(f"⚡ STINK FILLED: {label} @ {STINK_BID_PRICE:.2f} | "
                            f"{fill_sz:.0f} shares | potential +${pnl_potential:.2f}")

                    # Cancel the other side
                    for l2, oid2, _ in placed:
                        if l2 != label:
                            cancel_order(client, oid2)
                            print(f"  🗑️ Cancelled {l2} stink bid")

                    # Place TP sell if not holding to expiry
                    if not STINK_HOLD_TO_EXPIRY and STINK_TP_PRICE > STINK_BID_PRICE:
                        tp_ok, tp_resp = post_limit_sell(client, tid,
                                                         STINK_TP_PRICE, fill_sz)
                        if tp_ok and isinstance(tp_resp, dict):
                            tp_order_id = tp_resp.get("orderID")
                            print(f"  📈 TP placed: SELL {label} @ {STINK_TP_PRICE:.2f}")
                    break

            # DRY RUN simulation: simulate a fill if book shows price near stink level
            if DRY_RUN and not filled_side:
                for label, oid, tid in placed:
                    bid, ask = best_bid_ask(tid)
                    if ask is not None and ask <= STINK_BID_PRICE + 0.02:
                        filled_side = label
                        filled_token_id = tid
                        filled_size = shares_per_side
                        print(f"  ⚡ [DRY] SIMULATED FILL: {label} (ask={ask:.2f} near stink)")
                        tg_send(f"⚡ [DRY] Stink fill: {label} @ {STINK_BID_PRICE:.2f}")
                        break

        # Check if TP filled
        if filled_side and tp_order_id:
            tp_filled, tp_sz = get_order_fills(client, tp_order_id)
            if tp_filled and tp_sz > 0:
                pnl = (STINK_TP_PRICE * tp_sz) - STINK_BID_USDC
                print(f"  💰 STINK TP FILLED: {filled_side} @ {STINK_TP_PRICE:.2f} | pnl=+${pnl:.2f}")
                tg_send(f"💰 Stink TP: {filled_side} @ {STINK_TP_PRICE:.2f} | +${pnl:.2f}")
                break

        # Log status periodically
        if int(now) % 30 == 0:
            status = f"filled={filled_side or 'none'}" if filled_side else f"waiting fills ({secs_left:.0f}s left)"
            print(f"  🎯 Stink: {status}")

        time.sleep(STINK_POLL_SEC)

    # End of cycle — cancel anything remaining
    cancel_all_orders(client)
    print(f"  🏁 Stink bid cycle complete: {S.slug}")


# ================================================================
#  ENTRY LOGIC
# ================================================================
def get_dynamic_base(current_balance: float) -> float:
    """
    Escala la base de apuesta cuando el balance sube un 30%.
    La base sube también un 30% → ratio base/balance constante en 5.71%.

    Esto garantiza que el riesgo relativo no cambia nunca:
      - 2 pérdidas VERY HIGH + martingale 3× = siempre ~45.7% del balance
      - Sobrevivible en trade 1 y en trade 10,000

    El estado se persiste en S.dynamic_base y S.dynamic_base_next_lvl.
    """
    if not PROGRESSIVE_SIZING:
        return PROG_BASE_USDC

    # Inicializar si es primera vez
    if S.dynamic_base <= 0:
        S.dynamic_base           = PROG_BASE_USDC
        S.dynamic_base_next_lvl  = BAL_SCALE_INIT * (1 + BAL_SCALE_THRESH)

    # Escalar mientras el balance supere el umbral
    scaled = False
    while current_balance >= S.dynamic_base_next_lvl:
        old_base             = S.dynamic_base
        S.dynamic_base       = round(S.dynamic_base * (1 + BAL_SCALE_BASE_PCT), 4)
        S.dynamic_base_next_lvl = round(S.dynamic_base_next_lvl * (1 + BAL_SCALE_THRESH), 2)
        scaled = True
        print(f"📈 BASE ESCALADA: ${old_base:.4f} → ${S.dynamic_base:.4f} "
              f"(balance ${current_balance:.2f} ≥ umbral | próximo en ${S.dynamic_base_next_lvl:.2f})")
        tg_send(f"📈 Base escalada: ${old_base:.2f} → ${S.dynamic_base:.2f} | "
                f"balance ${current_balance:.2f} | próximo escalado en ${S.dynamic_base_next_lvl:.2f}")
        _save_sizing_state()  # persistir inmediatamente

    return S.dynamic_base


def compute_confidence(signal: str, reason: str) -> Tuple[float, str, float]:
    """
    v5.6: Confianza unificada con 6 fuentes de señal y 5 niveles.

    Fuentes (peso total = 1.0):
      TF:
        1. CL delta sobre mínimo    (30%)
        2. Confirmaciones CL        (25%)
        3. Imbalance dirección      (15%)
        4. Trade flow real          (15%)  ← NUEVO
        5. ATR: volatilidad relativa(10%)  ← NUEVO
        6. Sesión de mercado        ( 5%)  ← NUEVO

      PR (todas las fuentes):
        1. total_reversal_score     (35%)
        2. StochRSI extremo         (20%)  ← NUEVO
        3. Trade flow               (20%)  ← NUEVO
        4. ATR: movimiento vs ATR   (15%)  ← NUEVO
        5. Sesión de mercado        (10%)  ← NUEVO

    Niveles:
      VERY HIGH  ≥ 82% → 2.000× base
      HIGH       ≥ 65% → 1.625× base
      MEDIUM     ≥ 48% → 1.250× base
      ACCEPTABLE ≥ 32% → 0.875× base
      LOW        <  32% → 0.625× base
    """
    import re
    conf = 0.40

    # ── Indicadores compartidos ───────────────────────────────────
    session_name, session_score = compute_market_session()
    atr = compute_atr(14)
    stoch = compute_stoch_rsi(14, 14)

    if signal.startswith("TREND_"):
        cl_delta = abs(chainlink_feed.cl_delta_usd() or 0)
        cl_dir, _, cl_cnt = chainlink_feed.cl_direction()
        imb = binance_depth.imbalance()

        # 1. CL delta (0→1 cuando delta = 3× mínimo)
        delta_sc = min(1.0, max(0.0, (cl_delta - MIN_CL_DELTA_USD) / (MIN_CL_DELTA_USD * 2)))

        # 2. Confirmaciones (2=0.33, 3=0.67, 4+=1.0)
        confirm_sc = min(1.0, (cl_cnt - 1) / 3.0)

        # 3. Imbalance a favor
        if signal == "TREND_UP":
            imb_sc = min(1.0, max(0.0, (imb - 1.0) / 4.0))
        else:
            imb_sc = min(1.0, max(0.0, (1.0 - imb) / 0.8))

        # 4. Trade flow: v5.10 EAT-FLOW — net order consumption rate
        flow_dir = "UP" if signal == "TREND_UP" else "DN"
        eat_r, eat_dir, eat_desc = trade_flow.eat_rate(EAT_FLOW_WINDOW_SEC)
        # Score: eat_rate confirming our direction = high, opposing = low
        if signal == "TREND_UP":
            # Positive eat_rate = asks being consumed = bullish = confirms UP
            flow_sc = min(1.0, max(0.0, (eat_r + 0.5) / 1.0)) if eat_r > -0.5 else 0.0
        else:
            # Negative eat_rate = bids being consumed = bearish = confirms DN
            flow_sc = min(1.0, max(0.0, (-eat_r + 0.5) / 1.0)) if eat_r < 0.5 else 0.0

        # 5. ATR: si el CL delta supera 1× ATR = movimiento significativo
        atr_sc = 0.5
        if atr and atr > 0:
            atr_sc = min(1.0, cl_delta / atr)

        # 6. MACD(3/15/3) en velas de 1min — estrategia Moon Dev
        # Histograma > 0 = momentum alcista → favorece UP
        # Histograma < 0 = momentum bajista → favorece DN
        # Si MACD está OPUESTO a la señal → penalización fuerte (bloqueo suave)
        macd_sc = 0.5  # neutro por defecto
        try:
            mv, ms, _ = candle_analyzer.macd(fast=3, slow=15, signal=3)
            if mv is not None and ms is not None:
                macd_hist_val = mv - ms
                if signal == "TREND_UP":
                    if macd_hist_val > 0:
                        # MACD confirma UP — score proporcional a la fuerza
                        macd_sc = min(1.0, 0.5 + abs(macd_hist_val) / 20.0)
                    else:
                        # MACD contradice UP — penalización suave
                        # Floor en 0.30 para que MACD nunca bloquee solo una señal CL fuerte
                        macd_sc = max(0.30, 0.5 - abs(macd_hist_val) / 20.0)
                else:  # TREND_DN
                    if macd_hist_val < 0:
                        # MACD confirma DN
                        macd_sc = min(1.0, 0.5 + abs(macd_hist_val) / 20.0)
                    else:
                        # MACD contradice DN — penalización suave
                        macd_sc = max(0.30, 0.5 - abs(macd_hist_val) / 20.0)
        except Exception:
            macd_sc = 0.5

        # 7. Sesión
        sess_sc = session_score

        conf = (delta_sc   * 0.28 +
                confirm_sc * 0.23 +
                imb_sc     * 0.13 +
                flow_sc    * 0.13 +
                atr_sc     * 0.10 +
                macd_sc    * 0.08 +   # MACD(3/15/3) — Moon Dev strategy
                sess_sc    * 0.05)

    elif signal.startswith("PEAK_REVERT_"):
        cheap_dir = "UP" if "UP" in signal else "DN"

        # 1. total_reversal_score
        m = re.search(r'total=(\d+)', reason)
        total_sc = int(m.group(1)) if m else 3
        rev_sc = min(1.0, max(0.0, (total_sc - 2) / 6.0))

        # 2. StochRSI: oversold para UP, overbought para DN
        stoch_sc = 0.5
        if stoch:
            k, d = stoch
            if cheap_dir == "UP":
                stoch_sc = max(0.0, min(1.0, (20 - k) / 20)) if k < 20 else 0.3
            else:
                stoch_sc = max(0.0, min(1.0, (k - 80) / 20)) if k > 80 else 0.3

        # 3. Trade flow real
        flow_sc_raw, _ = trade_flow.reversal_score(cheap_dir, 30)
        flow_sc = max(0.0, flow_sc_raw / 2.0) if flow_sc_raw >= 0 else 0.0

        # 4. ATR: divergencia relativa al ATR (> 1× ATR = movimiento real)
        atr_sc = 0.5
        if atr and atr > 0:
            spot_now = spot_tracker.latest() or 1
            div_abs  = abs(spot_tracker.change_since_window_start() or 0) * spot_now
            atr_sc   = min(1.0, div_abs / (atr * 1.5))

        # 5. Sesión
        sess_sc = session_score

        conf = (rev_sc    * 0.35 +
                stoch_sc  * 0.20 +
                flow_sc   * 0.20 +
                atr_sc    * 0.15 +
                sess_sc   * 0.10)

    conf = round(max(0.0, min(1.0, conf)), 3)

    # ── v5.8: Sentiment / Fragility adjustment ───────────────────
    # No bloquea — ajusta confianza en [-0.15, +0.08] según:
    #   Fear & Greed, Funding Rate, OI change, CL staleness
    sent_dir = "UP" if "UP" in signal else "DN"
    sent_adj, sent_reason = sentiment_tracker.reversal_risk_adjustment(sent_dir)
    if abs(sent_adj) > 0.005:
        conf_before = conf
        conf = round(max(0.0, min(1.0, conf + sent_adj)), 3)
        print(f"  [sentiment] {sent_reason} → conf {conf_before:.0%} {sent_adj:+.0%} = {conf:.0%}")

    # ── v5.9: PTB Shift confidence boost ─────────────────────────
    # PTB override con diff > $20 = edge de información real.
    # Boost +8% para que señales MEDIUM borderline pasen a HIGH.
    ptb_shift_age = time.time() - S.ptb_shift_ts
    if (PTB_SHIFT_ENABLED
            and ptb_shift_age < PTB_SHIFT_WINDOW_SEC
            and S.ptb_shift_delta >= PTB_SHIFT_MIN_DIFF):
        ptb_boost = min(0.08, S.ptb_shift_delta / 500.0)  # max +8% at $40 diff
        conf_before = conf
        conf = round(max(0.0, min(1.0, conf + ptb_boost)), 3)
        print(f"  [ptb_shift] ⚡ diff=${S.ptb_shift_delta:.0f} boost={ptb_boost:+.2f} "
              f"→ conf {conf_before:.0%} → {conf:.0%}")

    # ── Clasificar nivel ─────────────────────────────────────────
    if conf >= CONF_VERYHIGH_THRESHOLD:
        nivel = "VERY HIGH";   mult = CONF_VERYHIGH_MULT
    elif conf >= CONF_HIGH_THRESHOLD:
        nivel = "HIGH";        mult = CONF_HIGH_MULT
    elif conf >= CONF_MED_THRESHOLD:
        nivel = "MEDIUM";      mult = CONF_MED_MULT
    else:
        # ACCEPTABLE y LOW bloqueados — datos muestran 6W/3L con señales débiles
        # vs 3W/0L con VERY HIGH. Solo MEDIUM+ tiene edge real.
        nivel = "LOW";         mult = 0.0  # mult=0 bloquea la entrada

    return conf, nivel, mult


# ================================================================
#  v5.13: WHALE ACCUMULATION TICK
# ================================================================
def whale_accum_tick(client):
    """
    Whale accumulation strategy — buys FIXED SHARES per order (like the whale).
    Each share pays $1 if it wins. WHALE_SHARES=30 → $30 payout per order.
    Phase 1: Split buy (both sides) — WHALE_SHARES each
    Phase 2: Reinforce winner — WHALE_SHARES on winning side
    Phase 3: Final push — WHALE_SHARES on winning side
    """
    if not S.trading_enabled or S.paused_by_telegram:
        return
    if len(S.tokens) != 2:
        return

    now = time.time()
    if S.end_time is None:
        return
    try:
        if hasattr(S.end_time, 'timestamp'):
            end_ts = S.end_time.timestamp()
        elif isinstance(S.end_time, str):
            from dateutil.parser import parse as dtparse
            end_ts = dtparse(S.end_time).timestamp()
        else:
            end_ts = float(S.end_time)
    except:
        end_ts = 0
    if end_ts <= 0:
        return

    start_ts = end_ts - WINDOW_SECONDS
    elapsed = now - start_ts

    up_id, dn_id = S.tokens
    shares = WHALE_SHARES

    # === PHASE 1: Split buy — buy SHARES of UP + SHARES of DN ===
    if WHALE_P1_START <= elapsed <= WHALE_P1_END and not S.whale_p1_done:
        if now - S.whale_p1_last_try < 15:
            return
        S.whale_p1_last_try = now

        up_bid, up_ask = best_bid_ask(up_id)
        dn_bid, dn_ask = best_bid_ask(dn_id)

        if up_ask is None or dn_ask is None:
            print(f"  ⚠️ 🐋P1: No book data (UP={up_ask} DN={dn_ask})")
            return

        if up_ask > WHALE_P1_MAX_PRICE and dn_ask > WHALE_P1_MAX_PRICE:
            print(f"  ⚠️ 🐋P1: Both expensive (UP={up_ask:.2f} DN={dn_ask:.2f} > {WHALE_P1_MAX_PRICE})")
            return

        print(f"\n🐋 Phase 1 — Split Buy {shares:.0f} shares each (elapsed={elapsed:.0f}s)")

        if up_ask <= WHALE_P1_MAX_PRICE:
            cost = shares * up_ask
            ok, resp = post_market_order(client, up_id, "BUY", cost)
            tag = "✅" if ok else "❌"
            print(f"  {tag} P1 BUY {shares:.0f} UP @ {up_ask:.2f}¢ = ${cost:.2f}")
            if ok:
                S.whale_spent_up += cost
                S.whale_buys.append((1, "UP", up_ask, cost, now))

        if dn_ask <= WHALE_P1_MAX_PRICE:
            cost = shares * dn_ask
            ok, resp = post_market_order(client, dn_id, "BUY", cost)
            tag = "✅" if ok else "❌"
            print(f"  {tag} P1 BUY {shares:.0f} DN @ {dn_ask:.2f}¢ = ${cost:.2f}")
            if ok:
                S.whale_spent_dn += cost
                S.whale_buys.append((1, "DN", dn_ask, cost, now))

        S.whale_p1_done = True
        total = S.whale_spent_up + S.whale_spent_dn
        print(f"  📊 P1 complete: UP=${S.whale_spent_up:.2f} DN=${S.whale_spent_dn:.2f} Total=${total:.2f}")
        return

    # === PHASE 2: Reinforce winner — SHARES on CL direction ===
    if WHALE_P2_START <= elapsed <= WHALE_P2_END and not S.whale_p2_done and S.whale_p1_done:
        if now - S.whale_p2_last_try < 10:
            return
        S.whale_p2_last_try = now

        cl_dir, cl_delta, cl_count = chainlink_feed.cl_direction()
        abs_delta = abs(cl_delta) if cl_delta else 0
        if not cl_dir or abs_delta < WHALE_P2_CL_DELTA:
            return

        token_id = up_id if cl_dir == "UP" else dn_id
        _, ask = best_bid_ask(token_id)

        if ask is None or ask > WHALE_P2_MAX_PRICE:
            print(f"  ⚠️ 🐋P2: {cl_dir} ask={ask} > {WHALE_P2_MAX_PRICE}")
            return

        cost = shares * ask
        print(f"\n🐋 Phase 2 — Reinforce {cl_dir} {shares:.0f} shares (elapsed={elapsed:.0f}s, CL Δ=${abs_delta:.0f})")
        ok, resp = post_market_order(client, token_id, "BUY", cost)
        tag = "✅" if ok else "❌"
        print(f"  {tag} P2 BUY {shares:.0f} {cl_dir} @ {ask:.2f}¢ = ${cost:.2f}")
        if ok:
            if cl_dir == "UP": S.whale_spent_up += cost
            else: S.whale_spent_dn += cost
            S.whale_buys.append((2, cl_dir, ask, cost, now))

        S.whale_p2_done = True
        return

    # === PHASE 3: Final push — SHARES on CL direction with strong confirmation ===
    if WHALE_P3_START <= elapsed <= WHALE_P3_END and not S.whale_p3_done and S.whale_p1_done:
        if now - S.whale_p3_last_try < 10:
            return
        S.whale_p3_last_try = now

        cl_dir, cl_delta, cl_count = chainlink_feed.cl_direction()
        abs_delta = abs(cl_delta) if cl_delta else 0
        if not cl_dir or abs_delta < WHALE_P3_CL_DELTA:
            return

        cl_age = chainlink_feed.on_chain_age()
        if cl_age > WHALE_MAX_CHAIN_AGE:
            return

        token_id = up_id if cl_dir == "UP" else dn_id
        _, ask = best_bid_ask(token_id)

        if ask is None or ask > WHALE_P3_MAX_PRICE:
            print(f"  ⚠️ 🐋P3: {cl_dir} ask={ask} > {WHALE_P3_MAX_PRICE}")
            return

        cost = shares * ask
        print(f"\n🐋 Phase 3 — Final Push {cl_dir} {shares:.0f} shares (elapsed={elapsed:.0f}s, CL Δ=${abs_delta:.0f}, age={cl_age:.0f}s)")
        ok, resp = post_market_order(client, token_id, "BUY", cost)
        tag = "✅" if ok else "❌"
        print(f"  {tag} P3 BUY {shares:.0f} {cl_dir} @ {ask:.2f}¢ = ${cost:.2f}")
        if ok:
            if cl_dir == "UP": S.whale_spent_up += cost
            else: S.whale_spent_dn += cost
            S.whale_buys.append((3, cl_dir, ask, cost, now))

        S.whale_p3_done = True
        return


# ================================================================
#  v5.15: MOMENTUM STRADDLE — CL direction + hedge + TP
# ================================================================

def straddle_check_merge():
    """
    Check if we can profitably merge pairs into USDC.
    Merge when:
    - We have N+ pairs (min(UP, DN) shares)
    - NET profit (after gas) ≥ STRADDLE_MERGE_MIN_NET_PROFIT
    v5.18 PATCH 4: reemplazado umbral fijo STRADDLE_MERGE_MAX_COMBINED por profit neto dinámico.
    Returns True if merge was executed.
    """
    if not STRADDLE_MERGE_ENABLED:
        return False
    if not S.condition_id:
        return False
    if len(S.tokens) != 2:
        return False

    # Calculate pairs available from tracked shares
    pairs = min(S.straddle_shares_up, S.straddle_shares_dn)
    if pairs < STRADDLE_MERGE_MIN_PAIRS:
        return False

    # Compute weighted avg combined cost per pair
    if S.straddle_shares_up <= 0 or S.straddle_shares_dn <= 0:
        return False
    avg_up = S.straddle_spent_up / S.straddle_shares_up
    avg_dn = S.straddle_spent_dn / S.straddle_shares_dn
    avg_combined = avg_up + avg_dn

    # v5.18 PATCH 4: verificar profit NETO tras gas (en lugar de umbral fijo de avg_combined)
    # Se conserva STRADDLE_MERGE_MAX_COMBINED como pre-filtro rápido (rechaza si avg > 1.00)
    if avg_combined > max(STRADDLE_MERGE_MAX_COMBINED, 1.00):
        return False

    # Verify on-chain balance (avoid merging more than we own)
    up_id, dn_id = S.tokens
    if DRY_RUN:
        real_pairs = min(S.straddle_shares_up, S.straddle_shares_dn)
    else:
        real_up = query_conditional_token_balance(up_id)
        real_dn = query_conditional_token_balance(dn_id)
        if real_up is None or real_dn is None:
            return False
        real_pairs = min(real_up, real_dn)

    if real_pairs < STRADDLE_MERGE_MIN_PAIRS:
        print(f"  ⚠️ Merge skipped: pairs={real_pairs:.1f} < min={STRADDLE_MERGE_MIN_PAIRS:.0f}")
        return False

    pairs_to_merge = int(real_pairs)  # floor
    # Profit bruto = pairs × (1 - avg_combined)
    expected_profit = pairs_to_merge * (1.0 - avg_combined)
    net_profit = expected_profit - STRADDLE_MERGE_GAS_COST_USD

    # v5.18 PATCH 4: descartar si el profit neto no vale el gas
    if net_profit < STRADDLE_MERGE_MIN_NET_PROFIT:
        # Log silencioso sólo si estuvimos cerca (evita spam)
        if expected_profit > 0.10:
            print(f"  🔀 Merge skip: gross=${expected_profit:.2f} - gas=${STRADDLE_MERGE_GAS_COST_USD:.2f} "
                  f"= net=${net_profit:.2f} < min=${STRADDLE_MERGE_MIN_NET_PROFIT:.2f}")
        return False

    print(f"\n🔀 MERGE OPPORTUNITY: {pairs_to_merge} pairs | "
          f"avg combined=${avg_combined:.3f} | gross=${expected_profit:+.2f} "
          f"| net (after gas)=${net_profit:+.2f}")

    ok = try_merge_positions(S.condition_id, pairs_to_merge)
    if ok:
        # Update tracking: subtract merged shares + proportional cost
        cost_up_merged = pairs_to_merge * avg_up
        cost_dn_merged = pairs_to_merge * avg_dn
        S.straddle_shares_up -= pairs_to_merge
        S.straddle_shares_dn -= pairs_to_merge
        S.straddle_spent_up -= cost_up_merged
        S.straddle_spent_dn -= cost_dn_merged
        # Add realized profit NETO (no bruto) to running total
        if not hasattr(S, 'straddle_merged_profit'):
            S.straddle_merged_profit = 0.0
        S.straddle_merged_profit += net_profit
    return ok


def straddle_check_tp(client):
    """Check if combined position has $40+ profit → sell ALL."""
    if len(S.tokens) != 2:
        return
    if S.straddle_sold_up and S.straddle_sold_dn:
        return  # already sold everything

    up_id, dn_id = S.tokens
    total_cost = S.straddle_spent_up + S.straddle_spent_dn
    if total_cost <= 0:
        return

    # Calculate current value of both sides
    total_value = 0.0
    up_bid, _ = best_bid_ask(up_id)
    dn_bid, _ = best_bid_ask(dn_id)

    up_val = S.straddle_shares_up * up_bid if (up_bid and S.straddle_shares_up > 0 and not S.straddle_sold_up) else 0
    dn_val = S.straddle_shares_dn * dn_bid if (dn_bid and S.straddle_shares_dn > 0 and not S.straddle_sold_dn) else 0
    total_value = up_val + dn_val

    profit = total_value - total_cost
    if profit < STRADDLE_TP_USD:
        return

    # === SELL EVERYTHING ===
    print(f"\n🎯 TP ${profit:.2f} ≥ ${STRADDLE_TP_USD:.0f} | "
          f"value=${total_value:.2f} - cost=${total_cost:.2f} = profit ${profit:.2f}")

    tick = S.tick or 0.01

    def _sell_side(token_id, tracked_shares, current_bid, side_label):
        """Use the proven _execute_sell pattern: query on-chain, market, then smart limit fallback."""
        # 1. Query actual on-chain balance (skip in DRY_RUN)
        if DRY_RUN:
            sell_amt = tracked_shares
        else:
            actual_balance = query_conditional_token_balance(token_id)
            if actual_balance is None:
                print(f"  ⚠️ {side_label}: balance query failed, using tracked={tracked_shares:.0f}")
                sell_amt = tracked_shares
            else:
                if actual_balance < 0.5:
                    print(f"  ⏭️ {side_label}: on-chain balance={actual_balance:.2f} ≈ 0 (ghost or already sold) — skip")
                    return True  # nothing to sell
                sell_amt = actual_balance
                if abs(actual_balance - tracked_shares) > 0.5:
                    print(f"  📊 {side_label} balance correction: tracked={tracked_shares:.0f} actual={actual_balance:.2f}")

        # 2. v5.18 FIX D1: Polymarket CLOB acepta size con 2 decimales (todos los
        #    tick sizes 0.1/0.01/0.001/0.0001 → size precision = 2). Antes usábamos
        #    int(sell_amt) que floor a entero, dejando residuos de 0-0.99 shares
        #    sin vender que tampoco se reclamaban al cierre. Ahora floor a 0.01.
        import math
        sell_amt = math.floor(sell_amt * 100) / 100
        if sell_amt < 0.01:
            print(f"  ⏭️ {side_label}: sell amount rounds to 0 — skip")
            return True

        # 3. Try market order first
        ok, resp = post_market_order(client, token_id, "SELL", sell_amt)
        if ok:
            print(f"  ✅ SELL {sell_amt:.2f} {side_label} @{current_bid:.2f} (market)")
            return True

        # 4. Smart limit fallback (bid - 2 ticks, with floor)
        if SELL_USE_LIMIT_FALLBACK:
            if current_bid and current_bid > 0.02:
                limit_price = current_bid - (2 * tick)
            else:
                limit_price = max(0.02, current_bid - SELL_LIMIT_DISCOUNT if current_bid else 0.02)
            limit_price = clamp_price(limit_price, tick, 0.01, 0.99)
            print(f"  ⚠️ Market failed, LIMIT SELL @{limit_price:.2f}")
            ok, resp = post_limit_sell(client, token_id, limit_price, sell_amt)
            if ok:
                print(f"  ✅ SELL {sell_amt:.2f} {side_label} @{limit_price:.2f} (limit)")
                return True

        print(f"  ❌ SELL {sell_amt:.2f} {side_label} — both market and limit failed")
        return False

    # Sell UP
    if S.straddle_shares_up > 0 and not S.straddle_sold_up and up_bid:
        up_shares_before = S.straddle_shares_up
        up_cost_before = S.straddle_spent_up
        if _sell_side(up_id, S.straddle_shares_up, up_bid, "UP"):
            S.straddle_sold_up = True
            # Record realized P&L: received bid × shares, subtract original cost
            realized_up = (up_shares_before * up_bid) - up_cost_before
            S.straddle_merged_profit += realized_up
            # Zero out position: shares sold, cost counted as realized
            S.straddle_shares_up = 0.0
            S.straddle_spent_up = 0.0

    # Sell DN
    if S.straddle_shares_dn > 0 and not S.straddle_sold_dn and dn_bid:
        dn_shares_before = S.straddle_shares_dn
        dn_cost_before = S.straddle_spent_dn
        if _sell_side(dn_id, S.straddle_shares_dn, dn_bid, "DN"):
            S.straddle_sold_dn = True
            realized_dn = (dn_shares_before * dn_bid) - dn_cost_before
            S.straddle_merged_profit += realized_dn
            S.straddle_shares_dn = 0.0
            S.straddle_spent_dn = 0.0

    if S.straddle_sold_up and S.straddle_sold_dn:
        tg_send(f"🎯 TP ALL | realized profit ${S.straddle_merged_profit:+.2f}")

def copy_trading_tick(client):
    """
    Momentum straddle — buys MORE on CL direction, LESS on opposite.
    STRADDLE_SHARES on momentum side, STRADDLE_SHARES/RATIO on hedge side.
    If no CL signal, buys equal on both (pure straddle fallback).
    Hold to expiry, auto-claim winner.
    """
    if not S.trading_enabled or S.paused_by_telegram:
        return
    if len(S.tokens) != 2:
        return

    now = time.time()
    up_id, dn_id = S.tokens

    # ================================================================
    # v5.18 PATCH 1 + HOTFIX: Drift-sync resistente a lag RPC.
    # Cambios vs versión anterior:
    #   1. COOLDOWN: durante N segundos tras un BUY exitoso NO se sincroniza
    #      (la blockchain tarda 2-5s en propagar balance al RPC público, y un
    #      sync prematuro leía 0 y marcaba "external sell" falsamente).
    #   2. DOBLE CONFIRMACIÓN: un "large drift" requiere N ticks consecutivos
    #      antes de frenar la ventana. Filtra lag transitorio del RPC.
    #   3. Se evalúa "large drift" ANTES del sync (con shares pre-sync),
    #      para no perder la señal por sincronizar a 0.
    # ================================================================
    in_post_buy_cooldown = (now - S.last_successful_buy_ts) < STRADDLE_POST_BUY_COOLDOWN_SEC

    if (not DRY_RUN
            and not in_post_buy_cooldown
            and (S.straddle_shares_up > 0 or S.straddle_shares_dn > 0)):
        real_up = query_conditional_token_balance(up_id)
        real_dn = query_conditional_token_balance(dn_id)
        if real_up is not None and real_dn is not None:
            pre_sync_up = S.straddle_shares_up
            pre_sync_dn = S.straddle_shares_dn
            drift_up = pre_sync_up - real_up
            drift_dn = pre_sync_dn - real_dn

            # Evaluar si hay "large drift" (>50% missing) ANTES de sincronizar
            large_drift_up = (pre_sync_up > 5 and drift_up > pre_sync_up * 0.50)
            large_drift_dn = (pre_sync_dn > 5 and drift_dn > pre_sync_dn * 0.50)
            is_large_drift = large_drift_up or large_drift_dn

            if is_large_drift:
                # Incrementar contador de strikes consecutivos
                S.large_drift_strikes += 1
                if S.large_drift_strikes < STRADDLE_LARGE_DRIFT_CONFIRMATIONS:
                    # Aún no confirmado — no hacer NADA (ni siquiera sync) para dar
                    # chance al RPC a propagar. Si en el próximo tick ya no hay drift,
                    # se resetea el contador.
                    print(f"  ⏳ Drift strike {S.large_drift_strikes}/{STRADDLE_LARGE_DRIFT_CONFIRMATIONS}: "
                          f"tracked UP={pre_sync_up:.1f}/DN={pre_sync_dn:.1f}, "
                          f"on-chain UP={real_up:.1f}/DN={real_dn:.1f} — esperando confirmación")
                else:
                    # Confirmado: sell externo real o posición perdida
                    print(f"\n⚠️ Large drift CONFIRMADO tras {S.large_drift_strikes} ticks — "
                          f"tracked pre-sync: UP={pre_sync_up:.1f}/DN={pre_sync_dn:.1f}, "
                          f"on-chain: UP={real_up:.1f}/DN={real_dn:.1f}")
                    print(f"   Likely external sell or order failure. Stopping buys for this window.")
                    # Sincronizar y marcar como sold sólo aquí (tras confirmación)
                    if pre_sync_up > 0.01:
                        S.straddle_spent_up *= (real_up / pre_sync_up) if real_up > 0 else 0
                    S.straddle_shares_up = max(0.0, real_up)
                    if pre_sync_dn > 0.01:
                        S.straddle_spent_dn *= (real_dn / pre_sync_dn) if real_dn > 0 else 0
                    S.straddle_shares_dn = max(0.0, real_dn)
                    S.straddle_sold_up = True
                    S.straddle_sold_dn = True
                    tg_send(f"⚠️ Large drift confirmado — bot stopping for this window")
                    S.large_drift_strikes = 0  # reset para próxima ventana
            else:
                # No hay large drift: resetear contador de strikes
                if S.large_drift_strikes > 0:
                    print(f"  ✅ Drift strike reset (RPC propagó: "
                          f"on-chain UP={real_up:.1f}/DN={real_dn:.1f})")
                S.large_drift_strikes = 0

                # Sync normal para drifts pequeños (slippage / partial fills)
                if abs(drift_up) > 0.5:
                    if pre_sync_up > 0.01:
                        S.straddle_spent_up *= (real_up / pre_sync_up) if real_up > 0 else 0
                    S.straddle_shares_up = max(0.0, real_up)
                if abs(drift_dn) > 0.5:
                    if pre_sync_dn > 0.01:
                        S.straddle_spent_dn *= (real_dn / pre_sync_dn) if real_dn > 0 else 0
                    S.straddle_shares_dn = max(0.0, real_dn)

    # === Check merge opportunity (convert pairs → USDC instantly) ===
    straddle_check_merge()

    # === Check TP on every tick ===
    straddle_check_tp(client)

    # Process pending claims from previous windows
    process_pending_claims()

    # Calculate elapsed time in window
    if S.end_time is None:
        return
    try:
        if hasattr(S.end_time, 'timestamp'):
            end_ts = S.end_time.timestamp()
        elif isinstance(S.end_time, str):
            from dateutil.parser import parse as dtparse
            end_ts = dtparse(S.end_time).timestamp()
        else:
            end_ts = float(S.end_time)
    except:
        return
    if end_ts <= 0:
        return

    start_ts = end_ts - WINDOW_SECONDS
    elapsed = now - start_ts

    # Only buy within configured window
    if elapsed < STRADDLE_START_SEC or elapsed > STRADDLE_END_SEC:
        return

    # Check interval
    if now - S.straddle_last_buy_ts < STRADDLE_INTERVAL:
        return

    # Check budget cap
    total_spent = S.straddle_spent_up + S.straddle_spent_dn
    if total_spent >= STRADDLE_MAX_BUDGET:
        return

    # Get current asks from WebSocket book (up_id, dn_id ya definidos al inicio del tick)
    _, up_ask = best_bid_ask(up_id)
    _, dn_ask = best_bid_ask(dn_id)

    if up_ask is None or dn_ask is None:
        return

    # Skip if either side too expensive
    if up_ask > STRADDLE_MAX_PRICE or dn_ask > STRADDLE_MAX_PRICE:
        return

    # === Determine momentum direction from Chainlink ===
    cl_dir, cl_delta, cl_cnt = chainlink_feed.cl_direction()
    abs_delta = abs(cl_delta) if cl_delta else 0

    hedge_shares = max(1, int(STRADDLE_SHARES / STRADDLE_RATIO))

    # ================================================================
    # v5.16: ASYMMETRIC TIMING MODE
    # Phase 1 (0 → PHASE1_MAX_SEC or until PHASE1_SHARES acc): momentum only
    # Phase 2 (after Phase 1): hedge only if opposite side ≤ HEDGE_MAX_PRICE
    # ================================================================
    if STRADDLE_ASYMMETRIC:
        # If TP already sold either side, stop buying this window completely
        # (don't re-accumulate a position that was just closed for profit)
        if S.straddle_sold_up or S.straddle_sold_dn:
            return

        # v5.18 PATCH 1: drift-sync movido al inicio del tick (antes de merge/TP).
        # Aquí ya no va nada — el sync ocurrió antes.

        # Determine momentum direction
        if cl_dir == "UP" and abs_delta >= STRADDLE_MIN_CL:
            mom_side = "UP"
            mom_shares_acc = S.straddle_shares_up
            mom_ask = up_ask
            hedge_side = "DN"
            hedge_ask = dn_ask
            mom_label = f"⬆️ CL+${abs_delta:.0f}"
        elif cl_dir == "DN" and abs_delta >= STRADDLE_MIN_CL:
            mom_side = "DN"
            mom_shares_acc = S.straddle_shares_dn
            mom_ask = dn_ask
            hedge_side = "UP"
            hedge_ask = up_ask
            mom_label = f"⬇️ CL-${abs_delta:.0f}"
        else:
            # No CL signal → skip this round entirely in asymmetric mode
            mom_label = f"⚖️ CL=${abs_delta:.0f} (<{STRADDLE_MIN_CL:.0f}) — skip"
            return

        # Determine phase
        # Phase 1 ends when either:
        # 1. We accumulated target momentum shares, OR
        # 2. Less than PHASE1_MAX_SEC remains in window (need time for Phase 2)
        time_remaining = (STRADDLE_END_SEC - elapsed)
        phase1_done = (mom_shares_acc >= STRADDLE_PHASE1_SHARES) or (time_remaining <= STRADDLE_PHASE1_MAX_SEC)

        if not phase1_done:
            # === PHASE 1: Accumulate momentum side only ===
            if mom_ask > STRADDLE_MAX_PRICE:
                return  # too expensive even for momentum
            cost = STRADDLE_SHARES * mom_ask
            if cost < 1.0:
                return
            remaining = STRADDLE_MAX_BUDGET - total_spent
            if cost > remaining:
                return

            # ================================================================
            # v5.18 PATCH 3: Filtros anti-piramidación para rondas R2+
            # ================================================================
            my_shares_here = S.straddle_shares_up if mom_side == "UP" else S.straddle_shares_dn
            is_pyramiding = my_shares_here >= STRADDLE_SHARES  # ya compramos ≥1 ronda aquí

            # --- FIX E1: No abrir posición en lado CONTRARIO si ya hay exposición ---
            # v5.18 FIX E1: si el CL flipea y abrimos el lado opuesto, terminamos
            # con ambos lados → pagamos cost_up + cost_dn pero solo 1 gana.
            # Net: en los 3 mercados con doble-lado la sesión perdió ~$25 puro.
            # Esta regla bloquea la nueva apertura del lado opuesto si ya tenemos
            # posición significativa en el lado contrario. Mejor mantener la apuesta
            # original (que tenía señal CL fuerte cuando se abrió) y aceptar el
            # posible loss que doblar la exposición.
            opposite_shares = S.straddle_shares_dn if mom_side == "UP" else S.straddle_shares_up
            if opposite_shares >= STRADDLE_SHARES * 0.5 and my_shares_here < 0.5:
                opp_side = "DN" if mom_side == "UP" else "UP"
                print(f"  ⛔ SKIP P1: CL flipeó a {mom_side} pero ya tengo "
                      f"{opposite_shares:.0f}sh {opp_side} — NO abrir lado contrario")
                return

            # --- FILTRO A: Límite duro de piramidación ---
            # Si configurado en env: STRADDLE_MAX_SAME_SIDE (default 2)
            # v5.18 FIX C: aplicar tolerancia por slippage. Con STRADDLE_SHARES=20 y
            # MAX_SAME_SIDE=2, el umbral teórico sería 40 shares, pero los BUYs reales
            # acumulan menos por slippage (ej: 2 rondas → 37-38 shares reales), lo que
            # permitía una 3ra ronda no intencional. Restamos 1/3 de STRADDLE_SHARES
            # como colchón para cerrar ese gap.
            max_shares_threshold = (STRADDLE_SHARES * STRADDLE_MAX_SAME_SIDE) - (STRADDLE_SHARES / 3)
            if is_pyramiding and my_shares_here >= max_shares_threshold:
                print(f"  ⛔ SKIP P1: límite {STRADDLE_MAX_SAME_SIDE} rondas {mom_side} "
                      f"alcanzado ({my_shares_here:.0f}sh ≥ {max_shares_threshold:.0f})")
                return

            # --- FILTRO B: CL sign-flip (inestabilidad de señal) ---
            if is_pyramiding:
                if not hasattr(S, 'cl_delta_history'):
                    S.cl_delta_history = []
                S.cl_delta_history.append((now, cl_delta))
                # Mantener solo últimos 60s
                S.cl_delta_history = [(t, d) for t, d in S.cl_delta_history if now - t < 60]

                # Contar flips de signo en últimos STRADDLE_CL_STABILITY_SEC
                recent = [(t, d) for t, d in S.cl_delta_history if now - t < STRADDLE_CL_STABILITY_SEC]
                recent_signs = [1 if d > STRADDLE_MIN_CL else (-1 if d < -STRADDLE_MIN_CL else 0)
                                for _, d in recent]
                sign_flips = sum(1 for i in range(1, len(recent_signs))
                                 if recent_signs[i] != 0 and recent_signs[i-1] != 0
                                 and recent_signs[i] != recent_signs[i-1])
                if sign_flips >= 1:
                    print(f"  ⛔ SKIP P1: CL Δ inestable ({sign_flips} flips en {STRADDLE_CL_STABILITY_SEC}s) — "
                          f"ya tengo {my_shares_here:.0f}sh {mom_side}")
                    return

            # --- FILTRO C: Veto por forming candle (contra-dirección) ---
            if is_pyramiding and STRADDLE_VETO_ON_CANDLE:
                try:
                    forming_type = ""
                    if candle_analyzer and getattr(candle_analyzer, '_current_candle', None):
                        forming_type = (candle_analyzer._current_candle.get("type", "") or "").upper()
                    is_bull_form = 'BULL' in forming_type
                    is_bear_form = 'BEAR' in forming_type or 'REJECTION_UP' in forming_type

                    if mom_side == "DN" and is_bull_form:
                        print(f"  ⛔ SKIP P1 R{S.straddle_rounds+1}: forming={forming_type} contradice DN "
                              f"(ya tengo {my_shares_here:.0f}sh DN)")
                        return
                    if mom_side == "UP" and is_bear_form:
                        print(f"  ⛔ SKIP P1 R{S.straddle_rounds+1}: forming={forming_type} contradice UP "
                              f"(ya tengo {my_shares_here:.0f}sh UP)")
                        return
                except Exception:
                    pass  # si el analyzer falla, no bloquear
            # ================================================================
            # Fin filtros anti-piramidación
            # ================================================================

            S.straddle_last_buy_ts = now
            S.straddle_rounds += 1

            token_id = up_id if mom_side == "UP" else dn_id
            print(f"\n📋 ASYM P1 R{S.straddle_rounds} (elapsed={elapsed:.0f}s) | {mom_label} | "
                  f"{mom_side}@{mom_ask:.2f}×{STRADDLE_SHARES:.0f} = ${cost:.2f} "
                  f"(acc: {mom_shares_acc:.0f}/{STRADDLE_PHASE1_SHARES:.0f})")
            ok, resp = post_market_order(client, token_id, "BUY", cost)
            if ok:
                # v5.18 PATCH 2: usar shares reales recibidas
                actual_shares = resp.get("actual_shares", STRADDLE_SHARES) if isinstance(resp, dict) else STRADDLE_SHARES
                actual_usdc   = resp.get("actual_usdc",   cost)            if isinstance(resp, dict) else cost
                eff_price = (actual_usdc / actual_shares) if actual_shares > 0 else mom_ask
                slip_pct  = ((eff_price - mom_ask) / mom_ask * 100) if mom_ask > 0 else 0

                if mom_side == "UP":
                    S.straddle_spent_up += actual_usdc
                    S.straddle_shares_up += actual_shares
                else:
                    S.straddle_spent_dn += actual_usdc
                    S.straddle_shares_dn += actual_shares

                S.last_buy_side = mom_side  # v5.18 PATCH 3
                S.last_successful_buy_ts = now  # v5.18 HOTFIX: cooldown drift-sync
                print(f"  ✅ BUY {actual_shares:.1f} {mom_side} @{mom_ask:.2f} "
                      f"(eff=${eff_price:.3f}, slip={slip_pct:+.1f}%, paid=${actual_usdc:.2f})")
                new_total = S.straddle_spent_up + S.straddle_spent_dn
                tg_send(f"📋 P1 {mom_side} {actual_shares:.0f}sh @{eff_price:.2f} = ${actual_usdc:.2f} | "
                        f"${new_total:.0f}/{STRADDLE_MAX_BUDGET:.0f}")
            else:
                print(f"  ❌ BUY {STRADDLE_SHARES:.0f} {mom_side} @{mom_ask:.2f} = ${cost:.2f}")
            return
        else:
            # === PHASE 2: Buy hedge to PROTECT existing position ===
            # v5.18 PATCH 6: el hedge debe cubrir la exposición actual, NO basarse en CL.
            # Bug anterior: hedge_side se definía como "opuesto al CL actual", pero si el CL
            # se había invertido, eso coincidía con el lado donde ya teníamos posición → el
            # bot doblaba la apuesta en vez de cubrirla.
            # Fix: determinar hedge_side por la posición actual (cubrir el lado expuesto).

            if S.straddle_shares_up > S.straddle_shares_dn + 0.5:
                # Tenemos exposición neta UP → hedge es DN
                hedge_side = "DN"
                hedge_ask = dn_ask
            elif S.straddle_shares_dn > S.straddle_shares_up + 0.5:
                # Tenemos exposición neta DN → hedge es UP
                hedge_side = "UP"
                hedge_ask = up_ask
            else:
                # Posición balanceada (o vacía) → no hay qué hedgear
                return

            if hedge_ask is None or hedge_ask > STRADDLE_HEDGE_MAX_PRICE:
                # Hedge too expensive — skip (CL was probably wrong, don't throw more money)
                return
            cost = STRADDLE_HEDGE_SHARES * hedge_ask
            if cost < 1.0:
                return
            remaining = STRADDLE_MAX_BUDGET - total_spent
            if cost > remaining:
                return

            S.straddle_last_buy_ts = now
            S.straddle_rounds += 1

            # Determine what side we're protecting (for clearer logs)
            protected_side = "DN" if hedge_side == "UP" else "UP"
            exposure = S.straddle_shares_up if protected_side == "UP" else S.straddle_shares_dn

            token_id = up_id if hedge_side == "UP" else dn_id
            print(f"\n📋 ASYM P2 R{S.straddle_rounds} (elapsed={elapsed:.0f}s) | {mom_label} | "
                  f"HEDGE {hedge_side}@{hedge_ask:.2f}×{STRADDLE_HEDGE_SHARES:.0f} = ${cost:.2f} "
                  f"(protege {exposure:.0f}sh {protected_side}, ≤{STRADDLE_HEDGE_MAX_PRICE:.2f}) ✅ cheap")
            ok, resp = post_market_order(client, token_id, "BUY", cost)
            if ok:
                # v5.18 PATCH 2: usar shares reales recibidas
                actual_shares = resp.get("actual_shares", STRADDLE_HEDGE_SHARES) if isinstance(resp, dict) else STRADDLE_HEDGE_SHARES
                actual_usdc   = resp.get("actual_usdc",   cost)                 if isinstance(resp, dict) else cost
                eff_price = (actual_usdc / actual_shares) if actual_shares > 0 else hedge_ask
                slip_pct  = ((eff_price - hedge_ask) / hedge_ask * 100) if hedge_ask > 0 else 0

                if hedge_side == "UP":
                    S.straddle_spent_up += actual_usdc
                    S.straddle_shares_up += actual_shares
                else:
                    S.straddle_spent_dn += actual_usdc
                    S.straddle_shares_dn += actual_shares

                S.last_buy_side = hedge_side  # v5.18 PATCH 3
                S.last_successful_buy_ts = now  # v5.18 HOTFIX: cooldown drift-sync
                print(f"  ✅ BUY {actual_shares:.1f} {hedge_side} @{hedge_ask:.2f} "
                      f"(eff=${eff_price:.3f}, slip={slip_pct:+.1f}%, paid=${actual_usdc:.2f})")
                new_total = S.straddle_spent_up + S.straddle_spent_dn
                tg_send(f"📋 P2 HEDGE {hedge_side} {actual_shares:.0f}sh @{eff_price:.2f} = ${actual_usdc:.2f} | "
                        f"${new_total:.0f}/{STRADDLE_MAX_BUDGET:.0f}")
            else:
                print(f"  ❌ BUY {STRADDLE_HEDGE_SHARES:.0f} {hedge_side} @{hedge_ask:.2f} = ${cost:.2f}")
            return

    # ================================================================
    # STANDARD STRADDLE MODE (non-asymmetric)
    # ================================================================
    if cl_dir == "UP" and abs_delta >= STRADDLE_MIN_CL:
        up_shares = STRADDLE_SHARES
        dn_shares = hedge_shares
        mom_label = f"⬆️ CL+${abs_delta:.0f}"
    elif cl_dir == "DN" and abs_delta >= STRADDLE_MIN_CL:
        up_shares = hedge_shares
        dn_shares = STRADDLE_SHARES
        mom_label = f"⬇️ CL-${abs_delta:.0f}"
    else:
        # No clear CL signal → equal shares (pure straddle)
        up_shares = STRADDLE_SHARES
        dn_shares = STRADDLE_SHARES
        mom_label = f"⚖️ CL=${abs_delta:.0f} (<{STRADDLE_MIN_CL:.0f})"

    # If TP already sold either side, stop buying completely this window
    if S.straddle_sold_up or S.straddle_sold_dn:
        return

    # Calculate costs
    cost_up = up_shares * up_ask if up_shares > 0 else 0
    cost_dn = dn_shares * dn_ask if dn_shares > 0 else 0
    cost_total = cost_up + cost_dn

    # Minimum order check ($1)
    if cost_total < 1.0:
        return
    if cost_up > 0 and cost_up < 1.0:
        return
    if cost_dn > 0 and cost_dn < 1.0:
        return

    # Budget remaining check
    remaining = STRADDLE_MAX_BUDGET - total_spent
    if cost_total > remaining:
        return

    S.straddle_last_buy_ts = now
    S.straddle_rounds += 1

    combined = up_ask + dn_ask
    print(f"\n📋 STRADDLE R{S.straddle_rounds} (elapsed={elapsed:.0f}s) | {mom_label} | "
          f"UP@{up_ask:.2f}×{up_shares:.0f} + DN@{dn_ask:.2f}×{dn_shares:.0f} = ${cost_total:.2f}")

    # Buy UP
    ok_up = False
    resp_up = None
    if up_shares > 0:
        ok_up, resp_up = post_market_order(client, up_id, "BUY", cost_up)
        tag_up = "✅" if ok_up else "❌"
        print(f"  {tag_up} BUY {up_shares:.0f} UP @{up_ask:.2f}¢ = ${cost_up:.2f}")
    elif S.straddle_sold_up:
        print(f"  ⏭️ UP — already TP'd")

    # Buy DN
    ok_dn = False
    resp_dn = None
    if dn_shares > 0:
        ok_dn, resp_dn = post_market_order(client, dn_id, "BUY", cost_dn)
        tag_dn = "✅" if ok_dn else "❌"
        print(f"  {tag_dn} BUY {dn_shares:.0f} DN @{dn_ask:.2f}¢ = ${cost_dn:.2f}")
    elif S.straddle_sold_dn:
        print(f"  ⏭️ DN — already TP'd")

    # v5.18 PATCH 2: usar shares reales recibidas
    if ok_up:
        actual_shares_up = resp_up.get("actual_shares", up_shares) if isinstance(resp_up, dict) else up_shares
        actual_usdc_up   = resp_up.get("actual_usdc",   cost_up)   if isinstance(resp_up, dict) else cost_up
        S.straddle_spent_up += actual_usdc_up
        S.straddle_shares_up += actual_shares_up
        S.last_buy_side = "UP"
        S.last_successful_buy_ts = now  # v5.18 HOTFIX: cooldown drift-sync
    if ok_dn:
        actual_shares_dn = resp_dn.get("actual_shares", dn_shares) if isinstance(resp_dn, dict) else dn_shares
        actual_usdc_dn   = resp_dn.get("actual_usdc",   cost_dn)   if isinstance(resp_dn, dict) else cost_dn
        S.straddle_spent_dn += actual_usdc_dn
        S.straddle_shares_dn += actual_shares_dn
        S.last_buy_side = "DN"
        S.last_successful_buy_ts = now  # v5.18 HOTFIX: cooldown drift-sync

    new_total = S.straddle_spent_up + S.straddle_spent_dn
    if ok_up or ok_dn:
        tg_send(f"📋 R{S.straddle_rounds} {mom_label} | "
                f"UP {up_shares:.0f}sh@{up_ask:.2f} DN {dn_shares:.0f}sh@{dn_ask:.2f} | "
                f"${new_total:.0f}/{STRADDLE_MAX_BUDGET:.0f}")


# ══════════════════════════════════════════════════════════════════════════════
# REGISTRO EN SOMBRA (2026-10-25) — SOLO REGISTRA, NUNCA COMPRA
# ──────────────────────────────────────────────────────────────────────────────
# Objetivo: medir qué aprobaría el bot ANTES de t+195 (desde SHADOW_FROM_SEC) con:
#   variante "PG": la lógica exacta del bot (Chainlink Polygon + pick_signal_trend_follow
#                  + los filtros del fast-track), evaluada desde t+120.
#   variante "DS": dispara cuando Chainlink Data Streams (el precio con el que resuelve
#                  Polymarket, ~2-3 s de atraso) marca ≥ MIN_CL_DELTA_USD a favor; aplica
#                  los mismos filtros del fast-track y registra qué diría la función de señal.
# Escribe en SHADOW_LOG_FILE (shadow_log.jsonl). No toca signals_log, órdenes, saldo,
# estado de compra ni Telegram. Cualquier error se ignora (no puede detener al bot).
# _shadow_ft_check() es COPIA de fast_track_check() (mismas variables de entorno y
# mismo orden); si se cambia fast_track_check, actualizar también esta copia.
# Apagar: SHADOW_ENABLE=0
# ══════════════════════════════════════════════════════════════════════════════
_SHADOW_CTX = {"active": False}
SHADOW_ENABLE    = os.getenv("SHADOW_ENABLE", "1") == "1"
SHADOW_FROM_SEC  = float(os.getenv("SHADOW_FROM_SEC", "120"))
SHADOW_TO_SEC    = float(os.getenv("SHADOW_TO_SEC", "260"))
SHADOW_EVERY_SEC = float(os.getenv("SHADOW_EVERY_SEC", "1.0"))
SHADOW_LOG_FILE  = os.getenv("SHADOW_LOG_FILE", "shadow_log.jsonl")
SHADOW_DS_MAX_AGE = float(os.getenv("SHADOW_DS_MAX_AGE", "6"))


class _ShadowDSFeed:
    """Chainlink Data Streams vía el canal público de Polymarket (topic
    crypto_prices_chainlink). Solo para la sombra. Se reconecta si el canal se calla
    (manda historial al conectar, así que no se pierden puntos)."""
    URL = "wss://ws-live-data.polymarket.com"

    def __init__(self):
        self._lock = threading.Lock()
        self._px = deque(maxlen=1800)      # (ts, precio) ~30 min
        self._thread = None
        self._last_data = 0.0
        self.reconnects = 0

    def start(self):
        if self._thread and self._thread.is_alive():
            return
        self._thread = threading.Thread(target=self._run, name="ShadowDS", daemon=True)
        self._thread.start()

    def _ingest(self, d):
        if not isinstance(d, dict):
            return
        pl = d.get("payload") or {}
        items = []
        if isinstance(pl, dict):
            if "value" in pl:
                items.append(pl)
            for k in ("data", "updates"):
                if isinstance(pl.get(k), list):
                    items += pl[k]
        pts = []
        for it in items:
            try:
                sym = str(it.get("symbol", pl.get("symbol", ""))).lower()
                if sym and ASSET not in sym:
                    continue
                t = it.get("timestamp", d.get("timestamp"))
                t = float(t) if t is not None else time.time()
                if t > 1e12:
                    t /= 1000.0
                pts.append((t, float(it["value"])))
            except Exception:
                continue
        pts.sort()
        with self._lock:
            for t, v in pts:
                if not self._px or t > self._px[-1][0]:
                    self._px.append((t, v))
        if pts:
            self._last_data = time.time()

    def _run(self):
        sub = json.dumps({"action": "subscribe",
                          "subscriptions": [{"topic": "crypto_prices_chainlink", "type": "*"}]})
        while True:
            ws = None
            try:
                ws = websocket.create_connection(self.URL, timeout=10,
                                                 sslopt={"cert_reqs": ssl.CERT_NONE})
                ws.send(sub)
                self.reconnects += 1
                t_conn = time.time(); last_ping = time.time()
                while True:
                    if time.time() - max(self._last_data, t_conn) > 5:
                        break                       # silencio → reconectar
                    if time.time() - last_ping >= 5:
                        try:
                            ws.send("PING")
                        except Exception:
                            break
                        last_ping = time.time()
                    ws.settimeout(5)
                    try:
                        raw = ws.recv()
                    except websocket.WebSocketTimeoutException:
                        continue
                    if not raw or raw in ("PONG", "pong"):
                        continue
                    try:
                        data = json.loads(raw)
                    except Exception:
                        continue
                    for x in (data if isinstance(data, list) else [data]):
                        self._ingest(x)
            except Exception:
                time.sleep(2)
            finally:
                try:
                    if ws:
                        ws.close()
                except Exception:
                    pass

    def at(self, t):
        """Precio vigente en el segundo t: el último con ts < t (como el PTB de Polymarket)."""
        with self._lock:
            best = None
            for ts, v in self._px:
                if ts < t:
                    best = (ts, v)
                else:
                    break
            return best

    def latest(self):
        with self._lock:
            return self._px[-1] if self._px else None


_shadow_ds = _ShadowDSFeed()
_SHADOW_STATE = {"slug": None, "logged": set(), "last_ts": 0.0}


def _shadow_ft_check(signal, ask):
    """COPIA de fast_track_check() (maybe_enter_position). Mismas variables de entorno."""
    USE_FAST_TRACK = os.getenv("USE_FAST_TRACK", "0") == "1"
    FT_PRICE_MIN = float(os.getenv("FT_PRICE_MIN", "0.85"))
    FT_PRICE_MAX = float(os.getenv("FT_PRICE_MAX", "0.97"))
    FT_BN_CHG_MIN = float(os.getenv("FT_BN_CHG_MIN", "40"))
    FT_RSI_UP_MAX = float(os.getenv("FT_RSI_UP_MAX", "75"))
    FT_RSI_DN_MIN = float(os.getenv("FT_RSI_DN_MIN", "25"))
    FT_REQUIRE_MACD_MATCH = os.getenv("FT_REQUIRE_MACD_MATCH", "1") == "1"
    FT_REQUIRE_CANDLE_COHERENT = os.getenv("FT_REQUIRE_CANDLE_COHERENT", "1") == "1"
    FT_IMB_MAX = float(os.getenv("FT_IMB_MAX", "100"))
    FT_MACD_HIST_MIN = float(os.getenv("FT_MACD_HIST_MIN", "0"))
    FT_MACD_SKIP_ABOVE_PRICE = float(os.getenv("FT_MACD_SKIP_ABOVE_PRICE", "0.0"))
    FT_REQUIRE_LAST_CANDLE_OK = os.getenv("FT_REQUIRE_LAST_CANDLE_OK", "0") == "1"
    FT_REJECT_DOJI = os.getenv("FT_REJECT_DOJI", "1") == "1"
    FT_BLOCK_VELOCITY_AGAINST = os.getenv("FT_BLOCK_VELOCITY_AGAINST", "1") == "1"
    FT_VELOCITY_MIN = float(os.getenv("FT_VELOCITY_MIN", "0.5"))
    FT_ATR_MAX_AT_HIGH_PRICE = float(os.getenv("FT_ATR_MAX_AT_HIGH_PRICE", "100"))
    FT_ATR_PRICE_MIN = float(os.getenv("FT_ATR_PRICE_MIN", "0.96"))
    if not USE_FAST_TRACK:
        return False, "USE_FAST_TRACK=0"
    if not str(signal).startswith("TREND_"):
        return False, "no es TREND"
    side_is_up = signal == "TREND_UP"
    if ask < FT_PRICE_MIN:
        return False, f"price ${ask:.3f} < FT_PRICE_MIN ${FT_PRICE_MIN}"
    if ask > FT_PRICE_MAX:
        return False, f"price ${ask:.3f} > FT_PRICE_MAX ${FT_PRICE_MAX}"
    try:
        rsi_now, _ = candle_analyzer.rsi()
    except Exception:
        rsi_now = None
    if rsi_now is not None:
        if side_is_up and rsi_now > FT_RSI_UP_MAX:
            return False, f"RSI={rsi_now:.0f} > FT_RSI_UP_MAX={FT_RSI_UP_MAX} (sobrecompra)"
        if not side_is_up and rsi_now < FT_RSI_DN_MIN:
            return False, f"RSI={rsi_now:.0f} < FT_RSI_DN_MIN={FT_RSI_DN_MIN} (sobreventa)"
    try:
        bn_chg = spot_tracker.change_since_window_start() or 0
        btc_price = spot_tracker.latest() or 0
        bn_change_usd = abs(bn_chg) * btc_price
    except Exception:
        bn_change_usd = None
    if bn_change_usd is not None and bn_change_usd < FT_BN_CHG_MIN:
        return False, f"BN_chg=${bn_change_usd:.0f} < FT_BN_CHG_MIN=${FT_BN_CHG_MIN}"
    _macd_skip = (FT_MACD_SKIP_ABOVE_PRICE > 0 and ask >= FT_MACD_SKIP_ABOVE_PRICE)
    if FT_REQUIRE_MACD_MATCH and not _macd_skip:
        try:
            macd_v, macd_s, _ = candle_analyzer.macd(fast=3, slow=15, signal=3)
            macd_h = (macd_v - macd_s) if (macd_v is not None and macd_s is not None) else None
        except Exception:
            macd_h = None
        if macd_h is not None:
            if side_is_up and macd_h <= 0:
                return False, f"MACD hist={macd_h:.1f} no es UP (esperado ▲ para BUY UP)"
            if not side_is_up and macd_h >= 0:
                return False, f"MACD hist={macd_h:.1f} no es DN (esperado ▼ para BUY DN)"
            if FT_MACD_HIST_MIN > 0:
                if side_is_up and macd_h < FT_MACD_HIST_MIN:
                    return False, f"MACD hist={macd_h:.1f} < FT_MACD_HIST_MIN={FT_MACD_HIST_MIN} (señal débil)"
                if not side_is_up and abs(macd_h) < FT_MACD_HIST_MIN:
                    return False, f"MACD hist={macd_h:.1f} demasiado débil (|hist| < {FT_MACD_HIST_MIN})"
    if FT_REQUIRE_CANDLE_COHERENT:
        cf = None
        try:
            if hasattr(candle_analyzer, '_current_candle') and candle_analyzer._current_candle:
                cf = candle_analyzer._current_candle.get("type", "")
        except Exception:
            cf = None
        if not cf:
            return False, "forming candle vacía (cambio de vela) — esperar a que se forme"
        if side_is_up and cf in ('STRONG_BEAR', 'BEAR'):
            return False, f"candle={cf} contradice BUY UP"
        if not side_is_up and cf in ('STRONG_BULL', 'BULL'):
            return False, f"candle={cf} contradice BUY DN"
        if side_is_up and cf in ('REJECTION_DN',):
            return False, f"candle={cf} (rechazo bajista) contradice BUY UP"
        if not side_is_up and cf in ('REJECTION_UP',):
            return False, f"candle={cf} (rechazo alcista) contradice BUY DN"
        if FT_REJECT_DOJI and cf == 'DOJI':
            return False, f"candle=DOJI (indecisión) — no operar sin dirección clara"
    if FT_REQUIRE_LAST_CANDLE_OK:
        try:
            last_c = candle_analyzer.last_candle(include_current=False)
            lc_type = last_c.get('type', '') if last_c else ''
        except Exception:
            lc_type = ''
        if not lc_type:
            return False, "last_candle vacía — datos insuficientes, esperar"
        if side_is_up and lc_type in ('STRONG_BEAR', 'BEAR'):
            return False, f"last_candle={lc_type} contradice BUY UP (vela previa bajista)"
        if not side_is_up and lc_type in ('STRONG_BULL', 'BULL'):
            return False, f"last_candle={lc_type} contradice BUY DN (vela previa alcista)"
    if FT_IMB_MAX < 100:
        try:
            imb_now = binance_depth.imbalance()
        except Exception:
            imb_now = None
        if imb_now is not None and imb_now > FT_IMB_MAX:
            return False, f"imb={imb_now:.2f} > FT_IMB_MAX={FT_IMB_MAX} (book sesgado peligrosamente)"
    if FT_BLOCK_VELOCITY_AGAINST:
        try:
            vel30 = spot_tracker.velocity(30.0)
        except Exception:
            vel30 = None
        if vel30 is not None:
            vel_against = (side_is_up and vel30 < -FT_VELOCITY_MIN) or \
                          (not side_is_up and vel30 > FT_VELOCITY_MIN)
            if vel_against:
                return False, (f"velocity_30s={vel30:+.2f}$/s va EN CONTRA de "
                               f"BUY {'UP' if side_is_up else 'DN'} (reversión tardía)")
    if FT_ATR_MAX_AT_HIGH_PRICE > 0 and ask >= FT_ATR_PRICE_MIN:
        try:
            atr_now = compute_atr(14)
        except Exception:
            atr_now = None
        if atr_now is not None and atr_now >= FT_ATR_MAX_AT_HIGH_PRICE:
            return False, (f"ATR={atr_now:.0f} >= {FT_ATR_MAX_AT_HIGH_PRICE} a precio "
                           f"${ask:.2f} (volatilidad extrema sin recompensa)")
    return True, "all checks passed"


def _shadow_context(side):
    """Foto de los datos en este segundo (solo lectura)."""
    out = {}
    try:
        tok = S.tokens[0] if side == "UP" else S.tokens[1]
        b = S.book.get(tok, {})
        out.update({"bid": safe_float(b.get("best_bid"), None), "ask": safe_float(b.get("best_ask"), None),
                    "ask_top3": safe_float(b.get("ask_top3"), None), "bid_top3": safe_float(b.get("bid_top3"), None)})
    except Exception:
        pass
    for k, fn in (("rsi", lambda: candle_analyzer.rsi()[0]),
                  ("vel30", lambda: spot_tracker.velocity(30.0)),
                  ("atr", lambda: compute_atr(14)),
                  ("imb", lambda: binance_depth.imbalance()),
                  ("bn_chg_usd", lambda: (spot_tracker.change_since_window_start() or 0) * (spot_tracker.latest() or 0)),
                  ("candle", lambda: (candle_analyzer._current_candle or {}).get("type")),
                  ("cl_delta", lambda: chainlink_feed.cl_direction()[1]),
                  ("cl_confirms", lambda: chainlink_feed.cl_direction()[2]),
                  ("cl_age_s", lambda: time.time() - chainlink_feed._updated_at if chainlink_feed._updated_at else None),
                  ("ptb", lambda: chainlink_feed.price_to_beat())):
        try:
            v = fn()
            out[k] = round(v, 4) if isinstance(v, float) else v
        except Exception:
            out[k] = None
    try:
        macd_v, macd_s, _ = candle_analyzer.macd(fast=3, slow=15, signal=3)
        out["macd_h"] = round(macd_v - macd_s, 3) if (macd_v is not None and macd_s is not None) else None
    except Exception:
        out["macd_h"] = None
    return out


def _shadow_write(rec):
    try:
        with open(SHADOW_LOG_FILE, "a") as f:
            f.write(json.dumps(rec, default=str) + "\n")
    except Exception:
        pass


def shadow_tick():
    """Llamada desde el loop principal. Solo lee y registra. Nunca compra."""
    if not SHADOW_ENABLE:
        return
    try:
        _shadow_ds.start()
        now = time.time()
        if now - _SHADOW_STATE["last_ts"] < SHADOW_EVERY_SEC:
            return
        _SHADOW_STATE["last_ts"] = now
        if not S.slug or len(S.tokens) != 2:
            return
        if _SHADOW_STATE["slug"] != S.slug:
            _SHADOW_STATE["slug"] = S.slug
            _SHADOW_STATE["logged"] = set()
        elapsed, left = window_timing()
        if elapsed is None or elapsed < SHADOW_FROM_SEC or elapsed > SHADOW_TO_SEC:
            return
        try:
            epoch = int(str(S.slug).split("-")[-1])
        except Exception:
            epoch = None

        # Data Streams: strike = último precio antes del epoch; delta = último − strike
        ds = {"ds_open": None, "ds_px": None, "ds_delta": None, "ds_age_s": None,
              "ds_reconnects": _shadow_ds.reconnects}
        if epoch:
            o = _shadow_ds.at(epoch); last = _shadow_ds.latest()
            if o and last:
                ds.update({"ds_open": round(o[1], 2), "ds_open_gap_s": round(epoch - o[0], 2),
                           "ds_px": round(last[1], 2), "ds_delta": round(last[1] - o[1], 2),
                           "ds_age_s": round(now - last[0], 2)})

        # Función de señal del bot SIN la espera de t+180 (solo en sombra)
        _SHADOW_CTX["active"] = True
        try:
            sig_fn, sig_reason = pick_signal_trend_follow()
        finally:
            _SHADOW_CTX["active"] = False

        quiet = False
        try:
            qh = os.getenv("QUIET_HOURS_UTC", "").strip()
            if qh:
                quiet = now_utc().hour in set(int(h) for h in qh.split(",") if h.strip())
        except Exception:
            pass

        variants = []
        if sig_fn in ("TREND_UP", "TREND_DN"):
            variants.append(("PG", sig_fn))
        if (ds["ds_delta"] is not None and ds["ds_age_s"] is not None
                and ds["ds_age_s"] <= SHADOW_DS_MAX_AGE and abs(ds["ds_delta"]) >= MIN_CL_DELTA_USD):
            variants.append(("DS", "TREND_UP" if ds["ds_delta"] > 0 else "TREND_DN"))

        for var, sig in variants:
            side = "UP" if sig == "TREND_UP" else "DN"
            ctx = _shadow_context(side)
            ask = ctx.get("ask")
            if ask is None:
                continue
            ok, why = _shadow_ft_check(sig, ask)
            decision = "SHADOW_PASS" if ok else "SHADOW_REJECT"
            key = f"{var}|{decision}|{(why or '').split('=')[0][:24] if not ok else ''}"
            first_pass = ok and f"{var}|PASS" not in _SHADOW_STATE["logged"]
            if key in _SHADOW_STATE["logged"] and not first_pass:
                continue
            _SHADOW_STATE["logged"].add(key)
            if ok:
                _SHADOW_STATE["logged"].add(f"{var}|PASS")
            rec = {"ts": round(now, 2), "slug": S.slug, "epoch": epoch, "variant": var, "side": side,
                   "decision": decision, "reason": why, "first_pass": first_pass,
                   "elapsed": round(elapsed, 1), "left": round(left, 1) if left is not None else None,
                   "sig_fn": sig_fn, "sig_fn_reason": str(sig_reason)[:200], "quiet_hour": quiet,
                   "real_entry_delay": NO_ENTRY_BEFORE_SEC, "min_cl_delta": MIN_CL_DELTA_USD}
            rec.update(ds); rec.update(ctx)
            _shadow_write(rec)
            if first_pass:
                print(f"  👻 SHADOW {var} PASS {side} @${ask:.3f} t+{elapsed:.0f}s "
                      f"| DSΔ={ds['ds_delta']} CLΔ={ctx.get('cl_delta')} | top3={ctx.get('ask_top3')} (solo registro)")
    except Exception:
        _SHADOW_CTX["active"] = False


# ══════════════════════════════════════════════════════════════════════════════
# MÉTODO DE COMPRA "TW" — SEÑAL TEMPRANA CON PTB REAL (2026-10-26, autorizado por el usuario)
# ──────────────────────────────────────────────────────────────────────────────
# Hallazgo 10-25: Polymarket resuelve con el PROMEDIO de Chainlink Data Streams del
# último minuto (PTB = promedio de los 60 s previos al inicio; cierre = promedio de
# t+240..300). 29/29 contra el oficial; el precio puntual falla 3/29.
# Regla (elegida con la 1a mitad 28/28, confirmada en la 2a 30/30; 58/58 en total):
#   entre t+TW_FROM_SEC y t+TW_TO_SEC,
#   z = |DS − PTB real| / (σ · √(260 − t + atraso DS)) ≥ TW_Z
#   DS a ≤ TW_RET_MAX USD de su máximo a favor en el ciclo,
#   DS avanzó ≥ TW_V10_MIN USD a favor en los últimos 10 s,
#   ask del lado entre TW_PRICE_MIN y TW_PRICE_MAX con ≥ TW_MIN_TOP3 acciones (3 niveles).
# INDEPENDIENTE del fast-track: NO usa ni cambia sus filtros, ni S.position_*, ni
# S.orders_sent, ni el sizing. Monto FIJO (TW_USDC).
# Precio: libro FRESCO por REST (el del WebSocket del bot puede ir atrasado). Orden LÍMITE
# FAK propia al precio real + TW_MAX_SLIP (máx TW_PRICE_MAX); hasta TW_MAX_TRIES intentos. Mantiene la posición hasta el cierre
# (Polymarket cobra solo). 1 compra por ciclo, tope diario, y se APAGA SOLO tras
# TW_STOP_AFTER_LOSSES pérdidas (queda guardado en TW_STATE_FILE; para reactivar,
# borrar ese archivo). Registro: tw_log.jsonl. Apagar del todo: TW_ENABLE=0.
# ══════════════════════════════════════════════════════════════════════════════
TW_ENABLE      = os.getenv("TW_ENABLE", "1") == "1"
TW_USDC        = float(os.getenv("TW_USDC", "5"))
# 10-26: monto = fracción del balance DISPONIBLE (TW, FLOW y CB). 0 = volver al monto fijo (TW_USDC / SIDE_USDC).
TW_PCT         = float(os.getenv("TW_PCT", "0.25"))
SIDE_PCT       = float(os.getenv("SIDE_PCT", "0.25"))
_PCT_SPENT = deque(maxlen=500)          # (ts, usdc) compras de TW/FLOW/CB aún no reflejadas en el balance


def _pct_note_spent(usdc):
    try: _PCT_SPENT.append((time.time(), float(usdc or 0)))
    except Exception: pass


def _pct_usdc(pct, fixed):
    """Monto por compra = pct × (último balance − lo que TW/FLOW/CB gastaron DESPUÉS de esa lectura).
    El balance se relee cada BALANCE_EVERY_SEC; así dos compras en el mismo ciclo no usan el mismo saldo."""
    if pct <= 0 or S.last_known_balance is None:
        return float(fixed)
    since = float(getattr(S, "last_balance_ts", 0.0) or 0.0)
    spent = sum(u for t, u in list(_PCT_SPENT) if t >= since)
    return round(max(0.0, (float(S.last_known_balance) - spent) * pct), 2)
TW_FROM_SEC    = float(os.getenv("TW_FROM_SEC", "100"))
TW_TO_SEC      = float(os.getenv("TW_TO_SEC", "195"))
TW_Z           = float(os.getenv("TW_Z", "2.8"))
TW_RET_MAX     = float(os.getenv("TW_RET_MAX", "5"))
TW_V10_MIN     = float(os.getenv("TW_V10_MIN", "5"))
TW_PRICE_MIN   = float(os.getenv("TW_PRICE_MIN", "0.89"))   # 10-28: antes 0.90
TW_PRICE_MAX   = float(os.getenv("TW_PRICE_MAX", "0.98"))
TW_MIN_TOP3    = float(os.getenv("TW_MIN_TOP3", "10"))
TW_DS_MAX_AGE  = float(os.getenv("TW_DS_MAX_AGE", "5"))
TW_MAX_PER_DAY = int(os.getenv("TW_MAX_PER_DAY", "60"))
TW_STOP_AFTER_LOSSES = int(os.getenv("TW_STOP_AFTER_LOSSES", "1"))
TW_STATE_FILE  = os.getenv("TW_STATE_FILE", "tw_state.json")
TW_LOG_FILE    = os.getenv("TW_LOG_FILE", "tw_log.jsonl")
TW_MAX_SLIP    = float(os.getenv("TW_MAX_SLIP", "0.01"))   # margen sobre el ask REAL (libro fresco) para la orden límite
TW_MAX_TRIES   = int(os.getenv("TW_MAX_TRIES", "5"))       # intentos por ciclo si la orden no llena
# 10-28: TOPE DE VOLATILIDAD para TODOS los métodos (TW, FLOW, CB, LATE, QUIET). σ = volatilidad de Data Streams en los
# 15 min antes del ciclo (lo normal es 1.5-2.5). Compras reales: σ<3 → 124/127 (+$102.72); σ≥3 → 32/38 (−$172.48,
# incluidas las 5 del FOMC). Capturador: σ<3 → 564/564. Sin σ conocida (primeros ~15 min tras reiniciar) no compra.
VOL_MAX        = float(os.getenv("VOL_MAX", "4.0"))
# 10-28: volatilidad RÁPIDA = la misma σ pero con los ÚLTIMOS 60 s de Data Streams (cómo está saltando el precio
# AHORA). En el FOMC de 11:30 la σ de 15 min era 3.36 pero la de 60 s ya era 5.0 al comprar. Capturador: con
# σ60 < 4.5 → 623 compras / 0 perdidos (sin esto 678 / 1). Lo normal en una compra: σ60 ≈ 2.
VOL60_MAX      = float(os.getenv("VOL60_MAX", "4.5"))


def sigma_ultimos(ser, secs=60):
    """σ de Data Streams en los últimos `secs` segundos (saltos /√dt), igual que la σ de 15 min. None si hay pocos datos."""
    try:
        last_t = ser[-1][0]
        pts = [(t, v) for t, v in ser if t >= last_t - secs]
        if len(pts) < 10:
            return None
        d = [(v2 - v1) / max(t2 - t1, 1.0) ** 0.5 for (t1, v1), (t2, v2) in zip(pts, pts[1:])]
        m = sum(d) / len(d)
        return (sum((x - m) ** 2 for x in d) / len(d)) ** 0.5
    except Exception:
        return None
# 10-28: PAUSA POR CALENDARIO. Las 5 pérdidas del FOMC (11:30-11:40) llegaron con σ previa tranquila: el tope de σ
# no avisa ANTES de un dato. Ningún método compra desde `antes` min hasta `despues` min alrededor de cada evento.
# Horas en UTC (EE. UU. sale del horario de verano el 1-nov: antes 8:30 ET = 12:30 UTC, después = 13:30 UTC).
# Fuentes: federalreserve.gov (FOMC), calendario BLS/BEA vía fedratecalc.com (revisar si cambian).
PAUSA_ENABLE   = os.getenv("PAUSA_ENABLE", "1") == "1"
_EVENTOS_BASE = [
    # (UTC ISO,            nombre,                         min antes, min después)
    ("2026-10-28T20:05Z", "Resultados Microsoft/Alphabet", 5, 40),
    ("2026-10-29T12:30Z", "PIB 3T + inflación PCE",        15, 60),
    ("2026-10-29T20:05Z", "Resultados Coinbase/Amazon",    5, 40),
    ("2026-10-30T12:30Z", "Costo del empleo (ECI)",        10, 30),
    ("2026-11-06T13:30Z", "Empleo (nómina no agrícola)",   15, 60),
    ("2026-11-10T13:30Z", "Inflación CPI",                 15, 60),
    ("2026-11-13T13:30Z", "Precios al productor PPI",      10, 30),
    ("2026-11-17T13:30Z", "Ventas minoristas",             10, 30),
    ("2026-11-18T19:00Z", "Minutas de la Fed",             10, 40),
    ("2026-11-25T13:30Z", "PIB 2a estimación + PCE",       15, 60),
    ("2026-12-04T13:30Z", "Empleo (nómina no agrícola)",   15, 60),
    ("2026-12-09T19:00Z", "Decisión Fed + conferencia",    15, 90),
    ("2026-12-10T13:30Z", "Inflación CPI",                 15, 60),
    ("2026-12-23T13:30Z", "PIB 3a estimación + PCE",       15, 60),
]
# Agregar más sin tocar el código:  PAUSA_EXTRA="2026-11-20T15:00Z|Discurso Powell|15|60;..."
for _x in (os.getenv("PAUSA_EXTRA", "") or "").split(";"):
    try:
        _p = _x.split("|")
        if len(_p) == 4: _EVENTOS_BASE.append((_p[0].strip(), _p[1].strip(), float(_p[2]), float(_p[3])))
    except Exception:
        pass
_EVENTOS = []
for _iso, _n, _a, _d in _EVENTOS_BASE:
    try:
        _t = datetime.strptime(_iso, "%Y-%m-%dT%H:%MZ").replace(tzinfo=timezone.utc).timestamp()
        _EVENTOS.append((_t - _a * 60, _t + _d * 60, _n, _t))
    except Exception:
        pass
_PAUSA_AVISADA = set()


def pausa_evento(now=None):
    """Nombre del evento si estamos dentro de su ventana de pausa; None si no. Avisa una vez por Telegram."""
    if not PAUSA_ENABLE:
        return None
    now = now or time.time()
    for t0, t1, nombre, t_ev in _EVENTOS:
        if t0 <= now <= t1:
            if t_ev not in _PAUSA_AVISADA:
                _PAUSA_AVISADA.add(t_ev)
                try:
                    fin = datetime.fromtimestamp(t1 - 7 * 3600, timezone.utc).strftime("%H:%M")
                    msg = f"⏸ Pausa por evento: {nombre}. Ningún método compra hasta las {fin} (hora Mazatlán)."
                    print(msg); _tw_tg(msg)
                except Exception:
                    pass
            return nombre
    return None
BOOK_LAG_FILE  = os.getenv("BOOK_LAG_FILE", "book_lag.jsonl")

_TW = {"slug": None, "ptb": None, "sig": None, "done": False, "last_res_check": 0.0, "state": None}


def _tw_log(rec):
    try:
        with open(TW_LOG_FILE, "a") as f:
            f.write(json.dumps(rec, default=str) + "\n")
    except Exception:
        pass


def _tw_tg(text):
    """Telegram propio del método TW: el tg_send del bot filtra (TG_ALLOW_TRIGGERS) y
    silenciaba estos avisos. Mismo token/chat. Apagar con TW_TELEGRAM=0."""
    if os.getenv("TW_TELEGRAM", "1") != "1":
        return
    try:
        if not (TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID):
            return
        base = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"
        params = {"chat_id": TELEGRAM_CHAT_ID, "text": text, "disable_web_page_preview": "true"}
        requests.get(base + "?" + urllib.parse.urlencode(params), timeout=8)
    except Exception:
        pass


def _tw_state():
    if _TW["state"] is None:
        st = {"disabled": False, "losses": 0, "wins": 0, "day": None, "count_day": 0, "pending": [],
              "paper_pending": [], "paper_wins": 0, "paper_losses": 0}
        try:
            with open(TW_STATE_FILE) as f:
                st.update(json.load(f))
            st.setdefault("paper_pending", []); st.setdefault("paper_wins", 0); st.setdefault("paper_losses", 0)
        except Exception:
            pass
        _TW["state"] = st
    return _TW["state"]


def _tw_save():
    try:
        with open(TW_STATE_FILE, "w") as f:
            json.dump(_TW["state"], f)
    except Exception:
        pass


def _tw_ds_series():
    try:
        with _shadow_ds._lock:
            return list(_shadow_ds._px)
    except Exception:
        return []


_TW_LOCK = threading.Lock()


def _tw_resolve_kick():
    """Lanza la revisión de resultados en un hilo aparte (las consultas HTTP no deben
    frenar el loop del bot, que también procesa el libro de Polymarket)."""
    st = _tw_state()
    if not (st["pending"] or st.get("paper_pending")) or time.time() - _TW["last_res_check"] < 30:
        return
    if _TW.get("res_thread") and _TW["res_thread"].is_alive():
        return
    _TW["last_res_check"] = time.time()
    th = threading.Thread(target=_tw_resolve_pending, name="TWresolve", daemon=True)
    _TW["res_thread"] = th; th.start()


def _tw_winner(slug):
    try:
        m = gamma_get_market_by_slug(slug) or {}
        prices, outs = m.get("outcomePrices"), m.get("outcomes")
        if isinstance(prices, str): prices = json.loads(prices)
        if isinstance(outs, str): outs = json.loads(outs)
        for o, px in zip(outs or [], prices or []):
            if float(px) >= 0.99:
                ol = str(o).lower()
                return "UP" if ("up" in ol or "yes" in ol) else "DN"
    except Exception:
        pass
    return None


def _tw_resolve_paper(st):
    """Resultado de las señales EN PAPEL (TW apagado): solo registro, no afecta nada."""
    with _TW_LOCK:
        todo = list(st.get("paper_pending", []))
    done = set()
    for p in todo:
        if time.time() < p["epoch"] + WINDOW_SECONDS + 60:
            continue
        w = _tw_winner(p["slug"])
        if w is None:
            if time.time() > p["epoch"] + WINDOW_SECONDS + 3600:
                done.add(p["slug"])
            continue
        done.add(p["slug"])
        won = (w == p["side"])
        if won: st["paper_wins"] += 1
        else:   st["paper_losses"] += 1
        _tw_log({"ts": time.time(), "kind": "TW_PAPER_RESULT", "slug": p["slug"], "side": p["side"], "winner": w,
                 "won": won, "entry_real_ask": p["price"], "paper_wins": st["paper_wins"],
                 "paper_losses": st["paper_losses"]})
    if done:
        with _TW_LOCK:
            st["paper_pending"] = [p for p in st.get("paper_pending", []) if p["slug"] not in done]
            _tw_save()


def _tw_resolve_pending():
    """Revisa en Polymarket el resultado de las compras TW ya cerradas (corre en hilo)."""
    st = _tw_state()
    try:
        _tw_resolve_paper(st)
    except Exception:
        pass
    with _TW_LOCK:
        todo = list(st["pending"])
    keep = []; done = set()
    for p in todo:
        if time.time() < p["epoch"] + WINDOW_SECONDS + 60:
            keep.append(p); continue
        winner = None
        try:
            m = gamma_get_market_by_slug(p["slug"]) or {}
            prices, outs = m.get("outcomePrices"), m.get("outcomes")
            if isinstance(prices, str): prices = json.loads(prices)
            if isinstance(outs, str): outs = json.loads(outs)
            for o, px in zip(outs or [], prices or []):
                if float(px) >= 0.99:
                    ol = str(o).lower()
                    winner = "UP" if ("up" in ol or "yes" in ol) else "DN"
        except Exception:
            winner = None
        if winner is None:
            if time.time() > p["epoch"] + WINDOW_SECONDS + 3600:
                _tw_log({"ts": time.time(), "kind": "TW_RESULT", "slug": p["slug"], "result": "UNKNOWN"})
                done.add(p["slug"]); continue
            keep.append(p); continue
        done.add(p["slug"])
        won = (winner == p["side"])
        pnl = (p["shares"] * 1.0 - p["usdc"]) if won else -p["usdc"]
        if won: st["wins"] += 1
        else:   st["losses"] += 1
        _tw_log({"ts": time.time(), "kind": "TW_RESULT", "slug": p["slug"], "side": p["side"], "winner": winner,
                 "won": won, "entry": p["price"], "usdc": p["usdc"], "pnl_est": round(pnl, 2),
                 "wins": st["wins"], "losses": st["losses"]})
        msg = (f"{'🎯' if won else '💀'} TW {'WON' if won else 'LOST'} {p['side']} @{p['price']:.3f} | "
               f"{'+' if pnl >= 0 else '-'}${abs(pnl):.2f} | TW total {st['wins']}W/{st['losses']}L | {p['slug']}")
        print(msg); _tw_tg(msg)
        if not won and st["losses"] >= TW_STOP_AFTER_LOSSES:
            st["disabled"] = True
            stop = (f"⛔ TW APAGADO tras {st['losses']} pérdida(s). El fast-track sigue normal. "
                    f"Para reactivar: borrar {TW_STATE_FILE}")
            print(stop); _tw_tg(stop)
    with _TW_LOCK:
        # conservar también lo que se agregó mientras este hilo corría
        st["pending"] = [p for p in st["pending"] if p["slug"] not in done and
                         (p in keep or p not in todo)]
        _tw_save()


def _tw_buy(client, token_id, ask, usdc=None):
    """Orden LÍMITE FAK propia del método TW al precio REAL del libro fresco (+TW_MAX_SLIP, sin pasar
    de TW_PRICE_MAX). 10-26: la orden de mercado dio "invalid amounts" y el libro del WS iba atrasado.
    FAK = llena lo que haya a ese precio o menos y cancela el resto (sin órdenes colgadas)."""
    cap = round(min(ask + TW_MAX_SLIP, TW_PRICE_MAX), 2)
    # acciones ENTERAS (precio 2 decimales × entero = monto de 2 decimales; evita el error
    # "invalid amounts ... max accuracy of 2 decimals" que dio la orden de mercado el 10-26)
    size = float(max(5, int((usdc or TW_USDC) // cap)))   # Polymarket: mínimo 5 acciones en límite
    if DRY_RUN:
        return True, {"status": "DRY_RUN", "actual_shares": size, "actual_usdc": round(size * cap, 4)}, cap
    try:
        from py_clob_client_v2.clob_types import OrderArgs, OrderType as _OT
        from py_clob_client_v2.order_builder.constants import BUY as _BUYc
        if not hasattr(_OT, "FAK"):
            return False, "cliente sin FAK", cap
        signed = client.create_order(OrderArgs(price=cap, size=size, side=_BUYc, token_id=token_id))
        resp = client.post_order(signed, _OT.FAK)
        print(f"📋 TW order (LÍMITE FAK BUY @${cap:.2f} x{size}): {resp}")
        resp = _enrich_order_response(resp, "BUY")
        if isinstance(resp, dict) and (resp.get("status") or "").upper() == "MATCHED" \
                and safe_float(resp.get("actual_shares"), 0) > 0:
            return True, resp, cap
        return False, resp, cap
    except Exception as e:
        return False, f"excepción: {e}", cap


def tw_tick(client):
    """Llamada desde el loop principal (cada DIAG). Errores se ignoran: nunca detiene al bot."""
    if not TW_ENABLE:
        return
    try:
        _shadow_ds.start(); _post_loss_guard.start()
        _tw_resolve_kick()
        st = _tw_state()
        # 2026-10-26: apagado (tras pérdida) o trading deshabilitado → MODO PAPEL: sigue evaluando
        # y registra qué habría comprado (con el precio real del libro), SIN mandar órdenes.
        paper = bool(st["disabled"] or not S.trading_enabled or S.paused_by_telegram)
        if not S.slug or len(S.tokens) != 2:
            return
        try:
            epoch = int(str(S.slug).split("-")[-1])
        except Exception:
            return
        now = time.time()
        if _TW["slug"] != S.slug:
            _TW.update({"slug": S.slug, "ptb": None, "sig": None, "done": False, "logged_skip": False, "tries": 0,
                        "logged_vol": False, "logged_ev": False, "logged_vol60": False})
            with _TW_LOCK:
                _already = any(p["slug"] == S.slug for p in st["pending"]) or \
                           any(p["slug"] == S.slug for p in st.get("paper_pending", []))
            if _already:
                _TW["done"] = True                      # ya se compró este ciclo (reinicio)
        if _TW["done"]:
            return
        today = now_utc().strftime("%Y-%m-%d")
        if st.get("day") != today:
            st["day"] = today; st["count_day"] = 0; _tw_save()
        if st["count_day"] >= TW_MAX_PER_DAY and not paper:
            return
        el = now - epoch
        if el < TW_FROM_SEC or el > TW_TO_SEC:
            return
        ser = _tw_ds_series()
        if len(ser) < 120:
            return
        # PTB real y volatilidad (una vez por ciclo)
        if _TW["ptb"] is None:
            pts = [v for t, v in ser if epoch - 60 <= t < epoch]
            hist = [(t, v) for t, v in ser if epoch - 900 <= t < epoch]
            if len(pts) < 30 or len(hist) < 120:
                return
            _TW["ptb"] = sum(pts) / len(pts)
            d_ = [(v2 - v1) / max(t2 - t1, 1.0) ** 0.5 for (t1, v1), (t2, v2) in zip(hist, hist[1:])]
            m_ = sum(d_) / len(d_)
            _TW["sig"] = (sum((x - m_) ** 2 for x in d_) / len(d_)) ** 0.5
        ptb, sig = _TW["ptb"], _TW["sig"]
        last_t, cur = ser[-1]
        age = now - last_t
        if not sig or age > TW_DS_MAX_AGE:
            return
        _ev = pausa_evento(now)
        if _ev:
            if not _TW.get("logged_ev"):
                _TW["logged_ev"] = True
                _tw_log({"ts": round(now, 2), "kind": "TW_SKIP_EVENTO", "slug": S.slug, "elapsed": round(el, 1), "evento": _ev})
            return
        if sig >= VOL_MAX:                       # 10-28: mercado demasiado agitado (p. ej. FOMC)
            if not _TW.get("logged_vol"):
                _TW["logged_vol"] = True
                _tw_log({"ts": round(now, 2), "kind": "TW_SKIP_VOL", "slug": S.slug, "elapsed": round(el, 1),
                         "sigma": round(sig, 4), "vol_max": VOL_MAX})
            return
        s60 = sigma_ultimos(ser, 60)
        if s60 is None or s60 >= VOL60_MAX:      # 10-28: volatilidad de los últimos 60 s
            if not _TW.get("logged_vol60"):
                _TW["logged_vol60"] = True
                _tw_log({"ts": round(now, 2), "kind": "TW_SKIP_VOL60", "slug": S.slug, "elapsed": round(el, 1),
                         "sigma60": round(s60, 3) if s60 is not None else None, "vol60_max": VOL60_MAX})
            return
        sg = 1 if cur > ptb else -1
        z = abs(cur - ptb) / (sig * max(260.0 - el + age, 1.0) ** 0.5)
        if z < TW_Z:
            return
        cyc = [v for t, v in ser if t >= epoch]
        if not cyc:
            return
        ret = max((v - ptb) * sg for v in cyc) - (cur - ptb) * sg
        if ret > TW_RET_MAX:
            return
        v0 = None
        for t, v in ser:
            if t <= last_t - 10: v0 = v
            else: break
        if v0 is None or (cur - v0) * sg < TW_V10_MIN:
            return
        side = "UP" if sg > 0 else "DN"
        _blocked, _guard_rec = _post_loss_guard.evaluate("TW", side, _post_loss_spot_series(), S.slug, now, ds_series=ser)
        if _blocked:
            _tw_log({**_guard_rec, "kind": "TW_POST_LOSS_BLOCK"})
            return
        token_id = S.tokens[0] if side == "UP" else S.tokens[1]
        b = S.book.get(token_id, {})
        ws_ask = safe_float(b.get("best_ask"), None)
        # 10-26: el libro del WebSocket del bot iba 12-26 s ATRASADO (veía 0.93 cuando el
        # real era 0.98). TW decide con el libro FRESCO pedido directo a Polymarket (REST).
        if (now - _TW.get("last_rest_ts", 0.0)) < 2.0:
            return                                    # no martillar la API (máx 1 consulta / 2 s)
        _TW["last_rest_ts"] = now
        try:
            lb = client.get_order_book(token_id)
            asks_raw = lb.get("asks") if isinstance(lb, dict) else getattr(lb, "asks", None)
            lv = sorted(((_lvl_price(a), _lvl_size(a)) for a in (asks_raw or [])
                         if _lvl_price(a) is not None), key=lambda x: x[0])
        except Exception:
            lv = []
        if not lv:
            return
        ask = float(lv[0][0]); top3 = float(sum(q or 0 for _, q in lv[:3]))
        if not (TW_PRICE_MIN <= ask <= TW_PRICE_MAX) or top3 < TW_MIN_TOP3:
            if not _TW.get("logged_skip"):
                _TW["logged_skip"] = True
                _tw_log({"ts": round(now, 2), "kind": "TW_SKIP_PRICE", "slug": S.slug, "side": side,
                         "elapsed": round(el, 1), "rest_ask": ask, "ws_ask": ws_ask, "rest_top3": round(top3, 1),
                         "z": round(z, 3)})
            return
        bal = S.last_known_balance if S.last_known_balance is not None else BALANCE_FALLBACK_USDC
        tw_usd = _pct_usdc(TW_PCT, TW_USDC)
        if not paper and bal is not None and bal < max(MIN_BALANCE_TO_TRADE, tw_usd):
            return
        if paper:
            _TW["done"] = True
            rec = {"ts": round(now, 2), "kind": "TW_PAPER", "slug": S.slug, "epoch": epoch, "side": side,
                   "elapsed": round(el, 1), "real_ask": ask, "real_top3": round(top3, 1), "ws_ask": ws_ask,
                   "z": round(z, 3), "ptb_real": round(ptb, 2), "ds_px": round(cur, 2), "ds_delta": round(cur - ptb, 2),
                   "ds_age_s": round(age, 2), "ret": round(ret, 2), "v10": round((cur - v0) * sg, 2),
                   "sigma": round(sig, 4), "motivo": ("apagado tras pérdida" if st["disabled"] else "trading deshabilitado")}
            try: rec["ptb_bot"] = chainlink_feed.price_to_beat()
            except Exception: pass
            _tw_log(rec)
            with _TW_LOCK:
                st.setdefault("paper_pending", []).append({"slug": S.slug, "epoch": epoch, "side": side, "price": float(ask)})
                _tw_save()
            print(f"  📝 TW EN PAPEL (no compra): {side} @${ask:.3f} t+{el:.0f}s | z={z:.2f} | {rec['motivo']}")
            return
        # ── comprar al precio REAL (aunque se haya movido desde que DS dio la señal) ──
        _TW["tries"] = _TW.get("tries", 0) + 1
        if _TW["tries"] >= TW_MAX_TRIES:
            _TW["done"] = True
        info = {"ts": round(now, 2), "kind": "TW_SIGNAL", "slug": S.slug, "epoch": epoch, "side": side,
                "elapsed": round(el, 1), "ask": ask, "ask_top3": top3, "ws_ask": ws_ask,
                "ws_ask_minus_real": round(ws_ask - ask, 3) if ws_ask is not None else None,
                "book_lag_p50_s": _BOOKLAG.get("last_p50"), "try": _TW.get("tries"), "z": round(z, 3), "ptb_real": round(ptb, 2),
                "ptb_bot": None, "ds_px": round(cur, 2), "ds_delta": round(cur - ptb, 2), "ds_age_s": round(age, 2),
                "ret": round(ret, 2), "v10": round((cur - v0) * sg, 2), "sigma": round(sig, 4), "sigma60": round(s60, 3), "usdc": tw_usd, "pct": TW_PCT,
                "cl_delta_bot": None, "fast_track_holding": S.position_token is not None}
        try: info["ptb_bot"] = chainlink_feed.price_to_beat()
        except Exception: pass
        try: info["cl_delta_bot"] = chainlink_feed.cl_delta_usd()
        except Exception: pass
        print(f"  🎯 TW BUY {side} @${ask:.3f} t+{el:.0f}s | z={z:.2f} PTB real={ptb:,.2f} DSΔ={cur - ptb:+.1f} "
              f"| ${tw_usd:.2f}")
        ok, resp, cap = _tw_buy(client, token_id, ask, tw_usd)
        info["ok"] = bool(ok); info["price_cap"] = cap
        if ok:
            _TW["done"] = True
            shares = safe_float(resp.get("actual_shares"), 0) or 0.0
            paid = safe_float(resp.get("actual_usdc"), 0) or 0.0
            fill_px = (paid / shares) if shares > 0 and paid > 0 else cap
            info.update({"fill_price": round(fill_px, 4), "shares": round(shares, 4), "paid_usdc": round(paid, 4),
                         "slip": round(fill_px - ask, 4)})
            st["count_day"] += 1
            st["pending"].append({"slug": S.slug, "epoch": epoch, "side": side, "price": float(fill_px),
                                  "usdc": float(paid or tw_usd), "shares": float(shares), "ts": now})
            _tw_save()
            _pct_note_spent(paid or tw_usd)
            _side_register(S.slug, side, shares, "TW")
            _tw_tg(f"🎯 TW BUY {side} @{fill_px:.3f} (señal {ask:.3f}) | ${paid or tw_usd:.2f} | t+{el:.0f}s | z={z:.2f} | "
                    f"PTB real {ptb:,.2f} DSΔ={cur - ptb:+.1f} | {S.slug}")
        else:
            info["resp"] = str(resp)[:300]
            print(f"  ❌ TW BUY no ejecutada (intento {_TW['tries']}/{TW_MAX_TRIES}, tope ${cap:.2f}): {str(resp)[:120]}")
        _tw_log(info)
    except Exception as e:
        try: print(f"  ⚠️ TW error (ignorado): {str(e)[:100]}")
        except Exception: pass


# ── ATRASO DEL LIBRO DE POLYMARKET (2026-10-26) ─────────────────────────────────
# Cada mensaje del WebSocket trae la hora del servidor ("timestamp", ms). Atraso =
# hora al procesarlo − esa hora. Resumen cada 60 s en BOOK_LAG_FILE y en consola.
# Antes del arreglo (señales dentro de on_message + consulta a Telegram) iba 12-26 s.
_BOOKLAG = {"vals": [], "t0": time.time(), "last_p50": None}


def _note_book_lag(obj):
    try:
        it = obj[0] if isinstance(obj, list) and obj else obj
        ts = it.get("timestamp") if isinstance(it, dict) else None
        if ts is None:
            return
        ts = float(ts)
        if ts > 1e12: ts /= 1000.0
        now = time.time()
        _BOOKLAG["vals"].append(now - ts)
        if now - _BOOKLAG["t0"] >= 60 and _BOOKLAG["vals"]:
            v = sorted(_BOOKLAG["vals"]); n = len(v)
            rec = {"ts": round(now, 1), "slug": S.slug, "n": n, "p50": round(v[n // 2], 3),
                   "p90": round(v[int(n * 0.9)], 3), "max": round(v[-1], 3), "min": round(v[0], 3)}
            _BOOKLAG.update({"vals": [], "t0": now, "last_p50": rec["p50"]})
            print(f"📶 Libro PM atraso: p50 {rec['p50']:.2f}s | p90 {rec['p90']:.2f}s | máx {rec['max']:.2f}s (n={n})")
            with open(BOOK_LAG_FILE, "a") as f:
                f.write(json.dumps(rec) + "\n")
    except Exception:
        pass


# ══════════════════════════════════════════════════════════════════════════════
# MÉTODOS DE COMPRA "FLOW" y "CB" (2026-10-26, autorizados por el usuario) — $2 cada uno
# ──────────────────────────────────────────────────────────────────────────────
# Encontrados en la búsqueda masiva (331 ciclos del capturador, elección con el 60% viejo,
# prueba con el 40% nuevo; ver BITACORA 10-26 (i)):
#   FLOW: compra neta en Polymarket del lado ≥ $2,062 en el ciclo + CVD Binance 60 s ≥ 2.529 BTC
#         a favor + subida de Data Streams en 60 s < 59.22 USD → 135/136 (neto +4.56 ¢/acción)
#   CB:   CVD de Coinbase en 30 s EN CONTRA del lado (< −0.6146 BTC) → 63/63 (neto +5.82 ¢/acción)
# Común a los dos (igual que en el análisis): t+100..195, lado = Data Streams vs PTB REAL
# (promedio 60 s), ask del lado entre 0.90 y 0.98 con ≥10 acciones (libro FRESCO por REST),
# 1ª vez que se cumple en el ciclo.
# INDEPENDIENTES entre sí y de TW / fast-track: estado, registro, Telegram y posiciones propias;
# no usan S.position_*, S.orders_sent, ni filtros/sizing del bot. Monto fijo SIDE_USDC ($5).
# Orden: de MERCADO por monto exacto = acciones enteras × precio (evita "invalid amounts";
# las órdenes límite exigen mínimo 5 acciones, imposible con $2), FAK, precio tope = ask fresco.
# Se apagan solos tras SIDE_STOP_AFTER_LOSSES pérdidas → modo PAPEL (siguen registrando).
# Reactivar: borrar flow_state.json / cb_state.json. Apagar del todo: FLOW_ENABLE=0 / CB_ENABLE=0.
# ══════════════════════════════════════════════════════════════════════════════
SIDE_USDC              = float(os.getenv("SIDE_USDC", "5"))
SIDE_FROM_SEC          = float(os.getenv("SIDE_FROM_SEC", "100"))
SIDE_TO_SEC            = float(os.getenv("SIDE_TO_SEC", "195"))
SIDE_PRICE_MIN         = float(os.getenv("SIDE_PRICE_MIN", "0.89"))   # 10-28: antes 0.90
SIDE_PRICE_MAX         = float(os.getenv("SIDE_PRICE_MAX", "0.98"))
SIDE_MIN_TOP3          = float(os.getenv("SIDE_MIN_TOP3", "10"))
SIDE_DS_MAX_AGE        = float(os.getenv("SIDE_DS_MAX_AGE", "5"))
SIDE_MIN_CUSH          = float(os.getenv("SIDE_MIN_CUSH", "17"))   # 10-26: USD mínimos entre DS y el PTB real (10-28: antes 20)
SIDE_MAX_PER_DAY       = int(os.getenv("SIDE_MAX_PER_DAY", "80"))
SIDE_MAX_TRIES         = int(os.getenv("SIDE_MAX_TRIES", "5"))
SIDE_STOP_AFTER_LOSSES = int(os.getenv("SIDE_STOP_AFTER_LOSSES", "1"))
FLOW_ENABLE  = os.getenv("FLOW_ENABLE", "1") == "1"
FLOW_PM_MIN  = float(os.getenv("FLOW_PM_MIN", "2062"))     # USD netos comprados del lado en PM (10-28: de vuelta a 2062; σ y z protegen)
FLOW_CVD_MIN = float(os.getenv("FLOW_CVD_MIN", "2.529"))   # BTC netos a favor en Binance (60 s) (10-28: de vuelta a 2.529)
FLOW_V60_MAX = float(os.getenv("FLOW_V60_MAX", "53.3"))    # USD que subió DS en 60 s (máximo) (10-26: −10%, antes 59.22)
CB_ENABLE    = os.getenv("CB_ENABLE", "1") == "1"
CB_CVD_MAX   = float(os.getenv("CB_CVD_MAX", "-0.5"))      # BTC netos en Coinbase 30 s (con signo del lado) (10-28: antes −0.6146)
CB_Z_MIN     = float(os.getenv("CB_Z_MIN", "1.50"))        # 10-29: z mínimo cuando está disponible (pérdida 19:15 UTC z=1.32; evita entradas con colchón débil)
# 10-26: método LATE = ya tarde en el ciclo, con colchón (SIDE_MIN_CUSH) y DS TODAVÍA avanzando a favor.
# Capturador 616 ciclos: 122/122 (19/19 en ciclos nuevos), +5.2¢ por acción; 61 ciclos que ningún otro método toma.
LATE_ENABLE   = os.getenv("LATE_ENABLE", "1") == "1"
LATE_FROM_SEC = float(os.getenv("LATE_FROM_SEC", "160"))   # desde t+160 (hasta SIDE_TO_SEC)
LATE_VEL5_MIN = float(os.getenv("LATE_VEL5_MIN", "1"))     # USD que avanzó DS a favor en los últimos 5 s (10-28: antes 2)
LATE_V10_MIN  = float(os.getenv("LATE_V10_MIN", "0"))      # 10-28: DS no más abajo que hace 10 s (protege al bajar vel5)
# 10-28: pérdida del ciclo 08:35 con Coinbase "persiguiendo" (+2.0 a +2.5 BTC netos a favor en 30 s). En general, con
# Coinbase ≥2 BTC a favor el favorito gana 88% (antes) / 77% (después) contra 92-94% del resto. Espejo de CB.
LATE_CB30_MAX = float(os.getenv("LATE_CB30_MAX", "99"))     # BTC netos en Coinbase 30 s a favor del lado (máximo). 99 = apagado; 1.75 = activo
LATE_V60_MIN  = float(os.getenv("LATE_V60_MIN", "0"))      # DS no debe estar más abajo que hace 60 s
LATE_PCT      = float(os.getenv("LATE_PCT", "0.10"))       # fracción del balance por compra (método nuevo: empieza en 10%)
# 10-27: las pérdidas de CB/LATE (y una de FLOW) llegaron con el colchón ya regresando: DS había devuelto
# ≥30% de su mejor distancia al PTB en el ciclo. TW ya lo exige (ret ≤ 5) y va 142/142.
SIDE_MAX_RET_REL = float(os.getenv("SIDE_MAX_RET_REL", "0.33"))  # FLOW, CB y LATE: retroceso máx. / colchón actual (10-28: antes 0.30)
# 10-28: "memoria" del retroceso. Las dos pérdidas del 10-28 (LATE 08:35, CB 09:10) compraron DESPUÉS de que el mismo
# método registró SKIP_RET en ese ciclo. Tras un SKIP_RET solo se compra si el colchón volvió casi a su máximo
# (retroceso < 10%) o si BTC ya está muy lejos (z ≥ 2.5). Capturador: 755 compras / 0 perdidas (sin esto: 771 / 2).
SIDE_RET_AFTER_SKIP = float(os.getenv("SIDE_RET_AFTER_SKIP", "0.10"))
SIDE_Z_AFTER_SKIP   = float(os.getenv("SIDE_Z_AFTER_SKIP", "2.5"))
# 10-28 14:00: CB perdió tras SKIP_RET → SKIP_RET_MEM → en 2 s un PICO de 21 USD en 5 s (2.95σ) marcó un "nuevo máximo"
# y el retroceso volvió a 0 → compró a 0.88 y se dio la vuelta. Un nuevo máximo hecho por un pico no cuenta como
# recuperación. Capturador: cuesta 1 compra de 623.
SIDE_SPIKE_K        = float(os.getenv("SIDE_SPIKE_K", "2.0"))   # pico = DS avanzó ≥ K·σ·√5 en los últimos 5 s
# 10-27: FLOW pierde en mercado tranquilo (σ < 1.9): 10-26 02:10 (1.88), 10-27 11:45 (1.47), 23:20 (1.33).
FLOW_SIG_MIN  = float(os.getenv("FLOW_SIG_MIN", "1.9"))    # σ de DS (900 s antes del ciclo), igual que TW
# 10-28: pérdida de FLOW en el ciclo 05:50 (σ 3.53, colchón 44 USD con 100 s por delante → z 1.23; el precio 0.90 era justo).
FLOW_Z_MIN    = float(os.getenv("FLOW_Z_MIN", "1.5"))      # z = colchón / (σ·√(260−t)), igual que TW
# 10-28: método QUIET = tarde en el ciclo, DS todavía avanzando a favor y la gente de Polymarket AÚN NO persigue
# (poco dinero neto en el último minuto) → precio más barato (~0.92). Capturador: 80/80, +7.5¢ por acción.
# Evidencia más débil que la de los otros métodos → arranca SOLO EN PAPEL (registra, no compra).
QUIET_ENABLE   = os.getenv("QUIET_ENABLE", "1") == "1"
QUIET_LIVE     = os.getenv("QUIET_LIVE", "0") == "1"       # 0 = solo papel; 1 = compra de verdad
QUIET_FROM_SEC = float(os.getenv("QUIET_FROM_SEC", "160"))
QUIET_PM60_MAX = float(os.getenv("QUIET_PM60_MAX", "1112"))  # USD netos del lado en PM en los últimos 60 s (máximo)
QUIET_VEL5_MIN = float(os.getenv("QUIET_VEL5_MIN", "0.5"))   # USD que avanzó DS a favor en los últimos 5 s (mínimo)
QUIET_PCT      = float(os.getenv("QUIET_PCT", "0.10"))

# Posiciones abiertas de los métodos laterales (TW, FLOW, CB): las usa la verificación de
# resultado del fast-track para NO confundir sus cobros con el del fast-track.
_SIDE_POS = []          # dicts: slug, side, shares, method, ts
_SIDE_POS_LOCK = threading.Lock()


def _side_register(slug, side, shares, method):
    try:
        with _SIDE_POS_LOCK:
            _SIDE_POS.append({"slug": slug, "side": side, "shares": float(shares or 0), "method": method,
                              "ts": time.time()})
            cutoff = time.time() - 3600
            _SIDE_POS[:] = [p for p in _SIDE_POS if p["ts"] >= cutoff]
    except Exception:
        pass


def _side_opp_shares(slug, side):
    """Acciones de métodos laterales en el MISMO ciclo y del lado CONTRARIO (si ganan, su cobro
    sube el saldo aunque el fast-track haya perdido)."""
    try:
        with _SIDE_POS_LOCK:
            return sum(p["shares"] for p in _SIDE_POS if p["slug"] == slug and p["side"] != side)
    except Exception:
        return 0.0


# ── Flujos: Binance spot (aggTrades), Coinbase (trades) y Polymarket (last_trade_price) ──────
class _FlowFeeds:
    """Hilo propio: cada 2 s lee las operaciones nuevas de Binance spot y Coinbase (REST, igual
    que el capturador). Guarda (hora, cantidad con signo del comprador agresor)."""
    def __init__(self):
        self.lock = threading.Lock()
        self.bn = deque(maxlen=200000); self.cb = deque(maxlen=20000)
        self.bn_last_id = None; self.cb_last_id = None; self.th = None; self.errors = 0

    def start(self):
        if self.th and self.th.is_alive():
            return
        self.th = threading.Thread(target=self._run, name="FlowFeeds", daemon=True); self.th.start()

    def _poll_bn(self):
        sym = BINANCE_SYMBOL
        if self.bn_last_id is None:
            j = requests.get("https://api.binance.com/api/v3/aggTrades", params={"symbol": sym, "limit": 1}, timeout=4).json()
            self.bn_last_id = j[-1]["a"]; return
        for _ in range(5):
            j = requests.get("https://api.binance.com/api/v3/aggTrades",
                             params={"symbol": sym, "limit": 1000, "fromId": self.bn_last_id + 1}, timeout=4).json()
            if not isinstance(j, list) or not j:
                break
            pts = []
            for t in j:
                q = float(t["q"]); pts.append((t["T"] / 1000.0, -q if t["m"] else q))
                self.bn_last_id = max(self.bn_last_id, t["a"])
            with self.lock:
                self.bn.extend(pts)
            if len(j) < 1000:
                break

    def _poll_cb(self):
        j = requests.get("https://api.exchange.coinbase.com/products/BTC-USD/trades", params={"limit": 100}, timeout=4).json()
        if not isinstance(j, list):
            return
        newest = self.cb_last_id; pts = []
        for t in j:
            tid = int(t["trade_id"])
            if self.cb_last_id is not None and tid <= self.cb_last_id:
                continue
            sz = float(t["size"])
            # en Coinbase 'side' es el lado del MAKER → el agresor compra si side == 'sell'
            try: ts = datetime.fromisoformat(str(t["time"]).replace("Z", "+00:00")).timestamp()
            except Exception: ts = time.time()
            pts.append((ts, sz if t["side"] == "sell" else -sz))
            if newest is None or tid > newest: newest = tid
        if self.cb_last_id is None:            # primera lectura = semilla (no contar historia)
            self.cb_last_id = newest; return
        self.cb_last_id = newest
        pts.sort()
        with self.lock:
            self.cb.extend(pts)

    def _run(self):
        while True:
            t0 = time.time()
            for fn in (self._poll_bn, self._poll_cb):
                try: fn()
                except Exception: self.errors += 1
            time.sleep(max(0.2, 2.0 - (time.time() - t0)))

    def cvd(self, which, secs, now=None):
        now = now or time.time()
        with self.lock:
            dq = self.bn if which == "bn" else self.cb
            return sum(q for t, q in dq if now - secs <= t <= now)


_flow_feeds = _FlowFeeds()

def _post_loss_guard_log(record):
    try:
        with open("post_loss_guard_log.jsonl", "a") as f:
            f.write(json.dumps(record, default=str) + "\n")
    except Exception:
        pass

_post_loss_guard = PostLossGuard(logger=_post_loss_guard_log)

def _post_loss_spot_series():
    try:
        with spot_tracker.lock:
            return list(spot_tracker.prices)
    except Exception:
        return []

_PM_TRADES = deque(maxlen=50000)     # (ts, asset_id, side, size, price) — del WebSocket del libro


def _note_pm_trades(obj):
    """Llamada desde on_message (muy liviana): guarda los trades 'last_trade_price' de Polymarket."""
    try:
        for it in (obj if isinstance(obj, list) else [obj]):
            if not isinstance(it, dict):
                continue
            if (it.get("event_type") or it.get("type")) != "last_trade_price":
                continue
            ts = float(it.get("timestamp") or 0)
            if ts > 1e12: ts /= 1000.0
            _PM_TRADES.append((ts or time.time(), str(it.get("asset_id")), str(it.get("side", "")).upper(),
                               float(it.get("size", 0) or 0), float(it.get("price", 0) or 0)))
    except Exception:
        pass


def _pm_net_up_usd(epoch):
    """Igual que el capturador: + = dinero hacia UP (agresor compra UP o vende DN), desde el inicio."""
    if len(S.tokens) != 2:
        return None
    up_id, dn_id = str(S.tokens[0]), str(S.tokens[1])
    net = 0.0
    for ts, aid, side, sz, px in list(_PM_TRADES):
        if ts < epoch or aid not in (up_id, dn_id):
            continue
        is_up = aid == up_id
        net += (1 if ((side == "BUY") == is_up) else -1) * sz * px
    return net


def _pm_net_up_usd_last(epoch, secs, now=None):
    """Igual que _pm_net_up_usd pero solo los últimos `secs` segundos (como pm_ws_net60_usd del capturador)."""
    if len(S.tokens) != 2:
        return None
    now = now or time.time()
    up_id, dn_id = str(S.tokens[0]), str(S.tokens[1])
    net = 0.0
    for ts, aid, side, sz, px in list(_PM_TRADES):
        if ts < epoch or ts < now - secs or aid not in (up_id, dn_id):
            continue
        is_up = aid == up_id
        net += (1 if ((side == "BUY") == is_up) else -1) * sz * px
    return net


# ── Motor común de los métodos laterales ─────────────────────────────────────────────────────
class _SideMethod:
    def __init__(self, name, enabled, rule, pct=None, paper_only=False):
        self.name = name; self.enabled = enabled; self.rule = rule; self.paper_only = paper_only
        self.pct = SIDE_PCT if pct is None else pct
        self.state_file = f"{name.lower()}_state.json"; self.log_file = f"{name.lower()}_log.jsonl"
        self.lock = threading.Lock(); self.st = None
        self.cyc = {"slug": None}; self.last_res = 0.0; self.res_th = None

    def log(self, rec):
        try:
            with open(self.log_file, "a") as f:
                f.write(json.dumps(rec, default=str) + "\n")
        except Exception:
            pass

    def state(self):
        if self.st is None:
            st = {"disabled": False, "losses": 0, "wins": 0, "day": None, "count_day": 0, "pending": [],
                  "paper_pending": [], "paper_wins": 0, "paper_losses": 0}
            try:
                with open(self.state_file) as f:
                    st.update(json.load(f))
            except Exception:
                pass
            self.st = st
        return self.st

    def save(self):
        try:
            with open(self.state_file, "w") as f:
                json.dump(self.st, f)
        except Exception:
            pass

    # resultados (en hilo aparte)
    def kick_resolve(self):
        st = self.state()
        if not (st["pending"] or st["paper_pending"]) or time.time() - self.last_res < 30:
            return
        if self.res_th and self.res_th.is_alive():
            return
        self.last_res = time.time()
        self.res_th = threading.Thread(target=self._resolve, name=f"{self.name}resolve", daemon=True)
        self.res_th.start()

    def _resolve(self):
        st = self.state()
        for key, paper in (("pending", False), ("paper_pending", True)):
            with self.lock:
                todo = list(st[key])
            done = set()
            for p in todo:
                if time.time() < p["epoch"] + WINDOW_SECONDS + 60:
                    continue
                w = _tw_winner(p["slug"])
                if w is None:
                    if time.time() > p["epoch"] + WINDOW_SECONDS + 3600:
                        done.add(p["slug"])
                    continue
                done.add(p["slug"]); won = (w == p["side"])
                if paper:
                    st["paper_wins" if won else "paper_losses"] += 1
                    self.log({"ts": time.time(), "kind": f"{self.name}_PAPER_RESULT", "slug": p["slug"], "side": p["side"],
                              "winner": w, "won": won, "entry_real_ask": p["price"],
                              "paper_wins": st["paper_wins"], "paper_losses": st["paper_losses"]})
                    continue
                pnl = (p["shares"] - p["usdc"]) if won else -p["usdc"]
                st["wins" if won else "losses"] += 1
                self.log({"ts": time.time(), "kind": f"{self.name}_RESULT", "slug": p["slug"], "side": p["side"],
                          "winner": w, "won": won, "entry": p["price"], "usdc": p["usdc"], "pnl_est": round(pnl, 2),
                          "wins": st["wins"], "losses": st["losses"]})
                msg = (f"{'🎯' if won else '💀'} {self.name} {'WON' if won else 'LOST'} {p['side']} @{p['price']:.3f} | "
                       f"{'+' if pnl >= 0 else '-'}${abs(pnl):.2f} | {self.name} total {st['wins']}W/{st['losses']}L | {p['slug']}")
                print(msg); _tw_tg(msg)
                if not won and st["losses"] >= SIDE_STOP_AFTER_LOSSES:
                    st["disabled"] = True
                    stop = (f"⛔ {self.name} APAGADO tras {st['losses']} pérdida(s) — sigue en papel. "
                            f"Los demás métodos siguen normal. Reactivar: borrar {self.state_file}")
                    print(stop); _tw_tg(stop)
            if done:
                with self.lock:
                    st[key] = [p for p in st[key] if p["slug"] not in done]
                    self.save()

    def tick(self, client, ctx):
        if not self.enabled:
            return
        st = self.state()
        self.kick_resolve()
        c = self.cyc
        if c.get("slug") != ctx["slug"]:
            with self.lock:
                already = any(p["slug"] == ctx["slug"] for p in st["pending"] + st["paper_pending"])
            self.cyc = c = {"slug": ctx["slug"], "done": already, "tries": 0, "last_rest": 0.0, "logged_skip": False}
        if c["done"]:
            return
        paper = bool(st["disabled"] or self.paper_only or not S.trading_enabled or S.paused_by_telegram)
        today = now_utc().strftime("%Y-%m-%d")
        if st.get("day") != today:
            st["day"] = today; st["count_day"] = 0; self.save()
        if not paper and st["count_day"] >= SIDE_MAX_PER_DAY:
            return
        ok_rule, info = self.rule(ctx)
        if not ok_rule:
            return
        if self.name in ("CB", "FLOW"):
            _blocked, _guard_rec = _post_loss_guard.evaluate(
                self.name, ctx["side"], _post_loss_spot_series(), ctx.get("slug"))
            if _blocked:
                self.log({**_guard_rec, "kind": self.name + "_POST_LOSS_BLOCK"})
                return
        now = time.time()
        _ev = pausa_evento(now)
        if _ev:                                  # 10-28: pausa por calendario (FOMC, CPI, empleo…)
            if not c.get("logged_ev"):
                c["logged_ev"] = True
                self.log({"ts": round(now, 2), "kind": f"{self.name}_SKIP_EVENTO", "slug": ctx["slug"],
                          "epoch": ctx["epoch"], "side": ctx["side"], "elapsed": round(ctx["el"], 1), "evento": _ev})
            return
        sig_c = ctx.get("sig")
        if sig_c is None or sig_c >= VOL_MAX:    # 10-28: tope de volatilidad (o σ aún desconocida)
            if not c.get("logged_vol"):
                c["logged_vol"] = True
                self.log({"ts": round(now, 2), "kind": f"{self.name}_SKIP_VOL", "slug": ctx["slug"],
                          "epoch": ctx["epoch"], "side": ctx["side"], "elapsed": round(ctx["el"], 1),
                          "sigma": sig_c, "vol_max": VOL_MAX, **info})
            return
        s60 = ctx.get("sig60")
        if s60 is None or s60 >= VOL60_MAX:      # 10-28: volatilidad de los últimos 60 s
            if not c.get("logged_vol60"):
                c["logged_vol60"] = True
                self.log({"ts": round(now, 2), "kind": f"{self.name}_SKIP_VOL60", "slug": ctx["slug"],
                          "epoch": ctx["epoch"], "side": ctx["side"], "elapsed": round(ctx["el"], 1),
                          "sigma60": s60, "vol60_max": VOL60_MAX, **info})
            return
        # 10-26: colchón mínimo. Con BTC pegado al PTB un pico de 1 s puede poner el precio en 0.90
        # (ciclo 16:10: DS a 12 USD, cb30 −0.65, DN 0.90 → ganó UP). Sigue vigilando el ciclo.
        cush = abs(ctx["cur"] - ctx["ptb"])
        if cush < SIDE_MIN_CUSH:
            if not c.get("logged_cush"):
                c["logged_cush"] = True
                self.log({"ts": round(now, 2), "kind": f"{self.name}_SKIP_CUSH", "slug": ctx["slug"],
                          "epoch": ctx["epoch"], "side": ctx["side"], "elapsed": round(ctx["el"], 1),
                          "ds_delta": round(ctx["cur"] - ctx["ptb"], 2), "min_cush": SIDE_MIN_CUSH,
                          "ws_ask": safe_float(S.book.get(S.tokens[0] if ctx["side"] == "UP" else S.tokens[1], {}).get("best_ask"), None),
                          **info})
            return
        # 10-27: no comprar si el colchón ya viene regresando (≥30% de su mejor nivel del ciclo).
        rr = ctx.get("ret_rel")
        if rr is not None and rr >= SIDE_MAX_RET_REL:
            if not c.get("logged_ret"):
                c["logged_ret"] = True
                self.log({"ts": round(now, 2), "kind": f"{self.name}_SKIP_RET", "slug": ctx["slug"],
                          "epoch": ctx["epoch"], "side": ctx["side"], "elapsed": round(ctx["el"], 1),
                          "ds_delta": round(ctx["cur"] - ctx["ptb"], 2), "ret_rel": rr, "max_ret_rel": SIDE_MAX_RET_REL,
                          "ws_ask": safe_float(S.book.get(S.tokens[0] if ctx["side"] == "UP" else S.tokens[1], {}).get("best_ask"), None),
                          **info})
            return
        _v5, _sg = ctx.get("vel5"), ctx.get("sig")
        _pico = bool(_v5 is not None and _sg and _v5 >= SIDE_SPIKE_K * _sg * 5 ** 0.5)
        if c.get("logged_ret") and rr is not None and (rr >= SIDE_RET_AFTER_SKIP or _pico) and \
                not (ctx.get("z") is not None and ctx["z"] >= SIDE_Z_AFTER_SKIP):
            if not c.get("logged_mem"):
                c["logged_mem"] = True
                self.log({"ts": round(now, 2), "kind": f"{self.name}_SKIP_RET_MEM", "slug": ctx["slug"],
                          "epoch": ctx["epoch"], "side": ctx["side"], "elapsed": round(ctx["el"], 1),
                          "ds_delta": round(ctx["cur"] - ctx["ptb"], 2), "ret_rel": rr, "z": ctx.get("z"), "pico": _pico,
                          "ws_ask": safe_float(S.book.get(S.tokens[0] if ctx["side"] == "UP" else S.tokens[1], {}).get("best_ask"), None),
                          **info})
            return
        if now - c["last_rest"] < 2.0:
            return
        c["last_rest"] = now
        token_id = S.tokens[0] if ctx["side"] == "UP" else S.tokens[1]
        ws_ask = safe_float(S.book.get(token_id, {}).get("best_ask"), None)
        try:
            lb = ctx["client"].get_order_book(token_id)
            asks_raw = lb.get("asks") if isinstance(lb, dict) else getattr(lb, "asks", None)
            lv = sorted(((_lvl_price(a), _lvl_size(a)) for a in (asks_raw or []) if _lvl_price(a) is not None),
                        key=lambda x: x[0])
        except Exception:
            lv = []
        if not lv:
            return
        ask = float(lv[0][0]); top3 = float(sum(q or 0 for _, q in lv[:3]))
        base = {"ts": round(now, 2), "slug": ctx["slug"], "epoch": ctx["epoch"], "side": ctx["side"],
                "elapsed": round(ctx["el"], 1), "real_ask": ask, "real_top3": round(top3, 1), "ws_ask": ws_ask,
                "ptb_real": round(ctx["ptb"], 2), "ds_delta": round(ctx["cur"] - ctx["ptb"], 2),
                "ds_age_s": round(ctx["age"], 2), "v60": ctx.get("v60"), "pm_net_side_usd": ctx.get("pm_net"),
                "cvd_bn_60s_side": ctx.get("cvd_bn60"), "cvd_cb_30s_side": ctx.get("cvd_cb30"),
                "vel5": ctx.get("vel5"), "ret_rel": ctx.get("ret_rel"), "sigma": ctx.get("sig"), "sigma60": ctx.get("sig60"), "z": ctx.get("z"), "pm60_side_usd": ctx.get("pm60"),
                "pct": self.pct, **info}
        if not (SIDE_PRICE_MIN <= ask <= SIDE_PRICE_MAX) or top3 < SIDE_MIN_TOP3:
            if not c["logged_skip"]:
                c["logged_skip"] = True; self.log({**base, "kind": f"{self.name}_SKIP_PRICE"})
            return
        if paper:
            c["done"] = True
            self.log({**base, "kind": f"{self.name}_PAPER",
                      "motivo": ("apagado tras pérdida" if st["disabled"] else
                                 "solo papel" if self.paper_only else "trading deshabilitado")})
            with self.lock:
                st["paper_pending"].append({"slug": ctx["slug"], "epoch": ctx["epoch"], "side": ctx["side"], "price": ask})
                self.save()
            print(f"  📝 {self.name} EN PAPEL (no compra): {ctx['side']} @${ask:.3f} t+{ctx['el']:.0f}s")
            return
        bal = S.last_known_balance if S.last_known_balance is not None else BALANCE_FALLBACK_USDC
        side_usd = _pct_usdc(self.pct, SIDE_USDC)
        # 10-29 CB: reducir tamaño cuando ask≥0.90 y z disponible pero <2.0 (entradas más caras/dudosas)
        if self.name == "CB" and ask >= 0.90 and ctx.get("z") is not None and ctx["z"] < 2.0:
            side_usd = round(side_usd * 0.65, 2)
        if bal is not None and bal < max(MIN_BALANCE_TO_TRADE, side_usd):
            return
        c["tries"] += 1
        if c["tries"] >= SIDE_MAX_TRIES:
            c["done"] = True
        print(f"  🧭 {self.name} BUY {ctx['side']} @${ask:.3f} t+{ctx['el']:.0f}s | ${side_usd:.2f}")
        ok, resp, amount = _side_buy(client, token_id, ask, side_usd)
        rec = {**base, "kind": f"{self.name}_SIGNAL", "ok": bool(ok), "try": c["tries"], "amount": amount}
        if ok:
            c["done"] = True
            shares = safe_float(resp.get("actual_shares"), 0) or 0.0
            paid = safe_float(resp.get("actual_usdc"), 0) or 0.0
            fill = (paid / shares) if shares > 0 and paid > 0 else ask
            rec.update({"fill_price": round(fill, 4), "shares": round(shares, 4), "paid_usdc": round(paid, 4),
                        "slip": round(fill - ask, 4)})
            st["count_day"] += 1
            with self.lock:
                st["pending"].append({"slug": ctx["slug"], "epoch": ctx["epoch"], "side": ctx["side"],
                                      "price": float(fill), "usdc": float(paid or amount), "shares": float(shares), "ts": now})
                self.save()
            _side_register(ctx["slug"], ctx["side"], shares, self.name)
            _pct_note_spent(paid or amount)
            _tw_tg(f"🧭 {self.name} BUY {ctx['side']} @{fill:.3f} (libro {ask:.3f}) | ${paid or amount:.2f} | "
                   f"t+{ctx['el']:.0f}s | {ctx['slug']}")
        else:
            rec["resp"] = str(resp)[:300]
            print(f"  ❌ {self.name} BUY no ejecutada (intento {c['tries']}/{SIDE_MAX_TRIES}): {str(resp)[:120]}")
        self.log(rec)


def _side_buy(client, token_id, ask, usdc):
    """Orden de MERCADO FAK por monto exacto = acciones ENTERAS × precio (2 decimales) con precio
    tope = ask fresco. Así el monto tiene 2 decimales y las acciones son enteras."""
    k = max(1, int(usdc // ask))
    amount = round(k * ask, 2)
    if DRY_RUN:
        return True, {"status": "DRY_RUN", "actual_shares": float(k), "actual_usdc": amount}, amount
    try:
        from py_clob_client_v2.clob_types import MarketOrderArgs, OrderType as _OT
        from py_clob_client_v2.order_builder.constants import BUY as _BUYc
        try:
            args = MarketOrderArgs(token_id=token_id, amount=amount, side=_BUYc, price=round(ask, 2))
        except TypeError:
            args = MarketOrderArgs(token_id=token_id, amount=amount, side=_BUYc)
        signed = client.create_market_order(args)
        resp = client.post_order(signed, _OT.FAK if hasattr(_OT, "FAK") else _OT.FOK)
        print(f"📋 Side order (MERCADO FAK ${amount:.2f} ≈ {k} acc @≤{ask:.2f}): {resp}")
        resp = _enrich_order_response(resp, "BUY")
        if isinstance(resp, dict) and (resp.get("status") or "").upper() == "MATCHED" \
                and safe_float(resp.get("actual_shares"), 0) > 0:
            return True, resp, amount
        return False, resp, amount
    except Exception as e:
        return False, f"excepción: {e}", amount


def _rule_flow(ctx):
    pm, cv, v60 = ctx.get("pm_net"), ctx.get("cvd_bn60"), ctx.get("v60")
    sig, z = ctx.get("sig"), ctx.get("z")
    ret_rel = ctx.get("ret_rel")
    # Filtro exclusivo de FLOW: rechaza retroceso relativo > 10%.
    # Si el dato no está disponible, conserva el comportamiento anterior.
    ret_ok = ret_rel is None or ret_rel <= 0.10
    info = {"rule": f"pm≥{FLOW_PM_MIN:g} cvd60≥{FLOW_CVD_MIN:g} v60<{FLOW_V60_MAX:g} σ≥{FLOW_SIG_MIN:g} z≥{FLOW_Z_MIN:g} ret_rel≤0.10 (si disponible)"}
    ok = (
        pm is not None and cv is not None and v60 is not None
        and pm >= FLOW_PM_MIN and cv >= FLOW_CVD_MIN and v60 < FLOW_V60_MAX
        and sig is not None and sig >= FLOW_SIG_MIN
        and z is not None and z >= FLOW_Z_MIN
        and ret_ok
    )
    return ok, info

def _rule_cb(ctx):
    cv = ctx.get("cvd_cb30")
    z = ctx.get("z")
    ok = (cv is not None and cv < CB_CVD_MAX)
    # 10-29: cuando z está disponible, exigir CB_Z_MIN (filtra colchón débil; la pérdida 19:15 tenía z=1.32)
    if ok and z is not None and z < CB_Z_MIN:
        ok = False
    return ok, {"rule": f"cb30<{CB_CVD_MAX:g} z≥{CB_Z_MIN:g} (si disponible)"}


def _rule_late(ctx):
    el, v5, v60, v10, cb = ctx.get("el"), ctx.get("vel5"), ctx.get("v60"), ctx.get("v10"), ctx.get("cvd_cb30")
    # Filtro exclusivo de LATE: rechaza solo la combinación de velocidad débil
    # (< 2 USD/5 s) y CVD de Coinbase prácticamente neutral (|CVD| < 0.10 BTC).
    # Si CVD no está disponible, conserva el comportamiento anterior.
    weak_without_cb_confirmation = (
        v5 is not None and v5 < 2.0
        and cb is not None and abs(cb) < 0.10
    )
    info = {"rule": f"t≥{LATE_FROM_SEC:g} vel5≥{LATE_VEL5_MIN:g} v10≥{LATE_V10_MIN:g} v60≥{LATE_V60_MIN:g} cb30<{LATE_CB30_MAX:g}; skip if vel5<2 and |cb30|<0.10"}
    ok = (
        el is not None and v5 is not None and v60 is not None and v10 is not None
        and el >= LATE_FROM_SEC and v5 >= LATE_VEL5_MIN
        and v10 >= LATE_V10_MIN and v60 >= LATE_V60_MIN
        and (cb is None or cb < LATE_CB30_MAX)
        and not weak_without_cb_confirmation
    )
    return ok, info

def _rule_quiet(ctx):
    el, v5, pm60 = ctx.get("el"), ctx.get("vel5"), ctx.get("pm60")
    info = {"rule": f"t≥{QUIET_FROM_SEC:g} pm60<{QUIET_PM60_MAX:g} vel5≥{QUIET_VEL5_MIN:g}"}
    ok = (el is not None and v5 is not None and pm60 is not None and el >= QUIET_FROM_SEC
          and pm60 < QUIET_PM60_MAX and v5 >= QUIET_VEL5_MIN)
    return ok, info


_SIDE_METHODS = [_SideMethod("FLOW", FLOW_ENABLE, _rule_flow), _SideMethod("CB", CB_ENABLE, _rule_cb),
                 _SideMethod("LATE", LATE_ENABLE, _rule_late, LATE_PCT),
                 _SideMethod("QUIET", QUIET_ENABLE, _rule_quiet, QUIET_PCT, paper_only=not QUIET_LIVE)]
_SIDE_CTX = {"slug": None, "ptb": None, "sig": None}


def side_methods_tick(client):
    """Llamada desde el hilo de señales (cada DIAG). Errores se ignoran: nunca detiene al bot."""
    if not (FLOW_ENABLE or CB_ENABLE or LATE_ENABLE or QUIET_ENABLE):
        return
    try:
        _shadow_ds.start(); _flow_feeds.start(); _post_loss_guard.start()
        if not S.slug or len(S.tokens) != 2:
            return
        epoch = int(str(S.slug).split("-")[-1]); now = time.time(); el = now - epoch
        for m in _SIDE_METHODS:
            if m.enabled:
                m.kick_resolve()
        if el < SIDE_FROM_SEC or el > SIDE_TO_SEC:
            return
        ser = _tw_ds_series()
        if len(ser) < 60:
            return
        if _SIDE_CTX["slug"] != S.slug:
            _SIDE_CTX.update({"slug": S.slug, "ptb": None, "sig": None})
        if _SIDE_CTX["ptb"] is None:
            pts = [v for t, v in ser if epoch - 60 <= t < epoch]
            if len(pts) < 30:
                return
            _SIDE_CTX["ptb"] = sum(pts) / len(pts)
        if _SIDE_CTX["sig"] is None:                # σ igual que TW: saltos de DS /√dt en los 900 s previos
            hist = [(t, v) for t, v in ser if epoch - 900 <= t < epoch]
            if len(hist) >= 120:
                d_ = [(v2 - v1) / max(t2 - t1, 1.0) ** 0.5 for (t1, v1), (t2, v2) in zip(hist, hist[1:])]
                m_ = sum(d_) / len(d_)
                _SIDE_CTX["sig"] = (sum((x - m_) ** 2 for x in d_) / len(d_)) ** 0.5
        ptb = _SIDE_CTX["ptb"]; last_t, cur = ser[-1]; age = now - last_t
        if age > SIDE_DS_MAX_AGE:
            return
        sg = 1 if cur > ptb else -1
        v0 = None
        for t, v in ser:
            if t <= last_t - 60: v0 = v
            else: break
        v10_0 = None                                # DS 10 s antes del último dato (como v10 del capturador)
        for t, v in ser:
            if t <= last_t - 10: v10_0 = v
            else: break
        v5 = None                                   # DS hace 5 s (reloj), igual que ds_vel_5s del capturador
        for t, v in ser:
            if t <= now - 5: v5 = v
            else: break
        cyc = [v for t, v in ser if t >= epoch]
        best = max([(v - ptb) * sg for v in cyc] + [(cur - ptb) * sg])
        ret_rel = (best - (cur - ptb) * sg) / max(abs(cur - ptb), 1.0)   # cuánto devolvió de su mejor colchón
        sig = _SIDE_CTX.get("sig")
        pm = _pm_net_up_usd(epoch)
        pm60 = _pm_net_up_usd_last(epoch, 60, now)
        ctx = {"slug": S.slug, "epoch": epoch, "el": el, "ptb": ptb, "cur": cur, "age": age,
               "pm60": round(pm60 * sg, 1) if pm60 is not None else None,
               "ret_rel": round(ret_rel, 3), "sig": round(sig, 4) if sig else None,
               "sig60": (lambda x: round(x, 3) if x is not None else None)(sigma_ultimos(ser, 60)),
               "z": round(abs(cur - ptb) / (sig * max(260.0 - el + age, 1.0) ** 0.5), 3) if sig else None,
               "vel5": round((cur - v5) * sg, 2) if v5 is not None else None,
               "v10": round((cur - v10_0) * sg, 2) if v10_0 is not None else None,
               "side": "UP" if sg > 0 else "DN", "client": client,
               "v60": round((cur - v0) * sg, 2) if v0 is not None else None,
               "pm_net": round(pm * sg, 1) if pm is not None else None,
               "cvd_bn60": round(_flow_feeds.cvd("bn", 60) * sg, 3),
               "cvd_cb30": round(_flow_feeds.cvd("cb", 30) * sg, 3),
               "_ds_series": ser}
        for m in _SIDE_METHODS:
            try:
                m.tick(client, ctx)
            except Exception as e:
                print(f"  ⚠️ {m.name} error (ignorado): {str(e)[:100]}")
    except Exception as e:
        try: print(f"  ⚠️ side_methods error (ignorado): {str(e)[:100]}")
        except Exception: pass


def maybe_enter_position(client, signal, reason):
    daily_rollover()
    maybe_disable_trading()
    if not S.trading_enabled:
        return
    # CRITICAL: never buy while holding a position
    if S.position_token is not None:
        return
    if signal == "NONE":
        return
    now = time.time()
    if S.orders_sent >= MAX_ORDERS_PER_MARKET:
        return
    if (now - S.last_order_ts) < ORDER_COOLDOWN_SEC:
        return
    # ----------------------------------------------------------------
    # FIX BUY-RETRY ANTI-CHASE (2026-04-26)
    # Si tuvimos un BUY fail reciente, esperar BUY_FAIL_COOLDOWN_SEC
    # antes de reintentar. Esto evita que el bot persiga el precio
    # cuando un mercado ilíquido reordena rápidamente entre intentos
    # (caso real: compra a 0.28 cuando había decidido a 0.95).
    # ----------------------------------------------------------------
    BUY_FAIL_COOLDOWN_SEC = float(os.getenv("BUY_FAIL_COOLDOWN_SEC", "10"))
    if (now - getattr(S, "last_buy_fail_ts", 0.0)) < BUY_FAIL_COOLDOWN_SEC:
        return
    if len(S.tokens) != 2:
        return

    up_id, dn_id = S.tokens

    # v5.0: Support both TREND_* and REVERT_* signals
    if signal in ("REVERT_UP", "TREND_UP", "PEAK_REVERT_UP"):
        token_id, label = up_id, "UP"
    elif signal in ("REVERT_DN", "TREND_DN", "PEAK_REVERT_DN"):
        token_id, label = dn_id, "DN"
    else:
        return

    is_trend_follow    = signal.startswith("TREND_")
    is_peak_reversion  = signal.startswith("PEAK_REVERT_")

    bid, ask = best_bid_ask(token_id)
    if REQUIRE_BOOK_FOR_TRADE and (bid is None or ask is None):
        return
    if bid is None or ask is None:
        return
    if SKIP_DUMMY_BOOK and is_dummy_001_099(bid, ask):
        return

    # ----------------------------------------------------------------
    # SIGNAL LOGGING (2026-06-03): registra CADA señal evaluada en
    # signals_log.jsonl, compremos o no, para análisis de backtest exacto.
    # Solo registra UNA VEZ por (slug, decision) para no spamear el archivo.
    # El outcome se completa al cerrar el mercado vía update_signal_outcome.
    # ----------------------------------------------------------------
    LOG_ALL_SIGNALS = os.getenv("LOG_ALL_SIGNALS", "1") == "1"
    if not hasattr(S, "_logged_signals"):
        S._logged_signals = set()
    # Reset del set cuando cambia el mercado
    if getattr(S, "_logged_signals_slug", None) != S.slug:
        S._logged_signals = set()
        S._logged_signals_slug = S.slug

    def _log_eval(decision_str):
        """Loguea esta señal con su decisión, una sola vez por (slug, decision)."""
        if not LOG_ALL_SIGNALS:
            return
        key = f"{S.slug}|{decision_str.split(':')[0]}"  # agrupar por tipo de decisión
        if key in S._logged_signals:
            return
        S._logged_signals.add(key)
        try:
            el, lf = window_timing()
            btc_open_now = cycle_log.btc_open if hasattr(cycle_log, 'btc_open') else None
            log_signal_entry(
                signal=signal, side=label, entry_price=ask,
                elapsed=el or 0, left=lf or 0,
                decision=decision_str, btc_open=btc_open_now,
            )
        except Exception:
            pass

    # ----------------------------------------------------------------
    # MULTI-ROUND CHAINLINK CONFIRMATION (2026-05-05)
    # 
    # Idea: en lugar de confirmar entre lecturas DIAG (cada 3s = info CL repetida),
    # confirmar entre DOS ROUNDS DISTINTOS DE CHAINLINK (info nueva real).
    # 
    # Round 1: primera vez que aparece señal válida → guardar (cl_price, cl_delta, token_price)
    # Round 2: cuando cl_price cambia (Chainlink hizo update on-chain)
    #   → Validar:
    #      a. CL Δ creció (más fuerte la señal en el nuevo round)
    #      b. Precio del token subió proporcionalmente (mercado acompaña)
    #      c. Sigue habiendo tiempo suficiente para cierre del mercado
    #   → Si pasa: COMPRAR
    #   → Si NO: ABORTAR
    # 
    # Variables env:
    #   USE_MULTI_ROUND_CONFIRM=1     activa la lógica (0 = comportamiento anterior, 1 = activo)
    #   CL_GROWTH_MIN=10              CL Δ debe crecer al menos $X entre rounds
    #   PRICE_GROWTH_MIN=0.01         Precio del token debe subir al menos $X
    #   MIN_TIME_LEFT_SEC=60          Mínimo de segundos restantes para entrar
    # ----------------------------------------------------------------
    USE_MULTI_ROUND_CONFIRM = os.getenv("USE_MULTI_ROUND_CONFIRM", "0") == "1"
    CL_GROWTH_MIN = float(os.getenv("CL_GROWTH_MIN", "10"))
    PRICE_GROWTH_MIN = float(os.getenv("PRICE_GROWTH_MIN", "0.01"))
    MIN_TIME_LEFT_SEC = float(os.getenv("MIN_TIME_LEFT_SEC", "60"))
    # MR_PRICE_MIN (2026-06-02): precio MÍNIMO del lado predicho para que el
    # Multi-Round considere entrar. Validado en backtest: con bet $176, solo a
    # precios >= $0.99 el Multi-Round es rentable (100% WR en esa zona).
    # Por debajo (precio 0.90-0.97), el Multi-Round pierde dinero porque el
    # profit por win es muy pequeño y las losses ocasionales dominan.
    # Para los precios 0.85-0.97 se usa Fast-Track con filtros propios.
    MR_PRICE_MIN = float(os.getenv("MR_PRICE_MIN", "0.0"))  # 0.0 = sin filtro

    # ----------------------------------------------------------------
    # QUIET HOURS (2026-06-02): stand-by automático en horarios problemáticos.
    # Hours UTC donde el bot NO debe operar (historicamente con peor WR).
    # Ejemplo: "7,8,14,16,19,21" cubre apertura Asia + apertura US + cierres.
    # ----------------------------------------------------------------
    QUIET_HOURS_UTC = os.getenv("QUIET_HOURS_UTC", "").strip()
    if QUIET_HOURS_UTC:
        try:
            quiet_set = set(int(h.strip()) for h in QUIET_HOURS_UTC.split(",") if h.strip())
            current_hour_utc = now_utc().hour
            if current_hour_utc in quiet_set:
                # Print solo una vez por mercado para no spamear
                if S.confirm_slug != S.slug:
                    print(f"  ⏰ QUIET HOUR (UTC {current_hour_utc:02d}:00) — bot en stand-by automático "
                          f"(QUIET_HOURS_UTC={QUIET_HOURS_UTC})")
                    S.confirm_slug = S.slug  # marcar como visto
                _log_eval(f"QUIET_HOUR_SKIP: UTC {current_hour_utc:02d}")
                return
        except Exception as e:
            pass  # ignorar si la variable está mal formada

    # ----------------------------------------------------------------
    # FAST-TRACK al ROUND 1 (2026-06-02):
    # Si las condiciones de calidad son MUY ALTAS, comprar al primer round
    # sin esperar el segundo. Esto captura oportunidades donde el mercado YA
    # confirmó visualmente la señal (precio del lado predicho ya está alto).
    # 
    # Validado en backtest: con estos filtros, WR = 100% en 104 trades.
    # 
    # Variables env:
    #   USE_FAST_TRACK=1              activa fast-track (default 0)
    #   FT_PRICE_MIN=0.85             precio mínimo del lado predicho
    #   FT_PRICE_MAX=0.97             precio máximo (evita 0.98-0.99 donde profit es minúsculo)
    #   FT_BN_CHG_MIN=40              cambio mínimo de Binance en USD
    #   FT_RSI_UP_MAX=75              RSI máximo para BUY UP (evitar sobrecompra)
    #   FT_RSI_DN_MIN=25              RSI mínimo para BUY DN (evitar sobreventa)
    #   FT_REQUIRE_MACD_MATCH=1       MACD direccional debe coincidir con side
    #   FT_REQUIRE_CANDLE_COHERENT=1  candle_form no debe contradecir el side
    # ----------------------------------------------------------------
    USE_FAST_TRACK = os.getenv("USE_FAST_TRACK", "0") == "1"
    FT_PRICE_MIN = float(os.getenv("FT_PRICE_MIN", "0.85"))
    FT_PRICE_MAX = float(os.getenv("FT_PRICE_MAX", "0.97"))
    FT_BN_CHG_MIN = float(os.getenv("FT_BN_CHG_MIN", "40"))
    FT_RSI_UP_MAX = float(os.getenv("FT_RSI_UP_MAX", "75"))
    FT_RSI_DN_MIN = float(os.getenv("FT_RSI_DN_MIN", "25"))
    FT_REQUIRE_MACD_MATCH = os.getenv("FT_REQUIRE_MACD_MATCH", "1") == "1"
    FT_REQUIRE_CANDLE_COHERENT = os.getenv("FT_REQUIRE_CANDLE_COHERENT", "1") == "1"
    # NUEVOS FILTROS (2026-06-03) — bloquear casos que el LOSS del 06/03 13:00 reveló:
    #   FT_IMB_MAX: imbalance máximo permitido (loss tenía imb=13.6, wins <2)
    #   FT_MACD_HIST_MIN: MACD histograma mínimo (loss tenía +1.7, wins +11 a +15)
    #   FT_REQUIRE_LAST_CANDLE_OK: last_candle no debe ser contraria al side
    FT_IMB_MAX = float(os.getenv("FT_IMB_MAX", "100"))  # 100 = sin filtro
    FT_MACD_HIST_MIN = float(os.getenv("FT_MACD_HIST_MIN", "0"))  # 0 = solo signo positivo
    # CARVE-OUT 2026-10-15: omitir el filtro MACD cuando el precio del token es
    # >= este valor. Datos verificados (watcher): permitir señales con MACD en
    # contra a precio >= $0.91 dio 84W/0L (+$223); el único loss estaba en $0.90,
    # por eso solo se omite a partir de 0.91. 0.0 = desactivado (MACD siempre aplica).
    FT_MACD_SKIP_ABOVE_PRICE = float(os.getenv("FT_MACD_SKIP_ABOVE_PRICE", "0.0"))
    FT_REQUIRE_LAST_CANDLE_OK = os.getenv("FT_REQUIRE_LAST_CANDLE_OK", "0") == "1"
    FT_REJECT_DOJI = os.getenv("FT_REJECT_DOJI", "1") == "1"  # rechazar velas DOJI (indecisión)
    # NUEVO 2026-06-14: bloquear compras cuando la velocidad del precio va en
    # contra del trade (reversión tardía). FT_VELOCITY_MIN = umbral en $/s para
    # considerar la velocidad "significativa" (evita rechazar por ruido).
    FT_BLOCK_VELOCITY_AGAINST = os.getenv("FT_BLOCK_VELOCITY_AGAINST", "1") == "1"
    FT_VELOCITY_MIN = float(os.getenv("FT_VELOCITY_MIN", "0.5"))  # $/s mínimo para bloquear
    # NUEVO 2026-06-26: rechazar compras a precio ALTO cuando la volatilidad (ATR)
    # es extrema. Lógica: a precio >= FT_ATR_PRICE_MIN ganas <$2, pero con ATR alto
    # el riesgo de reversión sube → mala relación riesgo/recompensa. Capturó el loss
    # 1782441000 (DN @$0.96, ATR=127) que ningún otro filtro atrapaba.
    # Poner FT_ATR_MAX_AT_HIGH_PRICE=0 para desactivar.
    FT_ATR_MAX_AT_HIGH_PRICE = float(os.getenv("FT_ATR_MAX_AT_HIGH_PRICE", "100"))
    FT_ATR_PRICE_MIN = float(os.getenv("FT_ATR_PRICE_MIN", "0.96"))
    
    # Función helper: ¿el fast-track aprueba esta señal?
    def fast_track_check():
        """Retorna (bool, str) — (aprueba, razón_si_no)"""
        if not USE_FAST_TRACK:
            return False, None
        if not is_trend_follow:
            return False, None
        
        # 1. Precio del lado predicho en rango óptimo
        if ask < FT_PRICE_MIN:
            return False, f"price ${ask:.3f} < FT_PRICE_MIN ${FT_PRICE_MIN}"
        if ask > FT_PRICE_MAX:
            return False, f"price ${ask:.3f} > FT_PRICE_MAX ${FT_PRICE_MAX}"
        
        # 2. RSI no extremo
        try:
            rsi_now, _ = candle_analyzer.rsi()
        except Exception:
            rsi_now = None
        if rsi_now is not None:
            side_is_up = signal == "TREND_UP"
            if side_is_up and rsi_now > FT_RSI_UP_MAX:
                return False, f"RSI={rsi_now:.0f} > FT_RSI_UP_MAX={FT_RSI_UP_MAX} (sobrecompra)"
            if not side_is_up and rsi_now < FT_RSI_DN_MIN:
                return False, f"RSI={rsi_now:.0f} < FT_RSI_DN_MIN={FT_RSI_DN_MIN} (sobreventa)"
        
        # 3. BN_chg mínimo (Binance se mueve realmente desde apertura del mercado)
        try:
            bn_chg = spot_tracker.change_since_window_start() or 0
            btc_price = spot_tracker.latest() or 0
            bn_change_usd = abs(bn_chg) * btc_price  # convertir a USD
        except Exception:
            bn_change_usd = None
        if bn_change_usd is not None and bn_change_usd < FT_BN_CHG_MIN:
            return False, f"BN_chg=${bn_change_usd:.0f} < FT_BN_CHG_MIN=${FT_BN_CHG_MIN}"
        
        # 4. MACD direccional coincide
        #    CARVE-OUT 2026-10-15: si el precio (ask) es >= FT_MACD_SKIP_ABOVE_PRICE,
        #    se OMITE este filtro (verificado 84W/0L permitiendo MACD-disagreement
        #    a precio alto). El único loss estaba en $0.90, por eso solo se omite
        #    a partir de 0.91. Con FT_MACD_SKIP_ABOVE_PRICE=0.0 el filtro siempre aplica.
        _macd_skip = (FT_MACD_SKIP_ABOVE_PRICE > 0 and ask >= FT_MACD_SKIP_ABOVE_PRICE)
        if FT_REQUIRE_MACD_MATCH and not _macd_skip:
            try:
                # FIX 2026-06-04: MACD(3/15/3) para velas 1min (no el estándar 12/26/9)
                macd_v, macd_s, _ = candle_analyzer.macd(fast=3, slow=15, signal=3)
                macd_h = (macd_v - macd_s) if (macd_v is not None and macd_s is not None) else None
            except Exception:
                macd_h = None
            if macd_h is not None:
                want_positive = signal == "TREND_UP"
                if want_positive and macd_h <= 0:
                    return False, f"MACD hist={macd_h:.1f} no es UP (esperado ▲ para BUY UP)"
                if not want_positive and macd_h >= 0:
                    return False, f"MACD hist={macd_h:.1f} no es DN (esperado ▼ para BUY DN)"
                # NUEVO 2026-06-03: MACD histograma debe ser FUERTE (no apenas positivo)
                # En el loss del 06/03 13:00 UTC, MACD_hist era solo +1.7 (wins: +11 a +15)
                if FT_MACD_HIST_MIN > 0:
                    if want_positive and macd_h < FT_MACD_HIST_MIN:
                        return False, f"MACD hist={macd_h:.1f} < FT_MACD_HIST_MIN={FT_MACD_HIST_MIN} (señal débil)"
                    if not want_positive and abs(macd_h) < FT_MACD_HIST_MIN:
                        return False, f"MACD hist={macd_h:.1f} demasiado débil (|hist| < {FT_MACD_HIST_MIN})"
        
        # 5. Candle coherente con side (forming actual)
        if FT_REQUIRE_CANDLE_COHERENT:
            cf = None
            try:
                if hasattr(candle_analyzer, '_current_candle') and candle_analyzer._current_candle:
                    cf = candle_analyzer._current_candle.get("type", "")
            except Exception:
                cf = None
            # FIX 2026-06-08: si forming está VACÍO (cambio de vela, segundos 00-04 del
            # minuto), RECHAZAR en vez de aprobar por defecto. Los losses del 06/07-08
            # ocurrieron porque el bot compró justo en el cambio de vela cuando los
            # filtros de candle no tenían datos válidos → aprobaban sin validar.
            if not cf:
                return False, "forming candle vacía (cambio de vela) — esperar a que se forme"
            if cf:
                side_is_up = signal == "TREND_UP"
                # Contradicciones: UP con candle bearish fuerte, DN con candle bullish fuerte
                if side_is_up and cf in ('STRONG_BEAR', 'BEAR'):
                    return False, f"candle={cf} contradice BUY UP"
                if not side_is_up and cf in ('STRONG_BULL', 'BULL'):
                    return False, f"candle={cf} contradice BUY DN"
                # NOTA 2026-06-14: REJECTION en el FORMING (vela en progreso) NO
                # es buen filtro — 8 wins tenían REJECTION_UP/DN en forming y ganaron
                # (la vela aún cambia). El loss 1781474400 se bloquea mejor por el
                # filtro de VELOCITY (más abajo), no por REJECTION del forming.
                # Mantenemos solo el rechazo de REJECTION_DN para UP y REJECTION_UP
                # para DN (rechazo claramente contrario al lado).
                if side_is_up and cf in ('REJECTION_DN',):
                    return False, f"candle={cf} (rechazo bajista) contradice BUY UP"
                if not side_is_up and cf in ('REJECTION_UP',):
                    return False, f"candle={cf} (rechazo alcista) contradice BUY DN"
                # NUEVO 2026-06-08: bloquear DOJI (vela de indecisión).
                # El loss 1780875900 (06/07) tenía forming=DOJI. Rechazar DOJI
                # llevó el WR de 98.6% → 100% en el backtest de 87 trades, y
                # ADEMÁS aumentó el PnL ($23.5/día vs $18.8/día) porque el loss
                # evitado pesa más que los wins pequeños sacrificados.
                # Controlable con FT_REJECT_DOJI (default 1).
                if FT_REJECT_DOJI and cf == 'DOJI':
                    return False, f"candle=DOJI (indecisión) — no operar sin dirección clara"
        
        # 6. NUEVO 2026-06-03: last_candle (vela anterior cerrada) coherente con side
        # En el loss del 06/03 13:00, last_candle=STRONG_BEAR pero el bot quería BUY UP
        if FT_REQUIRE_LAST_CANDLE_OK:
            try:
                last_c = candle_analyzer.last_candle(include_current=False)
                lc_type = last_c.get('type', '') if last_c else ''
            except Exception:
                lc_type = ''
            # FIX 2026-06-08: si last_candle vacío (datos insuficientes), rechazar
            if not lc_type:
                return False, "last_candle vacía — datos insuficientes, esperar"
            if lc_type:
                side_is_up = signal == "TREND_UP"
                if side_is_up and lc_type in ('STRONG_BEAR', 'BEAR'):
                    return False, f"last_candle={lc_type} contradice BUY UP (vela previa bajista)"
                if not side_is_up and lc_type in ('STRONG_BULL', 'BULL'):
                    return False, f"last_candle={lc_type} contradice BUY DN (vela previa alcista)"
        
        # 7. NUEVO 2026-06-03: imbalance no demasiado alto
        # En el loss del 06/03 13:00, imb=13.6 (wins tenían imb < 2)
        # Book muy sesgado = trap potencial
        if FT_IMB_MAX < 100:
            try:
                imb_now = binance_depth.imbalance()
            except Exception:
                imb_now = None
            if imb_now is not None and imb_now > FT_IMB_MAX:
                return False, f"imb={imb_now:.2f} > FT_IMB_MAX={FT_IMB_MAX} (book sesgado peligrosamente)"

        # 8. NUEVO 2026-06-14: filtro de VELOCIDAD en contra (detecta reversión tardía).
        # El loss 1781474400 compró UP cuando velocity_30s=-0.57 (BTC bajando) y
        # momentum_fading=True. Validado: trades con velocidad EN CONTRA del side
        # tuvieron 89% WR vs 100% a favor. Combinado con forming/momentum aísla losses.
        # Controlable con FT_BLOCK_VELOCITY_AGAINST (default 1).
        if FT_BLOCK_VELOCITY_AGAINST:
            try:
                vel30 = spot_tracker.velocity(30.0)
            except Exception:
                vel30 = None
            if vel30 is not None:
                side_is_up = signal == "TREND_UP"
                # velocidad significativa EN CONTRA del trade
                vel_against = (side_is_up and vel30 < -FT_VELOCITY_MIN) or \
                              (not side_is_up and vel30 > FT_VELOCITY_MIN)
                if vel_against:
                    return False, (f"velocity_30s={vel30:+.2f}$/s va EN CONTRA de "
                                   f"BUY {'UP' if side_is_up else 'DN'} (reversión tardía)")

        # 9. NUEVO 2026-06-26: filtro ATR alto + precio alto (volatilidad extrema
        # sin recompensa). A precio >= FT_ATR_PRICE_MIN el profit es <$2, y con ATR
        # alto el riesgo de reversión sube. Capturó el loss 1782441000 (DN@$0.96 ATR=127).
        if FT_ATR_MAX_AT_HIGH_PRICE > 0 and ask >= FT_ATR_PRICE_MIN:
            try:
                atr_now = compute_atr(14)
            except Exception:
                atr_now = None
            if atr_now is not None and atr_now >= FT_ATR_MAX_AT_HIGH_PRICE:
                return False, (f"ATR={atr_now:.0f} >= {FT_ATR_MAX_AT_HIGH_PRICE} a precio "
                               f"${ask:.2f} (volatilidad extrema sin recompensa)")

        return True, "all checks passed"
    
    # Si fast-track está activo y la señal pasa los filtros, COMPRAR directo (sin esperar Round 2)
    if USE_FAST_TRACK and is_trend_follow:
        ft_approved, ft_reason = fast_track_check()
        if ft_approved:
            print(f"  ⚡ FAST-TRACK aprobado: {label}=${ask:.3f} — bypassing multi-round, comprando")
            _log_eval("FAST_TRACK_BUY")
            # Saltarse multi-round: limpiar buffer y proceder a comprar
            S.confirm_cl_price = None
            # No hacer return — continuar al flujo de BUY
        else:
            # Fast-track no aprueba — registrar el rechazo (con la razón) para análisis
            _log_eval(f"FAST_TRACK_REJECT: {ft_reason}")
            # caer al multi-round normal
    
    # Aplicar multi-round solo si fast-track NO aprobó (o no está activo)
    if USE_MULTI_ROUND_CONFIRM and is_trend_follow:
        # Saltar multi-round si fast-track ya aprobó (variable local)
        ft_approved_now, _ = fast_track_check() if USE_FAST_TRACK else (False, None)
        if ft_approved_now:
            # Fast-track tomará el control, no aplicar multi-round
            pass
        else:
            try:
                cl_now_price = chainlink_feed.price()  # precio Chainlink ACTUAL (cambia en cada round)
                cl_now_delta = abs(chainlink_feed.cl_delta_usd() or 0)
            except Exception:
                cl_now_price = None
                cl_now_delta = 0
            
            # Calcular tiempo restante en la ventana (S.end_time es datetime, no timestamp UNIX)
            try:
                time_left = (S.end_time - now_utc()).total_seconds() if S.end_time else 999
            except Exception:
                time_left = 999
            
            # Reset si cambió mercado o señal o no hay precio CL
            if S.confirm_slug != S.slug or S.confirm_signal != signal or cl_now_price is None:
                S.confirm_cl_price = None
                S.confirm_cl_delta = None
                S.confirm_side_price = None
                S.confirm_time_left = None
                S.confirm_slug = S.slug
                S.confirm_signal = signal
            
            if S.confirm_cl_price is None:
                # PRIMERA LECTURA — guardar y esperar nuevo round CL
                S.confirm_cl_price = cl_now_price
                S.confirm_cl_delta = cl_now_delta
                S.confirm_side_price = ask
                S.confirm_time_left = time_left
                print(f"  ⏸️  ROUND 1 capturado: CL=${cl_now_price:,.2f} Δ=${cl_now_delta:.0f} "
                      f"{label}=${ask:.3f} time_left={time_left:.0f}s — esperando nuevo round Chainlink")
                _log_eval("R1_CAPTURED")
                return
            
            # Verificar si Chainlink hizo nuevo round (cl_price cambió)
            if abs(cl_now_price - S.confirm_cl_price) < 0.01:
                # Mismo round — esperar
                return  # silencioso, no spam
            
            # NUEVO ROUND DETECTADO — validar consistencia
            cl_growth = cl_now_delta - S.confirm_cl_delta
            price_growth = ask - S.confirm_side_price
            
            # Validar tiempo restante suficiente
            if time_left < MIN_TIME_LEFT_SEC:
                print(f"  🚫 ROUND 2: time_left={time_left:.0f}s < {MIN_TIME_LEFT_SEC:.0f}s mínimo — "
                      f"no hay tiempo suficiente para cierre")
                S.confirm_cl_price = None  # reset
                return
            
            # Validar que CL creció
            if cl_growth < CL_GROWTH_MIN:
                print(f"  🚫 ROUND 2: CL Δ no creció lo suficiente "
                      f"(${S.confirm_cl_delta:.0f}→${cl_now_delta:.0f}, "
                      f"crecimiento ${cl_growth:+.0f} < ${CL_GROWTH_MIN:.0f} mínimo) — señal débil")
                _log_eval(f"MULTI_ROUND_ABORT: CL débil ({cl_growth:+.0f})")
                S.confirm_cl_price = None  # reset
                return
            
            # Validar que precio token acompañó (subió proporcionalmente)
            if price_growth < PRICE_GROWTH_MIN:
                print(f"  🚫 ROUND 2: precio {label} no subió proporcionalmente "
                      f"(${S.confirm_side_price:.3f}→${ask:.3f}, "
                      f"crecimiento ${price_growth:+.3f} < ${PRICE_GROWTH_MIN:.3f}) — DIVERGENCIA")
                _log_eval(f"MULTI_ROUND_ABORT: divergencia ({price_growth:+.3f})")
                S.confirm_cl_price = None  # reset
                return
            
            # MR_PRICE_MIN filter (2026-06-02):
            # Multi-Round solo es rentable a precios MUY ALTOS (>=$0.99 con bet $176).
            # En zona 0.85-0.97, Fast-Track captura mejor con sus filtros propios.
            # Esto evita que Multi-Round entre en precios donde casi no hay margen.
            if MR_PRICE_MIN > 0 and ask < MR_PRICE_MIN:
                print(f"  🚫 ROUND 2: precio {label}=${ask:.3f} < MR_PRICE_MIN=${MR_PRICE_MIN:.3f} — "
                      f"zona reservada para Fast-Track (Multi-Round no rentable aquí)")
                _log_eval(f"MULTI_ROUND_ABORT: price<MR_MIN (${ask:.3f})")
                S.confirm_cl_price = None  # reset
                return
            
            # ¡PASÓ TODOS LOS CHECKS!
            print(f"  ✓ ROUND 2 OK: CL Δ ${S.confirm_cl_delta:.0f}→${cl_now_delta:.0f} (+${cl_growth:.0f}) | "
                  f"{label} ${S.confirm_side_price:.3f}→${ask:.3f} (+${price_growth:.3f}) | "
                  f"time_left={time_left:.0f}s — consistencia validada")
            _log_eval("MULTI_ROUND_BUY")
            S.confirm_cl_price = None  # reset para próxima señal
    
    # Liquidez: para TF verificamos el ask side específicamente
    # (vamos a comprar — necesitamos liquidez donde queremos llenar)
    liq_side = "ask" if is_trend_follow else "both"
    liq_ok, liq_reason = book_liq_ok(token_id, check_side=liq_side)
    if not liq_ok:
        print(f"🚫 LIQ_BLOCK {label}: {liq_reason}")
        return

    spread = ask - bid
    if spread > MAX_SPREAD:
        return

    # v5.0: Different price ranges for TF vs MR
    if is_trend_follow:
        # Trend follow: buy winning-direction token (more expensive: 0.50-0.75)
        if ask > TF_MAX_ENTRY_PRICE:
            imb = binance_depth.imbalance()
            up_b, up_a = best_bid_ask(S.tokens[0])
            dn_b, dn_a = best_bid_ask(S.tokens[1])
            cycle_log.record_rejection(signal, f"TF {label} ask={ask:.2f} > {TF_MAX_ENTRY_PRICE:.2f}",
                                       spot_tracker.latest(), spot_tracker.change_since_window_start(),
                                       imb, up_b, up_a, dn_b, dn_a)
            return
        if ask < TF_MIN_ENTRY_PRICE:
            # Token is suspiciously cheap for trend follow — CL says this direction but market disagrees
            imb = binance_depth.imbalance()
            up_b, up_a = best_bid_ask(S.tokens[0])
            dn_b, dn_a = best_bid_ask(S.tokens[1])
            cycle_log.record_rejection(signal, f"TF {label} ask={ask:.2f} < {TF_MIN_ENTRY_PRICE:.2f} — market disagrees",
                                       spot_tracker.latest(), spot_tracker.change_since_window_start(),
                                       imb, up_b, up_a, dn_b, dn_a)
            # Registrar observación si el token está en zona "barata" interesante
            if ask <= CHEAP_TOKEN_THRESH:
                cl_dir_obs, cl_delta_obs, cl_cnt_obs = chainlink_feed.cl_direction()
                log_cheap_token_observation(
                    side         = label,
                    token_price  = ask,
                    cl_dir       = cl_dir_obs or "",
                    cl_delta     = cl_delta_obs,
                    cl_count     = cl_cnt_obs,
                    reason_blocked = f"TF_MIN_ENTRY ask={ask:.2f} < {TF_MIN_ENTRY_PRICE:.2f}"
                )
            return
    elif is_peak_reversion:
        # Peak reversion: buy the CHEAP token (opposite side of the move)
        if ask > PR_MAX_ENTRY_PRICE:
            imb = binance_depth.imbalance()
            up_b, up_a = best_bid_ask(S.tokens[0])
            dn_b, dn_a = best_bid_ask(S.tokens[1])
            cycle_log.record_rejection(signal, f"PR {label} ask={ask:.2f} > {PR_MAX_ENTRY_PRICE:.2f} (not cheap enough)",
                                       spot_tracker.latest(), spot_tracker.change_since_window_start(),
                                       imb, up_b, up_a, dn_b, dn_a)
            return
        if ask < PR_MIN_ENTRY_PRICE:
            imb = binance_depth.imbalance()
            up_b, up_a = best_bid_ask(S.tokens[0])
            dn_b, dn_a = best_bid_ask(S.tokens[1])
            cycle_log.record_rejection(signal, f"PR {label} ask={ask:.2f} < {PR_MIN_ENTRY_PRICE:.2f} (near zero, skip)",
                                       spot_tracker.latest(), spot_tracker.change_since_window_start(),
                                       imb, up_b, up_a, dn_b, dn_a)
            return
    else:
        # Legacy MR: buy cheap token (0.08-0.20)
        if ask > MAX_ENTRY_PRICE:
            imb = binance_depth.imbalance()
            up_b, up_a = best_bid_ask(S.tokens[0])
            dn_b, dn_a = best_bid_ask(S.tokens[1])
            cycle_log.record_rejection(signal, f"{label} ask={ask:.2f} > {MAX_ENTRY_PRICE:.2f}",
                                       spot_tracker.latest(), spot_tracker.change_since_window_start(),
                                       imb, up_b, up_a, dn_b, dn_a)
            return
        if ask < MIN_ENTRY_PRICE:
            return

    # Book score check (required for MR, informational for TF)
    depth_dir = "UP" if label == "UP" else "DN"
    has_support, support_reason = binance_depth.has_wall_support(depth_dir)
    if not has_support and not is_trend_follow:
        # MR requires wall support. TF does not — Chainlink is our truth source.
        imb = binance_depth.imbalance()
        up_b, up_a = best_bid_ask(S.tokens[0])
        dn_b, dn_a = best_bid_ask(S.tokens[1])
        cycle_log.record_rejection(signal, f"no wall support: {support_reason}",
                                   spot_tracker.latest(), spot_tracker.change_since_window_start(),
                                   imb, up_b, up_a, dn_b, dn_a)
        return

    maybe_update_balance()
    _bal = S.last_known_balance if S.last_known_balance is not None else BALANCE_FALLBACK_USDC
    if _bal < MIN_BALANCE_TO_TRADE:
        log_exec_status(S.slug, signal, "BALANCE_LOW",
                        f"balance ${_bal:.2f} < min ${MIN_BALANCE_TO_TRADE}")
        return

    # ── Espera de ciclos tras pérdida ────────────────────────────────────
    # Pérdida → esperar 3 ciclos → entrar con BASE NORMAL (sin martingale)
    if PROGRESSIVE_SIZING and S.cycles_to_wait > 0:
        print(f"⏸️ Esperando {S.cycles_to_wait} ciclo(s) más antes de entrar "
              f"(pérdidas={S.consecutive_losses})")
        log_exec_status(S.slug, signal, "WAIT_AFTER_LOSS",
                        f"esperando {S.cycles_to_wait} ciclos (losses={S.consecutive_losses})")
        return

    # ── Bloquear si hay resolución pendiente ─────────────────────────────
    if S._pending_resolution and S.consecutive_losses > 0:
        print(f"⏸️ PENDING_RESOLUTION — no entrando hasta confirmar resultado anterior "
              f"(balance=${S.last_known_balance:.2f}, ref=${S._pending_resolution_bal:.2f})")
        log_exec_status(S.slug, signal, "PENDING_RESOLUTION",
                        f"balance=${S.last_known_balance:.2f} ref=${S._pending_resolution_bal:.2f}")
        return

    if FULL_BALANCE_MODE:
        # Saldo total hasta el tope fijo: min(balance × FULL_BAL_PCT, BET_HARD_CAP)
        desired_usdc = min((_bal or 0.0) * FULL_BAL_PCT, BET_HARD_CAP)
        desired_usdc = max(MIN_TRADE_USDC, desired_usdc)
    elif PROGRESSIVE_SIZING:
        # Siempre base dinámica normal — sin multiplicador por pérdidas anteriores
        dyn_base     = get_dynamic_base(_bal or BALANCE_FALLBACK_USDC)
        desired_usdc = dyn_base
    else:
        desired_usdc = max(MIN_TRADE_USDC, _bal * USE_BALANCE_PCT)

    # ── Cap dinámico: 35% del balance actual ─────────────────────────────
    # En FULL_BALANCE_MODE el tope es el saldo completo (el límite real lo pone
    # BET_HARD_CAP arriba), así que no se recorta al MAX_TRADE_BAL_PCT.
    _bal_pct_cap = 1.0 if FULL_BALANCE_MODE else MAX_TRADE_BAL_PCT
    dyn_max = (_bal or BALANCE_FALLBACK_USDC) * _bal_pct_cap
    dyn_max = max(MIN_TRADE_USDC, dyn_max)

    entry_price = clamp_price(float(ask), S.tick, 0.01, 0.99)

    # ── Confidence-based sizing ───────────────────────────────────────────
    conf_pct, conf_nivel, conf_mult = compute_confidence(signal, reason)

    # Escalar por confianza si está habilitado
    if CONF_SIZING_ENABLED:
        # El bloqueo por confianza 0 (filtro de calidad) SIEMPRE aplica,
        # incluso en FULL_BALANCE_MODE. Lo que se omite en modo saldo total
        # es el recorte de tamaño por confianza<1 (queremos usar el saldo).
        if conf_mult == 0.0:
            print(f"🚫 CONFIANZA {conf_nivel} {conf_pct*100:.0f}% — señal bloqueada (solo MEDIUM/HIGH/VERY HIGH)")
            return  # no entrar
        if not FULL_BALANCE_MODE:
            desired_usdc = desired_usdc * conf_mult
            desired_usdc = max(MIN_TRADE_USDC, min(dyn_max, desired_usdc))
        conf_bar = "█" * int(conf_pct * 10) + "░" * (10 - int(conf_pct * 10))
        print(f"📊 CONFIANZA: {conf_nivel} {conf_pct*100:.0f}% [{conf_bar}] × {conf_mult:.3f} → ${desired_usdc:.2f}")

    # ── Risk multiplier por book_score (liquidez del order book) ──────────
    if is_trend_follow:
        b_data     = S.book.get(token_id, {})
        book_score = safe_float(b_data.get("bid_top3"), 0) + safe_float(b_data.get("ask_top3"), 0)
        BOOK_RISK_LOW   = float(os.getenv("BOOK_RISK_LOW_THRESH",  "25"))
        BOOK_RISK_HIGH  = float(os.getenv("BOOK_RISK_HIGH_THRESH", "55"))
        BOOK_RISK_LOW_M = float(os.getenv("BOOK_RISK_LOW_MULT",    "0.75"))
        BOOK_RISK_HIGH_M= float(os.getenv("BOOK_RISK_HIGH_MULT",   "1.15"))

        if book_score < BOOK_RISK_LOW:
            book_risk = BOOK_RISK_LOW_M
        elif book_score > BOOK_RISK_HIGH:
            book_risk = BOOK_RISK_HIGH_M
        else:
            book_risk = 1.0

        if book_risk != 1.0 and not FULL_BALANCE_MODE:
            old_usdc = desired_usdc
            desired_usdc = max(MIN_TRADE_USDC, min(dyn_max, desired_usdc * book_risk))
            print(f"📖 BOOK_RISK: score={book_score:.0f} → {book_risk:.2f}× "
                  f"(${old_usdc:.2f}→${desired_usdc:.2f})")

    cap_usdc = desired_usdc
    if _bal is not None:
        cap_usdc = min(cap_usdc, max(0.0, _bal))
    allow = S.last_known_allowance
    if allow is not None:
        cap_usdc = min(cap_usdc, max(0.0, allow))
    cap_usdc = max(0.0, min(dyn_max, cap_usdc))
    if cap_usdc < MIN_TRADE_USDC:
        return

    # ----------------------------------------------------------------
    # FIX BUY-RETRY ANTI-CHASE (2026-04-26)
    # Pre-validar precio actual del orderbook antes de enviar BUY.
    # Si el ask DERIVÓ vs el precio que decidimos (entry_price), abortar.
    # Esto previene el caso del 0.28: bot decidió comprar a 0.95
    # pero entre intentos el precio bajó a 0.28 — NO comprar a precio
    # que cambió tanto, porque las condiciones de mercado son distintas.
    # ----------------------------------------------------------------
    MAX_BUY_PRICE_DRIFT = float(os.getenv("MAX_BUY_PRICE_DRIFT", "0.05"))
    MAX_BUY_PRICE_DRIFT_FAVORABLE = float(os.getenv("MAX_BUY_PRICE_DRIFT_FAVORABLE", "0.25"))
    MAX_BUY_PRICE_HARDLIMIT = float(os.getenv("MAX_BUY_PRICE_HARDLIMIT", "0.99"))
    try:
        live_book = client.get_order_book(token_id)
        # v2 SDK devuelve dict, no objeto. Compatible con ambos formatos:
        asks_raw = live_book.get('asks') if isinstance(live_book, dict) else getattr(live_book, 'asks', None)
        if asks_raw:
            def _ask_price(a):
                if isinstance(a, dict): return float(a.get('price', 0))
                return float(getattr(a, 'price', 0))
            asks_sorted = sorted(asks_raw, key=_ask_price)
            live_ask = _ask_price(asks_sorted[0])
            drift = live_ask - entry_price
            abs_drift = abs(drift)
            
            # ANTI-DRIFT INTELIGENTE (2026-05-04):
            # El drift puede ser FAVORABLE (señal confirmada) o ADVERSO (señal invalidada).
            # FAVORABLE = precio del lado predicho SUBIÓ → mercado confirma nuestra dirección.
            # ADVERSO = precio del lado predicho BAJÓ → mercado deja de creer en ese lado.
            # 
            # Cuando bot decide BUY UP a $X y luego ve UP a $X+drift (subió):
            #   = más gente compró UP → señal confirmada → comprar (aunque más caro)
            # Cuando bot decide BUY UP a $X y luego ve UP a $X-drift (bajó):
            #   = mercado revendió UP → señal invalidada → ABORTAR
            # 
            # El "drift" es del precio del LADO QUE QUEREMOS COMPRAR
            
            is_favorable = drift > 0  # precio del lado subió = nuestro lado más popular
            
            if abs_drift > MAX_BUY_PRICE_DRIFT_FAVORABLE:
                # Drift muy grande: sospechoso (posible split de whale o manipulación)
                print(f"  🚫 SKIP BUY: drift extremo ${entry_price:.3f}→${live_ask:.3f} "
                      f"(drift ${abs_drift:.3f} > ${MAX_BUY_PRICE_DRIFT_FAVORABLE} hardlimit) — sospechoso")
                S.last_buy_fail_ts = time.time()
                return
            
            if not is_favorable and abs_drift > MAX_BUY_PRICE_DRIFT:
                # Drift adverso: precio del lado predicho bajó → señal se está invalidando
                print(f"  🚫 SKIP BUY: drift ADVERSO ${entry_price:.3f}→${live_ask:.3f} "
                      f"(drift ${abs_drift:.3f} > ${MAX_BUY_PRICE_DRIFT}) — señal invalidada")
                S.last_buy_fail_ts = time.time()
                return
            
            if live_ask > MAX_BUY_PRICE_HARDLIMIT:
                # Precio absoluto excede el límite máximo (por ejemplo $0.97+)
                print(f"  🚫 SKIP BUY: precio absoluto ${live_ask:.3f} > hardlimit ${MAX_BUY_PRICE_HARDLIMIT:.3f}")
                S.last_buy_fail_ts = time.time()
                return
            
            if is_favorable and abs_drift > MAX_BUY_PRICE_DRIFT:
                # Drift favorable significativo: la señal se confirmó por el mercado
                print(f"  ✓ DRIFT FAVORABLE: ${entry_price:.3f}→${live_ask:.3f} "
                      f"(drift ${abs_drift:.3f}, señal confirmada) — comprando al precio actual")
            
            # Actualizar entry_price al precio actual del libro
            entry_price = live_ask
    except Exception as e:
        print(f"  ⚠️ pre-buy book check failed: {e} (continuando)")

    ok, resp = post_market_order(client, token_id, "BUY", cap_usdc)
    if ok:
        S.orders_sent += 1
        S.last_order_ts = now
        est_size = float(cap_usdc / entry_price)
        if isinstance(resp, dict):
            fill_size = safe_float(resp.get("size") or resp.get("fillSize") or resp.get("matched_size"), None)
            fill_price = safe_float(resp.get("price") or resp.get("avgPrice") or resp.get("avg_price"), None)
            if fill_size and fill_size > 0:
                est_size = fill_size
            if fill_price and fill_price > 0:
                entry_price = fill_price

        S.position_token = token_id
        S.position_label = label
        S.position_size = est_size
        S.entry_price = float(entry_price)
        S.entry_ts = now
        S.peak_price = float(entry_price)
        S.trail_active = False
        S.sell_fail_count = 0
        S.last_sell_fail_ts = 0.0
        S.entry_win_chg = spot_tracker.change_since_window_start() or 0.0
        S.entry_cl_delta = chainlink_feed.cl_delta_usd()  # v5.0: CL delta at entry
        S.is_trend_follow = is_trend_follow  # v5.0
        S.is_peak_reversion = is_peak_reversion  # v5.2
        # v5.9: mark if this entry was triggered during a PTB shift window
        ptb_shift_age = time.time() - S.ptb_shift_ts
        S.is_ptb_shift_entry = (PTB_SHIFT_ENABLED
                                and ptb_shift_age < PTB_SHIFT_WINDOW_SEC
                                and S.ptb_shift_delta >= PTB_SHIFT_MIN_DIFF)

        # v5.2: record PR-specific state
        if is_peak_reversion:
            spot_now = spot_tracker.latest() or 0
            spot_ptb = spot_tracker.window_start_price or spot_now
            S.pr_entry_divergence_usd = spot_now - spot_ptb
            S.pr_spot_ptb             = spot_ptb
            S.pr_peak_divergence_usd  = abs(spot_tracker.peak_move_from_window()) * (spot_ptb or 97000)
            S.pr_peak_trail           = float(entry_price)
            S.pr_trail_active         = False

        btc_at_entry = spot_tracker.latest()
        btc_str = f"${btc_at_entry:,.0f}" if btc_at_entry else "N/A"
        cl_delta = chainlink_feed.cl_delta_usd()
        cl_str = f"CL Δ=${cl_delta:+.0f}" if cl_delta is not None else ""
        mode = "TF" if is_trend_follow else ("PR" if is_peak_reversion else "MR")
        if is_trend_follow:
            msg = (f"🚀 TF BUY {label} | px={entry_price:.2f} | "
                   f"${cap_usdc:.2f} | {cl_str} | {ASSET.upper()}={btc_str} | {support_reason} | {S.slug}")
        elif is_peak_reversion:
            tp_target = entry_price * (1 + PR_TP_PCT)
            msg = (f"🔄 PR BUY {label} (cheap) | px={entry_price:.2f} | "
                   f"TP@{tp_target:.2f} (+{PR_TP_PCT*100:.0f}%) | "
                   f"${cap_usdc:.2f} | peak_div=${S.pr_peak_divergence_usd:.0f} "
                   f"entry_div=${S.pr_entry_divergence_usd:+.0f} | {ASSET.upper()}={btc_str} | {S.slug}")
        else:
            tp_target = entry_price * (1 + TP_PCT)
            msg = (f"🔄 MR BUY {label} | px={entry_price:.2f} | TP@{tp_target:.2f} (+{TP_PCT*100:.0f}%) | "
                   f"${cap_usdc:.2f} | {ASSET.upper()}={btc_str} | {support_reason} | {S.slug}")
        print(msg)
        tg_send(msg)
        cycle_log.record_buy(f"{mode}_{label}", entry_price, cap_usdc, btc_at_entry, S.slug or "")
        log_trade("BUY", label, entry_price, est_size, cap_usdc, f"{mode}_{signal}")

        # Persistir posición en disco — permite recuperarla si el bot se reinicia
        save_position_state()

        # Log estadístico — captura todas las señales activas para análisis de probabilidad
        elapsed_now, left_now = window_timing()
        log_signal_entry(
            signal      = signal,
            side        = label,
            entry_price = entry_price,
            elapsed     = elapsed_now or 0,
            left        = left_now or 0,
        )
    else:
        # FIX BUY-RETRY ANTI-CHASE (2026-04-26)
        # Registrar el timestamp del fail para activar BUY_FAIL_COOLDOWN_SEC
        # y NO martillar la API cuando hay liquidez seca.
        S.last_buy_fail_ts = time.time()
        print(f"❌ BUY FAIL: {resp}")


# ================================================================
#  SMART EXIT LOGIC
# ================================================================
def _trend_confirms_position() -> Tuple[bool, str]:
    """
    Check if the current data confirms our position is winning.

    FIX v5.1: In TF mode, use Chainlink delta (not Binance) as confirmation
    because Polymarket resolves by Chainlink, not Binance spot price.
    Binance-based confirmation is kept for legacy MR mode only.
    """
    if S.position_label is None:
        return False, "no position"

    # --- v5.0 TF mode: use Chainlink delta as ground truth ---
    if getattr(S, 'is_trend_follow', False):
        cl_delta = chainlink_feed.cl_delta_usd()
        if cl_delta is None:
            return False, "no CL data"
        if S.position_label == "UP" and cl_delta >= 0:
            return True, f"CL_CONFIRMS_UP: Δ=${cl_delta:+.0f} (above price_to_beat)"
        elif S.position_label == "DN" and cl_delta < 0:
            return True, f"CL_CONFIRMS_DN: Δ=${cl_delta:+.0f} (below price_to_beat)"
        else:
            return False, f"CL_AGAINST_POS: {S.position_label} but CL Δ=${cl_delta:+.0f}"

    # --- Legacy MR mode: use Binance spot delta ---
    if S.entry_win_chg is None:
        return False, "no position"
    win_chg_now = spot_tracker.change_since_window_start()
    if win_chg_now is None:
        return False, "no data"

    delta_since_entry = win_chg_now - S.entry_win_chg

    if S.position_label == "UP":
        if delta_since_entry > 0.0001:
            return True, f"UP_CONFIRMED: BTC bounced {delta_since_entry:+.5f} since entry"
        return False, f"UP not confirmed: BTC delta={delta_since_entry:+.5f}"
    elif S.position_label == "DN":
        if delta_since_entry < -0.0001:
            return True, f"DN_CONFIRMED: BTC pulled back {delta_since_entry:+.5f} since entry"
        return False, f"DN not confirmed: BTC delta={delta_since_entry:+.5f}"
    return False, "unknown"


def _execute_sell(client, token_id, sell_price, position_size, reason, is_emergency=False):
    tick = S.tick or 0.01
    sell_token_amount = position_size

    actual_balance = query_conditional_token_balance(token_id)
    if actual_balance is not None:
        if actual_balance == 0:
            # v5.10: Token balance is 0 on-chain — position is a ghost (proxy issue).
            # Don't retry 15+ times; just log and let it resolve at expiry.
            print(f"⚠️ GHOST SELL: on-chain token balance=0 — cannot sell (proxy wallet issue)")
            print(f"   Position will resolve at expiry via Polymarket auto-redemption")
            tg_send(f"⚠️ Ghost sell: balance=0 for {reason} — holding to expiry")
            return False, sell_price, "ghost_position_balance_zero"
        if actual_balance < 0.01:
            return False, sell_price, "balance too small"
        if actual_balance < sell_token_amount:
            print(f"📊 Balance correction: est={sell_token_amount:.2f} actual={actual_balance:.2f}")
            sell_token_amount = actual_balance

    print(f"🔻 SELL ({reason}): {sell_token_amount:.2f} tokens @ ~{sell_price:.2f} (entry={S.entry_price:.2f})")

    ok, resp = post_market_order(client, token_id, "SELL", sell_token_amount)
    if ok:
        return True, sell_price, resp

    if SELL_USE_LIMIT_FALLBACK:
        # FIX 2: never sell at 0.01+tick (price floor) — always use a real bid-based price.
        # Old code set aggressive_price=0.01+tick for emergencies, which caused -95% losses.
        # Now: use current bid minus a small discount, with a minimum of entry_price*0.25
        # so we always recover at least 25% of the entry value before giving up.
        current_bid, _ = best_bid_ask(token_id)
        if current_bid and current_bid > 0.02:
            # Sell slightly below current bid to get filled quickly
            aggressive_price = max(
                S.entry_price * 0.25,            # floor: at least 25% of entry price
                current_bid - (2 * tick)          # 2 ticks below current bid
            )
        else:
            # No valid bid — use entry-based floor rather than 0.01
            aggressive_price = max(sell_price - SELL_LIMIT_DISCOUNT, S.entry_price * 0.30)
        aggressive_price = clamp_price(aggressive_price, tick, 0.01, 0.99)
        print(f"🔻 LIMIT SELL fallback @ {aggressive_price:.2f} (bid={current_bid})")
        ok2, resp2 = post_limit_sell(client, token_id, aggressive_price, sell_token_amount)
        if ok2:
            return True, aggressive_price, resp2

    return False, sell_price, resp


def _clear_position(sell_price, reason, btc_now):
    gross = (sell_price - S.entry_price) * S.position_size
    S.pnl_usdc += gross
    daily_rollover()
    maybe_disable_trading()

    # ── Pérdida → esperar 3 ciclos, luego base normal (sin martingale) ──
    CYCLES_TO_WAIT = int(os.getenv("MARTINGALE_WAIT_CYCLES", "3"))
    if PROGRESSIVE_SIZING:
        if gross >= 0:
            if S.consecutive_losses > 0:
                print(f"📈 WIN tras {S.consecutive_losses} pérdida(s) → reset, base normal")
            S.consecutive_losses = 0
            S.cycles_to_wait     = 0
            S.cycles_waited      = 0
            S._balance_at_last_loss = None
        else:
            S.consecutive_losses += 1
            S._balance_at_last_loss = S.last_known_balance
            S.cycles_to_wait    = CYCLES_TO_WAIT
            S.cycles_waited     = 0
            dyn_now = S.dynamic_base if S.dynamic_base > 0 else PROG_BASE_USDC
            print(f"📉 Pérdida #{S.consecutive_losses} → pausando {CYCLES_TO_WAIT} ciclos, "
                  f"luego base normal ${dyn_now:.2f}")
            tg_send(f"📉 Pérdida #{S.consecutive_losses} — pausando {CYCLES_TO_WAIT} ciclos\n"
                    f"próxima apuesta: base normal ${dyn_now:.2f}")

    btc_str = f"${btc_now:,.0f}" if btc_now else "N/A"
    msg = (f"{'✅' if gross >= 0 else '❌'} SELL {reason} | px={sell_price:.2f} | "
           f"entry={S.entry_price:.2f} | pnl={gross:+.2f} | day={S.pnl_usdc:+.2f} | "
           f"{ASSET.upper()}={btc_str} | {S.slug}")
    print(msg)
    tg_send(msg)
    cycle_log.record_sell(reason, sell_price, S.entry_price, S.position_size, gross, btc_now)
    log_trade("SELL", S.position_label, sell_price, S.position_size,
              sell_price * S.position_size, reason, pnl=gross)

    # Actualiza el registro estadístico con el resultado real
    hold_sec = time.time() - S.entry_ts
    update_signal_outcome(
        slug        = S.slug or "",
        side        = S.position_label or "",
        exit_reason = reason,
        exit_price  = sell_price,
        pnl         = gross,
        hold_sec    = hold_sec,
    )

    S.position_token = None
    S.position_label = None
    S.position_size = 0.0
    S.entry_price = 0.0
    S.entry_ts = 0.0
    S.peak_price = 0.0
    S.trail_active = False
    S.sell_fail_count = 0
    S.last_sell_fail_ts = 0.0
    S.entry_win_chg = 0.0
    S.entry_cl_delta = None  # v5.0
    # Borrar estado persistido — posición cerrada
    clear_position_state()
    S.is_trend_follow = False  # v5.0
    S.is_peak_reversion = False  # v5.2
    S.is_ptb_shift_entry = False  # v5.9
    S.pr_entry_divergence_usd = 0.0
    S.pr_peak_divergence_usd  = 0.0
    S.pr_spot_ptb             = 0.0
    S.pr_peak_trail           = 0.0
    S.pr_trail_active         = False


def maybe_exit_position(client):
    if not S.position_token:
        return

    now = time.time()
    hold_time = now - S.entry_ts
    if hold_time < SELL_GRACE_SEC:
        return

    if S.sell_fail_count > 0 and (now - S.last_sell_fail_ts) < SELL_RETRY_COOLDOWN_SEC:
        return
    if S.sell_fail_count >= SELL_MAX_RETRIES:
        if S.sell_fail_count == SELL_MAX_RETRIES:
            print(f"⚠️ SELL gave up after {SELL_MAX_RETRIES} retries — letting position expire")
            S.sell_fail_count += 1
        return

    token_id = S.position_token
    bid, ask = best_bid_ask(token_id)
    _, secs_left = window_timing()

    # === v5.2: PEAK REVERSION EXIT LOGIC ===
    if getattr(S, 'is_peak_reversion', False):
        if bid is None or ask is None:
            return
        mid = (bid + ask) / 2.0

        # Track peak token price since entry (for trailing stop)
        if mid > S.pr_peak_trail:
            S.pr_peak_trail = mid

        # ── Ganancia mínima requerida: 35% ───────────────────────────────
        # Si detectamos reversión, holdear hasta que el token suba 35%.
        # NO hay venta de emergencia — si la señal fue correcta, la reversión ocurrirá.
        profit_pct = (mid - S.entry_price) / S.entry_price if S.entry_price > 0 else 0
        PR_MIN_SELL_PROFIT_PCT = float(os.getenv("PR_MIN_SELL_PROFIT_PCT", "0.35"))
        can_sell = profit_pct >= PR_MIN_SELL_PROFIT_PCT

        # Activate trail after PR_TRAIL_ACTIVATE_PCT gain
        if profit_pct >= PR_TRAIL_ACTIVATE_PCT and not S.pr_trail_active:
            S.pr_trail_active = True
            print(f"📈 PR trail activated: +{profit_pct*100:.0f}% (mid={mid:.2f})")

        # TP1: token recuperó PR_TP_PCT desde entrada
        tp_target = S.entry_price * (1.0 + PR_TP_PCT)
        if can_sell and mid >= tp_target:
            sell_price = clamp_price(float(bid), S.tick or 0.01, 0.01, 0.99)
            ok, actual, resp = _execute_sell(client, token_id, sell_price,
                                             S.position_size, f"PR_TP_{PR_TP_PCT*100:.0f}%")
            if ok:
                _clear_position(actual, f"PR_TP_{PR_TP_PCT*100:.0f}% (entry={S.entry_price:.2f}→{mid:.2f})",
                                spot_tracker.latest())
            return

        # TP2: token cerca de $1
        if can_sell and mid >= PR_TP_DELTA:
            sell_price = clamp_price(float(bid), S.tick or 0.01, 0.01, 0.99)
            ok, actual, resp = _execute_sell(client, token_id, sell_price,
                                             S.position_size, "PR_NEAR_1")
            if ok:
                _clear_position(actual, f"PR_NEAR_1 (mid={mid:.2f})", spot_tracker.latest())
            return

        # Trail stop: el pico retrocedió PR_TRAIL_OFFSET (solo si ya ganamos 35%+)
        if can_sell and S.pr_trail_active:
            trail_stop_level = S.pr_peak_trail - PR_TRAIL_OFFSET
            if mid <= trail_stop_level and trail_stop_level > S.entry_price:
                sell_price = clamp_price(float(bid), S.tick or 0.01, 0.01, 0.99)
                ok, actual, resp = _execute_sell(client, token_id, sell_price,
                                                 S.position_size, "PR_TRAIL")
                if ok:
                    _clear_position(actual,
                                    f"PR_TRAIL (peak={S.pr_peak_trail:.2f} stop={trail_stop_level:.2f})",
                                    spot_tracker.latest())
                return

        # Spot reversion: spot revirtió PR_REVERT_PCT del movimiento (solo si ganamos 35%+)
        spot_now = spot_tracker.latest()
        spot_ptb = S.pr_spot_ptb
        if can_sell and spot_now and spot_ptb:
            entry_div = S.pr_entry_divergence_usd
            current_div_usd = spot_now - spot_ptb
            if abs(entry_div) > 0:
                revert_frac = 1.0 - (abs(current_div_usd) / abs(entry_div))
                if revert_frac >= PR_REVERT_PCT:
                    pr_min_hold = float(os.getenv("PR_SPOT_REVERT_MIN_HOLD_SEC", "120"))
                    held_sec = time.time() - S.entry_ts
                    if held_sec >= pr_min_hold:
                        sell_price = clamp_price(float(bid), S.tick or 0.01, 0.01, 0.99)
                        ok, actual, resp = _execute_sell(client, token_id, sell_price,
                                                         S.position_size, "PR_SPOT_REVERT")
                        if ok:
                            _clear_position(actual,
                                            f"PR_SPOT_REVERT {revert_frac*100:.0f}% "
                                            f"(entry_div=${entry_div:+.0f} now=${current_div_usd:+.0f})",
                                            spot_tracker.latest())
                        return

        # ── Sin bail de emergencia ────────────────────────────────────────
        # Si detectamos reversión, holdear. El mercado resuelve en máx 900s.
        # El peor caso es perder la inversión al expirar — igual que con bail.
        # Log de estado para diagnóstico
        secs_left = (S.end_time - datetime.now(timezone.utc)).total_seconds() if S.end_time else 0
        if int(time.time()) % 30 == 0:  # log cada 30s sin spam
            print(f"  ⏳ PR HOLD: +{profit_pct*100:.1f}% (need {PR_MIN_SELL_PROFIT_PCT*100:.0f}%) "
                  f"mid={mid:.2f} entry={S.entry_price:.2f} left={secs_left:.0f}s")

        return   # Holdear — esperar que llegue al 35%

    # === v5.0: TREND FOLLOW EXIT LOGIC ===
    if getattr(S, 'is_trend_follow', False):
        # TF exits (v5.8):
        # 1. TP: token >= TF_TP_PRICE (take profit)
        # 2. SL: token cayó TF_SL_PCT% desde entry (cortar pérdida parcial)
        # 3. CL_REVERSE: Chainlink revirtió fuertemente (señal fundamental rota)
        # 4. Default: hold to expiry

        if bid is not None and ask is not None:
            mid = (bid + ask) / 2.0
            if mid > S.peak_price:
                S.peak_price = mid

            # TP: token near $1 — take profit
            # v5.9: PTB shift entries use lower TP (0.85) — repricing is fast
            tp_target_price = PTB_SHIFT_TP_PRICE if getattr(S, 'is_ptb_shift_entry', False) else TF_TP_PRICE
            if mid >= tp_target_price:
                tp_label = "TF_TP_SHIFT" if getattr(S, 'is_ptb_shift_entry', False) else "TF_TP"
                sell_price = clamp_price(float(bid), S.tick or 0.01, 0.01, 0.99)
                ok, actual, resp = _execute_sell(client, token_id, sell_price, S.position_size, tp_label)
                if ok:
                    _clear_position(actual, f"{tp_label} (token={mid:.2f})", spot_tracker.latest())
                return

            # ── v5.8: TOKEN STOP-LOSS ─────────────────────────────────────
            # Problema: sin SL, cada pérdida es -100% ($18). Con TP en 0.92
            # y win avg ~$4.40, necesitas 80%+ win rate solo para break-even.
            #
            # Solución: cortar pérdidas cuando el token cae TF_SL_PCT desde
            # el entry price. Con SL=40%, entry 0.74 → stop en 0.44:
            #   - Pérdida: ~$7.35 en vez de ~$18
            #   - Break-even WR baja de 80% a ~63%
            #
            # Grace period: TF_SL_GRACE_SEC evita stops prematuros por
            # volatilidad inicial del token (fake-outs en primeros 90s).
            if TF_SL_PCT > 0:
                sl_level = S.entry_price * (1.0 - TF_SL_PCT)
                if mid <= sl_level and hold_time >= TF_SL_GRACE_SEC:
                    loss_pct = (mid - S.entry_price) / S.entry_price * 100 if S.entry_price > 0 else 0
                    sell_price = clamp_price(float(bid), S.tick or 0.01, 0.01, 0.99)
                    ok, actual, resp = _execute_sell(
                        client, token_id, sell_price, S.position_size, "TF_SL")
                    if ok:
                        _clear_position(
                            actual,
                            f"TF_SL (entry={S.entry_price:.2f} sl={sl_level:.2f} "
                            f"mid={mid:.2f} {loss_pct:+.0f}%)",
                            spot_tracker.latest())
                    return

        # Emergency: Chainlink reversed strongly
        cl_delta = chainlink_feed.cl_delta_usd()
        entry_delta = getattr(S, 'entry_cl_delta', None)
        if cl_delta is not None and entry_delta is not None:
            # Check if CL has moved AGAINST our position since entry
            if S.position_label == "UP" and cl_delta < -TF_EMERGENCY_CL_REVERSE_USD:
                # We hold UP but CL is now strongly below price_to_beat
                S.cl_reverse_count += 1
                S.last_cl_reverse_dir = "UP"
                if bid is not None:
                    sell_price = clamp_price(float(bid), S.tick or 0.01, 0.01, 0.99)
                    ok, actual, resp = _execute_sell(client, token_id, sell_price, S.position_size, "TF_CL_REVERSE")
                    if ok:
                        _clear_position(actual, f"TF_CL_REVERSE (CL Δ=${cl_delta:+.0f})", spot_tracker.latest())
                return
            elif S.position_label == "DN" and cl_delta > TF_EMERGENCY_CL_REVERSE_USD:
                # We hold DN but CL is now strongly above price_to_beat
                S.cl_reverse_count += 1
                S.last_cl_reverse_dir = "DN"
                if bid is not None:
                    sell_price = clamp_price(float(bid), S.tick or 0.01, 0.01, 0.99)
                    ok, actual, resp = _execute_sell(client, token_id, sell_price, S.position_size, "TF_CL_REVERSE")
                    if ok:
                        _clear_position(actual, f"TF_CL_REVERSE (CL Δ=${cl_delta:+.0f})", spot_tracker.latest())

        # Default for TF: hold to expiry (watchdog handles resolution)
        return

    # === LEGACY MR EXIT LOGIC (v4.x) ===
    # Smart hold-to-expiry check: if trend confirms, HOLD (don't sell)
    trend_confirms, trend_reason = _trend_confirms_position()

    # If trend confirms our position, hold to expiry — only emergency exit applies
    if trend_confirms:
        if secs_left is not None and secs_left <= SELL_EMERGENCY_SEC:
            return
        if bid is None and secs_left is not None and secs_left <= 5:
            return
        return

    # === TREND DOES NOT CONFIRM — try TP only, else hold to expiry ===
    if bid is None or ask is None:
        return

    mid = (bid + ask) / 2.0
    if mid > S.peak_price:
        S.peak_price = mid

    # TP based on percentage
    tp_target = S.entry_price * (1.0 + TP_PCT)
    hit_tp = (mid >= tp_target)

    # Trail activation
    profit_pct = (mid - S.entry_price) / S.entry_price if S.entry_price > 0 else 0
    if profit_pct >= TRAIL_ACTIVATE_PCT and not S.trail_active:
        S.trail_active = True
        print(f"📈 Trail activated: +{profit_pct*100:.0f}% (mid={mid:.2f})")

    trail_stop = False
    if S.trail_active:
        trail_level = S.peak_price - TRAIL_OFFSET
        if mid <= trail_level and trail_level > S.entry_price:
            trail_stop = True

    # ONLY exit on profitable conditions — no panic sells
    if not (hit_tp or trail_stop):
        return

    # Determine reason
    if hit_tp:
        reason = f"TP_{TP_PCT*100:.0f}%"
    elif trail_stop:
        reason = f"TRAIL (peak={S.peak_price:.2f})"
    else:
        reason = "EXIT"

    sell_price = clamp_price(float(bid), S.tick or 0.01, 0.01, 0.99)

    ok, actual_price, resp = _execute_sell(
        client, token_id, sell_price, S.position_size, reason, is_emergency=False)
    if ok:
        _clear_position(actual_price, reason, spot_tracker.latest())
    else:
        S.sell_fail_count += 1
        S.last_sell_fail_ts = time.time()
        if S.sell_fail_count <= 3 or S.sell_fail_count % 10 == 0:
            print(f"⚠️ SELL retry ({S.sell_fail_count}/{SELL_MAX_RETRIES}): {resp}")


# ================================================================
#  DIAGNOSTICS
# ================================================================
def print_diag(signal, reason):
    price_now = spot_tracker.latest()
    if price_now:
        cycle_log.record_btc_tick(price_now)
    cycle_log.record_signal(signal)

    if len(S.tokens) != 2:
        return
    up_id, dn_id = S.tokens
    elapsed, left = window_timing()
    bal = S.last_known_balance if S.last_known_balance is not None else BALANCE_FALLBACK_USDC
    up_bid, up_ask = best_bid_ask(up_id)
    dn_bid, dn_ask = best_bid_ask(dn_id)
    price_str = f"${price_now:,.2f}" if price_now else "N/A"
    win_chg = spot_tracker.change_since_window_start()
    win_str = f"{win_chg:+.5f}" if win_chg is not None else "N/A"
    abs_dollar = abs(win_chg * (price_now or 67000)) if win_chg is not None else 0
    bid_vol, ask_vol, depth_ratio = binance_depth.raw_imbalance()
    ema_imb = binance_depth.imbalance()

    mode = "STRADDLE" if USE_COPY_TRADING else ("WHALE" if USE_WHALE_ACCUM else ("TF" if USE_TREND_FOLLOW else ("PR" if USE_PEAK_REVERSION else "MR")))
    print(f"\n{'='*40} DIAG v5 ({mode}) {'='*40}")
    print(f"slug={S.slug} | elapsed={elapsed:.0f}s left={left:.0f}s | orders={S.orders_sent}/{MAX_ORDERS_PER_MARKET}")
    # v5.0: Show Chainlink delta from price-to-beat
    cl_delta = chainlink_feed.cl_delta_usd()
    cl_dir, _, cl_cnt = chainlink_feed.cl_direction()
    ptb = chainlink_feed.price_to_beat()
    cl_str = f" | CL Δ=${cl_delta:+.0f} ({cl_dir}x{cl_cnt})" if cl_delta is not None else ""
    ptb_str = f" | ptb=${ptb:,.0f}" if ptb else ""
    print(f"{ASSET.upper()}={price_str} | BN_chg={win_str} (${abs_dollar:.0f}){cl_str}{ptb_str}")
    print(f"DEPTH: bids={bid_vol:.1f} asks={ask_vol:.1f} | imb={ema_imb:.2f} (raw={depth_ratio:.2f})")
    if signal != "NONE" and CONF_SIZING_ENABLED:
        conf_pct, conf_nivel, conf_mult = compute_confidence(signal, reason)
        conf_bar = "█" * int(conf_pct * 10) + "░" * (10 - int(conf_pct * 10))
        if conf_mult == 0.0:
            print(f"signal={signal} | 🚫 BLOQUEADO — {conf_nivel} {conf_pct*100:.0f}% [{conf_bar}] (mín MEDIUM)")
            print(f"  ↳ {reason}")
        else:
            dyn = get_dynamic_base(S.last_known_balance or BALANCE_FALLBACK_USDC)
            print(f"signal={signal} | CONFIANZA {conf_nivel} {conf_pct*100:.0f}% [{conf_bar}] → ${dyn * conf_mult:.2f}")
            print(f"  ↳ {reason}")
    else:
        print(f"signal={signal} | {reason}")
    print(f"UP bid={up_bid} ask={up_ask} | DN bid={dn_bid} ask={dn_ask}")
    sizing_str = ""
    if PROGRESSIVE_SIZING:
        # Calcular base dinámica real (no depende de que haya habido compras)
        dyn_diag = get_dynamic_base(bal)
        if S.loss_pause_until > 0 and time.time() < S.loss_pause_until:
            remain = S.loss_pause_until - time.time()
            sizing_str = f" | ⏸️ PAUSED ({remain:.0f}s left)"
        elif S.consecutive_losses > 0:
            next_bet = dyn_diag * MARTINGALE_MULT
            sizing_str = f" | bet=${next_bet:.2f} (🔺martingale losses={S.consecutive_losses})"
        else:
            sizing_str = f" | bet=${dyn_diag:.2f} (streak=0)"
    print(f"balance≈{bal:.2f} | pnl_today={S.pnl_usdc:+.2f} | enabled={S.trading_enabled}{sizing_str}")

    if USE_CANDLE_ANALYSIS:
        print(f"  {candle_analyzer.diag_string()}")
        # MACD(3/15/3) Moon Dev — mostrar alineación con señal actual
        try:
            mv, ms, _ = candle_analyzer.macd(fast=3, slow=15, signal=3)
            if mv is not None and ms is not None:
                hist_v = mv - ms
                direction = "▲ UP" if hist_v > 0 else "▼ DN"
                bar = "█" * min(10, int(abs(hist_v) / 5)) if abs(hist_v) > 0 else "─"
                print(f"  📊 MACD(3/15/3): hist={hist_v:+.1f} {direction} [{bar}]")
        except Exception:
            pass
    if CHAINLINK_ENABLED:
        chainlink_feed.record_spread(price_now)
        print(f"  {chainlink_feed.diag_string(price_now)}")
    # v5.8: Sentiment diagnostics
    print(f"  [sent] {sentiment_tracker.diag_string()}")

    # v5.3: Peak Reversion live diagnostics — todos los indicadores
    if USE_PEAK_REVERSION:
        spot_ptb = spot_tracker.window_start_price
        spot_now = price_now
        if spot_ptb and spot_now:
            div_usd    = spot_now - spot_ptb
            peak_move  = spot_tracker.peak_move_from_window()
            peak_usd   = abs(peak_move) * (spot_ptb or 97000)
            rev_pct    = 0.0
            if abs(peak_move) > 0.0001:
                curr_frac = (spot_now - spot_ptb) / spot_ptb
                if peak_move > 0 and curr_frac < peak_move:
                    rev_pct = (peak_move - curr_frac) / peak_move
                elif peak_move < 0 and curr_frac > peak_move:
                    rev_pct = (curr_frac - peak_move) / abs(peak_move)
            cheap_side = "UP" if peak_move < 0 else ("DN" if peak_move > 0 else "-")
            # Technical scores
            tech_sc, tech_r = (candle_analyzer.reversal_score(cheap_side)
                               if cheap_side != "-" and candle_analyzer.candles
                               else (0, "no candles"))
            macd_v, macd_s, macd_r = candle_analyzer.macd()
            ema_c, ema_r = candle_analyzer.ema_cross()
            rsi_v, _     = candle_analyzer.rsi()
            vol_s, vol_r, _ = candle_analyzer.volume_surge()
            pat_sc, pat_r = (candle_analyzer.chart_patterns(cheap_side)
                             if cheap_side != "-" else (0, "-"))
            print(f"  🔄 PR: div=${div_usd:+.0f} peak=${peak_usd:.0f} "
                  f"rev={rev_pct*100:.1f}% cheap={cheap_side} "
                  f"tech={tech_sc}/12 TP=+{PR_TP_PCT*100:.0f}%")
            rsi_str   = f"RSI={rsi_v:.0f}" if rsi_v else "RSI=N/A"
            macd_str  = (f"MACD_hist={macd_v-macd_s:+.1f}" if macd_v and macd_s else "MACD=N/A")
            ema_str   = f"EMA={'X↑' if ema_c>0 else ('X↓' if ema_c<0 else 'flat')}"
            vol_str   = f"VOL={'SURGE' if vol_s else 'norm'}"
            pat_str   = f"PAT={pat_r[:25]}" if pat_sc > 0 else "PAT=none"
            mm_str    = mm_tracker.diag_str(S.tokens) if S.tokens else "MM=N/A"
            # Nuevos indicadores v5.6
            atr_val   = compute_atr()
            atr_str   = f"ATR=${atr_val:.0f}" if atr_val else "ATR=N/A"
            stoch_val = compute_stoch_rsi()
            stoch_str = f"StochRSI K={stoch_val[0]:.0f}/D={stoch_val[1]:.0f}" if stoch_val else "StochRSI=N/A"
            sess_n, sess_s = compute_market_session()
            flow_r, flow_d = trade_flow.flow(30)
            flow_str  = f"FLOW={flow_r:.2f}" if flow_r else "FLOW=N/A"
            eat_r, eat_dir, eat_desc = trade_flow.eat_rate(EAT_FLOW_WINDOW_SEC)
            eat_str = f"EAT={eat_r:+.2f}/s({eat_dir})" if eat_r != 0 else "EAT=0"
            print(f"       {rsi_str} | {macd_str} | {ema_str} | {vol_str} | {pat_str}")
            print(f"       {stoch_str} | {atr_str} | {flow_str} | {eat_str} | SES={sess_n}({sess_s:.0%})")
            print(f"       {mm_str}")

    if S.position_token:
        bid, ask = best_bid_ask(S.position_token)
        mid = ((bid or 0) + (ask or 0)) / 2
        unr = (mid - S.entry_price) * S.position_size if mid > 0 else 0
        pct = ((mid - S.entry_price) / S.entry_price * 100) if S.entry_price > 0 else 0
        tp_target = S.entry_price * (1 + TP_PCT)
        confirms, conf_reason = _trend_confirms_position()
        hold_mode = "HOLD_TO_EXPIRY" if confirms else "ACTIVE_EXIT"
        trail_str = f" TRAIL(peak={S.peak_price:.2f})" if S.trail_active else ""
        print(f"POS: {S.position_label} sz={S.position_size:.2f} entry={S.entry_price:.2f} "
              f"mid={mid:.2f} unr={unr:+.2f} ({pct:+.0f}%) TP@{tp_target:.2f} "
              f"hold={time.time()-S.entry_ts:.0f}s | {hold_mode}{trail_str}")
        print(f"  {conf_reason}")


# ================================================================
#  POLYMARKET WS LOOP
# ================================================================
def run_ws(client, market, prefetch_state: dict = None, reconnect: bool = False):
    if reconnect:
        # v5.9: Reconexión mid-cycle — NO reinicializar mercado ni pedir PTB
        print(f"🔄 Reconectando WS al mercado activo (sin re-init)...")
        # v5.18 FIX B: reset del cooldown post-BUY para forzar drift-sync inmediato
        # en el siguiente tick. Sin esto, tras reconexión el tracker podría tener
        # valores inflados de un BUY previo y disparar TP falso ("ghost").
        S.last_successful_buy_ts = 0.0
        S.large_drift_strikes = 0
        # Sync directo e inmediato del tracker con on-chain, si aplica
        try:
            if not DRY_RUN and len(S.tokens) == 2 and (S.straddle_shares_up > 0 or S.straddle_shares_dn > 0):
                up_id_f, dn_id_f = S.tokens
                real_up_f = query_conditional_token_balance(up_id_f)
                real_dn_f = query_conditional_token_balance(dn_id_f)
                if real_up_f is not None and real_dn_f is not None:
                    old_up, old_dn = S.straddle_shares_up, S.straddle_shares_dn
                    if S.straddle_shares_up > 0.01:
                        S.straddle_spent_up *= (real_up_f / S.straddle_shares_up) if real_up_f > 0 else 0
                    S.straddle_shares_up = max(0.0, real_up_f)
                    if S.straddle_shares_dn > 0.01:
                        S.straddle_spent_dn *= (real_dn_f / S.straddle_shares_dn) if real_dn_f > 0 else 0
                    S.straddle_shares_dn = max(0.0, real_dn_f)
                    if abs(old_up - real_up_f) > 0.5 or abs(old_dn - real_dn_f) > 0.5:
                        print(f"  🔄 Post-reconnect sync: UP {old_up:.1f}→{real_up_f:.1f}, DN {old_dn:.1f}→{real_dn_f:.1f}")
        except Exception as e:
            print(f"  ⚠️ Post-reconnect sync error: {e}")
    else:
        init_market(market)
    mode = "STRADDLE" if USE_COPY_TRADING else ("WHALE" if USE_WHALE_ACCUM else ("TF" if USE_TREND_FOLLOW else ("PR" if USE_PEAK_REVERSION else "MR")))
    print(f"\n🚀 Bot v5.0 — {mode} | {ASSET.upper()}")
    print(f"   Market: {market_title(market)}")
    print(f"   slug={S.slug} | ends={S.end_time} | tokens={len(S.tokens)} | tick={S.tick}")
    price_now = spot_tracker.latest()
    if price_now:
        print(f"   {ASSET.upper()} window start: ${price_now:,.2f}")

    stop_flag = {"stop": False}
    ws_holder = {"ws": None}

    def _check_resolution_onchain():
        """
        FIX v5.1: Determine win/loss using the CLOB API balance endpoint.

        The original approach (redeemPositions on-chain) does NOT work because
        winning tokens are held in Polymarket's proxy wallet, not the EOA.
        Only the Polymarket UI can trigger proxy redemption.

        New approach:
          1. Query CLOB /balance-allowance BEFORE and AFTER a short wait.
          2. If balance grew → Polymarket auto-redeemed → WON.
          3. If balance unchanged → LOST (or proxy not yet redeemed).
          4. Fallback: use Chainlink close snapshot vs PTB as ground truth.

        FIX 2026-06-04: el cross-check ahora usa S._cl_close_snapshot (precio
        Chainlink EXACTO al cierre) comparado con el PTB de apertura, en lugar
        de cl_delta_usd() que usa el precio ACTUAL (ya movido hacia el sgte ciclo).
        Esto corrige falsos LOSS en mercados que cierran muy cerca del open.
        """
        if not S.position_token:
            return None, 0.0

        # Helper: determinar si la posición ganó usando el snapshot de cierre
        def _won_by_close_snapshot():
            """Compara precio CL al cierre vs PTB de apertura. None si no hay datos."""
            close_px = getattr(S, '_cl_close_snapshot', None)
            ptb = chainlink_feed.price_to_beat()
            if close_px is None or ptb is None:
                return None
            # El mercado resuelve UP si close > ptb (apertura), DN si close < ptb
            market_went_up = close_px > ptb
            if S.position_label == "UP":
                return market_went_up
            else:  # DN
                return not market_went_up

        # --- Step 1: read CLOB balance before resolution propagates ---
        pre_balance = _query_clob_balance()

        # --- Notificar ANTES del sleep — si el bot muere durante los 75s, el mensaje ya llegó ---
        pos_label  = S.position_label or "?"
        pos_entry  = S.entry_price
        pos_size   = S.position_size
        btc_pre    = spot_tracker.latest() or 0
        btc_open_p = spot_tracker.window_start_price or 0
        tg_send(f"⏳ Mercado cerró con posición {pos_label} abierta | "
                f"entry={pos_entry:.2f} | Verificando resultado on-chain... "
                f"({ASSET.upper()} {btc_open_p:,.0f}→{btc_pre:,.0f})")

        # --- Step 2: wait for Polymarket to auto-redeem with MULTIPLE retries ---
        # FIX 2026-06-02: bug donde si auto-redeem tardaba >75s, el bot declaraba
        # falso LOSS aunque on-chain hubiera ganado. Ahora reintenta múltiples veces.
        REDEEM_MAX_WAIT_SEC = int(os.getenv("REDEEM_MAX_WAIT_SEC", "180"))  # hasta 3 min
        REDEEM_CHECK_INTERVAL = int(os.getenv("REDEEM_CHECK_INTERVAL", "30"))  # cada 30s
        
        print(f"⏳ Waiting for Polymarket auto-redemption (max {REDEEM_MAX_WAIT_SEC}s, check cada {REDEEM_CHECK_INTERVAL}s)...")
        
        post_balance = None
        payout = 0
        won = None
        
        elapsed_wait = 0
        while elapsed_wait < REDEEM_MAX_WAIT_SEC:
            # Sleep en chunks pequeños para responder al stop_flag
            sleep_chunk = min(REDEEM_CHECK_INTERVAL, REDEEM_MAX_WAIT_SEC - elapsed_wait)
            for _ in range(sleep_chunk):
                if stop_flag.get("stop"):
                    print("⚠️ Stop flag set — aborting resolution wait")
                    break
                time.sleep(1)
            elapsed_wait += sleep_chunk
            
            if stop_flag.get("stop"):
                break
            
            # Check balance ahora
            post_balance = _query_clob_balance()
            if pre_balance is not None and post_balance is not None:
                payout = post_balance - pre_balance
                # 2026-10-26: descontar cobros de TW/FLOW/CB del lado contrario en este mismo ciclo
                if payout > 0.10 + _side_opp_shares(S.slug, S.position_label):
                    print(f"✅ CLOB balance grew ${payout:+.2f} (después de {elapsed_wait}s) → WON (auto-redeemed)")
                    won = True
                    break
                else:
                    # Aún no creció — pero verificar si la posición DEBERÍA haber ganado
                    # (cross-check con snapshot de cierre antes de declarar LOST)
                    snapshot_won = _won_by_close_snapshot()
                    if snapshot_won is not None:
                        if snapshot_won:
                            # Snapshot dice que ganaste, pero balance no creció
                            # Esperar más antes de declarar LOST
                            close_px = getattr(S, '_cl_close_snapshot', 0)
                            ptb = chainlink_feed.price_to_beat() or 0
                            print(f"  ⏳ ({elapsed_wait}s) balance no creció pero CL close dice WIN "
                                  f"(close=${close_px:,.0f} vs ptb=${ptb:,.0f}) — esperando más...")
                            continue
                        else:
                            # Snapshot confirma loss, no esperar más
                            close_px = getattr(S, '_cl_close_snapshot', 0)
                            ptb = chainlink_feed.price_to_beat() or 0
                            print(f"  ({elapsed_wait}s) balance no creció + CL close confirma LOSS "
                                  f"(close=${close_px:,.0f} vs ptb=${ptb:,.0f})")
                            break
                    # Sin snapshot, esperar más por si acaso
                    print(f"  ⏳ ({elapsed_wait}s) balance no creció todavía — re-verificando...")
        
        # --- Step 3: decisión final ---
        if won is True:
            return True, payout
        
        if pre_balance is not None and post_balance is not None:
            payout = post_balance - pre_balance
            if payout > 0.10 + _side_opp_shares(S.slug, S.position_label):   # 2026-10-26 (ver arriba)
                print(f"✅ CLOB balance grew ${payout:+.2f} → WON (auto-redeemed by Polymarket)")
                return True, payout
            else:
                # Antes de declarar LOST, hacer cross-check FINAL con snapshot de cierre
                snapshot_won = _won_by_close_snapshot()
                if snapshot_won is True:
                    # Discrepancia: snapshot dice WIN pero balance no creció
                    # Posiblemente auto-redeem aún pendiente — NO declarar LOSS
                    est_payout = S.position_size * 1.0
                    close_px = getattr(S, '_cl_close_snapshot', 0)
                    ptb = chainlink_feed.price_to_beat() or 0
                    print(f"⚠️ DISCREPANCIA: balance no creció pero CL close confirma WIN "
                          f"(close=${close_px:,.0f} vs ptb=${ptb:,.0f}). Asumiendo WIN.")
                    print(f"   Si el balance no aparece después, revisar manualmente en Polymarket.")
                    return True, est_payout

                print(f"❌ CLOB balance unchanged (${payout:+.2f}) → LOST (confirmado)")
                cost = S.entry_price * S.position_size
                return False, -cost

        # --- Fallback: use Chainlink close snapshot if CLOB query failed ---
        print("⚠️ CLOB balance unavailable — using Chainlink close snapshot as fallback")
        snapshot_won = _won_by_close_snapshot()
        if snapshot_won is not None:
            if snapshot_won:
                est_payout = S.position_size * 1.0
                return True, est_payout
            else:
                cost = S.entry_price * S.position_size
                return False, -cost

        return None, 0.0

    def _query_clob_balance():
        """Query USDC balance via CLOB API (sees proxy wallet). Falls back to on-chain EOA."""
        # Try CLOB API first — sees the proxy wallet balance
        try:
            from py_clob_client_v2.clob_types import BalanceAllowanceParams, AssetType
            params = BalanceAllowanceParams(asset_type=AssetType.COLLATERAL)
            resp = client.get_balance_allowance(params)
            if isinstance(resp, dict) and "balance" in resp:
                raw = float(resp["balance"])
                bal = raw / 1e6 if raw >= 10_000 else raw  # FIX: was 1_000_000, misses values like 544312
                print(f"  💰 CLOB proxy balance: ${bal:.4f}")
                return bal
        except Exception as e:
            print(f"  ⚠️ CLOB balance query failed: {e}")

        # Fallback: on-chain EOA balanceOf (only sees EOA, not proxy)
        return _query_usdc_balance()

    def _query_usdc_balance():
        """Query actual USDC balance on-chain via raw eth_call (balanceOf)."""
        if not HAS_WEB3:
            return None
        try:
            w3 = _get_w3()
            if not w3:
                return None
            owner = Web3.to_checksum_address(FUNDER_ADDRESS or SIGNER_ADDRESS)
            # balanceOf(address) selector = 0x70a08231
            bal_data = w3.eth.call({
                'to': Web3.to_checksum_address(USDC_POLYGON),
                'data': '0x70a08231' + owner[2:].lower().zfill(64)
            })
            return int(bal_data.hex(), 16) / (10 ** USDC_DECIMALS)
        except Exception as e:
            print(f"⚠️ USDC balance query error: {e}")
            return None

    def watchdog_loop():
        while not stop_flag["stop"]:
            try:
                ws = ws_holder["ws"]
                if ws is not None and S.end_time is not None:
                    secs_left = (S.end_time - now_utc()).total_seconds()
                    if secs_left <= 10 and secs_left > 2:
                        # ── Pre-fetch del siguiente mercado ────────────────────────────
                        if prefetch_state is not None and not prefetch_state.get("next_market"):
                            next_epoch = int(S.end_time.timestamp()) if S.end_time else 0
                            next_slug  = compute_slug(next_epoch)
                            def _prefetch(slug, epoch):
                                try:
                                    m = gamma_get_market_by_slug(slug)
                                    if m and m.get("active") and not m.get("closed") and extract_token_ids(m):
                                        prefetch_state["next_market"] = m
                                        print(f"⚡ Pre-fetch: {slug} listo")
                                except Exception:
                                    pass
                            threading.Thread(target=_prefetch, args=(next_slug, next_epoch),
                                             daemon=True).start()

                    if secs_left <= 2 and secs_left > -5:
                        # ── Capturar PTB exacto con latestRoundData al cierre ─────────────
                        # Una sola llamada RPC — mucho más rápida que getRoundData en loop.
                        # El round más reciente en este momento ES el PTB del siguiente ciclo.
                        cl_at_close = None
                        try:
                            for rpc in CHAINLINK_RPCS:
                                try:
                                    resp = requests.post(rpc, json={
                                        "jsonrpc": "2.0", "method": "eth_call",
                                        "params": [{"to": CHAINLINK_CONTRACT,
                                                    "data": "0xfeaf968c"}, "latest"],
                                        "id": 1
                                    }, timeout=3)
                                    result = resp.json().get("result", "")
                                    if result and len(result) > 130:
                                        answer     = int(result[66:130], 16)
                                        updated_at = int(result[194:258], 16)
                                        price      = answer / 1e8
                                        if price > 1000:
                                            cl_at_close = price
                                            print(f"📌 PTB latestRound: ${price:,.2f} "
                                                  f"(updatedAt={updated_at} "
                                                  f"age={int(time.time()-updated_at)}s)")
                                            break
                                except Exception:
                                    continue
                        except Exception:
                            pass
                        # Fallback: precio cached del feed
                        if not cl_at_close:
                            cl_at_close = chainlink_feed.price()
                        # FIX 2026-06-04: guardar el precio Chainlink EXACTO al cierre
                        # para que _check_resolution_onchain lo compare con el PTB de
                        # ESTE ciclo (no el precio actual que ya se movió hacia el sgte).
                        # Esto arregla los falsos LOSS en mercados que cierran muy cerca
                        # del open (movimientos < 0.0011 donde el desfase invertía el signo).
                        if cl_at_close and cl_at_close > 1000:
                            S._cl_close_snapshot = cl_at_close
                        if cl_at_close and cl_at_close > 1000:
                            chainlink_feed._pending_ptb = (cl_at_close, time.time())
                            print(f"📌 PTB del siguiente ciclo: ${cl_at_close:,.2f}")
                        if S.position_token:
                            btc_now = spot_tracker.latest()
                            btc_open = spot_tracker.window_start_price

                            # DON'T estimate resolution from Binance.
                            # Instead, wait and check on-chain after market close.
                            print(f"⏳ Market closing with {S.position_label} position | "
                                  f"entry={S.entry_price:.2f} | size={S.position_size:.2f} | "
                                  f"{ASSET.upper()} open={btc_open:,.0f} close={btc_now:,.0f}")

                            # FIX 2026-06-26 (anti-freeze): la resolución on-chain
                            # puede esperar hasta REDEEM_MAX_WAIT_SEC (180s). Antes
                            # corría AQUÍ, dentro de on_message, BLOQUEANDO el WS y
                            # retrasando la conexión al siguiente mercado (el bot se
                            # "congelaba" tras comprar). Ahora corre en un HILO daemon
                            # separado: el WS se cierra de inmediato y el bot pasa al
                            # siguiente mercado mientras la resolución se completa aparte.
                            _snapshot = {
                                "token": S.position_token,
                                "label": S.position_label,
                                "entry_price": S.entry_price,
                                "position_size": S.position_size,
                                "slug": S.slug,
                                "btc_open": btc_open,
                                "btc_now": btc_now,
                            }

                            def _resolve_async(snap):
                                try:
                                    won, payout = _check_resolution_onchain()
                                    if won is True:
                                        result = f"🎯 WON (verified on-chain, payout=${payout:.2f})"
                                        print(result)
                                        tg_send(f"🎯 WON {snap['label']} | entry={snap['entry_price']:.2f} | "
                                                f"payout=${payout:.2f} | {ASSET.upper()} "
                                                f"{snap['btc_open']:,.0f}→{snap['btc_now']:,.0f}")
                                        _clear_position(1.0, "RESOLVED_WIN", snap['btc_now'])
                                    elif won is False:
                                        result = f"💀 LOST (verified on-chain, payout=${payout:.2f})"
                                        print(result)
                                        tg_send(f"💀 LOST {snap['label']} | entry={snap['entry_price']:.2f} | "
                                                f"-${snap['entry_price'] * snap['position_size']:.2f} | "
                                                f"{ASSET.upper()} {snap['btc_open']:,.0f}→{snap['btc_now']:,.0f}")
                                        _clear_position(0.0, "RESOLVED_LOSS", snap['btc_now'])
                                    else:
                                        print(f"⚠️ Cannot verify resolution on-chain — marking as UNKNOWN")
                                        if S.consecutive_losses > 0:
                                            S._pending_resolution = True
                                            S._pending_resolution_bal = S.last_known_balance or 0.0
                                            print(f"⏸️ PENDING_RESOLUTION: martingale bloqueado hasta confirmar "
                                                  f"(balance: ${S._pending_resolution_bal:.2f})")
                                            tg_send(f"⏸️ Posición sin confirmar — no entraré hasta ver el resultado\n"
                                                    f"Reclama el win si ganaste, luego el bot continúa solo.")
                                        _clear_position(0.0, "RESOLVED_UNKNOWN", snap['btc_now'])
                                    process_pending_claims()
                                except Exception as _e:
                                    print(f"⚠️ Error en resolución async: {_e}")

                            print(f"🔍 Resolución on-chain en background (no bloquea el siguiente mercado)...")
                            threading.Thread(target=_resolve_async, args=(_snapshot,),
                                             name="resolve", daemon=True).start()
                        print("⏭️ Market ended.")
                        bal = S.last_known_balance if S.last_known_balance is not None else BALANCE_FALLBACK_USDC
                        cycle_log.write_cycle_summary(bal)
                        try:
                            ws.close()
                        except Exception:
                            pass
                        return
                if ws is not None and S.ws_open_ts > 0:
                    silent = time.time() - S.last_ws_msg_ts
                    if (time.time() - S.ws_open_ts) > WS_OPEN_GRACE_SEC and silent > WS_SILENT_RECONNECT_SEC:
                        print(f"⚠️ WS silent {silent:.1f}s. Reconnecting...")
                        try:
                            ws.close()
                        except Exception:
                            pass
                        return
            except Exception:
                pass
            time.sleep(0.5)

    def ping_loop():
        while not stop_flag["stop"]:
            try:
                ws = ws_holder["ws"]
                if ws is not None:
                    ws.send("PING")
            except Exception:
                pass
            time.sleep(WS_PING_TEXT_EVERY_SEC)

    def on_open(ws):
        ws_holder["ws"] = ws
        S.ws_open_ts = time.time()
        S.last_ws_msg_ts = time.time()
        print("🟢 Polymarket WS connected — subscribing")
        sub = {"type": "market", "assets_ids": S.tokens}
        ws.send(json.dumps(sub))

    def _diag_tick():
        """2026-10-26: MISMO código que antes corría dentro de on_message (sin cambios),
        ahora en su propio hilo para no frenar la lectura del libro de Polymarket."""
        maybe_update_balance()
        now = time.time()
        if now - S.last_diag_ts >= DIAG_EVERY_SEC:
            # v5.9: Check for PTB shift mid-cycle
            check_mid_cycle_ptb()
            # Revisar comandos de Telegram (pausa/start)
            # DESACTIVADO 2026-10-26 (pedido del usuario): esta consulta esperaba hasta 2 s cada
            # 3 s y atrasaba el libro. Solo queda la consulta de Telegram del PTB (init_market).
            # tg_check_commands()

            signal, reason = "NONE", "no signal"

            if USE_WHALE_ACCUM:
                # Whale mode: skip normal signal flow, use phase-based accumulation
                cl_dir, cl_delta, _ = chainlink_feed.cl_direction()
                abs_d = abs(cl_delta) if cl_delta else 0
                age = chainlink_feed.on_chain_age()
                p1 = "✅" if S.whale_p1_done else "⏳"
                p2 = "✅" if S.whale_p2_done else "⏳"
                p3 = "✅" if S.whale_p3_done else "⏳"
                spent = S.whale_spent_up + S.whale_spent_dn
                signal = "WHALE"
                reason = (f"🐋 P1{p1} P2{p2} P3{p3} | CL {cl_dir or '?'} ${abs_d:+.0f} "
                         f"age={age:.0f}s | UP=${S.whale_spent_up:.2f} DN=${S.whale_spent_dn:.2f}")
                S.last_diag_ts = now
                print_diag(signal, reason)
                if not S.paused_by_telegram:
                    whale_accum_tick(client)
                else:
                    print("⏸️ En STAND-BY — esperando 'start' por Telegram")
            elif USE_COPY_TRADING:
                # Momentum straddle: CL direction + hedge
                total_spent = S.straddle_spent_up + S.straddle_spent_dn
                cl_dir, cl_delta, _ = chainlink_feed.cl_direction()
                abs_d = abs(cl_delta) if cl_delta else 0
                if cl_dir == "UP" and abs_d >= STRADDLE_MIN_CL:
                    mom_str = f"⬆️CL+${abs_d:.0f}"
                elif cl_dir == "DN" and abs_d >= STRADDLE_MIN_CL:
                    mom_str = f"⬇️CL-${abs_d:.0f}"
                else:
                    mom_str = f"⚖️CL${abs_d:.0f}"
                signal = "STRADDLE"
                reason = (f"📋 R{S.straddle_rounds} {mom_str} | "
                         f"UP=${S.straddle_spent_up:.1f} ({S.straddle_shares_up:.0f}sh) "
                         f"DN=${S.straddle_spent_dn:.1f} ({S.straddle_shares_dn:.0f}sh) | "
                         f"${total_spent:.0f}/{STRADDLE_MAX_BUDGET:.0f}")
                S.last_diag_ts = now
                print_diag(signal, reason)
                if not S.paused_by_telegram:
                    copy_trading_tick(client)
                else:
                    print("⏸️ En STAND-BY — esperando 'start' por Telegram")
            else:
                if USE_TREND_FOLLOW:
                    shadow_tick()   # SHADOW 2026-10-25: solo registra (shadow_log.jsonl), nunca compra
                    tw_tick(client)  # TW 2026-10-26: método de compra temprano independiente ($5 fijos)
                    side_methods_tick(client)  # FLOW y CB 2026-10-26: métodos independientes ($2 fijos)
                    signal, reason = pick_signal_trend_follow()

                if signal == "NONE" and USE_PEAK_REVERSION:
                    signal, reason = pick_signal_peak_reversion()

                if signal == "NONE" and USE_MEAN_REVERSION:
                    signal, reason = pick_signal()
                S.last_diag_ts = now
                print_diag(signal, reason)
                maybe_exit_position(client)

                # No entrar si está pausado por Telegram
                if S.paused_by_telegram:
                    print("⏸️ En STAND-BY — esperando 'start' por Telegram")
                else:
                    maybe_enter_position(client, signal, reason)
        else:
            maybe_exit_position(client)

    def diag_loop():
        while not stop_flag["stop"]:
            try:
                if ws_holder.get("ws") is not None and len(S.tokens) == 2:
                    _diag_tick()
            except Exception as _e:
                print(f"⚠️ diag_loop error: {str(_e)[:120]}")
            time.sleep(0.2)

    def on_message(ws, message):
        daily_rollover()
        if not isinstance(message, str):
            return
        if DEBUG_RAW:
            print("RAW:", message[:700])
        S.last_ws_msg_ts = time.time()
        try:
            obj = json.loads(message)
        except Exception:
            return
        extract_books(obj)
        # v5.3: feed MM tracker with latest Polymarket book data
        if len(S.tokens) == 2:
            for tok_id in S.tokens:
                b = S.book.get(tok_id, {})
                bid_p = b.get("best_bid")
                ask_p = b.get("best_ask")
                bid_l = b.get("bid_top3", 0.0)
                ask_l = b.get("ask_top3", 0.0)
                mm_tracker.update(tok_id, bid_p, ask_p, bid_l, ask_l)
        # 2026-10-26: el cálculo de señales/compras/salidas se movió TAL CUAL al hilo
        # _diag_tick() (abajo). Aquí solo se lee el libro → siempre al día.
        _note_book_lag(obj)
        _note_pm_trades(obj)   # 2026-10-26: flujo de compras en PM para el método FLOW

    def on_error(ws, error):
        print(f"⚠️ WS error: {error}")

    def on_close(ws, code, msg):
        print(f"🔌 WS closed: {code} {msg}")

    threading.Thread(target=watchdog_loop, daemon=True).start()
    threading.Thread(target=ping_loop, daemon=True).start()
    _diag_th = threading.Thread(target=diag_loop, name="diag", daemon=True)   # 2026-10-26
    _diag_th.start()

    # v5.9: Stink bid mode — runs in parallel with TF
    if USE_STINK_BID and not reconnect:
        def stink_thread():
            try:
                time.sleep(3)  # let WS connect first
                run_stink_bid_cycle(client, market)
            except Exception as e:
                print(f"  ❌ Stink bid thread error: {e}")
        threading.Thread(target=stink_thread, daemon=True).start()

    headers = ["Origin: https://polymarket.com", "User-Agent: Mozilla/5.0"]
    ws = websocket.WebSocketApp(
        WS_URL, header=headers,
        on_open=on_open, on_message=on_message,
        on_error=on_error, on_close=on_close,
    )
    ws.run_forever(sslopt={"cert_reqs": ssl.CERT_NONE}, ping_interval=15, ping_timeout=10)
    stop_flag["stop"] = True
    # 2026-10-26: esperar a que el hilo de señales termine lo que esté haciendo (p. ej. una
    # orden en curso) antes de pasar al siguiente mercado — igual que antes, cuando on_message
    # tenía que terminar antes de que el WebSocket cerrara.
    try:
        _diag_th.join(timeout=30)
    except Exception:
        pass


# ================================================================
#  CLIENT INIT
# ================================================================
def make_client(signature_type):
    global API_CREDS, SIGNER_ADDRESS, FUNDER_ADDRESS
    pk = os.getenv("PRIVATE_KEY", "").strip()
    if not pk:
        raise RuntimeError("PRIVATE_KEY missing")
    SIGNER_ADDRESS = Account.from_key(pk).address
    FUNDER_ADDRESS = os.getenv("FUNDER_ADDRESS", os.getenv("POLY_ADDRESS", "")).strip()
    if not FUNDER_ADDRESS:
        FUNDER_ADDRESS = SIGNER_ADDRESS
    client = ClobClient(
        host=CLOB_HOST, chain_id=CHAIN_ID, key=pk,
        signature_type=signature_type, funder=FUNDER_ADDRESS,
    )
    # v2 MIGRATION (2026-04-28): create_or_derive_api_creds() → create_or_derive_api_key()
    # ANTI-CLOUDFLARE (2026-05-04): cachear API creds en disco para evitar
    # llamadas repetidas a /auth/api-key (que activan Cloudflare WAF en IPs de AWS).
    # Las creds son determinísticas por (private_key + funder), así que se pueden cachear.
    CREDS_CACHE_FILE = os.getenv("API_CREDS_CACHE", "/tmp/.poly_api_creds.json")
    API_CREDS = None
    try:
        if os.path.exists(CREDS_CACHE_FILE):
            import json as _json
            with open(CREDS_CACHE_FILE, "r") as f:
                cached = _json.load(f)
            if cached.get("signer") == SIGNER_ADDRESS and cached.get("funder") == FUNDER_ADDRESS:
                # Reconstruir API creds desde el cache
                from py_clob_client_v2.clob_types import ApiCreds
                API_CREDS = ApiCreds(
                    api_key=cached["api_key"],
                    api_secret=cached["api_secret"],
                    api_passphrase=cached["api_passphrase"],
                )
                print(f"🔐 API creds cargadas desde cache ({CREDS_CACHE_FILE})")
    except Exception as e:
        print(f"⚠️ Error leyendo creds cache: {e} — derivando de nuevo")
        API_CREDS = None
    
    if API_CREDS is None:
        # Solo llamar a Polymarket si no hay cache válido (evita Cloudflare WAF)
        API_CREDS = client.create_or_derive_api_key()
        # Guardar en cache para próximos arranques
        try:
            import json as _json
            api_key = _creds_get(API_CREDS, "api_key") or _creds_get(API_CREDS, "apiKey") or _creds_get(API_CREDS, "key")
            api_secret = _creds_get(API_CREDS, "api_secret") or _creds_get(API_CREDS, "apiSecret") or _creds_get(API_CREDS, "secret")
            api_passphrase = _creds_get(API_CREDS, "api_passphrase") or _creds_get(API_CREDS, "apiPassphrase") or _creds_get(API_CREDS, "passphrase")
            with open(CREDS_CACHE_FILE, "w") as f:
                _json.dump({
                    "signer": SIGNER_ADDRESS,
                    "funder": FUNDER_ADDRESS,
                    "api_key": api_key,
                    "api_secret": api_secret,
                    "api_passphrase": api_passphrase,
                }, f)
            os.chmod(CREDS_CACHE_FILE, 0o600)  # solo owner puede leer (seguridad)
            print(f"💾 API creds guardadas en cache ({CREDS_CACHE_FILE})")
        except Exception as e:
            print(f"⚠️ No se pudo guardar cache: {e}")
    
    client.set_api_creds(API_CREDS)
    return client


# ================================================================
#  ON-CHAIN: Approvals + Auto-Claim
# ================================================================
ERC1155_APPROVAL_ABI = json.loads("""[
  {"inputs": [{"name": "account","type": "address"},{"name": "operator","type": "address"}],
   "name": "isApprovedForAll","outputs": [{"name": "","type": "bool"}],
   "stateMutability": "view","type": "function"},
  {"inputs": [{"name": "operator","type": "address"},{"name": "approved","type": "bool"}],
   "name": "setApprovalForAll","outputs": [],
   "stateMutability": "nonpayable","type": "function"},
  {"inputs": [{"name": "account","type": "address"},{"name": "id","type": "uint256"}],
   "name": "balanceOf","outputs": [{"name": "","type": "uint256"}],
   "stateMutability": "view","type": "function"}
]""")

ERC20_APPROVAL_ABI = json.loads("""[
  {"inputs": [{"name": "owner","type": "address"},{"name": "spender","type": "address"}],
   "name": "allowance","outputs": [{"name": "","type": "uint256"}],
   "stateMutability": "view","type": "function"},
  {"inputs": [{"name": "spender","type": "address"},{"name": "amount","type": "uint256"}],
   "name": "approve","outputs": [{"name": "","type": "bool"}],
   "stateMutability": "nonpayable","type": "function"}
]""")

CTF_REDEEM_ABI = json.loads("""[
  {"inputs": [
    {"name": "collateralToken","type": "address"},
    {"name": "parentCollectionId","type": "bytes32"},
    {"name": "conditionId","type": "bytes32"},
    {"name": "indexSets","type": "uint256[]"}],
   "name": "redeemPositions","outputs": [],
   "stateMutability": "nonpayable","type": "function"},
  {"inputs": [
    {"name": "collateralToken","type": "address"},
    {"name": "parentCollectionId","type": "bytes32"},
    {"name": "conditionId","type": "bytes32"},
    {"name": "partition","type": "uint256[]"},
    {"name": "amount","type": "uint256"}],
   "name": "mergePositions","outputs": [],
   "stateMutability": "nonpayable","type": "function"},
  {"inputs": [{"name": "conditionId","type": "bytes32"}],
   "name": "payoutDenominator","outputs": [{"name": "","type": "uint256"}],
   "stateMutability": "view","type": "function"}
]""")

# v5.18 FIX A: ABI del Gnosis Safe proxy wallet de Polymarket (signature_type=2).
# Incluye execTransaction para ejecutar cualquier call via el Safe, y getOwners para
# detectar automáticamente si el Safe tiene un solo owner (caso común de Polymarket).
SAFE_ABI = json.loads("""[
  {"inputs": [
    {"name": "to","type": "address"},
    {"name": "value","type": "uint256"},
    {"name": "data","type": "bytes"},
    {"name": "operation","type": "uint8"},
    {"name": "safeTxGas","type": "uint256"},
    {"name": "baseGas","type": "uint256"},
    {"name": "gasPrice","type": "uint256"},
    {"name": "gasToken","type": "address"},
    {"name": "refundReceiver","type": "address"},
    {"name": "signatures","type": "bytes"}],
   "name": "execTransaction",
   "outputs": [{"name": "success","type": "bool"}],
   "stateMutability": "payable","type": "function"},
  {"inputs": [], "name": "getOwners",
   "outputs": [{"name": "","type": "address[]"}],
   "stateMutability": "view","type": "function"},
  {"inputs": [], "name": "getThreshold",
   "outputs": [{"name": "","type": "uint256"}],
   "stateMutability": "view","type": "function"}
]""")

_w3: Optional[Any] = None


def _get_w3():
    global _w3
    if _w3 is None:
        if not HAS_WEB3:
            return None
        _w3 = Web3(Web3.HTTPProvider(POLYGON_RPC))
        if not _w3.is_connected():
            print(f"⚠️ Cannot connect to Polygon RPC: {POLYGON_RPC}")
            _w3 = None
            return None
        print(f"🟢 Connected to Polygon RPC")
    return _w3


def _send_tx(w3, tx_data, pk):
    signed_tx = w3.eth.account.sign_transaction(tx_data, pk)
    tx_hash = w3.eth.send_raw_transaction(signed_tx.raw_transaction)
    print(f"   📤 tx: {tx_hash.hex()[:20]}...")
    receipt = w3.eth.wait_for_transaction_receipt(tx_hash, timeout=120)
    gas_matic = w3.from_wei(
        receipt['gasUsed'] * receipt.get('effectiveGasPrice', w3.eth.gas_price), 'ether')
    return receipt, tx_hash, gas_matic


def ensure_all_approvals():
    if not AUTO_APPROVE_ENABLED or not HAS_WEB3:
        return
    pk = os.getenv("PRIVATE_KEY", "").strip()
    if not pk:
        return
    w3 = _get_w3()
    if not w3:
        return
    account = Account.from_key(pk)
    owner_addr = os.getenv("FUNDER_ADDRESS", os.getenv("POLY_ADDRESS", "")).strip()
    if not owner_addr:
        owner_addr = account.address
    owner = Web3.to_checksum_address(owner_addr)
    signer = Web3.to_checksum_address(account.address)
    print(f"\n🔑 Checking approvals for {owner}...")
    ct_contract = w3.eth.contract(address=Web3.to_checksum_address(CONDITIONAL_TOKENS_ADDR), abi=ERC1155_APPROVAL_ABI)
    usdc_contract = w3.eth.contract(address=Web3.to_checksum_address(USDC_POLYGON), abi=ERC20_APPROVAL_ABI)
    MAX_UINT256 = 2**256 - 1
    nonce = w3.eth.get_transaction_count(signer)
    approvals_sent = 0
    for exchange in EXCHANGE_CONTRACTS:
        exchange_cs = Web3.to_checksum_address(exchange)
        label = "CTF_EX" if exchange == CTF_EXCHANGE_ADDR else \
                "NEG_RISK" if exchange == NEG_RISK_CTF_EXCHANGE else "ADAPTER"
        try:
            is_approved = ct_contract.functions.isApprovedForAll(owner, exchange_cs).call()
            if is_approved:
                print(f"   ✅ CT → {label}: approved")
            else:
                print(f"   🔄 CT → {label}: setting...")
                tx = ct_contract.functions.setApprovalForAll(exchange_cs, True).build_transaction({
                    'from': signer, 'nonce': nonce, 'gas': 80000,
                    'gasPrice': w3.eth.gas_price, 'chainId': CHAIN_ID,
                })
                receipt, tx_hash, gas = _send_tx(w3, tx, pk)
                if receipt['status'] == 1:
                    print(f"   ✅ CT → {label}: APPROVED (gas: {gas:.4f})")
                    nonce += 1
                    approvals_sent += 1
        except Exception as e:
            print(f"   ❌ CT → {label}: {e}")
        try:
            allowance = usdc_contract.functions.allowance(owner, exchange_cs).call()
            if allowance > 10**12:
                print(f"   ✅ USDC → {label}: OK")
            else:
                print(f"   🔄 USDC → {label}: setting...")
                tx = usdc_contract.functions.approve(exchange_cs, MAX_UINT256).build_transaction({
                    'from': signer, 'nonce': nonce, 'gas': 60000,
                    'gasPrice': w3.eth.gas_price, 'chainId': CHAIN_ID,
                })
                receipt, tx_hash, gas = _send_tx(w3, tx, pk)
                if receipt['status'] == 1:
                    print(f"   ✅ USDC → {label}: APPROVED (gas: {gas:.4f})")
                    nonce += 1
                    approvals_sent += 1
        except Exception as e:
            print(f"   ❌ USDC → {label}: {e}")
    if approvals_sent > 0:
        tg_send(f"🔑 Set {approvals_sent} new approvals")
    else:
        print("🔑 All approvals OK ✅")


def query_conditional_token_balance(token_id_hex: str) -> Optional[float]:
    if not HAS_WEB3:
        return None
    w3 = _get_w3()
    if not w3:
        return None
    try:
        owner_addr = FUNDER_ADDRESS or SIGNER_ADDRESS
        if not owner_addr:
            return None
        ct = w3.eth.contract(
            address=Web3.to_checksum_address(CONDITIONAL_TOKENS_ADDR), abi=ERC1155_APPROVAL_ABI)
        token_id_int = int(token_id_hex, 16) if token_id_hex.startswith("0x") else int(token_id_hex)
        raw_balance = ct.functions.balanceOf(
            Web3.to_checksum_address(owner_addr), token_id_int).call()
        return raw_balance / (10 ** USDC_DECIMALS)
    except Exception as e:
        print(f"⚠️ Token balance query failed: {e}")
        return None


def _build_safe_prevalidated_signature(signer_addr: str) -> bytes:
    """v5.18 FIX A: construye la signature 'pre-validated' para un Gnosis Safe
    cuando el que manda el execTransaction es un owner del Safe.

    Formato: r (32 bytes) = owner address padded + s (32 bytes) = 0 + v (1 byte) = 0x01
    Cuando v=1 y el msg.sender es un owner del Safe, el Safe acepta la tx sin
    requerir una firma EIP-712 adicional.
    """
    addr = Web3.to_checksum_address(signer_addr)
    addr_bytes = bytes.fromhex(addr[2:])
    # r: 32 bytes, los primeros 12 son ceros (padding), los últimos 20 son el address
    r = b'\x00' * 12 + addr_bytes
    s = b'\x00' * 32
    v = b'\x01'
    return r + s + v


def _execute_via_safe(w3, safe_addr: str, target: str, calldata: bytes, pk: str,
                      gas_limit: int = 500000) -> tuple:
    """v5.18 FIX A: ejecuta una llamada (target, calldata) a través del Safe proxy
    usando la signature pre-validated del signer (que debe ser owner del Safe).

    Return: (receipt, tx_hash, gas_matic)
    """
    account = Account.from_key(pk)
    signer_addr = Web3.to_checksum_address(account.address)
    safe_addr = Web3.to_checksum_address(safe_addr)

    safe = w3.eth.contract(address=safe_addr, abi=SAFE_ABI)
    signatures = _build_safe_prevalidated_signature(signer_addr)

    tx = safe.functions.execTransaction(
        Web3.to_checksum_address(target),  # to
        0,                                  # value
        calldata,                           # data
        0,                                  # operation (0=CALL)
        0,                                  # safeTxGas (0 = dejar que EVM decida)
        0,                                  # baseGas
        0,                                  # gasPrice
        "0x0000000000000000000000000000000000000000",  # gasToken (ETH=0x0)
        "0x0000000000000000000000000000000000000000",  # refundReceiver
        signatures
    ).build_transaction({
        'from': signer_addr,
        'nonce': w3.eth.get_transaction_count(signer_addr),
        'gas': gas_limit,
        'gasPrice': w3.eth.gas_price,
        'chainId': CHAIN_ID,
    })
    return _send_tx(w3, tx, pk)


def try_auto_claim(condition_id: str, token_label: str, position_size: float):
    """v5.18 FIX A: si FUNDER_ADDRESS != signer (Polymarket proxy wallet), ejecuta
    redeemPositions a través del Safe usando execTransaction con signature prevalidada.
    Si FUNDER_ADDRESS == signer (caso EOA directo, raro en Polymarket), usa el path
    directo original.
    """
    if not AUTO_CLAIM_ENABLED or not HAS_WEB3:
        return False
    pk = os.getenv("PRIVATE_KEY", "").strip()
    if not pk:
        return False
    try:
        w3 = _get_w3()
        if not w3:
            return False

        account = Account.from_key(pk)
        signer_addr = Web3.to_checksum_address(account.address)
        funder = (FUNDER_ADDRESS or "").strip() or signer_addr
        funder = Web3.to_checksum_address(funder)
        uses_safe = (funder.lower() != signer_addr.lower())

        ctf_addr = Web3.to_checksum_address(CONDITIONAL_TOKENS_ADDR)
        ctf = w3.eth.contract(address=ctf_addr, abi=CTF_REDEEM_ABI)
        cond_bytes = bytes.fromhex(condition_id.replace("0x", ""))

        # 1. Verificar que el mercado está resuelto on-chain
        try:
            payout_denom = ctf.functions.payoutDenominator(cond_bytes).call()
            if payout_denom == 0:
                print(f"⏳ AUTO_CLAIM: not yet resolved on-chain")
                return False
        except Exception:
            pass

        parent = b'\x00' * 32

        if uses_safe:
            # === CAMINO SAFE (Polymarket proxy) ===
            # Construimos el calldata de redeemPositions y lo ejecutamos via el Safe.
            calldata = ctf.encode_abi(
                abi_element_identifier="redeemPositions",
                args=[Web3.to_checksum_address(USDC_POLYGON), parent, cond_bytes, [1, 2]]
            )
            print(f"  🔐 AUTO_CLAIM via Safe {funder[:10]}... (signer={signer_addr[:10]}...)")
            try:
                receipt, tx_hash, gas = _execute_via_safe(w3, funder, ctf_addr, calldata, pk)
            except Exception as safe_err:
                print(f"  ⚠️ Safe execTransaction falló: {safe_err}")
                print(f"  ↪️ Fallback: intentando redeemPositions directo (puede no funcionar)")
                tx = ctf.functions.redeemPositions(
                    Web3.to_checksum_address(USDC_POLYGON), parent, cond_bytes, [1, 2]
                ).build_transaction({
                    'from': signer_addr, 'nonce': w3.eth.get_transaction_count(signer_addr),
                    'gas': 300000, 'gasPrice': w3.eth.gas_price, 'chainId': CHAIN_ID,
                })
                receipt, tx_hash, gas = _send_tx(w3, tx, pk)
        else:
            # === CAMINO EOA DIRECTO (signer tiene los tokens directamente) ===
            tx = ctf.functions.redeemPositions(
                Web3.to_checksum_address(USDC_POLYGON), parent, cond_bytes, [1, 2]
            ).build_transaction({
                'from': signer_addr, 'nonce': w3.eth.get_transaction_count(signer_addr),
                'gas': 300000, 'gasPrice': w3.eth.gas_price, 'chainId': CHAIN_ID,
            })
            receipt, tx_hash, gas = _send_tx(w3, tx, pk)

        if receipt['status'] == 1:
            method = "Safe" if uses_safe else "EOA"
            msg = f"✅ AUTO_CLAIM ({method}) | {token_label} | gas={gas:.4f} MATIC"
            print(msg)
            tg_send(msg)
            return True
        else:
            tg_send(f"❌ AUTO_CLAIM FAILED | tx={tx_hash.hex()[:16]}")
            print(f"❌ AUTO_CLAIM tx reverted: {tx_hash.hex()}")
            return False
    except Exception as e:
        print(f"❌ AUTO_CLAIM error: {e}")
        return False


def try_merge_positions(condition_id: str, pairs: int) -> bool:
    """
    Merge N pairs of UP+DN shares into N USDC via CTF mergePositions.
    Requires condition_id and N pairs of each outcome token.
    v5.18 FIX A: usa Safe proxy via execTransaction cuando FUNDER != signer.
    Returns True if merge tx succeeded.
    """
    if DRY_RUN:
        print(f"  🔀 [DRY] MERGE {pairs} pairs → ${pairs} USDC (simulated)")
        return True
    if not HAS_WEB3 or not condition_id or pairs <= 0:
        return False
    pk = os.getenv("PRIVATE_KEY", "").strip()
    if not pk:
        return False
    try:
        w3 = _get_w3()
        if not w3:
            return False
        account = Account.from_key(pk)
        signer_addr = Web3.to_checksum_address(account.address)
        funder = (FUNDER_ADDRESS or "").strip() or signer_addr
        funder = Web3.to_checksum_address(funder)
        uses_safe = (funder.lower() != signer_addr.lower())

        ctf_addr = Web3.to_checksum_address(CONDITIONAL_TOKENS_ADDR)
        ctf = w3.eth.contract(address=ctf_addr, abi=CTF_REDEEM_ABI)
        cond_bytes = bytes.fromhex(condition_id.replace("0x", ""))
        parent = b'\x00' * 32
        amount = int(pairs * (10 ** USDC_DECIMALS))

        if uses_safe:
            calldata = ctf.encode_abi(
                abi_element_identifier="mergePositions",
                args=[Web3.to_checksum_address(USDC_POLYGON), parent, cond_bytes, [1, 2], amount]
            )
            print(f"  🔐 MERGE via Safe {funder[:10]}...")
            receipt, tx_hash, gas = _execute_via_safe(w3, funder, ctf_addr, calldata, pk)
        else:
            tx = ctf.functions.mergePositions(
                Web3.to_checksum_address(USDC_POLYGON),
                parent, cond_bytes, [1, 2], amount
            ).build_transaction({
                'from': signer_addr,
                'nonce': w3.eth.get_transaction_count(signer_addr),
                'gas': 300000,
                'gasPrice': w3.eth.gas_price,
                'chainId': CHAIN_ID,
            })
            receipt, tx_hash, gas = _send_tx(w3, tx, pk)

        if receipt['status'] == 1:
            method = "Safe" if uses_safe else "EOA"
            msg = f"🔀 MERGE ({method}) {pairs} pairs → ${pairs:.2f} USDC | gas={gas:.4f} MATIC | tx={tx_hash.hex()[:16]}"
            print(msg)
            tg_send(msg)
            return True
        else:
            print(f"❌ MERGE FAILED | tx={tx_hash.hex()[:16]}")
            return False
    except Exception as e:
        print(f"❌ MERGE error: {e}")
        return False


_pending_claims: List[Dict] = []


def schedule_claim(condition_id: str, token_label: str, position_size: float):
    _pending_claims.append({
        'condition_id': condition_id, 'token_label': token_label,
        'size': position_size, 'ts': time.time(), 'attempts': 0,
    })


def process_pending_claims():
    if not _pending_claims:
        return
    now = time.time()
    still_pending = []
    for claim in _pending_claims:
        if claim['attempts'] >= 15:  # 15 attempts × 60s = 15 min coverage
            tg_send(f"⚠️ AUTO_CLAIM gave up for {claim['token_label']}")
            continue
        if claim['attempts'] > 0 and (now - claim['ts']) < 60:
            still_pending.append(claim)
            continue
        claim['attempts'] += 1
        claim['ts'] = now
        ok = try_auto_claim(claim['condition_id'], claim['token_label'], claim['size'])
        if not ok:
            still_pending.append(claim)
    _pending_claims.clear()
    _pending_claims.extend(still_pending)


# ================================================================
#  MAIN
# ================================================================
def main():
    # v5.9: lockfile incluye WINDOW_SECONDS para que sniper (5m) y stink (15m) no se pisen
    mode_suffix = "stink" if USE_STINK_BID else f"{WINDOW_SECONDS}s"
    lockfile_path = f"/tmp/mr_bot_v4_{ASSET}_{mode_suffix}.lock"

    # Robust lockfile: check if old PID is still alive, kill stale locks
    if os.path.exists(lockfile_path):
        try:
            with open(lockfile_path, "r") as f:
                old_pid = int(f.read().strip())
            # Check if process is still alive
            os.kill(old_pid, 0)  # signal 0 = check existence
            print(f"❌ ABORT: Another {ASSET} bot (PID {old_pid}) is still running!")
            print(f"   Kill it first: kill {old_pid}")
            sys.exit(1)
        except (ValueError, ProcessLookupError, FileNotFoundError):
            # PID file is invalid or process is dead — safe to proceed
            print(f"⚠️ Stale lockfile found (old process dead), removing...")
            os.remove(lockfile_path)
        except PermissionError:
            print(f"❌ ABORT: Another {ASSET} bot is running (cannot check PID)")
            sys.exit(1)

    _lockfp = open(lockfile_path, "w")
    try:
        fcntl.flock(_lockfp, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        print(f"❌ ABORT: Another {ASSET} bot instance is already running")
        sys.exit(1)
    _lockfp.write(str(os.getpid()))
    _lockfp.flush()

    mode_str = "Chainlink Trend Follow" if USE_TREND_FOLLOW else "Mean Reversion"
    print("=" * 60)
    print(f"  Bot v5.0 — {mode_str} | {ASSET.upper()}")
    if USE_TREND_FOLLOW:
        print(f"  Chainlink = truth source → buy WITH CL direction → hold to expiry")
    else:
        print(f"  Buy cheap on overreaction → hold if confirmed, TP if not")
    print("=" * 60)

    print(f"🔄 Starting {ASSET.upper()} spot tracker...")
    spot_tracker.start()
    time.sleep(1)

    if CHAINLINK_ENABLED:
        print("⛓️ Starting Chainlink feed...")
        chainlink_feed.start()
        time.sleep(1)

    print("📊 Starting depth tracker...")
    binance_depth.start()
    time.sleep(1)

    if USE_CANDLE_ANALYSIS:
        print("🕯️ Starting candle analyzer...")
        candle_analyzer.start()
        time.sleep(1)

    print("🌊 Starting trade flow tracker...")
    trade_flow.start()
    time.sleep(1)

    print("🔗 Starting Polymarket RTDS (Chainlink exact PTB)...")
    polymarket_rtds.start()
    time.sleep(5)  # dar tiempo a conectar, suscribir y recibir primeros precios

    prefill_window_history()

    client = make_client(ORDER_SIGNATURE_TYPE)

    try:
        ensure_all_approvals()
    except Exception as e:
        print(f"⚠️ Approval check failed: {e}")
        traceback.print_exc()

    print(f"✅ CLOB ready | Signer: {SIGNER_ADDRESS} | Funder: {FUNDER_ADDRESS}")
    print(f"   DRY_RUN: {'ON' if DRY_RUN else '❌ OFF — LIVE'}")
    print(f"   Asset: {ASSET.upper()} | Window: {WINDOW_SECONDS}s | Slug: {BASE_SLUG_PREFIX}")
    if USE_COPY_TRADING:
        print(f"   MODE: MOMENTUM STRADDLE (v5.15) — CL direction + hedge")
        print(f"   Momentum: {STRADDLE_SHARES:.0f}sh | Hedge: {STRADDLE_SHARES/STRADDLE_RATIO:.0f}sh (ratio {STRADDLE_RATIO:.0f}:1)")
        print(f"   Interval: {STRADDLE_INTERVAL:.0f}s | Window: {STRADDLE_START_SEC:.0f}-{STRADDLE_END_SEC:.0f}s")
        print(f"   Budget: ${STRADDLE_MAX_BUDGET:.0f}/window | Max price: {STRADDLE_MAX_PRICE} | Min CL: ${STRADDLE_MIN_CL:.0f}")
        max_rounds = int((STRADDLE_END_SEC - STRADDLE_START_SEC) / STRADDLE_INTERVAL)
        print(f"   Max rounds: {max_rounds} | TP: ${STRADDLE_TP_USD:.0f} profit → sell ALL | Hold to expiry + auto-claim")
    elif USE_WHALE_ACCUM:
        print(f"   MODE: WHALE ACCUMULATION (v5.13) — Split + Reinforce + Final Push")
        print(f"   Shares: {WHALE_SHARES:.0f} per order | P1: split {WHALE_SHARES:.0f}+{WHALE_SHARES:.0f} | P2: reinforce {WHALE_SHARES:.0f} | P3: final {WHALE_SHARES:.0f}")
        print(f"   P1: {WHALE_P1_START}-{WHALE_P1_END}s max@{WHALE_P1_MAX_PRICE} | P2: {WHALE_P2_START}-{WHALE_P2_END}s CL≥${WHALE_P2_CL_DELTA:.0f} max@{WHALE_P2_MAX_PRICE}")
        print(f"   P3: {WHALE_P3_START}-{WHALE_P3_END}s CL≥${WHALE_P3_CL_DELTA:.0f} max@{WHALE_P3_MAX_PRICE} | chain_age≤{WHALE_MAX_CHAIN_AGE:.0f}s")
    elif USE_TREND_FOLLOW:
        print(f"   MODE: TREND FOLLOW (v5.0) — Chainlink is truth source")
        print(f"   TF Entry: ${TF_MIN_ENTRY_PRICE:.2f}-${TF_MAX_ENTRY_PRICE:.2f} | CL delta >${MIN_CL_DELTA_USD:.0f} | confirm x{CL_CONFIRM_COUNT}")
        print(f"   TF Exit: HOLD_TO_EXPIRY | TP@{TF_TP_PRICE:.2f} | CL_REVERSE@${TF_EMERGENCY_CL_REVERSE_USD:.0f}")
    else:
        print(f"   MODE: MEAN REVERSION (legacy)")
        print(f"   Entry: ${MIN_ENTRY_PRICE:.2f}-${MAX_ENTRY_PRICE:.2f} | TP: +{TP_PCT*100:.0f}%")
        print(f"   Smart hold: trend confirms → hold to expiry, else active TP")
    print(f"   Imbalance filter: UP>={IMB_UP_MIN} DN<={IMB_DN_MAX}")
    if PROGRESSIVE_SIZING:
        print(f"   Sizing: PROGRESSIVE base=${PROG_BASE_USDC:.0f} step=${PROG_STEP_USDC:.0f} max=${PROG_MAX_USDC:.0f} (pause after {PROG_MAX_LOSSES} losses)")
    else:
        print(f"   Sizing: {USE_BALANCE_PCT*100:.0f}% (${MIN_TRADE_USDC}-${MAX_TRADE_USDC})")
    print(f"   CL poll: every {CHAINLINK_POLL_SEC:.0f}s | RPCs: {len(CHAINLINK_RPCS)}")
    print(f"   Daily loss limit: ${DAILY_LOSS_LIMIT_USDC:.0f}")
    print()

    last_completed_slug = None
    _reconnecting_slug = None  # v5.9: track mid-cycle reconnection
    prefetch_state: Dict[str, Any] = {}  # comparte next_market entre watchdog y main loop

    # ── Restaurar posición abierta si el bot fue reiniciado ──────────
    position_restored = restore_position_state()
    _load_sizing_state()  # restaurar dynamic_base si no viene de position_state
    if position_restored and S.slug:
        print(f"🔄 Reconectando al mercado de posición abierta: {S.slug}")
        restored_market = gamma_get_market_by_slug(S.slug)
        if restored_market:
            run_ws(client, restored_market, prefetch_state=prefetch_state)
            last_completed_slug = S.slug
        else:
            print(f"⚠️ No se pudo reconectar a {S.slug} — el mercado puede haber expirado")

    while True:
        try:
            # v5.9: Golden hours — solo operar en horarios configurados
            if not is_within_trading_hours():
                current_h = now_utc().hour
                if int(time.time()) % 300 == 0:  # log cada 5 min
                    print(f"😴 Fuera de golden hours (UTC {current_h:02d}:xx) — TRADING_HOURS_UTC={TRADING_HOURS_UTC}")
                # tg_check_commands()  # DESACTIVADO 2026-10-26 (pedido del usuario)
                time.sleep(30)
                continue

            # Usar mercado pre-fetcheado si está disponible (más rápido)
            market = prefetch_state.pop("next_market", None)
            if not market:
                market = find_active_btc_15m_market()

            if not market:
                print(f"⏳ No hay mercado {ASSET.upper()} activo. Esperando {min(15, WINDOW_SECONDS//4)}s...")
                time.sleep(min(15, WINDOW_SECONDS // 4))
                continue

            slug = market.get("slug", "")

            if slug == last_completed_slug:
                # Ya procesamos este ciclo — esperar a que cierre y llegue el siguiente
                end_dt = market_end_time(market)
                if end_dt:
                    wait = (end_dt - now_utc()).total_seconds()
                    wait = max(2, min(wait + 2, WINDOW_SECONDS + 10))
                    print(f"⏭️ {slug} ya completado. Esperando {wait:.0f}s al siguiente...")
                    time.sleep(wait)
                else:
                    time.sleep(15)
                continue

            is_reconnect = (slug == _reconnecting_slug)
            _reconnecting_slug = None  # reset

            if not is_reconnect:
                # ── Snapshot PTB al open exacto ──────────────────────────────────
                _ptb_age = time.time() - (chainlink_feed._pending_ptb[1] if chainlink_feed._pending_ptb else 0)
                if _ptb_age > 15:
                    try:
                        for _rpc in CHAINLINK_RPCS:
                            try:
                                _resp = requests.post(_rpc, json={
                                    "jsonrpc": "2.0", "method": "eth_call",
                                    "params": [{"to": CHAINLINK_CONTRACT, "data": "0xfeaf968c"}, "latest"],
                                    "id": 1
                                }, timeout=3)
                                _result = _resp.json().get("result", "")
                                if _result and len(_result) > 130:
                                    _price = int(_result[66:130], 16) / 1e8
                                    if _price > 1000:
                                        chainlink_feed._pending_ptb = (_price, time.time())
                                        print(f"📌 PTB refresh al open: ${_price:,.2f}")
                                        break
                            except Exception:
                                continue
                    except Exception:
                        pass

            run_ws(client, market, prefetch_state=prefetch_state, reconnect=is_reconnect)

            # v5.9: Solo marcar como completado si el mercado realmente expiró.
            end_dt = market_end_time(market)
            if end_dt and now_utc() >= end_dt:
                last_completed_slug = slug
                _reconnecting_slug = None
            else:
                remaining = (end_dt - now_utc()).total_seconds() if end_dt else 0
                if remaining > 15:
                    print(f"🔄 WS desconectado con {remaining:.0f}s restantes — reconectando...")
                    _reconnecting_slug = slug  # signal reconnect on next iteration
                else:
                    last_completed_slug = slug

            # Programar snapshot del PTB para el siguiente ciclo
            next_open_ts = round_down_to_window_epoch(int(time.time())) + WINDOW_SECONDS
            # PTB del siguiente ciclo lo capturará RTDS automáticamente
            # polymarket_rtds.get_price_at(epoch) cuando init_market lo llame

        except KeyboardInterrupt:
            print("👋 bye")
            spot_tracker.stop()
            binance_depth.stop()
            return
        except Exception as e:
            print(f"⚠️ loop error: {e}")
            traceback.print_exc()
            time.sleep(3)


if __name__ == "__main__":    main()
