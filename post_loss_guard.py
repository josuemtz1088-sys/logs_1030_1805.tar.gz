"""Read-only post-loss guards for CB/FLOW/TW. No trading/order APIs."""
import threading, time
from collections import deque
import requests

class BinancePerpCVD:
    URL = "https://fapi.binance.com/fapi/v1/aggTrades"
    def __init__(self, symbol="BTCUSDT", poll_sec=1.0):
        self.symbol=symbol; self.poll_sec=max(.5,float(poll_sec))
        self.lock=threading.Lock(); self.rows=deque(maxlen=100000)
        self.last_id=None; self.last_ts=0.; self.errors=0
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
            if data: self.last_id=max(int(x["a"]) for x in data)
            return
        points=[]
        for x in data:
            aid=int(x["a"])
            if aid<=self.last_id: continue
            ts=int(x["T"])/1000.; q=float(x["q"])
            points.append((ts,-q if bool(x["m"]) else q,aid))
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
        with self.lock: rows=list(self.rows); last=self.last_ts
        if not rows or now-last>3 or rows[0][0]>now-seconds+3: return None
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
        self.perp=BinancePerpCVD(); self.logger=logger or (lambda x:None)
        self.hist={k:deque(maxlen=2) for k in ("CB","FLOW","TW")}
        self.lock=threading.Lock()
    def start(self): self.perp.start()
    def evaluate(self,strategy,side,series,slug=None,now=None):
        name=str(strategy).upper()
        if name not in self.hist: return False,{"reason":"NOT_APPLICABLE"}
        now=time.time() if now is None else float(now)
        d=1 if str(side).upper()=="UP" else -1
        snap={"ts":now,"slug":slug,"side":str(side).upper(),
              "vel_15s":ds_velocity(series,15,now),
              "vel_30s":ds_velocity(series,30,now),
              "vel_60s":ds_velocity(series,60,now),
              "cvd_perp_30s":self.perp.cvd(30,now)}
        required={"CB":("vel_15s","vel_30s","vel_60s"),
                  "FLOW":("vel_15s","cvd_perp_30s"),
                  "TW":("vel_15s","vel_30s","cvd_perp_30s")}[name]
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
