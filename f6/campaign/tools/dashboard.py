#!/usr/bin/env python3
"""Live dashboard for the order-6 cube campaign.

    python3 campaign/dashboard.py [--port 8765] [--journal campaign/campaign.jsonl]

Tails the journal incrementally, looks at the workers' scratch directories
for what is being solved right now, and serves campaign/dashboard.html plus
/data.json.  Read-only: it never touches the journal or the driver.
"""
import argparse
import collections
import glob
import json
import os
import re
import shutil
import sys
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import cube_campaign as cc  # noqa: E402

TERMINAL = {"verified", "SAT", "split"}


class State:
    def __init__(self, journal, scratch, log):
        self.journal, self.scratch, self.log = journal, scratch, log
        self.offset = 0
        self.partial = b""
        self.recs = {}                      # cube id -> last record
        self.events = []                    # (ts, status, cube, solve_s, cake_s, lrat)
        self.header = None
        self.roots = [cc.cube_id(p, c) for p, c in cc.root_cubes(2)]
        self.root_index = {r: i for i, r in enumerate(self.roots)}
        self.children = {}                  # split cube id -> [child ids]
        self.lock = threading.Lock()
        self.t_start = time.time()
        self.n_start = None

    def kids(self, cid):
        if cid not in self.children:
            p, c = cc.parse_cube_id(cid)
            self.children[cid] = [cc.cube_id(cp, cc2) for cp, cc2 in cc.split_children(p, c)]
        return self.children[cid]

    def tail(self):
        try:
            size = os.path.getsize(self.journal)
        except OSError:
            return
        if size < self.offset:              # truncated / replaced
            self.offset, self.partial, self.recs, self.events = 0, b"", {}, []
        if size == self.offset:
            return
        with open(self.journal, "rb") as f:
            f.seek(self.offset)
            data = self.partial + f.read()
        lines = data.split(b"\n")
        self.partial = lines.pop()          # possibly torn last line
        self.offset = size - len(self.partial)
        for line in lines:
            line = line.strip()
            if not line:
                continue
            try:
                r = json.loads(line)
            except json.JSONDecodeError:
                continue
            if r.get("status") == "header":
                self.header = r
                continue
            self.recs[r["cube"]] = r
            self.events.append((r.get("ts", 0), r["status"], r["cube"], r.get("solve_s") or 0,
                                r.get("cake_s") or 0, r.get("lrat_bytes") or 0, r.get("depth", 0),
                                r.get("n_children", 0)))
        if self.n_start is None:
            self.n_start = len(self.events)

    def cover(self, cid, depth=0):
        """(covered, total) leaf count under cid, recursing through splits."""
        r = self.recs.get(cid)
        if r is None:
            return 0, 1
        if r["status"] == "verified":
            return 1, 1
        if r["status"] == "split":
            c = t = 0
            for k in self.kids(cid):
                a, b = self.cover(k, depth + 1)
                c += a
                t += b
            return c, t
        return 0, 1                         # SAT / non-terminal: not covered

    def running(self):
        out = []
        now = time.time()
        for wd in sorted(glob.glob(os.path.join(self.scratch, "w*"))):
            for cnf in glob.glob(os.path.join(wd, "c_*.cnf")):
                tag = os.path.basename(cnf)[2:-4]
                cid = tag.replace("_", ";").replace("-", ",")
                try:
                    started = os.path.getmtime(cnf)
                except OSError:
                    continue
                lrat = cnf[:-4] + ".lrat"
                lb = os.path.getsize(lrat) if os.path.exists(lrat) else 0
                lmt = os.path.getmtime(lrat) if os.path.exists(lrat) else started
                phase = "solving" if (now - lmt) < 3 or lb == 0 else "checking"
                out.append({"worker": os.path.basename(wd), "cube": cid, "depth": len(cc.parse_cube_id(cid)[0]),
                            "elapsed": round(now - started, 1), "lrat_mb": round(lb / 1e6, 1), "phase": phase})
        return out

    def progress_line(self):
        try:
            with open(self.log, "rb") as f:
                f.seek(max(0, os.path.getsize(self.log) - 20000))
                txt = f.read().decode("utf-8", "replace")
        except OSError:
            return None
        m = None
        for m in re.finditer(r"\[(\d+)/(\d+)\s+([\d.]+)s\]", txt):
            pass
        return (int(m.group(1)), int(m.group(2)), float(m.group(3))) if m else None

    def snapshot(self):
        with self.lock:
            self.tail()
            now = time.time()
            recs = self.recs
            by_status = collections.Counter(r["status"] for r in recs.values())
            by_depth = collections.defaultdict(collections.Counter)
            for c, r in recs.items():
                by_depth[len(cc.parse_cube_id(c)[0]) + (0 if not c.endswith("stop") else 0)][r["status"]] += 1
            # root map
            chars, detail = [], []
            n_untouched = 0
            for rid in self.roots:
                r = recs.get(rid)
                if r is None:
                    chars.append("p"); n_untouched += 1; detail.append(None); continue
                st = r["status"]
                if st == "verified":
                    chars.append("v"); detail.append([round(r.get("solve_s") or 0, 1), round((r.get("lrat_bytes") or 0) / 1e6), 1, 1])
                elif st == "split":
                    c, t = self.cover(rid)
                    chars.append("c" if c == t else "s"); detail.append([round(r.get("solve_s") or 0, 1), 0, c, t])
                elif st == "SAT":
                    chars.append("!"); detail.append([0, 0, 0, 1])
                else:
                    chars.append("f"); detail.append([round(r.get("solve_s") or 0, 1), 0, 0, 1])
            running = self.running()
            for w in running:
                i = self.root_index.get(w["cube"])
                if i is not None:
                    chars[i] = "r"
            # pending children under splits
            pend_children = 0
            for cid, r in recs.items():
                if r["status"] == "split":
                    for k in self.kids(cid):
                        if k not in recs:
                            pend_children += 1
            # throughput: records per 10 min over the last 24 h, and last hour rate
            buckets = collections.Counter()
            last_hour = 0
            t24 = now - 24 * 3600
            for ev in self.events:
                if ev[0] >= t24:
                    buckets[int((ev[0] - t24) // 600)] += 1
                if ev[0] >= now - 3600:
                    last_hour += 1
            series = [buckets.get(i, 0) for i in range(145)]
            prog = self.progress_line()
            # remaining: untouched roots + pending children (+ expected split growth of untouched roots)
            remaining = n_untouched + pend_children
            expected_growth = int(n_untouched * 0.054 * 110)
            # rate: this run's own progress line (cubes / elapsed) once it has
            # a few minutes behind it, else the journal's last-hour window
            win = [e[0] for e in self.events if e[0] >= now - 3600]
            span_h = max((now - min(win)) / 3600, 5 / 60) if win else 1
            rate = len(win) / span_h if win else 0
            if prog and prog[2] >= 300 and prog[0] >= 20:
                rate = prog[0] / prog[2] * 3600
            eta_h = (remaining + expected_growth) / rate if rate > 0 else None
            recent = [{"ts": e[0], "status": e[1], "cube": e[2], "solve_s": e[3], "cake_s": e[4],
                       "lrat_mb": round(e[5] / 1e6, 1), "n_children": e[7]} for e in self.events[-15:]][::-1]
            ver = [e for e in self.events if e[1] == "verified"]
            hardest = sorted(ver, key=lambda e: -(e[3] + e[4]))[:6]
            lrat_total = sum(e[5] for e in ver)
            # LRAT size histogram (log2 MB buckets)
            hist = collections.Counter()
            for e in ver:
                mb = e[5] / 1e6
                hist[min(12, max(0, int(mb).bit_length()))] += 1
            du = shutil.disk_usage(self.scratch if os.path.isdir(self.scratch) else HERE)
            scratch_bytes = 0
            for p in glob.glob(os.path.join(self.scratch, "w*", "*")):
                try:
                    scratch_bytes += os.path.getsize(p)
                except OSError:
                    pass
            return {
                "now": now, "started": self.t_start,
                "roots": len(self.roots), "root_map": "".join(chars), "root_detail": detail,
                "root_ids": self.roots,
                "by_status": dict(by_status), "by_depth": {d: dict(c) for d, c in sorted(by_depth.items())},
                "untouched_roots": n_untouched, "pending_children": pend_children,
                "expected_growth": expected_growth, "remaining": remaining,
                "rate_per_h": round(rate, 1), "eta_h": round(eta_h, 2) if eta_h is not None else None,
                "last_hour": last_hour, "series_10min": series, "progress": prog,
                "running": running, "recent": recent,
                "hardest": [{"cube": e[2], "solve_s": e[3], "cake_s": e[4], "lrat_mb": round(e[5] / 1e6)} for e in hardest],
                "lrat_total_tb": round(lrat_total / 1e12, 3), "lrat_hist": [hist.get(i, 0) for i in range(13)],
                "sat": by_status.get("SAT", 0), "records": len(self.events),
                "header": {k: self.header.get(k) for k in ("base_sha256", "num_vars", "num_clauses", "solver_version")} if self.header else None,
                "disk_free_gb": round(du.free / 1e9), "scratch_gb": round(scratch_bytes / 1e9, 2),
                "driver_alive": bool(running) or (prog is not None and now - os.path.getmtime(self.log) < 600 if os.path.exists(self.log) else False),
            }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--journal", default=os.path.join(HERE, "campaign.jsonl"))
    ap.add_argument("--scratch", default=os.path.join(HERE, "scratch"))
    ap.add_argument("--log", default=os.path.join(HERE, "campaign.live.log"))
    ap.add_argument("--port", type=int, default=8765)
    a = ap.parse_args()
    st = State(a.journal, a.scratch, a.log)
    st.tail()
    html_path = os.path.join(HERE, "dashboard.html")
    cache = {"t": 0, "body": b""}

    class H(BaseHTTPRequestHandler):
        def log_message(self, *_):
            pass

        def do_GET(self):
            if self.path.startswith("/data.json"):
                if time.time() - cache["t"] > 3:
                    cache["body"] = json.dumps(st.snapshot()).encode()
                    cache["t"] = time.time()
                body, ctype = cache["body"], "application/json"
            else:
                with open(html_path, "rb") as f:
                    body = f.read()
                ctype = "text/html; charset=utf-8"
            self.send_response(200)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(body)

    print(f"dashboard: http://localhost:{a.port}  (journal {a.journal}, {len(st.recs)} cubes loaded)", flush=True)
    ThreadingHTTPServer(("127.0.0.1", a.port), H).serve_forever()


if __name__ == "__main__":
    main()
