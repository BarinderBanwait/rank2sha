#!/usr/bin/env python3
"""make_reach_table.py -- build the R4 reach table from the committed reach outputs.

Sibling of make_tables.py, and deliberately separate from it: make_tables.py owns
the CERTIFICATE tables (tab:certs, tab:hyp, tab:compare, tab:reg, tab:lmfdb) and
nothing here may touch those.  This script owns one new table, tab:reach, and the
handful of summary numbers §6.1 quotes alongside it.

Reads   ../data/reach_*.out   (produced by reach.sh)
Writes  ../data/reach_table.tex   and prints the same to stdout.

Every number it emits comes from a `MACHINE reach.p<p>` line of a raw output
file.  Nothing is typed.

MACHINE line format, from reach.sage:

    MACHINE reach.p<p>   v=<v_p(c_2)> prec=<certified exponent>
                         digits=[p, n, summands, prec, leading digit, wall_ms]
    MACHINE setup.modsym v=0 prec=0 digits=[wall_ms]     (the level-12544 one-off)
    MACHINE setup.galrep v=0 prec=0 digits=[wall_ms]

A prime that hit its cap is written with v=0 prec=0 and -1 in the two value
slots; it is reported as CAP HIT and never silently dropped.

ROW SELECTION for the printed table is mechanical, so that the table is
reproducible and not curated: the first scanned prime, then the largest scanned
prime below each of 100, 200, 400, 600, 800 and 1000, then every scanned prime
at or above 1000 (the isolated high-p probes, of which there are few).
Duplicates are removed and the result is sorted.

Usage:  python3 make_reach_table.py
"""
import glob
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "..", "data")

MLINE = re.compile(r"MACHINE\s+(\S+)\s+v=\s*(-?\d+)\s+prec=\s*(-?\d+)\s+digits=\[([^\]]*)\]")

CUTS = [100, 200, 400, 600, 800, 1000]


def read_reach(path):
    """Return (rows, setup_ms, galrep_ms) from one reach_*.out file."""
    rows, setup_ms, galrep_ms = [], None, None
    with open(path) as fh:
        for ln in fh:
            m = MLINE.search(ln)
            if not m:
                continue
            tag = m.group(1)
            vals = [int(x) for x in m.group(4).replace(" ", "").split(",") if x != ""]
            if tag == "setup.modsym":
                setup_ms = vals[0]
            elif tag == "setup.galrep":
                galrep_ms = vals[0]
            elif tag.startswith("reach.p"):
                p, n, summands, prec, lead, wall_ms = vals
                rows.append({
                    "p": p, "n": n, "summands": summands, "prec": prec,
                    "lead": lead, "wall": wall_ms / 1000.0,
                    "v": int(m.group(2)),
                    "capped": (prec == -1),
                })
    return rows, setup_ms, galrep_ms


def select(rows):
    """The mechanical row selection described in the module docstring."""
    if not rows:
        return []
    ps = sorted(r["p"] for r in rows)
    picked = [ps[0]]
    for c in CUTS:
        below = [p for p in ps if p < c]
        if below:
            picked.append(max(below))
    picked.extend(p for p in ps if p >= CUTS[-1])
    return sorted(set(picked))


files = sorted(glob.glob(os.path.join(DATA, "reach_*.out")))
if not files:
    raise SystemExit("no ../data/reach_*.out found -- run reach.sh first")

all_rows, setups, galreps, provenance = [], [], [], []
for f in files:
    rows, s, g = read_reach(f)
    if not rows:
        continue
    all_rows.extend(rows)
    if s is not None:
        setups.append(s)
    if g is not None:
        galreps.append(g)
    provenance.append((os.path.basename(f), len(rows)))

by_p = {}
for r in all_rows:
    # a later file at the same prime wins only if it is not a capped run
    if r["p"] not in by_p or (by_p[r["p"]]["capped"] and not r["capped"]):
        by_p[r["p"]] = r
rows = [by_p[p] for p in sorted(by_p)]

good = [r for r in rows if not r["capped"]]
zero = [r for r in good if r["v"] == 0]
nonzero = [r for r in good if r["v"] != 0]
capped = [r for r in rows if r["capped"]]

L = []
B = L.append

B("%% GENERATED from code/data/reach_*.out by")
B("%%   python3 series/code/lpadic/make_reach_table.py")
B("%% Do not edit by hand; re-run and re-paste.")
B("%% Source files: " + ", ".join("%s (%d primes)" % pr for pr in provenance))
B("%% ---------------- BEGIN GENERATED reach-table -----------------------")
B(r"\begin{tabular}{r r r r r}")
B(r"\hline")
B(r"$p$ & $n$ & summands $(p-1)p^{\,n-1}$ & $v_p(c_2(p))$ & wall (s) \\")
B(r"\hline")
for p in select(rows):
    r = by_p[p]
    if r["capped"]:
        B(r"$%d$ & $%d$ & $%d$ & cap hit & --- \\" % (r["p"], r["n"], r["summands"]))
    else:
        B(r"$%d$ & $%d$ & $%d$ & $%d$ & $%.2f$ \\"
          % (r["p"], r["n"], r["summands"], r["v"], r["wall"]))
B(r"\hline")
B(r"\end{tabular}")
B("%% ---------------- END GENERATED reach-table -------------------------")
B("")
B("%% ---- summary numbers quoted in the prose of \\S\\ref{ss:costs} ----")
if rows:
    B("%%   split primes scanned            : %d" % len(rows))
    B("%%   range                           : %d .. %d" % (rows[0]["p"], rows[-1]["p"]))
    B("%%   approximation order used        : n = %s"
      % ", ".join(str(x) for x in sorted({r["n"] for r in good})))
    B("%%   v_p(c_2(p)) = 0 at              : %d of %d" % (len(zero), len(good)))
    B("%%   v_p(c_2(p)) != 0 at             : %s"
      % ([r["p"] for r in nonzero] if nonzero else "none"))
    B("%%   cap hit at                      : %s"
      % ([r["p"] for r in capped] if capped else "none"))
    B("%%   total per-prime wall time       : %.1f s" % sum(r["wall"] for r in good))
    B("%%   slowest single prime            : p = %d at %.2f s"
      % (max(good, key=lambda r: r["wall"])["p"],
         max(r["wall"] for r in good)))
    B("%%   fastest single prime            : p = %d at %.2f s"
      % (min(good, key=lambda r: r["wall"])["p"],
         min(r["wall"] for r in good)))
    B("%%   total summands                  : %d" % sum(r["summands"] for r in good))
if setups:
    B("%%   one-off modular symbols (12544) : %.2f s  (%s)"
      % (min(setups) / 1000.0,
         "identical across files" if len(set(setups)) == 1
         else "range %.2f--%.2f s" % (min(setups) / 1000.0, max(setups) / 1000.0)))
if galreps:
    B("%%   one-off Galois representation   : %.2f s" % (min(galreps) / 1000.0))

out = "\n".join(L) + "\n"
with open(os.path.join(DATA, "reach_table.tex"), "w") as fh:
    fh.write(out)
print(out, end="")
