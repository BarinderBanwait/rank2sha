#!/usr/bin/env python3
"""control_vs_paper.py -- the control: does this pipeline reproduce the frozen paper?

The four new certificates (p = 17, 29, 37, 41) are only worth anything if the same
pipeline reproduces the two published anchors. This script compares the MACHINE
lines in ../data/cert_5.out and ../data/cert_13.out against the expansions printed
in the FROZEN main.tex, which is read-only input here and is transcribed below with
its line numbers.

Frozen sources (main.tex, read-only):

  ssec:dictionary, 1555-1566
    Reg_5  = 5^2 + 3*5^3 + 3*5^4 + 3*5^5 + 3*5^6 + 4*5^7 + 4*5^8 + 3*5^9
             + 4*5^10 + 2*5^11 + 4*5^12 + ...                       [to O(5^13)]
    Reg_13 = 13^2 + 3*13^3 + 2*13^4 + 12*13^5 + 13^6 + 7*13^8 + 10*13^9
             + 10*13^11 + 9*13^12 + ...                             [to O(13^13)]

  eq:match5, 1581-1590
    height side : 1 + 4*5 + 3*5^2 + 5^3 + 5^5 + 5^6 + 2*5^8 + 2*5^10 + O(5^11)
    L-side      : 1 + 4*5 + 3*5^2 + 5^3 + 5^5 + 5^6 + O(5^7)

  eq:pred13, 1633-1636  (the PRE-REGISTERED height-side prediction, 2026-06-12)
    c_2(13) = 1 + 11*13 + 13^2 + 13^3 + 10*13^4 + 7*13^5 + 13^6 + 4*13^7
              + 6*13^8 + O(13^9)

  ssec:pred13 verification, 1641-1645  (the modular-symbol L-side at p = 13)
    c_2(13) = 1 + 11*13 + 13^2 + 13^3 + 10*13^4 + O(13^5)

Usage:  python3 control_vs_paper.py        (writes to stdout)
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "..", "data")
MLINE = re.compile(r"MACHINE\s+(\S+)\s+v=\s*(-?\d+)\s+prec=\s*(-?\d+)\s+digits=\[([^\]]*)\]")

# Transcribed from the frozen main.tex. Each entry: (tag, valuation, digits, where).
FROZEN = {
    5: [
        ("reg.pari", 2, [1, 3, 3, 3, 3, 4, 4, 3, 4, 2, 4],
         "main.tex:1557-1559  Reg_5"),
        ("reg.sage", 2, [1, 3, 3, 3, 3, 4, 4, 3, 4, 2, 4],
         "main.tex:1557-1559  Reg_5"),
        ("hs.pari", 0, [1, 4, 3, 1, 0, 1, 1, 0, 2, 0, 2],
         "main.tex:1583-1585  eq:match5 height side"),
        ("hs.sage", 0, [1, 4, 3, 1, 0, 1, 1, 0, 2, 0, 2],
         "main.tex:1583-1585  eq:match5 height side"),
        ("c2.modsym", 0, [1, 4, 3, 1, 0, 1, 1],
         "main.tex:1586-1587  eq:match5 L-side"),
    ],
    13: [
        ("reg.pari", 2, [1, 3, 2, 12, 1, 0, 7, 10, 0, 10, 9],
         "main.tex:1563-1565  Reg_13"),
        ("reg.sage", 2, [1, 3, 2, 12, 1, 0, 7, 10, 0, 10, 9],
         "main.tex:1563-1565  Reg_13"),
        ("hs.pari", 0, [1, 11, 1, 1, 10, 7, 1, 4, 6],
         "main.tex:1633-1636  eq:pred13, pre-registered height side"),
        ("hs.sage", 0, [1, 11, 1, 1, 10, 7, 1, 4, 6],
         "main.tex:1633-1636  eq:pred13, pre-registered height side"),
        ("c2.modsym", 0, [1, 11, 1, 1, 10],
         "main.tex:1641-1645  p=13 modular-symbol L-side"),
    ],
}


def read_machine(path):
    out = {}
    if not os.path.exists(path):
        return out
    with open(path) as fh:
        for ln in fh:
            m = MLINE.search(ln)
            if m:
                out[m.group(1)] = (
                    int(m.group(2)), int(m.group(3)),
                    [int(x) for x in m.group(4).replace(" ", "").split(",") if x],
                )
    return out


print("### control_vs_paper.py -- in-house recomputation vs the FROZEN main.tex")
print("main.tex is read-only input; the expansions it prints are transcribed in this")
print("script's docstring with their line numbers.")
print("")

fails = []
skips = []
for p in (5, 13):
    path = os.path.join(DATA, "cert_%d.out" % p)
    vals = read_machine(path)
    print("--- p = %d   (%s)" % (p, os.path.basename(path)))
    if not vals:
        skips.append("p=%d: no cert file" % p)
        print("    SKIPPED: %s not present" % path)
        continue
    for tag, v0, d0, where in FROZEN[p]:
        if tag not in vals:
            skips.append("p=%d %s: tag absent" % (p, tag))
            print("    %-11s SKIPPED (tag absent)   [%s]" % (tag, where))
            continue
        v, prec, d = vals[tag]
        if v != v0:
            fails.append("p=%d %s: valuation %s, paper says %s" % (p, tag, v, v0))
            print("    %-11s FAIL valuation %s vs paper %s   [%s]" % (tag, v, v0, where))
            continue
        k = min(len(d), len(d0))
        if d[:k] == d0[:k]:
            extra = ""
            if len(d) > len(d0):
                extra = "  (+%d further digits computed here)" % (len(d) - len(d0))
            print("    %-11s PASS  %d digits, v=%d%s   [%s]" % (tag, k, v, extra, where))
        else:
            fails.append("p=%d %s: %s vs paper %s" % (p, tag, d[:k], d0[:k]))
            print("    %-11s FAIL  %s vs paper %s   [%s]" % (tag, d[:k], d0[:k], where))
    print("")

print("-------------------------------------------------------------------------------")
for s in skips:
    print("SKIP: %s" % s)
if fails:
    print("RESULT: %d CONTROL CHECK(S) FAILED -- the pipeline does NOT reproduce the paper" % len(fails))
    for f in fails:
        print("   FAIL: %s" % f)
    sys.exit(1)
if skips:
    print("RESULT: all comparisons made PASS, but %d were skipped" % len(skips))
    sys.exit(0)
print("RESULT: ALL CONTROL CHECKS PASS -- the pipeline reproduces both frozen anchors")
sys.exit(0)
