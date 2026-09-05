#!/usr/bin/env python3
"""verify_unit_ms.py -- check the modular-symbol unit condition against the scan.

Reads the five files ../data/unit_ms_D<D>.txt written by unit_ms_family.py, the
regulator scans they are compared with, the excluded sets of
../data/excluded_set_family.out, and the LMFDB rows of
../data/lmfdb_five_curves.json.  Recomputes nothing.

Checks, per curve:
  (1) every line of the unit_ms file parses, and its primes are exactly the
      split primes 5 <= p < 1000 of good reduction;
  (2) at every such prime outside S_E, the unit condition v_p(c_2) = 0 holds if
      and only if the scan records v_p(Reg_p) = 2;
  (3) the primes with v_p(c_2) > 0 are listed, each with the valuation the scan
      records; by (2) these are exactly the primes where that valuation is not 2;
  (4) the split primes of S_E, which are the anomalous fives of
      lem:noanomalous, are reported separately and excluded from (2) and (3).

And once, across the five curves:
  (5) the valuation of the p-adic regulator that the LMFDB stores for each
      isogeny class at p < 100 agrees with the scan.

Exits 0 if every check passes.  Requires Python 3 only.  Run from this
directory:  python3 verify_unit_ms.py
"""

import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, os.pardir, "data")

PBOUND = 1000
CURVES = [56, 17, -33, -34, -39]
SCAN = {56: "all_primes_vreg.txt", 17: "scan_D17.txt", -33: "scan_D-33.txt",
        -34: "scan_D-34.txt", -39: "scan_D-39.txt"}
# lmfdb_iso of each curve, from ../data/lmfdb_five_curves.json
ISO = {56: "12544.g", 17: "9248.c", -33: "69696.i", -34: "73984.d", -39: "48672.n"}
CONDUCTOR = {56: 12544, 17: 9248, -33: 69696, -34: 73984, -39: 48672}

fails = []


def sieve(limit):
    is_p = [True] * (limit + 1)
    is_p[0] = is_p[1] = False
    i = 2
    while i * i <= limit:
        if is_p[i]:
            for j in range(i * i, limit + 1, i):
                is_p[j] = False
        i += 1
    return is_p


IS_PRIME = sieve(PBOUND)


def read_scan(name):
    """{p: v} from a scan file of lines "p v" or "p v FLAG"."""
    out = {}
    with open(os.path.join(DATA, name)) as fh:
        for ln in fh:
            f = ln.split()
            if len(f) >= 2 and f[0].isdigit():
                out[int(f[0])] = int(f[1])
    return out


def read_unit_ms(D):
    """{p: (v, certified precision)} from ../data/unit_ms_D<D>.txt."""
    out = {}
    path = os.path.join(DATA, "unit_ms_D%s.txt" % D)
    with open(path) as fh:
        for ln in fh:
            f = ln.split()
            if len(f) >= 6 and f[0].isdigit():
                p = int(f[0])
                v = f[3]
                out[p] = (0 if v == "0" else v, f[5])
    return out


def read_excluded():
    """{D: [split primes of good reduction in S_E]} from excluded_set_family.out."""
    out = {}
    cur = None
    with open(os.path.join(DATA, "excluded_set_family.out")) as fh:
        for ln in fh:
            m = re.match(r"=== D = (-?\d+)", ln.strip())
            if m:
                cur = int(m.group(1))
            elif cur is not None and "of those, of good reduction" in ln:
                body = ln.split(":", 1)[1].strip().strip("{}")
                out[cur] = [int(x) for x in body.split(",") if x.strip()]
    return out


EXC = read_excluded()
print("### verify_unit_ms.py -- the modular-symbol unit condition against the scan")
print("excluded sets read from data/excluded_set_family.out: %s"
      % {d: EXC.get(d) for d in CURVES})
print("")

for D in CURVES:
    ums = read_unit_ms(D)
    scan = read_scan(SCAN[D])
    excl = set(EXC.get(D, []))
    N = CONDUCTOR[D]

    want = [p for p in range(5, PBOUND) if IS_PRIME[p] and p % 4 == 1 and N % p != 0]
    if sorted(ums) != want:
        fails.append("D = %s: the primes of unit_ms_D%s.txt are not the split primes "
                     "below %s of good reduction" % (D, D, PBOUND))
        print("D = %-4s (1) prime range                      : FAIL" % D)
    else:
        print("D = %-4s (1) prime range                      : PASS  %d primes"
              % (D, len(want)))

    bad = []
    nunit = 0
    exc = []
    for p in want:
        if p in excl:
            continue
        v, _ = ums[p]
        if p not in scan:
            fails.append("D = %s: p = %s missing from %s" % (D, p, SCAN[D]))
            continue
        unit = (v == 0)
        if unit:
            nunit += 1
        else:
            exc.append((p, v, scan[p]))
        if unit != (scan[p] == 2):
            bad.append((p, v, scan[p]))
    if bad:
        fails.append("D = %s: unit condition and scan disagree at %s" % (D, bad))
        print("D = %-4s (2) unit condition <=> v(Reg) = 2    : FAIL  %s" % (D, bad))
    else:
        print("D = %-4s (2) unit condition <=> v(Reg) = 2    : PASS  %d primes outside S_E, "
              "%d with c_2 a unit" % (D, len(want) - len(excl & set(want)), nunit))
    print("D = %-4s (3) primes with v_p(c_2) > 0         : %s"
          % (D, [(p, str(v), "v(Reg) = %d" % r) for p, v, r in exc] or "none"))
    print("D = %-4s (4) split primes of S_E, reported apart: %s"
          % (D, [(p, "v_p(c_2) = %s" % ums[p][0], "v(Reg) = %s" % scan.get(p))
                 for p in sorted(excl) if p in ums] or "none"))
    print("")

# (5) the LMFDB valuation of the p-adic regulator against the scan
with open(os.path.join(DATA, "lmfdb_five_curves.json")) as fh:
    pad = json.load(fh)["ec_padic_val"]
nchecked = 0
pbad = []
for D in CURVES:
    scan = read_scan(SCAN[D])
    for ps, v in sorted(pad.get(ISO[D], {}).items(), key=lambda kv: int(kv[0])):
        p = int(ps)
        if p not in scan:
            continue
        nchecked += 1
        if int(v) != scan[p]:
            pbad.append((D, p, int(v), scan[p]))
if pbad:
    fails.append("LMFDB p-adic regulator valuations disagree with the scan at %s" % pbad)
    print("(5) LMFDB ec_padic val vs the scan          : FAIL  %s" % pbad)
else:
    print("(5) LMFDB ec_padic val vs the scan          : PASS  %d values, p < 100" % nchecked)

print("")
if fails:
    print("RESULT            : %d CHECK(S) FAILED" % len(fails))
    for f in fails:
        print("   FAIL: %s" % f)
    sys.exit(1)
print("RESULT            : ALL CHECKS PASS")
sys.exit(0)
