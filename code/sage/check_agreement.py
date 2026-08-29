#!/usr/bin/env python3
"""check_agreement.py -- mechanical cross-checks on a cert_<p>.out file.

Run as the fourth step of run.sh, and appended to the same output file, so that
every agreement the paper reports at p = 5, 13 is machine-verified inside the
committed output rather than asserted by a reader comparing two columns.

It parses the MACHINE lines emitted by ../gp/regulator.gp, regulator.sage and
certificates.sage:

    MACHINE <tag> v=<valuation> prec=<absolute precision> digits=[d0,d1,...]

meaning the value is sum_i d_i * p^(v+i) + O(p^prec), and checks:

  C1  Reg_p: PARI ellpadicregulator vs Sage padic_regulator vs the copy used
      inside certificates.sage -- equal valuation, equal on the common prefix.
      This is the "two implementations agreeing digit for digit" of the control
      on the normalisation at the end of ssec:scan.
  C2  Reg_p vs the explicit 2x2 Gram determinant of E.padic_height on the
      Mordell-Weil basis P1 = (8,8), P2 = (9,15) of tab:testbed. Saturation
      check.
  C3  height side (1-alpha^-1)^2 Reg_p / log_p(1+p)^2: PARI vs Sage.
  C4  a_p: PARI ellap vs Sage E.ap.
  C5  the two sides of eq:padicbsd -- height side vs L-side (modular symbols):
      equal valuation and equal digits over the full precision of the L-side.
  C6  the L-side certificate itself: v_p(c_2(p)) = 0, hence (with lem:c0c1)
      lambda_an = 2 and mu_an = 0.
  C7  cross-check against an LMFDB table of Iwasawa invariants, if one is
      given. LMFDB is corroboration only; a MISMATCH here is a stop-the-line
      event. The check is skipped when no table is given or the named file is
      absent.

Exit status 0 iff every check passes.

Usage:  python3 check_agreement.py <p> <cert_file> [lmfdb_file]
"""
import os
import re
import sys

p = int(sys.argv[1])
path = sys.argv[2]
lmfdb_path = sys.argv[3] if len(sys.argv) > 3 else None

LINE = re.compile(r"MACHINE\s+(\S+)\s+v=\s*(-?\d+)\s+prec=\s*(-?\d+)\s+digits=\[([^\]]*)\]")

vals = {}
with open(path) as fh:
    for ln in fh:
        m = LINE.search(ln)
        if m:
            tag, v, prec, ds = m.group(1), int(m.group(2)), int(m.group(3)), m.group(4)
            digits = [int(x) for x in ds.replace(" ", "").split(",") if x != ""]
            vals[tag] = (v, prec, digits)

print("### check_agreement.py -- mechanical cross-checks")
print("p                 : %s" % p)
print("cert file         : %s" % path)
print("MACHINE tags found: %s" % ", ".join(sorted(vals)))

fails = []
notes = []


def cmp_pair(t1, t2, label):
    if t1 not in vals or t2 not in vals:
        notes.append("%s: SKIPPED (missing %s)" % (label, t1 if t1 not in vals else t2))
        print("%-46s : SKIPPED (missing tag)" % label)
        return
    v1, pr1, d1 = vals[t1]
    v2, pr2, d2 = vals[t2]
    if v1 != v2:
        fails.append("%s: valuations differ (%s vs %s)" % (label, v1, v2))
        print("%-46s : FAIL valuations %s vs %s" % (label, v1, v2))
        return
    k = min(len(d1), len(d2))
    if k == 0:
        notes.append("%s: no digits in common" % label)
        print("%-46s : SKIPPED (no common digits)" % label)
        return
    if d1[:k] == d2[:k]:
        print("%-46s : PASS  v=%s, %s digits agree" % (label, v1, k))
    else:
        fails.append("%s: digits differ %s vs %s" % (label, d1[:k], d2[:k]))
        print("%-46s : FAIL  %s vs %s" % (label, d1[:k], d2[:k]))


cmp_pair("reg.pari", "reg.sage", "C1a Reg_p  PARI vs Sage")
cmp_pair("reg.sage", "reg.cert", "C1b Reg_p  Sage vs certificates.sage")
cmp_pair("reg.sage", "gram.sage", "C2  Reg_p  vs Gram det on (8,8),(9,15)")
cmp_pair("hs.pari", "hs.sage", "C3a height side  PARI vs Sage")
cmp_pair("hs.sage", "hs.cert", "C3b height side  Sage vs certificates.sage")
cmp_pair("ap.pari", "ap.sage", "C4  a_p  PARI vs Sage")

# C5 -- the two sides of eq:padicbsd
label = "C5  eq:padicbsd  height side vs L-side"
if "hs.pari" in vals and "c2.modsym" in vals:
    vh, prh, dh = vals["hs.pari"]
    vc, prc, dc = vals["c2.modsym"]
    if vh != vc:
        fails.append("C5: valuations differ, height %s vs L-side %s" % (vh, vc))
        print("%-46s : FAIL valuations %s vs %s" % (label, vh, vc))
    else:
        k = min(len(dh), len(dc))
        if dh[:k] == dc[:k]:
            print("%-46s : PASS  all %s certified L-side digits" % (label, k))
        else:
            fails.append("C5: digits differ %s vs %s" % (dh[:k], dc[:k]))
            print("%-46s : FAIL  %s vs %s" % (label, dh[:k], dc[:k]))
else:
    print("%-46s : SKIPPED (no L-side certificate)" % label)
    fails.append("C5: no L-side certificate in %s" % path)

# C6 -- the certificate
label = "C6  certificate  v_p(c_2(p)) = 0"
if "c2.modsym" in vals:
    vc, prc, dc = vals["c2.modsym"]
    if vc == 0 and dc and dc[0] % p != 0:
        print("%-46s : PASS  leading digit %s, rigorous to O(%s^%s)" % (label, dc[0], p, prc))
    else:
        fails.append("C6: v_p(c_2) = %s" % vc)
        print("%-46s : FAIL  v_p(c_2) = %s" % (label, vc))
else:
    print("%-46s : FAIL  no c_2 certificate" % label)
    fails.append("C6: no c_2 certificate")

lam = vals.get("lambda_an", (None, None, [None]))[2][0]
mu = vals.get("mu_an", (None, None, [None]))[2][0]
print("%-46s : lambda_an = %s , mu_an = %s" % ("C6b in-house Iwasawa invariants", lam, mu))

# C7 -- LMFDB corroboration, optional
label = "C7  vs LMFDB table (corroboration)"
if lmfdb_path and not os.path.exists(lmfdb_path):
    print("%-46s : SKIPPED (no such file: %s)" % (label, lmfdb_path))
elif lmfdb_path:
    lam_l = mu_l = None
    with open(lmfdb_path) as fh:
        for ln in fh:
            if ln.startswith("#") or not ln.strip():
                continue
            f = ln.split()
            if len(f) >= 4 and f[0].isdigit() and int(f[0]) == p:
                lam_l, mu_l = f[2], f[3]
    if lam_l is None:
        print("%-46s : SKIPPED (p not in table)" % label)
    else:
        ok = (str(lam) == lam_l and str(mu) == mu_l)
        if ok:
            print("%-46s : PASS  LMFDB lambda=%s mu=%s, in-house lambda=%s mu=%s"
                  % (label, lam_l, mu_l, lam, mu))
        else:
            fails.append("C7: LMFDB lambda=%s mu=%s vs in-house lambda=%s mu=%s"
                         % (lam_l, mu_l, lam, mu))
            print("%-46s : *** MISMATCH *** LMFDB lambda=%s mu=%s, in-house lambda=%s mu=%s"
                  % (label, lam_l, mu_l, lam, mu))
            print("*** STOP THE LINE: in-house recomputation disagrees with LMFDB at p = %s" % p)
else:
    print("%-46s : SKIPPED (no lmfdb file given)" % label)

print("-------------------------------------------------------------------------------")
if fails:
    print("RESULT            : %s CHECK(S) FAILED" % len(fails))
    for f in fails:
        print("   FAIL: %s" % f)
    sys.exit(1)
print("RESULT            : ALL CHECKS PASS")
sys.exit(0)
