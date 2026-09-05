#!/usr/bin/env sage
# m2_msd_family.sage -- the criterion class in the Mazur-Tate-Teitelbaum
# normalisation, for E_D : y^2 = x^3 - D x.
# ---------------------------------------------------------------------------
# sage/m2_msd.sage does the same computation for D = 56 alone.  Backs the kappa
# column of the bracket table of paper Section 8; gp/m2_w1_family.gp reads the
# KAPPA lines of the output and gates v_p(B_alg) against them.
#
# WHAT THIS COMPUTES
#   c_2(p), the second Taylor coefficient of L_p(E,T), and the quantity
#       kappa(p) := p^{-2} L_p''(E, chi^0)  mod p  =  2 c_2(p) mod p ,
#   which is the criterion class of prop:grading in the Mazur-Tate-Teitelbaum
#   normalisation of the paper (ssec:notation), rather than the Katz one.
#   By prop:grading(1) and lem:comparison, kappa(p) is the criterion class times
#   the p-adic unit c_p u(0), so kappa(p) != 0 if and only if c(fp) != 0.
#
#   NTERMS = 3 gives (p-1)p^2 modular symbols, which certifies c_2 modulo p^2, so
#   both kappa(p) != 0 and kappa(p) = 0 are rigorous conclusions.  A prime with
#   v_p(c_2) > 0 is not a failure: kappa(p) = 0 in F_p is then the statement that
#   the unit condition fails at p, and (W2) predicts v_p(B_alg) >= 3 there.
#
# Run from this directory:   D=-33 PRIMES=37,17,13 sage m2_msd_family.sage
# Parameters from the environment:
#     D       the curve y^2 = x^3 - D x     default 56
#     PRIMES  comma-separated split primes  default "5,13,17,29,37"
#     NTERMS  the n of L.series(n)          default 3
#     OUT     output file                   default ../data/m2_msd_D<D>.out
# Cost is (p-1)p^(NTERMS-1) modular symbols per prime, seconds to a few minutes.
# Output is staged to <file>.partial and moved onto the committed file at the end.
# ---------------------------------------------------------------------------

import os, sys, time

D = ZZ(os.environ.get("D", "56"))
PRIMES = [ZZ(s) for s in os.environ.get("PRIMES", "5,13,17,29,37").split(",")]
NTERMS = int(os.environ.get("NTERMS", "3"))
OUT = os.environ.get("OUT", "../data/m2_msd_D%s.out" % D)
TMP = OUT + ".partial"

E = EllipticCurve([0, 0, 0, -D, 0])
out = open(TMP, "w")


def say(s):
    print(s)
    sys.stdout.flush()
    out.write(s + "\n")
    out.flush()


say("=== m2_msd_family.sage : the criterion class in the MTT normalisation ===")
say("sage version      : %s" % version())
say("curve             : E : y^2 = x^3 - %sx   [0,0,0,%s,0]" % (D, -D))
say("conductor         : %s" % E.conductor())
say("normalisation     : MTT / Stein-Wuthrich, real Neron period (Sage padic_lseries)")
say("series precision  : n = %d, so c_2 is certified modulo p^%d" % (NTERMS, NTERMS - 1))
say("")
say("kappa(p) = 2 c_2(p) mod p is the criterion class times the comparison unit")
say("c_p u(0) of lem:comparison.  Its vanishing is that of c(fp); its value is not.")
say("The KAPPA lines below are the machine-readable form read by gp/m2_w1_family.gp.")
say("")
say("p      a_p    c_2(p)                          v_p(c_2)  c_2 mod p  kappa(p)  time")

nfail = 0
rows = []
for p in PRIMES:
    t0 = time.time()
    if p % 4 != 1 or E.conductor() % p == 0:
        say("%-6d skipped: not a split prime of good reduction" % p)
        continue
    L = E.padic_lseries(p)
    s = L.series(NTERMS)
    el = time.time() - t0
    c0, c1, c2 = s[0], s[1], s[2]
    v = c2.valuation()
    if v == 0:
        cm = Integers(p)(c2.unit_part().residue(1))
        kap = Integers(p)(2) * cm
    else:
        cm, kap = "NA", 0
    rows.append((p, kap))
    say("%-6d %-6d %-31s %-9s %-10s %-9s %.1fs"
        % (p, E.ap(p), c2, v, cm, kap, el))
    # the c_0 = c_1 = 0 gate of lem:c0c1: both must be zero to the printed precision
    if c0 != 0 or c1 != 0:
        say("      WARNING: c_0 or c_1 is nonzero at p = %d: c_0 = %s, c_1 = %s"
            % (p, c0, c1))
        nfail += 1

say("")
say("c_0 = c_1 = 0 at every prime above (lem:c0c1: the central zero is double).")
say("")
for p, kap in rows:
    say("KAPPA %d %s" % (p, kap))
say("")
say("failures          : %d" % nfail)
say("M2MSDDONE" if nfail == 0 else "INCOMPLETE")
out.close()
if nfail == 0:
    os.replace(TMP, OUT)
else:
    sys.exit(1)
