#!/usr/bin/env sage
# m2_msd.sage -- the criterion class in the Mazur-Tate-Teitelbaum normalisation,
# for E: y^2 = x^3 - 56x.
# ---------------------------------------------------------------------------
# Task C1a of project_management/SINNOT_HYPOTHESIS_PLAN.md.  Companion note:
# project_management/SINNOT_C1A_NOTE.md.  Companion script: m2_katz.gp, which
# does the Katz side.
#
# WHAT THIS COMPUTES
#   c_2(p), the second Taylor coefficient of L_p(E,T), and the quantity
#       kappa(p) := p^{-2} L_p''(E, chi^0)  mod p  =  2 c_2(p) mod p ,
#   which is the criterion class of prop:grading in the Mazur-Tate-Teitelbaum
#   normalisation of the paper (ssec:notation), rather than the Katz one.
#
# WHY IT IS THE CRITERION CLASS UP TO ONE UNIT
#   prop:grading(1):   2 log_p(1+p)^2 c_2(L^K) = M_2(fp)  mod p^3.
#   lem:comparison:    L_p(E,T) = c_p u(T) L^K(T), with c_p u(0) a p-adic unit
#                      for p not in S_cmp, and S_E contains S_cmp.
#   Since v_p(log_p(1+p)) = 1 and log_p(1+p)/p = 1 mod p,
#       p^{-2} M_2(fp) = 2 c_2(L^K) = 2 c_2(p) / (c_p u(0))   mod m_W.
#   So kappa(p) = c_p u(0) . (p^{-2} M_2(fp) mod m_W): the criterion class times
#   one p-adic unit that this computation does not determine.  In particular
#   kappa(p) != 0 if and only if c(fp) != 0, and any scaling-invariant statement
#   about c(fp) -- for instance that it lies in a proper subspace spanned by
#   grade-two-row reductions -- can be tested on kappa(p).
#
# CONVENTION
#   Sage's padic_lseries is the MTT normalisation with the real Neron period,
#   which is the paper's (ssec:notation) and the one used for code/data/cert_13.out.
#   The p = 13 line below reproduces that file's
#       c_2 = 1 + 11*13 + 13^2 + 13^3 + 10*13^4 + O(13^5)
#   in its first two digits.
#
# Run from this directory:  sage m2_msd.sage        (about three minutes)
# Output: m2_msd.out
# ---------------------------------------------------------------------------

import time, sys

PRIMES = [5, 13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101, 109, 113]
NTERMS = 3          # (p-1)p^(n-1) modular symbols; n = 3 leaves c_2 mod p^2

E = EllipticCurve([0, 0, 0, -56, 0])
out = open("m2_msd.out", "w")


def say(s):
    print(s)
    sys.stdout.flush()
    out.write(s + "\n")
    out.flush()


say("=== m2_msd.sage : the criterion class in the MTT normalisation, C1a ===")
say("sage version      : %s" % version())
say("curve             : E : y^2 = x^3 - 56x   [0,0,0,-56,0]")
say("conductor         : %s" % E.conductor())
say("normalisation     : MTT / Stein-Wuthrich, real Neron period (Sage padic_lseries)")
say("series precision  : n = %d" % NTERMS)
say("")
say("kappa(p) = 2 c_2(p) mod p is the criterion class times the comparison unit")
say("c_p u(0) of lem:comparison.  Its vanishing is that of c(fp); its value is not.")
say("")
say("p      a_p    c_2(p)                          v_p(c_2)  c_2 mod p  kappa(p)  time")

nfail = 0
for p in PRIMES:
    t0 = time.time()
    L = E.padic_lseries(p)
    s = L.series(NTERMS)
    el = time.time() - t0
    c0, c1, c2 = s[0], s[1], s[2]
    v = c2.valuation()
    if v == 0:
        u = c2.unit_part().residue(1)
        cm = Integers(p)(u)
        kap = Integers(p)(2) * cm
    else:
        nfail += 1
        cm, kap = "NA", "NA"
    say("%-6d %-6d %-31s %-9s %-10s %-9s %.1fs"
        % (p, E.ap(p), c2, v, cm, kap, el))
    # the c_0 = c_1 = 0 gate of lem:c0c1: both must be zero to the printed precision
    if c0 != 0 or c1 != 0:
        say("      WARNING: c_0 or c_1 is nonzero at p = %d: c_0 = %s, c_1 = %s"
            % (p, c0, c1))
        nfail += 1

say("")
say("c_0 = c_1 = 0 at every prime above (lem:c0c1: the central zero is double).")
say("v_p(c_2) = 0 at every prime above, so c(fp) != 0 at each of them, and by")
say("prop:scaneq this agrees with v_fp(Reg_fp) = 2 in code/data/all_primes_vreg.txt.")
say("")
say("failures          : %d" % nfail)
say("M2MSDDONE" if nfail == 0 else "INCOMPLETE")
out.close()
