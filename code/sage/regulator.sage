#!/usr/bin/env sage
# regulator.sage -- height side of eq:padicbsd for E: y^2 = x^3 - 56x, by Sage.
#
# The second of two independent implementations of Reg_p.  The first is
# ../gp/regulator.gp, which uses PARI/GP's ellpadicregulator.  The two supply
# the "two implementations agreeing digit for digit" of the control on the
# normalisation at the end of ssec:scan.
#
# Usage:  sage regulator.sage <p> [prec]
#
# Prints, at the given split prime p:
#   * Reg_p from E.padic_regulator(p, prec)                (Sage, sigma-function)
#   * Reg_p as an explicit 2x2 Gram determinant of E.padic_height(p, prec) on
#     the Mordell-Weil basis P1 = (8,8), P2 = (9,15) of tab:testbed.  Equality
#     of the determinant with padic_regulator checks the saturation.
#   * the unit root alpha, the Euler factor (1-alpha^-1)^2, log_p(1+p)
#   * the height side (1-alpha^-1)^2 * Reg_p / log_p(1+p)^2, the right-hand
#     side of eq:padicbsd with #Sha(E/Q)[p^oo] = 1.  That value of the Sha
#     factor is a theorem at every split p < 30000 (cor:shavanishing).

import sys, time

p    = Integer(sys.argv[1])
prec = Integer(sys.argv[2]) if len(sys.argv) > 2 else Integer(14)

print("### Sage height side")
print("sage version      : %s" % version())
print("p                 : %s" % p)
print("working precision : O(p^%s)" % prec)

E = EllipticCurve([0, 0, 0, -56, 0])
print("curve             : %s" % E)
print("conductor         : %s" % E.conductor())
print("discriminant      : %s" % E.discriminant())
print("Tamagawa product  : %s" % E.tamagawa_product())
print("torsion order     : %s" % E.torsion_order())
print("rank              : %s" % E.rank())

ap = E.ap(p)
print("a_p               : %s" % ap)
print("#Etilde(F_p)      : %s" % (p + 1 - ap))
print("anomalous?        : %s   (False = non-anomalous, lem:noanomalous)"
      % ((p + 1 - ap) % p == 0))
print("ordinary?         : %s" % E.is_ordinary(p))
print("good reduction?   : %s" % E.has_good_reduction(p))

# --- Reg_p, Sage's own implementation -----------------------------------
t0 = time.time()
reg = E.padic_regulator(p, prec)
t1 = time.time()
print("Reg_p (Sage)      : %s" % reg)
print("v_p(Reg_p)        : %s   (prop:scaneq: 2)" % reg.valuation())
print("padic_regulator   : %.3f s" % (t1 - t0))

# --- Reg_p as a Gram determinant on the MW basis of tab:testbed ---------
# <P,Q> = ( h(P+Q) - h(P) - h(Q) ) / 2 for the quadratic form h.
P1 = E(8, 8)
P2 = E(9, 15)
print("MW basis          : %s , %s" % (P1.xy(), P2.xy()))
try:
    h  = E.padic_height(p, prec)
    h11 = h(P1); h22 = h(P2); h12 = (h(P1 + P2) - h11 - h22) / 2
    gram = matrix(2, 2, [h11, h12, h12, h22])
    detg = gram.determinant()
    print("h(P1)             : %s" % h11)
    print("h(P2)             : %s" % h22)
    print("<P1,P2>           : %s" % h12)
    print("Gram determinant  : %s" % detg)
    print("v_p(Gram det)     : %s" % detg.valuation())
    print("Gram det == Reg_p : %s" % (detg - reg).is_zero())
except Exception as e:
    print("Gram determinant  : FAILED %r" % (e,))

# --- Euler factor, log, height side -------------------------------------
Qp_ = Qp(p, prec)
R.<X> = PolynomialRing(Qp_)
rts = (X**2 - ap*X + p).roots()
units = [r for r, m in rts if r.valuation() == 0]
assert len(units) == 1, "expected exactly one unit root, got %s" % len(units)
alpha = units[0]
eul = (1 - 1/alpha)**2
lg  = Qp_(1 + p).log()
print("alpha (unit root) : %s" % alpha)
print("(1-alpha^-1)^2    : %s" % eul)
print("v_p of that       : %s   (0 = non-anomalous)" % eul.valuation())
print("log_p(1+p)        : %s" % lg)
print("v_p(log_p(1+p))   : %s   (expected 1)" % lg.valuation())

hs = eul * Qp_(reg) / lg**2
print("HEIGHT SIDE       : (1-alpha^-1)^2 * Reg_p / log_p(1+p)^2 , Sha-factor 1")
print("height side       : %s" % hs)
print("v_p(height side)  : %s   (expected 0)" % hs.valuation())

# Machine-readable digit expansions.  Format shared with ../gp/regulator.gp and
# certificates.sage so that check_agreement.py can compare the two independent
# implementations mechanically:
#      MACHINE <tag> v=<valuation> prec=<absolute precision> digits=[d0,d1,...]
# where the value is  sum_i d_i p^(v+i) + O(p^prec).
def machine(u, tag):
    v = u.valuation()
    k = u.precision_absolute()
    x = ZZ((u / p**v).lift() % p**(k - v))
    d = x.digits(p)
    d = d + [0] * ((k - v) - len(d))
    print("MACHINE %s v=%s prec=%s digits=%s" % (tag, v, k, d))

machine(hs,  "hs.sage")
machine(Qp_(reg), "reg.sage")
try:
    machine(Qp_(detg), "gram.sage")
except Exception:
    pass
print("MACHINE ap.sage v=0 prec=0 digits=[%s]" % ap)
