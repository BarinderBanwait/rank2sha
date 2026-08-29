#!/usr/bin/env sage
# certificates.sage -- the L-side certificate at a split ordinary prime p for
#                      E : y^2 = x^3 - 56x   (conductor 12544 = 2^8 * 7^2).
#
# WHAT IT CERTIFIES
#   The left-hand side of eq:padicbsd, by modular symbols at level 12544 with
#   the proved truncation bounds of Stein-Wuthrich.  This is the L-side of the
#   control on the normalisation at the end of ssec:scan, run there at p = 5
#   and p = 13:
#
#       L_p(E,T) = c_0 + c_1 T + c_2 T^2 + ...
#
#   computed by E.padic_lseries(p).series(n).  By lem:c0c1, c_0 = c_1 = 0
#   exactly for every good ordinary p, so
#
#       v_p(c_2(p)) = 0   <==>   mu_an(p) = 0 and lambda_an(p) = 2.
#
#   The script reports v_p(c_2(p)), the base-p digits of c_2(p), and the
#   truncation bound actually achieved, so that the claim "the leading digit is
#   rigorous" is checkable rather than asserted.
#
# PRECISION MODEL (Sage 10.7, sage/schemes/elliptic_curves/padic_lseries.py)
#   series(n, prec) sums (p-1)*p^(n-1) measures, and truncates coefficient j
#   to O(p^b_j) with b = _prec_bounds(n,prec) = _e_bounds(n-1,prec) - _c_bound().
#   Here rho-bar_{E,p} is irreducible for every odd p (the isogeny class of E is
#   two curves joined by a 2-isogeny), so _c_bound() = 0, and for 2 <= j < p one
#   gets b_j = n - 1.  Hence c_2 is certified modulo p^(n-1): n-1 base-p digits.
#   The constant term is truncated at padic_prec - 2 = n + 2.
#   COST is therefore (p-1)*p^(n-1) modular-symbol evaluations -- exponential
#   in the number of digits requested.  n = 2 already certifies v_p(c_2) = 0.
#
# It also recomputes the right-hand side (1-alpha^-1)^2 * Reg_p / log_p(1+p)^2
# with #Sha(E/Q)[p^oo] = 1 (cor:shavanishing) and prints the digit-for-digit
# comparison of the two sides of eq:padicbsd.  The two independent
# implementations of Reg_p itself are regulator.sage (Sage) and
# ../gp/regulator.gp (PARI/GP).
#
# Usage:  sage certificates.sage <p> <n> [prec_T] [cap_seconds] [implementation]
#           p              the split ordinary prime
#           n              approximation order; c_2 is certified mod p^(n-1)
#           prec_T         number of T-coefficients to keep      (default 5)
#           cap_seconds    hard cap on the series computation    (default 0 = none)
#           implementation modular symbol implementation         (default eclib)

import sys, time

p    = Integer(sys.argv[1])
n    = Integer(sys.argv[2])
precT = Integer(sys.argv[3]) if len(sys.argv) > 3 else Integer(5)
cap   = Integer(sys.argv[4]) if len(sys.argv) > 4 else Integer(0)
impl  = sys.argv[5] if len(sys.argv) > 5 else 'eclib'

print("### L-side certificate, modular symbols at level 12544")
print("sage version      : %s" % version())
print("p                 : %s" % p)
print("n (approx order)  : %s" % n)
print("prec_T            : %s" % precT)
print("implementation    : %s" % impl)
print("hard cap (s)      : %s" % (cap if cap else "none"))

E = EllipticCurve([0, 0, 0, -56, 0])
print("curve             : %s" % E)
print("conductor         : %s" % E.conductor())
print("Tamagawa product  : %s" % E.tamagawa_product())
print("torsion order     : %s" % E.torsion_order())
print("prod c_v/#tors^2  : %s   (eq:padicbsd normalising factor)"
      % (E.tamagawa_product() / E.torsion_order()**2))

ap = E.ap(p)
print("a_p               : %s" % ap)
print("#Etilde(F_p)      : %s" % (p + 1 - ap))
print("good reduction    : %s" % E.has_good_reduction(p))
print("ordinary          : %s" % E.is_ordinary(p))
print("p = 1 mod 4       : %s   (split in K = Q(i))" % (p % 4 == 1))
print("anomalous         : %s   (lem:noanomalous: never, for this curve)"
      % ((p + 1 - ap) % p == 0))
print("rhobar irreducible: %s   (gives _c_bound() = 0 below)"
      % E.galois_representation().is_irreducible(p))

Lp = E.padic_lseries(p, implementation=impl)
print("Lp object         : %s" % Lp)
print("normalisation     : L_p(E,1) = (1-1/alpha)^2 L(E,1)/Omega_E   [Stein-Wuthrich]")

cb = Lp._c_bound()
print("_c_bound()        : %s   (denominator bound on the modular symbols)" % cb)
bounds = Lp._prec_bounds(n, precT)
print("_prec_bounds(n,precT): %s" % bounds)
print("   => provable truncation: coeff j of L_p(E,T) is correct mod p^bounds[j]")
print("summands in the Riemann sum: (p-1)*p^(n-1) = %s" % ((p - 1) * p**(n - 1)))

t0 = time.time()
ser = None
if cap:
    alarm(float(cap))
try:
    ser = Lp.series(n, prec=precT)
    if cap:
        cancel_alarm()
except AlarmInterrupt:
    print("CAP HIT            : series(%s, prec=%s) exceeded %s s -- NO CERTIFICATE AT THIS n"
          % (n, precT, cap))
    print("elapsed           : %.1f s" % (time.time() - t0))
    sys.exit(2)
t1 = time.time()
print("series runtime    : %.1f s" % (t1 - t0))
print("L_p(E,T)          : %s" % ser)

co = ser.list()
for j in range(min(4, len(co))):
    print("c_%s               : %s" % (j, co[j]))

if len(co) < 3:
    print("FATAL: fewer than three T-coefficients returned.")
    sys.exit(3)

c0, c1, c2 = co[0], co[1], co[2]
print("c_0 precision     : O(p^%s)   (lem:c0c1 gives c_0 = 0 exactly)" % c0.precision_absolute())
print("c_1 precision     : O(p^%s)   (lem:c0c1 gives c_1 = 0 exactly)" % c1.precision_absolute())
print("c_2 precision     : O(p^%s)   <-- the truncation bound achieved" % c2.precision_absolute())
print("c_0 is zero to that precision : %s" % (c0.is_zero()))
print("c_1 is zero to that precision : %s" % (c1.is_zero()))

digitsc2 = None
if c2.is_zero():
    print("c_2 valuation     : >= %s  (c_2 indistinguishable from 0 at this precision)"
          % c2.precision_absolute())
    print("CERTIFICATE       : NOT OBTAINED at n = %s -- increase n" % n)
    vc2 = None
else:
    vc2 = c2.valuation()
    print("v_p(c_2(p))       : %s" % vc2)
    x = ZZ((c2 / p**vc2).lift() % p**(c2.precision_absolute() - vc2))
    d = x.digits(p)
    d = d + [0] * ((c2.precision_absolute() - vc2) - len(d))
    digitsc2 = d
    print("c_2 digits (p^%s first, up to O(p^%s)) : %s"
          % (vc2, c2.precision_absolute(), d))
    print("MACHINE c2.modsym v=%s prec=%s digits=%s"
          % (vc2, c2.precision_absolute(), d))
    if vc2 == 0:
        print("CERTIFICATE       : v_p(c_2(p)) = 0  -- leading digit %s, rigorous to O(p^%s)"
              % (d[0], c2.precision_absolute()))
        print("  => by lem:c0c1 (c_0 = c_1 = 0 exactly), L_p(E,T) = T^2 (c_2 + ...) with")
        print("     c_2 in Z_p^*, hence  mu_an(p) = 0  and  lambda_an(p) = 2.")
        print("LAMBDA_AN         : 2")
        print("MU_AN             : 0")
        print("MACHINE lambda_an v=0 prec=0 digits=[2]")
        print("MACHINE mu_an v=0 prec=0 digits=[0]")
    else:
        print("CERTIFICATE       : FAILED -- v_p(c_2(p)) = %s != 0" % vc2)
        print("LAMBDA_AN         : > 2  (or mu > 0)")
        print("MU_AN             : ?")

# ---------------------------------------------------------------------------
# Right-hand side of eq:padicbsd, and the comparison of the two sides.
# The Mordell-Weil basis is that of tab:testbed, P1 = (8,8), P2 = (9,15);
# E.padic_regulator selects its own basis, so it is not named here.
# ---------------------------------------------------------------------------
hprec = max(Integer(14), n + 4)
Qp_ = Qp(p, hprec)
R.<X> = PolynomialRing(Qp_)
units = [r for r, m in (X**2 - ap*X + p).roots() if r.valuation() == 0]
assert len(units) == 1
alpha = units[0]
eul = (1 - 1/alpha)**2
lg = Qp_(1 + p).log()
reg = E.padic_regulator(p, hprec)
hs = eul * Qp_(reg) / lg**2

print("### height side (Sage), Sha-factor 1")
print("alpha             : %s" % alpha)
print("(1-alpha^-1)^2    : %s" % eul)
print("Reg_p             : %s" % reg)
print("v_p(Reg_p)        : %s" % reg.valuation())
print("log_p(1+p)        : %s" % lg)
print("height side       : %s" % hs)
print("v_p(height side)  : %s" % hs.valuation())

vh = hs.valuation()
xh = ZZ((hs / p**vh).lift() % p**(hs.precision_absolute() - vh))
dh = xh.digits(p)
dh = dh + [0] * ((hs.precision_absolute() - vh) - len(dh))
print("height side digits (p^%s first, up to O(p^%s)) : %s"
      % (vh, hs.precision_absolute(), dh))
print("MACHINE hs.cert v=%s prec=%s digits=%s" % (vh, hs.precision_absolute(), dh))
print("MACHINE reg.cert v=%s prec=%s digits=%s"
      % (reg.valuation(), reg.precision_absolute(),
         (ZZ((Qp_(reg) / p**reg.valuation()).lift()
             % p**(Qp_(reg).precision_absolute() - reg.valuation())).digits(p)
          + [0] * (Qp_(reg).precision_absolute() - reg.valuation()))[
             :Qp_(reg).precision_absolute() - reg.valuation()]))

print("### eq:padicbsd, two sides compared at p = %s" % p)
if digitsc2 is None:
    print("MATCH             : not available (no c_2 certificate at this n)")
else:
    k = min(len(dh), len(digitsc2))
    agree = (vh == vc2) and all(dh[i] == digitsc2[i] for i in range(k))
    print("digits compared   : %s" % k)
    print("height side       : %s" % dh[:k])
    print("L-side (mod syms) : %s" % digitsc2[:k])
    print("valuations        : height %s , L-side %s" % (vh, vc2))
    print("MATCH             : %s" % ("YES, all %s digits" % k if agree else "NO -- DISAGREEMENT"))
