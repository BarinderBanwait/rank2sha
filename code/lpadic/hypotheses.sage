#!/usr/bin/env sage
# hypotheses.sage -- the five NON-CERTIFICATE hypotheses of prop:consequence
# (main.tex:1065, via the excluded set eq:Sexc at main.tex:1049) at the six split
# ordinary primes of E : y^2 = x^3 - 56x.
#
# The sixth hypothesis, v_p(c_2(p)) = 0, is the certificate and is produced by
# certificates.sage; it is NOT computed here.
#
# TASK_BOARD_SERIES.md, "LMFDB Iwasawa invariants" item 4, states that the five
# non-certificate hypotheses were checked by hand at p = 17, 29, 37, 41. This
# script tabulates them machine-checkably at all six primes so that the report's
# six-row table traces to an output file rather than to a hand check.
#
# Usage:  sage hypotheses.sage        (writes to stdout; run.sh is not involved)

import sys

PRIMES = [5, 13, 17, 29, 37, 41]

print("### prop:consequence -- the five non-certificate hypotheses")
print("sage version      : %s" % version())

E = EllipticCurve([0, 0, 0, -56, 0])
K.<i> = QuadraticField(-1)

N     = E.conductor()
cprod = E.tamagawa_product()
tors  = E.torsion_order()
dK    = K.discriminant()

print("curve             : %s" % E)
print("minimal model     : %s" % list(E.a_invariants()))
print("conductor N       : %s = %s" % (N, factor(N)))
print("discriminant      : %s = %s" % (E.discriminant(), factor(E.discriminant())))
print("j-invariant       : %s" % E.j_invariant())
print("CM                : by the order of discriminant %s in K = Q(i)" % E.cm_discriminant())
print("rank              : %s" % E.rank())
print("torsion order     : %s" % tors)
print("Tamagawa product  : %s" % cprod)
print("K = Q(i), d_K     : %s" % dK)

M = 6 * N * cprod * tors * abs(dK)
print("6N*prod c_v*#tors*|d_K| = 6*%s*%s*%s*%s = %s = %s" % (N, cprod, tors, abs(dK), M, factor(M)))
print("   => the eq:Sexc divisibility condition is supported on %s"
      % sorted(q for q, e in factor(M)))

# isogeny class: the irreducibility input
iso = E.isogeny_class()
print("isogeny class     : %s curves, isogeny matrix degrees %s"
      % (len(iso.curves), sorted(set(sum([[d for d in row] for row in iso.matrix()], [])))))
print("   => every isogeny in the class has 2-power degree, so E admits no rational")
print("      p-isogeny for odd p, so rhobar_{E,p} is irreducible for every odd p.")

print("")
hdr = ("%-4s %-8s %-9s %-8s %-12s %-13s %-11s %-10s"
       % ("p", "p%4", "a_p", "#E(F_p)", "good+ord", "non-anom", "rhobar irr", "gcd(p,M)"))
print(hdr)
print("-" * len(hdr))
allok = True
for p in PRIMES:
    p = Integer(p)
    ap = E.ap(p)
    Np = p + 1 - ap
    good = E.has_good_reduction(p)
    ordy = E.is_ordinary(p)
    split = (p % 4 == 1)
    nonanom = (Np % p != 0)
    irr = E.galois_representation().is_irreducible(p)
    g = gcd(p, M)
    ok = good and ordy and split and nonanom and irr and (g == 1)
    allok = allok and ok
    print("%-4s %-8s %-9s %-8s %-12s %-13s %-11s %-10s"
          % (p, p % 4, ap, Np, "%s/%s" % (good, ordy), nonanom, irr, g))
    print("     MACHINE hyp p=%s split=%s ap=%s NEFp=%s good=%s ordinary=%s "
          "nonanomalous=%s irreducible=%s gcd_p_M=%s all=%s"
          % (p, split, ap, Np, good, ordy, nonanom, irr, g, ok))

print("")
print("comparison constant (lem:comparison, main.tex:985): for this curve the CM")
print("curve underlying the Katz measure may be taken to be E itself, and the")
print("period ratio is supported on {2,7} (main.tex remark at 1037-1046), so")
print("v_p(c_p) = 0 at EVERY split p. Not a computation; quoted from the frozen paper.")
print("")
print("### effective settings of E.padic_lseries, recorded for provenance")
print("Sage default chain: padics.py:109 padic_lseries(p, normalize=None,")
print("implementation='eclib'), then _normalize_padic_lseries (padics.py:77-94)")
print("maps normalize=None -> 'L_ratio'.")
for p in [Integer(x) for x in PRIMES]:
    Lp = E.padic_lseries(p)
    print("  p = %-3s implementation = %-6s normalize = %-8s alpha = %s"
          % (p, Lp._implementation, Lp._normalize, Lp.alpha(8)))
print("")
print("### software")
print("sage              : %s" % version())
try:
    import sage.libs.eclib as _ec
    print("eclib module      : %s" % _ec.__file__)
except Exception as e:
    print("eclib module      : (not introspectable) %r" % (e,))
print("pari version      : %s" % (pari.version(),))
print("")
print("ALL FIVE NON-CERTIFICATE HYPOTHESES HOLD AT ALL SIX PRIMES: %s" % allok)
print("MACHINE hyp_all v=0 prec=0 digits=[%s]" % (1 if allok else 0))
