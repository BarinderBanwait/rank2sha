#!/usr/bin/env sage
# reach.sage -- the R4 reach-and-cost measurement for
#               E : y^2 = x^3 - 56x   (conductor 12544 = 2^8 * 7^2).
#
# WHAT THIS IS, AND WHAT IT IS NOT
#   This script answers one question and no other: how far past p = 41 does the
#   arithmetic input of prop:criterion remain AVAILABLE, and what does it COST?
#   It computes v_p(c_2(p)) at the MINIMAL approximation order n that certifies
#   it, for split primes beyond the six treated in sec:certificates, and records
#   the wall-clock time of each.
#
#   It is NOT a certificate run.  run.sh / certificates.sage do the certificate:
#   two independent implementations of Reg_p, the Gram-determinant saturation
#   cross-check, the eq:match5 height-vs-L comparison, and check_agreement.py's
#   C1-C7.  This script runs one implementation at minimal precision and does
#   none of those checks.  Nothing it prints enters a theorem.  See
#   ss:standards and ssec:repro.
#
# COST MODEL (Sage 10.7, sage/schemes/elliptic_curves/padic_lseries.py)
#   series(n, prec) runs the double loop
#       for j in range(p^(n-1)):  for a in range(1, p):  ... measure(...)
#   i.e. exactly (p-1)*p^(n-1) summands, and truncates the coefficient of T^j to
#   O(p^b_j) with b = _e_bounds(n-1, prec) - _c_bound().  For this curve
#   _c_bound() = 0 at every odd p (rhobar_{E,p} is irreducible: the isogeny class
#   is two curves joined by a 2-isogeny), and _e_bounds(n-1,prec)[j] = n-1 for
#   2 <= j < p.  So c_2 is certified modulo p^(n-1): n-1 base-p digits, at a cost
#   of (p-1)*p^(n-1) summands.  n = 2 gives one digit, which is all the criterion
#   consumes: a nonzero leading digit IS v_p(c_2(p)) = 0.
#
# THE ONE-OFF
#   The space of modular symbols at level 12544 is built once, by
#   E.modular_symbol(sign=+1, implementation='eclib', normalize='L_ratio'), and
#   is cached on E.  Every subsequent E.padic_lseries(p) reuses it.  This script
#   times that one-off SEPARATELY from the per-prime cost, and prints the
#   construction time of each padic_lseries object so that the reuse is visible
#   rather than asserted.
#
# Usage:  sage reach.sage <pmin> <pmax> [precT] [cap_per_prime_s] [budget_s] [nmax]
#           pmin, pmax        inclusive range of primes to scan
#           precT             number of T-coefficients to keep    (default 5)
#           cap_per_prime_s   hard cap on one series() call       (default 0 = none)
#           budget_s          global wall-clock budget; the scan stops cleanly at
#                             the first prime that would start after it expires
#                                                                 (default 0 = none)
#           nmax              largest approximation order to try   (default 3)
#
# CAPS.  `timeout` is not on the local macOS PATH, so caps are enforced inside
# Sage by alarm(), exactly as in certificates.sage.  A prime whose series() call
# hits the cap is recorded as CAP HIT with the stage it reached and the scan
# stops; a prime is never silently dropped.

import sys, time

pmin  = Integer(sys.argv[1])
pmax  = Integer(sys.argv[2])
precT = Integer(sys.argv[3]) if len(sys.argv) > 3 else Integer(5)
cap   = Integer(sys.argv[4]) if len(sys.argv) > 4 else Integer(0)
budget = Integer(sys.argv[5]) if len(sys.argv) > 5 else Integer(0)
nmax  = Integer(sys.argv[6]) if len(sys.argv) > 6 else Integer(3)

print("### R4 reach measurement -- v_p(c_2(p)) at minimal approximation order")
print("sage version      : %s" % version())
print("p range           : %s .. %s" % (pmin, pmax))
print("prec_T            : %s" % precT)
print("cap per prime (s) : %s" % (cap if cap else "none"))
print("global budget (s) : %s" % (budget if budget else "none"))
print("n_max             : %s" % nmax)

E = EllipticCurve([0, 0, 0, -56, 0])
N = E.conductor()
print("curve             : %s" % E)
print("conductor         : %s" % N)
print("rank              : %s" % E.rank())
print("CM                : %s   (K = Q(i))" % E.cm_discriminant())

# --- the one-off: the space of modular symbols at level 12544 -----------------
print()
print("=== ONE-OFF SETUP (level 12544), timed separately ===")
t0 = time.time()
ms = E.modular_symbol(sign=+1, implementation='eclib', normalize='L_ratio')
t_ms = time.time() - t0
print("modular symbol    : %s" % ms)
print("setup runtime     : %.2f s   <-- one-off, level 12544, reused at every p"
      % t_ms)
print("MACHINE setup.modsym v=0 prec=0 digits=[%d]" % int(round(t_ms * 1000)))

t0 = time.time()
rho = E.galois_representation()
red = rho.reducible_primes()
t_rho = time.time() - t0
print("reducible primes  : %s   (=> _c_bound() = 0 at every odd p)" % red)
print("galois rep runtime: %.2f s   <-- also one-off" % t_rho)
print("MACHINE setup.galrep v=0 prec=0 digits=[%d]" % int(round(t_rho * 1000)))

# --- the scan -----------------------------------------------------------------
print()
print("=== PER-PRIME SCAN ===")
print("split = p = 1 mod 4 (so p splits in Q(i) and E is ordinary at p);")
print("p = 2 and p = 7 are excluded by bad reduction and are not 1 mod 4 anyway.")
print()

t_scan0 = time.time()
rows = []
stop_reason = "range exhausted"

for p in primes(pmin, pmax + 1):
    p = Integer(p)
    if p % 4 != 1:
        continue
    if N % p == 0:
        continue

    if budget and (time.time() - t_scan0) > float(budget):
        stop_reason = ("global budget of %s s expired before p = %s" % (budget, p))
        print("BUDGET EXPIRED    : stopping before p = %s (%.1f s elapsed in scan)"
              % (p, time.time() - t_scan0))
        break

    print("-------------------------------------------------------------------------------")
    print("p                 : %s" % p)
    ap = E.ap(p)
    print("a_p               : %s   #Etilde(F_p) = %s" % (ap, p + 1 - ap))
    print("ordinary          : %s" % E.is_ordinary(p))
    print("anomalous         : %s" % (((p + 1 - ap) % p) == 0))

    t0 = time.time()
    Lp = E.padic_lseries(p, implementation='eclib')
    t_obj = time.time() - t0
    print("padic_lseries obj : %.3f s   <-- cache hit on the level-12544 symbols"
          % t_obj)

    cb = Lp._c_bound()
    print("_c_bound()        : %s" % cb)

    n = Integer(2)
    row = None
    capped = False
    while n <= nmax:
        bounds = Lp._prec_bounds(n, precT)
        summands = (p - 1) * p**(n - 1)
        print("  n = %s : _prec_bounds = %s ; summands = (p-1)*p^(n-1) = %s"
              % (n, bounds, summands))
        t0 = time.time()
        ser = None
        if cap:
            alarm(float(cap))
        try:
            ser = Lp.series(n, prec=precT)
            if cap:
                cancel_alarm()
        except AlarmInterrupt:
            el = time.time() - t0
            print("  CAP HIT           : series(%s, prec=%s) exceeded %s s at p = %s"
                  % (n, precT, cap, p))
            print("  elapsed           : %.1f s" % el)
            print("MACHINE reach.p%s v=0 prec=0 digits=[%s, %s, %s, -1, -1, %d]"
                  % (p, p, n, summands, int(round(el * 1000))))
            rows.append((p, n, summands, None, None, el, "CAP HIT"))
            capped = True
            break
        el = time.time() - t0

        co = ser.list()
        if len(co) < 3:
            print("  FATAL             : fewer than three T-coefficients at p = %s" % p)
            rows.append((p, n, summands, None, None, el, "SHORT SERIES"))
            capped = True
            break
        c2 = co[2]
        prec2 = c2.precision_absolute()
        print("  series runtime    : %.2f s" % el)
        print("  c_2               : %s" % c2)
        print("  c_2 precision     : O(p^%s)   (= p^(n-1), the certified modulus)"
              % prec2)

        if c2.is_zero():
            print("  v_p(c_2(p))       : >= %s  (c_2 indistinguishable from 0 at O(p^%s))"
                  % (prec2, prec2))
            print("  NOT CERTIFIED at n = %s -- retrying at n = %s (cost x %s)"
                  % (n, n + 1, p))
            rows.append((p, n, summands, None, None, el, "inconclusive at this n"))
            n = n + 1
            continue

        vc2 = c2.valuation()
        x = ZZ((c2 / p**vc2).lift() % p**(prec2 - vc2))
        d = x.digits(p)
        d = d + [0] * ((prec2 - vc2) - len(d))
        print("  v_p(c_2(p))       : %s" % vc2)
        print("  c_2 digits        : %s   (p^%s first, up to O(p^%s))" % (d, vc2, prec2))
        verdict = "v_p(c_2(p)) = 0" if vc2 == 0 else ("v_p(c_2(p)) = %s" % vc2)
        if vc2 == 0:
            print("  INPUT AVAILABLE   : leading digit %s nonzero, rigorous to O(p^%s);"
                  % (d[0], prec2))
            print("                      by lem:c0c1 this is lambda_an = 2, mu_an = 0.")
            print("                      NOT A CERTIFICATE: no Reg_p cross-check, no")
            print("                      eq:match5 comparison, no check_agreement.py.")
        else:
            print("  INPUT FAILS       : v_p(c_2(p)) = %s != 0 -- prop:criterion (H6)"
                  % vc2)
            print("                      does not hold at p = %s by this run." % p)
        print("MACHINE reach.p%s v=%s prec=%s digits=[%s, %s, %s, %s, %s, %d]"
              % (p, vc2, prec2, p, n, summands, prec2, d[0], int(round(el * 1000))))
        rows.append((p, n, summands, prec2, vc2, el, verdict))
        row = True
        break

    if capped:
        stop_reason = "cap hit at p = %s" % p
        break
    if row is None:
        print("  EXHAUSTED n_max   : no certificate at p = %s up to n = %s" % (p, nmax))
        stop_reason = "n_max exhausted at p = %s" % p
        break

t_scan = time.time() - t_scan0

# --- summary ------------------------------------------------------------------
print()
print("===============================================================================")
print("SUMMARY -- reach measurement")
print("===============================================================================")
print("one-off setup (level 12544 modular symbols) : %.2f s" % t_ms)
print("one-off Galois representation               : %.2f s" % t_rho)
print("total per-prime scan time                   : %.2f s" % t_scan)
print("stop reason                                 : %s" % stop_reason)
print()
print("   p     n   summands   cert mod   v_p(c_2(p))   wall (s)   verdict")
for (p, n, s, prec2, v, el, verdict) in rows:
    print("%5s %5s %10s %10s %13s %10.2f   %s"
          % (p, n, s,
             ("p^%s" % prec2) if prec2 is not None else "-",
             v if v is not None else "-",
             el, verdict))
print()
ok = [r for r in rows if r[4] == 0]
print("primes with v_p(c_2(p)) = 0 in this scan    : %s" % [r[0] for r in ok])
print("primes with v_p(c_2(p)) != 0 in this scan   : %s"
      % [r[0] for r in rows if r[4] is not None and r[4] != 0])
if ok:
    print("largest split prime reached                 : %s" % max(r[0] for r in ok))
    print("total per-prime wall time over those primes : %.2f s"
          % sum(r[5] for r in ok))
    print("MACHINE reach.summary v=0 prec=0 digits=[%s, %s, %d, %d]"
          % (max(r[0] for r in ok), len(ok),
             int(round(sum(r[5] for r in ok) * 1000)), int(round(t_ms * 1000))))
print()
print("REMINDER: this is a cost-and-reach measurement, not a certificate.  The")
print("theorem of sec:certificates is claimed only at p = 5, 13, 17, 29, 37, 41,")
print("where the full pipeline of ssec:repro was run.")
