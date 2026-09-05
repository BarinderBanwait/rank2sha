# unit_ms_family.py -- the unit condition by modular symbols, for E_D : y^2 = x^3 - D x
# at every split prime below 1000 of good reduction.
# ---------------------------------------------------------------------------
# Backs paper Section 7.8 and prop:scaneq for the five rank-two curves of
# Coates--Liang--Sujatha, D = 56, 17, -33, -34, -39.  For each split p it forms
# the Mazur--Tate--Teitelbaum series L_p(E,T) from eclib modular symbols with the
# Stein--Wuthrich error bounds, at n = 2 and T-adic precision 3, and records
#     p   a_p   n   v_p(c_2)   c_2 mod p   the certified p-adic precision of c_2,
# with c_0 and c_1 shown vanishing to the same certified precision (lem:c0c1).
# The unit condition at p is v_p(c_2) = 0.  A prime at which n = 2 does not
# separate c_2 from 0 is rerun at n = 3, which certifies c_2 modulo p^2; the n
# column records which.
#
# Run from this directory:   D=-34 sage unit_ms_family.py
# Parameters from the environment:
#     D      the curve y^2 = x^3 - D x            default 56
#     PBOUND upper bound on the primes            default 1000
#     OUT    output file                          default ../data/unit_ms_D<D>.txt
# Cost is (p-1)p modular symbols per prime, about 15 minutes for one curve over
# the 80 split primes below 1000, at any of these conductors.  The modular-symbol space
# is built once and reused.  Output is staged to <file>.partial and moved onto the
# committed file only when every prime has been treated.
# ---------------------------------------------------------------------------
from sage.all import EllipticCurve, ZZ, Integers, prime_range, version
import os, sys, time

D = ZZ(os.environ.get("D", "56"))
PBOUND = ZZ(os.environ.get("PBOUND", "1000"))
OUT = os.environ.get("OUT", "../data/unit_ms_D%s.txt" % D)
TMP = OUT + ".partial"

E = EllipticCurve([0, 0, 0, -D, 0])
N = E.conductor()
f = open(TMP, "w")


def say(s):
    print(s, flush=True)
    f.write(s + "\n")
    f.flush()


say("=== unit_ms_family.py : the unit condition by modular symbols ===")
say("sage version      : %s" % version())
say("curve             : E : y^2 = x^3 - %sx   [0,0,0,%s,0]" % (D, -D))
say("conductor         : %s" % N)
say("CM discriminant   : %s" % E.cm_discriminant())
say("root number       : %s" % E.root_number())
say("modular symbol at 0 : %s   (L(E,1)/Omega up to a unit)"
    % E.modular_symbol(implementation='eclib')(0))
say("normalisation     : MTT / Stein-Wuthrich, real Neron period (Sage padic_lseries)")
say("series            : n = 2, T-adic precision 3; c_2 certified to the printed O(p^k)")
say("prime range       : split 5 <= p < %s of good reduction" % PBOUND)
say("")
say("# p     a_p     n  v_p(c2)  c2 mod p  prec(c2)  c0        c1        seconds")

primes = [p for p in prime_range(5, PBOUND) if p % 4 == 1 and N % p != 0]
skipped = [p for p in prime_range(5, PBOUND) if p % 4 == 1 and N % p == 0]
nunit = 0
nexc = 0
nfail = 0
exceptions = []
t00 = time.time()
for p in primes:
    t0 = time.time()
    try:
        L = E.padic_lseries(p, implementation='eclib')
        n = 2
        s = L.series(n, prec=3)
        c0, c1, c2 = s[0], s[1], s[2]
        # n = 2 certifies c_2 modulo p.  When it does not separate c_2 from 0,
        # n = 3 is run at that prime alone and certifies it modulo p^2.
        if c2.valuation() != 0:
            n = 3
            s = L.series(n, prec=3)
            c0, c1, c2 = s[0], s[1], s[2]
        v = c2.valuation()
        prec = c2.precision_absolute()
        cm = "NA" if v != 0 else str(Integers(p)(c2.unit_part().residue(1)))
        z0 = "0" if c0 == 0 else "NONZERO"
        z1 = "0" if c1 == 0 else "NONZERO"
        if c0 != 0 or c1 != 0:
            nfail += 1
        if v == 0:
            nunit += 1
        else:
            nexc += 1
            exceptions.append((p, v))
        say("%-7s %-7s %-2s %-8s %-9s %-9s %-9s %-9s %.1f"
            % (p, E.ap(p), n, v, cm, prec, z0, z1, time.time() - t0))
    except Exception as exc:                                   # noqa: BLE001
        nfail += 1
        say("%-7s %-7s ERROR %s" % (p, E.ap(p), exc))

say("")
say("split primes below %s of good reduction : %d" % (PBOUND, len(primes)))
if skipped:
    say("split primes of bad reduction, omitted  : %s" % skipped)
say("primes with c_2 a unit                  : %d" % nunit)
say("primes with v_p(c_2) > 0                : %d   %s"
    % (nexc, [(int(p), str(v)) for p, v in exceptions]))
say("c_0 = c_1 = 0 at every prime above      : %s" % (nfail == 0))
say("total time                              : %.0f s" % (time.time() - t00))
say("UNITMSDONE" if nfail == 0 else "INCOMPLETE")
f.close()
if nfail == 0:
    os.replace(TMP, OUT)
else:
    sys.exit(1)
