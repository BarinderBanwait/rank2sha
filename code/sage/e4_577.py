# e4_577.py -- the 577-adic L-function of E_4 : y^2 = x^3 + 34x, the one case
# below 30,000 that the criterion of Coates, Liang and Sujatha (CLS2, Thm 1.3)
# and Wuthrich's height computations left open.  Computes the Mazur--Tate--
# Teitelbaum series from eclib modular symbols (Stein--Wuthrich error bounds),
# together with the invariants that place 577 outside S_E.  Writes
# ../data/e4_577.out, staged as .partial and moved on success.
# Run from this directory:  sage e4_577.py        (about one minute)
from sage.all import *
import os, time
OUT = "../data/e4_577.out"; TMP = OUT + ".partial"
f = open(TMP, "w")
def say(s):
    print(s, flush=True); f.write(s + "\n"); f.flush()
E = EllipticCurve([0,0,0,34,0]); p = 577
say("curve y^2 = x^3 + 34x   conductor %d = %s" % (E.conductor(), factor(E.conductor())))
say("rank (mwrank, proved) %d   root number %d   torsion %d   Tamagawa product %d"
    % (E.rank(), E.root_number(), E.torsion_order(), E.tamagawa_product()))
say("a_577 = %d   anomalous: %s   577 splits in Q(i): %s" % (E.ap(p), (E.ap(p)-1) % p == 0, p % 4 == 1))
say("modular symbol at 0 (exact rational, L(E,1)/Omega up to a unit): %s" % E.modular_symbol(implementation='eclib')(0))
say("isogeny degrees over Q: %s" % E.isogeny_class().matrix().list() if False else "rational isogenies of E: degrees %s" % sorted(set(E.isogeny_class().matrix().list())))
t0 = time.time()
L = E.padic_lseries(p, implementation='eclib')
say("unit root alpha: valuation %d" % L.alpha(prec=4).valuation())
for n, prec in [(2, 4), (2, 6)]:
    s = L.series(n=n, prec=prec)
    say("L_577(E,T), n = %d, prec = %d: %s" % (n, prec, s))
c2 = L.series(n=2, prec=4)[2]
say("v_577(c_2) = %d   (c_2 = %s)" % (c2.valuation(), c2))
say("elapsed %.0f s" % (time.time() - t0))
say("E4_577_DONE")
f.close(); os.replace(TMP, OUT)
