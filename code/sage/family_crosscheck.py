#!/usr/bin/env sage
"""family_crosscheck.py -- an independent reading of the CLS-family exceptions.

The valuations of gp/scan_family.gp and gp/family_checks.gp come from PARI's
ellpadicregulator on the bases of data/family_bases.txt.  This script recomputes
them in SageMath, whose padic_regulator is a separate implementation and which
chooses its own saturated Mordell-Weil basis, and then computes the
modular-symbol p-adic L-series of y^2 = x^3 + 39x at p = 5, which is the other
side of the dictionary at the smallest of the exceptional primes.

Blocks, in order:
  1. the cyclotomic p-adic regulator at (D, p) = (56, 5), (-39, 5), (-33, 37)
     and (-34, 5), each at working precisions 8 and 14, D = 56 being the paper's
     testbed and the control;
  2. the same at (D, p) = (-39, 15289), at precisions 6 and 8;
  3. the p-adic L-series of y^2 = x^3 + 39x at p = 5, four terms at precision 6,
     from eclib modular symbols, falling back to Sage's own implementation and
     recording which one produced the series.

Output staging follows gp/deltaE.gp: every line is written to
../data/family_crosscheck.out.partial, and that file is moved onto
../data/family_crosscheck.out only once all six blocks have reported with no
failure.  An interrupted or failed run therefore leaves the committed file alone
and its partial output in the .partial file.  A complete run ends the output
file with a FAMILYCROSSCHECKDONE line.

Requires SageMath.  Run from this directory:  sage family_crosscheck.py
"""

from sage.all import *

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, os.pardir, "data")
OUT = os.path.join(DATA, "family_crosscheck.out")
TMP = OUT + ".partial"

# The exceptional lines of data/scan_D*.txt, with the paper's testbed as the
# control, and the precisions at which each is recomputed.
REG_PAIRS = [(56, 5), (-39, 5), (-33, 37), (-34, 5)]
REG_PRECS = [8, 14]
BIG_PAIR = (-39, 15289)
BIG_PRECS = [6, 8]
NBLOCKS = len(REG_PAIRS) + 2

_handle = None
_blocks = 0
_failures = 0


def say(text=""):
    """Print one line and append it to the staged output file."""
    print(text, flush=True)
    _handle.write(text + "\n")
    _handle.flush()


def regulator_block(D, p, precs):
    """Report Reg_p for y^2 = x^3 - Dx at p, at each precision in precs."""
    global _blocks, _failures
    E = EllipticCurve([0, 0, 0, -D, 0])
    say("D = %d  p = %d  conductor = %s  a_p = %s  anomalous = %s"
        "  Tamagawa = %s  gens = %s"
        % (D, p, E.conductor(), E.ap(p), (E.ap(p) - 1) % p == 0,
           E.tamagawa_product(), [P.xy() for P in E.gens()]))
    ok = True
    for prec in precs:
        try:
            R = E.padic_regulator(p, prec)
            say("   padic_regulator(%d, prec=%d): valuation %s   (%s)"
                % (p, prec, R.valuation(), R))
        except Exception as exc:
            say("   padic_regulator(%d, prec=%d): FAILED %s" % (p, prec, exc))
            ok = False
    if ok:
        _blocks += 1
    else:
        _failures += 1


def lseries_block():
    """Report the p-adic L-series of y^2 = x^3 + 39x at p = 5."""
    global _blocks, _failures
    E = EllipticCurve([0, 0, 0, 39, 0])
    say("D = -39  p = 5  y^2 = x^3 + 39x  level = %s  modular-symbol side"
        % E.conductor())
    for impl in ["eclib", "sage"]:
        try:
            L = E.padic_lseries(5, implementation=impl)
            series = L.series(n=4, prec=6)
            say("   implementation    : %s" % impl)
            say("   L_5(E,T), 4 terms, prec 6: %s" % series)
            _blocks += 1
            return
        except Exception as exc:
            say("   implementation %s unavailable: %s" % (impl, exc))
    _failures += 1


def main():
    global _handle
    if os.path.exists(TMP):
        os.remove(TMP)
    _handle = open(TMP, "w")

    try:
        sage_version = version()
    except Exception:
        sage_version = "unreported"
    say("### the CLS-family exceptions, recomputed in SageMath")
    say("sage              : %s" % sage_version)
    say("python            : %s" % sys.version.split()[0])
    say("quantity          : E.padic_regulator(p, prec), Sage's own saturated basis")
    say("curves            : y^2 = x^3 - Dx; D = 56 is the paper's testbed and the control")

    for D, p in REG_PAIRS:
        regulator_block(D, p, REG_PRECS)
    regulator_block(BIG_PAIR[0], BIG_PAIR[1], BIG_PRECS)
    lseries_block()

    if _blocks == NBLOCKS and _failures == 0:
        say("FAMILYCROSSCHECKDONE")
        _handle.close()
        os.replace(TMP, OUT)
        print("written to %s" % os.path.normpath(OUT), flush=True)
        return 0
    _handle.close()
    print("INCOMPLETE: %d of %d blocks reported, %d failed."
          % (_blocks, NBLOCKS, _failures), flush=True)
    print("%s left unchanged; partial output in %s."
          % (os.path.normpath(OUT), os.path.normpath(TMP)), flush=True)
    return 1


if __name__ == "__main__":
    sys.exit(main())
