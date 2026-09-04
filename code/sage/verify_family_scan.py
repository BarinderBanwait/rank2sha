#!/usr/bin/env python3
"""verify_family_scan.py -- re-parse and re-verify the four CLS-family scans.

Does for data/scan_D17.txt, data/scan_D-33.txt, data/scan_D-34.txt and
data/scan_D-39.txt what verify_scan.py does for data/all_primes_vreg.txt: it
decides every claim the README makes about those files from the files alone,
and recomputes no regulator.

Inputs, relative to this script's directory:
    ../data/scan_D17.txt, ../data/scan_D-33.txt,
    ../data/scan_D-34.txt, ../data/scan_D-39.txt

Checks, per file, in order:
  (1) every line parses as "p v" or "p v FLAG";
  (2) every entry is a prime and is = 1 mod 4;
  (3) the entries are strictly increasing, with no repetition;
  (4) the range is complete: the entries are exactly the primes p = 1 mod 4
      with 5 <= p < 30000 that do not divide D, so 17 is absent for D = 17 and
      D = -34, 13 is absent for D = -39, and nothing is absent for D = -33;
  (5) the count is 1610, 1611, 1610, 1610 respectively;
  (6) every recorded valuation is 2 apart from the five exceptional lines
      (D, p, v) = (17, 5, 0), (-33, 5, 0), (-33, 37, 3), (-39, 5, 3) and
      (-39, 15289, 3), each of which is present with that value;
  (7) the only flagged line is ESC on (D, p) = (-39, 15289).

Prints one PASS line per file and a terminal DONE line, and exits nonzero if
any check fails.

Requires Python 3 only.  Run from this directory:
    python3 verify_family_scan.py
"""

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, os.pardir, "data")

# The scanned range, as in verify_scan.py: every split prime below the bound of
# cor:shavanishing.
SCAN_LO = 5
SHA_BOUND = 30000

# The four curves y^2 = x^3 - Dx of Coates, Liang and Sujatha, with the line
# count of each scan file.
CURVES = [(17, 1610), (-33, 1611), (-34, 1610), (-39, 1610)]

# The lines with v != 2, and the only flagged line.
EXCEPTIONS = {
    (17, 5): 0,
    (-33, 5): 0,
    (-33, 37): 3,
    (-39, 5): 3,
    (-39, 15289): 3,
}
FLAGGED = {(-39, 15289): "ESC"}


def sieve(limit):
    """Return a list is_prime[0..limit] by the sieve of Eratosthenes."""
    flags = [True] * (limit + 1)
    flags[0] = flags[1] = False
    i = 2
    while i * i <= limit:
        if flags[i]:
            for j in range(i * i, limit + 1, i):
                flags[j] = False
        i += 1
    return flags


IS_PRIME = sieve(SHA_BOUND)


def read_entries(path):
    """Parse a scan output file.

    Returns (entries, malformed), where entries is a list of (lineno, p, v,
    flags) and malformed is the list of (lineno, line) that parse as neither.
    """
    entries, malformed = [], []
    with open(path) as handle:
        for lineno, raw in enumerate(handle, 1):
            line = raw.strip()
            if not line:
                continue
            parts = line.split()
            if len(parts) < 2:
                malformed.append((lineno, line))
                continue
            try:
                p, v = int(parts[0]), int(parts[1])
            except ValueError:
                malformed.append((lineno, line))
                continue
            entries.append((lineno, p, v, " ".join(parts[2:])))
    return entries, malformed


def verify(D, expected_count):
    """Check one scan file.  Returns the list of failures, empty on success."""
    name = "scan_D%d.txt" % D
    path = os.path.join(DATA, name)
    bad = []
    if not os.path.exists(path):
        return ["%s: missing" % name]

    entries, malformed = read_entries(path)
    if malformed:
        bad.append("%s: %d line(s) parse as neither \"p v\" nor \"p v FLAG\": %r"
                   % (name, len(malformed), malformed[:5]))
    primes = [p for (_, p, _, _) in entries]

    notprime = [p for p in primes if not (p <= SHA_BOUND and IS_PRIME[p])]
    if notprime:
        bad.append("%s: not prime: %r" % (name, notprime[:5]))

    notsplit = [p for p in primes if p % 4 != 1]
    if notsplit:
        bad.append("%s: not = 1 mod 4: %r" % (name, notsplit[:5]))

    if primes != sorted(set(primes)):
        bad.append("%s: entries are not strictly increasing" % name)

    expected = [p for p in range(SCAN_LO, SHA_BOUND)
                if IS_PRIME[p] and p % 4 == 1 and D % p != 0]
    missing = sorted(set(expected) - set(primes))
    extra = sorted(set(primes) - set(expected))
    if missing or extra:
        bad.append("%s: range incomplete: missing %r extra %r"
                   % (name, missing[:5], extra[:5]))

    if len(entries) != expected_count:
        bad.append("%s: %d lines, expected %d"
                   % (name, len(entries), expected_count))

    want = dict((p, v) for ((d, p), v) in EXCEPTIONS.items() if d == D)
    for (_, p, v, _) in entries:
        if p in want:
            if v != want[p]:
                bad.append("%s: v = %d at p = %d, expected %d"
                           % (name, v, p, want[p]))
        elif v != 2:
            bad.append("%s: v = %d at p = %d, expected 2" % (name, v, p))
    for p in sorted(set(want) - set(primes)):
        bad.append("%s: exceptional prime %d is absent" % (name, p))

    wantflag = dict((p, f) for ((d, p), f) in FLAGGED.items() if d == D)
    for (_, p, _, flags) in entries:
        if flags and wantflag.get(p) != flags:
            bad.append("%s: flag %r at p = %d, expected %r"
                       % (name, flags, p, wantflag.get(p, "")))
    seen = dict((p, f) for (_, p, _, f) in entries if f)
    for p in sorted(set(wantflag) - set(seen)):
        bad.append("%s: p = %d is not flagged %s" % (name, p, wantflag[p]))

    if not bad:
        shown = ", ".join("p = %d: v = %d" % (p, want[p]) for p in sorted(want))
        print("[PASS] %-16s %d lines, %d to %d, %s"
              % (name, len(entries), min(primes), max(primes),
                 shown if shown else "every v = 2"))
    return bad


def main():
    print("### verification of the CLS-family scans, y^2 = x^3 - Dx")
    print("python            : %s" % sys.version.split()[0])
    print("data directory    : %s" % os.path.normpath(DATA))
    print("range             : [%d, %d), primes p = 1 mod 4 not dividing D"
          % (SCAN_LO, SHA_BOUND))

    failures = []
    for D, count in CURVES:
        failures.extend(verify(D, count))

    if failures:
        for line in failures:
            print("[FAIL] %s" % line)
        print("checks failed     : %d" % len(failures))
        return 1
    print("VERIFYFAMILYSCANDONE")
    return 0


if __name__ == "__main__":
    sys.exit(main())
