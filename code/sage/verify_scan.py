#!/usr/bin/env python3
"""verify_scan.py -- re-parse and re-verify the committed scan output.

Backs the sentence of paper Section 5.3 (ssec:scan): "The output file was
re-parsed and re-verified in preparing this paper, for primality, for
p = 1 mod 4, for completeness of the range and for absence of flags."  It
also checks the count and the range bound that Corollary cor:shavanishing
needs.

Input, relative to this script's directory:
    ../data/all_primes_vreg.txt

Checks, in order:
  (1) every entry is a prime and is = 1 mod 4;
  (2) the range is complete: the entries are exactly the split primes below
      30000, with none missing and none extra, in strictly increasing order;
  (3) every recorded valuation is 2;
  (4) no line carries an ESC or a MAXED flag;
  (5) the count is 1611;
  (6) the largest prime is 29989 and every prime is below 30000, the bound
      below which cor:shavanishing gives Sha(E/Q)[p^oo] = 0.

Status: the script decides each check from the committed file alone.  It
recomputes no regulator.  It exits nonzero if any check fails.

Requires Python 3 only.  Run from this directory:  python3 verify_scan.py
"""

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, os.pardir, "data")

# The scanned range of Section 5.3: every split prime below the bound of
# cor:shavanishing.
SCAN_LO = 5
SHA_BOUND = 30000
TOTAL_PAPER = 1611
MAXPRIME_PAPER = 29989

_log = []
_failures = []


def say(text=""):
    print(text)
    _log.append(text)


def check(ok, description, detail=""):
    """Record one check.  ok is a bool; description is what was checked."""
    tag = "PASS" if ok else "FAIL"
    say("  [%s] %s%s" % (tag, description, ("   " + detail) if detail else ""))
    if not ok:
        _failures.append(description)
    return ok


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

    Returns (entries, flagged, markers, malformed) where entries is a list of
    (lineno, p, v), flagged is the list of (lineno, p, flags) whose line
    carries ESC or MAXED, markers is the list of JOBDONE lines, and malformed
    is the list of lines that parse as neither.
    """
    entries, flagged, markers, malformed = [], [], [], []
    with open(path) as handle:
        for lineno, raw in enumerate(handle, 1):
            line = raw.strip()
            if not line:
                continue
            parts = line.split()
            if parts[0] == "JOBDONE":
                markers.append((lineno, line))
                continue
            if len(parts) < 2:
                malformed.append((lineno, line))
                continue
            try:
                p, v = int(parts[0]), int(parts[1])
            except ValueError:
                malformed.append((lineno, line))
                continue
            entries.append((lineno, p, v))
            if len(parts) > 2:
                flagged.append((lineno, p, " ".join(parts[2:])))
    return entries, flagged, markers, malformed


def main():
    say("### verification of the committed scan output, paper Section 5.3")
    say("python            : %s" % sys.version.split()[0])
    say("data directory    : %s" % os.path.normpath(DATA))
    say("sieve bound       : %d" % SHA_BOUND)
    say("")

    path = os.path.join(DATA, "all_primes_vreg.txt")
    say("all_primes_vreg.txt   range [%d, %d)" % (SCAN_LO, SHA_BOUND))
    entries, flagged, markers, malformed = read_entries(path)
    primes = [p for (_, p, _) in entries]

    check(not malformed, "every line parses as \"p v\" or JOBDONE",
          "" if not malformed else "malformed: %r" % malformed[:5])

    bad = [(ln, p) for (ln, p, _) in entries
           if not (p <= SHA_BOUND and IS_PRIME[p])]
    check(not bad, "every entry is prime",
          "" if not bad else "not prime: %r" % bad[:5])

    bad = [(ln, p) for (ln, p, _) in entries if p % 4 != 1]
    check(not bad, "every entry is = 1 mod 4",
          "" if not bad else "not split: %r" % bad[:5])

    bad = [(ln, p, v) for (ln, p, v) in entries if v != 2]
    check(not bad, "every recorded valuation is 2",
          "" if not bad else "v != 2: %r" % bad[:5])

    check(not flagged, "no line carries an ESC or MAXED flag",
          "" if not flagged else "flagged: %r" % flagged[:5])

    check(primes == sorted(set(primes)),
          "entries are strictly increasing, with no repetition")

    expected = [p for p in range(SCAN_LO, SHA_BOUND)
                if IS_PRIME[p] and p % 4 == 1]
    missing = sorted(set(expected) - set(primes))
    extra = sorted(set(primes) - set(expected))
    check(not missing and not extra,
          "the range is complete: every split prime below %d, and no other"
          % SHA_BOUND,
          "" if not (missing or extra)
          else "missing %r extra %r" % (missing[:5], extra[:5]))

    total = len(entries)
    check(total == TOTAL_PAPER, "count is %d" % TOTAL_PAPER,
          "computed %d, paper %d" % (total, TOTAL_PAPER))

    check(primes[0] == SCAN_LO if primes else False,
          "first entry is the smallest split prime, %d" % SCAN_LO,
          "computed %d" % primes[0] if primes else "no entries")

    largest = max(primes) if primes else 0
    check(largest == MAXPRIME_PAPER, "largest prime is %d" % MAXPRIME_PAPER,
          "computed %d, paper %d" % (largest, MAXPRIME_PAPER))
    check(largest < SHA_BOUND,
          "every prime is below %d, so cor:shavanishing applies at all of "
          "them" % SHA_BOUND,
          "largest %d" % largest)

    if markers:
        say("  [note] %d JOBDONE marker line(s); the committed file "
            "carries none" % len(markers))
    say("")

    say("summary")
    say("  total             : %d   (paper: %d)" % (total, TOTAL_PAPER))
    say("  exceptions v != 2 : %d   (paper: zero)"
        % len([1 for (_, _, v) in entries if v != 2]))
    say("  escalation flags  : %d   (paper: zero)" % len(flagged))
    say("  largest prime     : %d   (paper: %d)" % (largest, MAXPRIME_PAPER))
    say("  checks failed     : %d" % len(_failures))
    say("VERIFYSCANDONE")

    out = os.path.join(DATA, "verify_scan.out")
    with open(out, "w") as handle:
        handle.write("\n".join(_log) + "\n")
    print("written to %s" % os.path.normpath(out))

    return 1 if _failures else 0


if __name__ == "__main__":
    sys.exit(main())
