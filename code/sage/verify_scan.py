#!/usr/bin/env python3
"""verify_scan.py -- re-parse and re-verify the four scan output files.

Backs the sentence of paper Section 5.3 (ssec:scan): "The four output files
were re-parsed and re-verified in preparing this paper, for primality, for
p = 1 mod 4, for completeness of each closed interval and for absence of
flags."  It also checks the counts of the segment table and the range bound
that Corollary cor:shavanishing needs.

Inputs, relative to this script's directory:
    ../data/res_1.txt, res_2.txt, res_3.txt, res_4.txt
    ../data/all_primes_vreg.txt

Checks, in order:
  (1) every entry is a prime and is = 1 mod 4;
  (2) each of the four closed intervals is complete: the entries are exactly
      the split primes of that interval, with none missing and none extra,
      listed in strictly increasing order;
  (3) every recorded valuation is 2;
  (4) no line carries an ESC or a MAXED flag;
  (5) the counts are 335, 77, 54, 42, total 508;
  (6) all_primes_vreg.txt is the concatenation of the four files, in order;
  (7) the largest prime is 16889 and every prime is below 30000, the bound
      below which cor:shavanishing gives Sha(E/Q)[p^oo] = 0.

Status: the script decides each check from the committed files alone.  It
recomputes no regulator.  It exits nonzero if any check fails.

Requires Python 3 only.  Run from this directory:  python3 verify_scan.py
"""

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, os.pardir, "data")

# lo, hi and the count printed in the segment table of Section 5.3
SEGMENTS = [
    ("res_1.txt", 5, 5113, 335),
    ("res_2.txt", 8009, 9349, 77),
    ("res_3.txt", 12517, 13513, 54),
    ("res_4.txt", 16001, 16889, 42),
]
TOTAL_PAPER = 508
MAXPRIME_PAPER = 16889
SHA_BOUND = 30000

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


def data_lines(path):
    """Return the data lines of a scan output file, JOBDONE markers dropped."""
    out = []
    with open(path) as handle:
        for raw in handle:
            line = raw.rstrip("\n")
            if line.strip() and not line.startswith("JOBDONE"):
                out.append(line)
    return out


def main():
    say("### verification of the four scan output files, paper Section 5.3")
    say("python            : %s" % sys.version.split()[0])
    say("data directory    : %s" % os.path.normpath(DATA))
    say("sieve bound       : %d" % SHA_BOUND)
    say("")

    all_entries = []
    for name, lo, hi, count_paper in SEGMENTS:
        path = os.path.join(DATA, name)
        say("%s   interval [%d, %d]" % (name, lo, hi))
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

        expected = [p for p in range(lo, hi + 1)
                    if IS_PRIME[p] and p % 4 == 1]
        missing = sorted(set(expected) - set(primes))
        extra = sorted(set(primes) - set(expected))
        check(not missing and not extra,
              "interval [%d, %d] is complete" % (lo, hi),
              "" if not (missing or extra)
              else "missing %r extra %r" % (missing[:5], extra[:5]))

        check(len(entries) == count_paper,
              "count is %d" % count_paper,
              "computed %d, paper %d" % (len(entries), count_paper))

        check(primes[0] == lo if primes else False,
              "first entry is the stated lower end %d" % lo,
              "computed %d" % primes[0] if primes else "no entries")
        check(primes[-1] == hi if primes else False,
              "last entry is the stated upper end %d" % hi,
              "computed %d" % primes[-1] if primes else "no entries")

        if markers:
            say("  [note] %d JOBDONE marker line(s); the committed files "
                "carry none" % len(markers))
        say("")
        all_entries.extend(entries)

    say("across the four files")
    total = len(all_entries)
    check(total == TOTAL_PAPER, "total count is %d" % TOTAL_PAPER,
          "computed %d, paper %d" % (total, TOTAL_PAPER))

    primes = [p for (_, p, _) in all_entries]
    check(primes == sorted(set(primes)),
          "the four segments are disjoint and in increasing order")

    largest = max(primes) if primes else 0
    check(largest == MAXPRIME_PAPER, "largest prime is %d" % MAXPRIME_PAPER,
          "computed %d, paper %d" % (largest, MAXPRIME_PAPER))
    check(largest < SHA_BOUND,
          "every prime is below %d, so cor:shavanishing applies at all of "
          "them" % SHA_BOUND,
          "largest %d" % largest)

    concat = []
    for name, _, _, _ in SEGMENTS:
        concat.extend(data_lines(os.path.join(DATA, name)))
    combined = data_lines(os.path.join(DATA, "all_primes_vreg.txt"))
    check(combined == concat,
          "all_primes_vreg.txt is the concatenation of the four files, in "
          "order",
          "%d lines against %d" % (len(combined), len(concat)))
    say("")

    say("summary")
    say("  segment counts    : %s   (paper: 335, 77, 54, 42)"
        % ", ".join(str(c) for c in
                    [len([1 for (_, p, _) in all_entries
                          if lo <= p <= hi])
                     for _, lo, hi, _ in SEGMENTS]))
    say("  total             : %d   (paper: %d)" % (total, TOTAL_PAPER))
    say("  exceptions v != 2 : %d   (paper: zero)"
        % len([1 for (_, _, v) in all_entries if v != 2]))
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
