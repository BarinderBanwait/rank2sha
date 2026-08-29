#!/usr/bin/env python3
"""null_model.py -- the null model of paper Section 5.4 (ssec:scanweight).

Backs every number of Section 5.4.  The model treats the events
v_fp(Reg_fp) > 2, one per scanned split prime, as independent, and assigns
each the probability 1/p that a random element of Z_p is divisible by p.  The
number of exceptions is then approximately Poisson with mean

    lambda = sum over the scanned primes of 1/p,

the sum being taken over the 508 primes of ../data/all_primes_vreg.txt.  The
three hypotheses of Section 5.4 assign a clean scan the probabilities

    (H1) Conjecture conj:strong                       1
    (H2) chance, exceptions at density 1/p            exp(-lambda)
    (H3) Wieferich collapse at density c/p            exp(-c*lambda)

so the likelihood ratio of (H1) to (H2) is exp(lambda) and that of (H1) to
(H3) is exp(c*lambda).

The script also computes the Poisson probability of five or more exceptions,
and repeats the computation of lambda over every split prime below 10^6 --
the split primes of K = Q(i) are the primes p = 1 mod 4 -- which is the
extension Section 5.4 considers and rejects.

Each computed value is printed beside the value printed in the paper.

Status: arithmetic on the committed prime list and on a sieve.  It uses no
regulator data beyond the list of scanned primes.

Requires Python 3 only.  Run from this directory:  python3 null_model.py
"""

import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, os.pardir, "data")

SCAN = os.path.join(DATA, "all_primes_vreg.txt")
EXTENSION_BOUND = 10 ** 6

# the values printed in Section 5.4, for comparison
PAPER = {
    "count": "508",
    "lambda": "0.803...",
    "clean_H2": "0.45",
    "clean_H3_c5": "0.018",
    "ratio_H1_H2": "2.2",
    "ratio_H1_H3_c5": "55",
    "ratio_H1_H3_c1": "2.2",
    "lambda_1e6": "1.03",
    "clean_1e6": "0.36",
    "ratio_1e6": "2.8",
    "five_or_more": "1.4e-03",
}

_log = []


def say(text=""):
    print(text)
    _log.append(text)


def row(label, computed, paper):
    say("  %-34s %-22s paper %s" % (label, computed, paper))


def sieve(limit):
    """Return a bytearray flags[0..limit-1] with flags[n] = 1 iff n is prime."""
    flags = bytearray([1]) * limit
    flags[0] = flags[1] = 0
    i = 2
    while i * i < limit:
        if flags[i]:
            step = i
            start = i * i
            flags[start::step] = bytearray(len(range(start, limit, step)))
        i += 1
    return flags


def poisson_tail(lam, k):
    """Return the Poisson(lam) probability of at least k events."""
    head = sum(math.exp(-lam) * lam ** j / math.factorial(j)
               for j in range(k))
    return 1.0 - head


def main():
    say("### the null model of paper Section 5.4 (ssec:scanweight)")
    say("python            : %s" % sys.version.split()[0])
    say("scanned primes    : %s" % os.path.normpath(SCAN))
    say("")

    primes = [int(line.split()[0]) for line in open(SCAN) if line.strip()]
    lam = math.fsum(1.0 / p for p in primes)

    say("the scanned set")
    row("number of primes", "%d" % len(primes), PAPER["count"])
    row("smallest, largest", "%d, %d" % (primes[0], primes[-1]), "5, 16889")
    row("lambda = sum 1/p", "%.6f" % lam, PAPER["lambda"])
    say("")

    say("probability of a clean scan")
    row("(H1) conj:strong", "1", "1")
    row("(H2) chance, exp(-lambda)", "%.4f" % math.exp(-lam),
        PAPER["clean_H2"])
    row("(H3) c = 5, exp(-5 lambda)", "%.4f" % math.exp(-5 * lam),
        PAPER["clean_H3_c5"])
    say("")

    say("likelihood ratios")
    row("(H1):(H2) = exp(lambda)", "%.3f" % math.exp(lam),
        PAPER["ratio_H1_H2"])
    row("(H1):(H3) at c = 5", "%.3f" % math.exp(5 * lam),
        PAPER["ratio_H1_H3_c5"])
    row("(H1):(H3) at c = 1", "%.3f" % math.exp(lam),
        PAPER["ratio_H1_H3_c1"])
    say("  (H3) at c = 1 is (H2), so the two ratios agree.")
    say("")

    say("the extension to every split prime below 10^6")
    flags = sieve(EXTENSION_BOUND)
    split = [p for p in range(5, EXTENSION_BOUND) if flags[p] and p % 4 == 1]
    lam6 = math.fsum(1.0 / p for p in split)
    row("number of split primes", "%d" % len(split), "not printed")
    row("lambda", "%.6f" % lam6, PAPER["lambda_1e6"])
    row("clean probability exp(-lambda)", "%.4f" % math.exp(-lam6),
        PAPER["clean_1e6"])
    row("(H1):(H2) = exp(lambda)", "%.3f" % math.exp(lam6),
        PAPER["ratio_1e6"])
    say("")

    say("the opposite outcome")
    row("Poisson(lambda), P(X >= 5)", "%.3e" % poisson_tail(lam, 5),
        PAPER["five_or_more"])
    say("")

    say("exact Bernoulli model, for comparison with the Poisson approximation")
    say("  The paper states the Poisson approximation.  Under the independent")
    say("  Bernoulli model itself the clean probability is the product of")
    say("  1 - 1/p over the scanned primes.")
    prod = 1.0
    for p in primes:
        prod *= 1.0 - 1.0 / p
    row("product of (1 - 1/p)", "%.4f" % prod, "not printed")
    row("Poisson exp(-lambda)", "%.4f" % math.exp(-lam), PAPER["clean_H2"])
    say("")
    say("NULLMODELDONE")

    out = os.path.join(DATA, "null_model.out")
    with open(out, "w") as handle:
        handle.write("\n".join(_log) + "\n")
    print("written to %s" % os.path.normpath(out))
    return 0


if __name__ == "__main__":
    sys.exit(main())
