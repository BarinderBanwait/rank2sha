# `code/descent` — the 𝔭-descent computation

This directory holds the Magma scripts of the $\varphi$-descent that was
written for the retired Paper I, together with the audit trail for every run:
what was run, on what, for how long, and — where a run did not finish — where
it stopped and what was tried. Paper I was withdrawn on 2026-08-25, its
headline theorem being subsumed by Coates–Liang–Sujatha (J. Algebra 322 (2009)
657–674; Milan J. Math. 78 (2010) 395–416, Theorem 1.3, via the 2-isogeny
$12544b1 \to 12544b2$). This code is kept as **private verification**: an
independent, non-$L$-function confirmation of $\Sha(E/\mathbb{Q})[5] = 0$
(unconditional) and $[13] = 0$ (under GRH) for the curve of the paper. It is
not cited by the paper and there is no plan to publish it.

All computations were carried out in **Magma V2.29-9** on a shared multi-user
machine, single-threaded, under a hard wall-clock cap on every job. Every
script named below, and the raw output of every run named below **including the
runs that failed**, is committed under `code/data/`.

The output files are as the machines produced them, with one documented
exception: home-directory paths and machine names have been replaced throughout
by the neutral tokens `$HOME`, `$SERIES`, `laptop` and `remote-host`. The
substitution is uniform and it touches no number, command flag, timing or
verdict.

## The scripts

| script | what it does |
| --- | --- |
| `pi_descent.m` | The descent itself, parameterised over the curve, the prime $p$, whether a GRH bound is set for the class group, the ramification hint for the maximal order, and whether an optimised representation of $F$ is computed first. It defines a function `PiDescent`; its command-line driver runs only when a prime is supplied, so that the controls can load the file and call the same function. |
| `controls.m` | The validation controls. It `load`s `pi_descent.m` and calls `PiDescent`; it does not re-implement the descent. A control exercising a copy of the code would not be a control. |
| `curve_data.m` | Recomputes every invariant of the curve section. |
| `labels.m` | Derives the Cremona/LMFDB label table from the curves. |
| `scan_cm.m` | The search for a detection control. |
| `field_profile.m` | Profiles $F = K(E[\pi])$ alone — degree, signature, discriminant, maximal order, Minkowski bound, class group — for $p = 5, 13, 17, 29$, deliberately skipping the $\pi$-torsion point, the automorphism group and the character, so that the cost of the *field* is separated from the cost of the *descent*. |

## The runs

Each output file in `../data/` carries a three-line provenance header recording
the exact command, the Magma version, and the date, host and cap.

| output file | what | wall clock | outcome |
| --- | --- | ---: | --- |
| `p5.out` | $p = 5$, GRH and unconditional | seconds | complete |
| `p13.out` | $p = 13$, GRH | 8 m 35 s | complete |
| `p13_unconditional.out` | $p = 13$, no GRH | 60 m cap | **did not finish** |
| `controls_p5.out` | the eight controls at $p = 5$ | 18 s | complete |
| `curve_data.out` | the curve invariants | ≈ 1 m | complete |
| `labels.out` | the label table | 7 s | complete |
| `field_profile.out` | the reach profile | see below | complete |
| `scan_A_pos.out`, `scan_A_neg.out` | 287 curves $y^2 = x^3 + Ax$ | 2 × 900 s cap | complete |

## Identifying the curves

Each control curve is specified by its Weierstrass coefficients, which
determine it; the database references below are for convenience only. They are
*derived* from the curves by `labels.m`, using Magma's copy of the Cremona
database, rather than entered by hand — an earlier draft carried hand-entered
identifiers and two of them named the wrong curve.

| label | $A$ | $N$ | Cremona | LMFDB | rank | torsion |
| --- | ---: | ---: | --- | --- | ---: | --- |
| C0 | −56 | 12544 | `12544b2` | `12544.g1` | 2 | ℤ/2 |
| C1 | 571787 | 220448 | `220448a1` | `220448.f2` | 0 | ℤ/2 |
| C1b | −2287148 | 220448 | `220448a2` | `220448.f1` | 0 | ℤ/2 |
| C2 | 7 | 1568 | `1568a1` | `1568.f2` | 0 | ℤ/2 |
| C6 | 1 | 64 | `64a4` | `64.a4` | 0 | ℤ/2 |
| C3 | 8 | 256 | `256b2` | `256.b2` | 1 | ℤ/2 |
| C4 | 14 | 12544 | `12544b1` | `12544.g2` | 2 | ℤ/2 |
| C5 | −17 | 9248 | `9248g1` | `9248.c1` | 2 | ℤ/2 |

Conductor, rank and torsion are computed from each curve, the rank certified by
matching `RankBounds`. C0 is the curve of the paper and C4 its 2-isogenous
partner; the two make up the whole class `12544b`. Every curve of conductor
12544 in the database was enumerated with its reference and its rank, so the
identification of C0 and C4 is read off the database rather than asserted. The
LMFDB column was obtained separately, by an exact match of Weierstrass
coefficients; the conductor, rank, torsion and analytic order of Ш returned
with each record agree with the in-house values in every case.

The two label columns **disagree as labels while agreeing as curves**: Cremona's
and the LMFDB's isogeny-class letters are different orderings, so this paper's
curve is `12544b2` in one scheme and `12544.g1` in the other, while `12544g1` in
Cremona's scheme is a different curve of rank 0. Conflating the two schemes is
what produced the erroneous identifiers in the earlier draft.

## Where the time goes

| stage | $p = 5$ | $p = 13$ |
| --- | ---: | ---: |
| $[F:\mathbb{Q}] = 2(p-1)$ | 8 | 24 |
| construction of $F$ | 0.03 s | 0.09 s |
| `MaximalOrder` with ramification hint | 0.03 s | 4.48 s |
| `ClassGroup` under GRH | 0.22 s | 27.22 s |
| `pSelmerGroup` | 0.01 s | 0.32 s |
| sum of the instrumented stages | 0.29 s | 32.1 s |
| total wall clock | ≈ 1 s | 515 s |

**The expected wall was not the actual wall.** Before this work the $p = 13$
descent was believed to be blocked at `MaximalOrder` on the degree-24 field,
which had exceeded a 540-second cap. Supplying the ramification —
`MaximalOrder(F : Ramification := [2,7,p])` — removes that stage entirely, from
"does not finish" to 4.5 seconds. An optimised representation of $F$ was not
needed and was not used. What then dominates is a stage that carries no timer of
its own: the eigenspace decomposition, which is everything the four instrumented
stages do not account for. At $p = 13$ that is 515 − 32 ≈ 483 seconds, about 94%
of the run. That stage is not intrinsically expensive: the implementation
applies all $p-2$ non-identity elements of $\Delta$ and prints the whole
eigenvalue spectrum, whereas the bound $b$ needs only a single generator
$\sigma_0$. It was left as it stands because the run finishes and because the
full spectrum is a check on faithfulness, but a reader wanting to push further
should start there and not at the class group.

The ramification hint deserves a word, since passing a wrong one to
`MaximalOrder` produces a non-maximal order silently and would invalidate
everything downstream. It is justified in advance and not by inspection:
$F = K(E[\pi])$ with $K = \mathbb{Q}(i)$, so $F/\mathbb{Q}$ is unramified
outside the primes of bad reduction of $E$, the prime $p$, and the primes
ramifying in $K$ — that is, outside $\{2,7,p\}$, since $\operatorname{disc} K =
-4$. Passing exactly that set is therefore not a guess. As a consistency check
the computed discriminants factor over the hinted set and nothing else:

    disc F = 2^24 · 5^3 · 7^6        (p = 5)
    disc F = 2^72 · 7^18 · 13^11     (p = 13)

with no remaining cofactor in either case.

## The caps that were hit (failures, reported)

Per the standing convention of this project a computation that does not finish
is a result and is recorded with the cap it hit and the fix that was tried, not
omitted. Two runs did not complete.

**The unconditional class group at $p = 13$.** Run with no GRH bound set and
`ClassGroup(OF : Proof := "Full")` under a one-hour cap; killed at the cap.
Magma does not merely fail to finish, it declines in advance, reporting that an
unconditional proof is infeasible, and the Minkowski bound of 3.1 × 10^16 is
why. Fix tried: the ramification hint, which does make the maximal order cheap
and does nothing here, the obstruction being the Minkowski bound and not the
order. We know of no fix. Output: `../data/p13_unconditional.out`.

**The descent at $p = 17$, first attempt.** Run under a one-hour cap with the
ramification hint; after 49 minutes it had not yet printed the order of the
$\pi$-torsion point, so it was still inside the root-finding that precedes the
maximal order, and it was stopped. Diagnosis, from `field_profile.m`: the
hinted maximal order at $p = 17$ costs 15 seconds, so the field is not the
obstruction; root-finding and `Automorphisms` over $F$ want the ring of integers
and, not finding one, trigger an *unhinted* maximal-order computation — the very
computation the hint exists to avoid, fired at a point in the run where the hint
has not been applied. Fix: compute and cache the hinted maximal order
immediately after $F$ is built. This is semantically a no-op and it cleared in
17 seconds the stage the first attempt could not clear in 49 minutes. Output:
`../data/p17_attempt1_stalled.out`.

**The descent at $p = 17$, second attempt.** Run with that fix in place. It
behaved exactly as the diagnosis predicts: the hinted maximal order was cached
in 17.5 seconds — the stage the first attempt could not clear in 49 minutes —
after which the run spent a further 39 minutes in the $\pi$-torsion and
character stage without printing the order of $T$, and was stopped there. So at
$p = 17$ the field is demonstrably not the obstruction, and what remains is the
stage that dominates the runtime. Output: `../data/p17_attempt2_stopped.out`.

## The reach of the method

Separating the field from the descent is what makes the limit of the method
legible, and the separation is the point of `field_profile.m`. On the field side
nothing obstructs $p = 17$:

| $p$ | $[F:\mathbb{Q}]$ | signature | `MaximalOrder` | Cl(F) under GRH | Minkowski bound |
| ---: | ---: | --- | ---: | --- | ---: |
| 5 | 8 | (0,4) | 0.02 s | [20], 0.22 s | 9.9 × 10^4 |
| 13 | 24 | (0,12) | 4.23 s | [260], 25.8 s | 3.1 × 10^16 |
| 17 | 32 | (0,16) | 15.4 s | [68], 190.5 s | 5.7 × 10^22 |
| 29 | 56 | (0,28) | 318 s | — | 4.6 × 10^42 |

The maximal order and the class group are, under GRH and with the ramification
hint, still cheap at $[F:\mathbb{Q}] = 32$; at $[F:\mathbb{Q}] = 56$ the maximal
order costs five minutes and the class group was not computed within a 2400 s
cap. Three obstructions should be kept apart, because only one of them is
intrinsic:

1. the class group **under GRH** is not the limit at the primes reached here —
   three minutes at $p = 17$;
2. the class group **unconditionally** is a genuine limit, and a hard one: the
   Minkowski bound is 99 208 at $p = 5$ and 3.1 × 10^16 at $p = 13$. No hint
   touches this, and it is exactly why the descent theorem is unconditional at 5
   and conditional at 13;
3. the remaining stages of the descent — the $\pi$-torsion point and the
   character, then the eigenspace decomposition — are what dominate the runtime,
   and they were also the stages where the two implementation obstacles above
   sat.

Two of the three obstacles were removed in the course of this work by supplying
information the implementation could not infer — the ramification of $F$, and
the order in which to compute things — and not by any mathematical advance. A
reader who wants to push past the primes reached here should expect the same:
the barrier at moderate $p$ is substantially one of implementation, and only the
unconditional class group is a barrier of principle.

## Reproduction

Each run is a single command of the form

    run.sh -t <cap> -j <name> -o data/<name>.out \
           pi_descent.m pp:=<p> curve:=0,0,0,-56,0 \
           grh:=<on|off> rk:=2 ram:=<primes>

and the wrapper records the command it issued in the output file, so a reader
can reconstruct every run from the outputs alone without consulting this file.
