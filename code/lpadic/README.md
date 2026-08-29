# `code/lpadic` — the A5 certificates

In-house recomputation of the analytic Iwasawa invariants of

> **E** : `y^2 = x^3 - 56x`, minimal model `[0,0,0,-56,0]`, conductor
> `N = 12544 = 2^8 * 7^2`, CM by `Z[i]`, rank 2, `#tors = 2`, `prod c_v = 4`

at the six split (ordinary) primes `p ∈ {5, 13, 17, 29, 37, 41}`.

## What is being certified, and why it is the whole theorem

`prop:consequence` (`main.tex`:1065) has six hypotheses. Five of them
(splitting, `p ∤ 6N·∏c_v·#tors·d_K`, non-anomalous, `ρ̄_{E,p}` irreducible,
comparison constant a unit) are structural for this curve and hold at all six
primes with no computation beyond `a_p`. The sixth is the numerical one:

    v_p(c_2(p)) = 0,

`c_2(p)` being the `T^2`-coefficient of the Mazur–Swinnerton-Dyer `p`-adic
`L`-function `L_p(E,T)`. By `lem:c0c1` (`main.tex`:884), `c_0 = c_1 = 0`
*exactly* at every good ordinary `p` for this curve, so

    v_p(c_2(p)) = 0   <==>   mu_an(p) = 0  and  lambda_an(p) = 2.

LMFDB reports `λ = 2, μ = 0` at all six primes (`../data/lmfdb_iwasawa.txt`),
but its knowl states **no error bounds**. LMFDB is corroboration; these scripts
produce the certificate the paper cites.

## Files

| file | what it does |
|---|---|
| `certificates.sage` | `L_p(E,T)` by modular symbols at level 12544, Stein–Wuthrich truncation bounds, `v_p(c_2(p))`, digits of `c_2(p)`, `λ_an`/`μ_an`, and the `eq:match5` height-vs-`L` comparison |
| `regulator.sage` | `Reg_p` — implementation 2 of 2 — Sage `E.padic_regulator`, plus an explicit Gram-determinant cross-check on the `main.tex` basis |
| `regulator.gp` | `Reg_p` — implementation 1 of 2 — PARI/GP `ellpadicregulator` |
| `run.sh` | runner: assembles all three into `../data/cert_<p>.out` with a header giving date, host, exact commands and software versions |

## Usage

    ./run.sh <p> <n> [prec_T] [cap_seconds]

e.g. `./run.sh 17 6 5 3600`. Individually:

    P=17 NPREC=14 gp -q regulator.gp
    sage regulator.sage 17 14
    sage certificates.sage 17 6 5 3600

## Precision and cost — read this before choosing `n`

Taken from the Sage source (`sage/schemes/elliptic_curves/padic_lseries.py`),
not guessed. `series(n, prec)` sums `(p-1)·p^(n-1)` measures and truncates the
coefficient of `T^j` to `O(p^{b_j})` with
`b = _e_bounds(n-1, prec) - _c_bound()`.

* `_c_bound() = 0` here, because `ρ̄_{E,p}` is irreducible at every odd `p` for
  this curve. `certificates.sage` prints it, and prints
  `E.galois_representation().is_irreducible(p)` alongside.
* `_e_bounds(n-1, prec)[j] = min_{j'≤j} v_p(binom(p^{n-1}, j'))`, which is
  `n-1` for `2 ≤ j < p`.

Hence:

| quantity | provable bound |
|---|---|
| `c_0` | `O(p^{n+2})` |
| `c_1` | `O(p^{n-1})` |
| `c_2` | `O(p^{n-1})` — i.e. **`n-1` certified base-`p` digits** |
| cost | `(p-1)·p^{n-1}` modular-symbol evaluations |

So the number of certified digits is `n-1` and the cost is exponential in it.
`n = 2` already certifies `v_p(c_2(p)) = 0` when the leading digit is nonzero.

This model reproduces the frozen paper's own displayed precisions exactly:
`p=5, n=8` → `O(5^10) + O(5^7)T + …` (7 digits); `p=13, n=6` → `O(13^8) +
O(13^5)T + …` (5 digits); `p=13, n=5` → 4 digits. All three appear verbatim in
`main.tex` `sec:anchor`/`app:anchor`.

## Caps

`timeout` and `gtimeout` are not on the local macOS PATH. The cap is enforced
inside Sage by `alarm()`: `certificates.sage` takes `cap_seconds` as its fourth
argument, and on expiry prints `CAP HIT` and exits 2 rather than running away.
Long runs are launched in the background with output redirected, never held in a
foreground call.

## Reproducing the frozen anchors

`p = 5` and `p = 13` are run by the same pipeline as the four new primes, as a
control that it reproduces `eq:match5` and `eq:pred13`. See `../../docs/A5_REPORT.md`.
