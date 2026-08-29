import Mathlib
import FinShaRank2.Defs
import FinShaRank2.Interface.Global

/-!
# Machine-verified certificates: `Certificates H` (task T14)

The project's own **numerical certificates** for the two unconditional corollaries
`cor:sha5`, `cor:sha13` of *Horizontal rigidity for second jets of Katz p-adic
L-functions, with applications to the Tate–Shafarevich group in rank two*.

Kept in a structure **separate** from `ClassicalInputs` (`TASK_BOARD.md` §1: the
epistemic three-way split) so their role — this project's machine-verified
numerics, as opposed to citable classical theorems — is visible to the referee.
`Certificates H` sits over a fixed `H : ClassicalInputs` and records, at the two
anchor primes `p = 5` and `p = 13`:

* their non-membership in the excluded set (`5 ∉ H.S`, `13 ∉ H.S`);
* the traces of Frobenius `a_5 = -2`, `a_13 = -6` (`gp`-verified below);
* the leading `p`-adic digit expansions of `c_2(p) = coeff 2 Lp` (`eq:match5`,
  `eq:pred13`), the datum from which T26 extracts `IsUnit (coeff 2 Lp)` and T34
  wires `cor:sha5`/`cor:sha13`.

## `a_p` verification against PARI/GP (mandated freeze check)

For the testbed curve `E : y² = x³ − 56x` (`ellinit([0,0,0,-56,0])`), on
`/opt/homebrew/bin/gp`:

```
$ echo 'ellap(ellinit([0,0,0,-56,0]),13)' | gp -q
-6
$ echo 'ellap(ellinit([0,0,0,-56,0]),5)' | gp -q
-2
```

So `A13 = -6` and `a_5 = -2`, matching the paper (`sec:testbed` / `cor:sha13`:
"`a_{13} = -6, so #Ẽ(𝔽₁₃) = 20`"; §`sec:anchor`: "`a_5 = -2`"). Both are even, as
CM evenness (`AnalyticData.ap_from_CM`) requires.

## Certificate shape (contract for T26 and T34)

Each digit congruence is stated (`TASK_BOARD.md` §2 conv. 3 — a congruence, not a
bare `IsUnit`) as an **equality in `ZMod (p^k)` of a `PadicInt.toZModPow` image**,
following the T03 recommendation (`NOTES/MathlibAudit.md` §1.4):

```
PadicInt.toZModPow k (PowerSeries.coeff 2 Lp) = ((d : ℤ) : ZMod (p ^ k))
```

with `d` the explicit digit sum written out digit-by-digit to mirror the paper.
This is exactly the shape T26's extraction lemma consumes: reduce further along
`ZMod.castHom (…) (ZMod p)` to `PadicInt.toZMod`, observe the leading digit is `1`
(so `p ∤ d`, i.e. the image in `ZMod p` is nonzero), hence `IsUnit (coeff 2 Lp)`
via `PadicInt.isUnit_iff` / `ker_toZMod = maximalIdeal`. The inner `(d : ℤ)`
annotation makes the integer `d` available for the `¬(p ∣ d)` step.

## Provenance of the digit strings

* `c2_5` (`eq:match5`, seven `5`-adic digits `1 + 4·5 + 3·5² + 5³ + 5⁵ + 5⁶ mod
  5⁷`): produced by **two independent implementations** — PARI σ-height
  computation of the height side and Sage modular symbols of the L-side — which
  agree digit-for-digit (`eq:match5`; §`sec:anchor`).
* `c2_13` (`eq:pred13`, five `13`-adic digits `1 + 11·13 + 13² + 13³ + 10·13⁴ mod
  13⁵`): **pre-registered 2026-06-12** as a full `13`-adic expansion from the
  height side, *before* any modular-symbol computation at `p = 13`; **confirmed
  2026-07-02** by the subsequent modular-symbol computation of `L_13(E,T)` at level
  `12544`, every computed digit agreeing (`eq:pred13`; §`ssec:pred13`).

Both digit strings were cross-checked against `main.tex` (`eq:match5`, `eq:pred13`)
before freezing.

## Local `Fact` instances

`Fact (Nat.Prime 5)` and `Fact (Nat.Prime 13)` are declared as local instances so
that the `ℤ_[5]`/`ℤ_[13]` and `PadicInt.toZModPow`/`ZMod` machinery in the digit
fields resolves. `Fact` is a `Prop`, so by proof irrelevance these are defeq to the
`Fact.mk hp` instances embedded in `dataAt`'s outputs — no instance mismatch.

Paper labels quoted below: `eq:match5`, `eq:pred13`, `cor:sha5`, `cor:sha13`,
`sec:testbed`, `eq:Sexc`.
-/

open PowerSeries

namespace FinShaRank2

/-- `5` is prime — local instance so `ℤ_[5]` / `ZMod (5^k)` machinery resolves in
the digit certificate at the anchor prime `p = 5`. -/
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- `13` is prime — local instance so `ℤ_[13]` / `ZMod (13^k)` machinery resolves
in the digit certificate at the anchor prime `p = 13`. -/
instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- **Numerical certificates over `H : ClassicalInputs`** for the two anchor primes
`p = 5, 13`. Separate from `ClassicalInputs` to keep this project's machine-
verified numerics epistemically distinct from the citable classical inputs
(`TASK_BOARD.md` §1). Consumed by T34 to prove `cor:sha5`, `cor:sha13`
unconditionally. -/
structure Certificates (H : ClassicalInputs) where
  /-- `5 ∉ S`: `5` splits in `ℚ(i)`, `5 ∤ 6N·∏c_v·#tors·d_K = 6·12544·4·2·4`,
  `5` non-anomalous (`a_5 = -2`), `ρ̄_{E,5}` irreducible, `5` not in the
  `lem:comparison` set. Used to invoke `H.dataAt 5`.
  SOURCE: `eq:Sexc` membership check at `5` (`cor:sha5` proof (i)–(iv)).
  PAPER:  `cor:sha5`, `eq:Sexc`. STATUS: certificate. -/
  five_notin : 5 ∉ H.S
  /-- `13 ∉ S`: `13 ≡ 1 (mod 4)` splits, `13 ∤ 6N·∏c_v·#tors·d_K`, `13`
  non-anomalous (`a_13 = -6`), `ρ̄_{E,13}` irreducible, `13` not in the
  `lem:comparison` set. Used to invoke `H.dataAt 13`.
  SOURCE: `eq:Sexc` membership check at `13` (`cor:sha13` proof).
  PAPER:  `cor:sha13`, `eq:Sexc`. STATUS: certificate. -/
  thirteen_notin : 13 ∉ H.S
  /-- **`a_5 = -2`** for `E : y² = x³ − 56x` (PARI: `ellap(…,5) = -2`; paper
  §`sec:anchor`). Feeds `lem:noanomalous` at `p = 5` (`#Ẽ(𝔽₅) = 8`, prime to `5`).
  SOURCE: PARI/GP `ellap(ellinit([0,0,0,-56,0]),5) = -2`; `main.tex` §`sec:anchor`.
  PAPER:  `cor:sha5` proof (ii). STATUS: certificate (`gp`-verified). -/
  a5 : (H.dataAt 5 (by norm_num) (by norm_num) five_notin).analytic.ap = -2
  /-- **`a_13 = -6`** for `E : y² = x³ − 56x` (PARI: `ellap(…,13) = -6`; paper
  `cor:sha13`: "`a_{13} = -6`"). The even value `A13`, feeding `lem:noanomalous`
  at `p = 13` (`#Ẽ(𝔽₁₃) = 20`, prime to `13`).
  SOURCE: PARI/GP `ellap(ellinit([0,0,0,-56,0]),13) = -6`; `main.tex` `cor:sha13`.
  PAPER:  `cor:sha13` proof. STATUS: certificate (`gp`-verified). -/
  a13 : (H.dataAt 13 (by norm_num) (by norm_num) thirteen_notin).analytic.ap = -6
  /-- **`5`-adic digits of `c_2(5)`** (`eq:match5`): the image of `coeff 2 Lp₅`
  under `toZModPow 7` equals the seven-digit sum `1 + 4·5 + 3·5² + 5³ + 5⁵ + 5⁶`
  in `ZMod (5⁷)`. Leading digit `1`, so `5 ∤` the value: T26 extracts
  `IsUnit (coeff 2 Lp₅)` (see the module docstring for the shape/extraction).

  Provenance: two independent implementations — PARI σ-heights (height side) and
  Sage modular symbols (L-side) — agree digit-for-digit (`eq:match5`).
  SOURCE: `eq:match5` (L-side, seven digits mod `5⁷`); PARI σ-height cross-check.
  PAPER:  `eq:match5`, `cor:sha5` proof (v). STATUS: certificate (two
          independent implementations). -/
  c2_5 : PadicInt.toZModPow 7
        (PowerSeries.coeff 2 (H.dataAt 5 (by norm_num) (by norm_num) five_notin).analytic.Lp)
      = ((1 + 4 * 5 + 3 * 5 ^ 2 + 5 ^ 3 + 5 ^ 5 + 5 ^ 6 : ℤ) : ZMod (5 ^ 7))
  /-- **`13`-adic digits of `c_2(13)`** (`eq:pred13`): the image of `coeff 2 Lp₁₃`
  under `toZModPow 5` equals the five-digit sum `1 + 11·13 + 13² + 13³ + 10·13⁴`
  in `ZMod (13⁵)`. Leading digit `1`, so `13 ∤` the value: T26 extracts
  `IsUnit (coeff 2 Lp₁₃)`.

  Provenance: **pre-registered 2026-06-12** (full `13`-adic expansion from the
  height side, before any `p = 13` modular-symbol computation); **confirmed
  2026-07-02** by the modular-symbol computation of `L_13(E,T)` at level `12544`,
  every computed digit agreeing (`eq:pred13`).
  SOURCE: `eq:pred13` (five digits mod `13⁵`); pre-registered height-side
          prediction, confirmed by modular symbols.
  PAPER:  `eq:pred13`, `cor:sha13` proof. STATUS: certificate (pre-registered
          2026-06-12, confirmed 2026-07-02). -/
  c2_13 : PadicInt.toZModPow 5
        (PowerSeries.coeff 2 (H.dataAt 13 (by norm_num) (by norm_num) thirteen_notin).analytic.Lp)
      = ((1 + 11 * 13 + 13 ^ 2 + 13 ^ 3 + 10 * 13 ^ 4 : ℤ) : ZMod (13 ^ 5))

end FinShaRank2
