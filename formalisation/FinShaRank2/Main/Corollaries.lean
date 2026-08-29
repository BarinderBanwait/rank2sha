import Mathlib
import FinShaRank2.Defs
import FinShaRank2.Interface.Global
import FinShaRank2.Interface.Certificates
import FinShaRank2.Kernel.Normalization
import FinShaRank2.Main.Consequence
import FinShaRank2.Main.Dictionary
import FinShaRank2.Statements

/-!
# `cor:sha5` and `cor:sha13` — the two unconditional anchor corollaries (task T34)

Frozen headline signatures (T15 statement freeze; `TASK_BOARD.md` §2 conv. 7).
The proofs are supplied by task T34, the project's headline gate.

> **Corollary (`cor:sha5`).** *`Ш(E/ℚ)[5^∞] = 0`, `corank_{ℤ_5} Sel_{5^∞}(E/ℚ) = 2`,
> `μ_an(5) = 0`, `λ_an(5) = 2`, and the cyclotomic `5`-adic height pairing on
> `E(ℚ)` is nondegenerate. All statements are unconditional.*

> **Corollary (`cor:sha13`).** *`Ш(E/ℚ)[13^∞] = 0`,
> `corank_{ℤ_13} Sel_{13^∞}(E/ℚ) = 2`, `μ_an(13) = 0`, `λ_an(13) = 2`, and the
> cyclotomic `13`-adic height pairing on `E(ℚ)` is nondegenerate. All statements
> are unconditional.*

"Unconditional" means: conditional on the interface `H : ClassicalInputs`
(citable classical theorems) **plus** this project's machine-verified numerics
`C : Certificates H`, and on nothing else. In particular — this is the whole point
of the T15 split (`TASK_BOARD.md` §1, conv. 4) — **no conjectural hypothesis
occurs here**: neither `hyp:sinnott` (`SinnottHyp`) nor `conj:EK`
(`H.deltaE ≠ 0`), both of which live only in `thm_reduction`.

## Translation conventions (`TASK_BOARD.md` §2)

* `corank_{ℤ_p} Sel_{p^∞}(E/ℚ) = 2` ↦
  `Module.finrank ℤ_[p] (…).selmer.SelDual = 2` (conv. 1, dual side).
* `Ш(E/ℚ)[p^∞] = 0` ↦ `Subsingleton (…).selmer.ShaDual` (conv. 1).
* `μ_an(p) = 0` ↦ `MuZero (…).analytic.Lp`; `λ_an(p) = 2` ↦
  `lambdaAn (…).analytic.Lp = 2`, kept adjacent per conv. 5.
* The prime witnesses and the split hypothesis are the literal
  `(by norm_num : (5 : ℕ).Prime)`, `(by norm_num : 5 % 4 = 1)` spellings already
  used by `Certificates.a5` / `Certificates.c2_5`, so `C`'s fields apply to these
  statements' subterms with no adapter (proof irrelevance makes any other witness
  definitionally equal). The `Fact (Nat.Prime 5)` / `Fact (Nat.Prime 13)`
  instances come from `Interface/Certificates.lean`.

## The fifth conclusion (faithfulness item, closed)

The board's original mandated shape (`TASK_BOARD.md` T15) listed **four**
conclusions — corank, Ш, μ, λ — whereas both corollaries in `main.tex` also
assert *"the cyclotomic `p`-adic height pairing on `E(ℚ)` is nondegenerate"*.
The board's sketch therefore under-stated the paper. By PM amendment of
2026-07-30 that fifth conclusion was **restored** to both frozen statements, and
T34 discharges it as `((prop_dictionary (p := 5) H … ).mp hc2).1` — the
`heightNondeg` component of `prop:dictionary`, whose left-hand side these proofs
establish anyway. Both corollaries below therefore carry **all five** of the
paper's conclusions, and the faithfulness item is closed: the formal statements
do not under-state `cor:sha5` / `cor:sha13`.

## Proof route for T34

At `p = 5`: `C.c2_5` → `Kernel.Normalization.isUnit_of_cert_five` gives
`IsUnit (coeff 2 Lp₅)`; `Kernel.Normalization.isPUnit_c2tilde_iff_of_split`
(fed by `H.torsSqOverTam_eq` and by `h5 := fun _ => C.a5`) upgrades it to
`IsPUnit (…).c2tilde`; `prop_consequence` then delivers all four conclusions.
At `p = 13`: identically, with `C.c2_13`, `isUnit_of_cert_thirteen`, and `h5`
vacuous (`13 = 5` is absurd). `C.five_notin` / `C.thirteen_notin` supply
`p ∉ H.S`. `C.a13` is not needed for `h5` (it feeds the `p ≥ 13` Hasse branch of
`lem:noanomalous` only through `AnalyticData.hasse` and `ap_from_CM`, which are
interface fields) but is recorded in `Certificates` as the referee-facing datum.

Paper labels rendered here: `cor:sha5`, `cor:sha13`, `eq:match5`, `eq:pred13`.
-/

open PowerSeries

namespace FinShaRank2

/-- **`cor:sha5`** — the anchor corollary at `p = 5`, unconditional modulo the
interface `H` and the certificates `C`.

> *`Ш(E/ℚ)[5^∞] = 0`, `corank_{ℤ_5} Sel_{5^∞}(E/ℚ) = 2`, `μ_an(5) = 0`,*
> *`λ_an(5) = 2` … All statements are unconditional.*

Conclusions in the board's frozen order: corank, Ш, μ, λ, **and height
nondegeneracy** — the paper's fifth conclusion, restored to the frozen shape by
PM amendment 2026-07-30 after W4-B2 flagged that the board's four-conjunct sketch
under-states the paper. T34 discharges it as `((prop_dictionary H hsplit hpS).mp
hc2).1`.

No conjectural hypothesis occurs (`TASK_BOARD.md` §1): the only inputs are
`H : ClassicalInputs` and `C : Certificates H`.

TRANSLATION: conv. 1 dual side for corank/Ш; conv. 5 μ/λ pairing; the
`(by norm_num)` witnesses match `Certificates`' spelling verbatim. -/
theorem cor_sha5 (H : ClassicalInputs) (C : Certificates H) :
    Module.finrank ℤ_[5]
        (H.dataAt 5 (by norm_num) (by norm_num) C.five_notin).selmer.SelDual = 2
      ∧ Subsingleton (H.dataAt 5 (by norm_num) (by norm_num) C.five_notin).selmer.ShaDual
      ∧ MuZero (H.dataAt 5 (by norm_num) (by norm_num) C.five_notin).analytic.Lp
      ∧ lambdaAn (H.dataAt 5 (by norm_num) (by norm_num) C.five_notin).analytic.Lp = 2
      ∧ (H.dataAt 5 (by norm_num) (by norm_num) C.five_notin).height.heightNondeg := by
  set D := H.dataAt 5 (by norm_num) (by norm_num) C.five_notin with hD
  -- `eq:match5`: the seven-digit certificate `C.c2_5` makes `c₂(5)` a `5`-adic unit.
  have hunit : IsUnit (coeff 2 D.analytic.Lp) := isUnit_of_cert_five C.c2_5
  -- `rmk:normalisation`(i): the normalised jet `c̃₂(5)` is then a unit too. The
  -- residual `a₅ = −2` input of `lem:noanomalous` is the certificate `C.a5`.
  have hc2 : IsPUnit D.c2tilde :=
    (isPUnit_c2tilde_iff_of_split (coeff 2 D.analytic.Lp) H.torsSqOverTam (by norm_num)
      D.analytic.hasse D.analytic.ap_from_CM D.analytic.alpha_root (fun _ => C.a5)
      H.torsSqOverTam_eq).mpr hunit
  -- `prop:consequence` delivers μ, λ, the corank and Ш.
  obtain ⟨hmu, hlam, hrk, hsha⟩ :=
    prop_consequence (p := 5) H (by norm_num) C.five_notin (fun _ => C.a5) hc2
  -- `prop:dictionary`, forward direction, delivers the fifth conclusion.
  exact ⟨hrk, hsha, hmu, hlam,
    ((prop_dictionary (p := 5) H (by norm_num) C.five_notin).mp hc2).1⟩

/-- **`cor:sha13`** — the anchor corollary at `p = 13`, unconditional modulo the
interface `H` and the certificates `C`. The `13`-adic digit certificate
`Certificates.c2_13` was **pre-registered 2026-06-12** from the height side and
confirmed 2026-07-02 by the independent modular-symbol computation
(`eq:pred13`), which is what makes this corollary a prediction rather than a fit.

> *`Ш(E/ℚ)[13^∞] = 0`, `corank_{ℤ_13} Sel_{13^∞}(E/ℚ) = 2`, `μ_an(13) = 0`,*
> *`λ_an(13) = 2` … All statements are unconditional.*

Conclusions in the board's frozen order: corank, Ш, μ, λ, **and height
nondegeneracy** — the paper's fifth conclusion, restored to the frozen shape by
PM amendment 2026-07-30 after W4-B2 flagged that the board's four-conjunct sketch
under-states the paper. T34 discharges it as `((prop_dictionary H hsplit hpS).mp
hc2).1`.

No conjectural hypothesis occurs (`TASK_BOARD.md` §1).

TRANSLATION: as for `cor_sha5`. -/
theorem cor_sha13 (H : ClassicalInputs) (C : Certificates H) :
    Module.finrank ℤ_[13]
        (H.dataAt 13 (by norm_num) (by norm_num) C.thirteen_notin).selmer.SelDual = 2
      ∧ Subsingleton (H.dataAt 13 (by norm_num) (by norm_num) C.thirteen_notin).selmer.ShaDual
      ∧ MuZero (H.dataAt 13 (by norm_num) (by norm_num) C.thirteen_notin).analytic.Lp
      ∧ lambdaAn (H.dataAt 13 (by norm_num) (by norm_num) C.thirteen_notin).analytic.Lp = 2
      ∧ (H.dataAt 13 (by norm_num) (by norm_num) C.thirteen_notin).height.heightNondeg := by
  set D := H.dataAt 13 (by norm_num) (by norm_num) C.thirteen_notin with hD
  -- `eq:pred13`: the five-digit certificate `C.c2_13` makes `c₂(13)` a `13`-adic unit.
  have hunit : IsUnit (coeff 2 D.analytic.Lp) := isUnit_of_cert_thirteen C.c2_13
  -- At `p = 13` the residual `p = 5` hypothesis of `lem:noanomalous` is vacuous.
  have hvac : (13 : ℕ) = 5 → D.analytic.ap = -2 := fun h => absurd h (by norm_num)
  -- `rmk:normalisation`(i): the normalised jet `c̃₂(13)` is then a unit too.
  have hc2 : IsPUnit D.c2tilde :=
    (isPUnit_c2tilde_iff_of_split (coeff 2 D.analytic.Lp) H.torsSqOverTam (by norm_num)
      D.analytic.hasse D.analytic.ap_from_CM D.analytic.alpha_root hvac
      H.torsSqOverTam_eq).mpr hunit
  -- `prop:consequence` delivers μ, λ, the corank and Ш.
  obtain ⟨hmu, hlam, hrk, hsha⟩ :=
    prop_consequence (p := 13) H (by norm_num) C.thirteen_notin hvac hc2
  -- `prop:dictionary`, forward direction, delivers the fifth conclusion.
  exact ⟨hrk, hsha, hmu, hlam,
    ((prop_dictionary (p := 13) H (by norm_num) C.thirteen_notin).mp hc2).1⟩

end FinShaRank2
