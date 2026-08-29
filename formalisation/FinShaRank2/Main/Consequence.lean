import Mathlib
import FinShaRank2.Defs
import FinShaRank2.Interface.Global
import FinShaRank2.Kernel.LambdaModule
import FinShaRank2.Kernel.Normalization
import FinShaRank2.Kernel.ShaEndgame
import FinShaRank2.Kernel.TsqUnit
import FinShaRank2.Main.Lemma41
import FinShaRank2.Statements

/-!
# `prop:consequence` — the arithmetic consequence of a unit second jet (task T31)

Frozen headline signature (T15 statement freeze; `TASK_BOARD.md` §2 conv. 7).
The proof is supplied by task T31.

> **Proposition (`prop:consequence`).** *Assume Conjecture `conj:weak`. Then for
> every non-anomalous split prime `p ∉ S` with `c̃₂(p) ∈ ℤ_p^×` one has:*
> *(1) `μ_an(𝔭) = 0` and `λ_an(𝔭) = 2`; (2) `corank_{ℤ_p} Sel_{p^∞}(E/ℚ) = 2`;*
> *(3) `Ш(E/ℚ)[p^∞] = 0`.*

`conj:weak` is quoted in the paper only to *produce* the hypothesis
`c̃₂(p) ∈ ℤ_p^×` at all but finitely many split primes; the proposition's own
content is the implication from that unit condition at a single prime. The formal
statement therefore takes the unit condition as the hypothesis `hc2` and mentions
no conjecture — matching `TASK_BOARD.md` §1 (no conjectural hypothesis outside
`thm_reduction`) and the paper's own remark that the proof "is unconditional once
`v_p(c₂(p)) = 0` is certified" (`cor:sha5` proof).

## Translation conventions (`TASK_BOARD.md` §2)

* `c̃₂(p) ∈ ℤ_p^×` ↦ `IsPUnit (…).c2tilde`, the norm-one predicate of `Defs.lean`
  applied to the normalised second jet of `Statements.lean`.
* `μ_an(𝔭) = 0` ↦ `MuZero (…).analytic.Lp`; `λ_an(𝔭) = 2` ↦
  `lambdaAn (…).analytic.Lp = 2`. These are kept **paired** (conv. 5): `lambdaAn`
  is a junk-valued `sInf` and is meaningful only under `MuZero`.
* `corank_{ℤ_p} Sel_{p^∞}(E/ℚ) = 2` ↦
  `Module.finrank ℤ_[p] (…).selmer.SelDual = 2` (conv. 1, dual side).
* `Ш(E/ℚ)[p^∞] = 0` ↦ `Subsingleton (…).selmer.ShaDual` (conv. 1, dual side).
* "split prime `p ∉ S`" ↦ the binders `hsplit : p % 4 = 1` and `hpS : p ∉ H.S`.
  `hpS` now carries content: `ClassicalInputs.notAnomalous` is the `S_an` clause
  of `eq:Sexc`.
* "non-anomalous" is *not* an assumption of this theorem: it is `H.notAnomalous`
  at `p`, which is a clause of the definition of `S`.

## How non-anomality reaches `rmk:normalisation`(i)

`Kernel.Anomalous.isPUnit_one_sub_alphaInv_iff`, applied to the `AnalyticData`
field `alpha_root`, turns `H.notAnomalous p …` — the statement `a_p ≢ 1 (mod p)`
in the spelling that lemma uses — into `IsPUnit ((1 : ℚ_[p]) − α_p⁻¹)`, which is
the hypothesis of `Kernel.Normalization.isPUnit_c2tilde_iff`.

Until R2a this theorem instead carried a residual hypothesis

```
h5 : p = 5 → (H.dataAt p Fact.out hsplit hpS).analytic.ap = -2
```

because `S : Finset ℕ` was opaque data and `p ∉ H.S` had no formal non-anomality
content. `notAnomalous` supplies that content at every split `p ∉ S`, so `h5` is
gone from this theorem and from `thm_reduction`. The proved non-anomality lemma
`lem:noanomalous`(2) is not discarded: `Kernel.Anomalous.anomalous_iff_five`
still gives the clause unconditionally at every split `p ≥ 13`.

Paper labels rendered here: `prop:consequence`, `lem:noanomalous`, `eq:Sexc`,
`rmk:normalisation`(i).
-/

open PowerSeries

namespace FinShaRank2

/-- **Non-anomality at a split prime `p ∉ S`, in the form `rmk:normalisation`(i)
consumes.** `ClassicalInputs.notAnomalous` is the `S_an` clause of `eq:Sexc`,
stated as `a_p ≢ 1 (mod p)`; `Kernel.Anomalous.isPUnit_one_sub_alphaInv_iff`, fed
the `AnalyticData` field `alpha_root`, converts it into the `p`-adic unit
statement for the local factor `1 − α_p⁻¹`.

This is the bridge that lets `prop_consequence` and `thm_reduction` call
`Kernel.Normalization.isPUnit_c2tilde_iff` with no residual `p = 5` hypothesis.
PAPER: `eq:Sexc` (`S_an`), `def:anomalous`, `rmk:normalisation`(i). -/
theorem ClassicalInputs.isPUnit_one_sub_alphaInv (H : ClassicalInputs) {p : ℕ} [Fact p.Prime]
    (hsplit : p % 4 = 1) (hpS : p ∉ H.S) :
    IsPUnit ((1 : ℚ_[p]) -
      (((H.dataAt p Fact.out hsplit hpS).analytic.α : ℤ_[p]) : ℚ_[p])⁻¹) :=
  (isPUnit_one_sub_alphaInv_iff (H.dataAt p Fact.out hsplit hpS).analytic.alpha_root).mpr
    (H.notAnomalous p Fact.out hsplit hpS)

/-- **`prop:consequence`** at a split prime `p ∉ H.S` whose normalised second jet
`c̃₂(p)` is a `p`-adic unit.

> *(1) `μ_an(𝔭) = 0` and `λ_an(𝔭) = 2`; (2) `corank_{ℤ_p} Sel_{p^∞}(E/ℚ) = 2`;*
> *(3) `Ш(E/ℚ)[p^∞] = 0`.*

The four conclusions are returned in the order `MuZero`, `lambdaAn = 2`,
`finrank = 2`, `Subsingleton ShaDual` — i.e. the paper's (1), (2), (3) with the
μ/λ pair split, kept adjacent per conv. 5.

Assembly route for T31 (`TASK_BOARD.md`): `rmk:normalisation`(i) via
`Kernel.Normalization.isPUnit_c2tilde_iff`, fed non-anomality by
`ClassicalInputs.isPUnit_one_sub_alphaInv`, turns `hc2` into
`IsUnit (coeff 2 Lp)`; `lem:c0c1` (T30) gives `c₀ = c₁ = 0`; T21 factors
`Lp = X² · unit`, yielding `MuZero`/`lambdaAn = 2` and
`Associated (∏ fᵢ) X²` for `iwasawa.rubin_structure`; T23
(`selmer_dual_structure`) plus `iwasawa.control` and `no_finite_submodule`
identify `SelDual ≃ₗ ℤ_p²`; T27 (`sha_endgame_of_nonempty`) then consumes the five
`SelmerData` exactness fields to deliver `Subsingleton ShaDual` and `finrank = 2`.

`hsplit`/`hpS` are the paper's "split `p ∉ S`". No conjectural hypothesis appears.

TRANSLATION: see the module docstring (dual-side coranks, `IsPUnit`,
`MuZero`/`lambdaAn` pairing). -/
theorem prop_consequence (H : ClassicalInputs) {p : ℕ} [Fact p.Prime]
    (hsplit : p % 4 = 1) (hpS : p ∉ H.S)
    (hc2 : IsPUnit (H.dataAt p Fact.out hsplit hpS).c2tilde) :
    MuZero (H.dataAt p Fact.out hsplit hpS).analytic.Lp
      ∧ lambdaAn (H.dataAt p Fact.out hsplit hpS).analytic.Lp = 2
      ∧ Module.finrank ℤ_[p] (H.dataAt p Fact.out hsplit hpS).selmer.SelDual = 2
      ∧ Subsingleton (H.dataAt p Fact.out hsplit hpS).selmer.ShaDual := by
  set D := H.dataAt p Fact.out hsplit hpS with hDdef
  -- **step 1** `rmk:normalisation`(i): the normalised jet is a unit iff `c₂` is.
  --   Non-anomality comes from `H.notAnomalous`, the `S_an` clause of `eq:Sexc`.
  have step1 : IsUnit (coeff 2 D.analytic.Lp) :=
    (isPUnit_c2tilde_iff (coeff 2 D.analytic.Lp) _ H.torsSqOverTam
      (H.isPUnit_one_sub_alphaInv hsplit hpS) H.torsSqOverTam_eq).mp hc2
  -- **steps 2 and 3** `lem:c0c1` (T30), applied to the bundle's `AnalyticData`.
  have step2 : constantCoeff D.analytic.Lp = 0 := c0_eq_zero D.analytic
  have step3 : coeff 1 D.analytic.Lp = 0 := c1_eq_zero D.analytic
  -- **step 4** T21: `Lp = T²·unit`, hence `μ = 0`, `λ = 2`, `Associated Lp T²`.
  --   The one adapter in the whole chain: `constantCoeff` ↦ `coeff 0`.
  have step2' : coeff 0 D.analytic.Lp = 0 := by
    rw [coeff_zero_eq_constantCoeff_apply]; exact step2
  have hmu : MuZero D.analytic.Lp := muZero_of_coeffs step2' step3 step1
  have hlam : lambdaAn D.analytic.Lp = 2 := lambdaAn_eq_two_of_coeffs step2' step3 step1
  have hassocLp : Associated D.analytic.Lp ((X : Λ p) ^ 2) :=
    associated_X_sq_of_coeffs step2' step3 step1
  -- **step 5** Mazur control transports the T25 rank bound onto the T-coinvariants.
  have step5 : 2 ≤ Module.finrank ℤ_[p]
      (D.iwasawa.X ⧸ (Ideal.span {(X : Λ p)} • (⊤ : Submodule (Λ p) D.iwasawa.X))) := by
    rw [D.iwasawa.control.finrank_eq]
    exact rank_lower_bound D.selmer.π D.selmer.π_surj
  -- **step 6** Rubin ⊕ structure theorem, fed to T23.
  obtain ⟨n, f, φ, hker, hcok, hchar⟩ := D.iwasawa.rubin_structure
  obtain ⟨hTzero, hXfree⟩ :=
    selmer_dual_structure D.iwasawa.X D.iwasawa.no_finite_submodule φ hker hcok
      (hchar.trans hassocLp) step5
  -- **step 7** collapse the coinvariants, then transport along `control`.
  have step7 : Nonempty (D.selmer.SelDual ≃ₗ[ℤ_[p]] (Fin 2 → ℤ_[p])) := by
    obtain ⟨e⟩ := hXfree
    obtain ⟨q⟩ := quotient_collapse D.iwasawa.X hTzero
    exact ⟨D.iwasawa.control.symm.trans (q.trans e)⟩
  -- **step 8** T27 on `SelmerData`'s five exactness fields.
  have step8 := sha_endgame_of_nonempty D.selmer.ι D.selmer.π D.selmer.ι_inj
    D.selmer.π_surj D.selmer.mw_sha_exact step7
  exact ⟨hmu, hlam, step8.2, step8.1⟩

end FinShaRank2
