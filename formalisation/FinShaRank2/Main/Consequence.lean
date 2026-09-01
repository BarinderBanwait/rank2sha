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
# Theorem B (Theorem 3.9) — the arithmetic consequence of a unit second jet

The paper's statement, which `prop_consequence` below renders:

> **Theorem B (Theorem 3.9).** *Let `p ≥ 5` be a split prime of good
> reduction with `p ∉ S_E` and `c̃₂(p) ∈ ℤ_p^×`. Then:*
> *(1) `μ_an(𝔭) = 0` and `λ_an(𝔭) = 2`; (2) `corank_{ℤ_p} Sel_{p^∞}(E/ℚ) = 2`;*
> *(3) `Ш(E/ℚ)[p^∞] = 0`.*

The statement carries no conjectural hypothesis; its content is the implication
from the unit condition at a single prime. The formal statement takes that unit
condition as the hypothesis `hc2`, so no conjectural hypothesis reaches this
theorem, matching the head of the paper's
proof, which records that nothing in it assumes Conjecture 3.4 or Conjecture 3.5.

## Translation conventions

* `c̃₂(p) ∈ ℤ_p^×` ↦ `IsPUnit (…).c2tilde`, the norm-one predicate of `Defs.lean`
  applied to the normalised second jet of `Statements.lean`.
* `μ_an(𝔭) = 0` ↦ `MuZero (…).analytic.Lp`; `λ_an(𝔭) = 2` ↦
  `lambdaAn (…).analytic.Lp = 2`. These are kept **paired** (the junk-value pair, kept
  adjacent): `lambdaAn`
  is a junk-valued `sInf` and is meaningful only under `MuZero`.
* `corank_{ℤ_p} Sel_{p^∞}(E/ℚ) = 2` ↦
  `Module.finrank ℤ_[p] (…).selmer.SelDual = 2` (dual side).
* `Ш(E/ℚ)[p^∞] = 0` ↦ `Subsingleton (…).selmer.ShaDual` (dual side).
* "split prime `p ∉ S`" ↦ the binders `hsplit : p % 4 = 1` and `hpS : p ∉ H.S`.
  `hpS` now carries content: `ClassicalInputs.notAnomalous` is the `S_an` clause
  of (7).
* "non-anomalous" is *not* an assumption of this theorem: it is `H.notAnomalous`
  at `p`, which is a clause of the definition of `S`.

## How non-anomality reaches Proposition 3.3

`Kernel.Anomalous.isPUnit_one_sub_alphaInv_iff`, applied to the `AnalyticData`
field `alpha_root`, turns `H.notAnomalous p …` — the statement `a_p ≢ 1 (mod p)`
in the spelling that lemma uses — into `IsPUnit ((1 : ℚ_[p]) − α_p⁻¹)`, which is
the hypothesis of `Kernel.Normalization.isPUnit_c2tilde_iff`.

Non-anomality is supplied by `ClassicalInputs.notAnomalous` at every split
`p ∉ S`, so no residual hypothesis at `p = 5` is carried here or in
`thm_reduction`.  The proved lemma `Kernel.Anomalous.anomalous_iff_five` gives
the clause unconditionally at every split `p ≥ 13`.

Paper statements rendered here: Theorem B, Lemma 2.3, (7),
Proposition 3.3.
-/

open PowerSeries

namespace FinShaRank2

/-- **Non-anomality at a split prime `p ∉ S`, in the form Proposition 3.3
consumes.** `ClassicalInputs.notAnomalous` is the `S_an` clause of (7),
stated as `a_p ≢ 1 (mod p)`; `Kernel.Anomalous.isPUnit_one_sub_alphaInv_iff`, fed
the `AnalyticData` field `alpha_root`, converts it into the `p`-adic unit
statement for the local factor `1 − α_p⁻¹`.

This is the bridge that lets `prop_consequence` and `thm_reduction` call
`Kernel.Normalization.isPUnit_c2tilde_iff` with no residual `p = 5` hypothesis.
PAPER: (7) (`eq:Sexc`) (`S_an`), Definition 2.2 (`def:anomalous`), Proposition 3.3
(`prop:normalisation`). -/
theorem ClassicalInputs.isPUnit_one_sub_alphaInv (H : ClassicalInputs) {p : ℕ} [Fact p.Prime]
    (hsplit : p % 4 = 1) (hpS : p ∉ H.S) :
    IsPUnit ((1 : ℚ_[p]) -
      (((H.dataAt p Fact.out hsplit hpS).analytic.α : ℤ_[p]) : ℚ_[p])⁻¹) :=
  (isPUnit_one_sub_alphaInv_iff (H.dataAt p Fact.out hsplit hpS).analytic.alpha_root).mpr
    (H.notAnomalous p Fact.out hsplit hpS)

/-- **Theorem B (Theorem 3.9)** at a split prime `p ∉ H.S` whose normalised second jet
`c̃₂(p)` is a `p`-adic unit.

> *(1) `μ_an(𝔭) = 0` and `λ_an(𝔭) = 2`; (2) `corank_{ℤ_p} Sel_{p^∞}(E/ℚ) = 2`;*
> *(3) `Ш(E/ℚ)[p^∞] = 0`.*

The four conclusions are returned in the order `MuZero`, `lambdaAn = 2`,
`finrank = 2`, `Subsingleton ShaDual` — i.e. the paper's (1), (2), (3) with the
μ/λ pair split, kept adjacent so that the junk-value pair stays adjacent.

Assembly route for `prop_consequence`: Proposition 3.3 via
`Kernel.Normalization.isPUnit_c2tilde_iff`, fed non-anomality by
`ClassicalInputs.isPUnit_one_sub_alphaInv`, turns `hc2` into
`IsUnit (coeff 2 Lp)`; Lemma 3.1 (`c0_eq_zero`/`c1_eq_zero`) gives `c₀ = c₁ = 0`;
`Kernel/TsqUnit.lean` factors
`Lp = X² · unit`, yielding `MuZero`/`lambdaAn = 2` and
`Associated (∏ fᵢ) X²` for `iwasawa.rubin_structure`; `selmer_dual_structure`
(`selmer_dual_structure`) plus `iwasawa.control` and `no_finite_submodule`
identify `SelDual ≃ₗ ℤ_p²`; `sha_endgame_of_nonempty` (`sha_endgame_of_nonempty`) then
consumes the five
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
  -- **step 1** Proposition 3.3: the normalised jet is a unit iff `c₂` is.
  --   Non-anomality comes from `H.notAnomalous`, the `S_an` clause of (7).
  have step1 : IsUnit (coeff 2 D.analytic.Lp) :=
    (isPUnit_c2tilde_iff (coeff 2 D.analytic.Lp) _ H.torsSqOverTam
      (H.isPUnit_one_sub_alphaInv hsplit hpS) H.torsSqOverTam_eq).mp hc2
  -- **steps 2 and 3** Lemma 3.1 (`c0_eq_zero`/`c1_eq_zero`), applied to the bundle's `AnalyticData`.
  have step2 : constantCoeff D.analytic.Lp = 0 := c0_eq_zero D.analytic
  have step3 : coeff 1 D.analytic.Lp = 0 := c1_eq_zero D.analytic
  -- **step 4** `Kernel/TsqUnit.lean`: `Lp = T²·unit`, hence `μ = 0`, `λ = 2`, `Associated Lp T²`.
  --   The one adapter in the whole chain: `constantCoeff` ↦ `coeff 0`.
  have step2' : coeff 0 D.analytic.Lp = 0 := by
    rw [coeff_zero_eq_constantCoeff_apply]; exact step2
  have hmu : MuZero D.analytic.Lp := muZero_of_coeffs step2' step3 step1
  have hlam : lambdaAn D.analytic.Lp = 2 := lambdaAn_eq_two_of_coeffs step2' step3 step1
  have hassocLp : Associated D.analytic.Lp ((X : Λ p) ^ 2) :=
    associated_X_sq_of_coeffs step2' step3 step1
  -- **step 5** Mazur control transports the `SelmerData.π_surj` rank bound onto the T-coinvariants.
  have step5 : 2 ≤ Module.finrank ℤ_[p]
      (D.iwasawa.X ⧸ (Ideal.span {(X : Λ p)} • (⊤ : Submodule (Λ p) D.iwasawa.X))) := by
    rw [D.iwasawa.control.finrank_eq]
    exact rank_lower_bound D.selmer.π D.selmer.π_surj
  -- **step 6** Rubin ⊕ structure theorem, fed to `selmer_dual_structure`.
  obtain ⟨n, f, φ, hker, hcok, hchar⟩ := D.iwasawa.rubin_structure
  obtain ⟨hTzero, hXfree⟩ :=
    selmer_dual_structure D.iwasawa.X D.iwasawa.no_finite_submodule φ hker hcok
      (hchar.trans hassocLp) step5
  -- **step 7** collapse the coinvariants, then transport along `control`.
  have step7 : Nonempty (D.selmer.SelDual ≃ₗ[ℤ_[p]] (Fin 2 → ℤ_[p])) := by
    obtain ⟨e⟩ := hXfree
    obtain ⟨q⟩ := quotient_collapse D.iwasawa.X hTzero
    exact ⟨D.iwasawa.control.symm.trans (q.trans e)⟩
  -- **step 8** `sha_endgame_of_nonempty` on `SelmerData`'s five exactness fields.
  have step8 := sha_endgame_of_nonempty D.selmer.ι D.selmer.π D.selmer.ι_inj
    D.selmer.π_surj D.selmer.mw_sha_exact step7
  exact ⟨hmu, hlam, step8.2, step8.1⟩

end FinShaRank2
