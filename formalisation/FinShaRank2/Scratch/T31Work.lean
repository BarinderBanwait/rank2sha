import Mathlib
import FinShaRank2.Defs
import FinShaRank2.Interface.Global
import FinShaRank2.Interface.Analytic
import FinShaRank2.Kernel.FunctionalEquation
import FinShaRank2.Kernel.TsqUnit
import FinShaRank2.Kernel.LambdaModule
import FinShaRank2.Kernel.Normalization
import FinShaRank2.Kernel.ShaEndgame
import FinShaRank2.Main.Consequence
import FinShaRank2.Main.Lemma41
import FinShaRank2.Statements

/-!
Scratch work for agent W5-A2: Part 1 (promotion of `quotient_collapse` /
`rank_lower_bound`), Part 2 (T30 `lem:c0c1`), Part 3 (T31 `prop:consequence`).
Not root-imported, not audited.
-/

open PowerSeries

namespace FinShaRank2
namespace T31Work

variable {p : ℕ} [Fact p.Prime]

/-! ### Part 1 — the two promoted kernel lemmas (verbatim from `Scratch/T15Chain.lean`) -/

theorem quotient_collapse (M : Type) [AddCommGroup M] [Module (Λ p) M] [Module ℤ_[p] M]
    [IsScalarTower ℤ_[p] (Λ p) M] (hzero : ∀ x : M, (X : Λ p) • x = 0) :
    Nonempty ((M ⧸ (Ideal.span {(X : Λ p)} • (⊤ : Submodule (Λ p) M))) ≃ₗ[ℤ_[p]] M) := by
  have hbot : (Ideal.span {(X : Λ p)} • (⊤ : Submodule (Λ p) M)) = ⊥ := by
    refine le_antisymm (Submodule.smul_le.mpr ?_) bot_le
    intro r hr m _
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    rw [Submodule.mem_bot, mul_smul, hzero, smul_zero]
  exact ⟨(Submodule.quotEquivOfEqBot _ hbot).restrictScalars ℤ_[p]⟩

theorem rank_lower_bound {N : Type} [AddCommGroup N] [Module ℤ_[p] N] [Module.Finite ℤ_[p] N]
    (π : N →ₗ[ℤ_[p]] (Fin 2 → ℤ_[p])) (hπ : Function.Surjective π) :
    2 ≤ Module.finrank ℤ_[p] N := by
  have h := LinearMap.finrank_le_finrank_of_surjective (f := π) hπ
  rwa [Module.finrank_fin_fun] at h

/-! ### Part 2 — T30 `lem:c0c1`, generalized to a bare `AnalyticData` -/

theorem c0_eq_zero {p : ℕ} [Fact p.Prime] {hsplit : p % 4 = 1}
    (A : AnalyticData p hsplit) : constantCoeff A.Lp = 0 := by
  have h := A.interp
  rw [A.msymb_zero] at h
  simp only [Rat.cast_zero, mul_zero] at h
  exact PadicInt.coe_eq_zero.mp h

theorem c1_eq_zero {p : ℕ} [Fact p.Prime] {hsplit : p % 4 = 1}
    (A : AnalyticData p hsplit) : coeff 1 A.Lp = 0 := by
  obtain ⟨U, _hUunit, hU0, hFE⟩ := A.funct_eq
  exact coeff_one_Lp_eq_zero A.Lp U hU0 hFE (c0_eq_zero A)

/-! ### Part 3 — T31 `prop:consequence` -/

theorem prop_consequence (H : ClassicalInputs) {p : ℕ} [Fact p.Prime]
    (hsplit : p % 4 = 1) (hpS : p ∉ H.S)
    (h5 : p = 5 → (H.dataAt p Fact.out hsplit hpS).analytic.ap = -2)
    (hc2 : IsPUnit (H.dataAt p Fact.out hsplit hpS).c2tilde) :
    MuZero (H.dataAt p Fact.out hsplit hpS).analytic.Lp
      ∧ lambdaAn (H.dataAt p Fact.out hsplit hpS).analytic.Lp = 2
      ∧ Module.finrank ℤ_[p] (H.dataAt p Fact.out hsplit hpS).selmer.SelDual = 2
      ∧ Subsingleton (H.dataAt p Fact.out hsplit hpS).selmer.ShaDual := by
  set D := H.dataAt p Fact.out hsplit hpS with hDdef
  -- **step 1** `rmk:normalisation`(i)
  have step1 : IsUnit (coeff 2 D.analytic.Lp) :=
    (isPUnit_c2tilde_iff_of_split (coeff 2 D.analytic.Lp) H.torsSqOverTam hsplit
      D.analytic.hasse D.analytic.ap_from_CM D.analytic.alpha_root h5
      H.torsSqOverTam_eq).mp hc2
  -- **step 2** and **step 3**: `lem:c0c1` (T30)
  have step2 : constantCoeff D.analytic.Lp = 0 := c0_eq_zero D.analytic
  have step3 : coeff 1 D.analytic.Lp = 0 := c1_eq_zero D.analytic
  -- **step 4** T21
  have step2' : coeff 0 D.analytic.Lp = 0 := by
    rw [coeff_zero_eq_constantCoeff_apply]; exact step2
  have hmu : MuZero D.analytic.Lp := muZero_of_coeffs step2' step3 step1
  have hlam : lambdaAn D.analytic.Lp = 2 := lambdaAn_eq_two_of_coeffs step2' step3 step1
  have hassocLp : Associated D.analytic.Lp ((X : Λ p) ^ 2) :=
    associated_X_sq_of_coeffs step2' step3 step1
  -- **step 5** Mazur control + promoted `rank_lower_bound`
  have step5 : 2 ≤ Module.finrank ℤ_[p]
      (D.iwasawa.X ⧸ (Ideal.span {(X : Λ p)} • (⊤ : Submodule (Λ p) D.iwasawa.X))) := by
    rw [D.iwasawa.control.finrank_eq]
    exact rank_lower_bound D.selmer.π D.selmer.π_surj
  -- **step 6** Rubin ⊕ structure theorem, fed to T23
  obtain ⟨n, f, φ, hker, hcok, hchar⟩ := D.iwasawa.rubin_structure
  obtain ⟨hTzero, hXfree⟩ :=
    selmer_dual_structure D.iwasawa.X D.iwasawa.no_finite_submodule φ hker hcok
      (hchar.trans hassocLp) step5
  -- **step 7** promoted `quotient_collapse`, then transport along `control`
  have step7 : Nonempty (D.selmer.SelDual ≃ₗ[ℤ_[p]] (Fin 2 → ℤ_[p])) := by
    obtain ⟨e⟩ := hXfree
    obtain ⟨q⟩ := quotient_collapse D.iwasawa.X hTzero
    exact ⟨D.iwasawa.control.symm.trans (q.trans e)⟩
  -- **step 8** T27
  have step8 := sha_endgame_of_nonempty D.selmer.ι D.selmer.π D.selmer.ι_inj
    D.selmer.π_surj D.selmer.mw_sha_exact step7
  exact ⟨hmu, hlam, step8.2, step8.1⟩

end T31Work
end FinShaRank2

#print axioms FinShaRank2.T31Work.quotient_collapse
#print axioms FinShaRank2.T31Work.rank_lower_bound
#print axioms FinShaRank2.T31Work.c0_eq_zero
#print axioms FinShaRank2.T31Work.c1_eq_zero
#print axioms FinShaRank2.T31Work.prop_consequence

-- Acceptance criterion 3: the LANDED declarations.
#print axioms FinShaRank2.c0_eq_zero
#print axioms FinShaRank2.c1_eq_zero
#print axioms FinShaRank2.prop_consequence
#print axioms FinShaRank2.quotient_collapse
#print axioms FinShaRank2.rank_lower_bound
