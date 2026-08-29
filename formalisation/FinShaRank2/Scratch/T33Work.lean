import Mathlib
import FinShaRank2.Defs
import FinShaRank2.Interface.Global
import FinShaRank2.Interface.Katz
import FinShaRank2.Kernel.Decoupling
import FinShaRank2.Kernel.FunctionalEquation
import FinShaRank2.Kernel.GradingValuation
import FinShaRank2.Kernel.Normalization
import FinShaRank2.Main.Consequence
import FinShaRank2.Statements

/-!
Scratch work for T33 (`thm:reduction`).  Not root-imported, not audited.
-/

open PowerSeries

namespace FinShaRank2
namespace T33Work

theorem thm_reduction' (H : ClassicalInputs)
    (h87 : H.deltaE ≠ 0)
    (h86 : ∀ (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1) (hpS : p ∉ H.S),
      letI : Fact p.Prime := ⟨hp⟩
      SinnottHyp p (H.dataAt p hp hsplit hpS).analytic.Lp (H.dataAt p hp hsplit hpS).katz)
    (h5 : ∀ (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1) (hpS : p ∉ H.S),
      letI : Fact p.Prime := ⟨hp⟩
      p = 5 → (H.dataAt p hp hsplit hpS).analytic.ap = -2) :
    ConjStrong H
      ∧ ∀ (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1) (hpS : p ∉ H.S),
          padicValRat p H.deltaE = 0 →
            letI : Fact p.Prime := ⟨hp⟩
            MuZero (H.dataAt p hp hsplit hpS).analytic.Lp
              ∧ lambdaAn (H.dataAt p hp hsplit hpS).analytic.Lp = 2
              ∧ Subsingleton (H.dataAt p hp hsplit hpS).selmer.ShaDual := by
  have key : ∀ (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1) (hpS : p ∉ H.S),
      padicValRat p H.deltaE = 0 →
        letI : Fact p.Prime := ⟨hp⟩
        IsPUnit (H.dataAt p hp hsplit hpS).c2tilde := by
    intro p hp hsplit hpS hval
    letI : Fact p.Prime := ⟨hp⟩
    set D := H.dataAt p hp hsplit hpS with hDdef
    -- step 1
    have hne : D.katz.deltaE_local ≠ 0 := by rw [D.deltaE_tie]; exact h87
    have hval' : padicValRat p D.katz.deltaE_local = 0 := by rw [D.deltaE_tie]; exact hval
    -- step 2
    have hnv : D.katz.NonvanishingOnDE := D.katz.resultant_link hne hval'
    -- step 3
    have hsin := h86 p hp hsplit hpS
    have htr : D.katz.traceClass ≠ 0 := hsin.nonvanishing hnv
    have hres : IsLocalRing.residue D.katz.W D.katz.m2core ≠ 0 := by
      rw [hsin.presentation]; exact htr
    -- step 4
    have hpne : (p : D.katz.W) ≠ 0 := by
      intro h
      have h0 : (p : ℤ_[p]) = 0 := by
        apply D.katz.algInj
        rw [map_natCast, map_zero]
        exact h
      exact (Nat.cast_ne_zero.mpr hp.ne_zero) h0
    obtain ⟨κ₀, hcong⟩ := D.katz.grading_congr
    have hLK : IsUnit (coeff 2 D.katz.LKatz) :=
      (isUnit_iff_residue_ne_zero_of_grading_congr D.katz.maxIdeal_eq_p hpne κ₀ _ _ hcong).mpr hres
    -- step 5
    obtain ⟨c, u, hcomp⟩ := D.katz.comparison
    haveI := D.katz.algMap_isLocalHom
    have hu0 : IsUnit (coeff 0 (u : PowerSeries D.katz.W)) := by
      rw [coeff_zero_eq_constantCoeff]
      exact u.isUnit.map (constantCoeff (R := D.katz.W))
    have hc0 : constantCoeff D.analytic.Lp = 0 := by
      have h := D.analytic.interp
      rw [D.analytic.msymb_zero] at h
      simp only [Rat.cast_zero, mul_zero] at h
      exact PadicInt.coe_eq_zero.mp h
    have hc0' : coeff 0 D.analytic.Lp = 0 := by
      rw [coeff_zero_eq_constantCoeff_apply]; exact hc0
    have hc1 : coeff 1 D.analytic.Lp = 0 := by
      obtain ⟨U, _hU, hU0, hFE⟩ := D.analytic.funct_eq
      exact coeff_one_Lp_eq_zero D.analytic.Lp U hU0 hFE hc0
    have hmul1 : ∀ A B : PowerSeries D.katz.W,
        coeff 1 (A * B) = coeff 0 A * coeff 1 B + coeff 1 A * coeff 0 B := by
      intro A B
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp [Finset.sum_range_succ]
    have hmul0 : ∀ A B : PowerSeries D.katz.W,
        coeff 0 (A * B) = coeff 0 A * coeff 0 B := by
      intro A B
      rw [coeff_zero_eq_constantCoeff, map_mul]
    have hK0 : coeff 0 D.katz.LKatz = 0 := by
      have h : coeff 0 (D.analytic.Lp.map (algebraMap ℤ_[p] D.katz.W)) = 0 := by
        rw [coeff_map, hc0', map_zero]
      rw [hcomp, Decoupling.coeff_smul_eq_mul, hmul0] at h
      rw [c.isUnit.mul_right_eq_zero, hu0.mul_right_eq_zero] at h
      exact h
    have hK1 : coeff 1 D.katz.LKatz = 0 := by
      have h : coeff 1 (D.analytic.Lp.map (algebraMap ℤ_[p] D.katz.W)) = 0 := by
        rw [coeff_map, hc1, map_zero]
      rw [hcomp, Decoupling.coeff_smul_eq_mul, hmul1, hK0, mul_zero, add_zero] at h
      rw [c.isUnit.mul_right_eq_zero, hu0.mul_right_eq_zero] at h
      exact h
    have hLp2 : IsUnit (coeff 2 D.analytic.Lp) :=
      Decoupling.isUnit_coeff_two_of_comparison (algebraMap ℤ_[p] D.katz.W)
        D.analytic.Lp D.katz.LKatz c u hcomp hK0 hK1 hLK
    -- step 6
    exact (isPUnit_c2tilde_iff_of_split (coeff 2 D.analytic.Lp) H.torsSqOverTam hsplit
      D.analytic.hasse D.analytic.ap_from_CM D.analytic.alpha_root (h5 p hp hsplit hpS)
      H.torsSqOverTam_eq).mpr hLp2
  refine ⟨fun p hp hsplit hpS _ hval => key p hp hsplit hpS hval, ?_⟩
  intro p hp hsplit hpS hval
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hmu, hlam, _, hsha⟩ :=
    prop_consequence H hsplit hpS (h5 p hp hsplit hpS) (key p hp hsplit hpS hval)
  exact ⟨hmu, hlam, hsha⟩

theorem conjStrong_only (H : ClassicalInputs)
    (h87 : H.deltaE ≠ 0)
    (h86 : ∀ (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1) (hpS : p ∉ H.S),
      letI : Fact p.Prime := ⟨hp⟩
      SinnottHyp p (H.dataAt p hp hsplit hpS).analytic.Lp (H.dataAt p hp hsplit hpS).katz)
    (h5 : ∀ (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1) (hpS : p ∉ H.S),
      letI : Fact p.Prime := ⟨hp⟩
      p = 5 → (H.dataAt p hp hsplit hpS).analytic.ap = -2) :
    ∀ (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1) (hpS : p ∉ H.S),
    padicValRat p H.deltaE = 0 →
      letI : Fact p.Prime := ⟨hp⟩
      IsPUnit (H.dataAt p hp hsplit hpS).c2tilde := by
  intro p hp hsplit hpS hval
  letI : Fact p.Prime := ⟨hp⟩
  set D := H.dataAt p hp hsplit hpS with hDdef
  -- step 1
  have hne : D.katz.deltaE_local ≠ 0 := by rw [D.deltaE_tie]; exact h87
  have hval' : padicValRat p D.katz.deltaE_local = 0 := by rw [D.deltaE_tie]; exact hval
  -- step 2
  have hnv : D.katz.NonvanishingOnDE := D.katz.resultant_link hne hval'
  -- step 3
  have hsin := h86 p hp hsplit hpS
  have htr : D.katz.traceClass ≠ 0 := hsin.nonvanishing hnv
  have hres : IsLocalRing.residue D.katz.W D.katz.m2core ≠ 0 := by
    rw [hsin.presentation]; exact htr
  -- step 4
  have hpne : (p : D.katz.W) ≠ 0 := by
    intro h
    have h0 : (p : ℤ_[p]) = 0 := by
      apply D.katz.algInj
      rw [map_natCast, map_zero]
      exact h
    exact (Nat.cast_ne_zero.mpr hp.ne_zero) h0
  obtain ⟨κ₀, hcong⟩ := D.katz.grading_congr
  have hLK : IsUnit (coeff 2 D.katz.LKatz) :=
    (isUnit_iff_residue_ne_zero_of_grading_congr D.katz.maxIdeal_eq_p hpne κ₀ _ _ hcong).mpr hres
  -- step 5
  obtain ⟨c, u, hcomp⟩ := D.katz.comparison
  haveI := D.katz.algMap_isLocalHom
  have hu0 : IsUnit (coeff 0 (u : PowerSeries D.katz.W)) := by
    rw [coeff_zero_eq_constantCoeff]
    exact u.isUnit.map (constantCoeff (R := D.katz.W))
  have hc0 : constantCoeff D.analytic.Lp = 0 := by
    have h := D.analytic.interp
    rw [D.analytic.msymb_zero] at h
    simp only [Rat.cast_zero, mul_zero] at h
    exact PadicInt.coe_eq_zero.mp h
  have hc0' : coeff 0 D.analytic.Lp = 0 := by
    rw [coeff_zero_eq_constantCoeff_apply]; exact hc0
  have hc1 : coeff 1 D.analytic.Lp = 0 := by
    obtain ⟨U, _hU, hU0, hFE⟩ := D.analytic.funct_eq
    exact coeff_one_Lp_eq_zero D.analytic.Lp U hU0 hFE hc0
  have hmul1 : ∀ A B : PowerSeries D.katz.W,
      coeff 1 (A * B) = coeff 0 A * coeff 1 B + coeff 1 A * coeff 0 B := by
    intro A B
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp [Finset.sum_range_succ]
  have hmul0 : ∀ A B : PowerSeries D.katz.W,
      coeff 0 (A * B) = coeff 0 A * coeff 0 B := by
    intro A B
    rw [coeff_zero_eq_constantCoeff, map_mul]
  have hK0 : coeff 0 D.katz.LKatz = 0 := by
    have h : coeff 0 (D.analytic.Lp.map (algebraMap ℤ_[p] D.katz.W)) = 0 := by
      rw [coeff_map, hc0', map_zero]
    rw [hcomp, Decoupling.coeff_smul_eq_mul, hmul0] at h
    rw [c.isUnit.mul_right_eq_zero, hu0.mul_right_eq_zero] at h
    exact h
  have hK1 : coeff 1 D.katz.LKatz = 0 := by
    have h : coeff 1 (D.analytic.Lp.map (algebraMap ℤ_[p] D.katz.W)) = 0 := by
      rw [coeff_map, hc1, map_zero]
    rw [hcomp, Decoupling.coeff_smul_eq_mul, hmul1, hK0, mul_zero, add_zero] at h
    rw [c.isUnit.mul_right_eq_zero, hu0.mul_right_eq_zero] at h
    exact h
  have hLp2 : IsUnit (coeff 2 D.analytic.Lp) :=
    Decoupling.isUnit_coeff_two_of_comparison (algebraMap ℤ_[p] D.katz.W)
      D.analytic.Lp D.katz.LKatz c u hcomp hK0 hK1 hLK
  -- step 6
  exact (isPUnit_c2tilde_iff_of_split (coeff 2 D.analytic.Lp) H.torsSqOverTam hsplit
    D.analytic.hasse D.analytic.ap_from_CM D.analytic.alpha_root (h5 p hp hsplit hpS)
    H.torsSqOverTam_eq).mpr hLp2

end T33Work
end FinShaRank2

#print axioms FinShaRank2.T33Work.thm_reduction'
#print axioms FinShaRank2.prop_consequence
#print axioms FinShaRank2.T33Work.conjStrong_only
