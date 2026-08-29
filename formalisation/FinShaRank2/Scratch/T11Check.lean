import FinShaRank2.Interface.Analytic

/-! T11 scratch: exercise every field of a hypothetical `AnalyticData`.

Not imported by the root module; ignored by the audit. Confirms each field of
`AnalyticData p h` type-checks at its intended type, and that `ap_from_CM`
yields `2 ∣ ap`. -/

open PowerSeries

namespace T11Check

variable {p : ℕ} [Fact p.Prime] {h : p % 4 = 1} (A : FinShaRank2.AnalyticData p h)

example : FinShaRank2.Λ p := A.Lp
example : ℤ := A.ap
example : ℤ_[p]ˣ := A.α

example : (A.α : ℤ_[p]) ^ 2 - (A.ap : ℤ_[p]) * (A.α : ℤ_[p]) + (p : ℤ_[p]) = 0 :=
  A.alpha_root

example : ℚ := A.modularSymbol0

example : ((constantCoeff A.Lp : ℤ_[p]) : ℚ_[p])
    = (1 - ((A.α : ℤ_[p]) : ℚ_[p])⁻¹) ^ 2 * (A.modularSymbol0 : ℚ_[p]) :=
  A.interp

example : A.modularSymbol0 = 0 := A.msymb_zero

example : ∃ U : FinShaRank2.Λ p, IsUnit U ∧ constantCoeff U = 1 ∧
    A.Lp.subst FinShaRank2.σ = U * A.Lp :=
  A.funct_eq

example : ∃ π : GaussianInt, π.norm = (p : ℤ) ∧ A.ap = 2 * π.re := A.ap_from_CM

example : A.ap ^ 2 ≤ 4 * (p : ℤ) := A.hasse

/-- `ap_from_CM` yields `2 ∣ ap` trivially. -/
example : (2 : ℤ) ∣ A.ap := by
  obtain ⟨π, _, hap⟩ := A.ap_from_CM
  exact ⟨π.re, hap⟩

end T11Check
