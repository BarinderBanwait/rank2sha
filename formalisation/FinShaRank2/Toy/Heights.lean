import FinShaRank2.Interface.Heights
import FinShaRank2.Toy.Analytic

/-!
# Toy height layer: `Toy.toyHeight`

The height / p-adic-BSD layer of the non-vacuity instance. The toy world takes
`Reg_γ := 1`, `shaOrd := 1`, `heightNondeg := True`, and — forced by the `ClassicalInputs`
tie-equation `c2norm_tie` — the normalised jet

`c2norm := c̃₂ = coeff₂(X²) · (1 − α⁻¹)⁻² · 1 = (1 − α⁻¹)⁻²`.

Everything then reduces to the single quantitative fact that the toy prime is
**non-anomalous**: `α − 1` is a `ℤ_[p]`-unit (`Setup.alpha_sub_one_unit`, proved
in `Toy/Analytic.lean` from `α ≡ 2a` and `0 < 2a − 1 < p`), whence
`‖1 − α⁻¹‖ = 1` and `c2norm` is a p-adic unit. Both `spr_*` fields are then
equalities/equivalences between true statements.
-/

namespace FinShaRank2

namespace Toy

variable {p : ℕ} [Fact p.Prime]

/-- The inverse unit root, computed inside `ℤ_[p]`: `((α : ℤ_[p]) : ℚ_[p])⁻¹` is
the image of the ring-theoretic inverse `↑α⁻¹`. -/
theorem coe_alphaInv (α : ℤ_[p]ˣ) :
    (((α : ℤ_[p]) : ℚ_[p]))⁻¹ = ((((α⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) : ℚ_[p]) := by
  have h : (((α : ℤ_[p]) : ℚ_[p])) * ((((α⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) : ℚ_[p]) = 1 := by
    rw [← PadicInt.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, PadicInt.coe_one]
  exact (eq_inv_of_mul_eq_one_left (by rw [mul_comm] at h; exact h)).symm

/-- **Non-anomality in `ℚ_[p]` form**: if `α − 1` is a `ℤ_[p]`-unit then
`1 − α⁻¹` is a p-adic unit. -/
theorem isPUnit_one_sub_alphaInv {α : ℤ_[p]ˣ} (hα : IsUnit ((α : ℤ_[p]) - 1)) :
    IsPUnit ((1 : ℚ_[p]) - (((α : ℤ_[p]) : ℚ_[p]))⁻¹) := by
  have hfac : (1 : ℤ_[p]) - ((α⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
      = ((α⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * ((α : ℤ_[p]) - 1) := by
    have h : ((α⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (α : ℤ_[p]) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [mul_sub, h, mul_one]
  rw [coe_alphaInv, ← PadicInt.coe_one, ← PadicInt.coe_sub, isPUnit_coe_iff, hfac]
  exact (Units.isUnit _).mul hα

/-- The toy normalised second jet is a p-adic unit. -/
theorem isPUnit_toy_c2norm {α : ℤ_[p]ˣ} (hα : IsUnit ((α : ℤ_[p]) - 1)) :
    IsPUnit (c2tilde (1 : ℚ_[p]) (((α : ℤ_[p]) : ℚ_[p]))⁻¹ 1) := by
  have h := isPUnit_one_sub_alphaInv hα
  rw [IsPUnit] at h ⊢
  rw [c2tilde]
  rw [Rat.cast_one, mul_one, one_mul, norm_pow, norm_inv, h, inv_one, one_pow]

/-- **Toy `HeightData`**: trivial regulator and Ш-order, nondegeneracy `True`,
and the normalised jet forced by the `ClassicalInputs` tie-equation. -/
noncomputable def toyHeight (α : ℤ_[p]ˣ) (hα : IsUnit ((α : ℤ_[p]) - 1)) : HeightData p where
  Reg_γ := 1
  heightNondeg := True
  shaOrd := 1
  c2norm := c2tilde (1 : ℚ_[p]) (((α : ℤ_[p]) : ℚ_[p]))⁻¹ 1
  reg_integral := le_of_eq norm_one
  sha_integral := le_of_eq norm_one
  spr_padicBSD := by
    rw [norm_one, mul_one]
    exact isPUnit_toy_c2norm hα
  spr_nondeg := by
    refine ⟨fun _ => ⟨trivial, ?_, ?_⟩, fun _ => isPUnit_toy_c2norm hα⟩ <;>
      exact (norm_one : ‖(1 : ℚ_[p])‖ = 1)

end Toy

end FinShaRank2
