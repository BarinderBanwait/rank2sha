import FinShaRank2.Toy.Heights

/-!
# Anti-vacuity height layer (task T41): `Toy.shaHeight`

The height / p-adic-BSD layer of the anti-vacuity instance `ToySha`. Compared
with the T40 layer (`Toy/Heights.lean`) the Ш-order proxy is the **non-unit**

`shaOrd := p`,

which is exactly what `PrimeData.shaOrd_tie` demands once `ShaDual` is not
subsingleton, and the normalised jet proxy is the one forced by
`PrimeData.c2norm_tie` from `Lp = C p · X²`:

`c2norm := c̃₂ = p · (1 − α⁻¹)⁻² · 1`.

The two `spr_*` fields then balance:

* `spr_padicBSD`: `‖c2norm‖ = ‖p‖ · ‖(1 − α⁻¹)‖⁻² = ‖p‖ = ‖Reg_γ‖ · ‖shaOrd‖`,
  using `‖1 − α⁻¹‖ = 1` (non-anomality of the toy prime, `Toy/Analytic.lean`);
* `spr_nondeg`: **both sides are false** — `‖c2norm‖ = ‖p‖ = 1/p ≠ 1` on the
  left, and `IsPUnit shaOrd` fails on the right — so it holds by
  `iff_of_false`.

`Reg_γ := 1` and `heightNondeg := True` as in T40.
-/

namespace FinShaRank2

namespace Toy

variable {p : ℕ} [Fact p.Prime]

/-- `p` is not a `ℤ_[p]`-unit, hence not a p-adic unit in `ℚ_[p]` either. This
is the arithmetic content of the whole anti-vacuity construction. -/
theorem not_isPUnit_p : ¬ IsPUnit (((p : ℤ_[p]) : ℚ_[p])) := fun h =>
  mem_nonunits_iff.mp PadicInt.p_nonunit (isPUnit_coe_iff.mp h)

/-- The anti-vacuity normalised jet has the same norm as `p`: the interpolation
factor `(1 − α⁻¹)⁻²` is a p-adic unit at the non-anomalous toy prime. -/
theorem norm_sha_c2norm {α : ℤ_[p]ˣ} (hα : IsUnit ((α : ℤ_[p]) - 1)) :
    ‖c2tilde (((p : ℤ_[p]) : ℚ_[p])) (((α : ℤ_[p]) : ℚ_[p]))⁻¹ 1‖
      = ‖(((p : ℤ_[p]) : ℚ_[p]))‖ := by
  have h1 : ‖(1 : ℚ_[p]) - (((α : ℤ_[p]) : ℚ_[p]))⁻¹‖ = 1 := isPUnit_one_sub_alphaInv hα
  rw [c2tilde, Rat.cast_one, mul_one, norm_mul, norm_pow, norm_inv, h1, inv_one, one_pow,
    mul_one]

/-- **Anti-vacuity `HeightData`**: `Reg_γ = 1`, `heightNondeg = True`, and the
non-unit Ш-order proxy `shaOrd = p` with the matching jet `c̃₂ = p·(1−α⁻¹)⁻²`. -/
noncomputable def shaHeight (α : ℤ_[p]ˣ) (hα : IsUnit ((α : ℤ_[p]) - 1)) : HeightData p where
  Reg_γ := 1
  heightNondeg := True
  shaOrd := ((p : ℤ_[p]) : ℚ_[p])
  c2norm := c2tilde (((p : ℤ_[p]) : ℚ_[p])) (((α : ℤ_[p]) : ℚ_[p]))⁻¹ 1
  reg_integral := le_of_eq norm_one
  sha_integral := by
    rw [PadicInt.padic_norm_e_of_padicInt]
    exact PadicInt.norm_le_one _
  spr_padicBSD := by rw [norm_sha_c2norm hα, norm_one, one_mul]
  spr_nondeg := by
    refine iff_of_false (fun h => not_isPUnit_p (p := p) ?_) (fun h => not_isPUnit_p (p := p) h.2.2)
    rw [IsPUnit] at h ⊢
    rw [← norm_sha_c2norm hα]
    exact h

end Toy

end FinShaRank2
