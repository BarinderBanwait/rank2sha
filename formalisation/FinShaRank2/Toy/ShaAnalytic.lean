import FinShaRank2.Toy.Analytic

/-!
# Anti-vacuity analytic layer (task T41): `Toy.shaAnalytic`

The **anti-vacuity** instance `ToySha` (`Toy/ShaTrivial.lean`) is the tripwire
complementary to the non-vacuity instance `ToyTrivial` of task T40: it witnesses
that `ClassicalInputs` alone does **not** entail the headline conclusion
`Subsingleton ShaDual`. This file supplies its **analytic** layer.

## The anti-vacuity world

It reuses the whole toy arithmetic of `Toy/Analytic.lean` (`Toy.Setup`: the
two-square decomposition `a² + b² = p`, `a_p = 2a`, the Hensel unit root `α`,
non-anomality) and changes exactly one datum:

`Lp := C p · X²`  instead of  `Lp := X²`.

The point is `coeff 2 Lp = p`, a **non-unit**. That is forced: `PrimeData`'s
tie-equations make `‖c2norm‖ = ‖coeff 2 Lp‖ · ‖1 − α⁻¹‖⁻² · ‖Reg_γ‖` and
`spr_padicBSD` makes `‖c2norm‖ = ‖Reg_γ‖ · ‖shaOrd‖`, while `shaOrd_tie`
forces `shaOrd` to be a non-unit as soon as `ShaDual` is not subsingleton. Since
the toy prime is non-anomalous (`‖1 − α⁻¹‖ = 1`), `coeff 2 Lp` must be a
non-unit, so `Lp = X²` is impossible here.

Every other analytic field is unchanged in substance: `constantCoeff Lp = 0`
still gives `interp` (with `modularSymbol0 = 0`), and the functional equation
is the T40 one multiplied by the constant `C p`.
-/

open PowerSeries

namespace FinShaRank2

namespace Toy

variable {p : ℕ} [Fact p.Prime]

/-! ### The anti-vacuity p-adic L-function `C p · X²` -/

/-- The anti-vacuity toy L-function `Lp = C p · X²`. Its second coefficient is
`p`, a non-unit — the whole point of task T41. -/
noncomputable def shaLp (p : ℕ) [Fact p.Prime] : Λ p := C (p : ℤ_[p]) * X ^ 2

/-- `coeff 2 (C p · X²) = p`. -/
theorem coeff_two_shaLp : coeff 2 (shaLp p) = (p : ℤ_[p]) := by
  rw [shaLp, coeff_C_mul, coeff_X_pow]; simp

/-- `C p · X²` has vanishing constant term. -/
theorem constantCoeff_shaLp : constantCoeff (shaLp p) = 0 := by simp [shaLp]

/-- **The toy functional equation for `C p · X²`**: the T40 witness `U` for `X²`
works verbatim, since `subst σ` fixes the constant `C p`. -/
theorem functionalEquation_shaLp :
    ∃ U : Λ p, IsUnit U ∧ constantCoeff U = 1 ∧ (shaLp p).subst σ = U * shaLp p := by
  obtain ⟨U, hU, hU0, hfe⟩ := functionalEquation_X_sq (p := p)
  refine ⟨U, hU, hU0, ?_⟩
  have key : (shaLp p).subst σ = C (p : ℤ_[p]) * (((X : Λ p) ^ 2).subst σ) := by
    rw [shaLp, subst_mul hasSubst_σ, subst_C]
    rfl
  rw [key, hfe, shaLp]
  ring

/-! ### The analytic layer -/

/-- **Anti-vacuity `AnalyticData`** at a split prime: identical to
`Toy.toyAnalytic` except that `Lp = C p · X²`. -/
noncomputable def shaAnalytic (hsplit : p % 4 = 1) (s : Setup p) : AnalyticData p hsplit where
  Lp := shaLp p
  ap := 2 * (s.a : ℤ)
  α := s.α
  alpha_root := s.alpha_root
  modularSymbol0 := 0
  interp := by rw [constantCoeff_shaLp]; simp
  msymb_zero := rfl
  funct_eq := functionalEquation_shaLp
  ap_from_CM := s.gaussian
  hasse := by
    have := s.ha_sq
    nlinarith

end Toy

end FinShaRank2
