import Mathlib
import FinShaRank2.Defs

/-!
# `T²`-unit factorisation kernel (task T21)

This file proves, as pure `mathlib`-only algebra over the Iwasawa algebra
`Λ = ℤ_[p]⟦X⟧`, the elementary factorisation that drives Step 1 of the paper's
`prop:consequence`: a power series whose first two coefficients vanish and whose
second coefficient is a `ℤ_[p]`-unit is `X²` times a unit.

## Main result

`FinShaRank2.tsq_factor` :
`coeff 0 f = 0 → coeff 1 f = 0 → IsUnit (coeff 2 f) → ∃ u : (Λ p)ˣ, f = X ^ 2 * ↑u`.

The route is the one sketched on the board:

* the two vanishing coefficients give `X² ∣ f` via `PowerSeries.X_pow_dvd_iff`;
* writing `f = X² * g`, the identity `coeff 2 f = constantCoeff g`
  (`PowerSeries.coeff_X_pow_mul`) turns the unit hypothesis on `coeff 2 f` into a
  unit constant coefficient of `g`;
* over the (commutative) ring `ℤ_[p]`, `PowerSeries.isUnit_iff_constantCoeff`
  upgrades that to `IsUnit g`, so `g` is a genuine unit `u`.

## Corollaries (all four, in two forms)

Each of the four downstream facts is stated **twice**: once from the factored
form `f = X² * ↑u` (`…_of_factored`) and once from the three coefficient
hypotheses (`…_of_coeffs`). Downstream callers differ: T23/T31 consume the
`Associated` corollary, and `prop_consequence` consumes `MuZero`/`lambdaAn`.

* order:      `order_eq_two_of_factored`,     `order_eq_two_of_coeffs`
* μ = 0:      `muZero_of_factored`,           `muZero_of_coeffs`
* λ = 2:      `lambdaAn_eq_two_of_factored`,  `lambdaAn_eq_two_of_coeffs`
* associate:  `associated_X_sq_of_factored`,  `associated_X_sq_of_coeffs`

The `_of_coeffs` forms are proved uniformly by routing through `tsq_factor` and
the corresponding `_of_factored` form, so all three coefficient hypotheses are
genuinely used.

A small convenience `coeffs_X_sq` records the three coefficient facts for the
concrete series `X²` itself (for the toy instantiation `Lp := X²`, task T40).

## API notes for T31 / T40

* `PowerSeries.order` lands in `ℕ∞`; `order_eq_two_of_*` states
  `PowerSeries.order f = 2` with `(2 : ℕ∞)` (the `order_eq_nat`/`Nat.cast` gap is
  bridged internally with `simpa`).
* `lambdaAn f = 2` is a `Nat.sInf` computation: `2` is in the coefficient-unit
  set while `0, 1` are excluded (their coefficients are `0`, and `0` is not a
  unit in the nontrivial ring `ℤ_[p]`).
* `PowerSeries.coeff` carries its coefficient ring implicitly on this pin; here
  `coeff n f : ℤ_[p]`.
-/

open PowerSeries

namespace FinShaRank2

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-! ### Coefficient extraction from the factored form -/

/-- From a factorisation `f = X² * ↑u` with `u` a unit, read off the three
coefficient facts: the constant and linear coefficients vanish, and the quadratic
coefficient (equal to `constantCoeff ↑u`) is a `ℤ_[p]`-unit. This is the shared
engine of every `_of_factored` corollary below. -/
private lemma coeffs_of_factored {f : Λ p} (u : (Λ p)ˣ) (hf : f = (X : Λ p) ^ 2 * ↑u) :
    coeff 0 f = 0 ∧ coeff 1 f = 0 ∧ IsUnit (coeff 2 f) := by
  have hdvd : (X : Λ p) ^ 2 ∣ f := by rw [hf]; exact dvd_mul_right _ _
  have hvanish := (PowerSeries.X_pow_dvd_iff).mp hdvd
  refine ⟨hvanish 0 (by norm_num), hvanish 1 (by norm_num), ?_⟩
  have hcoeff : coeff 2 f = constantCoeff (↑u : Λ p) := by
    rw [hf, ← coeff_zero_eq_constantCoeff_apply]
    have h := coeff_X_pow_mul (↑u : Λ p) 2 0
    rwa [zero_add] at h
  rw [hcoeff]
  exact isUnit_iff_constantCoeff.mp u.isUnit

/-! ### Main theorem -/

/-- **T21 (main).** If the constant and linear coefficients of `f : Λ p` vanish
and the quadratic coefficient is a `ℤ_[p]`-unit, then `f = X² · u` for a genuine
unit `u` of `Λ = ℤ_[p]⟦X⟧`.

Paper: `prop:consequence`, Step 1 (the `X²`-unit factorisation of `L_p`). -/
theorem tsq_factor {f : Λ p} (h0 : coeff 0 f = 0) (h1 : coeff 1 f = 0)
    (h2 : IsUnit (coeff 2 f)) : ∃ u : (Λ p)ˣ, f = (X : Λ p) ^ 2 * ↑u := by
  have hdvd : (X : Λ p) ^ 2 ∣ f := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · exact h0
    · exact h1
  obtain ⟨g, hg⟩ := hdvd
  have hcoeff : coeff 2 f = constantCoeff g := by
    rw [hg, ← coeff_zero_eq_constantCoeff_apply]
    have h := coeff_X_pow_mul g 2 0
    rwa [zero_add] at h
  have hgunit : IsUnit g := isUnit_iff_constantCoeff.mpr (hcoeff ▸ h2)
  obtain ⟨u, hu⟩ := hgunit
  exact ⟨u, by rw [hg, ← hu]⟩

/-! ### Corollaries from the factored form `f = X² * ↑u` -/

/-- Order corollary (factored form): `order f = 2`. -/
theorem order_eq_two_of_factored {f : Λ p} (u : (Λ p)ˣ) (hf : f = (X : Λ p) ^ 2 * ↑u) :
    PowerSeries.order f = 2 := by
  obtain ⟨hc0, hc1, hc2⟩ := coeffs_of_factored u hf
  have h : PowerSeries.order f = ((2 : ℕ) : ℕ∞) :=
    PowerSeries.order_eq_nat.mpr ⟨hc2.ne_zero, fun i hi => by interval_cases i <;> assumption⟩
  simpa using h

/-- μ = 0 corollary (factored form): some coefficient of `f` is a unit. -/
theorem muZero_of_factored {f : Λ p} (u : (Λ p)ˣ) (hf : f = (X : Λ p) ^ 2 * ↑u) :
    MuZero f := by
  obtain ⟨_, _, hc2⟩ := coeffs_of_factored u hf
  exact ⟨2, hc2⟩

/-- λ = 2 corollary (factored form): the least coefficient-unit index is `2`. -/
theorem lambdaAn_eq_two_of_factored {f : Λ p} (u : (Λ p)ˣ) (hf : f = (X : Λ p) ^ 2 * ↑u) :
    lambdaAn f = 2 := by
  obtain ⟨hc0, hc1, hc2⟩ := coeffs_of_factored u hf
  have hmem2 : 2 ∈ {n | IsUnit (coeff n f)} := hc2
  have key : ∀ m ∈ {n | IsUnit (coeff n f)}, 2 ≤ m := by
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · interval_cases m
      · rw [hc0] at hm; exact absurd hm not_isUnit_zero
      · rw [hc1] at hm; exact absurd hm not_isUnit_zero
    · exact hge
  exact le_antisymm (Nat.sInf_le hmem2) (key _ (Nat.sInf_mem ⟨2, hmem2⟩))

/-- Associate corollary (factored form): `f` is associate to `X²`. Feeds T23/T31
(their `Associated (∏ fᵢ) (X²)` / `Associated Lp (X²)` inputs). -/
theorem associated_X_sq_of_factored {f : Λ p} (u : (Λ p)ˣ) (hf : f = (X : Λ p) ^ 2 * ↑u) :
    Associated f (X ^ 2 : Λ p) :=
  ⟨u⁻¹, by rw [hf, mul_assoc, Units.mul_inv, mul_one]⟩

/-! ### Corollaries from the three coefficient hypotheses -/

/-- Order corollary (coefficient form): `order f = 2`. -/
theorem order_eq_two_of_coeffs {f : Λ p} (h0 : coeff 0 f = 0) (h1 : coeff 1 f = 0)
    (h2 : IsUnit (coeff 2 f)) : PowerSeries.order f = 2 := by
  obtain ⟨u, hf⟩ := tsq_factor h0 h1 h2
  exact order_eq_two_of_factored u hf

/-- μ = 0 corollary (coefficient form). -/
theorem muZero_of_coeffs {f : Λ p} (h0 : coeff 0 f = 0) (h1 : coeff 1 f = 0)
    (h2 : IsUnit (coeff 2 f)) : MuZero f := by
  obtain ⟨u, hf⟩ := tsq_factor h0 h1 h2
  exact muZero_of_factored u hf

/-- λ = 2 corollary (coefficient form). -/
theorem lambdaAn_eq_two_of_coeffs {f : Λ p} (h0 : coeff 0 f = 0) (h1 : coeff 1 f = 0)
    (h2 : IsUnit (coeff 2 f)) : lambdaAn f = 2 := by
  obtain ⟨u, hf⟩ := tsq_factor h0 h1 h2
  exact lambdaAn_eq_two_of_factored u hf

/-- Associate corollary (coefficient form): `f` is associate to `X²`. -/
theorem associated_X_sq_of_coeffs {f : Λ p} (h0 : coeff 0 f = 0) (h1 : coeff 1 f = 0)
    (h2 : IsUnit (coeff 2 f)) : Associated f (X ^ 2 : Λ p) := by
  obtain ⟨u, hf⟩ := tsq_factor h0 h1 h2
  exact associated_X_sq_of_factored u hf

/-! ### Convenience for the toy instantiation `Lp := X²` (task T40) -/

/-- The three coefficient facts for the concrete series `X²` itself: the constant
and linear coefficients vanish and the quadratic coefficient is a unit. Lets the
toy instance `Lp := X²` (task T40) discharge the hypotheses of the corollaries
above directly. -/
theorem coeffs_X_sq :
    coeff 0 (X ^ 2 : Λ p) = 0 ∧ coeff 1 (X ^ 2 : Λ p) = 0 ∧
      IsUnit (coeff 2 (X ^ 2 : Λ p)) :=
  coeffs_of_factored 1 (by rw [Units.val_one, mul_one])

end

end FinShaRank2
