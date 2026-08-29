import FinShaRank2.Interface.Analytic

/-!
# Toy analytic layer (task T40): `Toy.toyAnalytic`

Non-vacuity of the assumption surface (`TASK_BOARD.md` §1) is proved by
*constructing* an instance of `ClassicalInputs` in a toy world where every field
is genuinely provable. This file supplies the **analytic** layer.

## The toy world

At every split prime `p ≡ 1 (mod 4)` the toy takes

* `Lp := X²` — so `c₀ = c₁ = 0` and `c₂ = 1` (a unit), matching `coeffs_X_sq`;
* `modularSymbol0 := 0`, making the MTT interpolation equation `0 = (…)² · 0`;
* `a_p := 2a`, where `a² + b² = p` is the two-square decomposition of the split
  prime (`Nat.Prime.sq_add_sq`).

The choice `a_p := 2a` (rather than the board's original sketch `a_p := 2`) is
forced by the frozen `ap_from_CM` field, which demands a Gaussian integer `π` of
norm `p` with `a_p = 2 Re π`: at a general split `p` the value `a_p = 2` would
require `p = 1 + b²`. With `π = a + bi` both `ap_from_CM` and the Hasse bound
`(2a)² = 4a² ≤ 4p` hold, and `0 < 2a < p` makes the toy prime non-anomalous,
which the height layer needs (`Toy/Heights.lean`).

## Contents

* `Toy.Setup` — the bundled toy arithmetic at `p` (the integer `a`, the unit root
  `α`, and the four facts the interface layers consume).
* `Toy.nonempty_setup` / `Toy.setup` — construction of a `Setup`, via
  `Nat.Prime.sq_add_sq` and Hensel's lemma (`hensels_lemma`) applied to
  `F = X² − 2aX + p` at the approximate root `2a`.
* `Toy.subst_σ_X_sq`, `Toy.functionalEquation_X_sq` — the toy functional
  equation `subst σ (X²) = ((1+X)⁻¹)² · X²` (reusable test coverage for T20).
* `Toy.toyAnalytic` — `AnalyticData p hsplit`.
-/

open PowerSeries

namespace FinShaRank2

namespace Toy

variable {p : ℕ} [Fact p.Prime]

/-! ### p-adic norm helper -/

/-- Ultrametric rigidity: an element `1`-close to a norm-one element has norm
one. Used twice — to see that the Hensel root `α` is a unit, and that `α − 1` is
a unit (non-anomality of the toy prime). -/
theorem norm_eq_one_of_sub_lt {x y : ℤ_[p]} (hy : ‖y‖ = 1) (h : ‖x - y‖ < 1) : ‖x‖ = 1 := by
  refine le_antisymm (PadicInt.norm_le_one x) ?_
  by_contra hlt
  rw [not_le] at hlt
  have hyx : ‖y - x‖ < 1 := by
    rw [show y - x = -(x - y) by ring, norm_neg]; exact h
  have hmax := PadicInt.nonarchimedean (y - x) x
  rw [show y - x + x = y by ring, hy] at hmax
  exact absurd hmax (not_le.mpr (max_lt hyx hlt))

/-! ### The toy functional equation -/

/-- `1 + X` is a unit of `Λ = ℤ_[p]⟦X⟧` (its constant coefficient is `1`). -/
noncomputable def oneAddXUnit (p : ℕ) [Fact p.Prime] : (Λ p)ˣ :=
  (show IsUnit (1 + X : Λ p) from
    isUnit_iff_constantCoeff.mpr
      (by rw [map_add, map_one, constantCoeff_X, add_zero]; exact isUnit_one)).unit

@[simp] theorem oneAddXUnit_val : ((oneAddXUnit p : (Λ p)ˣ) : Λ p) = 1 + X := by
  unfold oneAddXUnit
  exact IsUnit.unit_spec _

/-- `constantCoeff` of the inverse of `1 + X` is `1`. -/
theorem constantCoeff_oneAddXUnit_inv :
    constantCoeff (((oneAddXUnit p)⁻¹ : (Λ p)ˣ) : Λ p) = 1 := by
  have h : ((oneAddXUnit p : (Λ p)ˣ) : Λ p) * (((oneAddXUnit p)⁻¹ : (Λ p)ˣ) : Λ p) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have := congrArg (constantCoeff (R := ℤ_[p])) h
  rw [map_mul, map_one, oneAddXUnit_val] at this
  simpa using this

/-- **The functional-equation substitution applied to `X²`**: `σ` is
`(1+X)⁻¹ − 1`, so `subst σ X² = σ² = ((1+X)⁻¹)² · X²`.

This is the identity the toy `funct_eq` needs; it is stated separately because it
is reusable test coverage for the T20 kernel (`oneAddX_mul_σ` plus mathlib's
`subst_pow` / `subst_X`). -/
theorem subst_σ_X_sq :
    ((X : Λ p) ^ 2).subst σ = ((((oneAddXUnit p)⁻¹ : (Λ p)ˣ) : Λ p)) ^ 2 * (X : Λ p) ^ 2 := by
  have hσ : (σ : Λ p) = (((oneAddXUnit p)⁻¹ : (Λ p)ˣ) : Λ p) * (-X) := by
    have h := oneAddX_mul_σ (p := p)
    rw [← oneAddXUnit_val (p := p)] at h
    calc (σ : Λ p)
        = (((oneAddXUnit p)⁻¹ : (Λ p)ˣ) : Λ p) *
            (((oneAddXUnit p : (Λ p)ˣ) : Λ p) * σ) := by
          rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      _ = (((oneAddXUnit p)⁻¹ : (Λ p)ˣ) : Λ p) * (-X) := by rw [h]
  rw [subst_pow hasSubst_σ, subst_X hasSubst_σ, hσ]
  ring

/-- The toy `funct_eq` witness: `subst σ (X²) = U · X²` with `U = ((1+X)⁻¹)²` a
unit of constant term `1`. -/
theorem functionalEquation_X_sq :
    ∃ U : Λ p, IsUnit U ∧ constantCoeff U = 1 ∧ ((X : Λ p) ^ 2).subst σ = U * X ^ 2 := by
  refine ⟨((((oneAddXUnit p)⁻¹ : (Λ p)ˣ) : Λ p)) ^ 2, ?_, ?_, subst_σ_X_sq⟩
  · exact (Units.isUnit _).pow 2
  · rw [map_pow, constantCoeff_oneAddXUnit_inv, one_pow]

/-! ### The toy arithmetic setup at a split prime -/

/-- **Bundled toy arithmetic at a split prime `p`.**

`a` is the first component of a two-square decomposition `a² + b² = p`, so that
`a_p := 2a` satisfies the CM shape `a_p = 2 Re π` with `π = a + bi` of norm `p`,
and `α` is the Hensel unit root of `X² − 2aX + p`. The last field records
non-anomality (`α ≢ 1 mod p`), which the toy height layer consumes. -/
structure Setup (p : ℕ) [Fact p.Prime] where
  /-- The real part of a Gaussian generator of a prime above `p`. -/
  a : ℕ
  /-- `a ≥ 1` (else `p = b²` would not be prime). -/
  ha_pos : 1 ≤ a
  /-- `2a < p`, from `a² < p` and `p ≥ 5`. Gives non-anomality. -/
  ha_lt : 2 * a < p
  /-- `a² ≤ p`; the Hasse bound `(2a)² ≤ 4p` in disguise. -/
  ha_sq : (a : ℤ) ^ 2 ≤ (p : ℤ)
  /-- The Gaussian-integer witness of the CM shape of `a_p = 2a`. -/
  gaussian : ∃ π : GaussianInt, π.norm = (p : ℤ) ∧ (2 * (a : ℤ)) = 2 * π.re
  /-- The unit root of the toy Frobenius polynomial. -/
  α : ℤ_[p]ˣ
  /-- `α² − 2a·α + p = 0`. -/
  alpha_root : ((α : ℤ_[p])) ^ 2 - ((2 * (a : ℤ) : ℤ) : ℤ_[p]) * (α : ℤ_[p]) + (p : ℤ_[p]) = 0
  /-- Non-anomality: `α − 1` is a `ℤ_[p]`-unit (as `α ≡ 2a` and `0 < 2a − 1 < p`). -/
  alpha_sub_one_unit : IsUnit ((α : ℤ_[p]) - 1)

/-- **The toy setup exists at every split prime.** Two-square decomposition
(`Nat.Prime.sq_add_sq`) plus Hensel's lemma at the approximate root `2a`. -/
theorem nonempty_setup (hsplit : p % 4 = 1) : Nonempty (Setup p) := by
  have hp : p.Prime := Fact.out
  have hp5 : 5 ≤ p := by have := hp.two_le; omega
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  -- `a ≥ 1` and `b ≥ 1`: otherwise `p` is a perfect square.
  have hsq : ∀ c d : ℕ, c ^ 2 + d ^ 2 = p → c = 0 → False := by
    intro c d hcd hc
    subst hc
    have hdvd : d ∣ p := ⟨d, by rw [← hcd]; ring⟩
    rcases (hp.eq_one_or_self_of_dvd d hdvd) with h1 | h1 <;> subst h1 <;> nlinarith
  have ha_pos : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr fun h => hsq a b hab h
  have hb_pos : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr fun h => hsq b a (by omega) h
  have ha_sqlt : a ^ 2 < p := by nlinarith
  have ha_lt : 2 * a < p := by nlinarith
  -- The Hensel input: the approximate root `A = 2a`, a `ℤ_[p]`-unit.
  set A : ℤ_[p] := ((2 * a : ℕ) : ℤ_[p]) with hA
  have hAcast : ((2 * (a : ℤ) : ℤ) : ℤ_[p]) = A := by rw [hA]; push_cast; ring
  have hAnorm : ‖A‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one A) ?_
    by_contra hlt
    rw [not_le] at hlt
    rw [← hAcast] at hlt
    have hdvd := (PadicInt.norm_int_lt_one_iff_dvd (2 * (a : ℤ))).mp hlt
    have hle := Int.le_of_dvd (by omega) hdvd
    omega
  set F : Polynomial ℤ_[p] :=
    Polynomial.X ^ 2 - Polynomial.C A * Polynomial.X + Polynomial.C (p : ℤ_[p]) with hF
  have hev : Polynomial.aeval A F = (p : ℤ_[p]) := by simp [hF]; ring
  have hdev : Polynomial.aeval A (Polynomial.derivative F) = A := by simp [hF]; ring
  have hhyp : ‖Polynomial.aeval A F‖ <
      ‖Polynomial.aeval A (Polynomial.derivative F)‖ ^ 2 := by
    rw [hev, hdev, hAnorm, one_pow]
    exact (PadicInt.norm_lt_one_iff_dvd _).mpr dvd_rfl
  obtain ⟨z, hz0, hz1, -⟩ := hensels_lemma hhyp
  rw [hdev, hAnorm] at hz1
  have hznorm : ‖z‖ = 1 := norm_eq_one_of_sub_lt hAnorm hz1
  -- `α − 1` is a unit: `α ≡ 2a (mod p)` and `0 < 2a − 1 < p`.
  have hA1cast : ((2 * (a : ℤ) - 1 : ℤ) : ℤ_[p]) = A - 1 := by rw [hA]; push_cast; ring
  have hA1norm : ‖A - 1‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) ?_
    by_contra hlt
    rw [not_le] at hlt
    rw [← hA1cast] at hlt
    have hdvd := (PadicInt.norm_int_lt_one_iff_dvd (2 * (a : ℤ) - 1)).mp hlt
    have hle := Int.le_of_dvd (by omega) hdvd
    omega
  have hz1norm : ‖z - 1‖ = 1 := by
    refine norm_eq_one_of_sub_lt hA1norm ?_
    rw [show z - 1 - (A - 1) = z - A by ring]
    exact hz1
  refine ⟨{
    a := a
    ha_pos := ha_pos
    ha_lt := ha_lt
    ha_sq := by exact_mod_cast le_of_lt ha_sqlt
    gaussian := ⟨⟨(a : ℤ), (b : ℤ)⟩, ?_, rfl⟩
    α := (PadicInt.isUnit_iff.mpr hznorm).unit
    alpha_root := ?_
    alpha_sub_one_unit := ?_ }⟩
  · rw [Zsqrtd.norm_def]
    push_cast [← hab]
    ring
  · rw [IsUnit.unit_spec, hAcast]
    simp only [hF] at hz0
    simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at hz0
    simpa using hz0
  · rw [IsUnit.unit_spec]
    exact PadicInt.isUnit_iff.mpr hz1norm

/-- The chosen toy setup at a split prime (`Classical.choice` on
`nonempty_setup`). -/
noncomputable def setup (p : ℕ) [Fact p.Prime] (hsplit : p % 4 = 1) : Setup p :=
  (nonempty_setup hsplit).some

/-- **The toy prime is not anomalous**: `a_p = 2a ≢ 1 (mod p)`.

`Setup` carries `1 ≤ a` and `2a < p`, so `2a − 1` lies strictly between `0` and
`p` and cannot be divisible by `p`. This is the form `ClassicalInputs.notAnomalous`
asks for — the `S_an` clause of `eq:Sexc` — and it is discharged from the toy data
itself, with no change to the toy `a_p`.

Used by both toy worlds: `ToyTrivial` and `ToySha` take the same `a_p = 2a`. -/
theorem Setup.ap_ne_one (s : Setup p) : ¬ (((2 * (s.a : ℤ) : ℤ) : ZMod p) = 1) := by
  intro hcong
  have hpos : (1 : ℤ) ≤ (s.a : ℤ) := by exact_mod_cast s.ha_pos
  have hlt : 2 * (s.a : ℤ) < (p : ℤ) := by exact_mod_cast s.ha_lt
  have hdvd : (p : ℤ) ∣ (2 * (s.a : ℤ) - 1) := by
    have h0 : ((2 * (s.a : ℤ) - 1 : ℤ) : ZMod p) = 0 := by
      push_cast
      push_cast at hcong
      rw [hcong]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0
  have hle : (p : ℤ) ≤ 2 * (s.a : ℤ) - 1 := Int.le_of_dvd (by omega) hdvd
  omega

/-! ### The analytic layer -/

/-- **Toy `AnalyticData`** at a split prime: `Lp = X²`, `a_p = 2a`, `α` the
Hensel unit root, and a vanishing modular symbol. Every field is proved. -/
noncomputable def toyAnalytic (hsplit : p % 4 = 1) (s : Setup p) : AnalyticData p hsplit where
  Lp := (X : Λ p) ^ 2
  ap := 2 * (s.a : ℤ)
  α := s.α
  alpha_root := s.alpha_root
  modularSymbol0 := 0
  interp := by simp
  msymb_zero := rfl
  funct_eq := functionalEquation_X_sq
  ap_from_CM := s.gaussian
  hasse := by
    have := s.ha_sq
    nlinarith
end Toy

end FinShaRank2
