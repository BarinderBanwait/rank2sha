import FinShaRank2.Defs

/-!
# Functional-equation coefficient lemma

Ring-generic kernel lemma behind the vanishing of the linear coefficient
`c₁(p)` of the p-adic L-function (paper Lemma 3.1). Nothing here mentions the
paper's interface; the file is `mathlib`-only and reasons purely about power
series over a commutative ring.

## The substitution series

Over any commutative ring `R` we form the functional-equation substitution
`σ_R = (1 + X)⁻¹ − 1 = Σₙ₌₁^∞ (−1)ⁿ Xⁿ`, defined by exactly the same one-line
`PowerSeries.mk` as `FinShaRank2.σ` (which is fixed at `R = ℤ_[p]`). Over
`ℤ_[p]` the two series are **definitionally equal** (`σ = σR ℤ_[p]` by `rfl`),
so the ℤ_[p]-specialisation at the end phrases everything against the `σ` of
`Defs.lean` that the interface (`AnalyticData.funct_eq`, `AnalyticData`) uses.

## Main results

* `coeff_one_subst_σR` (core sub-lemma): `coeff 1 (f.subst σ_R) = − coeff 1 f`
  for every `f`. Only the degree-`≤ 1` data of `f` and `σ_R` enters; the
  `coeff 0 f = 0` hypothesis is not needed for this half; it is used only on the
  product side.
* `coeff_one_eq_zero_of_functionalEquation` (ring-generic main theorem): if
  `constantCoeff U = 1`, `f.subst σ_R = U * f` and `coeff 0 f = 0`, then
  `coeff 1 f = 0`, provided `R` is 2-torsion-free.
* `coeff_one_Lp_eq_zero` (ℤ_[p] specialisation, consumed verbatim by `c0_eq_zero`/`c1_eq_zero`):
  the same conclusion phrased against `FinShaRank2.σ`, with the 2-torsion-freeness
  discharged internally (`ℤ_[p]` is a characteristic-zero domain).

## 2-torsion-freeness

The ring hypothesis is the explicit, referee-transparent spelling
`∀ x : R, 2 • x = 0 → x = 0`. It is
exactly what the final step needs — the functional equation forces
`− coeff 1 f = coeff 1 f`, i.e. `2 • coeff 1 f = 0` — and is trivially true for
`ℤ_[p]`, so it never surfaces in the specialisation.

## Reuse notes for downstream tasks

`σR`, `constantCoeff_σR`, `coeff_one_σR`, `hasSubst_σR` and the characterising
identity `oneAddX_mul_σR : (1 + X) * σ_R = −X` are all ring-generic and reusable;
in particular `oneAddX_mul_σR` is the `(1 + X)⁻¹` handle that `ToyTrivial`'s toy
functional equation (`subst σ (X²) = X²·(1 + X)⁻²`) will want.
-/

open PowerSeries

namespace FinShaRank2

section Generic

variable {R : Type*} [CommRing R]

/-- The ring-generic functional-equation substitution
`σ_R = (1 + X)⁻¹ − 1 = Σₙ₌₁^∞ (−1)ⁿ Xⁿ`. Identical one-line definition to
`FinShaRank2.σ`, which fixes `R = ℤ_[p]`; over `ℤ_[p]` the two coincide by
`rfl`. -/
noncomputable def σR (R : Type*) [CommRing R] : PowerSeries R :=
  PowerSeries.mk fun n => if n = 0 then 0 else (-1) ^ n

/-- The constant term of `σ_R` vanishes (it represents `(1 + X)⁻¹ − 1`, which is
`0` at `X = 0`). This is the side condition that makes `σ_R` substitutable. -/
theorem constantCoeff_σR : constantCoeff (σR R) = 0 := by
  simp [σR, constantCoeff_mk]

/-- The linear coefficient of `σ_R` is `−1`. -/
theorem coeff_one_σR : coeff 1 (σR R) = -1 := by
  simp [σR, coeff_mk]

/-- `σ_R` is a legal power-series substitution, since its constant term
vanishes. -/
theorem hasSubst_σR : HasSubst (σR R) :=
  HasSubst.of_constantCoeff_zero' (by simp [σR, constantCoeff_mk])

/-- Characterising identity `(1 + X) · σ_R = −X`, i.e. `σ_R = (1 + X)⁻¹ − 1`
exactly. Ring-generic analogue of `FinShaRank2.oneAddX_mul_σ`; a self-contained
algebraic handle on `σ_R` (reusable for `ToyTrivial`'s `(1 + X)⁻¹` reasoning). -/
theorem oneAddX_mul_σR : (1 + X) * (σR R) = -X := by
  rw [add_mul, one_mul]
  ext n
  rw [map_add, map_neg, coeff_X]
  obtain _ | _ | m := n
  · simp [σR]
  · simp [σR, coeff_succ_X_mul]
  · rw [show m + 2 = (m + 1) + 1 from rfl, coeff_succ_X_mul]
    simp only [σR, coeff_mk, Nat.succ_ne_zero, if_false, if_neg (show m + 2 ≠ 1 by omega)]
    rw [pow_succ]; ring

/-- For every exponent `d ≠ 1`, the linear coefficient of `σ_R ^ d` vanishes:
at `d = 0` because `σ_R ^ 0 = 1`, and at `d ≥ 2` because `X² ∣ σ_R ^ d`
(`σ_R` is divisible by `X`). This is the only fact about `σ_R` beyond
`coeff 1 σ_R = −1` that the core sub-lemma needs. -/
theorem coeff_one_σR_pow_of_ne {d : ℕ} (hd : d ≠ 1) : coeff 1 ((σR R) ^ d) = 0 := by
  rcases d with _ | _ | k
  · simp [coeff_one]
  · exact absurd rfl hd
  · have hdvd : (X : R⟦X⟧) ^ (k + 1 + 1) ∣ (σR R) ^ (k + 1 + 1) :=
      pow_dvd_pow_of_dvd (X_dvd_iff.mpr constantCoeff_σR) _
    exact (X_pow_dvd_iff.mp hdvd) 1 (by omega)

/-- **Core sub-lemma.** The linear coefficient of `f.subst σ_R` is `− coeff 1 f`.

Via `PowerSeries.coeff_subst'`, `coeff 1 (f.subst σ_R) = ∑ᶠ d, coeff d f • coeff 1 (σ_R ^ d)`;
every term with `d ≠ 1` dies by `coeff_one_σR_pow_of_ne`, leaving
`coeff 1 f • coeff 1 σ_R = coeff 1 f • (−1) = − coeff 1 f`. -/
theorem coeff_one_subst_σR (f : PowerSeries R) :
    coeff 1 (f.subst (σR R)) = - coeff 1 f := by
  rw [coeff_subst' hasSubst_σR f 1,
    finsum_eq_single _ 1 fun d hd => by rw [coeff_one_σR_pow_of_ne hd, smul_zero]]
  simp only [pow_one, coeff_one_σR, smul_eq_mul, mul_neg_one]

/-- **Ring-generic functional-equation coefficient lemma** (paper Lemma 3.1).

If `R` is 2-torsion-free, `U` has constant term `1`, the functional equation
`f.subst σ_R = U * f` holds, and `coeff 0 f = 0`, then `coeff 1 f = 0`.

Proof: comparing linear coefficients, the substitution side gives
`coeff 1 (f.subst σ_R) = − coeff 1 f` (`coeff_one_subst_σR`), while on the
product side `coeff 0 f = 0` and `constantCoeff U = 1` give
`coeff 1 (U * f) = coeff 1 f` (the cross term `coeff 1 U * coeff 0 f` drops, and
`(U − 1) * f` is divisible by `X²`). Hence `− coeff 1 f = coeff 1 f`, i.e.
`2 • coeff 1 f = 0`, and 2-torsion-freeness finishes. -/
theorem coeff_one_eq_zero_of_functionalEquation
    (h2 : ∀ x : R, 2 • x = 0 → x = 0)
    (f U : PowerSeries R) (hU : constantCoeff U = 1)
    (hFE : f.subst (σR R) = U * f) (hf0 : coeff 0 f = 0) :
    coeff 1 f = 0 := by
  have hfc : constantCoeff f = 0 := by rw [← coeff_zero_eq_constantCoeff_apply]; exact hf0
  -- substitution side
  have hL : coeff 1 (f.subst (σR R)) = - coeff 1 f := coeff_one_subst_σR f
  -- product side: coeff 1 (U * f) = coeff 1 f
  have hR : coeff 1 (U * f) = coeff 1 f := by
    have hU0 : constantCoeff (U - 1) = 0 := by rw [map_sub, hU, map_one, sub_self]
    have hX2 : (X : R⟦X⟧) ^ 2 ∣ (U - 1) * f := by
      rw [pow_two]; exact mul_dvd_mul (X_dvd_iff.mpr hU0) (X_dvd_iff.mpr hfc)
    have hz : coeff 1 ((U - 1) * f) = 0 := (X_pow_dvd_iff.mp hX2) 1 (by norm_num)
    have hsplit : U * f = f + (U - 1) * f := by ring
    rw [hsplit, map_add, hz, add_zero]
  -- combine: − coeff 1 f = coeff 1 f
  have key : - coeff 1 f = coeff 1 f := by rw [← hL, hFE, hR]
  -- 2-torsion-freeness kills it
  apply h2
  rw [two_nsmul]
  linear_combination -key

end Generic

/-- **ℤ_[p]-specialisation of the functional-equation lemma**, phrased against the
`σ` of `Defs.lean` (paper Lemma 3.1, the `c₁(p) = 0` half). This is the exact
statement `c0_eq_zero`/`c1_eq_zero` consumes: from the `AnalyticData.funct_eq` data
`constantCoeff U = 1` and `Lp.subst σ = U * Lp`, together with `constantCoeff Lp = 0`
(the `c₀(p) = 0` output of the interpolation half), it concludes `coeff 1 Lp = 0`.

The `IsUnit U` component of `funct_eq` is not needed and is intentionally absent.
2-torsion-freeness is discharged here: `ℤ_[p]` is a characteristic-zero domain. -/
theorem coeff_one_Lp_eq_zero {p : ℕ} [Fact p.Prime]
    (Lp U : Λ p) (hU : constantCoeff U = 1)
    (hFE : Lp.subst σ = U * Lp) (hLp0 : constantCoeff Lp = 0) :
    coeff 1 Lp = 0 := by
  have hσ : (σ : Λ p) = σR ℤ_[p] := rfl
  refine coeff_one_eq_zero_of_functionalEquation ?_ Lp U hU ?_ ?_
  · intro x hx
    have hxx : x + x = 0 := by rw [← two_nsmul]; exact hx
    have h2x : (2 : ℤ_[p]) * x = 0 := by rw [two_mul]; exact hxx
    rcases mul_eq_zero.mp h2x with h | h
    · norm_num at h
    · exact h
  · rw [← hσ]; exact hFE
  · rw [coeff_zero_eq_constantCoeff_apply]; exact hLp0

end FinShaRank2
