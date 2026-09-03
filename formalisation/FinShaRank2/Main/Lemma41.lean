import Mathlib
import FinShaRank2.Defs
import FinShaRank2.Interface.Analytic
import FinShaRank2.Kernel.FunctionalEquation

/-!
# Lemma 4.1 — vanishing of the first two Taylor coefficients

The paper's statement, which `c0_eq_zero` and `c1_eq_zero` below render:

> **Lemma 4.1.** *Assume `L(E,1) = 0` and `w(E) = +1`. Then for every good
> ordinary `p`, `c₀(p) = c₁(p) = 0`.*

Both hypotheses of the paper's lemma are already discharged inside `AnalyticData`:

* `L(E,1) = 0` is the certificate field `msymb_zero : modularSymbol0 = 0`, which
  combines with the data-equation `interp` (MTT interpolation at the trivial
  character) to give `c₀(p) = 0` — this is the data-equation convention in
  action: the vanishing is *derived*, not assumed;
* `w(E) = +1` is folded into the field `funct_eq`, the MTT `p`-adic functional
  equation with the root number already substituted.

## Translation conventions

* `c₀(p)` ↦ `PowerSeries.constantCoeff L_p`, `c₁(p)` ↦ `PowerSeries.coeff 1 L_p`,
  both valued in `ℤ_[p]` (the coefficient ring of `Λ p`).
* "good ordinary `p`" is carried by the ambient `AnalyticData p hsplit` bundle: the
  paper works at split primes `p ≡ 1 (mod 4)` of good reduction, which is exactly
  the parameterisation of `AnalyticData`.

## Statement shape (deliberate)

These two are stated over a bare `AnalyticData p hsplit`, *not* over
`ClassicalInputs` — they are the minimal-hypothesis form, consuming only the three
fields (`interp`, `msymb_zero`, `funct_eq`) that the paper's proof uses.
Downstream (Theorem A (Theorem 4.9), `prop_consequence`) they are applied to
`(H.dataAt p hp hsplit hpS).analytic`.

Paper statements rendered here: Lemma 4.1.
-/

open PowerSeries

namespace FinShaRank2

/-- **Lemma 4.1, first half — `c₀(p) = 0`.**

> *`c₀(p) = L_p(E,0) = (1 − α_p⁻¹)² · L(E,1)/Ω_E = 0`.*

Derived from the MTT interpolation data-equation `A.interp` together
with the exact certificate `A.msymb_zero : modularSymbol0 = 0`; the only work is
cast arithmetic, since `interp` lives in `ℚ_[p]` while the conclusion is the
integral statement `constantCoeff L_p = 0` in `ℤ_[p]` (the coercion
`ℤ_[p] ↪ ℚ_[p]` is injective).

TRANSLATION: `c₀(p)` ↦ `constantCoeff A.Lp : ℤ_[p]`; the paper's hypothesis
`L(E,1) = 0` ↦ the field `A.msymb_zero`. -/
theorem c0_eq_zero {p : ℕ} [Fact p.Prime] {hsplit : p % 4 = 1}
    (A : AnalyticData p hsplit) : constantCoeff A.Lp = 0 := by
  have h := A.interp
  rw [A.msymb_zero] at h
  simp only [Rat.cast_zero, mul_zero] at h
  exact PadicInt.coe_eq_zero.mp h

/-- **Lemma 4.1, second half — `c₁(p) = 0`.**

> *For good `p` there is a unit power series `U(T) ∈ Λ^×` with `U(0) = 1` such
> that `L_p(E,(1+T)⁻¹−1) = w(E)·U(T)·L_p(E,T)`; with `w(E) = +1`, comparing linear
> coefficients gives `−c₁ = c₁`, hence `c₁ = 0`.*

Derived from the field `A.funct_eq` — the functional equation with the
root number `w(E) = +1` already folded in — via the kernel lemma
`FinShaRank2.coeff_one_Lp_eq_zero` (`Kernel/FunctionalEquation.lean`,
`Kernel/FunctionalEquation.lean`), which
performs the "compare linear coefficients" step abstractly. That kernel lemma also
consumes `constantCoeff Lp = 0`, i.e. `c0_eq_zero` above, exactly as the paper's
proof does; its 2-torsion side condition is discharged from `ℤ_[p]` being a
characteristic-zero domain (no oddness of `p` is needed).

TRANSLATION: `c₁(p)` ↦ `coeff 1 A.Lp : ℤ_[p]`; the substitution
`T ↦ (1+T)⁻¹ − 1` ↦ `PowerSeries.subst σ` with `σ` of `Defs.lean`; `w(E) = +1` is
folded into `A.funct_eq`. -/
theorem c1_eq_zero {p : ℕ} [Fact p.Prime] {hsplit : p % 4 = 1}
    (A : AnalyticData p hsplit) : coeff 1 A.Lp = 0 := by
  obtain ⟨U, _hUunit, hU0, hFE⟩ := A.funct_eq
  exact coeff_one_Lp_eq_zero A.Lp U hU0 hFE (c0_eq_zero A)

end FinShaRank2
