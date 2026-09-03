import Mathlib

/-!
# Unit factors of a unit resultant)

This file proves, as pure `mathlib`-only valuation theory over an abstract valued field, the
valuation step in the proof of the paper's Theorem C (Theorem 5.10). Nothing here
mentions the paper's
interface: the argument is carried over a bare `Valuation v : L → Γ`, so the instantiation
`L := Q̄`, `v := v_𝔭` performed downstream is a substitution.

## Mathematical content

Definition 3.1 sets `δ_E(c) = ∏_{t ∈ D_E} F_c(t)`. The proof of Theorem C
argues: each
factor `F_c(t)` is `𝔭`-integral by Hypothesis 5.8(i), so `v_𝔭(δ_E(c)) = ∑_{t ∈ D_E} v_𝔭(F_c(t))`
is a sum of nonnegative terms; hence `𝔭 ∤ δ_E(c)` forces `v_𝔭(F_c(t)) = 0` for every
`t ∈ D_E`. `forall_eq_one_of_prod_eq_one` is that implication.

## Sign convention

**mathlib normalises valuations multiplicatively, and the inequality below is not backwards.**
A `Valuation L Γ` is a monoid-with-zero hom `L →*₀ Γ` into a linearly ordered commutative
monoid with zero, so where the paper writes an additive `v_𝔭` this file writes its exponential.
The translation is:

* paper `v_𝔭(x) ≥ 0` (`x` is `𝔭`-integral) reads here as `v x ≤ 1`;
* paper `v_𝔭(x) = 0` (`x` is a `𝔭`-unit) reads here as `v x = 1`;
* paper `v_𝔭(xy) = v_𝔭(x) + v_𝔭(y)` reads here as `v (x * y) = v x * v y`.

The multiplicative encoding is forced by the pin: `AddValuation` carries no lemma for the
valuation of a product — only `map_le_sum`, which is the analogue of `map_add`, not of
`map_prod` — whereas `Valuation` has a `MonoidWithZeroHomClass` instance, so the root
`map_prod` applies to it directly.

## Main results

* `FinShaRank2.Resultant.forall_eq_one_of_prod_eq_one` — the paper's implication: if every
  factor is integral and the product is a unit, every factor is a unit.
* `FinShaRank2.Resultant.prod_ne_zero_of_prod_eq_one` — the product is nonzero as soon as its
  valuation is `1`.

The second is a small strengthening over the paper, which carries `δ_E(c) ≠ 0` as a separate
hypothesis of Theorem C. In the valuation formulation that hypothesis is
free: `v x = 1`
already implies `x ≠ 0`, provided the value monoid `Γ` is nontrivial. The strengthening does not
make the paper's hypothesis redundant, because Theorem C also uses
`δ_E(c) ≠ 0` outside
this step, and because `Γ` nontrivial is an extra assumption.

## Downstream

`Main/Reduction.lean` consumes `forall_eq_one_of_prod_eq_one` as the first step of
`thm_reduction`, applied to the divisor `D_E` and the values `F_c` of `EKPackage`
(`Interface/EK.lean`). Until the refactor that step was the assumed `KatzData` field
`resultant_link`, which asserted its conclusion outright; the integrality it rested on is
now the hypothesis `SinnottHyp.integral`, where the paper puts it.

Paper statements: Theorem C, Definition 3.1, Hypothesis 5.8(i), §2.1.
-/

namespace FinShaRank2.Resultant

variable {L Γ ι : Type*} [Field L] [LinearOrderedCommMonoidWithZero Γ]

/-- **Unit factors of a unit product.** Let `v` be a valuation on `L`, let `D` be a finite index
set, and let `F : ι → L`. If every factor `F t`, `t ∈ D`, is integral (`v (F t) ≤ 1`) and the
product `∏ t ∈ D, F t` is a unit (`v (∏ t ∈ D, F t) = 1`), then every factor is a unit
(`v (F t) = 1`).

Recall the sign convention of the module docstring: `v x ≤ 1` is the paper's `v_𝔭(x) ≥ 0` and
`v x = 1` is the paper's `v_𝔭(x) = 0`.

The proof distributes `v` over the product (`map_prod`, available because `Valuation` is a
`MonoidWithZeroHomClass`) and applies `Finset.prod_eq_one_iff_of_le_one'`: in an ordered
commutative monoid a product of elements `≤ 1` equals `1` exactly when every factor equals `1`.
PAPER: Theorem C (Theorem 5.10, `thm:reduction`), proof; Hypothesis 5.8 (`hyp:sinnott`)(i). -/
theorem forall_eq_one_of_prod_eq_one (v : Valuation L Γ) (D : Finset ι) (F : ι → L)
    (hint : ∀ t ∈ D, v (F t) ≤ 1) (hδ : v (∏ t ∈ D, F t) = 1) :
    ∀ t ∈ D, v (F t) = 1 := by
  rw [map_prod] at hδ
  exact (Finset.prod_eq_one_iff_of_le_one' hint).mp hδ

/-- **A unit product is nonzero.** If `v (∏ t ∈ D, F t) = 1` and the value monoid `Γ` is
nontrivial, then `∏ t ∈ D, F t ≠ 0`.

Theorem C (Theorem 5.10) assumes `δ_E(c) ≠ 0` separately from `𝔭 ∤ δ_E(c)`; at the point where the
valuation argument is made, the first follows from the second. A valuation sends `0` to `0`
(`Valuation.ne_zero_iff`), and `1 ≠ 0` in a nontrivial `Γ`. PAPER: Theorem C,
Definition 3.1. -/
theorem prod_ne_zero_of_prod_eq_one [Nontrivial Γ] (v : Valuation L Γ) (D : Finset ι)
    (F : ι → L) (hδ : v (∏ t ∈ D, F t) = 1) :
    (∏ t ∈ D, F t) ≠ 0 :=
  v.ne_zero_iff.mp (by rw [hδ]; exact one_ne_zero)

end FinShaRank2.Resultant
