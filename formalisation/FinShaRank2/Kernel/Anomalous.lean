import Mathlib
import FinShaRank2.Defs

/-!
# Anomalous-prime arithmetic (task T24, paper `lem:noanomalous`)

This file proves, as pure `mathlib`-only arithmetic, that the split primes
relevant to the testbed curve `E : y² = x³ − 56x` are **non-anomalous**: the
Frobenius unit root `α_p` satisfies `α_p ≢ 1 (mod 𝔭)`, equivalently the local
factor `1 − α_p⁻¹` that appears in the interpolation / normalisation is a
`p`-adic unit. This is exactly the input that discharges the non-anomalous
hypothesis carried by every theorem about `c2tilde` (see `Defs.lean`), used by
tasks T26 (`rmk:normalisation`(i)) and T31 (`prop:consequence`).

The argument has four gap-free pieces, matching the paper's proof:

* **(i) Hasse squeeze** (`ap_ne_one_of_hasse`). If `2 ∣ a`, `a² ≤ 4p` and
  `13 ≤ p` then `a ≢ 1 (mod p)`: from `a ≡ 1 (mod p)` we get `p ∣ (a − 1)` with
  `a − 1` odd hence nonzero, so `p ≤ |a − 1|`; but the Hasse bound forces
  `|a − 1| < p` for `p ≥ 13`, a contradiction.
* **(ii) Small prime** (`neg_two_ne_one_zmod_five`). At `p = 5`, where the Hasse
  squeeze does not apply, `a₅ = −2` is non-anomalous by direct computation:
  `−2 ≢ 1 (mod 5)`.
* **(iii) Unit-root lemma** (`isUnit_one_sub_alphaInv_iff`, and its `ℚ_[p]`-norm
  bridge `isPUnit_one_sub_alphaInv_iff`). For a unit `α` with
  `α² − a·α + p = 0`, reducing mod `𝔭` gives `α ≡ a (mod 𝔭)`; hence
  `1 − α⁻¹` is a unit iff `a ≢ 1 (mod p)`.
* **(iv) CM evenness** (`two_dvd_ap`). The `ap_from_CM` datum `a = 2·Re(π)`
  yields `2 ∣ a` in one line.

The composed convenience lemma `noAnomalous` packages all four for T31: from the
`AnalyticData` fields `hasse`, `ap_from_CM`, `alpha_root` and the split-prime
case split `13 ≤ p ∨ (p = 5 ∧ a_p = −2)`, it concludes
`IsPUnit ((1 : ℚ_[p]) − α_p⁻¹)`.

## Residue-field route

The unit-root reduction (iii) uses the mod-`p` residue ring homomorphism
`PadicInt.toZMod : ℤ_[p] →+* ZMod p` (rather than `toZModPow` or a norm
argument): its kernel is the maximal ideal (`PadicInt.ker_toZMod`), so for a
local ring an element is a unit exactly when its residue is nonzero
(`toZMod_eq_zero_iff_not_isUnit`). Reducing `alpha_root` under `toZMod` and
cancelling the unit `toZMod α` gives `toZMod α = (a : ZMod p)` directly, and the
whole equivalence follows in the field `ZMod p`.

Paper labels: `lem:noanomalous`, `def:c2tilde`, `rmk:normalisation`.
-/

namespace FinShaRank2

/-! ### Residue-map unit criterion -/

/-- In the local ring `ℤ_[p]`, an element lies in the kernel of the residue map
`PadicInt.toZMod` exactly when it is **not** a unit: `RingHom.ker toZMod` is the
maximal ideal (`PadicInt.ker_toZMod`), whose members are precisely the
non-units. -/
private theorem toZMod_eq_zero_iff_not_isUnit {p : ℕ} [Fact p.Prime] (y : ℤ_[p]) :
    PadicInt.toZMod y = 0 ↔ ¬ IsUnit y := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

/-- Unit criterion via the residue map: `y : ℤ_[p]` is a unit iff its residue
`PadicInt.toZMod y` is nonzero in `ZMod p`. -/
private theorem isUnit_iff_toZMod_ne_zero {p : ℕ} [Fact p.Prime] (y : ℤ_[p]) :
    IsUnit y ↔ PadicInt.toZMod y ≠ 0 := by
  rw [ne_eq, toZMod_eq_zero_iff_not_isUnit, not_not]

/-- **Reduction of the Frobenius relation mod `𝔭`.** If the unit `α` satisfies
`α² − a·α + p = 0` in `ℤ_[p]`, then its residue is `toZMod α = (a : ZMod p)`.
Reducing the relation kills `p` (as `(p : ZMod p) = 0`) and gives
`toZMod α · (toZMod α − a) = 0`; the residue of a unit is nonzero in the field
`ZMod p`, so it cancels. -/
private theorem toZMod_alpha_root {p : ℕ} [Fact p.Prime] {a : ℤ} {α : ℤ_[p]ˣ}
    (h : (α : ℤ_[p]) ^ 2 - (a : ℤ_[p]) * (α : ℤ_[p]) + (p : ℤ_[p]) = 0) :
    PadicInt.toZMod (α : ℤ_[p]) = (a : ZMod p) := by
  have hmap := congrArg PadicInt.toZMod h
  simp only [map_add, map_sub, map_mul, map_pow, map_intCast, map_natCast, map_zero,
    ZMod.natCast_self] at hmap
  set t := PadicInt.toZMod (α : ℤ_[p]) with ht
  have hunit : IsUnit t := (α.isUnit).map PadicInt.toZMod
  have hfac : t * (t - (a : ZMod p)) = 0 := by linear_combination hmap
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact absurd h1 hunit.ne_zero
  · exact sub_eq_zero.mp h2

/-! ### (iii) Unit-root lemma -/

/-- **Unit-root lemma (`ℤ_[p]` side).** For a unit `α` with `α² − a·α + p = 0`,
the local factor `1 − α⁻¹` (with `α⁻¹` the unit inverse) is a unit in `ℤ_[p]`
iff `a ≢ 1 (mod p)`.

Route: `toZMod α = a` (`toZMod_alpha_root`), so `toZMod α⁻¹ = a⁻¹` and
`toZMod (1 − α⁻¹) = 1 − a⁻¹` in the field `ZMod p`; then `1 − α⁻¹` is a unit iff
its residue is nonzero (`isUnit_iff_toZMod_ne_zero`) iff `a⁻¹ ≠ 1` iff
`a ≠ 1`. -/
theorem isUnit_one_sub_alphaInv_iff {p : ℕ} [Fact p.Prime] {a : ℤ} {α : ℤ_[p]ˣ}
    (h : (α : ℤ_[p]) ^ 2 - (a : ℤ_[p]) * (α : ℤ_[p]) + (p : ℤ_[p]) = 0) :
    IsUnit ((1 : ℤ_[p]) - ((α⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) ↔ ¬ ((a : ZMod p) = 1) := by
  have key : PadicInt.toZMod (α : ℤ_[p]) = (a : ZMod p) := toZMod_alpha_root h
  have hinv : PadicInt.toZMod ((α⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = ((a : ZMod p))⁻¹ := by
    have hmul : PadicInt.toZMod ((α⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * PadicInt.toZMod (α : ℤ_[p]) = 1 := by
      rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
    rw [key] at hmul
    exact eq_inv_of_mul_eq_one_left hmul
  rw [isUnit_iff_toZMod_ne_zero, map_sub, map_one, hinv, ne_eq, sub_eq_zero]
  exact not_congr (by rw [eq_comm, inv_eq_one])

/-- **Unit-root lemma (`ℚ_[p]`-norm bridge).** The same statement in the
`IsPUnit` (norm-one) form on `ℚ_[p]` that `c2tilde` consumes: `1 − α_p⁻¹`, with
`α_p⁻¹` the field inverse of the coerced unit root, has `p`-adic norm one iff
`a ≢ 1 (mod p)`.

Bridged to the `ℤ_[p]` version via `isPUnit_coe_iff` after identifying the
coerced unit inverse with the field inverse (`eq_inv_of_mul_eq_one_left`). -/
theorem isPUnit_one_sub_alphaInv_iff {p : ℕ} [Fact p.Prime] {a : ℤ} {α : ℤ_[p]ˣ}
    (h : (α : ℤ_[p]) ^ 2 - (a : ℤ_[p]) * (α : ℤ_[p]) + (p : ℤ_[p]) = 0) :
    IsPUnit ((1 : ℚ_[p]) - ((α : ℤ_[p]) : ℚ_[p])⁻¹) ↔ ¬ ((a : ZMod p) = 1) := by
  have hcoe : (((α⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = ((α : ℤ_[p]) : ℚ_[p])⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← PadicInt.coe_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, PadicInt.coe_one]
  rw [← hcoe, ← PadicInt.coe_one, ← PadicInt.coe_sub, isPUnit_coe_iff]
  exact isUnit_one_sub_alphaInv_iff h

/-! ### (i) Hasse squeeze -/

/-- **Hasse squeeze.** For an even trace `a` obeying the Hasse bound `a² ≤ 4p`
at a prime `p ≥ 13`, the trace is non-anomalous: `a ≢ 1 (mod p)`.

If `a ≡ 1 (mod p)` then `p ∣ (a − 1)`; since `a` is even, `a − 1` is odd, hence
nonzero, so `p ≤ |a − 1|`. The Hasse bound `a² ≤ 4p` with `p ≥ 13` forces
`|a − 1| < p` (integer-only: `(p ± 1)² > 4p` for `p ≥ 13`), a contradiction. No
primality of `p` is required. -/
theorem ap_ne_one_of_hasse {p : ℕ} {a : ℤ}
    (heven : 2 ∣ a) (hhasse : a ^ 2 ≤ 4 * (p : ℤ)) (hp : 13 ≤ p) :
    ¬ ((a : ZMod p) = 1) := by
  intro hcong
  have hdvd : (p : ℤ) ∣ (a - 1) := by
    have h0 : ((a - 1 : ℤ) : ZMod p) = 0 := by push_cast; rw [hcong]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0
  have hpz : (13 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  have hne : a - 1 ≠ 0 := by omega
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hdvd' : (p : ℤ) ∣ (1 - a) := by
      rw [show (1 - a) = -(a - 1) by ring]; exact (dvd_neg).mpr hdvd
    have hle : (p : ℤ) ≤ 1 - a := Int.le_of_dvd (by omega) hdvd'
    have h1 : (0 : ℤ) ≤ 1 - a - p := by linarith
    have h2 : (0 : ℤ) ≤ -a + p - 1 := by linarith
    nlinarith [hhasse, mul_nonneg h1 h2]
  · have hle : (p : ℤ) ≤ a - 1 := Int.le_of_dvd hgt hdvd
    have h1 : (0 : ℤ) ≤ a - 1 - p := by linarith
    have h2 : (0 : ℤ) ≤ a - 1 + p := by linarith
    nlinarith [hhasse, mul_nonneg h1 h2]

/-! ### (ii) Small prime `p = 5` -/

/-- **Small-prime non-anomality at `p = 5`.** The trace `a₅ = −2` is
non-anomalous: `−2 ≢ 1 (mod 5)`, checked by kernel-level `decide` (no
`native_decide`). This covers the prime `p = 5 < 13` where the Hasse squeeze
`ap_ne_one_of_hasse` does not apply. -/
theorem neg_two_ne_one_zmod_five : ¬ (((-2 : ℤ) : ZMod 5) = 1) := by decide

/-! ### (iv) CM evenness -/

/-- **CM evenness of the trace.** From the `ap_from_CM`-shaped datum
`a = 2·Re(π)` (with `π` a Gaussian integer of norm `p`), conclude `2 ∣ a`. -/
theorem two_dvd_ap {p : ℕ} {a : ℤ}
    (h : ∃ π : GaussianInt, π.norm = (p : ℤ) ∧ a = 2 * π.re) : 2 ∣ a := by
  obtain ⟨π, _, ha⟩ := h
  exact ⟨π.re, ha⟩

/-! ### Composed non-anomality (the T31 deliverable) -/

/-- **Non-anomality, composed for `prop:consequence` (T31).** Package (i)–(iv):
from the `AnalyticData` fields `hasse` (`a² ≤ 4p`), `ap_from_CM`
(`a = 2·Re(π)`, `N(π) = p`) and `alpha_root` (`α² − a·α + p = 0`), together with
the split-prime case split `13 ≤ p ∨ (p = 5 ∧ a = −2)`, conclude that the local
factor `1 − α⁻¹` is a `p`-adic unit,
`IsPUnit ((1 : ℚ_[p]) − α⁻¹)`.

This is the exact non-anomalous hypothesis carried by `c2tilde`: at any split
prime `p ∉ S` with `p ≥ 13` it is discharged by the Hasse squeeze (i) fed by CM
evenness (iv); at `p = 5` by the direct computation (ii). -/
theorem noAnomalous {p : ℕ} [Fact p.Prime] {a : ℤ} {α : ℤ_[p]ˣ}
    (hasse : a ^ 2 ≤ 4 * (p : ℤ))
    (ap_from_CM : ∃ π : GaussianInt, π.norm = (p : ℤ) ∧ a = 2 * π.re)
    (alpha_root : (α : ℤ_[p]) ^ 2 - (a : ℤ_[p]) * (α : ℤ_[p]) + (p : ℤ_[p]) = 0)
    (hp : 13 ≤ p ∨ (p = 5 ∧ a = -2)) :
    IsPUnit ((1 : ℚ_[p]) - ((α : ℤ_[p]) : ℚ_[p])⁻¹) := by
  rw [isPUnit_one_sub_alphaInv_iff alpha_root]
  rcases hp with hp13 | ⟨rfl, ha5⟩
  · exact ap_ne_one_of_hasse (two_dvd_ap ap_from_CM) hasse hp13
  · rw [ha5]; exact neg_two_ne_one_zmod_five

end FinShaRank2
