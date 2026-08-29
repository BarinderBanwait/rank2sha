import Mathlib
import FinShaRank2.Defs
import FinShaRank2.Kernel.Anomalous

/-!
# Normalisation of the second jet (task T26)

Two pieces of `mathlib`-only arithmetic for *Horizontal rigidity for second jets
of Katz p-adic L-functions, with applications to the Tate–Shafarevich group in
rank two*:

* **(A) `rmk:normalisation`(i).** At a non-anomalous prime and with the testbed's
  rational factor `(#tors)²/∏cᵥ = 1`, the normalisation is invisible to the unit
  test: `IsPUnit (c̃₂(p)) ↔ IsUnit (c₂(p))`. Formally
  `isPUnit_c2tilde_iff`, on the standalone `Defs.c2tilde`.
* **(B) Non-anomality bridge.** Every split prime of the testbed is either `5` or
  at least `13` (`Kernel/Anomalous.eq_five_or_thirteen_le`), which is exactly the
  case split `Kernel/Anomalous.noAnomalous` (T24) consumes; hence
  `isPUnit_one_sub_alphaInv_of_split` produces the `IsPUnit (1 − α_p⁻¹)`
  hypothesis of (A) from the `AnalyticData` field shapes alone — **except** at
  `p = 5`, where the value `a₅ = −2` must be supplied (see the consumption
  section).

This file also held the digit-certificate extraction lemmas
`isUnit_of_toZModPow_cert`, `isUnit_of_toZModPow_cert'`, `isUnit_of_cert_five`
and `isUnit_of_cert_thirteen`, which served the withdrawn anchor corollaries
`cor:sha5` / `cor:sha13`. They were retired to `legacy/Anchors.lean` on
2026-08-29 and are not part of the audited tree.

## Proof routes

**(A)** `c2tilde c₂ α⁻¹ tors = c₂ · (1 − α⁻¹)⁻² · tors`, and `IsPUnit` is the
norm condition `‖·‖ = 1` (`Defs.IsPUnit`). With `‖1 − α⁻¹‖ = 1` and `tors = 1`
the multiplicative norm collapses the two extra factors, so
`‖c̃₂‖ = ‖c₂‖`; `Defs.isPUnit_coe_iff` then converts `‖(c₂ : ℚ_[p])‖ = 1` into
`IsUnit (c₂ : ℤ_[p])`. Nothing here needs `c₂ ≠ 0` or invertibility of
`1 − α⁻¹` beyond its norm.

**(B)** A prime `p` with `p % 4 = 1` and `p < 13` must be `5`: the residues
`1, 9` below `13` are `1` (not prime) and `9 = 3²`. `interval_cases` plus
`Nat.Prime 9 = False` closes it, and the result feeds `noAnomalous`'s
`13 ≤ p ∨ (p = 5 ∧ a = −2)` disjunction.

## Interface consumption

* **`prop:consequence` and `thm:reduction`.** `isPUnit_c2tilde_iff` is stated on
  `Defs.c2tilde` with an integral `c2 : ℤ_[p]` coerced to `ℚ_[p]`, i.e. against
  the mandatory double-coercion spelling `c2tilde ((coeff 2 Lp : ℤ_[p]) : ℚ_[p])
  (((α : ℤ_[p]) : ℚ_[p])⁻¹) tst` used by `PrimeData.c2norm_tie` (T14) and
  `Statements.PrimeData.c2tilde` (T15); it applies to those terms with no
  adapter. Its `tors = 1` hypothesis is discharged by
  `ClassicalInputs.torsSqOverTam_eq`, and its `IsPUnit (1 − alphaInv)` hypothesis
  by `ClassicalInputs.isPUnit_one_sub_alphaInv` (`Main/Consequence.lean`) from
  the `notAnomalous` field, the `S_an` clause of `eq:Sexc`.
* **The two `_of_split` lemmas are off that route** since task R2a. They compose
  (B) with (A) and so carry the residual side condition `p = 5 → a = −2`, which
  the caller had to supply at `p = 5`; `notAnomalous` supplies non-anomality at
  every split `p ∉ S` instead. They are kept because (B) is the *proved*
  `lem:noanomalous`(2) — it derives non-anomality from the Hasse bound and the CM
  shape at every split `p ≥ 13`, which bounds what `notAnomalous` assumes beyond
  the proved lemma to the single value `a₅`.

Paper labels quoted below: `rmk:normalisation`, `def:c2tilde`,
`lem:noanomalous`.
-/

open PowerSeries

namespace FinShaRank2

/-! ### (A) `rmk:normalisation`(i) — the normalisation is invisible to the unit test -/

/-- **`rmk:normalisation`(i).** At a non-anomalous prime (`IsPUnit (1 − α_p⁻¹)`,
supplied by `lem:noanomalous` / T24) and with the testbed's rational factor
`(#tors)²/∏cᵥ = 1`, the normalised second jet is a `p`-adic unit exactly when the
raw second jet is:
`IsPUnit (c̃₂(p)) ↔ IsUnit (c₂(p))`.

The second jet `c2 : ℤ_[p]` is integral (it is `coeff 2 Lp`) and is coerced into
`ℚ_[p]`, where `c2tilde` lives; the right-hand side is genuine invertibility in
`ℤ_[p]`.

Route: `‖·‖` is multiplicative on `ℚ_[p]`, so `‖c̃₂‖ = ‖c₂‖ · ‖1 − α⁻¹‖⁻² · ‖1‖`
collapses to `‖c₂‖`; then `isPUnit_coe_iff`. PAPER: `rmk:normalisation`(i),
`def:c2tilde`. -/
theorem isPUnit_c2tilde_iff {p : ℕ} [Fact p.Prime] (c2 : ℤ_[p]) (alphaInv : ℚ_[p]) (tors : ℚ)
    (hanom : IsPUnit ((1 : ℚ_[p]) - alphaInv)) (htors : tors = 1) :
    IsPUnit (c2tilde (c2 : ℚ_[p]) alphaInv tors) ↔ IsUnit c2 := by
  have hanom' : ‖(1 : ℚ_[p]) - alphaInv‖ = 1 := hanom
  subst htors
  rw [← isPUnit_coe_iff]
  show ‖c2tilde (c2 : ℚ_[p]) alphaInv 1‖ = 1 ↔ ‖(c2 : ℚ_[p])‖ = 1
  simp only [c2tilde, norm_mul, norm_pow, norm_inv, hanom', Rat.cast_one,
    inv_one, one_pow, mul_one]

/-! ### (B) Bridging T24's non-anomality to the normalisation hypothesis

The split-prime dichotomy `eq_five_or_thirteen_le` used below was moved to
`Kernel/Anomalous.lean` (task R1β), where `anomalous_iff_five` also needs it;
`Anomalous.lean` is imported by this file, so the name is unchanged. -/

/-- **Non-anomality at a split prime, in the form `rmk:normalisation`(i)
consumes.** From the `AnalyticData` fields `hasse`, `ap_from_CM`, `alpha_root`
(verbatim shapes) plus the split hypothesis `p % 4 = 1`, the local factor
`1 − α_p⁻¹` is a `p`-adic unit — provided the value `a₅ = −2` is supplied in the
single case `p = 5`.

The side condition `h5 : p = 5 → a = -2` is vacuous at every split prime `p ≠ 5`
(`fun h => absurd h (by omega)` and the like) and must be supplied by the caller
at `p = 5`.

**Not on the route the main theorems take.** They obtain non-anomality from
`ClassicalInputs.notAnomalous`, the `S_an` clause of `eq:Sexc`, through
`ClassicalInputs.isPUnit_one_sub_alphaInv` (`Main/Consequence.lean`), and so carry
no `p = 5` side condition. This lemma is what makes that assumption small: it
proves the same conclusion outright at every split `p ≥ 13`, from the
`AnalyticData` fields alone.

Route: `eq_five_or_thirteen_le` supplies `noAnomalous`'s case split. PAPER:
`lem:noanomalous`, `rmk:normalisation`(i). -/
theorem isPUnit_one_sub_alphaInv_of_split {p : ℕ} [Fact p.Prime] {a : ℤ} {α : ℤ_[p]ˣ}
    (hsplit : p % 4 = 1)
    (hasse : a ^ 2 ≤ 4 * (p : ℤ))
    (ap_from_CM : ∃ π : GaussianInt, π.norm = (p : ℤ) ∧ a = 2 * π.re)
    (alpha_root : (α : ℤ_[p]) ^ 2 - (a : ℤ_[p]) * (α : ℤ_[p]) + (p : ℤ_[p]) = 0)
    (h5 : p = 5 → a = -2) :
    IsPUnit ((1 : ℚ_[p]) - ((α : ℤ_[p]) : ℚ_[p])⁻¹) :=
  noAnomalous hasse ap_from_CM alpha_root
    ((eq_five_or_thirteen_le (Fact.out : p.Prime) hsplit).symm.imp_right fun h => ⟨h, h5 h⟩)

/-- **`rmk:normalisation`(i) composed with `lem:noanomalous`(2).** The
composition of `isPUnit_one_sub_alphaInv_of_split` and `isPUnit_c2tilde_iff`:
from the `AnalyticData` fields alone (plus `p = 5 → a = −2` and the pinned
rational factor `torsSqOverTam = 1` of `ClassicalInputs.torsSqOverTam_eq`),

`IsPUnit (c̃₂(p)) ↔ IsUnit (c₂(p))`

with `c̃₂(p)` in the mandatory double-coercion spelling
`c2tilde ((c2 : ℤ_[p]) : ℚ_[p]) (((α : ℤ_[p]) : ℚ_[p])⁻¹) tors` of
`PrimeData.c2norm_tie` / `Statements.PrimeData.c2tilde`.

Like `isPUnit_one_sub_alphaInv_of_split`, it is off the route the main theorems
take since task R2a; see that lemma's docstring. PAPER: `rmk:normalisation`(i),
`def:c2tilde`, `lem:noanomalous`. -/
theorem isPUnit_c2tilde_iff_of_split {p : ℕ} [Fact p.Prime] {a : ℤ} {α : ℤ_[p]ˣ}
    (c2 : ℤ_[p]) (tors : ℚ)
    (hsplit : p % 4 = 1)
    (hasse : a ^ 2 ≤ 4 * (p : ℤ))
    (ap_from_CM : ∃ π : GaussianInt, π.norm = (p : ℤ) ∧ a = 2 * π.re)
    (alpha_root : (α : ℤ_[p]) ^ 2 - (a : ℤ_[p]) * (α : ℤ_[p]) + (p : ℤ_[p]) = 0)
    (h5 : p = 5 → a = -2) (htors : tors = 1) :
    IsPUnit (c2tilde (c2 : ℚ_[p]) (((α : ℤ_[p]) : ℚ_[p])⁻¹) tors) ↔ IsUnit c2 :=
  isPUnit_c2tilde_iff c2 _ tors
    (isPUnit_one_sub_alphaInv_of_split hsplit hasse ap_from_CM alpha_root h5) htors

end FinShaRank2
