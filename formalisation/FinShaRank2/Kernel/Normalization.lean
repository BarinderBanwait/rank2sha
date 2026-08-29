import Mathlib
import FinShaRank2.Defs
import FinShaRank2.Kernel.Anomalous

/-!
# Normalisation of the second jet, and digit-certificate extraction (task T26)

Two independent pieces of `mathlib`-only arithmetic for *Horizontal rigidity for
second jets of Katz p-adic L-functions, with applications to the Tate–Shafarevich
group in rank two*:

* **(A) `rmk:normalisation`(i).** At a non-anomalous prime and with the testbed's
  rational factor `(#tors)²/∏cᵥ = 1`, the normalisation is invisible to the unit
  test: `IsPUnit (c̃₂(p)) ↔ IsUnit (c₂(p))`. Formally
  `isPUnit_c2tilde_iff`, on the standalone `Defs.c2tilde`.
* **(B) Certificate extraction.** A digit congruence in the frozen T14 shape
  `PadicInt.toZModPow k x = ((d : ℤ) : ZMod (p ^ k))` together with a
  non-divisibility side condition yields `IsUnit x` (`isUnit_of_toZModPow_cert`,
  `isUnit_of_toZModPow_cert'`), with the two anchor primes instantiated verbatim
  (`isUnit_of_cert_five`, `isUnit_of_cert_thirteen`).

A third, small piece bridges T24 to (A):

* **(C) Non-anomality bridge.** Every split prime of the testbed is either `5` or
  at least `13` (`eq_five_or_thirteen_le`), which is exactly the case split
  `Kernel/Anomalous.noAnomalous` (T24) consumes; hence
  `isPUnit_one_sub_alphaInv_of_split` produces the `IsPUnit (1 − α_p⁻¹)`
  hypothesis of (A) from the `AnalyticData` field shapes alone — **except** at
  `p = 5`, where the value `a₅ = −2` must be supplied (see the contract section).

## Proof routes

**(A)** `c2tilde c₂ α⁻¹ tors = c₂ · (1 − α⁻¹)⁻² · tors`, and `IsPUnit` is the
norm condition `‖·‖ = 1` (`Defs.IsPUnit`). With `‖1 − α⁻¹‖ = 1` and `tors = 1`
the multiplicative norm collapses the two extra factors, so
`‖c̃₂‖ = ‖c₂‖`; `Defs.isPUnit_coe_iff` then converts `‖(c₂ : ℚ_[p])‖ = 1` into
`IsUnit (c₂ : ℤ_[p])`. Nothing here needs `c₂ ≠ 0` or invertibility of
`1 − α⁻¹` beyond its norm.

**(B)** Contrapositive. If `x : ℤ_[p]` is not a unit then `‖x‖ < 1`
(`PadicInt.isUnit_iff`, `PadicInt.norm_le_one`), so `p ∣ x`
(`PadicInt.norm_lt_one_iff_dvd`), say `x = p * y`. Pushing the certificate along
`ZMod.castHom (p ^ k ∣ …) (ZMod p)` — legal because `k ≥ 1` — makes the left side
`(p : ZMod p) * … = 0`, so the reduced digit `(d : ZMod p)` vanishes,
contradicting the side condition. The `¬ ((p : ℤ) ∣ d)` variant is the same
statement through `ZMod.intCast_zmod_eq_zero_iff_dvd`; it is the form the anchor
primes use, since `norm_num` discharges a divisibility of explicit integers.

**(C)** A prime `p` with `p % 4 = 1` and `p < 13` must be `5`: the residues
`1, 9` below `13` are `1` (not prime) and `9 = 3²`. `interval_cases` plus
`Nat.Prime 9 = False` closes it, and the result feeds `noAnomalous`'s
`13 ≤ p ∨ (p = 5 ∧ a = −2)` disjunction.

## Interface consumption (contract for T31/T34)

* **T31 (`prop:consequence`).** `isPUnit_c2tilde_iff` is stated on `Defs.c2tilde`
  with an integral `c2 : ℤ_[p]` coerced to `ℚ_[p]`, i.e. against the mandatory
  double-coercion spelling `c2tilde ((coeff 2 Lp : ℤ_[p]) : ℚ_[p])
  (((α : ℤ_[p]) : ℚ_[p])⁻¹) tst` used by `PrimeData.c2norm_tie` (T14) and
  `Statements.PrimeData.c2tilde` (T15); it applies to those terms with no
  adapter. Its `tors = 1` hypothesis is discharged by
  `ClassicalInputs.torsSqOverTam_eq`, and its `IsPUnit (1 − alphaInv)` hypothesis
  by `isPUnit_one_sub_alphaInv_of_split` below (or directly by T24's
  `noAnomalous`), whose hypotheses are the `AnalyticData` fields `hasse`,
  `ap_from_CM`, `alpha_root` verbatim. `isPUnit_c2tilde_iff_of_split` packages
  the two into a single call.
* **Residual input at `p = 5`.** `isPUnit_one_sub_alphaInv_of_split` carries the
  side condition `p = 5 → a = −2`. It is *vacuous at every split prime `p ≠ 5`*
  and is discharged at `p = 5` by the certificate `Certificates.a5`. It cannot be
  removed: `ClassicalInputs.S` is opaque `Finset ℕ` data, so `p ∉ S` carries no
  formal non-anomality content (the four membership reasons of `eq:Sexc` are
  documentation), and `a₅ = −2` is a numerical fact about the testbed curve.
* **T34 (`cor:sha5`, `cor:sha13`).** `isUnit_of_cert_five` and
  `isUnit_of_cert_thirteen` take `Certificates.c2_5` / `Certificates.c2_13`
  **verbatim** — same `k` (`7`, `5`), same `((… : ℤ) : ZMod (p ^ k))` coercion
  spelling, same digit sums — and return
  `IsUnit (PowerSeries.coeff 2 (…).analytic.Lp)` directly
  (`Scratch/T26Check.lean` exercises exactly these two calls against a
  hypothetical `(H : ClassicalInputs) (C : Certificates H)`). The
  `[Fact (Nat.Prime 5)]` / `[Fact (Nat.Prime 13)]` binders are instance-implicit
  rather than local instances, so they are resolved at the call site by the
  project-wide instances declared in `Interface/Certificates.lean` — this file
  stays in the `Kernel/` layer (mathlib + `Defs` + `Kernel/Anomalous` only).

Paper labels quoted below: `rmk:normalisation`, `def:c2tilde`, `eq:match5`,
`eq:pred13`, `lem:noanomalous`, `cor:sha5`, `cor:sha13`.
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

/-! ### (B) Digit-certificate extraction -/

/-- **Certificate extraction, residue-field form.** A digit congruence in the
frozen T14 shape — an equality in `ZMod (p ^ k)` between `PadicInt.toZModPow k x`
and the image of an explicit integer `d` — upgrades to `IsUnit x` as soon as the
reduction of `d` mod `p` is nonzero. Needs `1 ≤ k` so that `p ∣ p ^ k`.

Route (contrapositive): a non-unit `x` has `‖x‖ < 1`, hence `p ∣ x`; reducing the
certificate along `ZMod.castHom (dvd_pow_self p _) (ZMod p)` sends the left side
to `0`, forcing `(d : ZMod p) = 0`. PAPER: `cor:sha5`, `cor:sha13` (extraction
step). -/
theorem isUnit_of_toZModPow_cert {p : ℕ} [Fact p.Prime] {x : ℤ_[p]} {k : ℕ} (hk : 1 ≤ k)
    {d : ℤ} (hcert : PadicInt.toZModPow k x = (d : ZMod (p ^ k)))
    (hd : ¬ ((d : ZMod p) = 0)) : IsUnit x := by
  by_contra hx
  rw [PadicInt.isUnit_iff] at hx
  obtain ⟨y, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd x).mp ((PadicInt.norm_le_one x).lt_of_ne hx)
  apply hd
  have hg := congrArg
    (ZMod.castHom (dvd_pow_self p (Nat.one_le_iff_ne_zero.mp hk)) (ZMod p)) hcert
  simp only [map_mul, map_natCast, map_intCast, ZMod.natCast_self, zero_mul] at hg
  exact hg.symm

/-- **Certificate extraction, divisibility form.** Same as
`isUnit_of_toZModPow_cert`, with the side condition phrased as `¬ ((p : ℤ) ∣ d)`
— the form in which `norm_num` discharges it for an explicit digit sum. This is
the version the anchor primes use. PAPER: `cor:sha5`, `cor:sha13`. -/
theorem isUnit_of_toZModPow_cert' {p : ℕ} [Fact p.Prime] {x : ℤ_[p]} {k : ℕ} (hk : 1 ≤ k)
    {d : ℤ} (hcert : PadicInt.toZModPow k x = (d : ZMod (p ^ k)))
    (hd : ¬ ((p : ℤ) ∣ d)) : IsUnit x :=
  isUnit_of_toZModPow_cert hk hcert
    (fun h => hd ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp h))

/-! ### (B') The two anchor primes, instantiated on the frozen certificate shape -/

/-- **`eq:match5` ⟹ `IsUnit c₂(5)`.** The hypothesis is `Certificates.c2_5`
verbatim: the image of `x` under `PadicInt.toZModPow 7` equals the seven-digit
sum `1 + 4·5 + 3·5² + 5³ + 5⁵ + 5⁶` in `ZMod (5 ^ 7)`. The digit sum is `18971`,
which is `≡ 1 (mod 5)`, so `5 ∤ 18971` and `x` is a unit.

Applied by T34 to `C.c2_5` with
`x := PowerSeries.coeff 2 (H.dataAt 5 _ _ C.five_notin).analytic.Lp`, no adapter.
PAPER: `eq:match5`, `cor:sha5` proof (v). -/
theorem isUnit_of_cert_five [Fact (Nat.Prime 5)] {x : ℤ_[5]}
    (hcert : PadicInt.toZModPow 7 x
      = ((1 + 4 * 5 + 3 * 5 ^ 2 + 5 ^ 3 + 5 ^ 5 + 5 ^ 6 : ℤ) : ZMod (5 ^ 7))) :
    IsUnit x :=
  isUnit_of_toZModPow_cert' (by norm_num) hcert (by norm_num)

/-- **`eq:pred13` ⟹ `IsUnit c₂(13)`.** The hypothesis is `Certificates.c2_13`
verbatim: the image of `x` under `PadicInt.toZModPow 5` equals the five-digit sum
`1 + 11·13 + 13² + 13³ + 10·13⁴` in `ZMod (13 ^ 5)`. The digit sum is `288120`,
which is `≡ 1 (mod 13)`, so `13 ∤ 288120` and `x` is a unit.

Applied by T34 to `C.c2_13` with
`x := PowerSeries.coeff 2 (H.dataAt 13 _ _ C.thirteen_notin).analytic.Lp`, no
adapter. PAPER: `eq:pred13`, `cor:sha13` proof. -/
theorem isUnit_of_cert_thirteen [Fact (Nat.Prime 13)] {x : ℤ_[13]}
    (hcert : PadicInt.toZModPow 5 x
      = ((1 + 11 * 13 + 13 ^ 2 + 13 ^ 3 + 10 * 13 ^ 4 : ℤ) : ZMod (13 ^ 5))) :
    IsUnit x :=
  isUnit_of_toZModPow_cert' (by norm_num) hcert (by norm_num)

/-! ### (C) Bridging T24's non-anomality to the normalisation hypothesis -/

/-- **Split primes are `5` or at least `13`.** A prime `p` with `p ≡ 1 (mod 4)`
— the paper's standing splitness assumption for `K = ℚ(i)`, carried as
`AnalyticData`'s `hsplit` — satisfies `p = 5 ∨ 13 ≤ p`: below `13` the residue
class `1 mod 4` contains only `1` and `9`, neither of which is prime.

This is exactly the disjunction `Kernel/Anomalous.noAnomalous` consumes, so it is
what turns the split hypothesis into the Hasse-squeeze / small-prime case split
of `lem:noanomalous`. -/
theorem eq_five_or_thirteen_le {p : ℕ} (hp : p.Prime) (hsplit : p % 4 = 1) :
    p = 5 ∨ 13 ≤ p := by
  rcases Nat.lt_or_ge p 13 with hlt | hge
  · refine Or.inl ?_
    interval_cases p <;> first | omega | exact absurd hp (by norm_num)
  · exact Or.inr hge

/-- **Non-anomality at a split prime, in the form `rmk:normalisation`(i)
consumes.** From the `AnalyticData` fields `hasse`, `ap_from_CM`, `alpha_root`
(verbatim shapes) plus the split hypothesis `p % 4 = 1`, the local factor
`1 − α_p⁻¹` is a `p`-adic unit — provided the value `a₅ = −2` is supplied in the
single case `p = 5`.

The side condition `h5 : p = 5 → a = -2` is vacuous at every split prime `p ≠ 5`
(`fun h => absurd h (by omega)` and the like) and is discharged at `p = 5` by the
certificate `Certificates.a5`. It is genuinely needed: `ClassicalInputs.S` is
opaque `Finset` data, so `p ∉ S` carries no formal non-anomality content.

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

/-- **`rmk:normalisation`(i), packaged for T31.** The composition of
`isPUnit_one_sub_alphaInv_of_split` and `isPUnit_c2tilde_iff`: from the
`AnalyticData` fields alone (plus `p = 5 → a = −2` and the pinned rational factor
`torsSqOverTam = 1` of `ClassicalInputs.torsSqOverTam_eq`),

`IsPUnit (c̃₂(p)) ↔ IsUnit (c₂(p))`

with `c̃₂(p)` in the mandatory double-coercion spelling
`c2tilde ((c2 : ℤ_[p]) : ℚ_[p]) (((α : ℤ_[p]) : ℚ_[p])⁻¹) tors` of
`PrimeData.c2norm_tie` / `Statements.PrimeData.c2tilde`. PAPER:
`rmk:normalisation`(i), `def:c2tilde`, `lem:noanomalous`. -/
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
