import Mathlib

/-!
# Core definitions

This file fixes the basic objects shared across the whole formalization of
*Second derivatives of p-adic L-functions and the Shafarevich–Tate group of
rank-two CM elliptic curves*.

It is intentionally interface-free: it mentions none of the per-prime data
structures. `Interface/` builds those on top of these definitions and `Kernel/`
reasons about them, so everything here is a **standalone** definition of
explicit arguments.

Contents:

* `Λ p` — the Iwasawa algebra `ℤ_[p]⟦X⟧` (mathlib `PowerSeries ℤ_[p]`).
* `σ` — the functional-equation substitution representing `(1 + T)⁻¹ − 1`,
  with the coefficient facts and the `HasSubst` witness that `Kernel/FunctionalEquation.lean` (the
  functional-equation coefficient lemma, paper Lemma 3.1) consumes.
* `IsPUnit` — the p-adic unit predicate `‖x‖ = 1` on `ℚ_[p]`.
* `MuZero`, `lambdaAn` — the Iwasawa μ = 0 predicate and analytic λ-invariant of
  a power series (paper Theorem B (Theorem 3.9), Step 2).
* `c2tilde` — the normalised second jet Definition 3.2.
* `corank` — the `ℤ_[p]`-corank abbreviation (`Module.finrank ℤ_[p] ·`) used to
  phrase the Selmer-corank conclusions (conventions §2.1).

Paper statements quoted below: Definition 3.2, Proposition 3.3, Lemma 3.1,
Theorem B.

## API notes for downstream tasks

* `PowerSeries.coeff` carries its coefficient ring **implicitly** in this mathlib
  release (`coeff n f`, not `coeff R n f`); `MuZero`/`lambdaAn` are written that
  way. See `NOTES/MathlibAudit.md` §3(1).
* `Λ` is an `abbrev`, so it is reducibly equal to `PowerSeries ℤ_[p]` and every
  `PowerSeries`/`MvPowerSeries` instance is available on it without glue.
* `σ` is fixed at coefficient ring `ℤ_[p]` (its type is `Λ p`). A task needing
  the ring-generic substitution `Σₙ (−1)ⁿ Tⁿ` over an arbitrary base (e.g. the
  ring-generic half of `Kernel/FunctionalEquation.lean`) should replicate the one-line
  `PowerSeries.mk`; the
  proofs here transfer verbatim.
-/

open PowerSeries

namespace FinShaRank2

variable {p : ℕ} [Fact p.Prime]

/-- The Iwasawa algebra `Λ = ℤ_[p]⟦X⟧` in which the p-adic L-function `L_p(E, T)`
of the testbed curve lives. Declared as an `abbrev` so it is reducibly
`PowerSeries ℤ_[p]`: all ring, algebra, local-ring and Noetherian instances flow
automatically (see `NOTES/MathlibAudit.md`). The variable `T` of the paper is
mathlib's `PowerSeries.X`. -/
abbrev Λ (p : ℕ) [Fact p.Prime] : Type := PowerSeries ℤ_[p]

/-- The functional-equation substitution, representing `(1 + T)⁻¹ − 1`
as the power series `Σₙ₌₁^∞ (−1)ⁿ Tⁿ = −T + T² − T³ + ⋯`.

Substituting `σ` into `L_p(E, T)` realises the change of variable `s ↦ 2 − s` on
the cyclotomic line that underlies the Mazur–Tate–Teitelbaum functional equation
with sign `w(E) = +1`; this is the input to Lemma 3.1 (see `oneAddX_mul_σ` and
`FinShaRank2.hasSubst_σ`). -/
noncomputable def σ : Λ p := PowerSeries.mk fun n => if n = 0 then 0 else (-1) ^ n

/-- The constant term of `σ` vanishes: `σ` represents `(1 + T)⁻¹ − 1`, which is
`0` at `T = 0`. This is exactly the side condition that makes `σ` substitutable
(`hasSubst_σ`). -/
theorem constantCoeff_σ : constantCoeff (σ : Λ p) = 0 := by
  simp [σ, constantCoeff_mk]

/-- The linear coefficient of `σ` is `−1` (the leading term of `(1 + T)⁻¹ − 1`).
Task `Kernel/FunctionalEquation.lean` uses this to turn the functional equation into `c₁
= −c₁`, forcing
`c₁ = 0` (Lemma 3.1). -/
theorem coeff_one_σ : coeff 1 (σ : Λ p) = -1 := by
  simp [σ, coeff_mk]

/-- `σ` is a legal power-series substitution, because its constant term vanishes
(`constantCoeff_σ`). This is the witness that `L_p.subst σ` is well defined; it
feeds the functional-equation hypothesis of `AnalyticData` (`AnalyticData`) and the kernel
lemma `Kernel/FunctionalEquation.lean`. Tool: `PowerSeries.HasSubst.of_constantCoeff_zero'`. -/
theorem hasSubst_σ : HasSubst (σ : Λ p) :=
  HasSubst.of_constantCoeff_zero' (by simp [σ, constantCoeff_mk])

/-- Characterising identity `(1 + T) · σ = −T`, i.e. `σ = (1 + T)⁻¹ − 1`
exactly. Provided as a convenience for `Kernel/FunctionalEquation.lean` (a
self-contained algebraic handle on
`σ` that avoids re-deriving its coefficients). -/
theorem oneAddX_mul_σ : (1 + X) * (σ : Λ p) = -X := by
  rw [add_mul, one_mul]
  ext n
  rw [map_add, map_neg, coeff_X]
  obtain _ | _ | m := n
  · simp [σ]
  · simp [σ, coeff_succ_X_mul]
  · rw [show m + 2 = (m + 1) + 1 from rfl, coeff_succ_X_mul]
    simp only [σ, coeff_mk, Nat.succ_ne_zero, if_false, if_neg (show m + 2 ≠ 1 by omega)]
    rw [pow_succ]; ring

/-- `x : ℚ_[p]` is a **p-adic unit** when `‖x‖ = 1`. For `x` in the ring of
integers this is genuine invertibility (`isPUnit_coe_iff`); phrasing it on
`ℚ_[p]` lets `c2tilde` — which lives in `ℚ_[p]` — be tested directly.
Paper: the conclusion `\tilde c_2(p) ∈ ℤ_p^×` of Conjecture 3.4. -/
def IsPUnit (x : ℚ_[p]) : Prop := ‖x‖ = 1

/-- For an integral element, `IsPUnit` of its image in `ℚ_[p]` is exactly
`IsUnit` in `ℤ_[p]`. This bridges the norm-phrased conclusion to the ring-theoretic
`IsUnit (coeff 2 L_p)` that `isPUnit_c2tilde_iff` (Proposition 3.3) extracts.
Tools: `PadicInt.padic_norm_e_of_padicInt`, `PadicInt.isUnit_iff`. -/
theorem isPUnit_coe_iff {x : ℤ_[p]} : IsPUnit (x : ℚ_[p]) ↔ IsUnit x := by
  rw [IsPUnit, PadicInt.padic_norm_e_of_padicInt, PadicInt.isUnit_iff]

/-- Vanishing of the Iwasawa μ-invariant, phrased on the Pontryagin-dual side as:
some coefficient of `f` is a `ℤ_[p]`-unit (equivalently, not every coefficient
lies in the maximal ideal `(p)`). Paper: Theorem B (Theorem 3.9), Step 2.

Kept **paired** with `lambdaAn` in downstream statements (conventions §2.5): the
λ-invariant is meaningful only where `MuZero` holds. -/
def MuZero (f : Λ p) : Prop := ∃ n, IsUnit (PowerSeries.coeff n f)

/-- The analytic λ-invariant of `f`: the least index `n` whose coefficient is a
`ℤ_[p]`-unit — i.e. the order of `f` modulo the maximal ideal, when `f ≠ 0` mod
`(p)`.

**Junk-value convention** (conventions §2.5): `sInf` of the empty set is `0`, so
`lambdaAn f = 0` carries no information unless `MuZero f` holds. Statements must
pair `lambdaAn f = 2` with `MuZero f`. The coefficient ring of `PowerSeries.coeff`
is implicit in this mathlib release. -/
noncomputable def lambdaAn (f : Λ p) : ℕ := sInf {n | IsUnit (PowerSeries.coeff n f)}

/-- The **normalised second jet** `\tilde c_2(p)` of Definition 3.2:
`\tilde c_2(p) = c_2(p) · (1 − α_p⁻¹)⁻² · (#E(ℚ)_tors)² / ∏_v c_v`,
with `α_p` the unit root of `X² − a_p X + p`.

This is a standalone function of its data:
* `c2` — the second Taylor coefficient `c_2(p) = coeff 2 L_p`, cast to `ℚ_[p]`;
* `alphaInv` — the inverse unit root `α_p⁻¹ ∈ ℚ_[p]`;
* `torsSqOverTam` — the rational factor `(#tors)² / ∏_v c_v` (equal to `1` for the
  testbed curve; pinned as data in `ClassicalInputs`).

This file mentions no interface structure: `Interface/` supplies the arguments,
and `isPUnit_c2tilde_iff` (Proposition 3.3) proves `IsPUnit (c2tilde …) ↔ IsUnit (coeff 2 L_p)`
under the non-anomalous hypothesis.

**Junk-value convention** (conventions §2.5): `c2tilde` is total. At an anomalous
prime `1 − α_p⁻¹ = 0`, so `(1 − alphaInv)⁻¹ = 0` and the value degenerates; every
theorem about `c2tilde` therefore carries the non-anomalous hypothesis
`IsUnit (1 − alphaInv)` explicitly (for the testbed curve it is discharged via
Lemma 2.3, `Kernel/Anomalous.lean`). -/
noncomputable def c2tilde (c2 alphaInv : ℚ_[p]) (torsSqOverTam : ℚ) : ℚ_[p] :=
  c2 * (1 - alphaInv)⁻¹ ^ 2 * (torsSqOverTam : ℚ_[p])

/-- The `ℤ_[p]`-corank of a module, i.e. `Module.finrank ℤ_[p] M`.

On the dual side (conventions §2.1) the paper's statement
`corank_{ℤ_p} Sel_{p^∞}(E/ℚ) = 2` is phrased as `corank SelDual = 2`, since over
the DVR `ℤ_[p]` the finrank of the finitely generated dual computes the corank of
the original discrete module. -/
noncomputable abbrev corank (M : Type*) [AddCommGroup M] [Module ℤ_[p] M] : ℕ :=
  Module.finrank ℤ_[p] M

end FinShaRank2
