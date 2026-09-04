import Mathlib
import FinShaRank2.Defs
import FinShaRank2.Interface.Global
import FinShaRank2.Interface.Katz
import FinShaRank2.Kernel.Decoupling
import FinShaRank2.Kernel.FunctionalEquation
import FinShaRank2.Kernel.GradingValuation
import FinShaRank2.Kernel.Normalization
import FinShaRank2.Kernel.Resultant
import FinShaRank2.Main.Consequence
import FinShaRank2.Statements

/-!
# Theorem C (Theorem 7.10) — Conjecture 7.9 + Hypothesis 7.8 ⟹ the unit condition outside an explicit set

`thm_reduction` is the paper's theorem, taking one instance of Conjecture 7.9;
`thm_reduction_of_conjEK` is the same statement with that instance
supplied by the conjecture.

> **Theorem (Reduction, Theorem C).** *Assume Hypothesis 7.8 for*
> *`E`, let `c` be a vector as in its part (i), and assume `δ_E(c) ≠ 0`. Then for*
> *every split `p ≥ 5` of good reduction with `p ∉ S_E ∪ supp(c)` and*
> *`𝔭 ∤ δ_E(c)`: `c̃₂(p) ∈ ℤ_p^×`, `λ_an(𝔭) = 2`, `Ш(E/ℚ)[p^∞] = 0`. If*
> *`S_E` is finite, Conjecture 5.1 holds for `E`.*

## The epistemic firewall

**Conjecture 7.9 and Hypothesis 7.8 occur in this file and nowhere else.** Both appear
strictly in hypothesis position:

* `hEK` = one instance of Conjecture 7.9, the nonvanishing of the Eisenstein–Kronecker
  invariant Definition 6.2; formally `H.ek.deltaE c ≠ 0`. The conjecture itself is
  `ConjEK H` (`Statements.lean`) and is a hypothesis of `thm_reduction_of_conjEK`
  below, which is the only declaration that mentions it;
* `hsin` = Hypothesis 7.8, formally the `Prop`-structure `SinnottHyp` quantified
  over every split `p ∉ H.S ∪ supp(c)`.

Neither occurs in `prop_consequence`, `prop_dictionary` or `cor_horizontal`: those
are conditional on the interface alone, apart from `cor_horizontal`'s `ConjWeak`,
which is the paper's own hypothesis for Corollary B. `SinnottHyp` is never a field of
an instantiable structure, so the assumption surface `ClassicalInputs` stays free
of conjecture.

## Translation conventions

* The theorem's display at the vector `c` ↦ `ConjStrongAt H c` (`Statements.lean`);
  the paper's excluded set is `H.S ∪ H.ek.supp c`. `ConjStrong H`, its universal
  closure, is the strong form withdrawn from the paper on 2026-09-03 and is *not*
  what this theorem proves.
* `𝔭 ∤ δ_E(c)`, i.e. `v_𝔭(ι_p δ_E(c)) = 0` (§2.1) ↦
  `H.ek.v p (H.ek.deltaE c) = 1`. Mathlib's `Valuation` is multiplicative, so the
  paper's `v_𝔭(x) = 0` is `v x = 1` (module docstring of `Interface/EK.lean`).
* `p ∉ supp(c)` ↦ `p ∉ H.ek.supp c`.
* `λ_an(𝔭) = 2` ↦ `lambdaAn (…).analytic.Lp = 2`, kept paired with
  `MuZero (…).analytic.Lp` so that the junk-value pair stays adjacent (`lambdaAn` is
  junk-valued without it).
* `Ш(E/ℚ)[p^∞] = 0` ↦ `Subsingleton (…).selmer.ShaDual` (dual side).
* "`p ≥ 5` of good reduction, `p ∉ S_E`" ↦ `hsplit : p % 4 = 1` and `hpS : p ∉ H.S`.

## Deviations from the paper's shape, and why

1. `hsin` is spelled `SinnottHyp p (…).analytic.Lp (…).katz H.ek c`, not
   `SinnottHyp p … (….toKatzData) …`: the `KatzData` and `ClassicalInputs` interface
   exposes the Katz layer
   as the `PrimeData` **field** `katz : KatzData p analytic.Lp`, and there is no
   `toKatzData` coercion (aggregation, not `extends` — see
   `Interface/Global.lean`). Same content, forced spelling.
2. The paper's last assertion is conditional on `S_E` being finite. `H.S` is a
   `Finset ℕ`, so finiteness holds by construction and the conditional disappears.
3. The first conjunct reports `MuZero` alongside `lambdaAn = 2` (the junk-value pair,
kept adjacent); the
   paper's display names only `c̃₂(p) ∈ ℤ_p^×`, `λ_an(𝔭) = 2` and `Ш = 0`.
4. `ConjStrongAt` carries no integrality clause; integrality is classical
   (Remark 3.4), see the docstring in `Statements.lean`.

Paper statements rendered here: Theorem C, Conjecture 7.9, Hypothesis 7.8,
Definition 6.2, Theorem A (Theorem 3.8).
-/

open PowerSeries

namespace FinShaRank2

/-- **Theorem C (Theorem 7.10)** — the paper's reduction of horizontal rigidity to
Conjecture 7.9 (`hEK`) and Hypothesis 7.8 (`hsin`).

> *Assume Hypothesis 7.8 for `E`, let `c` be a vector as in its part*
> *(i), and assume `δ_E(c) ≠ 0`. Then for every split `p ≥ 5` of good reduction*
> *with `p ∉ S_E ∪ supp(c)` and `𝔭 ∤ δ_E(c)`: `c̃₂(p) ∈ ℤ_p^×`, `λ_an(𝔭) = 2`,*
> *`Ш(E/ℚ)[p^∞] = 0`. If `S_E` is finite, Conjecture 5.1 holds*
> *for `E`.*

The conclusion is the conjunction of the per-prime statement and `ConjStrongAt H c`,
the theorem's display at the vector `c`.

Assembly route. `hsin.integral` is Hypothesis 7.8(i)'s integrality clause, so the
factors of `δ_E(c) = ∏_{t ∈ D_E} F_c(t)` (`EKPackage.deltaE_def`) are all
`𝔭`-integral; with `𝔭 ∤ δ_E(c)`,
`Kernel.Resultant.forall_eq_one_of_prod_eq_one` gives `v_𝔭(F_c(t)) = 0` for every
`t ∈ D_E`. That is the antecedent of `hsin.nonvanishing`, which yields
`traceClass ≠ 0`; `hsin.presentation` identifies the residue of `m2core` with it,
so `SelmerData.π_surj` (`Kernel.GradingValuation.isUnit_iff_residue_ne_zero_of_grading_congr`)
yields `IsUnit (coeff 2 LKatz)`; `KatzData.comparison` + `Kernel/Decoupling.lean`
(`Kernel.Decoupling.isUnit_coeff_two_of_comparison`) transfers unitness to
`coeff 2 Lp`; `isPUnit_c2tilde_iff` (`Kernel.Normalization.isPUnit_c2tilde_iff`, fed non-anomality
by `ClassicalInputs.isPUnit_one_sub_alphaInv` and the rational factor by
`H.torsSqOverTam_eq`) converts it to `IsPUnit c̃₂(p)`; `prop_consequence` supplies
the remaining three conclusions.

The first step is proved rather than assumed, and the integrality it rests on is
a clause of `hsin`, which is where the paper puts it.

`_hEK` renders input (i) of Theorem C. The conclusions rendered here do not consume
it: at each prime `𝔭 ∤ δ_E(c)` already forces `δ_E(c) ≠ 0`
(`Kernel.Resultant.prod_ne_zero_of_prod_eq_one`), and `ConjStrongAt H c` carries that
hypothesis on every prime it speaks about. What consumes it in the paper is Theorem
C's final clause, "if `S_E` is finite, Conjecture 5.1 holds for `E`", which is **not
rendered**: deriving it needs `{p | 𝔭 ∣ δ_E(c)}` to be finite, and `EKPackage.v` is an
abstract family of valuations with no such field. The hypothesis is kept so the
statement matches the paper's input list.

`hEK`/`hsin` are the **only** conjectural hypotheses in the project and occur
nowhere else.

TRANSLATION: see the module docstring (`𝔭 ∤ δ_E(c)` ↦ `H.ek.v p (H.ek.deltaE c) = 1`;
dual-side Ш; μ/λ pairing). -/
theorem thm_reduction (H : ClassicalInputs) (c : Fin 6 → H.ek.K)
    (_hEK : H.ek.deltaE c ≠ 0)
    (hsin : ∀ (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1) (hpS : p ∉ H.S),
      p ∉ H.ek.supp c →
      letI : Fact p.Prime := ⟨hp⟩
      SinnottHyp p (H.dataAt p hp hsplit hpS).analytic.Lp (H.dataAt p hp hsplit hpS).katz
        H.ek c) :
    (∀ (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1) (hpS : p ∉ H.S), p ∉ H.ek.supp c →
        H.ek.v p (H.ek.deltaE c) = 1 →
          letI : Fact p.Prime := ⟨hp⟩
          IsPUnit (H.dataAt p hp hsplit hpS).c2tilde
            ∧ MuZero (H.dataAt p hp hsplit hpS).analytic.Lp
            ∧ lambdaAn (H.dataAt p hp hsplit hpS).analytic.Lp = 2
            ∧ Subsingleton (H.dataAt p hp hsplit hpS).selmer.ShaDual)
      ∧ ConjStrongAt H c := by
  have key : ∀ (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1) (hpS : p ∉ H.S),
      p ∉ H.ek.supp c → H.ek.v p (H.ek.deltaE c) = 1 →
        letI : Fact p.Prime := ⟨hp⟩
        IsPUnit (H.dataAt p hp hsplit hpS).c2tilde := by
    intro p hp hsplit hpS hsupp hval
    have : Fact p.Prime := ⟨hp⟩
    set D := H.dataAt p hp hsplit hpS with hDdef
    have hsin' := hsin p hp hsplit hpS hsupp
    -- step 1 Hypothesis 7.8(i) makes every factor of `δ_E(c)` `𝔭`-integral, and
    --   `𝔭 ∤ δ_E(c)` then forces every factor to be a `𝔭`-unit.
    have hprod : H.ek.v p (∏ t ∈ H.ek.D, H.ek.Fc c t) = 1 := by
      rw [← H.ek.deltaE_def c]; exact hval
    have hunits : ∀ t ∈ H.ek.D, H.ek.v p (H.ek.Fc c t) = 1 :=
      Resultant.forall_eq_one_of_prod_eq_one (H.ek.v p) H.ek.D (H.ek.Fc c)
        hsin'.integral hprod
    -- step 2 Hypothesis 7.8(ii), then its presentation clause.
    have htr : D.katz.traceClass ≠ 0 := hsin'.nonvanishing hunits
    have hres : IsLocalRing.residue D.katz.W D.katz.m2core ≠ 0 := by
      rw [hsin'.presentation]; exact htr
    -- step 4
    have hpne : (p : D.katz.W) ≠ 0 := by
      intro h
      have h0 : (p : ℤ_[p]) = 0 := by
        apply D.katz.algInj
        rw [map_natCast, map_zero]
        exact h
      exact (Nat.cast_ne_zero.mpr hp.ne_zero) h0
    obtain ⟨κ₀, hcong⟩ := D.katz.grading_congr
    have hLK : IsUnit (coeff 2 D.katz.LKatz) :=
      (isUnit_iff_residue_ne_zero_of_grading_congr D.katz.maxIdeal_eq_p hpne κ₀ _ _ hcong).mpr hres
    -- step 5
    obtain ⟨c, u, hcomp⟩ := D.katz.comparison
    have := D.katz.algMap_isLocalHom
    have hu0 : IsUnit (coeff 0 (u : PowerSeries D.katz.W)) := by
      rw [coeff_zero_eq_constantCoeff]
      exact u.isUnit.map (constantCoeff (R := D.katz.W))
    have hc0 : constantCoeff D.analytic.Lp = 0 := by
      have h := D.analytic.interp
      rw [D.analytic.msymb_zero] at h
      simp only [Rat.cast_zero, mul_zero] at h
      exact PadicInt.coe_eq_zero.mp h
    have hc0' : coeff 0 D.analytic.Lp = 0 := by
      rw [coeff_zero_eq_constantCoeff_apply]; exact hc0
    have hc1 : coeff 1 D.analytic.Lp = 0 := by
      obtain ⟨U, _hU, hU0, hFE⟩ := D.analytic.funct_eq
      exact coeff_one_Lp_eq_zero D.analytic.Lp U hU0 hFE hc0
    have hmul1 : ∀ A B : PowerSeries D.katz.W,
        coeff 1 (A * B) = coeff 0 A * coeff 1 B + coeff 1 A * coeff 0 B := by
      intro A B
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp [Finset.sum_range_succ]
    have hmul0 : ∀ A B : PowerSeries D.katz.W,
        coeff 0 (A * B) = coeff 0 A * coeff 0 B := by
      intro A B
      rw [coeff_zero_eq_constantCoeff, map_mul]
    have hK0 : coeff 0 D.katz.LKatz = 0 := by
      have h : coeff 0 (D.analytic.Lp.map (algebraMap ℤ_[p] D.katz.W)) = 0 := by
        rw [coeff_map, hc0', map_zero]
      rw [hcomp, Decoupling.coeff_smul_eq_mul, hmul0] at h
      rw [c.isUnit.mul_right_eq_zero, hu0.mul_right_eq_zero] at h
      exact h
    have hK1 : coeff 1 D.katz.LKatz = 0 := by
      have h : coeff 1 (D.analytic.Lp.map (algebraMap ℤ_[p] D.katz.W)) = 0 := by
        rw [coeff_map, hc1, map_zero]
      rw [hcomp, Decoupling.coeff_smul_eq_mul, hmul1, hK0, mul_zero, add_zero] at h
      rw [c.isUnit.mul_right_eq_zero, hu0.mul_right_eq_zero] at h
      exact h
    have hLp2 : IsUnit (coeff 2 D.analytic.Lp) :=
      Decoupling.isUnit_coeff_two_of_comparison (algebraMap ℤ_[p] D.katz.W)
        D.analytic.Lp D.katz.LKatz c u hcomp hK0 hK1 hLK
    -- step 6 Proposition 3.3, with non-anomality from `H.notAnomalous`.
    exact (isPUnit_c2tilde_iff (coeff 2 D.analytic.Lp) _ H.torsSqOverTam
      (H.isPUnit_one_sub_alphaInv hsplit hpS) H.torsSqOverTam_eq).mpr hLp2
  refine ⟨?_, key⟩
  intro p hp hsplit hpS hsupp hval
  have : Fact p.Prime := ⟨hp⟩
  have hc2 := key p hp hsplit hpS hsupp hval
  obtain ⟨hmu, hlam, _, hsha⟩ := prop_consequence H hsplit hpS hc2
  exact ⟨hc2, hmu, hlam, hsha⟩

/-- **Theorem C (Theorem 7.10) with its first input supplied by Conjecture 7.9.**

Theorem C lists as its input (i) the nonvanishing `δ_E(c) ≠ 0` for a vector `c` as
in its input (ii), and records that Conjecture 7.9 implies it, that vector being
nonzero. `thm_reduction` takes the single instance `H.ek.deltaE c ≠ 0`; this
corollary takes the conjecture instead and applies it at `c`.

`hc : c ≠ 0` is the nonzeroness that Hypothesis 7.8(i) asserts of the vector it
produces ("There exist a nonzero `c ∈ K⁶` and an integer `k ≥ 1` …"). It is a
separate hypothesis here because `SinnottHyp` renders the three clauses
`integral`, `presentation` and `nonvanishing` and carries `c` as a parameter, so
the existential of Hypothesis 7.8(i) — and with it the nonzeroness of its witness —
is discharged by the caller, as in `thm_reduction`.

`hconj` and `hsin` are conjectural and occur in hypothesis position only. This is
the only declaration in the project that mentions `ConjEK`.

TRANSLATION: as `thm_reduction`; Conjecture 7.9 ↦ `ConjEK H` (`Statements.lean`), whose
docstring records the one hypothesis of Conjecture 7.9 that is not rendered. -/
theorem thm_reduction_of_conjEK (H : ClassicalInputs) (c : Fin 6 → H.ek.K) (hc : c ≠ 0)
    (hconj : ConjEK H)
    (hsin : ∀ (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1) (hpS : p ∉ H.S),
      p ∉ H.ek.supp c →
      letI : Fact p.Prime := ⟨hp⟩
      SinnottHyp p (H.dataAt p hp hsplit hpS).analytic.Lp (H.dataAt p hp hsplit hpS).katz
        H.ek c) :
    (∀ (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1) (hpS : p ∉ H.S), p ∉ H.ek.supp c →
        H.ek.v p (H.ek.deltaE c) = 1 →
          letI : Fact p.Prime := ⟨hp⟩
          IsPUnit (H.dataAt p hp hsplit hpS).c2tilde
            ∧ MuZero (H.dataAt p hp hsplit hpS).analytic.Lp
            ∧ lambdaAn (H.dataAt p hp hsplit hpS).analytic.Lp = 2
            ∧ Subsingleton (H.dataAt p hp hsplit hpS).selmer.ShaDual)
      ∧ ConjStrongAt H c :=
  thm_reduction H c (hconj c hc) hsin

end FinShaRank2
