import Mathlib
import FinShaRank2.Defs
import FinShaRank2.Interface.Global
import FinShaRank2.Interface.Katz
import FinShaRank2.Kernel.Decoupling
import FinShaRank2.Kernel.FunctionalEquation
import FinShaRank2.Kernel.GradingValuation
import FinShaRank2.Kernel.Normalization
import FinShaRank2.Main.Consequence
import FinShaRank2.Statements

/-!
# `thm:reduction` — Conjecture `conj:EK` + Hypothesis `hyp:sinnott` ⟹ `conj:strong` (task T33)

Frozen headline signature (T15 statement freeze; `TASK_BOARD.md` §2 conv. 7).
The proof is supplied by task T33.

> **Theorem (Reduction, `thm:reduction`).** *Assume Conjecture `conj:EK` and
> Hypothesis `hyp:sinnott`. Then Conjecture `conj:strong` holds for `E` with the
> invariant `δ_E` of `def:deltaE` and with `S_E = S` …: for every split `p ∉ S`
> with `𝔭 ∤ δ_E`, `c̃₂(p) ∈ ℤ_p^×`, and consequently (`prop:consequence`)
> `λ_an(𝔭) = 2` and `Ш(E/ℚ)[p^∞] = 0`.*

## The epistemic firewall (`TASK_BOARD.md` §1, conv. 4)

**This is the only declaration in the project that may mention conjectural
input.** The two conjectural items appear here strictly in hypothesis position:

* `h87` = `conj:EK`, the nonvanishing `δ_E ≠ 0` of the Eisenstein–Kronecker
  resultant invariant `def:deltaE`; formally `H.deltaE ≠ 0`;
* `h86` = `hyp:sinnott`, the Sinnott-type hypothesis, formally the
  `Prop`-structure `SinnottHyp` quantified over every split `p ∉ H.S`.

Neither occurs in `prop_consequence`, `prop_dictionary`, `cor_sha5`, or
`cor_sha13`: those are conditional on the interface (plus `Certificates`) alone.
`SinnottHyp` is never a field of an instantiable structure, so the assumption
surface `ClassicalInputs` stays free of conjecture.

## Translation conventions (`TASK_BOARD.md` §2)

* Conjecture `conj:strong` ↦ `ConjStrong H` (`Statements.lean`), which already
  quantifies over split `p ∉ H.S` and carries the `𝔭 ∤ δ_E` side condition.
* `𝔭 ∤ δ_E`, i.e. `v_𝔭(ι_p δ_E) = 0` (`ssec:notation`) ↦
  `padicValRat p H.deltaE = 0`.
* `λ_an(𝔭) = 2` ↦ `lambdaAn (…).analytic.Lp = 2`, kept paired with
  `MuZero (…).analytic.Lp` per conv. 5 (`lambdaAn` is junk-valued without it).
* `Ш(E/ℚ)[p^∞] = 0` ↦ `Subsingleton (…).selmer.ShaDual` (conv. 1).
* `S_E = S` is built in: `ConjStrong H` and the second conjunct both quantify over
  `p ∉ H.S`, the paper's `eq:Sexc` set.

## Deviations from the board's mandated shape, and why

1. `h86` is spelled `SinnottHyp p (…).analytic.Lp (…).katz`, not
   `SinnottHyp p … (….toKatzData)`: the frozen T13/T14 interface exposes the Katz
   layer as the `PrimeData` **field** `katz : KatzData p analytic.Lp`, and there is
   no `toKatzData` coercion (aggregation, not `extends` — see
   `Interface/Global.lean`). Same content, forced spelling.
2. A third hypothesis `h5` is present, per the PM ruling of 2026-07-30
   (option (a)): T24's `lem:noanomalous` closes non-anomality unconditionally for
   split `p ≥ 13`, but the residual case `p = 5` needs `a₅ = −2`, which
   `ClassicalInputs` does not supply (`S : Finset ℕ` is opaque data, so `p ∉ H.S`
   has no formal non-anomality content). `h5` is **certificate-grade arithmetic,
   not a conjecture** — it is discharged from `Certificates.a5` — so the epistemic
   split is untouched. See `Main/Consequence.lean` for the full rationale.
3. The second conjunct reports `MuZero` alongside `lambdaAn = 2` (conv. 5); the
   paper's sentence names only `λ_an(𝔭) = 2` and `Ш = 0`.

Paper labels rendered here: `thm:reduction`, `conj:EK`, `hyp:sinnott`,
`conj:strong`, `def:deltaE`, `prop:consequence`.
-/

open PowerSeries

namespace FinShaRank2

/-- **`thm:reduction`** — the paper's reduction of horizontal rigidity to
`conj:EK` (`h87`) and `hyp:sinnott` (`h86`).

> *Then Conjecture `conj:strong` holds for `E` with the invariant `δ_E` and*
> *`S_E = S`: for every split `p ∉ S` with `𝔭 ∤ δ_E`, `c̃₂(p) ∈ ℤ_p^×`, and*
> *consequently `λ_an(𝔭) = 2` and `Ш(E/ℚ)[p^∞] = 0`.*

The conclusion is the conjunction of the conjecture itself, `ConjStrong H`, and
the arithmetic consequence spelled out per split prime with `𝔭 ∤ δ_E`.

Assembly route for T33 (`TASK_BOARD.md`): `KatzData.resultant_link` turns `h87` +
`padicValRat p H.deltaE = 0` (transported to the local avatar by
`PrimeData.deltaE_tie`) into `NonvanishingOnDE`; `h86`'s `nonvanishing` then gives
`traceClass ≠ 0` and its `presentation` identifies the residue of `m2core` with
it, so T25 (`Kernel.GradingValuation.isUnit_iff_residue_ne_zero_of_grading_congr`)
yields `IsUnit (coeff 2 LKatz)`; `KatzData.comparison` + T22
(`Kernel.Decoupling.isUnit_coeff_two_of_comparison`) transfers unitness to
`coeff 2 Lp`; T26 (`Kernel.Normalization.isPUnit_c2tilde_iff_of_split`, fed by
`h5` and `H.torsSqOverTam_eq`) converts it to `IsPUnit c̃₂(p)`, which is
`ConjStrong H`; `prop_consequence` then supplies the second conjunct.

`h86`/`h87` are the **only** conjectural hypotheses in the project and occur
nowhere else (`TASK_BOARD.md` §1).

TRANSLATION: see the module docstring (`𝔭 ∤ δ_E` ↦ `padicValRat p H.deltaE = 0`;
dual-side Ш; μ/λ pairing). -/
theorem thm_reduction (H : ClassicalInputs)
    (h87 : H.deltaE ≠ 0)
    (h86 : ∀ (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1) (hpS : p ∉ H.S),
      letI : Fact p.Prime := ⟨hp⟩
      SinnottHyp p (H.dataAt p hp hsplit hpS).analytic.Lp (H.dataAt p hp hsplit hpS).katz)
    (h5 : ∀ (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1) (hpS : p ∉ H.S),
      letI : Fact p.Prime := ⟨hp⟩
      p = 5 → (H.dataAt p hp hsplit hpS).analytic.ap = -2) :
    ConjStrong H
      ∧ ∀ (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1) (hpS : p ∉ H.S),
          padicValRat p H.deltaE = 0 →
            letI : Fact p.Prime := ⟨hp⟩
            MuZero (H.dataAt p hp hsplit hpS).analytic.Lp
              ∧ lambdaAn (H.dataAt p hp hsplit hpS).analytic.Lp = 2
              ∧ Subsingleton (H.dataAt p hp hsplit hpS).selmer.ShaDual := by
  have key : ∀ (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1) (hpS : p ∉ H.S),
      padicValRat p H.deltaE = 0 →
        letI : Fact p.Prime := ⟨hp⟩
        IsPUnit (H.dataAt p hp hsplit hpS).c2tilde := by
    intro p hp hsplit hpS hval
    letI : Fact p.Prime := ⟨hp⟩
    set D := H.dataAt p hp hsplit hpS with hDdef
    -- step 1
    have hne : D.katz.deltaE_local ≠ 0 := by rw [D.deltaE_tie]; exact h87
    have hval' : padicValRat p D.katz.deltaE_local = 0 := by rw [D.deltaE_tie]; exact hval
    -- step 2
    have hnv : D.katz.NonvanishingOnDE := D.katz.resultant_link hne hval'
    -- step 3
    have hsin := h86 p hp hsplit hpS
    have htr : D.katz.traceClass ≠ 0 := hsin.nonvanishing hnv
    have hres : IsLocalRing.residue D.katz.W D.katz.m2core ≠ 0 := by
      rw [hsin.presentation]; exact htr
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
    haveI := D.katz.algMap_isLocalHom
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
    -- step 6
    exact (isPUnit_c2tilde_iff_of_split (coeff 2 D.analytic.Lp) H.torsSqOverTam hsplit
      D.analytic.hasse D.analytic.ap_from_CM D.analytic.alpha_root (h5 p hp hsplit hpS)
      H.torsSqOverTam_eq).mpr hLp2
  refine ⟨fun p hp hsplit hpS _ hval => key p hp hsplit hpS hval, ?_⟩
  intro p hp hsplit hpS hval
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hmu, hlam, _, hsha⟩ :=
    prop_consequence H hsplit hpS (h5 p hp hsplit hpS) (key p hp hsplit hpS hval)
  exact ⟨hmu, hlam, hsha⟩

end FinShaRank2
