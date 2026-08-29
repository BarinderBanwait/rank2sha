import Mathlib
import FinShaRank2.Defs
import FinShaRank2.Interface.Global
import FinShaRank2.Interface.Certificates
import FinShaRank2.Kernel.FunctionalEquation
import FinShaRank2.Kernel.TsqUnit
import FinShaRank2.Kernel.LambdaModule
import FinShaRank2.Kernel.Normalization
import FinShaRank2.Kernel.ShaEndgame
import FinShaRank2.Statements

/-!
# T15 pre-freeze chain test (`TASK_BOARD.md` T15, risk register #3)

Scratch file — **not** imported by the root module, not audited.

The board mandates: *"Before declaring the freeze, write scratch `example`s that
chain the interface fields end-to-end with sorried kernel calls — this catches
composition mismatches while they are still cheap."*

This file composes the **real** chain of `prop:consequence` from a
`ClassicalInputs` at a split `p ∉ S`, using the genuine interface fields and the
genuine kernel theorems.

**Outcome: the chain composes with no adapters beyond one `coeff 0` /
`constantCoeff` rewrite, and it closes completely.** `T15Chain.chain` is a
finished, axiom-clean proof of exactly the frozen `FinShaRank2.prop_consequence`
statement — it is T31's assembly, available for lifting verbatim into
`Main/Consequence.lean`. Two auxiliary steps that no existing kernel file
supplied (`quotient_collapse`, `rank_lower_bound`) were identified by this test
and are proved below.

Chain exercised, in order:

1. `Kernel.Normalization.isPUnit_c2tilde_iff_of_split` on `PrimeData.c2tilde`
   (`rmk:normalisation`(i));
2. `AnalyticData.interp` + `AnalyticData.msymb_zero` ⟹ `c₀ = 0` (`lem:c0c1`);
3. `AnalyticData.funct_eq` + `Kernel.FunctionalEquation.coeff_one_Lp_eq_zero`
   ⟹ `c₁ = 0` (`lem:c0c1`);
4. `Kernel.TsqUnit.{muZero_of_coeffs, lambdaAn_eq_two_of_coeffs,
   associated_X_sq_of_coeffs}` ⟹ `μ = 0`, `λ = 2`, `Associated Lp X²`;
5. `IwasawaData.control` ⟹ the rank lower bound on the T-coinvariants;
6. `IwasawaData.rubin_structure` + `Kernel.LambdaModule.selmer_dual_structure`
   ⟹ `T` kills `X` and `X ≃ₗ[ℤ_[p]] ℤ_p²`;
7. `IwasawaData.control` again ⟹ `SelDual ≃ₗ[ℤ_[p]] ℤ_p²`;
8. `Kernel.ShaEndgame.sha_endgame_of_nonempty` on `SelmerData`'s five exactness
   fields ⟹ `Subsingleton ShaDual` and `finrank SelDual = 2`.

## Findings (see the agent report for the full write-up)

* **(A) `control` vs T23's T-coinvariants — MATCH, confirmed by composition.**
  `IwasawaData.control` has domain
  `X ⧸ (Ideal.span {(PowerSeries.X : Λ p)} • (⊤ : Submodule (Λ p) X))` and
  `selmer_dual_structure`'s `hrank` speaks about the same expression, including
  the `Module ℤ_[p]` structure inferred from the scalar tower. `rw
  [D.iwasawa.control.finrank_eq]` rewrites the one into the other with no
  adapter (`step5` below).
* **(B) `sha_endgame_of_nonempty` on `SelmerData` — MATCH, confirmed.** The five
  fields `ι`, `π`, `ι_inj`, `π_surj`, `mw_sha_exact` apply positionally with no
  adapter (`step8` below). This supersedes the never-written
  `Scratch/T27Check.lean` cited by `Kernel/ShaEndgame.lean`.
* **(C) `constantCoeff` vs `coeff 0` — minor, adapter needed.**
  `AnalyticData.interp` and `Kernel.FunctionalEquation.coeff_one_Lp_eq_zero`
  speak of `constantCoeff Lp`, whereas `Kernel.TsqUnit.*_of_coeffs` want
  `coeff 0 Lp`. One rewrite by `PowerSeries.coeff_zero_eq_constantCoeff_apply`
  bridges them (`step4` below).
* **(D) coinvariants collapse — gap found, closed here.**
  `selmer_dual_structure` returns `X ≃ₗ ℤ_p²` together with `∀ x, T • x = 0`,
  while `control` speaks about `X ⧸ T·X`. Turning the former into
  `SelDual ≃ₗ ℤ_p²` needs "`T` acts as `0` ⟹ `Ideal.span {T} • ⊤ = ⊥` ⟹
  `X ⧸ ⊥ ≃ₗ X`". No kernel file supplied it; proved below as
  `quotient_collapse`.
* **(E) rank lower bound — gap found, closed here.** `2 ≤ finrank ℤ_[p] SelDual`,
  the input to `selmer_dual_structure`'s `hrank`, must come from
  `SelmerData.π_surj` (`SelDual ↠ ℤ_p²`). No kernel lemma supplied it; proved
  below as `rank_lower_bound` from `LinearMap.finrank_le_finrank_of_surjective`.
  Note this is where the *certified Mordell–Weil rank 2* enters the chain.
* **(F) no circularity.** The `hrank` input to T23 is the corank-two *lower*
  bound coming from `SelmerData.π` (Mordell–Weil), not from the conclusion
  `finrank SelDual = 2`; the chain closes without assuming what it proves.
-/

open PowerSeries

namespace FinShaRank2
namespace T15Chain

variable {p : ℕ} [Fact p.Prime]

/-! ### The two sub-goals this test discovered were missing -/

/-- **(D)** The coinvariants collapse when `T` acts as zero on `X`: the
`Λ`-submodule `(T) • ⊤` is then `⊥`, and `M ⧸ ⊥ ≃ₗ M` restricted to `ℤ_[p]`.

Identified as a missing step by this chain test and proved here; T31 (or a kernel
task) should adopt it verbatim. -/
theorem quotient_collapse (M : Type) [AddCommGroup M] [Module (Λ p) M] [Module ℤ_[p] M]
    [IsScalarTower ℤ_[p] (Λ p) M] (hzero : ∀ x : M, (X : Λ p) • x = 0) :
    Nonempty ((M ⧸ (Ideal.span {(X : Λ p)} • (⊤ : Submodule (Λ p) M))) ≃ₗ[ℤ_[p]] M) := by
  have hbot : (Ideal.span {(X : Λ p)} • (⊤ : Submodule (Λ p) M)) = ⊥ := by
    refine le_antisymm (Submodule.smul_le.mpr ?_) bot_le
    intro r hr m _
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    rw [Submodule.mem_bot, mul_smul, hzero, smul_zero]
  exact ⟨(Submodule.quotEquivOfEqBot _ hbot).restrictScalars ℤ_[p]⟩

/-- **(E)** A surjection onto `ℤ_p²` forces `ℤ_[p]`-rank at least two — the input
to `selmer_dual_structure`'s `hrank`, supplied by `SelmerData.π_surj`.

Identified as a missing step by this chain test and proved here (mathlib's
`LinearMap.finrank_le_finrank_of_surjective` + `Module.finrank_fin_fun`); T31
should adopt it verbatim. -/
theorem rank_lower_bound {N : Type} [AddCommGroup N] [Module ℤ_[p] N] [Module.Finite ℤ_[p] N]
    (π : N →ₗ[ℤ_[p]] (Fin 2 → ℤ_[p])) (hπ : Function.Surjective π) :
    2 ≤ Module.finrank ℤ_[p] N := by
  have h := LinearMap.finrank_le_finrank_of_surjective (f := π) hπ
  rwa [Module.finrank_fin_fun] at h

/-! ### The end-to-end chain -/

/-- **The full `prop:consequence` chain, composed against the frozen interface.**

Statement **identical** to the frozen `FinShaRank2.prop_consequence`
(`Main/Consequence.lean`), and here fully proved by the real assembly. Every
interface field and kernel theorem is applied **verbatim**; the only adapter
needed anywhere is `coeff_zero_eq_constantCoeff_apply` (finding (C)), plus the
two auxiliaries above. T31 can lift this proof body unchanged. -/
theorem chain (H : ClassicalInputs) (hsplit : p % 4 = 1) (hpS : p ∉ H.S)
    (h5 : p = 5 → (H.dataAt p Fact.out hsplit hpS).analytic.ap = -2)
    (hc2 : IsPUnit (H.dataAt p Fact.out hsplit hpS).c2tilde) :
    MuZero (H.dataAt p Fact.out hsplit hpS).analytic.Lp
      ∧ lambdaAn (H.dataAt p Fact.out hsplit hpS).analytic.Lp = 2
      ∧ Module.finrank ℤ_[p] (H.dataAt p Fact.out hsplit hpS).selmer.SelDual = 2
      ∧ Subsingleton (H.dataAt p Fact.out hsplit hpS).selmer.ShaDual := by
  set D := H.dataAt p Fact.out hsplit hpS with hDdef
  -- **step 1** `rmk:normalisation`(i): the normalised jet is a unit iff `c₂` is.
  have step1 : IsUnit (coeff 2 D.analytic.Lp) :=
    (isPUnit_c2tilde_iff_of_split (coeff 2 D.analytic.Lp) H.torsSqOverTam hsplit
      D.analytic.hasse D.analytic.ap_from_CM D.analytic.alpha_root h5
      H.torsSqOverTam_eq).mp hc2
  -- **step 2** `lem:c0c1` first half: interpolation + the vanishing modular symbol.
  have step2 : constantCoeff D.analytic.Lp = 0 := by
    have h := D.analytic.interp
    rw [D.analytic.msymb_zero] at h
    simp only [Rat.cast_zero, mul_zero] at h
    exact PadicInt.coe_eq_zero.mp h
  -- **step 3** `lem:c0c1` second half: the MTT functional equation via T20.
  have step3 : coeff 1 D.analytic.Lp = 0 := by
    obtain ⟨U, _hUunit, hU0, hFE⟩ := D.analytic.funct_eq
    exact coeff_one_Lp_eq_zero D.analytic.Lp U hU0 hFE step2
  -- **step 4** T21: `Lp = T²·unit`, hence `μ = 0`, `λ = 2`, `Associated Lp T²`.
  --   (C) the one adapter in the whole chain: `constantCoeff` ↦ `coeff 0`.
  have step2' : coeff 0 D.analytic.Lp = 0 := by
    rw [coeff_zero_eq_constantCoeff_apply]; exact step2
  have hmu : MuZero D.analytic.Lp := muZero_of_coeffs step2' step3 step1
  have hlam : lambdaAn D.analytic.Lp = 2 := lambdaAn_eq_two_of_coeffs step2' step3 step1
  have hassocLp : Associated D.analytic.Lp ((X : Λ p) ^ 2) :=
    associated_X_sq_of_coeffs step2' step3 step1
  -- **step 5** (A) Mazur control transports the rank bound onto the T-coinvariants.
  have step5 : 2 ≤ Module.finrank ℤ_[p]
      (D.iwasawa.X ⧸ (Ideal.span {(X : Λ p)} • (⊤ : Submodule (Λ p) D.iwasawa.X))) := by
    rw [D.iwasawa.control.finrank_eq]
    exact rank_lower_bound D.selmer.π D.selmer.π_surj
  -- **step 6** Rubin ⊕ structure theorem, fed to T23.
  obtain ⟨n, f, φ, hker, hcok, hchar⟩ := D.iwasawa.rubin_structure
  obtain ⟨hTzero, hXfree⟩ :=
    selmer_dual_structure D.iwasawa.X D.iwasawa.no_finite_submodule φ hker hcok
      (hchar.trans hassocLp) step5
  -- **step 7** (D) collapse the coinvariants, then transport along `control`.
  have step7 : Nonempty (D.selmer.SelDual ≃ₗ[ℤ_[p]] (Fin 2 → ℤ_[p])) := by
    obtain ⟨e⟩ := hXfree
    obtain ⟨q⟩ := quotient_collapse D.iwasawa.X hTzero
    exact ⟨D.iwasawa.control.symm.trans (q.trans e)⟩
  -- **step 8** (B) T27 on `SelmerData`'s five exactness fields, verbatim.
  have step8 := sha_endgame_of_nonempty D.selmer.ι D.selmer.π D.selmer.ι_inj
    D.selmer.π_surj D.selmer.mw_sha_exact step7
  exact ⟨hmu, hlam, step8.2, step8.1⟩

end T15Chain
end FinShaRank2

namespace FinShaRank2
namespace T15Chain

/-! ### The anchor-corollary path: `Certificates` ⟹ the frozen `cor_sha5` shape

Validates that the frozen `cor_sha5` / `cor_sha13` statements of
`Main/Corollaries.lean` are reachable from `H` and `C` alone (no conjectural
input), and that `Certificates`' `(by norm_num)` witnesses compose with
`chain`'s `Fact.out` witness (proof irrelevance).
-/

/-- `cor:sha5`, frozen shape, proved from `H` + `C` via `chain`. -/
theorem cor5 (H : ClassicalInputs) (C : Certificates H) :
    Module.finrank ℤ_[5]
        (H.dataAt 5 (by norm_num) (by norm_num) C.five_notin).selmer.SelDual = 2
      ∧ Subsingleton (H.dataAt 5 (by norm_num) (by norm_num) C.five_notin).selmer.ShaDual
      ∧ MuZero (H.dataAt 5 (by norm_num) (by norm_num) C.five_notin).analytic.Lp
      ∧ lambdaAn (H.dataAt 5 (by norm_num) (by norm_num) C.five_notin).analytic.Lp = 2 := by
  set D := H.dataAt 5 (by norm_num) (by norm_num) C.five_notin with hD
  have hunit : IsUnit (coeff 2 D.analytic.Lp) := isUnit_of_cert_five C.c2_5
  have hc2 : IsPUnit D.c2tilde :=
    (isPUnit_c2tilde_iff_of_split (coeff 2 D.analytic.Lp) H.torsSqOverTam (by norm_num)
      D.analytic.hasse D.analytic.ap_from_CM D.analytic.alpha_root (fun _ => C.a5)
      H.torsSqOverTam_eq).mpr hunit
  obtain ⟨hmu, hlam, hrk, hsha⟩ :=
    chain (p := 5) H (by norm_num) C.five_notin (fun _ => C.a5) hc2
  exact ⟨hrk, hsha, hmu, hlam⟩

/-- `cor:sha13`, frozen shape, proved from `H` + `C` via `chain`; here the
residual `h5` hypothesis is vacuous. -/
theorem cor13 (H : ClassicalInputs) (C : Certificates H) :
    Module.finrank ℤ_[13]
        (H.dataAt 13 (by norm_num) (by norm_num) C.thirteen_notin).selmer.SelDual = 2
      ∧ Subsingleton (H.dataAt 13 (by norm_num) (by norm_num) C.thirteen_notin).selmer.ShaDual
      ∧ MuZero (H.dataAt 13 (by norm_num) (by norm_num) C.thirteen_notin).analytic.Lp
      ∧ lambdaAn (H.dataAt 13 (by norm_num) (by norm_num) C.thirteen_notin).analytic.Lp = 2 := by
  set D := H.dataAt 13 (by norm_num) (by norm_num) C.thirteen_notin with hD
  have hunit : IsUnit (coeff 2 D.analytic.Lp) := isUnit_of_cert_thirteen C.c2_13
  have hvac : (13 : ℕ) = 5 → D.analytic.ap = -2 := fun h => absurd h (by norm_num)
  have hc2 : IsPUnit D.c2tilde :=
    (isPUnit_c2tilde_iff_of_split (coeff 2 D.analytic.Lp) H.torsSqOverTam (by norm_num)
      D.analytic.hasse D.analytic.ap_from_CM D.analytic.alpha_root hvac
      H.torsSqOverTam_eq).mpr hunit
  obtain ⟨hmu, hlam, hrk, hsha⟩ :=
    chain (p := 13) H (by norm_num) C.thirteen_notin hvac hc2
  exact ⟨hrk, hsha, hmu, hlam⟩

end T15Chain
end FinShaRank2

-- Axiom hygiene checks: each prints `[propext, Classical.choice, Quot.sound]`.
#print axioms FinShaRank2.T15Chain.chain
#print axioms FinShaRank2.T15Chain.cor5
#print axioms FinShaRank2.T15Chain.cor13
