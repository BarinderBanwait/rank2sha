import Mathlib
import FinShaRank2.Defs

/-!
# Λ-module structure kernel (task T23)

This file proves, as pure `mathlib`-only algebra, Steps 3–4 of the paper's
`prop:consequence`: the structural core of the passage from the fused
Rubin ⊕ structure-theorem datum on the Selmer dual `X` to the two facts the
Sha endgame consumes — that the cyclotomic variable acts as zero on `X`, and
that `X` is `ℤ_[p]`-free of rank two.

The main deliverable is `FinShaRank2.selmer_dual_structure`. Two small auxiliaries
that the T15 chain test (`TASK_BOARD.md` T15, findings (D) and (E)) identified as
missing links between this file's output and the neighbouring interface fields are
supplied alongside it: `FinShaRank2.quotient_collapse` and
`FinShaRank2.rank_lower_bound` (final section).

## Internal split (paper `prop:consequence` Steps 3–4)

* **(a)** `PowerSeries.X` is prime in `Λ` (`PowerSeries.X_prime`), and the
  quotients `Λ ⧸ (Xᵏ)` are `ℤ_[p]`-linearly the free modules `Fin k → ℤ_[p]`
  via the first `k` coefficients (`quotXpow_linEquiv`). No Weierstrass
  preparation is used.
* **(b)** From `Associated (∏ i, f i) (X²)` in the domain `Λ`: every factor
  `f i` divides `X²`, hence — by primality and cancellation alone
  (`dvd_prime_pow`, no UFD / pseudo-isomorphism / characteristic-ideal theory)
  — is associate to `X^{kᵢ}` with `kᵢ ≤ 2` and `∑ kᵢ = 2`
  (`quotSpan_of_dvd_Xsq`, `associated_X_pow_inj`).
* **(c)** Consequently the codomain `C := Π i, Λ ⧸ (f i)` is `ℤ_[p]`-free,
  finite, of rank `∑ kᵢ = 2` (`Module.finrank_pi_fintype`).
* **(d)** `LinearMap.ker φ` is finite (`hker`) hence `⊥` (`hnofin`), so `φ` is
  injective; `X` therefore embeds `ℤ_[p]`-linearly into the free rank-2 module
  `C`, forcing `X` finite, torsion-free and hence free with
  `finrank ℤ_[p] X ≤ 2`. The coinvariants hypothesis `hrank` gives the matching
  lower bound `finrank ℤ_[p] X ≥ 2` (a quotient of `X`), so `finrank ℤ_[p] X = 2`
  and rank–nullity on the coinvariants submodule forces the `X`-action to vanish.

## Coinvariants formulation (the T12 / T15 contract)

The hypothesis `hrank` is stated with the **T-coinvariants** submodule in the
`Ideal.span`-smul form
```
X ⧸ (Ideal.span {(PowerSeries.X : Λ p)} • (⊤ : Submodule (Λ p) X))
```
with the `ℤ_[p]`-module structure on the quotient inferred through the scalar
tower `[Module ℤ_[p] X] [IsScalarTower ℤ_[p] (Λ p) X]`. This is **the identical
term** used by task T12's `control` field, so `selmer_dual_structure` composes
against `IwasawaData.control` with no bridge lemma required at T15.

## Note on `_hcok`

The finite-cokernel hypothesis `_hcok` (the surjectivity half of the Rubin
pseudo-isomorphism) is kept in the signature for faithfulness to the interface,
but is **not needed** for this conclusion: the coinvariants lower bound already
pins `finrank ℤ_[p] X = 2`, so the embedding `X ↪ C` alone suffices. The result
is therefore proved from strictly weaker hypotheses than the paper states.
-/

open PowerSeries

namespace FinShaRank2

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-! ### (a) Primality of `X` and the structure of `Λ ⧸ (Xᵏ)` -/

/-- Divisibility of `X`-powers in `Λ` is monotone in the exponent. -/
private lemma pow_X_dvd_le {a b : ℕ} (h : (X : Λ p) ^ a ∣ (X : Λ p) ^ b) : a ≤ b :=
  (pow_dvd_pow_iff X_prime.ne_zero X_prime.not_isUnit).mp h

/-- `X`-powers in the domain `Λ` are exponent-injective up to associates. -/
private lemma associated_X_pow_inj {a b : ℕ}
    (h : Associated ((X : Λ p) ^ a) ((X : Λ p) ^ b)) : a = b :=
  le_antisymm (pow_X_dvd_le h.dvd) (pow_X_dvd_le h.symm.dvd)

/-- The quotient `Λ ⧸ (Xᵏ)` is `ℤ_[p]`-linearly isomorphic to the free module
`Fin k → ℤ_[p]`, via the first `k` coefficients. -/
private lemma quotXpow_linEquiv (k : ℕ) :
    Nonempty ((Λ p ⧸ Ideal.span {(X : Λ p) ^ k}) ≃ₗ[ℤ_[p]] (Fin k → ℤ_[p])) := by
  set ψ : Λ p →ₗ[ℤ_[p]] (Fin k → ℤ_[p]) :=
    LinearMap.pi (fun i : Fin k => PowerSeries.coeff (i : ℕ)) with hψ
  have hsurj : Function.Surjective ψ := by
    intro v
    refine ⟨∑ i : Fin k, PowerSeries.C (v i) * (X : Λ p) ^ (i : ℕ), ?_⟩
    funext j
    simp only [hψ, LinearMap.pi_apply, map_sum, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    rw [Fintype.sum_eq_single j (fun i hij => by
      rw [if_neg (fun hh => hij (Fin.val_inj.mp hh).symm), mul_zero])]
    simp
  have hker : LinearMap.ker ψ = (Ideal.span {(X : Λ p) ^ k}).restrictScalars ℤ_[p] := by
    ext g
    rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, Ideal.mem_span_singleton,
      PowerSeries.X_pow_dvd_iff]
    constructor
    · intro hg m hm
      simpa [hψ, LinearMap.pi_apply] using congrFun hg ⟨m, hm⟩
    · intro hg
      funext j
      simpa [hψ, LinearMap.pi_apply] using hg (j : ℕ) j.isLt
  exact ⟨(Submodule.Quotient.restrictScalarsEquiv ℤ_[p] (Ideal.span {(X : Λ p) ^ k})).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans (LinearMap.quotKerEquivOfSurjective ψ hsurj))⟩

/-- A divisor of `X²` in `Λ` is associate to a power `X^{k}` with `k ≤ 2`, and the
corresponding quotient `Λ ⧸ (g)` is `ℤ_[p]`-linearly the free module `Fin k → ℤ_[p]`. -/
private lemma quotSpan_of_dvd_Xsq (g : Λ p) (hg : g ∣ (X : Λ p) ^ 2) :
    ∃ k, k ≤ 2 ∧ Associated g ((X : Λ p) ^ k) ∧
      Nonempty ((Λ p ⧸ Ideal.span {g}) ≃ₗ[ℤ_[p]] (Fin k → ℤ_[p])) := by
  obtain ⟨k, hk, hassoc⟩ := (dvd_prime_pow X_prime 2).mp hg
  refine ⟨k, hk, hassoc, ?_⟩
  have hspan : Ideal.span {g} = Ideal.span {(X : Λ p) ^ k} :=
    (Ideal.span_singleton_eq_span_singleton).mpr hassoc
  obtain ⟨e⟩ := quotXpow_linEquiv (p := p) k
  exact ⟨((Submodule.quotEquivOfEq _ _ hspan).restrictScalars ℤ_[p]).trans e⟩

/-! ### Main structure theorem (`prop:consequence` Steps 3–4) -/

/-- **T23.** Steps 3–4 of `prop:consequence` as pure algebra.

Given a finitely generated `Λ`-module `X` (the Selmer dual) with no nonzero
finite `Λ`-submodule (`hnofin`, Greenberg), a Rubin ⊕ structure-theorem map
`φ : X → Π i, Λ ⧸ (f i)` with finite kernel (`hker`) and finite cokernel
(`_hcok`), characteristic product `Associated (∏ i, f i) (X²)` (`hchar`, from the
`X²`-unit factorisation of `L_p`), and a rank-two lower bound on the
T-coinvariants (`hrank`, Mazur control), the cyclotomic variable `X` acts as zero
on `X` and `X` is `ℤ_[p]`-free of rank two.

The T-coinvariants quotient in `hrank` uses the `Ideal.span`-smul form, matching
task T12's `control` field verbatim (see the module docstring). -/
theorem selmer_dual_structure
    (X_mod : Type) [AddCommGroup X_mod] [Module (Λ p) X_mod] [Module.Finite (Λ p) X_mod]
    [Module ℤ_[p] X_mod] [IsScalarTower ℤ_[p] (Λ p) X_mod]
    (hnofin : ∀ N : Submodule (Λ p) X_mod, Finite N → N = ⊥)
    {n : ℕ} {f : Fin n → Λ p}
    (φ : X_mod →ₗ[Λ p] Π i, (Λ p) ⧸ Ideal.span {f i})
    (hker : Finite (LinearMap.ker φ))
    (_hcok : Finite ((Π i, (Λ p) ⧸ Ideal.span {f i}) ⧸ LinearMap.range φ))
    (hchar : Associated (∏ i, f i) ((X : Λ p) ^ 2))
    (hrank : 2 ≤ Module.finrank ℤ_[p]
      (X_mod ⧸ (Ideal.span {(X : Λ p)} • (⊤ : Submodule (Λ p) X_mod)))) :
    (∀ x : X_mod, (X : Λ p) • x = 0) ∧
      Nonempty (X_mod ≃ₗ[ℤ_[p]] (Fin 2 → ℤ_[p])) := by
  -- Each factor divides `X²`.
  have hdvd : ∀ i, f i ∣ (X : Λ p) ^ 2 := fun i =>
    (Finset.dvd_prod_of_mem f (Finset.mem_univ i)).trans hchar.dvd
  -- Per-factor structure: `Λ ⧸ (f i) ≃ Fin (k i) → ℤ_[p]`, `f i ~ X^{k i}`, `k i ≤ 2`.
  choose k hk hassoc hequiv using fun i => quotSpan_of_dvd_Xsq (f i) (hdvd i)
  have ei : ∀ i, (Λ p ⧸ Ideal.span {f i}) ≃ₗ[ℤ_[p]] (Fin (k i) → ℤ_[p]) := fun i => (hequiv i).some
  have free_i : ∀ i, Module.Free ℤ_[p] (Λ p ⧸ Ideal.span {f i}) := fun i =>
    Module.Free.of_equiv (ei i).symm
  have fin_i : ∀ i, Module.Finite ℤ_[p] (Λ p ⧸ Ideal.span {f i}) := fun i =>
    Module.Finite.equiv (ei i).symm
  have nz_i : ∀ i, NoZeroSMulDivisors ℤ_[p] (Λ p ⧸ Ideal.span {f i}) := fun i =>
    Function.Injective.noZeroSMulDivisors (ei i) (ei i).injective (map_zero _) (map_smul (ei i))
  -- (b) `∑ k i = 2` from `∏ f i ~ X²` (primality + cancellation only).
  have hsum : (∑ i, k i) = 2 := by
    have h1 : Associated (∏ i, f i) (∏ i, (X : Λ p) ^ (k i)) :=
      Associated.prod Finset.univ f (fun i => (X : Λ p) ^ (k i)) (fun i _ => hassoc i)
    rw [Finset.prod_pow_eq_pow_sum] at h1
    exact associated_X_pow_inj (h1.symm.trans hchar)
  -- (c) `finrank ℤ_[p] C = ∑ k i = 2`.
  have hCfin2 : Module.finrank ℤ_[p] (Π i, (Λ p) ⧸ Ideal.span {f i}) = 2 := by
    rw [Module.finrank_pi_fintype, ← hsum]
    exact Finset.sum_congr rfl fun i _ =>
      (LinearEquiv.finrank_eq (ei i)).trans (Module.finrank_fin_fun ℤ_[p])
  -- (d) `φ` injective from `hker` + `hnofin`.
  have hinj : Function.Injective φ :=
    LinearMap.ker_eq_bot.mp (hnofin _ hker)
  set φ' : X_mod →ₗ[ℤ_[p]] (Π i, (Λ p) ⧸ Ideal.span {f i}) := φ.restrictScalars ℤ_[p] with hφ'
  have hinj' : Function.Injective φ' := hinj
  -- `X` is `ℤ_[p]`-finite (embeds in the Noetherian `C`), torsion-free, hence free.
  have : Module.Finite ℤ_[p] X_mod := Module.Finite.of_injective φ' hinj'
  have : NoZeroSMulDivisors ℤ_[p] X_mod :=
    Function.Injective.noZeroSMulDivisors φ' hinj' (map_zero φ') (map_smul φ')
  have : Module.Free ℤ_[p] X_mod := inferInstance
  -- Upper bound `finrank ℤ_[p] X ≤ 2` from the embedding into `C`.
  have hle : Module.finrank ℤ_[p] X_mod ≤ 2 := by
    rw [← LinearMap.finrank_range_of_inj hinj', ← hCfin2]
    exact Submodule.finrank_le _
  -- Convert `hrank` to a `ℤ_[p]`-submodule quotient via `restrictScalars`.
  set TX : Submodule (Λ p) X_mod := Ideal.span {(X : Λ p)} • (⊤ : Submodule (Λ p) X_mod) with hTX
  set TXℤ : Submodule ℤ_[p] X_mod := TX.restrictScalars ℤ_[p] with hTXℤ
  have hconv : Module.finrank ℤ_[p] (X_mod ⧸ TX) = Module.finrank ℤ_[p] (X_mod ⧸ TXℤ) :=
    (LinearEquiv.finrank_eq (Submodule.Quotient.restrictScalarsEquiv ℤ_[p] TX)).symm
  have hrank' : 2 ≤ Module.finrank ℤ_[p] (X_mod ⧸ TXℤ) := hconv ▸ hrank
  -- Lower bound `finrank ℤ_[p] X ≥ 2` from the coinvariants.
  have hge : 2 ≤ Module.finrank ℤ_[p] X_mod :=
    hrank'.trans (Submodule.finrank_quotient_le TXℤ)
  have hXrank : Module.finrank ℤ_[p] X_mod = 2 := le_antisymm hle hge
  refine ⟨?_, ⟨(Module.finBasisOfFinrankEq ℤ_[p] X_mod hXrank).equivFun⟩⟩
  -- Conclusion 1: rank–nullity on `TXℤ` forces the `X`-action to vanish.
  have hrn : Module.finrank ℤ_[p] (X_mod ⧸ TXℤ) + Module.finrank ℤ_[p] TXℤ =
      Module.finrank ℤ_[p] X_mod := Submodule.finrank_quotient_add_finrank TXℤ
  have hTXℤ0 : Module.finrank ℤ_[p] TXℤ = 0 := by omega
  have hbot : TXℤ = ⊥ := Submodule.finrank_eq_zero.mp hTXℤ0
  intro x
  have hmem : (X : Λ p) • x ∈ TXℤ := by
    rw [hTXℤ, Submodule.restrictScalars_mem]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  rw [hbot] at hmem
  simpa using hmem

/-! ### Auxiliaries flanking the structure theorem (T15 chain-test findings (D), (E))

Both statements below are pure `mathlib` algebra; they mention no interface field.
They were isolated by the T15 pre-freeze chain test as the two steps that no kernel
file supplied when `selmer_dual_structure` is composed with task T12's `control`
equivalence on one side and task T27's Sha endgame on the other. They are stated
here in the exact shape that composition needs. -/

/-- **T15 finding (D) — collapse of the `T`-coinvariants.**

If the cyclotomic variable `X` acts as zero on `M` — which is precisely the first
conclusion of `selmer_dual_structure` — then the `Λ`-submodule
`(X) • ⊤` is `⊥`, so the coinvariants quotient `M ⧸ (X) • ⊤` is `ℤ_[p]`-linearly
just `M`.

This is the bridge from `selmer_dual_structure`'s output, which describes `M`
itself, to task T12's `control` field, whose domain is the coinvariants quotient in
the `Ideal.span`-smul form fixed by the T15 contract (see the module docstring).
The `ℤ_[p]`-structure on the quotient is inferred through the scalar tower, and the
equivalence is obtained by restricting scalars along `ℤ_[p] → Λ p`.

TRANSLATION: `T` of the paper ↦ `PowerSeries.X : Λ p`; "`T` kills `X`" ↦ `hzero`. -/
theorem quotient_collapse (M : Type) [AddCommGroup M] [Module (Λ p) M] [Module ℤ_[p] M]
    [IsScalarTower ℤ_[p] (Λ p) M] (hzero : ∀ x : M, (X : Λ p) • x = 0) :
    Nonempty ((M ⧸ (Ideal.span {(X : Λ p)} • (⊤ : Submodule (Λ p) M))) ≃ₗ[ℤ_[p]] M) := by
  have hbot : (Ideal.span {(X : Λ p)} • (⊤ : Submodule (Λ p) M)) = ⊥ := by
    refine le_antisymm (Submodule.smul_le.mpr fun r hr m _ => ?_) bot_le
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    rw [Submodule.mem_bot, mul_smul, hzero, smul_zero]
  exact ⟨(Submodule.quotEquivOfEqBot _ hbot).restrictScalars ℤ_[p]⟩

/-- **T15 finding (E) — the rank-two lower bound from a surjection onto `ℤ_[p]²`.**

A `ℤ_[p]`-linear surjection `N ↠ (Fin 2 → ℤ_[p])` forces `2 ≤ finrank ℤ_[p] N`
(`LinearMap.finrank_le_finrank_of_surjective` together with
`Module.finrank_fin_fun`).

This supplies the `hrank` hypothesis of `selmer_dual_structure` after transport
along `control`: the surjection is task T25's `SelmerData.π_surj`, so this lemma is
where the certified Mordell–Weil rank two enters the chain. Note the direction — the
bound is a hypothesis of the structure theorem, not a consequence of it, so no
circularity arises (T15 finding (F)).

TRANSLATION: `corank_{ℤ_p} Sel_{p^∞} ≥ 2` ↦ `2 ≤ Module.finrank ℤ_[p] N` on the dual
side (`TASK_BOARD.md` §2 conv. 1). -/
theorem rank_lower_bound {N : Type} [AddCommGroup N] [Module ℤ_[p] N] [Module.Finite ℤ_[p] N]
    (π : N →ₗ[ℤ_[p]] (Fin 2 → ℤ_[p])) (hπ : Function.Surjective π) :
    2 ≤ Module.finrank ℤ_[p] N :=
  (Module.finrank_fin_fun ℤ_[p]).symm.trans_le (LinearMap.finrank_le_finrank_of_surjective hπ)

end

end FinShaRank2
