import Mathlib
import FinShaRank2.Defs

/-! T23 scratch — develop `selmer_dual_structure` here, then lift to Kernel/. -/

open PowerSeries

namespace FinShaRank2

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-! ### (a) Primality of X and structure of `Λ ⧸ (Xᵏ)` -/

/-- Divisibility of `X`-powers is monotone in the exponent. -/
lemma pow_X_dvd_le {a b : ℕ} (h : (X : Λ p) ^ a ∣ (X : Λ p) ^ b) : a ≤ b := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨c, hc⟩ := h
  have hXne : (X : Λ p) ≠ 0 := X_prime.ne_zero
  have key : (X : Λ p) ^ b * 1 = (X : Λ p) ^ b * ((X : Λ p) ^ (a - b) * c) := by
    rw [mul_one, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' (le_of_lt hlt), hc]
  have h1 : (1 : Λ p) = (X : Λ p) ^ (a - b) * c := mul_left_cancel₀ (pow_ne_zero b hXne) key
  have hunit : IsUnit ((X : Λ p) ^ (a - b)) := IsUnit.of_mul_eq_one _ h1.symm
  have hge : 1 ≤ a - b := by omega
  rw [← Nat.sub_add_cancel hge, pow_succ] at hunit
  exact X_prime.not_unit (isUnit_of_mul_isUnit_right hunit)

/-- `X`-powers are exponent-injective up to associates in the domain `Λ`. -/
lemma associated_X_pow_inj {a b : ℕ}
    (h : Associated ((X : Λ p) ^ a) ((X : Λ p) ^ b)) : a = b :=
  le_antisymm (pow_X_dvd_le h.dvd) (pow_X_dvd_le h.symm.dvd)

/-- `Λ ⧸ (Xᵏ)` is `ℤ_[p]`-linearly the free module `Fin k → ℤ_[p]`,
via the first `k` coefficients. -/
lemma quotXpow_linEquiv (k : ℕ) :
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
    ext f
    constructor
    · intro hf
      rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
      intro m hm
      have := congrFun (LinearMap.mem_ker.mp hf) ⟨m, hm⟩
      simpa [hψ, LinearMap.pi_apply] using this
    · intro hf
      rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at hf
      rw [LinearMap.mem_ker]
      funext j
      simpa [hψ, LinearMap.pi_apply] using hf (j : ℕ) j.isLt
  exact ⟨(Submodule.Quotient.restrictScalarsEquiv ℤ_[p] (Ideal.span {(X : Λ p) ^ k})).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans (LinearMap.quotKerEquivOfSurjective ψ hsurj))⟩

/-- A divisor of `X²` gives a quotient `Λ ⧸ (g)` that is `ℤ_[p]`-free of some rank `k ≤ 2`,
recording the associate. -/
lemma quotSpan_of_dvd_Xsq (g : Λ p) (hg : g ∣ (X : Λ p) ^ 2) :
    ∃ k, k ≤ 2 ∧ Associated g ((X : Λ p) ^ k) ∧
      Nonempty ((Λ p ⧸ Ideal.span {g}) ≃ₗ[ℤ_[p]] (Fin k → ℤ_[p])) := by
  obtain ⟨k, hk, hassoc⟩ := (dvd_prime_pow X_prime 2).mp hg
  refine ⟨k, hk, hassoc, ?_⟩
  have hspan : Ideal.span {g} = Ideal.span {(X : Λ p) ^ k} :=
    (Ideal.span_singleton_eq_span_singleton).mpr hassoc
  obtain ⟨e⟩ := quotXpow_linEquiv (p := p) k
  exact ⟨((Submodule.quotEquivOfEq _ _ hspan).restrictScalars ℤ_[p]).trans e⟩

/-! ### Main theorem -/

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
  -- Per-factor structure.
  choose k hk hassoc hequiv using fun i => quotSpan_of_dvd_Xsq (f i) (hdvd i)
  have ei : ∀ i, (Λ p ⧸ Ideal.span {f i}) ≃ₗ[ℤ_[p]] (Fin (k i) → ℤ_[p]) := fun i => (hequiv i).some
  haveI free_i : ∀ i, Module.Free ℤ_[p] (Λ p ⧸ Ideal.span {f i}) := fun i =>
    Module.Free.of_equiv (ei i).symm
  haveI fin_i : ∀ i, Module.Finite ℤ_[p] (Λ p ⧸ Ideal.span {f i}) := fun i =>
    Module.Finite.equiv (ei i).symm
  haveI nz_i : ∀ i, NoZeroSMulDivisors ℤ_[p] (Λ p ⧸ Ideal.span {f i}) := fun i =>
    Function.Injective.noZeroSMulDivisors (ei i) (ei i).injective (map_zero _)
      (fun c x => map_smul _ c x)
  haveI : Module.Free ℤ_[p] (Π i, (Λ p) ⧸ Ideal.span {f i}) := inferInstance
  haveI : NoZeroSMulDivisors ℤ_[p] (Π i, (Λ p) ⧸ Ideal.span {f i}) := inferInstance
  haveI : Module.Finite ℤ_[p] (Π i, (Λ p) ⧸ Ideal.span {f i}) := inferInstance
  -- `∑ k i = 2`.
  have hsum : (∑ i, k i) = 2 := by
    have h1 : Associated (∏ i, f i) (∏ i, (X : Λ p) ^ (k i)) :=
      Associated.prod Finset.univ f (fun i => (X : Λ p) ^ (k i)) (fun i _ => hassoc i)
    rw [Finset.prod_pow_eq_pow_sum] at h1
    exact associated_X_pow_inj (h1.symm.trans hchar)
  -- `finrank C = 2`.
  have hCfin2 : Module.finrank ℤ_[p] (Π i, (Λ p) ⧸ Ideal.span {f i}) = 2 := by
    rw [Module.finrank_pi_fintype]
    rw [show (∑ i, Module.finrank ℤ_[p] (Λ p ⧸ Ideal.span {f i})) = ∑ i, k i from
      Finset.sum_congr rfl (fun i _ => by
        rw [LinearEquiv.finrank_eq (ei i), Module.finrank_fin_fun])]
    exact hsum
  -- (d) `φ` is injective.
  have hinj : Function.Injective φ :=
    LinearMap.ker_eq_bot.mp (hnofin _ hker)
  set φ' : X_mod →ₗ[ℤ_[p]] (Π i, (Λ p) ⧸ Ideal.span {f i}) := φ.restrictScalars ℤ_[p] with hφ'
  have hinj' : Function.Injective φ' := by rw [hφ', LinearMap.coe_restrictScalars]; exact hinj
  -- `X_mod` is `ℤ_[p]`-finite, torsion-free hence free.
  haveI : IsNoetherian ℤ_[p] (Π i, (Λ p) ⧸ Ideal.span {f i}) := inferInstance
  haveI : Module.Finite ℤ_[p] X_mod := Module.Finite.of_injective φ' hinj'
  haveI : NoZeroSMulDivisors ℤ_[p] X_mod :=
    Function.Injective.noZeroSMulDivisors φ' hinj' (map_zero φ') (fun c x => map_smul φ' c x)
  haveI : Module.Free ℤ_[p] X_mod := inferInstance
  -- Upper bound: `finrank X_mod ≤ 2`.
  have hle : Module.finrank ℤ_[p] X_mod ≤ 2 := by
    rw [← LinearMap.finrank_range_of_inj hinj', ← hCfin2]
    exact Submodule.finrank_le _
  -- Convert the coinvariants hypothesis to a `ℤ_[p]`-submodule quotient.
  set TX : Submodule (Λ p) X_mod := Ideal.span {(X : Λ p)} • (⊤ : Submodule (Λ p) X_mod) with hTX
  set TXℤ : Submodule ℤ_[p] X_mod := TX.restrictScalars ℤ_[p] with hTXℤ
  have hconv : Module.finrank ℤ_[p] (X_mod ⧸ TX) = Module.finrank ℤ_[p] (X_mod ⧸ TXℤ) :=
    (LinearEquiv.finrank_eq (Submodule.Quotient.restrictScalarsEquiv ℤ_[p] TX)).symm
  have hrank' : 2 ≤ Module.finrank ℤ_[p] (X_mod ⧸ TXℤ) := by rw [← hconv]; exact hrank
  -- Lower bound: `finrank X_mod ≥ 2`.
  have hge : 2 ≤ Module.finrank ℤ_[p] X_mod :=
    hrank'.trans (Submodule.finrank_quotient_le TXℤ)
  have hXrank : Module.finrank ℤ_[p] X_mod = 2 := le_antisymm hle hge
  refine ⟨?_, ⟨(Module.finBasisOfFinrankEq ℤ_[p] X_mod hXrank).equivFun⟩⟩
  -- Conclusion 1: the `X`-action vanishes.
  have hrn : Module.finrank ℤ_[p] (X_mod ⧸ TXℤ) + Module.finrank ℤ_[p] TXℤ =
      Module.finrank ℤ_[p] X_mod := Submodule.finrank_quotient_add_finrank TXℤ
  have hTXℤ0 : Module.finrank ℤ_[p] TXℤ = 0 := by omega
  have hbot : TXℤ = ⊥ := Submodule.finrank_eq_zero.mp hTXℤ0
  have hTXbot : TX = ⊥ := by
    have : TX.restrictScalars ℤ_[p] = (⊥ : Submodule (Λ p) X_mod).restrictScalars ℤ_[p] := by
      rw [← hTXℤ]; simpa using hbot
    exact Submodule.restrictScalars_injective ℤ_[p] _ _ this
  intro x
  have hmem : (X : Λ p) • x ∈ TX :=
    Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  rw [hTXbot] at hmem
  simpa using hmem

end

end FinShaRank2
