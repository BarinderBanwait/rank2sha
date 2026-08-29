import FinShaRank2.Interface.Iwasawa

/-!
# Toy Iwasawa / descent layers (task T40): `Toy.toySelmer`, `Toy.toyIwasawa`

The Λ-module and descent layers of the non-vacuity instance (`TASK_BOARD.md`
§1). The toy world takes

* `X := (Λ/(X))²` — the Iwasawa module, on which `T = PowerSeries.X` acts as
  zero, so its Γ-coinvariants are `X` itself;
* `SelDual := ℤ_[p]²`, `ShaDual := PUnit` — a trivial Ш, so the descent
  sequence is `0 → 0 → ℤ_[p]² → ℤ_[p]² → 0`.

The single piece of real work is the `ℤ_[p]`-linear identification
`Λ/(X) ≃ ℤ_[p]` (`Toy.quotXEquiv`, the constant-coefficient map), which serves
both the control isomorphism and the torsion-freeness behind
`no_finite_submodule`. `rubin_structure` is then the identity map with
`n = 2`, `fᵢ = X`, so `∏ᵢ fᵢ = X² = Lp` on the nose.
-/

open PowerSeries

namespace FinShaRank2

namespace Toy

variable {p : ℕ} [Fact p.Prime]

/-! ### `Λ/(X) ≃ ℤ_[p]` -/

/-- The kernel of `coeff 0 : Λ →ₗ[ℤ_[p]] ℤ_[p]` is the ideal `(X)`. -/
theorem ker_coeff_zero :
    LinearMap.ker (PowerSeries.coeff 0 : Λ p →ₗ[ℤ_[p]] ℤ_[p])
      = (Ideal.span {(X : Λ p)}).restrictScalars ℤ_[p] := by
  ext g
  rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, Ideal.mem_span_singleton,
    PowerSeries.X_dvd_iff, coeff_zero_eq_constantCoeff_apply]

/-- `coeff 0` is surjective (`C` is a section). -/
theorem surjective_coeff_zero :
    Function.Surjective (PowerSeries.coeff 0 : Λ p →ₗ[ℤ_[p]] ℤ_[p]) :=
  fun r => ⟨PowerSeries.C r, by simp⟩

/-- **`Λ/(X) ≃ ℤ_[p]`**, `ℤ_[p]`-linearly, via the constant coefficient. -/
noncomputable def quotXEquiv (p : ℕ) [Fact p.Prime] :
    (Λ p ⧸ Ideal.span {(X : Λ p)}) ≃ₗ[ℤ_[p]] ℤ_[p] :=
  (Submodule.Quotient.restrictScalarsEquiv ℤ_[p] (Ideal.span {(X : Λ p)})).symm.trans
    ((Submodule.quotEquivOfEq _ _ ker_coeff_zero.symm).trans
      (LinearMap.quotKerEquivOfSurjective _ surjective_coeff_zero))

/-! ### The toy Iwasawa module `X = (Λ/(X))²` -/

/-- The toy Iwasawa module `X = (Λ/(X))²` (dual side). `T = PowerSeries.X` acts
as zero on it. -/
abbrev ToyX (p : ℕ) [Fact p.Prime] : Type := Fin 2 → (Λ p ⧸ Ideal.span {(X : Λ p)})

/-- `ℤ_[p]`-linear identification `X = (Λ/(X))² ≃ ℤ_[p]²`. -/
noncomputable def toyXEquiv (p : ℕ) [Fact p.Prime] : ToyX p ≃ₗ[ℤ_[p]] (Fin 2 → ℤ_[p]) :=
  LinearEquiv.piCongrRight fun _ => quotXEquiv p

/-- Elements of `(X)` annihilate `Λ/(X)`. -/
theorem smul_quotX_eq_zero {r : Λ p} (hr : r ∈ Ideal.span {(X : Λ p)})
    (q : Λ p ⧸ Ideal.span {(X : Λ p)}) : r • q = 0 := by
  obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective (Ideal.span {(X : Λ p)}) q
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
  exact Ideal.mul_mem_right g _ hr

/-- **The Γ-coinvariants of the toy module are everything**: `T · X = 0`, i.e.
`Ideal.span {T} • ⊤ = ⊥`. -/
theorem span_X_smul_top_eq_bot :
    Ideal.span {(X : Λ p)} • (⊤ : Submodule (Λ p) (ToyX p)) = ⊥ := by
  rw [eq_bot_iff, Submodule.smul_le]
  intro r hr n _
  rw [Submodule.mem_bot]
  funext i
  exact smul_quotX_eq_zero hr (n i)

/-- **No nonzero finite Λ-submodule** (Greenberg's input, here a theorem): the
toy module is `ℤ_[p]`-torsion-free, so any submodule containing a nonzero element
contains the infinitely many multiples `n · x`, hence cannot be finite. -/
theorem toy_no_finite_submodule (N : Submodule (Λ p) (ToyX p)) (hN : Finite N) : N = ⊥ := by
  by_contra hne
  obtain ⟨x, hxN, hx0⟩ := (Submodule.ne_bot_iff N).mp hne
  have hx' : toyXEquiv p x ≠ 0 := fun h => hx0 ((toyXEquiv p).map_eq_zero_iff.mp h)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx'
  rw [Pi.zero_apply] at hi
  have hinj : Function.Injective (fun k : ℕ => (⟨(k : Λ p) • x, N.smul_mem _ hxN⟩ : N)) := by
    intro k l hkl
    have h1 : (k : ℕ) • x = (l : ℕ) • x := by
      rw [← Nat.cast_smul_eq_nsmul (Λ p) k x, ← Nat.cast_smul_eq_nsmul (Λ p) l x]
      exact congrArg Subtype.val hkl
    have h2 : (k : ℕ) • (toyXEquiv p x) = (l : ℕ) • (toyXEquiv p x) := by
      rw [← map_nsmul, ← map_nsmul, h1]
    have h3 : (k : ℤ_[p]) * (toyXEquiv p x i) = (l : ℤ_[p]) * (toyXEquiv p x i) := by
      have := congrFun h2 i
      rwa [Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, nsmul_eq_mul] at this
    have h4 : ((k : ℤ_[p]) - (l : ℤ_[p])) * (toyXEquiv p x i) = 0 := by
      rw [sub_mul, h3, sub_self]
    rcases mul_eq_zero.mp h4 with h5 | h5
    · exact Nat.cast_injective (sub_eq_zero.mp h5)
    · exact absurd h5 hi
  have : Finite ℕ := Finite.of_injective _ hinj
  exact not_finite ℕ

/-! ### The descent layer -/

/-- **Toy `SelmerData`**: `SelDual = ℤ_[p]²`, `ShaDual = PUnit` (trivial Ш), the
descent sequence `0 → 0 → ℤ_[p]² → ℤ_[p]² → 0`. -/
noncomputable def toySelmer (p : ℕ) [Fact p.Prime] : SelmerData p where
  SelDual := Fin 2 → ℤ_[p]
  ShaDual := PUnit
  ι := 0
  π := LinearMap.id
  ι_inj := fun a b _ => Subsingleton.elim a b
  π_surj := fun v => ⟨v, rfl⟩
  mw_sha_exact := by rw [LinearMap.range_zero, LinearMap.ker_id]

/-! ### The Iwasawa layer -/

/-- **Toy `IwasawaData`** over `Lp = X²` and `SelDual = ℤ_[p]²`. -/
noncomputable def toyIwasawa (p : ℕ) [Fact p.Prime] :
    IwasawaData p ((X : Λ p) ^ 2) (Fin 2 → ℤ_[p]) where
  X := ToyX p
  no_finite_submodule := toy_no_finite_submodule
  rubin_structure := by
    refine ⟨2, fun _ => (X : Λ p), LinearMap.id, ?_, ?_, ?_⟩
    · rw [LinearMap.ker_id]; infer_instance
    · have : Subsingleton
          ((Fin 2 → (Λ p ⧸ Ideal.span {(X : Λ p)})) ⧸
            LinearMap.range (LinearMap.id : ToyX p →ₗ[Λ p] ToyX p)) :=
        Submodule.Quotient.subsingleton_iff.mpr LinearMap.range_id
      infer_instance
    · rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  control :=
    ((Submodule.Quotient.restrictScalarsEquiv ℤ_[p]
        (Ideal.span {(X : Λ p)} • (⊤ : Submodule (Λ p) (ToyX p)))).symm.trans
      (Submodule.quotEquivOfEqBot _
        (by rw [span_X_smul_top_eq_bot, Submodule.restrictScalars_bot]))).trans (toyXEquiv p)

end Toy

end FinShaRank2
