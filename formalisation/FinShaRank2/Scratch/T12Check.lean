import Mathlib
import FinShaRank2.Interface.Iwasawa

/-!
# T12 acceptance check

Exercises every field of `IwasawaData` and `SelmerData` on hypothetical terms,
including forming `Module.finrank ℤ_[p] D.X` (the board's T12 acceptance clause:
proves the `ℤ_[p]`-instance plumbing on `X` actually works). Scratch only — not
imported by the root module, excluded from audit.
-/

noncomputable section

open PowerSeries FinShaRank2

variable {p : ℕ} [Fact p.Prime]

/-! ## `IwasawaData` — every field + the finrank acceptance clause -/

-- ACCEPTANCE: forming `Module.finrank ℤ_[p] D.X` (ℤ_[p] plumbing on X works).
example (Lp : Λ p) (SelDual : Type) [AddCommGroup SelDual] [Module ℤ_[p] SelDual]
    (D : IwasawaData p Lp SelDual) : ℕ :=
  Module.finrank ℤ_[p] D.X

-- The Λ-module structure and Λ-finiteness on `X` resolve.
example (Lp : Λ p) (SelDual : Type) [AddCommGroup SelDual] [Module ℤ_[p] SelDual]
    (D : IwasawaData p Lp SelDual) : Module.Finite (Λ p) D.X := inferInstance

-- `no_finite_submodule`.
example (Lp : Λ p) (SelDual : Type) [AddCommGroup SelDual] [Module ℤ_[p] SelDual]
    (D : IwasawaData p Lp SelDual) (N : Submodule (Λ p) D.X) (hN : Finite N) : N = ⊥ :=
  D.no_finite_submodule N hN

-- `rubin_structure`: destructure it and reach the `Associated … Lp` conclusion.
example (Lp : Λ p) (SelDual : Type) [AddCommGroup SelDual] [Module ℤ_[p] SelDual]
    (D : IwasawaData p Lp SelDual) :
    ∃ (n : ℕ) (f : Fin n → Λ p), Associated (∏ i, f i) Lp := by
  obtain ⟨n, f, _φ, _hker, _hcok, hassoc⟩ := D.rubin_structure
  exact ⟨n, f, hassoc⟩

-- `control`: the Γ-coinvariants ≃ₗ SelDual, and finrank transports across it.
example (Lp : Λ p) (SelDual : Type) [AddCommGroup SelDual] [Module ℤ_[p] SelDual]
    (D : IwasawaData p Lp SelDual) :
    Module.finrank ℤ_[p]
        (D.X ⧸ (Ideal.span {(PowerSeries.X : Λ p)} • (⊤ : Submodule (Λ p) D.X)))
      = Module.finrank ℤ_[p] SelDual :=
  D.control.finrank_eq

/-! ## `SelmerData` — every field -/

-- finrank of both duals forms (ℤ_[p] plumbing works).
example (S : SelmerData p) : ℕ := Module.finrank ℤ_[p] S.SelDual
example (S : SelmerData p) : ℕ := Module.finrank ℤ_[p] S.ShaDual

-- f.g. instances resolve.
example (S : SelmerData p) : Module.Finite ℤ_[p] S.SelDual := inferInstance
example (S : SelmerData p) : Module.Finite ℤ_[p] S.ShaDual := inferInstance

-- the descent maps and the three exactness props.
example (S : SelmerData p) : S.ShaDual →ₗ[ℤ_[p]] S.SelDual := S.ι
example (S : SelmerData p) : S.SelDual →ₗ[ℤ_[p]] (Fin 2 → ℤ_[p]) := S.π
example (S : SelmerData p) : Function.Injective S.ι := S.ι_inj
example (S : SelmerData p) : Function.Surjective S.π := S.π_surj
example (S : SelmerData p) : LinearMap.range S.ι = LinearMap.ker S.π := S.mw_sha_exact

/-! ## The two structures share one `SelDual` (contract for T14/T31) -/

-- T14 threads `selmer.SelDual` into `IwasawaData`; then `control` and
-- `mw_sha_exact` speak about the *same* type, with no bridge required.
example (Lp : Λ p) (S : SelmerData p) (D : IwasawaData p Lp S.SelDual) :
    (D.X ⧸ (Ideal.span {(PowerSeries.X : Λ p)} • (⊤ : Submodule (Λ p) D.X)))
      ≃ₗ[ℤ_[p]] S.SelDual :=
  D.control

end
