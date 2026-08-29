import Mathlib
import FinShaRank2.Defs

/-!
# Sha endgame — `prop:consequence` Step 5 (task T27)

This file proves, as pure `ℤ_[p]`-module algebra, the final step of the paper's
`prop:consequence`: from the dualized descent sequence

```
0 → Ш(E/ℚ)[p^∞]^∨ → Sel_{p^∞}(E/ℚ)^∨ → (E(ℚ)⊗ℚ_p/ℤ_p)^∨ ≅ ℤ_p^2 → 0
```

together with the fact — established upstream (T21/T23) — that the Selmer dual is
`ℤ_[p]`-free of rank two, we read off the two headline conclusions
(conventions §2.1):

* `Subsingleton Sha` (i.e. `Ш(E/ℚ)[p^∞] = 0` on the dual side), and
* `Module.finrank ℤ_[p] Sel = 2` (i.e. `corank_{ℤ_p} Sel_{p^∞}(E/ℚ) = 2`).

## Proof route (Orzech property; `NOTES/MathlibAudit.md` §1.5, §4)

The surjection `π : Sel ↠ ℤ_p^2` composed with a rank-two identification
`e : Sel ≃ ℤ_p^2` gives a **surjective endomorphism** `π ∘ e⁻¹` of the finitely
generated module `Fin 2 → ℤ_[p]` over the commutative ring `ℤ_[p]`. Every
commutative ring has the Orzech property
(`OrzechProperty.injective_of_surjective_endomorphism`), so that endomorphism is
injective; composing back with the bijection `e` shows `π` itself is injective.

Injectivity of `π` collapses the exact sequence: `ker π = ⊥`, hence
`range ι = ⊥` by exactness, so the injection `ι : Sha ↪ Sel` lands in `⊥` and
`Sha` is a subsingleton. The rank statement is the equivalence `e` transported by
`LinearEquiv.finrank_eq` and `Module.finrank_fin_fun`.

This avoids `ℚ_[p]`-base-change and rank-additivity entirely (the board's fallback
sketch), per the T03 audit recommendation.

## Interface consumption (contract for T31)

The bundled corollary `sha_endgame_of_nonempty` takes the five exactness fields in
the **exact shapes** of `FinShaRank2.SelmerData` (`ι`, `π`, `ι_inj`, `π_surj`,
`mw_sha_exact`), followed by the `Nonempty (Sel ≃ₗ ℤ_p^2)` that T31 assembles from
`IwasawaData.control` and `selmer_dual_structure` (T23). Hence T31 applies it to a
`SelmerData` record's fields verbatim, with no adapter (`Scratch/T15Chain.lean`
exercises exactly this call end-to-end, at step 8 of `T15Chain.chain`).
-/

namespace FinShaRank2

variable {p : ℕ} [Fact p.Prime]

/-- **T27, `prop:consequence` Step 5.** Given the dualized descent data on
finitely generated `ℤ_[p]`-modules — an injection `ι : Sha ↪ Sel`, a surjection
`π : Sel ↠ ℤ_p^2`, exactness `range ι = ker π`, and a rank-two identification
`e : Sel ≃ ℤ_p^2` — the Tate–Shafarevich dual is a subsingleton and the Selmer
dual has `ℤ_[p]`-rank two.

The `Sel ≃ ℤ_p^2` input is where the upstream structure theorem (`Lp ~ X²`,
Mazur control) lands; see the module docstring. -/
theorem sha_endgame
    {Sha Sel : Type} [AddCommGroup Sha] [Module ℤ_[p] Sha]
    [AddCommGroup Sel] [Module ℤ_[p] Sel]
    (ι : Sha →ₗ[ℤ_[p]] Sel) (π : Sel →ₗ[ℤ_[p]] (Fin 2 → ℤ_[p]))
    (ι_inj : Function.Injective ι) (π_surj : Function.Surjective π)
    (mw_sha_exact : LinearMap.range ι = LinearMap.ker π)
    (e : Sel ≃ₗ[ℤ_[p]] (Fin 2 → ℤ_[p])) :
    Subsingleton Sha ∧ Module.finrank ℤ_[p] Sel = 2 := by
  -- The endomorphism `g = π ∘ e⁻¹` of the finitely generated free module `ℤ_p^2`.
  set g : (Fin 2 → ℤ_[p]) →ₗ[ℤ_[p]] (Fin 2 → ℤ_[p]) := π.comp e.symm.toLinearMap with hg
  -- `g` is surjective (composite of the surjection `π` and the bijection `e⁻¹`).
  have hg_surj : Function.Surjective g := by
    rw [hg, LinearMap.coe_comp]
    exact π_surj.comp e.symm.surjective
  -- Orzech property of the commutative ring `ℤ_[p]`: a surjective endomorphism of a
  -- finitely generated module is injective.
  have hg_inj : Function.Injective g :=
    OrzechProperty.injective_of_surjective_endomorphism g hg_surj
  -- Transport injectivity of `g` back to `π` along the bijection `e`.
  have hπinj : Function.Injective π := by
    intro a b hab
    refine e.injective (hg_inj ?_)
    have : g (e a) = π a := by rw [hg]; simp
    have hb : g (e b) = π b := by rw [hg]; simp
    rw [this, hb]
    exact hab
  -- Exactness collapses: `ker π = ⊥`, hence `range ι = ⊥`.
  have hker : LinearMap.ker π = ⊥ := LinearMap.ker_eq_bot.mpr hπinj
  have hrange : LinearMap.range ι = ⊥ := mw_sha_exact.trans hker
  have hι0 : ι = 0 := LinearMap.range_eq_bot.mp hrange
  refine ⟨?_, ?_⟩
  · -- `Sha` is a subsingleton: `ι` is injective and identically zero.
    refine subsingleton_of_forall_eq 0 fun y => ι_inj ?_
    simp [hι0]
  · -- The rank statement transported along `e`.
    rw [e.finrank_eq, Module.finrank_fin_fun ℤ_[p]]

/-- **Bundled corollary for T31** (`prop:consequence` Step 5, `Nonempty`-wrapped).

Identical to `sha_endgame` but taking the rank-two identification as
`Nonempty (Sel ≃ₗ ℤ_p^2)` — the shape T31 obtains from `IwasawaData.control`
composed with `selmer_dual_structure` (T23). The five preceding arguments are the
`FinShaRank2.SelmerData` fields `ι`, `π`, `ι_inj`, `π_surj`, `mw_sha_exact` in that
order, so T31 applies this to a `SelmerData` record with no glue. -/
theorem sha_endgame_of_nonempty
    {Sha Sel : Type} [AddCommGroup Sha] [Module ℤ_[p] Sha]
    [AddCommGroup Sel] [Module ℤ_[p] Sel]
    (ι : Sha →ₗ[ℤ_[p]] Sel) (π : Sel →ₗ[ℤ_[p]] (Fin 2 → ℤ_[p]))
    (ι_inj : Function.Injective ι) (π_surj : Function.Surjective π)
    (mw_sha_exact : LinearMap.range ι = LinearMap.ker π)
    (hequiv : Nonempty (Sel ≃ₗ[ℤ_[p]] (Fin 2 → ℤ_[p]))) :
    Subsingleton Sha ∧ Module.finrank ℤ_[p] Sel = 2 :=
  hequiv.elim fun e => sha_endgame ι π ι_inj π_surj mw_sha_exact e

end FinShaRank2
