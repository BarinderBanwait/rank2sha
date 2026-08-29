import Mathlib

/-!
# Orbit criterion (task R1β, paper `lem:orbit`)

This file renders the paper's `lem:orbit` (Lemma 4.6 of `deltaE.tex`) as pure `mathlib`-only
Galois theory. Nothing here mentions the paper's interface: the statements are carried over an
abstract Galois extension `L/K` and an abstract `Gal(L/K)`-set `D`, so the instantiation
`K := K`, `L :=` the abelian extension carrying the section values, `D := D_E = Cl_𝔣(K)` is a
substitution.

## Mathematical content

Let `L/K` be Galois, let `D` be a finite `Gal(L/K)`-set, and let `F : D → L` be equivariant,
`F (σ • t) = σ (F t)`.

1. `∏_{t ∈ D} F t` lies in `K`. Each `σ` permutes `D`, hence permutes the factors, hence fixes
   the product; a fixed element of a Galois extension lies in the base field.
2. If `Gal(L/K)` acts transitively on `D` and `F` vanishes at one point, it vanishes at every
   point. Transitivity gives `σ` with `t = σ • t₀`, and then `F t = σ (F t₀) = 0`.

## Status

This file is a faithful rendering of a paper lemma, not a link in the main chain, for two
reasons.

* The paper applies `lem:orbit` to `D_E` and `F_c` granting an equivariance input it does not
  prove: the reciprocity of Eisenstein–Kronecker values, `r_{a,b}(σ t) = σ (r_{a,b}(t))`
  (`deltaE.tex`, the paragraph after `lem:orbit`). The algebraic trivialisation behind
  Bannai–Kobayashi Cor. 2.11 is fixed only up to a root of unity, so the action is not pinned
  down there. Here that input is the hypothesis `hF`; it is assumed, not derived.
* The paper records explicitly that `thm:reduction` does not depend on this lemma
  (`deltaE.tex`, same paragraph): its proof works with `v_𝔭` on `Q̄^×` directly. What the lemma
  supplies is the `K`-rationality of `δ_E(c)` and the equivalence between pointwise
  nonvanishing of `F_c` on `D_E` and `δ_E(c) ≠ 0`.

## Main results

* `FinShaRank2.Orbit.prod_mem_range_algebraMap` — part (1).
* `FinShaRank2.Orbit.forall_eq_zero_of_exists_eq_zero` — part (2).

Part (1) lands in `Set.range (algebraMap K L)` rather than in an `IntermediateField`, which
avoids subtype coercions at the call site. It uses `InfiniteGalois.mem_range_algebraMap_iff_fixed`
rather than `IsGalois.mem_range_algebraMap_iff_fixed`, because the latter additionally requires
`[FiniteDimensional K L]`, which `lem:orbit` does not assume.

Paper labels: `lem:orbit`, `def:deltaE`, `eq:DEdef`, `conj:EK`, `thm:reduction`.
-/

namespace FinShaRank2.Orbit

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {D : Type*} [MulAction (L ≃ₐ[K] L) D]

/-- **Orbit criterion, part (1).** Let `L/K` be Galois, let the finite set `D` carry an action
of `Gal(L/K)`, and let `F : D → L` be equivariant: `F (σ • t) = σ (F t)` for all `σ` and `t`.
Then `∏ t, F t` lies in the image of `K` in `L`.

Every `σ ∈ Gal(L/K)` permutes `D`, so reindexing the product along the permutation
`MulAction.toPerm σ` shows `σ` fixes `∏ t, F t`; an element of a Galois extension fixed by every
element of the Galois group lies in the base field
(`InfiniteGalois.mem_range_algebraMap_iff_fixed`). PAPER: `lem:orbit`(1). -/
theorem prod_mem_range_algebraMap [IsGalois K L] [Fintype D] (F : D → L)
    (hF : ∀ (σ : L ≃ₐ[K] L) (t : D), F (σ • t) = σ (F t)) :
    (∏ t, F t) ∈ Set.range (algebraMap K L) := by
  rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
  intro σ
  calc σ (∏ t, F t) = ∏ t, σ (F t) := map_prod σ F Finset.univ
    _ = ∏ t, F (σ • t) := Finset.prod_congr rfl fun t _ ↦ (hF σ t).symm
    _ = ∏ t, F t := Equiv.prod_comp (MulAction.toPerm σ) F

/-- **Orbit criterion, part (2).** If `Gal(L/K)` acts transitively on `D` and the equivariant
function `F : D → L` vanishes at one point of `D`, then it vanishes at every point.

Transitivity gives `σ` with `σ • t₀ = t`; equivariance then gives `F t = σ (F t₀) = σ 0 = 0`.
Neither finiteness of `D` nor the Galois hypothesis on `L/K` is used. PAPER: `lem:orbit`(2). -/
theorem forall_eq_zero_of_exists_eq_zero [MulAction.IsPretransitive (L ≃ₐ[K] L) D] (F : D → L)
    (hF : ∀ (σ : L ≃ₐ[K] L) (t : D), F (σ • t) = σ (F t))
    (h : ∃ t, F t = 0) : ∀ t, F t = 0 := by
  obtain ⟨t₀, ht₀⟩ := h
  intro t
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (L ≃ₐ[K] L) t₀ t
  rw [← hσ, hF, ht₀, map_zero]

end FinShaRank2.Orbit
