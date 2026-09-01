import Mathlib
import FinShaRank2.Defs

/-!
# Eisenstein–Kronecker interface: `EKPackage`

The archimedean side of Definition 4.8. `EKPackage` bundles the divisor `D_E` of (12),
the six-function package `𝓡_E` of (13), a multiplicative valuation at each
rational prime, and the support function `supp` of Hypothesis 4.10. On top of that data,
`δ_E(c)` is a **definition**, not an assumed datum:

    EKPackage.Fc     P c t = ∑ i, c i • P.r i t
    EKPackage.deltaE P c   = ∏ t ∈ P.D, P.Fc c t

The product is written out, so Definition 4.8 is discharged by unfolding, and the only
data assumed are the objects the paper itself constructs: `D_E`, `𝓡_E`, `v_𝔭`, `supp`.

## The valuation normalisation is multiplicative — read this before comparing with the paper

Mathlib's `Valuation L Γ` is a monoid homomorphism to a linearly ordered commutative monoid
with zero, so the order runs opposite to the paper's additive `v_𝔭`. The dictionary is:

| paper (`v_𝔭`, additive) | Lean (`P.v p`, multiplicative) |
|---|---|
| `v_𝔭(x) ≥ 0` (`x` is `𝔭`-integral) | `P.v p x ≤ 1` |
| `v_𝔭(x) = 0` (`𝔭 ∤ x`) | `P.v p x = 1` |
| `v_𝔭(x) > 0` (`𝔭 ∣ x`) | `P.v p x < 1` |
| `v_𝔭(x) = ∞` (`x = 0`) | `P.v p x = 0` |

Every inequality of Hypothesis 4.10 and Theorem C (Theorem 4.12) therefore reads
reversed in the Lean.
`AddValuation` would preserve the direction but has no product lemma at this mathlib pin, and
`δ_E(c)` is a product, so the multiplicative encoding is the one used.

No normalisation `v_𝔭(p) = …` is imposed. Nothing downstream uses one and the value depends on
the choice of `Γ`.

## `δ_E(c)` lands in `L`, not in `K`

`L` is the paper's `Q̄`. That `δ_E(c) ∈ K` is Lemma 4.9(1), which the paper proves only after
granting the equivariance `r_{a,b}(σ t) = σ(r_{a,b}(t))`, an input it uses rather than proves.
Theorem C does not use Lemma 4.9, and `δ_E(c)` is not proved rational
(`deltaE.tex`, after Theorem C), so the divisibility condition `𝔭 ∤ δ_E(c)` is not
symmetric in `𝔭` and `𝔭̄`. Testing it with `padicValRat`, as the structure being replaced did,
asserts a rationality that is not available.

Paper statements quoted below: (12), (13), Definition 4.8, Lemma 4.9,
Hypothesis 4.10, Theorem C.
-/

namespace FinShaRank2

/-- The six slots of (13), as the pairs `(a, b)` with `a ≥ 0`, `b ≥ 1`, `a + b ≤ 3`,
in the order the paper lists them (graded by `a + b - 1`).

`EKPackage.r` is indexed by `Fin 6` rather than by pairs, so this def records which slot is
which. `jetIndex_image` checks that the enumeration is exactly the paper's index set.
PAPER: (13) (`eq:jetpackage`). STATUS: definition. -/
def jetIndex : Fin 6 → ℕ × ℕ
  | 0 => (0, 1)
  | 1 => (0, 2)
  | 2 => (1, 1)
  | 3 => (0, 3)
  | 4 => (1, 2)
  | 5 => (2, 1)

/-- `jetIndex` enumerates the index set of (13) — the pairs `(a, b)` with `b ≥ 1`
and `a + b ≤ 3` — without repetition. -/
theorem jetIndex_image :
    (Finset.univ.image jetIndex) =
      ((Finset.range 4) ×ˢ (Finset.range 4)).filter fun ab ↦ 1 ≤ ab.2 ∧ ab.1 + ab.2 ≤ 3 := by
  decide

/-- `jetIndex` is injective, so the six `Fin 6` slots are six distinct pairs `(a, b)`. -/
theorem jetIndex_injective : Function.Injective jetIndex := by decide

/-- **Eisenstein–Kronecker package for a CM elliptic curve `E/ℚ`** (paper §4.4).

The data of Definition 4.8 other than the coefficient vector: the divisor `D_E` of (12),
the six functions `r_{a,b}` of (13), the valuation `v_𝔭` at each rational prime, and
the support function of Hypothesis 4.10. The invariant `δ_E(c)` is then the def
`EKPackage.deltaE`, not a field.

The carrier types are in `Type` and their algebraic instances are bundled as instance fields,
re-exported by the `attribute [instance]` line below, so that `P.K`, `P.L` and `P.Γ` carry
`Field`/`Algebra`/`LinearOrderedCommMonoidWithZero` everywhere downstream. This follows
`KatzData` (`Interface/Katz.lean`). -/
structure EKPackage where
  /-- The imaginary quadratic field `K` by which `E` has complex multiplication; the
  coefficient vectors `c` of Definition 4.8 are elements of `K⁶`.
  SOURCE: the paper's own definition.
  PAPER:  Definition 4.8 (`def:deltaE`) (`c = (c_{a,b}) ∈ K⁶`). STATUS: data. -/
  K : Type
  /-- `K` is a field. STATUS: classical (structure instance). -/
  [fieldK : Field K]
  /-- The field `L` in which the values of the package `𝓡_E` lie; the paper's `Q̄`. The values
  `e^*_{a,b}(t, 0) / A(Γ)^a` are algebraic, and in fact lie in an abelian extension of `K`, but
  only the field structure and the `K`-algebra structure are used here.
  SOURCE: Bannai–Kobayashi [K. Bannai and S. Kobayashi, *Algebraic theta functions and the
  p-adic interpolation of Eisenstein–Kronecker numbers*, Duke Math. J. 153 (2010), no. 2,
  229–295], Thm. 2.9 and Cor. 2.11 (algebraicity of the section values).
  PAPER:  (13) (`eq:jetpackage`) (`r_{a,b} : D_E → Q̄`). STATUS: data. -/
  L : Type
  /-- `L` is a field. STATUS: classical (structure instance). -/
  [fieldL : Field L]
  /-- `L` is a `K`-algebra, so that a coefficient `c_{a,b} ∈ K` scales a value `r_{a,b}(t) ∈ L`.
  STATUS: classical (structure instance). -/
  [algKL : Algebra K L]
  /-- The value monoid of the valuations `v_𝔭`. Left as a parameter: no normalisation
  `v_𝔭(p) = …` is imposed, and nothing downstream depends on the choice.
  SOURCE: the paper's own definition. PAPER: §2.1 (§2.1) (`v_𝔭` on `Q̄^×`).
  STATUS: data. -/
  Γ : Type
  /-- `Γ` is a linearly ordered commutative monoid with zero: the value monoid of a
  multiplicative `Valuation`. STATUS: classical (structure instance). -/
  [ordΓ : LinearOrderedCommMonoidWithZero Γ]
  /-- The type indexing the points of the divisor. The paper takes the points to be the ray
  classes themselves; `ι` is left abstract because nothing below uses the group structure.
  SOURCE: the paper's own definition. PAPER: (12) (`eq:DEdef`). STATUS: data. -/
  ι : Type
  /-- The divisor `D_E := Cl_𝔣(K) = (O_K/𝔣)^× / μ_K`, the ray class group of conductor `𝔣`,
  as a finite set of points. Finiteness is what makes `Res(F_c, D_E)` a finite product.
  SOURCE: classical (finiteness of the ray class group).
  PAPER:  (12) (`eq:DEdef`). STATUS: data. -/
  D : Finset ι
  /-- `D_E` is nonempty: it is a group, so it contains the trivial class.
  SOURCE: classical (a ray class group is a nonempty finite abelian group).
  PAPER:  (12) (`eq:DEdef`). STATUS: classical. -/
  D_nonempty : D.Nonempty
  /-- The package `𝓡_E` of six functions `r_{a,b} : D_E → Q̄`, indexed by `Fin 6` through
  `jetIndex`: the grade-`≤ 2` jet of the reduced theta function evaluated along the
  `𝔣`-division values, `r_{a,b}([g]) = ε(g)^{-(a+b)} e^*_{a,b}(t_g, 0) / A(Γ)^a`.
  The functions are defined on all of `ι`, not only on `D`; only their values on `D` are used.
  SOURCE: Bannai–Kobayashi [op. cit.], (15) and Thm. 1.17 (the coefficients `e^*_{a,b}`),
  Thm. 2.9 and Cor. 2.11 (algebraicity after division by `A(Γ)^a`).
  PAPER:  (13) (`eq:jetpackage`). STATUS: data. -/
  r : Fin 6 → ι → L
  /-- The valuation `v_𝔭` on `L`, indexed by the rational prime `p`; `𝔭` is the prime of `Q̄`
  determined by the embedding `ι_p` fixed in §2.1. **Multiplicative**: `v_𝔭(x) = 0`
  in the paper is `P.v p x = 1` here, and `v_𝔭(x) ≥ 0` is `P.v p x ≤ 1`. See the module
  docstring.
  SOURCE: classical (valuation theory).
  PAPER:  §2.1 (§2.1); used in Hypothesis 4.10 (`hyp:sinnott`) and Theorem C (Theorem
  4.12, `thm:reduction`). STATUS: data. -/
  v : ℕ → Valuation L Γ
  /-- `supp(c)`: the finite set of rational primes lying below a prime of `Q̄` at which some
  entry of `c` is not a unit. Left opaque. Theorem C (Theorem 4.12) uses it only through
  the exclusion
  `p ∉ supp(c)`, and the paper's bound on it — that the entries of the expected `c` are roots of
  unity times Gauss sums times rationals supported on `{2, 3}`, so that `supp(c)` adds no split
  prime to `S_E` — is stated there as an expectation, not a theorem.
  SOURCE: the paper's own definition.
  PAPER:  Hypothesis 4.10 (`hyp:sinnott`) (the definition of `supp(c)`). STATUS: data. -/
  supp : (Fin 6 → K) → Finset ℕ

attribute [instance] EKPackage.fieldK EKPackage.fieldL EKPackage.algKL EKPackage.ordΓ

namespace EKPackage

variable (P : EKPackage) (c : Fin 6 → P.K)

/-- `F_c := ∑_{a,b} c_{a,b} r_{a,b}`, the coefficient vector `c` applied to the package `𝓡_E`.
PAPER: Definition 4.8 (`def:deltaE`). STATUS: definition. -/
def Fc (t : P.ι) : P.L := ∑ i, c i • P.r i t

/-- `δ_E(c) := Res(F_c, D_E) = ∏_{t ∈ D_E} F_c(t)`, the candidate invariant of Definition 4.8.

It lands in `P.L`, the paper's `Q̄`. That it lies in `K` is Lemma 4.9(1), which needs the
equivariance input the paper does not prove; Theorem C (Theorem 4.12) does not use it.
PAPER: Definition 4.8 (`def:deltaE`). STATUS: definition. -/
def deltaE : P.L := ∏ t ∈ P.D, P.Fc c t

theorem Fc_def (t : P.ι) : P.Fc c t = ∑ i, c i • P.r i t := rfl

theorem deltaE_def : P.deltaE c = ∏ t ∈ P.D, P.Fc c t := rfl

/-- `δ_E(c) ≠ 0` exactly when `F_c` vanishes at no point of `D_E`. Immediate from Definition 4.8
once `δ_E(c)` is the product rather than assumed data.
PAPER: the sentence following Definition 4.8 (`def:deltaE`). STATUS: definition
(consequence of unfolding). -/
theorem deltaE_ne_zero_iff : P.deltaE c ≠ 0 ↔ ∀ t ∈ P.D, P.Fc c t ≠ 0 := by
  rw [deltaE_def, Finset.prod_ne_zero_iff]

/-- `δ_E(c)` on a one-point divisor is the single value of `F_c`.

Stated for a hypothesis `P.D = {t}` rather than by unfolding a particular package: on an
instantiated `EKPackage` the carriers `P.K`, `P.L`, `P.ι` are projections, and unfolding the
package in the goal reduces them to their concrete values while leaving the instance arguments
in projected form, which makes the goal type-incorrect at instance transparency and blocks
`simp`. The toy instances therefore go through this lemma. -/
theorem deltaE_singleton (t : P.ι) (h : P.D = {t}) : P.deltaE c = P.Fc c t := by
  rw [deltaE_def, h, Finset.prod_singleton]

end EKPackage

end FinShaRank2
