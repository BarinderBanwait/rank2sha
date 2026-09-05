import Mathlib
import FinShaRank2.Defs

/-!
# Eisenstein–Kronecker interface: `EKPackage`

The formal counterpart of the Bannai–Kobayashi jet: the divisor `D_E` of (10),
the six-function package `𝓡_E` of (11), and a multiplicative valuation at each
rational prime. Only the objects the paper itself constructs are assumed.

## The valuation normalisation is multiplicative

Mathlib's `Valuation L Γ` is a monoid homomorphism to a linearly ordered commutative monoid
with zero, so the order runs opposite to the paper's additive `v_𝔭`. The dictionary is:

| paper (`v_𝔭`, additive) | Lean (`P.v p`, multiplicative) |
|---|---|
| `v_𝔭(x) ≥ 0` (`x` is `𝔭`-integral) | `P.v p x ≤ 1` |
| `v_𝔭(x) = 0` (`𝔭 ∤ x`) | `P.v p x = 1` |
| `v_𝔭(x) > 0` (`𝔭 ∣ x`) | `P.v p x < 1` |
| `v_𝔭(x) = ∞` (`x = 0`) | `P.v p x = 0` |

No normalisation `v_𝔭(p) = …` is imposed. Nothing downstream uses one and the value depends on
the choice of `Γ`.

The section values lie in `L`, the paper's `Q̄`; no rationality over `K` is asserted.

Paper statements quoted below: (10), (11).
-/

namespace FinShaRank2

/-- The six slots of (11), as the pairs `(a, b)` with `a ≥ 0`, `b ≥ 1`, `a + b ≤ 3`,
in the order the paper lists them (graded by `a + b - 1`).

`EKPackage.r` is indexed by `Fin 6` rather than by pairs, so this def records which slot is
which. `jetIndex_image` checks that the enumeration is exactly the paper's index set.
PAPER: (11) (`eq:jetpackage`). STATUS: definition. -/
def jetIndex : Fin 6 → ℕ × ℕ
  | 0 => (0, 1)
  | 1 => (0, 2)
  | 2 => (1, 1)
  | 3 => (0, 3)
  | 4 => (1, 2)
  | 5 => (2, 1)

/-- `jetIndex` enumerates the index set of (11) — the pairs `(a, b)` with `b ≥ 1`
and `a + b ≤ 3` — without repetition. -/
theorem jetIndex_image :
    (Finset.univ.image jetIndex) =
      ((Finset.range 4) ×ˢ (Finset.range 4)).filter fun ab ↦ 1 ≤ ab.2 ∧ ab.1 + ab.2 ≤ 3 := by
  decide

/-- `jetIndex` is injective, so the six `Fin 6` slots are six distinct pairs `(a, b)`. -/
theorem jetIndex_injective : Function.Injective jetIndex := by decide

/-- **Eisenstein–Kronecker package for a CM elliptic curve `E/ℚ`**.

The data of the Bannai–Kobayashi jet: the divisor `D_E` of (10), the six functions
`r_{a,b}` of (11), and the valuation `v_𝔭` at each rational prime.

The carrier types are in `Type` and their algebraic instances are bundled as instance fields,
re-exported by the `attribute [instance]` line below, so that `P.K`, `P.L` and `P.Γ` carry
`Field`/`Algebra`/`LinearOrderedCommMonoidWithZero` everywhere downstream. This follows
`KatzData` (`Interface/Katz.lean`). -/
structure EKPackage where
  /-- The imaginary quadratic field `K` by which `E` has complex multiplication; the
  coefficients scaling the six sections are elements of `K`.
  SOURCE: the paper's own definition.
  PAPER:  (11) (`eq:jetpackage`). STATUS: data. -/
  K : Type
  /-- `K` is a field. STATUS: classical (structure instance). -/
  [fieldK : Field K]
  /-- The field `L` in which the values of the package `𝓡_E` lie; the paper's `Q̄`. The values
  `e^*_{a,b}(t, 0) / A(Γ)^a` are algebraic, and in fact lie in an abelian extension of `K`, but
  only the field structure and the `K`-algebra structure are used here.
  SOURCE: Bannai–Kobayashi [K. Bannai and S. Kobayashi, *Algebraic theta functions and the
  p-adic interpolation of Eisenstein–Kronecker numbers*, Duke Math. J. 153 (2010), no. 2,
  229–295], Thm. 2.9 and Cor. 2.11 (algebraicity of the section values).
  PAPER:  (11) (`eq:jetpackage`) (`r_{a,b} : D_E → Q̄`). STATUS: data. -/
  L : Type
  /-- `L` is a field. STATUS: classical (structure instance). -/
  [fieldL : Field L]
  /-- `L` is a `K`-algebra, so that a coefficient `c_{a,b} ∈ K` scales a value `r_{a,b}(t) ∈ L`.
  STATUS: classical (structure instance). -/
  [algKL : Algebra K L]
  /-- The value monoid of the valuations `v_𝔭`. Left as a parameter: no normalisation
  `v_𝔭(p) = …` is imposed, and nothing downstream depends on the choice.
  SOURCE: the paper's own definition. PAPER: §2.1 (`ssec:notation`) (`v_𝔭` on `Q̄^×`).
  STATUS: data. -/
  Γ : Type
  /-- `Γ` is a linearly ordered commutative monoid with zero: the value monoid of a
  multiplicative `Valuation`. STATUS: classical (structure instance). -/
  [ordΓ : LinearOrderedCommMonoidWithZero Γ]
  /-- The type indexing the points of the divisor. The paper takes the points to be the ray
  classes themselves; `ι` is left abstract because nothing below uses the group structure.
  SOURCE: the paper's own definition. PAPER: (10) (`eq:DEdef`). STATUS: data. -/
  ι : Type
  /-- The divisor `D_E := Cl_𝔣(K) = (O_K/𝔣)^× / μ_K`, the ray class group of conductor `𝔣`,
  as a finite set of points.
  SOURCE: classical (finiteness of the ray class group).
  PAPER:  (10) (`eq:DEdef`). STATUS: data. -/
  D : Finset ι
  /-- `D_E` is nonempty: it is a group, so it contains the trivial class.
  SOURCE: classical (a ray class group is a nonempty finite abelian group).
  PAPER:  (10) (`eq:DEdef`). STATUS: classical. -/
  D_nonempty : D.Nonempty
  /-- The package `𝓡_E` of six functions `r_{a,b} : D_E → Q̄`, indexed by `Fin 6` through
  `jetIndex`: the grade-`≤ 2` jet of the reduced theta function evaluated along the
  `𝔣`-division values, `r_{a,b}([g]) = ε(g)^{-(a+b)} e^*_{a,b}(t_g, 0) / A(Γ)^a`.
  The functions are defined on all of `ι`, not only on `D`; only their values on `D` are used.
  SOURCE: Bannai–Kobayashi [op. cit.], (17) and Thm. 1.17 (the coefficients `e^*_{a,b}`),
  Thm. 2.9 and Cor. 2.11 (algebraicity after division by `A(Γ)^a`).
  PAPER:  (11) (`eq:jetpackage`). STATUS: data. -/
  r : Fin 6 → ι → L
  /-- The valuation `v_𝔭` on `L`, indexed by the rational prime `p`; `𝔭` is the prime of `Q̄`
  determined by the embedding `ι_p` fixed in §2.1. **Multiplicative**: `v_𝔭(x) = 0`
  in the paper is `P.v p x = 1` here, and `v_𝔭(x) ≥ 0` is `P.v p x ≤ 1`. See the module
  docstring.
  SOURCE: classical (valuation theory).
  PAPER:  §2.1 (`ssec:notation`), `eq:classsums`. STATUS: data. -/
  v : ℕ → Valuation L Γ

attribute [instance] EKPackage.fieldK EKPackage.fieldL EKPackage.algKL EKPackage.ordΓ

end FinShaRank2
