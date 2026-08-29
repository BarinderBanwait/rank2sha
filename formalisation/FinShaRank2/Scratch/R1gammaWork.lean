import Mathlib
import FinShaRank2.Interface.EK

/-!
# R1γ scratch: constructibility of `EKPackage`

Not built by `lake build`, not audited. Its purpose is to check, before R2a depends on it,
that `EKPackage` is cheap to instantiate — `ToyTrivial` and `ToySha` are anti-vacuity
tripwires and R2a has to build an `EKPackage` inside both.

The witness below is the cheapest one: a one-point divisor over `ℚ`, all six sections
constantly `1`, the trivial valuation at every prime, empty support. The four instance fields
are synthesised, so `toyEK` lists nine entries and no proofs beyond `D_nonempty`.

## Notes for R2a — read before writing toy computations

1. **Never unfold the package in a goal.** `simp [toyEK]` reduces `toyEK.L` to `ℚ` while
   leaving the `CommMonoid` argument of `Finset.prod` as `toyEK.fieldL.toCommMonoid`. The
   goal is then type-incorrect at instance transparency and `simp` refuses to rewrite it
   (`Finset.prod_singleton` silently does not fire). Go through the general API lemmas of
   `Interface/EK.lean` — `deltaE_singleton`, `deltaE_ne_zero_iff`, `deltaE_def`, `Fc_def` —
   which are stated at the projections and never touch the carriers.
2. **Give points of the divisor a name at type `toyEK.ι`.** Writing `(0 : Fin 1)` inside a
   statement about `toyEK` produces a term Lean will not accept at reducible transparency in
   later rewrites; `toyPt` below is the same point declared at `toyEK.ι`, and it rewrites.
3. **Coefficient vectors are `Fin 6 → toyEK.K`, not `Fin 6 → ℚ`.** The two are definitionally
   equal but not syntactically, and `rw` with an `EKPackage` lemma fails on the second form.
4. **Concrete mathlib lemmas about `ℚ` or `NNReal` need their types pinned.** The valuation
   examples below pass `(R := ℚ) (Γ₀ := NNReal)`; without them Lean unifies against `toyEK.L`
   and fails to find `NoZeroDivisors toyEK.L` and `DecidablePred fun x ↦ x = 0`.
-/

namespace FinShaRank2

/-- A one-point `EKPackage` over `ℚ`. Every field is filled by a literal; the four instance
fields (`fieldK`, `fieldL`, `algKL`, `ordΓ`) are synthesised, so they need no entry. -/
noncomputable def toyEK : EKPackage where
  K := ℚ
  L := ℚ
  Γ := NNReal
  ι := Fin 1
  D := {0}
  D_nonempty := ⟨0, Finset.mem_singleton_self 0⟩
  r := fun _ _ ↦ 1
  v := fun _ ↦ 1
  supp := fun _ ↦ ∅

/-- The single point of the toy divisor, declared at type `toyEK.ι`. -/
def toyPt : toyEK.ι := (0 : Fin 1)

theorem toyEK_D : toyEK.D = {toyPt} := rfl

@[simp] theorem toyEK_r (i : Fin 6) (t : toyEK.ι) : toyEK.r i t = 1 := rfl

@[simp] theorem toyEK_supp (c : Fin 6 → toyEK.K) : toyEK.supp c = ∅ := rfl

/-- The carriers are definitionally the intended ones. -/
example : toyEK.K = ℚ := rfl
example : toyEK.L = ℚ := rfl
example : toyEK.Γ = NNReal := rfl
example : toyEK.ι = Fin 1 := rfl

/-- `δ_E(c)` over a one-point divisor collapses to the single value of `F_c`. -/
example (c : Fin 6 → toyEK.K) : toyEK.deltaE c = toyEK.Fc c toyPt :=
  toyEK.deltaE_singleton c _ toyEK_D

/-- And that value is the coefficient sum, transported along `algebraMap`. The `algebraMap` is
not cosmetic: `F_c` is a `K`-combination of `L`-valued sections, so it lands in `L`. -/
example (c : Fin 6 → toyEK.K) : toyEK.deltaE c = algebraMap toyEK.K toyEK.L (∑ i, c i) := by
  rw [toyEK.deltaE_singleton c _ toyEK_D]
  simp only [EKPackage.Fc_def, toyEK_r, ← Algebra.algebraMap_eq_smul_one, ← map_sum]

/-- `δ_E(0) = 0`. -/
example : toyEK.deltaE 0 = 0 := by
  rw [toyEK.deltaE_singleton 0 _ toyEK_D]
  simp [EKPackage.Fc]

/-- The nonvanishing criterion specialises as expected. -/
example (c : Fin 6 → toyEK.K) : toyEK.deltaE c ≠ 0 ↔ ∑ i, c i ≠ 0 := by
  rw [toyEK.deltaE_singleton c _ toyEK_D]
  simp only [EKPackage.Fc_def, toyEK_r, ← Algebra.algebraMap_eq_smul_one, ← map_sum]
  exact map_ne_zero_iff _ (algebraMap toyEK.K toyEK.L).injective

/-- The valuation field is usable. On the trivial valuation `v_𝔭(x) = 1` — the paper's
`v_𝔭(x) = 0`, i.e. `𝔭 ∤ x` — holds for every nonzero `x`. Note the multiplicative
normalisation. -/
example (p : ℕ) (x : ℚ) (hx : x ≠ 0) : toyEK.v p x = 1 :=
  Valuation.one_apply_of_ne_zero (R := ℚ) (Γ₀ := NNReal) hx

/-- And `v_𝔭(x) ≤ 1` — the paper's `v_𝔭(x) ≥ 0`, i.e. `x` is `𝔭`-integral — holds for every
`x`, as it must for the trivial valuation. -/
example (p : ℕ) (x : ℚ) : toyEK.v p x ≤ 1 :=
  Valuation.one_apply_le_one (R := ℚ) (Γ₀ := NNReal) x

/-- `supp` is usable in exclusion position, which is all `thm:reduction` needs. -/
example (p : ℕ) (c : Fin 6 → toyEK.K) : p ∉ toyEK.supp c := by simp

/-!
## `simp` hygiene check for `deltaE`

`map_prod` is `@[simp]` at this pin, so the concern was that `simp` would tear `deltaE` apart
behind the caller's back. It does not: `deltaE` is a plain `def`, `deltaE_def` and `Fc_def`
are not simp lemmas, and `simp` does not unfold plain defs unless they are named in the simp
set. The two checks below are the evidence, and they are why `@[irreducible]` is not wanted:
it would block the toy computations above and buy nothing.
-/

/-- The default `simp` set — `map_prod` included — makes no progress on `deltaE`, even with a
rewrite for `P.D` in hand: `deltaE` stays folded, so nothing rewrites underneath it. Naming it
does unfold it, which is what `deltaE_singleton` and the toy proofs above rely on. -/
example (P : EKPackage) (c : Fin 6 → P.K) (h : P.D = ∅) : P.deltaE c = 1 := by
  fail_if_success simp [h]
  simp [EKPackage.deltaE, h]

end FinShaRank2
