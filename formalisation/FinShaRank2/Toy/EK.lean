import FinShaRank2.Interface.EK

/-!
# Toy Eisenstein–Kronecker layer: `Toy.toyEK`

The `EKPackage` field of both `ClassicalInputs` instances — the non-vacuity
instance `ToyTrivial` (`ToyTrivial`) and the anti-vacuity instance `ToySha` (`ToySha`). The
package is a global datum, independent of the prime and of the per-prime layers,
so one witness serves both.

The witness is the cheapest one: a one-point divisor over `ℚ`, all six sections
of (7) constantly `1`, the trivial valuation at every rational prime,
empty support. The four instance fields of `EKPackage` are synthesised.

`δ_E(c)` is then not a datum but the def `EKPackage.deltaE`, and on this package
it computes: the divisor is a single point, so `δ_E(c) = ∑ᵢ cᵢ` transported along
`algebraMap ℚ ℚ`, and `δ_E(c) ≠ 0` iff that sum is nonzero (`deltaE_sum`,
`deltaE_ne_zero`). Nothing downstream needs the computation — Theorem C (Theorem 5.10)
consumes the package through `Fc`, `D`, `v` and `supp` only — but it is what
makes the layer a witness rather than a restatement.

## Do not unfold the package in a goal

`simp [toyEK]` reduces `toyEK.L` to `ℚ` while leaving the `CommMonoid` argument
of `Finset.prod` at the projection `toyEK.fieldL.toCommMonoid`. The goal is then
type-incorrect at instance transparency and `simp` refuses to rewrite it —
`Finset.prod_singleton` silently does not fire. Every proof below goes through
the general API of `Interface/EK.lean` (`deltaE_singleton`, `deltaE_def`,
`Fc_def`), which is stated at the projections and never touches the carriers.
Two further consequences of the same design: divisor points must be named at type
`toyEK.ι` (`toyPt` below), and coefficient vectors at type `Fin 6 → toyEK.K`.
-/

namespace FinShaRank2

namespace Toy

/-- **Toy `EKPackage`**: a one-point divisor over `ℚ`, constant sections, trivial
valuations, empty support. Every field is a literal; the four instance fields
(`fieldK`, `fieldL`, `algKL`, `ordΓ`) are synthesised. -/
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

/-- The single point of the toy divisor, declared at type `toyEK.ι`. Writing
`(0 : Fin 1)` inside a statement about `toyEK` produces a term that later
rewrites will not accept at reducible transparency. -/
def toyPt : toyEK.ι := (0 : Fin 1)

theorem toyEK_D : toyEK.D = {toyPt} := rfl

@[simp] theorem toyEK_r (i : Fin 6) (t : toyEK.ι) : toyEK.r i t = 1 := rfl

@[simp] theorem toyEK_supp (c : Fin 6 → toyEK.K) : toyEK.supp c = ∅ := rfl

/-- `δ_E(c)` on the toy package is the coefficient sum, transported along
`algebraMap`. The `algebraMap` is not cosmetic: `F_c` is a `K`-combination of
`L`-valued sections, so it lands in `L`. -/
theorem deltaE_sum (c : Fin 6 → toyEK.K) :
    toyEK.deltaE c = algebraMap toyEK.K toyEK.L (∑ i, c i) := by
  rw [toyEK.deltaE_singleton c _ toyEK_D]
  simp only [EKPackage.Fc_def, toyEK_r, ← Algebra.algebraMap_eq_smul_one, ← map_sum]

/-- So `δ_E(c) ≠ 0` exactly when the coefficient sum is nonzero. -/
theorem deltaE_ne_zero (c : Fin 6 → toyEK.K) : toyEK.deltaE c ≠ 0 ↔ ∑ i, c i ≠ 0 := by
  rw [deltaE_sum]
  exact map_ne_zero_iff _ (algebraMap toyEK.K toyEK.L).injective

/-- On the trivial valuation every nonzero element is a `𝔭`-unit: `toyEK.v p x = 1`
is the paper's `v_𝔭(x) = 0`. Note the multiplicative normalisation
(`Interface/EK.lean`, module docstring). -/
theorem toyEK_v_eq_one (p : ℕ) {x : ℚ} (hx : x ≠ 0) : toyEK.v p x = 1 :=
  Valuation.one_apply_of_ne_zero (R := ℚ) (Γ₀ := NNReal) hx

/-- And every element is `𝔭`-integral: `toyEK.v p x ≤ 1` is the paper's
`v_𝔭(x) ≥ 0`. -/
theorem toyEK_v_le_one (p : ℕ) (x : ℚ) : toyEK.v p x ≤ 1 :=
  Valuation.one_apply_le_one (R := ℚ) (Γ₀ := NNReal) x

end Toy

end FinShaRank2
