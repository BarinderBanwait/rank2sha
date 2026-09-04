import FinShaRank2.Interface.EK

/-!
# Toy Eisenstein–Kronecker layer: `Toy.toyEK`

The `EKPackage` field shared by both `ClassicalInputs` instances, `ToyTrivial` and
`ToySha`: a one-point divisor over `ℚ`, all six sections of (11) constantly `1`, and
the trivial valuation at every rational prime. The four instance fields (`fieldK`,
`fieldL`, `algKL`, `ordΓ`) are synthesised, and the single divisor point is named
`toyPt` at type `toyEK.ι`.
-/

namespace FinShaRank2

namespace Toy

/-- **Toy `EKPackage`**: a one-point divisor over `ℚ`, constant sections, trivial
valuations. Every field is a literal; the four instance fields
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

/-- The single point of the toy divisor, declared at type `toyEK.ι`. Writing
`(0 : Fin 1)` inside a statement about `toyEK` produces a term that later
rewrites will not accept at reducible transparency. -/
def toyPt : toyEK.ι := (0 : Fin 1)

theorem toyEK_D : toyEK.D = {toyPt} := rfl

@[simp] theorem toyEK_r (i : Fin 6) (t : toyEK.ι) : toyEK.r i t = 1 := rfl

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
