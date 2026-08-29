import FinShaRank2.Interface.Katz

/-!
# Toy Katz layer (task T40): `Toy.toyKatz`

The Katz-measure / `δ_E` layer of the non-vacuity instance. The toy world takes
the unramified coefficient ring to be `W := ℤ_[p]` itself (unramified of degree
one over `ℤ_[p]`, so `algebraMap` is the identity and the maximal ideal is
`(p)`), `L^{Katz} := X² = Lp`, `m2core := 1`, `δ_E := 1` and
`NonvanishingOnDE := True`.

Both computational fields are then immediate: `comparison` holds with
`c = u = 1`, and `grading_congr` with `κ₀ = 1` because
`coeff 2 (X²) = 1 = m2core`, so the congruence is `p² · 0 ∈ (p³)`.
-/

open PowerSeries

namespace FinShaRank2

namespace Toy

variable {p : ℕ} [Fact p.Prime]

/-- **Toy `KatzData`** over `Lp = X²`: `W = ℤ_[p]`, `L^{Katz} = X²`,
`m2core = 1`, `δ_E = 1`. -/
noncomputable def toyKatz (p : ℕ) [Fact p.Prime] : KatzData p ((X : Λ p) ^ 2) where
  W := ℤ_[p]
  algInj := by intro x y h; simpa using h
  maxIdeal_eq_p := PadicInt.maximalIdeal_eq_span_p
  LKatz := (X : PowerSeries ℤ_[p]) ^ 2
  comparison := ⟨1, 1, by simp⟩
  m2core := 1
  grading_congr := ⟨1, by simp⟩
  deltaE_local := 1
  NonvanishingOnDE := True
  resultant_link := fun _ _ => trivial
  traceClass := 1

end Toy

end FinShaRank2
