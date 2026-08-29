import FinShaRank2.Interface.Katz
import FinShaRank2.Toy.ShaAnalytic

/-!
# Anti-vacuity Katz layer (task T41): `Toy.shaKatz`

The Katz-measure layer of the anti-vacuity instance `ToySha`. As in the T40 layer
(`Toy/Katz.lean`) the unramified coefficient ring is `W := ℤ_[p]` itself and
`L^{Katz} := Lp`.

The one change forced by `Lp = C p · X²` is the **grade-two core**: since
`coeff 2 L^{Katz} = p`, the frozen `grading_congr` field
`p² · (κ₀ · coeff 2 L^{Katz} − m2core) ∈ (p³)` forces `m2core ≡ 0 (mod p)`, so
`m2core := 1` (the T40 value) is *not* available. We take `m2core := p`, which
makes the congruence an equality `p² · 0 = 0` with `κ₀ = 1`.

This is the expected shadow of the T25 grading-valuation kernel: a non-unit
`coeff 2 L^{Katz}` goes hand in hand with a vanishing criterion class. Nothing
in `KatzData` asserts that the criterion class is nonzero, so the layer is
constructible.
-/

open PowerSeries

namespace FinShaRank2

namespace Toy

variable {p : ℕ} [Fact p.Prime]

/-- **Anti-vacuity `KatzData`** over `Lp = C p · X²`: `W = ℤ_[p]`,
`L^{Katz} = C p · X²`, `m2core = p`. -/
noncomputable def shaKatz (p : ℕ) [Fact p.Prime] : KatzData p (shaLp p) where
  W := ℤ_[p]
  algInj := by intro x y h; simpa using h
  maxIdeal_eq_p := PadicInt.maximalIdeal_eq_span_p
  LKatz := shaLp p
  comparison := ⟨1, 1, by simp [shaLp]⟩
  m2core := (p : ℤ_[p])
  grading_congr := ⟨1, by simp [coeff_two_shaLp]⟩
  traceClass := 1

end Toy

end FinShaRank2
