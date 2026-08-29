import Mathlib
import FinShaRank2.Interface.Heights
import FinShaRank2.Interface.Katz

/-!
# T13 acceptance check (scratch — not imported by the root; excluded from audit)

Exercises every field of `HeightData` and `KatzData`, the `criterionClass` def,
and states (does not prove) a `SinnottHyp` term type. Compile directly:
`cd formal && lake env lean FinShaRank2/Scratch/T13Check.lean`.
-/

noncomputable section

namespace T13Check

open FinShaRank2

variable {p : ℕ} [Fact p.Prime]

/-! ## `HeightData` — every field -/

example (H : HeightData p) : ℚ_[p] := H.Reg_γ
example (H : HeightData p) : Prop := H.heightNondeg
example (H : HeightData p) : ℚ_[p] := H.shaOrd
example (H : HeightData p) : ℚ_[p] := H.c2norm
example (H : HeightData p) : ‖H.Reg_γ‖ ≤ 1 := H.reg_integral
example (H : HeightData p) : ‖H.shaOrd‖ ≤ 1 := H.sha_integral
example (H : HeightData p) : ‖H.c2norm‖ = ‖H.Reg_γ‖ * ‖H.shaOrd‖ := H.spr_padicBSD
example (H : HeightData p) :
    IsPUnit H.c2norm ↔ (H.heightNondeg ∧ IsPUnit H.Reg_γ ∧ IsPUnit H.shaOrd) :=
  H.spr_nondeg

/-! ## `KatzData` — every field (`Lp` threaded as parameter) -/

example (Lp : Λ p) (K : KatzData p Lp) : Type := K.W
-- the four bundled instances are available on `K.W`:
example (Lp : Λ p) (K : KatzData p Lp) : CommRing K.W := inferInstance
example (Lp : Λ p) (K : KatzData p Lp) : IsDomain K.W := inferInstance
example (Lp : Λ p) (K : KatzData p Lp) : IsLocalRing K.W := inferInstance
example (Lp : Λ p) (K : KatzData p Lp) : Algebra ℤ_[p] K.W := inferInstance
example (Lp : Λ p) (K : KatzData p Lp) : Function.Injective (algebraMap ℤ_[p] K.W) := K.algInj
example (Lp : Λ p) (K : KatzData p Lp) :
    IsLocalRing.maximalIdeal K.W = Ideal.span {(p : K.W)} := K.maxIdeal_eq_p
example (Lp : Λ p) (K : KatzData p Lp) : PowerSeries K.W := K.LKatz
example (Lp : Λ p) (K : KatzData p Lp) :
    ∃ (c : K.Wˣ) (u : (PowerSeries K.W)ˣ),
      Lp.map (algebraMap ℤ_[p] K.W) = (c : K.W) • ((u : PowerSeries K.W) * K.LKatz) :=
  K.comparison
example (Lp : Λ p) (K : KatzData p Lp) : K.W := K.m2core
example (Lp : Λ p) (K : KatzData p Lp) :
    ∃ κ₀ : K.Wˣ, (p : K.W) ^ 2 * ((κ₀ : K.W) * PowerSeries.coeff 2 K.LKatz - K.m2core)
      ∈ Ideal.span {(p : K.W) ^ 3} := K.grading_congr
example (Lp : Λ p) (K : KatzData p Lp) : ℚ := K.deltaE_local
example (Lp : Λ p) (K : KatzData p Lp) : Prop := K.NonvanishingOnDE
example (Lp : Λ p) (K : KatzData p Lp) :
    K.deltaE_local ≠ 0 → padicValRat p K.deltaE_local = 0 → K.NonvanishingOnDE :=
  K.resultant_link
example (Lp : Λ p) (K : KatzData p Lp) : IsLocalRing.ResidueField K.W := K.traceClass

/-! ## `criterionClass` (a def) and the bonus local-hom helper -/

example (Lp : Λ p) (K : KatzData p Lp) : IsLocalRing.ResidueField K.W := K.criterionClass
example (Lp : Λ p) (K : KatzData p Lp) :
    K.criterionClass = IsLocalRing.residue K.W K.m2core := rfl
example (Lp : Λ p) (K : KatzData p Lp) : IsLocalHom (algebraMap ℤ_[p] K.W) :=
  K.algMap_isLocalHom

/-! ## `SinnottHyp` — state a term *type* (hypothesis position only; not proved) -/

example (Lp : Λ p) (K : KatzData p Lp) : Prop := Nonempty (SinnottHyp p Lp K)
-- and its two fields have the intended shapes:
example (Lp : Λ p) (K : KatzData p Lp) (S : SinnottHyp p Lp K) :
    IsLocalRing.residue K.W K.m2core = K.traceClass := S.presentation
example (Lp : Λ p) (K : KatzData p Lp) (S : SinnottHyp p Lp K) :
    K.NonvanishingOnDE → K.traceClass ≠ 0 := S.nonvanishing

end T13Check

end
