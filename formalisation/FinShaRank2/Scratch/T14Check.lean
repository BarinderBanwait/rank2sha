import FinShaRank2.Interface.Global
import FinShaRank2.Interface.Certificates

/-!
# T14 acceptance scratch: destructure `PrimeData`, `ClassicalInputs`, `Certificates`

Not imported by the root module; excluded from the audit. Exercises **every**
field of the three T14 structures so that the field types (in particular the
three `PrimeData` tie-equations and the two digit certificates) are known to
compose. Also serves as the "how to destructure" cheat-sheet for T15.
-/

open PowerSeries

namespace FinShaRank2.Scratch

open FinShaRank2

/-- The board's mandated acceptance witness, plus a full field sweep of
`ClassicalInputs` and `Certificates`. -/
example (H : ClassicalInputs) (C : Certificates H) : True := by
  -- every `ClassicalInputs` field
  let _S : Finset ℕ := H.S
  let _dE : ℚ := H.deltaE
  let _t : ℚ := H.torsSqOverTam
  have _teq : H.torsSqOverTam = 1 := H.torsSqOverTam_eq
  let _dat := H.dataAt
  -- every `Certificates` field
  have _fn : 5 ∉ H.S := C.five_notin
  have _tn : 13 ∉ H.S := C.thirteen_notin
  have _a5 := C.a5
  have _a13 := C.a13
  have _c5 := C.c2_5
  have _c13 := C.c2_13
  trivial

/-- Full field sweep of `PrimeData` at a generic split prime, exercising the three
tie-equations. -/
example (p : ℕ) (hp : p.Prime) (h4 : p % 4 = 1) (H : ClassicalInputs)
    (hpS : p ∉ H.S) : True := by
  haveI : Fact p.Prime := ⟨hp⟩
  let D := H.dataAt p hp h4 hpS
  -- the four aggregated layers
  let _an : AnalyticData p h4 := D.analytic
  let _se : SelmerData p := D.selmer
  let _iw : IwasawaData p D.analytic.Lp D.selmer.SelDual := D.iwasawa
  let _he : HeightData p := D.height
  let _ka : KatzData p D.analytic.Lp := D.katz
  -- the three welded tie-equations
  have _c2 : D.height.c2norm
      = c2tilde ((PowerSeries.coeff 2 D.analytic.Lp : ℤ_[p]) : ℚ_[p])
          (((D.analytic.α : ℤ_[p]) : ℚ_[p])⁻¹) H.torsSqOverTam := D.c2norm_tie
  have _sha : IsPUnit D.height.shaOrd ↔ Subsingleton D.selmer.ShaDual := D.shaOrd_tie
  have _de : D.katz.deltaE_local = H.deltaE := D.deltaE_tie
  trivial

/-- Cheat-sheet for T15: pull the genuine analytic jet and Selmer duals out of a
`PrimeData` value; confirms the field-access paths downstream statements use. -/
example (p : ℕ) (hp : p.Prime) (h4 : p % 4 = 1) (H : ClassicalInputs)
    (hpS : p ∉ H.S) : Prop := by
  haveI : Fact p.Prime := ⟨hp⟩
  let D := H.dataAt p hp h4 hpS
  -- `Lp`, `coeff 2 Lp`, the Selmer/Sha duals, the corank target type
  let _Lp : Λ p := D.analytic.Lp
  let _c2coeff : ℤ_[p] := PowerSeries.coeff 2 D.analytic.Lp
  let _SelDual : Type := D.selmer.SelDual
  let _ShaDual : Type := D.selmer.ShaDual
  exact Subsingleton D.selmer.ShaDual

end FinShaRank2.Scratch
