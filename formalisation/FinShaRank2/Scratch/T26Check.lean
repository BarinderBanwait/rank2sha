import Mathlib
import FinShaRank2.Interface.Certificates
import FinShaRank2.Kernel.Normalization

/-!
# T26 contract checks (scratch, not audited)

Exercises `Kernel/Normalization.lean` against the **frozen** interface shapes:

1. **Certificate shape (T14 contract).** `Certificates.c2_5` / `Certificates.c2_13`
   are consumed verbatim by `isUnit_of_cert_five` / `isUnit_of_cert_thirteen`, with
   no adapter.
2. **`c2tilde` spelling (T11 gotcha).** `isPUnit_c2tilde_iff` /
   `isPUnit_c2tilde_iff_of_split` apply to the mandatory double-coercion spelling
   `c2tilde ((coeff 2 Lp : ℤ_[p]) : ℚ_[p]) (((α : ℤ_[p]) : ℚ_[p])⁻¹) tst` used by
   `PrimeData.c2norm_tie` (and by `Statements.PrimeData.c2tilde`).
3. **Non-anomality bridge.** `isPUnit_one_sub_alphaInv_of_split` applies to the
   `AnalyticData` fields `hasse`, `ap_from_CM`, `alpha_root` verbatim; the residual
   `p = 5 → a = −2` is vacuous away from `5` and discharged by `Certificates.a5`
   at `5`.
-/

open PowerSeries

namespace FinShaRank2Check

open FinShaRank2

/-! ### CHECK 1 — certificate shape, verbatim application -/

/-- `C.c2_5` feeds `isUnit_of_cert_five` directly. -/
example (H : ClassicalInputs) (C : Certificates H) :
    IsUnit (PowerSeries.coeff 2
      (H.dataAt 5 (by norm_num) (by norm_num) C.five_notin).analytic.Lp) :=
  isUnit_of_cert_five C.c2_5

/-- `C.c2_13` feeds `isUnit_of_cert_thirteen` directly. -/
example (H : ClassicalInputs) (C : Certificates H) :
    IsUnit (PowerSeries.coeff 2
      (H.dataAt 13 (by norm_num) (by norm_num) C.thirteen_notin).analytic.Lp) :=
  isUnit_of_cert_thirteen C.c2_13

/-! ### CHECK 3 — the non-anomality bridge on `AnalyticData` fields -/

/-- The bridge consumes `AnalyticData`'s `hasse`, `ap_from_CM`, `alpha_root`
verbatim, plus the residual `p = 5 → ap = −2`. -/
example {p : ℕ} [Fact p.Prime] {hsplit : p % 4 = 1} (D : AnalyticData p hsplit)
    (h5 : p = 5 → D.ap = -2) :
    IsPUnit ((1 : ℚ_[p]) - ((D.α : ℤ_[p]) : ℚ_[p])⁻¹) :=
  isPUnit_one_sub_alphaInv_of_split hsplit D.hasse D.ap_from_CM D.alpha_root h5

/-- Away from `5` the residual side condition is vacuous (illustrated at `p = 13`). -/
example (H : ClassicalInputs) (C : Certificates H) :
    IsPUnit ((1 : ℚ_[13])
        - (((H.dataAt 13 (by norm_num) (by norm_num) C.thirteen_notin).analytic.α : ℤ_[13])
            : ℚ_[13])⁻¹) :=
  isPUnit_one_sub_alphaInv_of_split (by norm_num)
    (H.dataAt 13 (by norm_num) (by norm_num) C.thirteen_notin).analytic.hasse
    (H.dataAt 13 (by norm_num) (by norm_num) C.thirteen_notin).analytic.ap_from_CM
    (H.dataAt 13 (by norm_num) (by norm_num) C.thirteen_notin).analytic.alpha_root
    (by omega)

/-- At `p = 5` the residual side condition is discharged by the certificate `C.a5`. -/
example (H : ClassicalInputs) (C : Certificates H) :
    IsPUnit ((1 : ℚ_[5])
        - (((H.dataAt 5 (by norm_num) (by norm_num) C.five_notin).analytic.α : ℤ_[5])
            : ℚ_[5])⁻¹) :=
  isPUnit_one_sub_alphaInv_of_split (by norm_num)
    (H.dataAt 5 (by norm_num) (by norm_num) C.five_notin).analytic.hasse
    (H.dataAt 5 (by norm_num) (by norm_num) C.five_notin).analytic.ap_from_CM
    (H.dataAt 5 (by norm_num) (by norm_num) C.five_notin).analytic.alpha_root
    (fun _ => C.a5)

/-! ### CHECK 2 — the `c2tilde` double-coercion spelling -/

/-- `isPUnit_c2tilde_iff_of_split` applies to the T14/T15 spelling verbatim. -/
example {p : ℕ} [Fact p.Prime] (H : ClassicalInputs) (hsplit : p % 4 = 1) (hpS : p ∉ H.S)
    (h5 : p = 5 → (H.dataAt p Fact.out hsplit hpS).analytic.ap = -2) :
    IsPUnit (c2tilde
        ((PowerSeries.coeff 2 (H.dataAt p Fact.out hsplit hpS).analytic.Lp : ℤ_[p]) : ℚ_[p])
        ((((H.dataAt p Fact.out hsplit hpS).analytic.α : ℤ_[p]) : ℚ_[p])⁻¹)
        H.torsSqOverTam)
      ↔ IsUnit (PowerSeries.coeff 2 (H.dataAt p Fact.out hsplit hpS).analytic.Lp) :=
  isPUnit_c2tilde_iff_of_split _ _ hsplit
    (H.dataAt p Fact.out hsplit hpS).analytic.hasse
    (H.dataAt p Fact.out hsplit hpS).analytic.ap_from_CM
    (H.dataAt p Fact.out hsplit hpS).analytic.alpha_root
    h5 H.torsSqOverTam_eq

/-- The same, routed through the frozen tie-equation `PrimeData.c2norm_tie`: the
height-side proxy `c2norm` is a `p`-adic unit iff `coeff 2 Lp` is a unit. -/
example {p : ℕ} [Fact p.Prime] (H : ClassicalInputs) (hsplit : p % 4 = 1) (hpS : p ∉ H.S)
    (h5 : p = 5 → (H.dataAt p Fact.out hsplit hpS).analytic.ap = -2) :
    IsPUnit (H.dataAt p Fact.out hsplit hpS).height.c2norm
      ↔ IsUnit (PowerSeries.coeff 2 (H.dataAt p Fact.out hsplit hpS).analytic.Lp) := by
  rw [(H.dataAt p Fact.out hsplit hpS).c2norm_tie]
  exact isPUnit_c2tilde_iff_of_split _ _ hsplit
    (H.dataAt p Fact.out hsplit hpS).analytic.hasse
    (H.dataAt p Fact.out hsplit hpS).analytic.ap_from_CM
    (H.dataAt p Fact.out hsplit hpS).analytic.alpha_root
    h5 H.torsSqOverTam_eq

/-! ### End-to-end: certificate ⟹ `c̃₂(5)` is a `p`-adic unit (the T34 shape) -/

/-- The full T26 contribution to `cor:sha5`: digit certificate ⟹ `IsUnit c₂(5)` ⟹
`IsPUnit c̃₂(5)`, through the frozen `c2norm` proxy. -/
example (H : ClassicalInputs) (C : Certificates H) :
    IsPUnit (H.dataAt 5 (by norm_num) (by norm_num) C.five_notin).height.c2norm := by
  rw [(H.dataAt 5 (by norm_num) (by norm_num) C.five_notin).c2norm_tie]
  exact (isPUnit_c2tilde_iff_of_split _ _ (by norm_num)
      (H.dataAt 5 (by norm_num) (by norm_num) C.five_notin).analytic.hasse
      (H.dataAt 5 (by norm_num) (by norm_num) C.five_notin).analytic.ap_from_CM
      (H.dataAt 5 (by norm_num) (by norm_num) C.five_notin).analytic.alpha_root
      (fun _ => C.a5) H.torsSqOverTam_eq).mpr (isUnit_of_cert_five C.c2_5)

/-- The same at `p = 13` (`cor:sha13`). -/
example (H : ClassicalInputs) (C : Certificates H) :
    IsPUnit (H.dataAt 13 (by norm_num) (by norm_num) C.thirteen_notin).height.c2norm := by
  rw [(H.dataAt 13 (by norm_num) (by norm_num) C.thirteen_notin).c2norm_tie]
  exact (isPUnit_c2tilde_iff_of_split _ _ (by norm_num)
      (H.dataAt 13 (by norm_num) (by norm_num) C.thirteen_notin).analytic.hasse
      (H.dataAt 13 (by norm_num) (by norm_num) C.thirteen_notin).analytic.ap_from_CM
      (H.dataAt 13 (by norm_num) (by norm_num) C.thirteen_notin).analytic.alpha_root
      (by omega) H.torsSqOverTam_eq).mpr (isUnit_of_cert_thirteen C.c2_13)

end FinShaRank2Check
