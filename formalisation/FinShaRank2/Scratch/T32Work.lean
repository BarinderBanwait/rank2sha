import Mathlib
import FinShaRank2.Defs
import FinShaRank2.Interface.Global
import FinShaRank2.Statements
import FinShaRank2.Main.Dictionary

/-!
# T32 scratch — `prop:dictionary` (not audited, not root-imported)
-/

open PowerSeries

namespace FinShaRank2

section Route1

/-- Route 1: `c2norm_tie` → `spr_nondeg` → `shaOrd_tie`. -/
theorem t32_route1 (H : ClassicalInputs) {p : ℕ} [Fact p.Prime]
    (hsplit : p % 4 = 1) (hpS : p ∉ H.S) :
    IsPUnit (H.dataAt p Fact.out hsplit hpS).c2tilde
      ↔ ((H.dataAt p Fact.out hsplit hpS).height.heightNondeg
          ∧ IsPUnit (H.dataAt p Fact.out hsplit hpS).height.Reg_γ
          ∧ Subsingleton (H.dataAt p Fact.out hsplit hpS).selmer.ShaDual) := by
  have htie : (H.dataAt p Fact.out hsplit hpS).c2tilde
      = (H.dataAt p Fact.out hsplit hpS).height.c2norm :=
    (H.dataAt p Fact.out hsplit hpS).c2norm_tie.symm
  rw [htie, (H.dataAt p Fact.out hsplit hpS).height.spr_nondeg,
    (H.dataAt p Fact.out hsplit hpS).shaOrd_tie]

end Route1

#print axioms t32_route1
#print axioms FinShaRank2.prop_dictionary

end FinShaRank2
