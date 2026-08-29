import Mathlib
import FinShaRank2.Defs
import FinShaRank2.Interface.Global
import FinShaRank2.Statements

/-!
# `prop:dictionary` — the height/analytic dictionary (task T32)

Frozen headline signature (T15 statement freeze; `TASK_BOARD.md` §2 conv. 7).
The proof is supplied by task T32.

> **Proposition (Dictionary, `prop:dictionary`).** *Let `p ∉ S` be a non-anomalous
> split prime. The following are equivalent:*
> *(1) `c̃₂(p) ∈ ℤ_p^×`;*
> *(2) the cyclotomic `p`-adic height pairing on `E(ℚ)` is nondegenerate with*
> *`v_p(Reg_γ) = 0`, and `Ш(E/ℚ)[p^∞] = 0`.*

## Translation conventions (`TASK_BOARD.md` §2)

* `c̃₂(p) ∈ ℤ_p^×` ↦ `IsPUnit (…).c2tilde` (`Defs.IsPUnit`, `‖·‖ = 1` on `ℚ_[p]`,
  applied to the normalised second jet of `Statements.lean`).
* "the cyclotomic `p`-adic height pairing on `E(ℚ)` is nondegenerate" ↦ the opaque
  `HeightData` predicate `(…).height.heightNondeg`.
* `v_p(Reg_γ) = 0` ↦ `IsPUnit (…).height.Reg_γ`, i.e. `‖Reg_γ‖ = 1`. This is the
  same content: `HeightData.reg_integral` gives `‖Reg_γ‖ ≤ 1`, so norm one is
  exactly valuation zero. Phrasing it as `IsPUnit` matches the interface field
  `HeightData.spr_nondeg` verbatim, so no valuation/norm adapter is needed.
* `Ш(E/ℚ)[p^∞] = 0` ↦ `Subsingleton (…).selmer.ShaDual` (conv. 1, dual side).
* "split `p ∉ S`" ↦ the binders `hsplit : p % 4 = 1`, `hpS : p ∉ H.S`.

## Why no non-anomality hypothesis appears

The paper states the dictionary at non-anomalous `p` because its proof routes
through `prop:consequence` and `prop:normalisation`. Against the frozen
interface, however, both directions are available from the Schneider/Perrin-Riou
consequence-forms alone:

* `PrimeData.c2norm_tie` identifies `(…).height.c2norm` with the normalised jet
  `(…).c2tilde` **definitionally** (T14 tie-equation), so (1) is a statement about
  the height-side proxy;
* `HeightData.spr_nondeg : IsPUnit c2norm ↔ (heightNondeg ∧ IsPUnit Reg_γ ∧
  IsPUnit shaOrd)` is the packaged leading-term theorem, and
* `PrimeData.shaOrd_tie : IsPUnit shaOrd ↔ Subsingleton ShaDual` is the T13/T14
  proxy-meaning assignment.

No anomality-sensitive step (`prop:normalisation`, which converts between
`c̃₂` and `c₂`) is needed, so no `h5`/non-anomality hypothesis is carried here.
This is a *strengthening* relative to the paper's statement, not a weakening: the
formal proposition holds at every split `p ∉ S`. T32 may instead route through
`spr_padicBSD` + `reg_integral` + `sha_integral` (`‖c2norm‖ = ‖Reg_γ‖ · ‖shaOrd‖`
with both factors of norm `≤ 1`, so the product is a unit iff both are), which is
the valuation-arithmetic route sketched on the board; both routes are open and the
signature is agnostic between them.

Paper labels rendered here: `prop:dictionary`, `eq:padicbsd`.
-/

open PowerSeries

namespace FinShaRank2

/-- **`prop:dictionary`** at a split prime `p ∉ H.S`.

> *The following are equivalent: (1) `c̃₂(p) ∈ ℤ_p^×`; (2) the cyclotomic `p`-adic*
> *height pairing on `E(ℚ)` is nondegenerate with `v_p(Reg_γ) = 0`, and*
> *`Ш(E/ℚ)[p^∞] = 0`.*

Direction `→` is the paper's (1) ⇒ (2) and direction `←` its (2) ⇒ (1); the
right-hand conjunction is written in the field order of
`HeightData.spr_nondeg` (nondegeneracy, regulator, Ш) so that T32's proof is a
rewrite along `PrimeData.c2norm_tie` followed by `spr_nondeg` and
`PrimeData.shaOrd_tie`.

`v_p(Reg_γ) = 0` is rendered `IsPUnit (…).height.Reg_γ`; see the module docstring
for why that is the same statement and why no non-anomality hypothesis is
carried.

TRANSLATION: `c̃₂(p) ∈ ℤ_p^×` ↦ `IsPUnit (…).c2tilde`; "nondegenerate" ↦
`heightNondeg`; `v_p(Reg_γ) = 0` ↦ `IsPUnit Reg_γ`; `Ш(E/ℚ)[p^∞] = 0` ↦
`Subsingleton ShaDual`. -/
theorem prop_dictionary (H : ClassicalInputs) {p : ℕ} [Fact p.Prime]
    (hsplit : p % 4 = 1) (hpS : p ∉ H.S) :
    IsPUnit (H.dataAt p Fact.out hsplit hpS).c2tilde
      ↔ ((H.dataAt p Fact.out hsplit hpS).height.heightNondeg
          ∧ IsPUnit (H.dataAt p Fact.out hsplit hpS).height.Reg_γ
          ∧ Subsingleton (H.dataAt p Fact.out hsplit hpS).selmer.ShaDual) := by
  -- Step 1 (`PrimeData.c2norm_tie`): the height-side proxy `c2norm` *is* the
  -- normalised analytic jet `c̃₂(p)`, so (1) is a statement about `c2norm`.
  have htie : (H.dataAt p Fact.out hsplit hpS).c2tilde
      = (H.dataAt p Fact.out hsplit hpS).height.c2norm :=
    (H.dataAt p Fact.out hsplit hpS).c2norm_tie.symm
  -- Step 2 (`HeightData.spr_nondeg`, the packaged Schneider/Perrin-Riou
  -- leading-term theorem) and Step 3 (`PrimeData.shaOrd_tie`, the T13/T14
  -- proxy-meaning assignment) then rewrite the goal into the stated form.
  rw [htie, (H.dataAt p Fact.out hsplit hpS).height.spr_nondeg,
    (H.dataAt p Fact.out hsplit hpS).shaOrd_tie]

end FinShaRank2
