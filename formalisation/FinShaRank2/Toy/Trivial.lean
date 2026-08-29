import FinShaRank2.Interface.Global
import FinShaRank2.Toy.Analytic
import FinShaRank2.Toy.Iwasawa
import FinShaRank2.Toy.Heights
import FinShaRank2.Toy.Katz

/-!
# Non-vacuity of `ClassicalInputs` (task T40): `FinShaRank2.ToyTrivial`

**The assumption surface of this formalization is consistent.** This file
assembles the four toy layers into

`ToyTrivial : ClassicalInputs`,

with *every field proved* — no incomplete proofs, no new axiom declarations, and
`#print axioms ToyTrivial` showing only `propext`, `Classical.choice`,
`Quot.sound`. A
skeptical referee's first question — "could `ClassicalInputs` be
contradictory, so that the main theorems are vacuous?" — is thereby answered
negatively by a Lean-kernel-checked construction (`TASK_BOARD.md` §1).

## The toy world, layer by layer

| datum | toy value | file |
|---|---|---|
| `S` | `∅` (so every split prime carries data) | here |
| `δ_E`, `(#tors)²/∏cᵥ` | `1`, `1` | here |
| `Lp` | `X²` | `Toy/Analytic.lean` |
| `a_p`, `α` | `2a` with `a² + b² = p`; Hensel unit root | `Toy/Analytic.lean` |
| `X` (Iwasawa) | `(Λ/(X))²` | `Toy/Iwasawa.lean` |
| `SelDual`, `ShaDual` | `ℤ_[p]²`, `PUnit` | `Toy/Iwasawa.lean` |
| `Reg_γ`, `shaOrd`, `heightNondeg` | `1`, `1`, `True` | `Toy/Heights.lean` |
| `W`, `LKatz`, `m2core` | `ℤ_[p]`, `X²`, `1` | `Toy/Katz.lean` |

This is a *toy* world: it is not the testbed curve, and no faithfulness claim is
made about it. Its only job is to witness satisfiability of the assumption
bundle. The complementary tripwire — that the assumptions alone do **not** force
the headline conclusion — is the anti-vacuity instance `ToySha` (task T41).

## Deviation from the board sketch

The board's original sketch used `a_p := 2`. That is incompatible with the
frozen `AnalyticData.ap_from_CM` field (`∃ π : GaussianInt, π.norm = p ∧
a_p = 2 Re π`), which at a general split `p` would force `p = 1 + b²`. The
amended toy uses `a_p := 2a` from the two-square decomposition of `p`; see the
module docstring of `Toy/Analytic.lean`.
-/

open PowerSeries

namespace FinShaRank2

namespace Toy

variable {p : ℕ} [Fact p.Prime]

/-- **Toy `PrimeData`** at a split prime `p`, with the three T14 tie-equations
discharged: the height proxy `c2norm` *is* the normalised analytic jet of
`Lp = X²`, the Ш-order proxy is a unit exactly as `ShaDual = PUnit` is trivial,
and the local `δ_E` is the global `1`. -/
noncomputable def toyPrimeData (p : ℕ) [Fact p.Prime] (hsplit : p % 4 = 1) :
    PrimeData p hsplit 1 1 where
  analytic := toyAnalytic hsplit (setup p hsplit)
  selmer := toySelmer p
  iwasawa := toyIwasawa p
  height := toyHeight (setup p hsplit).α (setup p hsplit).alpha_sub_one_unit
  katz := toyKatz p
  c2norm_tie := by
    have h2 : (PowerSeries.coeff 2 ((X : Λ p) ^ 2) : ℤ_[p]) = 1 := by
      rw [PowerSeries.coeff_X_pow]; norm_num
    show c2tilde (1 : ℚ_[p]) (((setup p hsplit).α : ℤ_[p]) : ℚ_[p])⁻¹ 1
        = c2tilde ((PowerSeries.coeff 2 ((X : Λ p) ^ 2) : ℤ_[p]) : ℚ_[p])
            ((((setup p hsplit).α : ℤ_[p]) : ℚ_[p])⁻¹) 1
    rw [h2, PadicInt.coe_one]
  shaOrd_tie := by
    constructor
    · intro _
      exact (inferInstance : Subsingleton PUnit)
    · intro _
      exact (norm_one : ‖(1 : ℚ_[p])‖ = 1)
  deltaE_tie := rfl

end Toy

/-- **Non-vacuity of the assumption surface (task T40).**

`ToyTrivial` is a *proved* instance of `ClassicalInputs`: the excluded set is
empty, the two global rationals are `1`, and every split prime carries the toy
per-prime bundle of `Toy.toyPrimeData`. Its existence shows that
`ClassicalInputs` is satisfiable, hence that the headline implications
`theorem … (H : ClassicalInputs) (C : Certificates H) : …` are not vacuous.

SOURCE: none — this is a construction, not an assumption.
PAPER:  `TASK_BOARD.md` §1 (trust story, non-vacuity).
STATUS: theorem (toy model). -/
noncomputable def ToyTrivial : ClassicalInputs where
  S := ∅
  deltaE := 1
  torsSqOverTam := 1
  torsSqOverTam_eq := rfl
  dataAt := fun p hp hsplit _ => @Toy.toyPrimeData p (Fact.mk hp) hsplit

end FinShaRank2
