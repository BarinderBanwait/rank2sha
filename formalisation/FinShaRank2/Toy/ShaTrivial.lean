import FinShaRank2.Interface.Global
import FinShaRank2.Toy.EK
import FinShaRank2.Toy.ShaAnalytic
import FinShaRank2.Toy.ShaIwasawa
import FinShaRank2.Toy.ShaHeights
import FinShaRank2.Toy.ShaKatz

/-!
# Anti-vacuity of `ClassicalInputs` (task T41): `FinShaRank2.ToySha`

**The assumption surface of this formalization does not smuggle in the
conclusion.** Task T40 (`Toy/Trivial.lean`) built `ToyTrivial : ClassicalInputs`
and thereby showed the assumption bundle is *consistent*. This file is the
complementary tripwire for `TASK_BOARD.md` §2 convention 4 (no conclusion
leakage): it builds a **second** proved instance

`ToySha : ClassicalInputs`

in which the headline conclusion **fails** — `ShaDual` is not subsingleton, the
Iwasawa μ-invariant does not vanish, and `λ_an ≠ 2`. Hence no strengthening of
the interface fields can be entailing those conclusions; the numerical `c₂`
certificate is genuinely load-bearing rather than decorative. If someone later
strengthens an interface field so that it does entail the conclusion, this file
stops compiling, which is exactly its job.

## The anti-vacuity world, layer by layer

| datum | value | file |
|---|---|---|
| `S` | `∅` (so every split prime carries data) | here |
| `(#tors)²/∏cᵥ` | `1` | here |
| `ek` (`D_E`, `𝓡_E`, `v_𝔭`, `supp`) | as `ToyTrivial` | `Toy/EK.lean` |
| `Lp` | `C p · X²` (so `coeff 2 Lp = p`, a **non-unit**) | `Toy/ShaAnalytic.lean` |
| `a_p`, `α` | `2a` with `a² + b² = p`; Hensel unit root (as T40) | `Toy/ShaAnalytic.lean` |
| `X` (Iwasawa) | `Λ/(X) × Λ/(X) × Λ/(C p)` | `Toy/ShaIwasawa.lean` |
| `SelDual`, `ShaDual` | `ℤ_[p]² × ℤ_[p]/(p)`, `ℤ_[p]/(p)` | `Toy/ShaIwasawa.lean` |
| `Reg_γ`, `shaOrd`, `heightNondeg` | `1`, `p`, `True` | `Toy/ShaHeights.lean` |
| `W`, `LKatz`, `m2core` | `ℤ_[p]`, `C p · X²`, `p` | `Toy/ShaKatz.lean` |

Every value here is *forced*, not chosen: `shaOrd_tie` forces `shaOrd` to be a
non-unit once `ShaDual` is nontrivial; `spr_padicBSD` and `c2norm_tie` then force
`coeff 2 Lp` to be a non-unit at the (non-anomalous) toy prime; and
`rubin_structure` forces the elementary divisors of `X` to multiply to `Lp`,
which together with `π_surj` (rank two) and a nontrivial `ShaDual` pins the
multiset to `(X, X, C p)`.

This is a *toy* world: it is not the testbed curve, and no faithfulness claim is
made about it. Its only job is to witness that the assumption bundle does not
entail the conclusion. What excludes this world is the numerical `c₂` datum:
`toySha_fails_c2_5_certificate` shows the seven computed `5`-adic digits of
`c₂(5)` for the testbed curve are not the digits of `coeff 2 (shaLp 5) = 5`.
-/

open PowerSeries

namespace FinShaRank2

namespace Toy

variable {p : ℕ} [Fact p.Prime]

/-- **Anti-vacuity `PrimeData`** at a split prime `p`, with the two tie-equations
discharged: the height proxy `c2norm` *is* the normalised analytic jet of
`Lp = C p · X²`; and the Ш-order proxy `shaOrd = p` is a non-unit exactly as
`ShaDual = ℤ_[p]/(p)` is nontrivial (`shaOrd_tie` is an iff between two false
statements). -/
noncomputable def shaPrimeData (p : ℕ) [Fact p.Prime] (hsplit : p % 4 = 1) :
    PrimeData p hsplit 1 where
  analytic := shaAnalytic hsplit (setup p hsplit)
  selmer := shaSelmer p
  iwasawa := shaIwasawa p
  height := shaHeight (setup p hsplit).α (setup p hsplit).alpha_sub_one_unit
  katz := shaKatz p
  c2norm_tie := by
    show c2tilde (((p : ℤ_[p]) : ℚ_[p])) ((((setup p hsplit).α : ℤ_[p]) : ℚ_[p]))⁻¹ 1
        = c2tilde ((PowerSeries.coeff 2 (shaLp p) : ℤ_[p]) : ℚ_[p])
            (((((setup p hsplit).α : ℤ_[p]) : ℚ_[p]))⁻¹) 1
    rw [coeff_two_shaLp]
  shaOrd_tie := iff_of_false not_isPUnit_p not_subsingleton_ShaK

/-! ### The two failures of the headline conclusion -/

/-- Every coefficient of `Lp = C p · X²` is divisible by `p`, so the Iwasawa
μ-invariant of the anti-vacuity L-function does **not** vanish. -/
theorem not_muZero_shaLp : ¬ MuZero (shaLp p) := by
  rintro ⟨n, hn⟩
  rw [shaLp, coeff_C_mul] at hn
  exact mem_nonunits_iff.mp PadicInt.p_nonunit (isUnit_of_mul_isUnit_left hn)

/-- The analytic λ-invariant of `Lp = C p · X²` is the junk value `0`, not `2`
(the set of unit-coefficient indices is empty). -/
theorem lambdaAn_shaLp : lambdaAn (shaLp p) = 0 := by
  have hempty : {n | IsUnit (PowerSeries.coeff n (shaLp p))} = (∅ : Set ℕ) := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hn
    rw [shaLp, coeff_C_mul] at hn
    exact mem_nonunits_iff.mp PadicInt.p_nonunit (isUnit_of_mul_isUnit_left hn)
  rw [lambdaAn, hempty]
  exact Nat.sInf_empty

end Toy

/-- **The anti-vacuity instance (task T41).**

`ToySha` is a *proved* instance of `ClassicalInputs` — every field discharged, no
incomplete proofs, no new axiom declarations — in which the headline conclusion
`Ш(E/ℚ)[p^∞] = 0` (dual side: `Subsingleton ShaDual`) is **false at every split
prime**. It witnesses that `ClassicalInputs` alone does not entail the paper's
conclusions.

SOURCE: none — this is a construction, not an assumption.
PAPER:  `TASK_BOARD.md` §1 (trust story), §2 conv. 4 (no conclusion leakage).
STATUS: theorem (toy model). -/
noncomputable def ToySha : ClassicalInputs where
  S := ∅
  ek := Toy.toyEK
  torsSqOverTam := 1
  torsSqOverTam_eq := rfl
  dataAt := fun p hp hsplit _ => @Toy.shaPrimeData p (Fact.mk hp) hsplit
  notAnomalous := fun p hp hsplit _ =>
    @Toy.Setup.ap_ne_one p (Fact.mk hp) (@Toy.setup p (Fact.mk hp) hsplit)

/-- **`ToySha` fails the headline conclusion at every split prime.** Three
conclusions are false in this world: Ш is nontrivial, `μ ≠ 0`, and
`λ_an ≠ 2`. -/
theorem toySha_conclusions_fail (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1)
    (hpS : p ∉ ToySha.S) :
    letI : Fact p.Prime := ⟨hp⟩
    ¬ Subsingleton (ToySha.dataAt p hp hsplit hpS).selmer.ShaDual
      ∧ ¬ MuZero (ToySha.dataAt p hp hsplit hpS).analytic.Lp
      ∧ lambdaAn (ToySha.dataAt p hp hsplit hpS).analytic.Lp ≠ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨Toy.not_subsingleton_ShaK, Toy.not_muZero_shaLp, ?_⟩
  rw [show (ToySha.dataAt p hp hsplit hpS).analytic.Lp = Toy.shaLp p from rfl,
    Toy.lambdaAn_shaLp]
  norm_num

/-- **The anti-vacuity theorem (task T41).**

The classical-inputs interface does **not** entail the triviality of Ш: there is
no proof of `Subsingleton ShaDual` from `H : ClassicalInputs` and splitness
alone. Witnessed by `ToySha` (at `p = 5`, and in fact at every split prime, by
`toySha_conclusions_fail`).

Together with T40's `ToyTrivial` (which shows the same interface *is*
satisfiable) this pins the epistemic status of the assumption surface: it is
consistent, and it is not question-begging. What closes the gap is the numerical
`c₂` datum, which `ToySha` fails (`toySha_fails_c2_5_certificate`).

SOURCE: none — this is a construction, not an assumption.
PAPER:  `TASK_BOARD.md` §1, §2 conv. 4.
STATUS: theorem (tripwire). -/
theorem interface_does_not_force_sha_trivial :
    ¬ ∀ (H : ClassicalInputs) (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1) (hpS : p ∉ H.S),
        letI : Fact p.Prime := ⟨hp⟩
        Subsingleton (H.dataAt p hp hsplit hpS).selmer.ShaDual := by
  intro h
  exact (toySha_conclusions_fail 5 (by norm_num) (by norm_num) (Finset.notMem_empty 5)).1
    (h ToySha 5 (by norm_num) (by norm_num) (Finset.notMem_empty 5))

/-- **`ToySha` fails the computed `5`-adic jet certificate.**

The certificate is the seven-digit congruence
`toZModPow 7 (coeff 2 Lp₅) = 1 + 4·5 + 3·5² + 5³ + 5⁵ + 5⁶ mod 5⁷`, whose leading
`5`-adic digit is `1`. In the anti-vacuity world `coeff 2 (shaLp 5) = 5`, whose
leading digit is `0`, so the congruence is false. This is what excludes `ToySha`,
and hence what makes the numerical `c₂` datum load-bearing rather than
decorative: `interface_does_not_force_sha_trivial` shows the interface alone does
not give the conclusion, and this lemma identifies the datum that does.

The Frobenius-trace datum `a₅ = −2` fails here too, since the toy `a_p = 2a` is
positive; only the jet digits are used below.

SOURCE: none — this is a computation about the toy instance.
PAPER:  none. The digits on the right are this project's computation of `c₂(5)`
        for the testbed curve; paper v1 displayed them, and paper v2 dropped the
        display together with the anchor corollaries it served
        (`legacy/Anchors.lean`). `TASK_BOARD.md` §1: the numerics are
        load-bearing.
STATUS: theorem (toy model). -/
theorem toySha_fails_c2_5_certificate :
    letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    PadicInt.toZModPow 7 (PowerSeries.coeff 2 (Toy.shaLp 5))
      ≠ ((1 + 4 * 5 + 3 * 5 ^ 2 + 5 ^ 3 + 5 ^ 5 + 5 ^ 6 : ℤ) : ZMod (5 ^ 7)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro hcert
  have key : PadicInt.toZModPow 7 (PowerSeries.coeff 2 (Toy.shaLp 5))
      = ((5 : ℕ) : ZMod (5 ^ 7)) := by
    rw [Toy.coeff_two_shaLp, map_natCast]
  have h : ((5 : ℕ) : ZMod (5 ^ 7))
      = ((1 + 4 * 5 + 3 * 5 ^ 2 + 5 ^ 3 + 5 ^ 5 + 5 ^ 6 : ℤ) : ZMod (5 ^ 7)) :=
    key.symm.trans hcert
  revert h
  decide

/-- Sanity check for the audit: `ToySha` really is a `ClassicalInputs`. -/
noncomputable example : ClassicalInputs := ToySha

end FinShaRank2
