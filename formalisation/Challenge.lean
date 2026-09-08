import Mathlib
import FinShaRank2.Defs
import FinShaRank2.Statements

/-!
# Comparator challenge: the statements

This module is the *Challenge* half of a `comparator` run (see
`https://github.com/leanprover/comparator`). It states the five theorems the
formalisation is judged on, each with `sorry`, and imports only the trusted
part of the project: `Defs.lean`, the six files under `Interface/`, and
`Statements.lean`. Nothing under `Kernel/`, `Main/` or `Toy/` is in its
import closure.

The *Solution* module (`Solution.lean`) imports the proofs. Comparator
builds both, exports both with `lean4export`, and accepts only if

1. every declaration occurring in the statements below is identical in the
   Challenge and Solution environments, so the proofs cannot have redefined
   anything the statements depend on;
2. the proofs use no axiom beyond `propext`, `Quot.sound` and
   `Classical.choice`;
3. the exported proof terms are accepted by the Lean kernel, replayed from an
   empty environment, and by the external kernel `nanoda`.

What comparator does not check, and cannot, is that the statements below and
the structures they quantify over say what the paper says. That is the human
task described in the README; it is confined to the import closure of this
file.

The statements are copied verbatim from `Main/Lemma41.lean`,
`Main/Consequence.lean`, `Main/Dictionary.lean` and `Toy/ShaTrivial.lean`.
The configuration is `scripts/comparator.json`.
-/

open PowerSeries

namespace FinShaRank2

/-- Lemma 3.1(1): the constant term of `L_p(E,T)` vanishes. -/
theorem c0_eq_zero {p : ℕ} [Fact p.Prime] {hsplit : p % 4 = 1}
    (A : AnalyticData p hsplit) : constantCoeff A.Lp = 0 := sorry

/-- Lemma 3.1(2): the linear term of `L_p(E,T)` vanishes. -/
theorem c1_eq_zero {p : ℕ} [Fact p.Prime] {hsplit : p % 4 = 1}
    (A : AnalyticData p hsplit) : coeff 1 A.Lp = 0 := sorry

/-- Theorem A (Theorem 3.8): at a split prime `p ∉ S` with `c̃₂(p)` a `p`-adic
unit, `μ = 0`, `λ = 2`, the Selmer corank is `2`, and `Ш(E/ℚ)[p^∞] = 0`. -/
theorem prop_consequence (H : ClassicalInputs) {p : ℕ} [Fact p.Prime]
    (hsplit : p % 4 = 1) (hpS : p ∉ H.S)
    (hc2 : IsPUnit (H.dataAt p Fact.out hsplit hpS).c2tilde) :
    MuZero (H.dataAt p Fact.out hsplit hpS).analytic.Lp
      ∧ lambdaAn (H.dataAt p Fact.out hsplit hpS).analytic.Lp = 2
      ∧ Module.finrank ℤ_[p] (H.dataAt p Fact.out hsplit hpS).selmer.SelDual = 2
      ∧ Subsingleton (H.dataAt p Fact.out hsplit hpS).selmer.ShaDual := sorry

/-- Proposition 4.2: the unit condition on `c̃₂(p)` is equivalent to the
conjunction of height nondegeneracy, `v_p(Reg_γ) = 0`, and `Ш(E/ℚ)[p^∞] = 0`. -/
theorem prop_dictionary (H : ClassicalInputs) {p : ℕ} [Fact p.Prime]
    (hsplit : p % 4 = 1) (hpS : p ∉ H.S) :
    IsPUnit (H.dataAt p Fact.out hsplit hpS).c2tilde
      ↔ ((H.dataAt p Fact.out hsplit hpS).height.heightNondeg
          ∧ IsPUnit (H.dataAt p Fact.out hsplit hpS).height.Reg_γ
          ∧ Subsingleton (H.dataAt p Fact.out hsplit hpS).selmer.ShaDual) := sorry

/-- Anti-vacuity: the assumptions alone do not force `Ш(E/ℚ)[p^∞] = 0`. -/
theorem interface_does_not_force_sha_trivial :
    ¬ ∀ (H : ClassicalInputs) (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1) (hpS : p ∉ H.S),
        letI : Fact p.Prime := ⟨hp⟩
        Subsingleton (H.dataAt p hp hsplit hpS).selmer.ShaDual := sorry

end FinShaRank2
