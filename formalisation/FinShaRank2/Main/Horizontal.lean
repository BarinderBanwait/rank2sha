import Mathlib
import FinShaRank2.Interface.Global
import FinShaRank2.Main.Consequence
import FinShaRank2.Statements

/-!
# Corollary B (Corollary 4.10) — horizontal control along the split primes

> **Corollary B (Corollary 4.10).** *Let `E/ℚ` have CM by the maximal*
> *order `𝒪_K` of an imaginary quadratic field `K`, with `rank E(ℚ) = 2`,*
> *`L(E,1) = 0` and `w(E) = +1` and with finitely many anomalous split primes, and*
> *assume Conjecture 4.7. Then horizontal control (Definition*
> *Definition 2.1) holds for `E` along the split primes of `K`.*

The paper's proof has two steps: every condition defining `S_E` other than
anomalousness excludes only finitely many split primes, so `S_E` is finite; and
Conjecture 4.7 supplies the hypothesis of Theorem A (Theorem 4.9) at all but finitely many
split `p`. Only the second step has a counterpart here — see point 2 below.

With this file the paper's three lettered results are all formalised: Corollary B
here, Theorem A as `prop_consequence` (`Main/Consequence.lean`), Theorem C as
`thm_reduction` (`Main/Reduction.lean`).

## Translation conventions

* "horizontal control for `E` along a set `𝒫`" ↦ `HorizontalControl P shaVanishes`
  (`Statements.lean`), which unfolds to the finiteness of
  `{p | p ∈ P ∧ ¬ shaVanishes p}`.
* "the split primes of `K`" ↦ `{p | p.Prime ∧ p % 4 = 1}`. Throughout the project
  `K = ℚ(i)`, where a prime splits iff `p ≡ 1 (mod 4)`; `p % 4 = 1` is the same
  condition as the binder `hsplit` of every other statement.
* "`Ш(E/ℚ)[p] = 0`" ↦ `Subsingleton (…).selmer.ShaDual` (dual side).
  See point 1 below.
* Conjecture 4.7 ↦ the hypothesis `hweak : ConjWeak H` (`Statements.lean`).
* The `Fact p.Prime` instance that the `PrimeData` projections require is supplied
  inside the predicate from the binder `hp`, as in `ConjWeak`. Without it the
  projection `.selmer` does not elaborate: `p` is bound by the predicate, so no
  instance is in scope.

## Three points where this differs from the paper

1. **`Ш[p]` versus `Ш[p^∞]`.** Definition 2.1 concludes `Ш(E/ℚ)[p] = 0`, while
   the predicate supplied here is `Subsingleton (…).selmer.ShaDual`, which renders
   `Ш(E/ℚ)[p^∞] = 0` (dual side) and so is stronger. What is proved therefore implies
   what Definition 2.1 states, not the other way round. The `HorizontalControl`
   docstring in `Statements.lean` records the same point at the definition.

2. **Finiteness of `S_E` is free here.** The paper's `S_E` is a set that can be
   infinite, and the hypothesis "finitely many anomalous split primes" is what
   makes it finite: every other condition defining `S_E` excludes only finitely
   many split primes. In this encoding `ClassicalInputs.S : Finset ℕ` is finite by
   construction, and `ClassicalInputs.notAnomalous` puts every anomalous split
   prime inside `S`. So neither the hypothesis nor the first step of the paper's
   proof has a counterpart in `cor_horizontal`. This is a simplification the
   encoding makes, not something proved.

3. **The curve-level hypotheses are carried by `H`.** CM by the maximal order,
   `rank E(ℚ) = 2`, `L(E,1) = 0` and `w(E) = +1` are properties of the fixed curve,
   held by `H : ClassicalInputs` and by the per-prime bundles `H.dataAt` supplies.
   They are not restated in the Lean statement. This is the standing convention of
   the project and applies to `prop_consequence` and `thm_reduction` equally.

Paper statements rendered here: Corollary B, Definition 2.1,
Conjecture 4.7, Theorem A, (10).
-/

namespace FinShaRank2

/-- **Corollary B (Corollary 4.10)** — horizontal control for `E` along the split
primes of `K`, conditional on Conjecture 4.7.

> *Let `E/ℚ` have CM by the maximal order `𝒪_K` of an imaginary quadratic field*
> *`K`, with `rank E(ℚ) = 2`, `L(E,1) = 0` and `w(E) = +1` and with finitely many*
> *anomalous split primes, and assume Conjecture 4.7. Then horizontal*
> *control (Definition 2.1) holds for `E` along the split primes of*
> *`K`.*

Assembly route. `ConjWeak H` supplies a finite set `T` such that every split
`p ∉ H.S` outside `T` has `IsPUnit (…).c2tilde`; `prop_consequence` turns that into
`Subsingleton (…).selmer.ShaDual` at each such `p`. The set of split primes at
which the per-prime predicate fails is therefore contained in `T`, which is finite.
At `p ∈ H.S` the predicate holds vacuously — there is no `hpS : p ∉ H.S` to supply
— so `H.S` does not enter the bound.

`hweak` is the paper's own hypothesis for this corollary and is the only
conjectural hypothesis of the statement. `ConjEK` and `SinnottHyp` do not appear.

TRANSLATION: see the module docstring (split primes as `p % 4 = 1`; dual-side Ш,
which is `Ш[p^∞] = 0` where the paper asks for `Ш[p] = 0`; finiteness of `S`
by construction). -/
theorem cor_horizontal (H : ClassicalInputs) (hweak : ConjWeak H) :
    HorizontalControl {p | p.Prime ∧ p % 4 = 1}
      (fun p ↦ ∀ (hp : p.Prime) (hsplit : p % 4 = 1) (hpS : p ∉ H.S),
        have : Fact p.Prime := ⟨hp⟩
        Subsingleton (H.dataAt p hp hsplit hpS).selmer.ShaDual) := by
  obtain ⟨T, hT⟩ := hweak
  refine Set.Finite.subset T.finite_toSet ?_
  intro p hp
  by_contra hpT
  refine hp.2 ?_
  intro hprime hsplit hpS
  have : Fact p.Prime := ⟨hprime⟩
  exact (prop_consequence H hsplit hpS
    (hT p hprime hsplit hpS fun h ↦ hpT (Finset.mem_coe.mpr h))).2.2.2

end FinShaRank2
