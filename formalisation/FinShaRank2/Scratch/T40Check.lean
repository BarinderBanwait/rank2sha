import FinShaRank2.Toy.Trivial

/-!
# T40 acceptance harness (not imported by the root module)

Checks that every toy layer instance and the assembled `ToyTrivial` typecheck
and are axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only).
-/

namespace FinShaRank2

-- acceptance: the deliverable typechecks at the declared type
noncomputable example : ClassicalInputs := ToyTrivial

section Layers

variable {p : ℕ} [Fact p.Prime] (hsplit : p % 4 = 1)

noncomputable example : AnalyticData p hsplit := Toy.toyAnalytic hsplit (Toy.setup p hsplit)
noncomputable example : SelmerData p := Toy.toySelmer p
noncomputable example : IwasawaData p ((PowerSeries.X : Λ p) ^ 2) (Fin 2 → ℤ_[p]) :=
  Toy.toyIwasawa p
noncomputable example : HeightData p :=
  Toy.toyHeight (Toy.setup p hsplit).α (Toy.setup p hsplit).alpha_sub_one_unit
noncomputable example : KatzData p ((PowerSeries.X : Λ p) ^ 2) := Toy.toyKatz p
noncomputable example : PrimeData p hsplit 1 1 := Toy.toyPrimeData p hsplit

end Layers

-- end-to-end: the aggregator really produces data at a concrete split prime
noncomputable example :
    @PrimeData 5 (Fact.mk (by norm_num)) (by norm_num) ToyTrivial.deltaE
      ToyTrivial.torsSqOverTam :=
  ToyTrivial.dataAt 5 (by norm_num) (by norm_num) (by simp [ToyTrivial])

#print axioms ToyTrivial
#print axioms Toy.toyPrimeData
#print axioms Toy.toyAnalytic
#print axioms Toy.toySelmer
#print axioms Toy.toyIwasawa
#print axioms Toy.toyHeight
#print axioms Toy.toyKatz
#print axioms Toy.setup
#print axioms Toy.nonempty_setup
#print axioms Toy.subst_σ_X_sq
#print axioms Toy.functionalEquation_X_sq
#print axioms Toy.quotXEquiv
#print axioms Toy.toy_no_finite_submodule
#print axioms Toy.isPUnit_toy_c2norm

end FinShaRank2
