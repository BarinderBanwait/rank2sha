import FinShaRank2.Main.Lemma41
import FinShaRank2.Main.Consequence
import FinShaRank2.Main.Dictionary
import FinShaRank2.Toy.ShaTrivial

/-!
# Comparator solution: the proofs

The *Solution* half of the `comparator` run described in `Challenge.lean`.
It declares nothing. Importing the four modules above puts the proved
theorems `FinShaRank2.c0_eq_zero`, `FinShaRank2.c1_eq_zero`,
`FinShaRank2.prop_consequence`, `FinShaRank2.prop_dictionary` and
`FinShaRank2.interface_does_not_force_sha_trivial` into the environment, and
comparator exports them from here by name.

The import closure of this module is the part of the project comparator
treats as untrusted: `Kernel/`, `Main/` and `Toy/`.
-/
