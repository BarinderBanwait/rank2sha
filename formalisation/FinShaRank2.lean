import FinShaRank2.Defs
import FinShaRank2.Interface.Analytic
import FinShaRank2.Interface.Iwasawa
import FinShaRank2.Interface.Heights
import FinShaRank2.Interface.Katz
import FinShaRank2.Interface.EK
import FinShaRank2.Interface.Global
import FinShaRank2.Kernel.Anomalous
import FinShaRank2.Kernel.Decoupling
import FinShaRank2.Kernel.FunctionalEquation
import FinShaRank2.Kernel.GradingValuation
import FinShaRank2.Kernel.LambdaModule
import FinShaRank2.Kernel.Normalization
import FinShaRank2.Kernel.ShaEndgame
import FinShaRank2.Kernel.TsqUnit
import FinShaRank2.Toy.EK
import FinShaRank2.Toy.Trivial
import FinShaRank2.Toy.ShaTrivial
import FinShaRank2.Statements
import FinShaRank2.Main.Lemma41
import FinShaRank2.Main.Consequence
import FinShaRank2.Main.Dictionary

/-!
# FinShaRank2, root module

Root import for the Lean 4 formalisation of *Second derivatives of p-adic
L-functions and the Shafarevich–Tate group of rank-two CM elliptic curves*.

The tree it collects is: the interface layers (`Interface/`), the kernel
lemmas they feed (`Kernel/`), Theorem A and the analytic-arithmetic dictionary
(`Main/`), and the two witness worlds (`Toy/`).

Everything imported (transitively) from this module is audited by
`scripts/audit.sh`: it must contain no incomplete proofs and use only the
standard axioms `propext`, `Classical.choice`, `Quot.sound`.
-/
