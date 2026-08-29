import Mathlib
import FinShaRank2.Defs
import FinShaRank2.Interface.Global
import FinShaRank2.Interface.Certificates
import FinShaRank2.Kernel.Normalization
import FinShaRank2.Main.Consequence
import FinShaRank2.Main.Dictionary
import FinShaRank2.Statements
import FinShaRank2.Main.Corollaries

/-!
T34 scratch. Not root-imported, not audited.

Landed-declaration checks for `FinShaRank2.cor_sha5` / `cor_sha13`:
axiom hygiene, plus a transitive-constant scan confirming that no conjectural
input (`thm_reduction`, `SinnottHyp`, a `deltaE` nonvanishing hypothesis)
occurs anywhere in their proof terms.
-/

open Lean in
/-- Collect every constant a declaration transitively depends on. -/
partial def T34deps (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  match env.find? n with
  | some ci =>
      for c in ci.type.getUsedConstants do T34deps env c
      match ci.value? with
      | some v => for c in v.getUsedConstants do T34deps env c
      | none => pure ()
  | none => pure ()

/-- Does `s` contain `t` as a substring? -/
def T34has (s t : String) : Bool := ((s.splitOn t).length > 1)

/-- Conjectural markers to scan for. -/
def T34markers : List String := ["SinnottHyp", "thm_reduction", "sinnott", "Sinnott"]

open Lean Elab Command in
/-- Report any transitive dependency whose name matches a conjectural marker. -/
elab "#conjectural_scan" id:ident : command => do
  let env ← getEnv
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  let (_, s) := (T34deps env n).run {}
  let bad := s.toList.filter (fun m => T34markers.any (T34has m.toString))
  logInfo m!"{n}: total deps = {s.size}, conjectural deps = {bad}"

#print axioms FinShaRank2.cor_sha5
#print axioms FinShaRank2.cor_sha13
#conjectural_scan FinShaRank2.cor_sha5
#conjectural_scan FinShaRank2.cor_sha13
