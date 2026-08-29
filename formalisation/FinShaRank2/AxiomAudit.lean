import Lean.Util.CollectAxioms
import FinShaRank2

/-!
# Axiom audit gate (task T02)

Machine gate run by `scripts/audit.sh` step [3/3] via
`lake env lean FinShaRank2/AxiomAudit.lean`.

For every declaration in `auditedDecls` it collects the axioms the
declaration (transitively) depends on, and **fails elaboration** — hence
exits nonzero — unless every such axiom is one of the three standard ones:
`propext`, `Classical.choice`, `Quot.sound`.

In particular this catches:
* incomplete proofs (`sorryAx`),
* `native_decide` (`Lean.ofReduceBool` / `Lean.ofReduceNat`),
* any stray global `axiom` declaration,

per the trust story of `TASK_BOARD.md` §1.

This file is *not* imported by the root module `FinShaRank2.lean`: it is the
auditor, not part of the audited library. T42 points `auditedDecls` at the
five headline declarations and both toy instances.
-/

open Lean

namespace FinShaRank2.AxiomAudit

/-- The exact axiom whitelist of `TASK_BOARD.md` §1: audited declarations may
use these three standard axioms and nothing else. -/
def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- The declarations audited by the gate below.

**Consolidated 2026-07-30 (PM).** Covers every fully-proved public declaration of
`Defs.lean` (T10), the whole `Kernel/` tree (T20–T27), and the non-vacuity
instances of `Toy/` (T40) — layer by layer, so a regression pinpoints its layer.
Until Wave 3 this list held only the three `σ` facts, which made `audit.sh`'s
step [3/3] far weaker than the trust story of §1 implies; the gap was an artifact
of deferring consolidation while four agents edited concurrently, not a decision.

`Main/` is deliberately absent: it carries incomplete frozen signatures during the
T15→T34 window, and `sorryAx` would (correctly) fail this gate. T42 adds the five
headline declarations (`prop_consequence`, `prop_dictionary`, `thm_reduction`,
`cor_sha5`, `cor_sha13`) plus `ToySha` once they are proved, and empties the
allowlist consumed by step [2/3].

(Note for editors: step [2/3] greps this tree for the bare word "s·o·r·r·y", so
prose here must not spell it out — that is why the allowlist file is referred to
obliquely above.)

Note the gate also fails on a *missing* declaration, so this list doubles as a
rename tripwire. -/
def auditedDecls : List Name :=
  -- T10 — core σ facts (Defs.lean)
  [``FinShaRank2.constantCoeff_σ, ``FinShaRank2.coeff_one_σ, ``FinShaRank2.hasSubst_σ,
  -- T24 — anomalous-prime arithmetic (lem:noanomalous)
   ``FinShaRank2.isUnit_one_sub_alphaInv_iff, ``FinShaRank2.isPUnit_one_sub_alphaInv_iff,
   ``FinShaRank2.ap_ne_one_of_hasse, ``FinShaRank2.neg_two_ne_one_zmod_five,
   ``FinShaRank2.two_dvd_ap, ``FinShaRank2.noAnomalous,
  -- T22 — decoupling (lem:decoupling)
   ``FinShaRank2.Decoupling.coeff_two_mul, ``FinShaRank2.Decoupling.coeff_two_mul_of_snd_low,
   ``FinShaRank2.Decoupling.coeff_two_mul_of_fst_low, ``FinShaRank2.Decoupling.coeff_smul_eq_mul,
   ``FinShaRank2.Decoupling.coeff_eq_zero_of_map_eq_zero,
   ``FinShaRank2.Decoupling.isUnit_coeff_two_map_iff,
   ``FinShaRank2.Decoupling.isUnit_coeff_two_of_comparison,
  -- T20 — functional equation
   ``FinShaRank2.σR, ``FinShaRank2.constantCoeff_σR, ``FinShaRank2.coeff_one_σR,
   ``FinShaRank2.hasSubst_σR, ``FinShaRank2.oneAddX_mul_σR,
   ``FinShaRank2.coeff_one_σR_pow_of_ne, ``FinShaRank2.coeff_one_subst_σR,
   ``FinShaRank2.coeff_one_eq_zero_of_functionalEquation, ``FinShaRank2.coeff_one_Lp_eq_zero,
  -- T25 — grading valuation (prop:grading(2))
   ``FinShaRank2.dvd_of_pow_mul_mem_span_pow_succ,
   ``FinShaRank2.isUnit_iff_residue_ne_zero_of_grading_congr,
  -- T23 — Λ-module structure kernel (highest-risk item)
   ``FinShaRank2.selmer_dual_structure,
  -- T31 — promoted from the T15 chain test into the kernel (Wave 5)
   ``FinShaRank2.quotient_collapse, ``FinShaRank2.rank_lower_bound,
  -- T26 — normalization + certificate extraction
   ``FinShaRank2.isPUnit_c2tilde_iff, ``FinShaRank2.isUnit_of_toZModPow_cert,
   ``FinShaRank2.isUnit_of_toZModPow_cert', ``FinShaRank2.isUnit_of_cert_five,
   ``FinShaRank2.isUnit_of_cert_thirteen, ``FinShaRank2.eq_five_or_thirteen_le,
   ``FinShaRank2.isPUnit_one_sub_alphaInv_of_split, ``FinShaRank2.isPUnit_c2tilde_iff_of_split,
  -- T27 — Sha endgame (prop:consequence Step 5)
   ``FinShaRank2.sha_endgame, ``FinShaRank2.sha_endgame_of_nonempty,
  -- T21 — T²-unit factorization
   ``FinShaRank2.tsq_factor, ``FinShaRank2.order_eq_two_of_factored,
   ``FinShaRank2.muZero_of_factored, ``FinShaRank2.lambdaAn_eq_two_of_factored,
   ``FinShaRank2.associated_X_sq_of_factored, ``FinShaRank2.order_eq_two_of_coeffs,
   ``FinShaRank2.muZero_of_coeffs, ``FinShaRank2.lambdaAn_eq_two_of_coeffs,
   ``FinShaRank2.associated_X_sq_of_coeffs, ``FinShaRank2.coeffs_X_sq,
  -- T30/T31/T32/T33/T34 — THE FIVE HEADLINE THEOREMS (TASK_BOARD.md §0)
   ``FinShaRank2.c0_eq_zero, ``FinShaRank2.c1_eq_zero,
   ``FinShaRank2.prop_consequence, ``FinShaRank2.prop_dictionary,
   ``FinShaRank2.thm_reduction, ``FinShaRank2.cor_sha5, ``FinShaRank2.cor_sha13,
  -- T40 — non-vacuity: ClassicalInputs is satisfiable, layer by layer
   ``FinShaRank2.Toy.toyAnalytic, ``FinShaRank2.Toy.toySelmer, ``FinShaRank2.Toy.toyIwasawa,
   ``FinShaRank2.Toy.toyHeight, ``FinShaRank2.Toy.toyKatz, ``FinShaRank2.Toy.toyPrimeData,
  -- T41 — anti-vacuity: the interface alone does NOT force the conclusion
   ``FinShaRank2.Toy.shaAnalytic, ``FinShaRank2.Toy.shaSelmer, ``FinShaRank2.Toy.shaIwasawa,
   ``FinShaRank2.Toy.shaHeight, ``FinShaRank2.Toy.shaKatz, ``FinShaRank2.Toy.shaPrimeData,
   ``FinShaRank2.ToySha, ``FinShaRank2.interface_does_not_force_sha_trivial,
   ``FinShaRank2.toySha_conclusions_fail, ``FinShaRank2.isEmpty_certificates_toySha,
   ``FinShaRank2.ToyTrivial]

/-- Collect the axioms of every declaration in `auditedDecls` and throw
(failing elaboration, so `lake env lean` exits nonzero) if any declaration is
missing or uses an axiom outside `allowedAxioms`. -/
def runAudit : CoreM Unit := do
  let env ← getEnv
  let mut failures : Array MessageData := #[]
  for d in auditedDecls do
    if env.contains d then
      let axs ← collectAxioms d
      let bad := axs.filter fun a => !allowedAxioms.contains a
      if bad.isEmpty then
        logInfo m!"AxiomAudit OK: {d} uses only {axs.toList}"
      else
        failures := failures.push m!"{d} uses disallowed axioms: {bad.toList}"
    else
      failures := failures.push m!"audited declaration {d} does not exist"
  unless failures.isEmpty do
    throwError "AXIOM AUDIT FAILED:\n{MessageData.joinSep failures.toList "\n"}"
  logInfo m!"AxiomAudit: all {auditedDecls.length} audited declaration(s) clean"

#eval runAudit

end FinShaRank2.AxiomAudit
