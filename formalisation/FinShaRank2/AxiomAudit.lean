import Lean.Util.CollectAxioms
import FinShaRank2

/-!
# Axiom audit gate

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

so that a reader can trust the audited statements without reading their
proofs.

This file is *not* imported by the root module `FinShaRank2.lean`: it is the
auditor, not part of the audited library.  `auditedDecls` below points at the
headline declarations, the kernel lemmas they rest on, and both toy instances.
-/

open Lean

namespace FinShaRank2.AxiomAudit

/-- The exact axiom whitelist: audited declarations may use these three
standard axioms of the Lean library and nothing else. -/
def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- The declarations audited by the gate below.

The list covers every fully proved public declaration of `Defs.lean`, the whole
of `Kernel/`, the headline theorems of `Main/`, and both toy instances under
`Toy/` — grouped by layer, so a regression pinpoints the layer it came from.

`Main/` carries no incomplete signature: all five headline declarations are
audited, and the three lettered results of the paper are among them — Corollary B
is `cor_horizontal`, Theorem A is `prop_consequence`, Theorem C is
`thm_reduction`.

Note the gate also fails on a *missing* declaration, so this list doubles as a
rename tripwire. -/
def auditedDecls : List Name :=
  -- core σ facts (Defs.lean)
  [``FinShaRank2.constantCoeff_σ, ``FinShaRank2.coeff_one_σ, ``FinShaRank2.hasSubst_σ,
  -- anomalous-prime arithmetic (Lemma 2.3)
   ``FinShaRank2.isUnit_one_sub_alphaInv_iff, ``FinShaRank2.isPUnit_one_sub_alphaInv_iff,
   ``FinShaRank2.ap_ne_one_of_hasse, ``FinShaRank2.neg_two_ne_one_zmod_five,
   ``FinShaRank2.two_dvd_ap, ``FinShaRank2.noAnomalous,
  -- decoupling (Lemma 5.3)
   ``FinShaRank2.Decoupling.coeff_two_mul, ``FinShaRank2.Decoupling.coeff_two_mul_of_snd_low,
   ``FinShaRank2.Decoupling.coeff_two_mul_of_fst_low, ``FinShaRank2.Decoupling.coeff_smul_eq_mul,
   ``FinShaRank2.Decoupling.coeff_eq_zero_of_map_eq_zero,
   ``FinShaRank2.Decoupling.isUnit_coeff_two_map_iff,
   ``FinShaRank2.Decoupling.isUnit_coeff_two_of_comparison,
  -- functional equation
   ``FinShaRank2.σR, ``FinShaRank2.constantCoeff_σR, ``FinShaRank2.coeff_one_σR,
   ``FinShaRank2.hasSubst_σR, ``FinShaRank2.oneAddX_mul_σR,
   ``FinShaRank2.coeff_one_σR_pow_of_ne, ``FinShaRank2.coeff_one_subst_σR,
   ``FinShaRank2.coeff_one_eq_zero_of_functionalEquation, ``FinShaRank2.coeff_one_Lp_eq_zero,
  -- grading valuation (Proposition 5.2(2))
   ``FinShaRank2.dvd_of_pow_mul_mem_span_pow_succ,
   ``FinShaRank2.isUnit_iff_residue_ne_zero_of_grading_congr,
  -- Λ-module structure kernel (highest-risk item)
   ``FinShaRank2.selmer_dual_structure,
  -- auxiliaries flanking the structure theorem
   ``FinShaRank2.quotient_collapse, ``FinShaRank2.rank_lower_bound,
  -- normalisation
   ``FinShaRank2.isPUnit_c2tilde_iff, ``FinShaRank2.eq_five_or_thirteen_le,
   ``FinShaRank2.isPUnit_one_sub_alphaInv_of_split, ``FinShaRank2.isPUnit_c2tilde_iff_of_split,
  -- Sha endgame (Theorem A (Theorem 4.9) Step 5)
   ``FinShaRank2.sha_endgame, ``FinShaRank2.sha_endgame_of_nonempty,
  -- T²-unit factorisation
   ``FinShaRank2.tsq_factor, ``FinShaRank2.order_eq_two_of_factored,
   ``FinShaRank2.muZero_of_factored, ``FinShaRank2.lambdaAn_eq_two_of_factored,
   ``FinShaRank2.associated_X_sq_of_factored, ``FinShaRank2.order_eq_two_of_coeffs,
   ``FinShaRank2.muZero_of_coeffs, ``FinShaRank2.lambdaAn_eq_two_of_coeffs,
   ``FinShaRank2.associated_X_sq_of_coeffs, ``FinShaRank2.coeffs_X_sq,
  -- THE HEADLINE THEOREMS
   ``FinShaRank2.c0_eq_zero, ``FinShaRank2.c1_eq_zero,
   ``FinShaRank2.prop_consequence, ``FinShaRank2.prop_dictionary,
   ``FinShaRank2.thm_reduction,
  -- the (10) non-anomality clause, bridged to Proposition 4.3
   ``FinShaRank2.ClassicalInputs.isPUnit_one_sub_alphaInv,
  -- Corollary B, and Theorem C with its first input from Conjecture 5.9
   ``FinShaRank2.cor_horizontal, ``FinShaRank2.thm_reduction_of_conjEK,
  -- non-vacuity: ClassicalInputs is satisfiable, layer by layer
   ``FinShaRank2.Toy.toyAnalytic, ``FinShaRank2.Toy.toySelmer, ``FinShaRank2.Toy.toyIwasawa,
   ``FinShaRank2.Toy.toyHeight, ``FinShaRank2.Toy.toyKatz, ``FinShaRank2.Toy.toyEK,
   ``FinShaRank2.Toy.Setup.ap_ne_one, ``FinShaRank2.Toy.toyPrimeData,
  -- anti-vacuity: the interface alone does NOT force the conclusion
   ``FinShaRank2.Toy.shaAnalytic, ``FinShaRank2.Toy.shaSelmer, ``FinShaRank2.Toy.shaIwasawa,
   ``FinShaRank2.Toy.shaHeight, ``FinShaRank2.Toy.shaKatz, ``FinShaRank2.Toy.shaPrimeData,
   ``FinShaRank2.ToySha, ``FinShaRank2.interface_does_not_force_sha_trivial,
   ``FinShaRank2.toySha_conclusions_fail, ``FinShaRank2.toySha_fails_c2_5_certificate,
   ``FinShaRank2.ToyTrivial,
  -- resultant valuation step (Theorem C (Theorem 5.10) proof)
   ``FinShaRank2.Resultant.forall_eq_one_of_prod_eq_one,
   ``FinShaRank2.Resultant.prod_ne_zero_of_prod_eq_one,
  -- orbit criterion (Lemma 3.2)
   ``FinShaRank2.Orbit.prod_mem_range_algebraMap,
   ``FinShaRank2.Orbit.forall_eq_zero_of_exists_eq_zero,
  -- anomalous primes at split p (Lemma 2.3(2))
   ``FinShaRank2.anomalous_iff_five,
  -- the Eisenstein–Kronecker package (Definition 3.1, (7))
   ``FinShaRank2.jetIndex_image, ``FinShaRank2.jetIndex_injective,
   ``FinShaRank2.EKPackage.deltaE_ne_zero_iff, ``FinShaRank2.EKPackage.deltaE_singleton]

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
