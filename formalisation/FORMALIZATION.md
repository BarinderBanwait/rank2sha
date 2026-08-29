# FORMALIZATION.md — Referee guide to the Lean formalization

*Companion to "Horizontal rigidity for second jets of Katz p-adic L-functions, with
applications to the Tate–Shafarevich group in rank two" (`main.tex`). This document
explains what has been machine-checked by Lean 4 (mathlib, pinned to release
`v4.33.1`), what is assumed and why, and how to reproduce the verification from a
fresh clone of this repository.*

Status: COMPLETE (all six sections). Last updated 2026-08-18 (task T52).

> **Note added 2026-08-25 (paper v2).** The paper has been rewritten (v2, ≤30 pp)
> and by design carries **no formalization discussion**: v1's §1.9 (the
> formalization essay) and Appendix B (the statement-correspondence tables) were
> removed from the manuscript, and **this document is their canonical home** —
> §1 here covers v1 §1.9's content (interface-first design, axiom discipline,
> the literature/certificate/conjecture three-way split, the ToyTrivial/ToySha
> non-vacuity instances, honest limits), and §2 carries the correspondence
> tables. Three things a reader coming from v2 should know:
>
> 1. **Statement numbering below refers to v1** (`main.tex`, frozen). v2
>    renumbers sections and *removes* Corollaries `cor:sha5`/`cor:sha13` as
>    paper statements: Coates–Liang–Sujatha (J. Algebra 322 (2009) 657–674;
>    Milan J. Math. 78 (2010) 395–416, Thm. 1.3) prove Ш(E₁/Q)[p^∞] = 0 for the
>    2-isogenous partner E₁ : y² = x³ + 14x at every split p < 30,000, which
>    transfers to E across the 2-isogeny — subsuming the two corollaries. The
>    Lean theorems `cor_sha5`/`cor_sha13` remain exactly what they always were:
>    kernel-checked implications from the certificate bundle, unaffected by the
>    literature having independently established their conclusions.
> 2. **(H5)/comparison docstring correction.** The interface field
>    `KatzData.comparison` and related docstrings describe the
>    MTT-vs-Katz comparison in v1's terms (a comparison constant c_p assembled
>    from a period ratio and local factors). Per `H5_CORRECTION_NOTE.md` in the
>    working directory (verified against Rubin, Invent. Math. 103 (1991), §12):
>    Rubin's Thm. 12.3 is stated over Q for the Mazur–Swinnerton-Dyer
>    L-function, the Katz-to-cyclotomic comparison is carried out inside his
>    proof as an equality of ideals, and the honest quoted residue is only the
>    MSD(1974)-vs-MTT(1986) normalisation. This does not affect any Lean proof
>    (the field is an assumption, not a theorem), but the docstring's
>    *description* of the cited literature is superseded; v2 §3 carries the
>    corrected account.
> 3. v2's evidence sections reframe the 508-prime regulator scan using the CLS
>    input (no Ш assumption below 30,000); the certificates consumed by the
>    Lean project (`Certificates.c2_5`, `c2_13`, `a5`, `a13`) are unchanged.

## Table of contents

1. [The trust story](#1-the-trust-story)
2. [Statement-by-statement table](#2-statement-by-statement-table)
3. [Certificate provenance](#3-certificate-provenance)
4. [The ToyTrivial / ToySha argument](#4-the-toytrivial--toysha-argument)
5. [Known descopes and why they are harmless](#5-known-descopes-and-why-they-are-harmless)
6. [Build and audit instructions](#6-build-and-audit-instructions)

---

## 1. The trust story

### 1.1 What this document is for

This paper was produced by AI agents. That is exactly the situation in which a human
referee's trust should be *conditional and checkable*, not taken on faith. The
formalization exists to shrink the referee's job to two finite, human-sized tasks:

1. **Read one small tree of assumption *statements*** — plain mathematical
   propositions, each carrying a pinpoint literature citation — and judge whether they
   are true (they are, with two clearly marked exceptions that the paper itself flags
   as conjectural).
2. **Read the five headline Lean statements side by side with the corresponding
   statements in `main.tex`**, and judge whether the Lean sentence says what the paper
   sentence says.

Once those two checks pass, the referee does **not** need to check any of the
algebra, the module theory, the case-splitting, or the bookkeeping in between: Lean's
kernel — a small, independently-implemented, widely-trusted piece of software — has
mechanically verified that the conclusion follows from the stated assumptions by
pure logic. That is what "formally verified" buys here, and §1.4 below is explicit
about what it does *not* buy.

### 1.2 What "formally verified" means concretely

Every proof in this repository is checked by the Lean 4 kernel against mathlib
(pinned to release `v4.33.1`, mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`
— see §6). Concretely:

* **Zero global `axiom` declarations anywhere in the project.** Every assumed
  mathematical input — every classical theorem, every numerical computation this
  project performed itself, every genuinely open conjecture the paper depends on — is
  a *field of an explicit Lean structure*, and the five headline theorems are literal
  implications of the form
  ```
  theorem prop_consequence (H : ClassicalInputs) … (hc2 : IsPUnit …) : … := by …
  ```
  i.e. "given data `H` satisfying these named properties, the conclusion holds." There
  is no hidden `axiom foo : bar` anywhere for the kernel to take on faith outside of
  Lean's own three built-in logical axioms.
* **`#print axioms` on every headline declaration shows exactly**
  `propext, Classical.choice, Quot.sound` **and nothing else.** These three are
  mathlib's standing background axioms (propositional extensionality, choice,
  quotient soundness) — universally accepted foundational principles of the
  mathlib/Lean ecosystem, not project-specific assumptions, and not something this
  formalization introduces. This was re-derived independently by the project's own PM
  role and can be reproduced by any referee in one command (§6).
* **The `scripts/audit.sh` gate is mechanical**, not a matter of an agent's say-so: it
  (1) rebuilds the whole project, (2) greps every audited file for the literal
  substrings that mark an incomplete proof, against an allowlist file that is
  currently *empty*, and (3) elaborates a program that calls Lean's own
  `Lean.collectAxioms` on a fixed list of 74 declarations and fails the build if any
  of them uses anything outside the three-axiom whitelist above. Verified output is
  quoted in full in §6.

### 1.3 Why an interface-first design

A fully "from-scratch" formalization of this paper — one that constructs Selmer
groups, the Tate–Shafarevich group, Katz's two-variable p-adic L-functions, and
cyclotomic p-adic heights as literal mathlib objects and *proves* Mazur's control
theorem, Rubin's Iwasawa main conjecture for CM fields, and the Bannai–Kobayashi
comparison theorem inside Lean — is a multi-year formalization project in its own
right, comparable in scope to formalizing a large fraction of a graduate course in
Iwasawa theory. As of the mathlib pin used here, mathlib has essentially none of this
machinery: a project audit (`TASK_BOARD.md` task T64, repeated at each mathlib
version check) found continuous-cohomology infrastructure landing piecemeal
(`RepresentationTheory/Homological/ContCohomology`, merged 2026-07-02) but **no
definition of the Tate–Shafarevich group, the Weil–Châtelet group, or Selmer groups
anywhere in mathlib** — confirmed by source search, not merely absence of a
convenient name.

Formalizing all of that from first principles would not, moreover, be formalizing
*this paper*: it would be formalizing a large slab of twentieth-century algebraic
number theory that the paper legitimately treats as known background, citable by
theorem number. What is actually new — the thing a referee needs to check with real
scrutiny — is the paper's own chain of deductions: the horizontal-rigidity argument,
the reduction of the Ш-vanishing corollaries to a single numerical unit condition on
a second Taylor coefficient, and the arithmetic that turns two digit-expansion
computations into unconditional statements about Ш(E/ℚ)[5^∞] and Ш(E/ℚ)[13^∞].

The design adopted therefore **treats every universally-accepted classical theorem
the paper cites (Rubin, Mazur, Greenberg, Mazur–Tate–Teitelbaum, Bannai–Kobayashi,
de Shalit, Schneider/Perrin-Riou, Hasse, …) as an explicit, human-refereeable
assumption** — a Lean structure field with a docstring naming the exact theorem, the
paper, and the page/theorem number — and asks Lean's kernel to certify only what the
paper's *own* argument deduces from those inputs. This is not a weaker form of
verification; it is the only form of verification whose *scope* matches the paper's
actual mathematical content, and it makes the classical dependencies of the paper's
"unconditional" claims *more* explicit than the paper itself, not less (§1.4, §2).

### 1.4 The epistemic three-way split

Every fact this formalization consumes falls into exactly one of three categories,
and the category is visible in the Lean source by construction, not by convention
alone:

1. **`ClassicalInputs`** (`FinShaRank2/Interface/Global.lean`) — the aggregate
   structure of citable, published theorems (Rubin's main conjecture, Mazur's control
   theorem, the MTT interpolation formula, the Bannai–Kobayashi comparison theorem,
   the Schneider/Perrin-Riou leading-term theorem, the Hasse bound, …), each a
   structure field with a `SOURCE: … PAPER: … STATUS: …` docstring pinning it to a
   specific citation and to the specific paper label and proof step that uses it.
   Consumed as an ordinary hypothesis `H : ClassicalInputs` by every headline theorem.
2. **`Certificates H`** (`FinShaRank2/Interface/Certificates.lean`) — this project's
   *own* machine-verified numerics: the traces of Frobenius `a_5 = -2`, `a_13 = -6`,
   and the leading p-adic digit expansions of the second Taylor coefficient
   `c₂(p) = coeff 2 L_p` at `p = 5, 13`. Kept in a **separate** structure from
   `ClassicalInputs` specifically so a referee can see at a glance which facts are
   citable literature and which are this project's own computation (§3).
3. **Conjectural hypotheses** — exactly two: `hyp:sinnott` (the Lean structure
   `SinnottHyp`) and `conj:EK` (the Lean proposition `H.deltaE ≠ 0`). These are the
   only genuinely open items the paper's argument depends on for its *general*
   reduction theorem, and they occur **only in hypothesis position of one
   declaration**, `thm_reduction` — never as a field of any structure that could be
   *instantiated*. `SinnottHyp` is a `Prop`-valued structure, not a `ClassicalInputs`
   field; grepping `FinShaRank2/Main/` and `FinShaRank2/Statements.lean` for
   `SinnottHyp` and `H.deltaE ≠ 0` confirms both occur in exactly one file
   (`Main/Reduction.lean`) and nowhere else.

The load-bearing consequence: **`cor_sha5` and `cor_sha13` — the two theorems that
Ш(E/ℚ)[5^∞] = 0 and Ш(E/ℚ)[13^∞] = 0 — use neither conjectural item.** This was not
just eyeballed; a metaprogram walked the full transitive closure of constants each
corollary's proof term depends on (~2610 constants each) and searched for the two
conjectural markers, finding none. The two anchor corollaries rest on `ClassicalInputs`
(citable literature) plus `Certificates` (this project's own numerics) and nothing
else. `thm_reduction`, by contrast, is the one place the paper's *general* conjectural
reduction is rendered — and it is honestly conditional, exactly as the paper presents
it.

### 1.5 Non-vacuity, proved rather than asserted

A structure with enough fields can always be vacuous — self-contradictory, so that
every theorem "proved" from it is proved from a false premise and worth nothing. This
formalization does not leave that to inspection: `FinShaRank2.ToyTrivial` is a fully
worked, sorry-free instance of `ClassicalInputs` in a simplified ("toy") algebraic
world, proving the assumption bundle is *consistent*. Its complement,
`FinShaRank2.ToySha`, is a second fully worked instance satisfying every interface
field exactly as frozen but in which Ш is **not** trivial — proving that the interface
does not smuggle in its own conclusion. Both are explained for a non-Lean reader in
§4; both are part of the mechanical audit (§6).

### 1.6 What "formally verified" does *not* mean here

To be scrupulously honest about scope, matching this document's own governing rule:

* It does **not** mean the cited classical theorems (Rubin, Mazur, MTT,
  Bannai–Kobayashi, Schneider/Perrin-Riou, …) have themselves been formally verified.
  They are trusted the way a human referee trusts a citation: by checking that the
  cited statement is real, correctly attributed, and correctly used. Every citation
  in this project is pinned to a specific paper, theorem number, and (where relevant)
  page, precisely so a referee can perform that check quickly (§2).
* It does **not** mean the *paper's* informal exposition, background survey (§3 of
  `main.tex`), computational scan (§6), or forward-looking discussion (§9) have been
  checked in any formal sense — they were never claims requiring proof, and §5 below
  records this explicitly rather than leaving it implicit.
* It does **not** mean the Lean statements are self-evidently the right rendering of
  the paper's mathematics — that is exactly the second thing (§1.1, item 2) a referee
  must check by reading, and §2 is built to make that check as fast as possible.
* It does **not** extend to two conjectural inputs (`hyp:sinnott`, `conj:EK`), which
  remain exactly as open as the paper says they are — see §1.4.

---

## 2. Statement-by-statement table

Every declaration name below was checked against the Lean source (file paths given).
The **status** column uses five values:

* **kernel-proved** — a Lean `theorem`, sorry-free, proved from the interface/kernel
  layer, checked by `AxiomAudit.lean`.
* **interface field + citation** — a field of an interface structure, carrying a
  `SOURCE`/`PAPER`/`STATUS` docstring pinning it to the cited theorem; not itself
  proved in Lean (it *is* the assumption).
* **certificate** — a field of `Certificates H`, this project's own numerical
  computation (§3).
* **conjectural hypothesis** — occurs only in hypothesis position of `thm_reduction`.
* **descoped** — not formalized; documented in prose here (§5).

| Paper label | Lean declaration(s) | File | Status | Faithfulness notes |
|---|---|---|---|---|
| `def:horizontal` | `HorizontalVanishing` | `Statements.lean` | formal `def` | Standalone predicate on a set of primes `P` and an abstract triviality predicate; deliberately general, matches "holds for all but finitely many `p ∈ 𝒫`" verbatim as finiteness of the failure set. |
| `lem:c0c1` | `c0_eq_zero`, `c1_eq_zero` | `Main/Lemma41.lean` | **kernel-proved** | Stated over a bare `AnalyticData p hsplit` (minimal-hypothesis form), not over `ClassicalInputs`; `prop_consequence` applies it downstream. `c₀ = 0` derived from `interp` + certificate `msymb_zero`; `c₁ = 0` derived from `funct_eq` via the kernel lemma `coeff_one_Lp_eq_zero`. |
| `def:c2tilde` | `c2tilde` (`Defs.lean`), `PrimeData.c2tilde` (`Statements.lean`) | `Defs.lean`, `Statements.lean` | formal `def` | Total function (junk value at anomalous primes, documented — §2 conv. 5 of the board); the rational factor `(#tors)²/∏c_v` is pinned `= 1` for the testbed curve by `ClassicalInputs.torsSqOverTam_eq`, a checkable datum rather than a baked-in constant. |
| `rmk:normalisation`(i) | `isPUnit_c2tilde_iff_of_split` | `Kernel/Normalization.lean` | **kernel-proved** | `IsPUnit c̃₂(p) ↔ IsUnit (coeff 2 L_p)` at every split `p`, folding in the non-anomality input (`noAnomalous`, `h5`) internally rather than assuming it. Parts (ii) and (iii) of the same remark need no separate row: (ii) restates `eq:padicbsd` (already `HeightData.spr_padicBSD`/`spr_nondeg` above); (iii) integrality of `c₂(p)` is automatic from the Lean type `AnalyticData.Lp : Λ p := PowerSeries ℤ_[p]` (`Defs.lean`) and is asserted by no separate field — see §5.9. |
| `conj:strong` / `conj:weak` | `ConjStrong H`, `ConjWeak H` | `Statements.lean` | formal `def` | Renderings of the paper's two conjectures as Lean propositions. Not proved as standalone conjectures (that is exactly the paper's open question); `ConjStrong H` is what `thm_reduction` *derives* from `hyp:sinnott` + `conj:EK`. |
| `lem:comparison` | `KatzData.comparison` | `Interface/Katz.lean` | **interface field + citation** | SOURCE: Bannai–Kobayashi, Duke Math. J. 153 (2010), Cor. 3.12, + de Shalit, *Iwasawa theory of elliptic curves with CM*, Perspectives in Math. 3, II §4. Consequence-form: the comparison constant `c` and series unit `u` are taken already as units in `Wˣ`/`(W⟦T⟧)ˣ`, which bakes in "`v_p(c_p) = 0` for `p ∉ S`" — documented in-file as a deliberate consequence-form, not a strengthening hidden from the reader. |
| `prop:consequence` | `prop_consequence` | `Main/Consequence.lean` | **kernel-proved** | Drops the paper's "Assume `conj:weak`" (the paper quotes it only to *produce* the unit hypothesis at all-but-finitely-many primes; the Lean statement takes the unit condition directly at one prime, so it mentions no conjecture at all) and drops "non-anomalous" (proved unconditionally for split `p ≥ 13` by `lem:noanomalous`/T24, leaving only the certificate-grade residual hypothesis `h5 : p = 5 → a_p = -2`). **Both deviations run in the safe direction: fewer hypotheses, not weaker conclusions.** |
| `rmk:nofinitesub` | — | — | **descoped** (prose) | Consequence of `IwasawaData.no_finite_submodule`'s docstring, not a separate lemma; see §5. |
| `prop:dictionary` | `prop_dictionary` | `Main/Dictionary.lean` | **kernel-proved** | Carries **no** non-anomality hypothesis at all — a genuine strengthening over the paper's statement, which restricts to non-anomalous `p`. Both directions available from the Schneider/Perrin-Riou consequence-forms (`c2norm_tie`, `spr_nondeg`, `shaOrd_tie`) with no anomality-sensitive step. Route-finding note: the board's alternative valuation-arithmetic route (`spr_padicBSD` + integrality) was checked and **cannot** prove this statement as frozen — it recovers the regulator and Ш conjuncts but has no handle on `heightNondeg` — so the tie-equation route is necessary, not merely convenient. |
| `cav:failure`, `rmk:KL`, `rmk:fq`, `rmk:modesnow`, `rmk:correlation` | — | — | **descoped** (prose) | Remarks/caveats about the scope and interpretation of the results; documented in §5. |
| `lem:noanomalous` | `noAnomalous` (+ `ap_ne_one_of_hasse`, `isPUnit_one_sub_alphaInv_iff`, `two_dvd_ap`) | `Kernel/Anomalous.lean` | **kernel-proved** | Proved unconditionally for `K = ℚ(i)`, `13 ≤ p`, from the `AnalyticData` fields `hasse` and `ap_from_CM` (Hasse-bound squeeze + CM evenness of `a_p`). At `p = 5` the residual case is closed by the single certified value `a_5 = -2` (`decide`, `neg_two_ne_one_zmod_five`), fed downstream from `Certificates.a5`. Conclusion delivered as `IsPUnit (1 − α_p⁻¹)` (norm-one), not the weaker bare `IsUnit` in the field `ℚ_[p]` — a deliberate contract strengthening flagged in the T24 report and honored by T26/T31. |
| `eq:padicbsd` | `HeightData.spr_padicBSD`, `HeightData.spr_nondeg` | `Interface/Heights.lean` | **interface field + citation** | SOURCE: Schneider, Invent. Math. 79 (1985), Thms 2, 2′; Perrin-Riou, Invent. Math. 109 (1992), §§3.4.2–3.4.3; packaged as Stein–Wuthrich, Math. Comp. 82 (2013), Thm 6.1. `spr_nondeg` is the **one sanctioned exception** to the "no conclusion vocabulary in assumptions" rule (board convention 4): the cited theorem genuinely has iff shape. It is phrased over `HeightData`'s own proxies `c2norm`, `shaOrd` — never over `IsUnit (coeff 2 Lp)` or `Subsingleton ShaDual` directly — which is exactly what keeps `ToySha` (§4) constructible. |
| `cor:sha5` | `cor_sha5` | `Main/Corollaries.lean` | **kernel-proved** | Carries **all five** of the paper's conclusions (Selmer corank = 2, Ш = 0, μ = 0, λ = 2, height pairing nondegenerate); conjunct order permuted relative to the board's original sketch, immaterial in a conjunction. Uses `H : ClassicalInputs` and `C : Certificates H` and **provably nothing else** (§1.4); the specific `Certificates` fields consumed at `p = 5` are `C.five_notin`, `C.a5`, `C.c2_5` (§3.2) — `C.thirteen_notin`, `C.a13`, `C.c2_13` play no role in this proof. |
| `cor:sha13` | `cor_sha13` | `Main/Corollaries.lean` | **kernel-proved** | As `cor_sha5`, at `p = 13`. The `c2_13` certificate was pre-registered before the confirming computation existed (§3) — the strongest single credibility argument available for this result. The specific `Certificates` fields consumed are `C.thirteen_notin`, `C.c2_13` (§3.2); unlike `cor_sha5`, `C.a13` is *not* needed for the residual non-anomality hypothesis (vacuous at `p = 13`, since `13 ≠ 5`), though it is still recorded in `Certificates` as a referee-facing datum. |
| `prop:jetformula` | `KatzData.grading_congr` (docstring) | `Interface/Katz.lean` | **interface field** (partial) | The field records only the *resulting algebraic congruence* `p²·(κ₀·c₂(L^K) − m2core) ∈ (p³)`; the Eisenstein–Kronecker second-moment bookkeeping that derives this congruence (`c₂(L^K) = ½∫m² dμ_ψ`, the divided-congruence calculus of Bannai–Kobayashi §§2–3) is **not** carried into Lean. Abstract skeleton form is stretch task T61, not attempted. See §5. |
| `prop:grading` | part (2): `isUnit_iff_residue_ne_zero_of_grading_congr`; part (1): `KatzData.grading_congr`, `KatzData.m2core` | `Kernel/GradingValuation.lean`; `Interface/Katz.lean` | part (2) **kernel-proved**; part (1) **interface field** | Part (2) (the valuation-theoretic unit ⟺ nonzero-residue equivalence in a general local domain) is a clean, ring-generic, kernel-proved lemma. Part (1) (the congruence itself, from the moment calculus) is assumed as data, per `prop:jetformula` above; `m2core : W` (the `p⁻²`-lift of the grade-two moment sum) is the opaque datum `grading_congr` and `SinnottHyp.presentation` both refer to, `STATUS: data`. |
| `lem:decoupling` | `coeff_two_mul`, `isUnit_coeff_two_of_comparison`, et al. | `Kernel/Decoupling.lean` | **kernel-proved** | Ring-generic (arbitrary commutative ring, no project-specific data): the three-term coefficient-of-product formula and its unit-transfer corollary along an injective local ring map. |
| `def:deltaE` | `KatzData.deltaE_local`, `KatzData.resultant_link` | `Interface/Katz.lean` | data field + **interface field + citation** | `deltaE_local : ℚ` is opaque data (the resultant-norm invariant); `resultant_link` is the classical resultant-norm property (`δ_E ≠ 0 ∧ 𝔭∤δ_E → NonvanishingOnDE`), itself citation-grade but not tied to a single external paper beyond the definition. Welded to the global `ClassicalInputs.deltaE` by `PrimeData.deltaE_tie`. `NonvanishingOnDE : Prop` (`KatzData`) is the opaque predicate this codomain names — "the fixed grade-two combination of `𝓡_E` is nonzero on `D_E mod 𝔭`" — asserted nowhere, only the target type of `resultant_link` and the antecedent of `hyp:sinnott`(ii) below. |
| `hyp:sinnott` | `SinnottHyp` | `Interface/Katz.lean` | **conjectural hypothesis** | `Prop`-valued structure, two fields (`presentation`, `nonvanishing`); occurs **only** as a hypothesis `h86` of `thm_reduction`. Never a field of any instantiable structure — confirmed by grep across `Main/` and `Statements.lean`. Both fields quantify over `KatzData.traceClass : IsLocalRing.ResidueField W`, the opaque mod-`𝔭` Sinnott trace (`STATUS: opaque data`) that `presentation` equates with the criterion class and `nonvanishing` requires nonzero. |
| `conj:EK` | `H.deltaE ≠ 0` | hypothesis `h87` of `thm_reduction`, `Main/Reduction.lean` | **conjectural hypothesis** | The nonvanishing of the candidate invariant `δ_E`; occurs only as `thm_reduction`'s hypothesis `h87`, never asserted or assumed elsewhere. |
| `thm:reduction` | `thm_reduction` | `Main/Reduction.lean` | **kernel-proved** (conditional) | The **only** declaration in the project that mentions conjectural input, and it does so purely in hypothesis position (`h86 = hyp:sinnott`, `h87 = conj:EK`, plus the certificate-grade residual `h5` at `p = 5`, same role as in `prop_consequence`). Conclusion reports `MuZero` alongside `lambdaAn = 2` (paired per the junk-value convention, §1). The full novel deduction chain — `resultant_link` → `SinnottHyp` → grading-valuation kernel → decoupling → normalization — is proved end-to-end with **no interface change**, closing what was tracked as the project's top residual risk. |
| §3 (`thm:gillard`, BK1–3) | — | — | **descoped** (prose) | Expository background theorems the paper surveys but does not re-prove; not formalized. See §5. |
| §6 scan, §9 outlook | — | — | **descoped** (prose) | Computational scan across many primes and forward-looking discussion; not formalized, not part of the two anchor corollaries. See §5. |

Two rows deserve a further remark, since they are the ones most likely to draw a
skeptical referee's attention:

* **The paper calls `cor:sha5`/`cor:sha13` "unconditional"; the Lean statements are
  conditional on `H : ClassicalInputs` and `C : Certificates H`.** This is not a
  weakening — it is the entire point of this formalization's design (§1.3–§1.4). The
  paper's own proof already *depends* on Rubin's main conjecture, Mazur's control
  theorem, the MTT interpolation formula, and half a dozen other classical results;
  calling the corollary "unconditional" means unconditional *given those accepted
  theorems*, exactly as any paper in this area does. The Lean rendering simply makes
  that implicit dependency into an explicit, typed hypothesis `H`, so a referee can
  see and check every one of those dependencies in one place (§1.4, §2 above) instead
  of having to reconstruct them from the paper's citation trail.
* **`prop_consequence`, `prop_dictionary`, and `thm_reduction` each drop a hypothesis
  the paper states** (`conj:weak`, "non-anomalous"). In every case the Lean statement
  was checked against `main.tex` side by side (the paper's own PM faithfulness audit,
  2026-08-18) and the deviation runs in the safe direction: either the hypothesis is
  *proved* elsewhere in the project and therefore redundant to assume (non-anomality,
  proved by `lem:noanomalous`/T24), or the paper only invokes it to derive a weaker
  form of a hypothesis the Lean statement already takes directly (`conj:weak`). No
  deviation found anywhere weakens a conclusion or smuggles in an unproved hypothesis.

One further point belongs here, not because this table makes any false claim
of completeness — its own column header ('Paper label | Lean declaration(s)
| …') shows plainly that it is organized by paper label, not by interface
field — but because enumerating every field of
`ClassicalInputs`'s constituent structures and checking each against a
paper-label row is exactly the audit a careful referee will perform, and five
fields will not turn up by name anywhere in this table:
`AnalyticData.alpha_root`, `AnalyticData.modularSymbol0`,
`IwasawaData.mw_sha_exact`, `KatzData.algInj`, `KatzData.maxIdeal_eq_p`. Each
is a genuine interface field with its own `SOURCE`/`PAPER`/`STATUS` docstring
in its home file (`Interface/Analytic.lean`, `Interface/Iwasawa.lean`,
`Interface/Katz.lean` respectively). What makes them safe to leave
undiscussed here, checked mechanically rather than by inspection — the same
transitive-constant closure scan of §6.6, run with these five names as
markers — is that **no headline theorem's closure touches any of them**:
```
cor_sha5:         undocumented-field deps = []
cor_sha13:        undocumented-field deps = []
prop_consequence: undocumented-field deps = []
thm_reduction:    undocumented-field deps = []
```
These five fields are carried by the interface but consumed by no proved
result. The direction of this is unambiguously safe: an unused field can only
make `ClassicalInputs` *harder* to satisfy — one more proof obligation
`ToyTrivial`/`ToySha` (§4) had to discharge to witness consistency and
non-vacuity — never easier, and it cannot smuggle anything into a conclusion
it plays no role in deriving. A referee running the field-by-field audit this
paragraph anticipates should read these five names as accounted for, not
overlooked.

---

## 3. Certificate provenance

### 3.1 What a "certificate" is here, and why it is a separate structure

`Certificates H` (`FinShaRank2/Interface/Certificates.lean`) packages exactly six
facts about the testbed curve `E : y² = x³ − 56x` at the two anchor primes
`p = 5, 13` — the project's *own* numerical computations, kept in a structure
separate from `ClassicalInputs` precisely so a referee can tell at a glance which
facts are citable published mathematics and which are this project's arithmetic
(§1.4). Note this repository is rooted at `formal/`: the parent project's `data/`
and `scripts/` directories (which independently *produced* these numbers via
PARI/GP and Sage) are **not** part of this repository. What follows records the
certificate values and their provenance inline, directly from the docstrings of
`Interface/Certificates.lean`, so that this document is self-contained for a
referee who has only this repository.

### 3.2 The six fields, verbatim

```lean
structure Certificates (H : ClassicalInputs) where
  five_notin      : 5 ∉ H.S
  thirteen_notin  : 13 ∉ H.S
  a5   : (H.dataAt 5  …).analytic.ap = -2
  a13  : (H.dataAt 13 …).analytic.ap = -6
  c2_5  : PadicInt.toZModPow 7 (coeff 2 (H.dataAt 5  …).analytic.Lp)
            = ((1 + 4*5 + 3*5^2 + 5^3 + 5^5 + 5^6 : ℤ) : ZMod (5^7))
  c2_13 : PadicInt.toZModPow 5 (coeff 2 (H.dataAt 13 …).analytic.Lp)
            = ((1 + 11*13 + 13^2 + 13^3 + 10*13^4 : ℤ) : ZMod (13^5))
```

**Frobenius traces (`a5`, `a13`).** For the testbed curve, verified against PARI/GP
(`ellinit([0,0,0,-56,0])`):
```
$ echo 'ellap(ellinit([0,0,0,-56,0]),5)'  | gp -q
-2
$ echo 'ellap(ellinit([0,0,0,-56,0]),13)' | gp -q
-6
```
So `a_5 = -2` and `a_13 = -6`, matching `main.tex` (§`sec:anchor`: "`a_5 = -2`";
`cor:sha13`: "`a_{13} = -6`, so `#Ẽ(𝔽₁₃) = 20`"). Both are even, as CM evenness of
`a_p` (`AnalyticData.ap_from_CM`) requires. `a_13` feeds `lem:noanomalous`'s
unconditional branch (`13 ≤ p`, no certificate needed there beyond `hasse` +
`ap_from_CM`); `a_5` feeds the one residual case `lem:noanomalous` cannot close
unconditionally (§2, `lem:noanomalous` row).

**Digit congruences (`c2_5`, `c2_13`).** These are the numerical heart of the two
anchor corollaries. Each states that the second Taylor coefficient of the MTT
p-adic L-function, `c₂(p) = coeff 2 L_p ∈ ℤ_[p]`, reduces mod `p^k` to an explicit
digit sum whose *leading* digit is `1` — hence the value is not divisible by `p`,
hence `coeff 2 L_p` is a `p`-adic unit. This is exactly `eq:match5` and `eq:pred13`
of `main.tex`:

* `c2_5` (`eq:match5`): `c₂(5) ≡ 1 + 4·5 + 3·5² + 5³ + 5⁵ + 5⁶  (mod 5⁷)` — seven
  5-adic digits.
* `c2_13` (`eq:pred13`): `c₂(13) ≡ 1 + 11·13 + 13² + 13³ + 10·13⁴  (mod 13⁵)` —
  five 13-adic digits.

The certificate shape is deliberately a *congruence* (an equality of
`PadicInt.toZModPow k` images in `ZMod (p^k)`), not a bare `IsUnit` assertion (board
convention 3: data-equations over bare Props) — so a referee can check the digit
string against an independent computation rather than trusting an opaque Boolean.
The extraction from congruence to unit (`Kernel/Normalization.lean`:
`isUnit_of_toZModPow_cert`, specialised to `isUnit_of_cert_five` /
`isUnit_of_cert_thirteen`) reduces the digit sum further along
`ZMod.castHom → ZMod p`, observes the leading digit `1` survives (so `p ∤` the
value), and concludes `IsUnit (coeff 2 L_p)` via
`PadicInt.isUnit_iff`/`ker_toZMod = maximalIdeal`.

### 3.3 Two independent implementations

`c2_5` was produced by **two independent computational routes that agree
digit-for-digit**: a PARI computation of the p-adic sigma-height side, and an
independent Sage computation of modular symbols on the L-function side. Agreement
of two independently-implemented computations on a seven-digit p-adic expansion is
itself informative — a coding error in either implementation would need to produce
the same wrong answer in both to survive this check.

### 3.4 The p = 13 certificate: a prediction, not a fit

This is the single strongest credibility argument this project can offer for
`cor:sha13`, and it deserves to be stated plainly with its dates:

* **2026-06-12** — the full 13-adic digit expansion `c2_13` was **pre-registered**:
  computed and recorded from the height side (the p-adic sigma-height computation)
  *before* any modular-symbol computation of `L_13(E,T)` existed.
* **2026-07-02** — an independent modular-symbol computation of `L_13(E,T)` at
  level `12544` was carried out, and **every computed digit agreed** with the
  pre-registered prediction.

This is what makes `cor:sha13` a genuine *prediction*, confirmed after the fact by
an independent method, rather than a numerical coincidence found by searching until
something matched. A referee who wants a check with essentially no room for
after-the-fact curve-fitting should look here first. Both digit strings (`c2_5`,
`c2_13`) were additionally cross-checked against `main.tex`'s own statements of
`eq:match5`/`eq:pred13` before the T15 statement freeze.

### 3.5 The `Fact` instances

`Interface/Certificates.lean` declares local instances `Fact (Nat.Prime 5)` and
`Fact (Nat.Prime 13)` so the `ℤ_[5]`/`ℤ_[13]` and `PadicInt.toZModPow`/`ZMod`
machinery in the digit fields type-checks. `Fact` is `Prop`-valued, so by proof
irrelevance these are definitionally equal to the `Fact.mk hp` instances embedded
in `ClassicalInputs.dataAt`'s output type — there is no instance mismatch to worry
about, and this is a bookkeeping detail rather than a mathematical assumption.

---

## 4. The ToyTrivial / ToySha argument

### 4.1 The question this section answers

`ClassicalInputs` is a large structure — roughly two dozen fields spread across four
per-prime layers. A skeptical referee should ask two sharp questions about any large
assumption bundle before trusting theorems proved from it:

* **(Consistency) Could the bundle be self-contradictory?** If so, *every* theorem
  "proved" from it — including the headline results — would be proved from a false
  premise, hence worth nothing (in classical logic, anything follows from a
  contradiction).
* **(Non-question-begging) Does the bundle already contain its own conclusion in
  disguise?** If some interface field secretly forces Ш = 0 as a side effect of
  looking innocuous, then `cor_sha5`/`cor_sha13` would be reporting a *definition*,
  not a *theorem*.

Both questions are answered here not by argument but by **construction**: two
fully worked, Lean-kernel-checked example worlds.

### 4.2 `ToyTrivial` — the assumption bundle is consistent

`FinShaRank2.ToyTrivial : ClassicalInputs` (`FinShaRank2/Toy/Trivial.lean`, built
from the layer files `Toy/Analytic.lean`, `Toy/Iwasawa.lean`, `Toy/Heights.lean`,
`Toy/Katz.lean`) is a complete instance of `ClassicalInputs` in a deliberately
simplified algebraic world — **not** the testbed curve `E`, and no claim is made
that it models `E` in any way. Its only job is to witness that the assumption
bundle can be satisfied at all, with every single field genuinely proved (no
`sorry`, no shortcuts):

| Interface datum | Toy value |
|---|---|
| excluded set `S` | `∅` (every split prime carries data) |
| `δ_E`, `(#tors)²/∏c_v` | `1`, `1` |
| p-adic L-function `L_p` | `X²` (literally the power series `T²`) |
| `a_p`, unit root `α` | `a_p = 2a` from a two-squares decomposition `p = a² + b²`, `α` the Hensel root |
| Iwasawa module `X` | `(Λ/(X))²` |
| Selmer/Ш duals | `SelDual = ℤ_[p]²`, `ShaDual = PUnit` (the one-point group) |
| regulator, Ш-order proxy, height nondegeneracy | `1`, `1`, `True` |
| Katz coefficient ring, `L^{Katz}`, grade-two core | `ℤ_[p]`, `X²`, `1` |

Two points from the construction are worth relaying to a referee rather than taking
on faith: (1) `no_finite_submodule` was not free — it needed genuine
ℤ_[p]-torsion-freeness of `(Λ/(X))²`, actually proved rather than assumed away;
(2) the height-side proxy `c2norm` is *forced* (by the mandatory tie-equation
`c2norm_tie`) to equal `(1 − α⁻¹)⁻²` — it cannot be chosen freely to make the height
fields trivially satisfiable, and the construction had to show the forced value
still satisfies `spr_padicBSD`/`spr_nondeg`. Nothing in the toy world was chosen by
weakening a field's stated content.

**Verdict:** `example : ClassicalInputs := ToyTrivial` compiles, sorry-free, and
`#print axioms ToyTrivial` shows only the three standard axioms. The assumption
surface is consistent.

### 4.3 `ToySha` — the assumption bundle does not beg the question

`FinShaRank2.ToySha : ClassicalInputs` (`FinShaRank2/Toy/ShaTrivial.lean`, layers in
`Toy/ShaAnalytic.lean`, `Toy/ShaIwasawa.lean`, `Toy/ShaHeights.lean`,
`Toy/ShaKatz.lean`) is a **second** complete, fully proved instance of
`ClassicalInputs` — every field satisfied exactly as frozen, no field weakened or
reinterpreted — but built so that the headline conclusion **fails**:

| Interface datum | ToySha value | Contrast with `ToyTrivial` |
|---|---|---|
| p-adic L-function `L_p` | `C p · X²` (so `coeff 2 L_p = p`, a **non-unit**) | was `X²` (`coeff 2 = 1`, a unit) |
| Iwasawa module `X` | `Λ/(X) × Λ/(X) × Λ/(C p)` | was `(Λ/(X))²` |
| Selmer/Ш duals | `SelDual = ℤ_[p]² × ℤ_[p]/(p)`, `ShaDual = ℤ_[p]/(p)` (**nontrivial**) | was `ℤ_[p]²`, `PUnit` |
| Ш-order proxy | `p` (a non-unit) | was `1` (a unit) |
| grade-two core `m2core` | `p` | was `1` |

Everything else — `S = ∅`, `δ_E = 1`, the regulator, `heightNondeg`, and every
citation-grade interface field — is satisfied identically to `ToyTrivial`. The point
is that **nothing forces this world to be excluded by the assumption bundle alone**:
three formal results make this precise.

* **`FinShaRank2.interface_does_not_force_sha_trivial`** — there is *no* proof, from
  `H : ClassicalInputs` and splitness alone, that `Subsingleton ShaDual` (i.e.
  Ш`[p^∞] = 0`) at every split prime. Witnessed directly by `ToySha`.
* **`FinShaRank2.toySha_conclusions_fail`** — stronger: **three of the five**
  headline conclusions fail at **every** split prime of the `ToySha` world
  simultaneously — Ш is not trivial, `MuZero` fails, and `lambdaAn ≠ 2`. This is not
  a single cherry-picked counterexample prime; it is a systematic failure across the
  whole toy world.
* **`FinShaRank2.isEmpty_certificates_toySha`** — and here is the sharpest point of
  the whole non-vacuity/anti-vacuity pair: `Certificates ToySha` is **provably
  empty**. There is no way to instantiate the numerical-certificate structure over
  `ToySha`, because its proof would require `coeff 2 L_p` to have leading 5-adic
  digit `1` (per `c2_5`), but in the `ToySha` world `coeff 2 L_p = 5` — leading digit
  `0`. **The Lean proof of `isEmpty_certificates_toySha` runs through the certificate
  field `c2_5` specifically**, reducing both sides mod `5⁷` and closing by `decide`
  on the resulting numeral disequality. In plain terms: it is not that the interface
  happens to be too weak in some vague sense to pin down Ш — it is *exactly* the
  numerical `c₂` digit certificate that would be needed to rule this world out, and
  that certificate genuinely fails for it. This is about as direct a formal
  demonstration as is available that the certificates in §3 are load-bearing
  mathematics, not decoration: swap in a world where the certificate is false, and
  the certificate structure itself becomes uninhabitable, exactly tracking the
  headline conclusion's failure.

### 4.4 Why a referee should care about both halves

Together, `ToyTrivial` and `ToySha` bracket the design from both sides:

* `ToyTrivial` rules out the concern "maybe this elaborate structure is quietly
  unsatisfiable, and the headline theorems are vacuously true." It is not — it has a
  genuine model.
* `ToySha` rules out the opposite concern, the more common failure mode in an
  interface-first formalization built under time pressure: "maybe some field was
  worded just strongly enough to make the proof go through, secretly assuming the
  conclusion." It does not — there is a genuine model of the *interface* in which the
  *conclusion* is false, so the interface is logically weaker than its conclusion,
  as an assumption bundle should be.

A rigidity finding worth relaying to a referee interested in how tight the interface
actually is: in the `ToySha` construction, the combination of `rubin_structure`
(the Rubin/Washington structure theorem field), `SelmerData.π_surj` (surjectivity
onto the rank-2 Mordell–Weil part), and a nontrivial `ShaDual` together **pin the
elementary-divisor multiset of the Iwasawa module `X` to exactly `(X, X, C p)`** —
every algebraically consistent alternative multiset was checked by the constructing
agent and shown to fail one of the interface constraints. The anti-vacuity witness is
therefore not a lucky accident of a loosely-constrained construction; it is close to
the unique way to falsify the conclusion while honoring every interface field as
written.

---

## 5. Known descopes and why they are harmless

### 5.1 How to read this section

The disposition table in `TASK_BOARD.md` §4 marks a handful of paper items
**not formalized (documented)** or **commentary → docstrings**, and §2 above
tags the corresponding table rows **descoped**. This section is the answer a
referee should not have to extract by cross-referencing three documents: for
every such item, what it is, why an interface-first formalization does not
attempt it, and — the part that actually bears on trust — exactly which
theorem(s) are affected by its absence and which are not.

The governing fact, stated once here rather than repeated nine times below, and
stated precisely because §6.6 hands a referee the tool to check it exactly as
written: **`KatzData`, `D_E`, and all Eisenstein–Kronecker content are absent
outright from the transitive-constant closures of `prop_consequence`,
`prop_dictionary`, `cor_sha5`, and `cor_sha13` — the kernel-proved,
unconditional results.** The one apparent exception, `ClassicalInputs.deltaE`,
is not really one: it occurs in the *type* of `cor_sha5`/`cor_sha13` and in the
*type* of `ClassicalInputs.dataAt` — never in the *value* (proof term) of
anything in either corollary's closure, and under no hypothesis. The reason is
structural and inert, not a hidden dependency: `dataAt`'s signature threads
`δ_E` as a type-level parameter of `PrimeData` (`Interface/Global.lean:229`,
`∀ p hp hsplit, p ∉ S → @PrimeData p _ hsplit deltaE torsSqOverTam`) purely so
`deltaE_tie` can weld the local Katz avatar to the global datum for
`thm_reduction`'s benefit; the anchor corollaries inherit `δ_E` only as an
index on a type they mention in passing (via `H.dataAt`), never as a
hypothesis they assume or a value their proof inspects. This was verified
mechanically, not by inspection — §6.6 below reproduces the exact check. The
asymmetry is exactly what §1.4 claims: `thm_reduction`'s closure genuinely
contains `KatzData`, `ConjStrong`, and `SinnottHyp`; the two anchor
corollaries' closures do not. Every descope in §5.2–§5.3 below therefore lands,
at most, on `thm_reduction` — the one declaration the project has always
presented as conditional — and not on the two anchor corollaries a referee is
likeliest to scrutinise first. Where a descope instead touches material the
anchor corollaries *do* use (§5.4, the heights analytics), this section says
so explicitly and names the citation that absorbs the trust.

Three categories recur below, and each item is labelled with one on
introduction: **(exposition)** — prose with no proposition to formalize;
**(citation)** — the content is real mathematics but is exactly what
`ClassicalInputs`/`Certificates` already exist to absorb as a named, sourced
assumption, so "not formalized" means "assumed, visibly, per §1.3" rather than
"missing"; **(open)** — content the paper itself does not claim to have proved.

### 5.2 The integral content of `prop:jetformula` (and the bookkeeping behind `hyp:sinnott`(i))

**(citation, honestly flagged as such by the paper itself)**

`prop:jetformula` (`main.tex` §`ssec:jetformula`) proves an exact identity:
`c₂(L^K) = (1/2 log_p(1+p)²) ∫ ℓ(g)² dμ_ψ(g)`, obtained by expanding
`(1+T)^{m(g)}` in binomial coefficients of a `ℤ_p`-valued exponent and
integrating termwise against the Katz measure `μ_ψ`. `prop:grading`(1) then
reduces this integral, coset by coset, to the grade-two moment sum `M₂(𝔭)`, and
`§ssec:moments` further identifies `M₂(𝔭)` with an explicit unit-linear
combination of Eisenstein–Kronecker numbers via the Bannai–Kobayashi
interpolation property (BK3).

None of this — the construction of the Katz measure from elliptic units, its
integration theory, the Amice–Mahler correspondence, the binomial-coefficient
calculus of a `ℤ_p`-valued exponent, or the Fourier/Kummer-congruence
bookkeeping that turns polynomial moments into Eisenstein–Kronecker numbers —
exists in mathlib or in this project. Building it would mean formalizing a
working theory of `p`-adic measures on profinite groups and their Amice
transforms from scratch: a project on the scale of task T61 (scoped, in the
board's stretch phase, as an "abstract jet/binomial skeleton" covering only the
*elementary* combinatorial fragment `c₂ = ½∫m² − ½∫m`, explicitly **not**
attempted) times several, once the actual Eisenstein–Kronecker calculus is
included.

What is formalized instead is only the **resulting algebraic congruence**:
`KatzData.grading_congr : ∃ κ₀ : Wˣ, p² · (κ₀ · coeff 2 LKatz − m2core) ∈ (p³)`
— an interface field with `SOURCE: Bannai–Kobayashi Prop. 3.3 / Thm. 3.7 (Duke
Math. J. 153 (2010)) + de Shalit II §4`, `STATUS: consequence-form`. Its
docstring is explicit about the boundary: *"the Eisenstein–Kronecker bookkeeping
identifying `M₂(𝔭)`/`m2core` 'to the last constant' is **not** carried in
Lean. This field records only the resulting algebraic congruence."* That
sentence is this project's own honest admission, not a claim of a citation this
formalization does not have — and it is exactly the same admission the paper
makes about `hyp:sinnott`(i) ("Bannai–Kobayashi calculus bookkeeping … we expect
it to be provable by those methods; we state it as part of the hypothesis
because we have not carried out the bookkeeping to the last constant"). The
Lean rendering does not paper over this: `grading_congr` is a `KatzData` field
consumed exactly like a citation, with the caveat visible in-file.

**Effect on the headline results.** `KatzData` — hence `grading_congr`, hence
this entire descope — is touched by exactly one declaration: `thm_reduction`,
which the project has always presented as conditional on `hyp:sinnott` and
`conj:EK` (§1.4, §2). `prop_consequence`, `prop_dictionary`, `cor_sha5`, and
`cor_sha13` never destructure `.katz` from a `PrimeData` at all (§5.1). So this
descope shifts trust onto a citation (Bannai–Kobayashi's second-moment
calculus) *inside a declaration that was already conditional*; it changes
nothing about the status of the two anchor corollaries.

### 5.3 The geometry of `D_E` and the definition of `δ_E`

**(citation for the definitional shape; `δ_E ≠ 0` itself is `conj:EK`, an open conjecture)**

`def:deltaE` (`main.tex` §`ssec:reduction`) constructs `D_E` as the divisor of
definition of the fixed theta-jet package `𝓡_E` on a zero-dimensional
`Q̄`-scheme (the `𝔣`-torsion translates of the central parameter), and `δ_E` as
the resultant-norm `Nm_{/ℚ} Res(…)` of the grade-two combination of `𝓡_E`
prescribed by `M₂`. The paper is explicit that the recipe is "algorithmic for
any given curve" — theta-quotient expressions in `℘, ℘′, ζ` and the quasi-period
`s₂` of the CM lattice, evaluated at `56`-division values of the lemniscatic
lattice for the testbed — but also explicit that carrying it out is **future
work**: `rmk:correlation` names "computing `δ_E` for the testbed … the decisive
experiment" as "phase two of this programme," not something the paper itself
has done.

Formalizing `D_E` would require the algebraic theta-function machinery (the
Kronecker theta function, Weierstrass `℘/℘′/ζ` at division values, CM
quasi-periods), a formal resultant over a number field, and `Nm_{/ℚ}` — none of
it existing in mathlib, and none of it computed even informally for the
testbed curve yet. There is, at present, no concrete numerical object to
formalize a construction of.

The Lean rendering matches this precisely rather than fabricating a
construction: `KatzData.deltaE_local : ℚ` is **opaque data** — a bare rational
number, `SOURCE: def:deltaE (resultant-norm of the fixed algebraic expression);
Bannai–Kobayashi (BK2) algebraicity`, `STATUS: data` — and `resultant_link :
deltaE_local ≠ 0 → padicValRat p deltaE_local = 0 → NonvanishingOnDE` records
only the abstract resultant-norm property (a classical fact about resultants,
`STATUS: classical`), not a derivation from an actual theta-jet computation.
`δ_E ≠ 0` itself is `conj:EK`, one of the paper's two named open conjectures
(§1.4); the Lean formalization does not assert it anywhere, only receives it as
hypothesis `h87` of `thm_reduction`.

**Effect on the headline results.** As in §5.2: `δ_E`, `D_E`, and
`NonvanishingOnDE`/`resultant_link` are consumed only by `thm_reduction`. The
two anchor corollaries never construct or reference `D_E`; their unconditional
status is untouched. What this descope *does* mean honestly: a referee should
not expect the Lean repository to contain any evidence, numerical or formal,
that `δ_E ≠ 0` for the testbed curve — the paper does not claim to have that
evidence yet either, and `thm_reduction`'s conditional status already signals
this at the type level.

### 5.4 The heights analytics: what `Reg_γ` does and does not carry into the kernel

**(citation — and the one descope in this section that a referee should read
most carefully, because it *does* touch the anchor corollaries)**

`main.tex` §`sec:anchor` computes the cyclotomic `p`-adic regulator `Reg_p` of
the fixed basis `{P₁, P₂}` via the `p`-adic sigma function (Mazur–Stein–Tate),
by two independent implementations (PARI's `ellpadicregulator`, Sage's
`padic_regulator`) that agree digit for digit, e.g.
`Reg_5 = 5² + 3·5³ + 3·5⁴ + … (mod 5^13)`. This computation is **not**
reproduced or re-verified anywhere in this repository, and — this is the point
worth stating precisely — **it does not need to be**, for a reason specific to
how `prop_dictionary` is proved.

`HeightData.Reg_γ : ℚ_[p]` is opaque data (no sigma-function construction
behind it in Lean); `spr_padicBSD` and `spr_nondeg` are citation-grade fields
(`SOURCE: Schneider, Invent. Math. 79 (1985); Perrin-Riou, Invent. Math. 109
(1992); packaged as Stein–Wuthrich Thm 6.1`). `spr_nondeg` states an **iff**:
`IsPUnit c2norm ↔ (heightNondeg ∧ IsPUnit Reg_γ ∧ IsPUnit shaOrd)`. The fifth
conclusion of `cor_sha5`/`cor_sha13` (height-pairing nondegeneracy) is derived
— via `prop_dictionary`, whose entire proof is the three rewrites
`c2norm_tie.symm → spr_nondeg → shaOrd_tie` (T32 board report) — by reading
this iff in the **forward** direction from `IsPUnit c2norm`, which the
certificates `c2_5`/`c2_13` already establish independently on the
*L-function* side. The proof never needs to know `Reg_γ`'s numeric value, its
digit expansion, or even that a specific PARI/Sage computation produced it —
only that *some* element of `ℚ_[p]` exists satisfying the cited tie-equations.
`reg_integral` and `sha_integral` (the ‖·‖ ≤ 1 integrality facts) are, per the
same T32 report, **unused** by the proof that lands in `cor_sha5`/`cor_sha13`.

Put plainly: **the specific digit strings `Reg_5`, `Reg_13` displayed in
`main.tex` play no role in the Lean proof of `cor_sha5`/`cor_sha13` at all.**
In the paper they serve a real epistemic purpose — an independent numerical
route to the same `eq:match5`/`eq:pred13` identity that the L-function side
already certifies, strengthening the reader's confidence that the identity is
not a bookkeeping artefact — but that purpose is narrative corroboration
external to the Lean chain, not a premise the kernel checks. The Lean proof's
entire numerical content, at both anchor primes, runs through the certificates
`c2_5`/`c2_13` of §3 (the L-function side only); the height side enters solely
as the *citation* `spr_padicBSD`/`spr_nondeg`, exactly as any other classical
theorem in `ClassicalInputs` does. A referee auditing what the kernel actually
checked should not come away thinking two independent numerical computations
were verified — only one was (§3.3–§3.4), and the other is real, corroborating,
externally-reproducible mathematics that this formalization is honest about
not having touched.

### 5.5 §3 background: the Sinnott–Gillard mechanism and (BK1)–(BK3)

**(exposition, with two partial exceptions that are already citations elsewhere)**

`main.tex` §`sec:gillard` is explicitly labelled expository by the paper itself
("This section is expository"): it recalls the Katz measure's construction
from elliptic units, states Gillard's theorem (`thm:gillard`, the vanishing of
the `μ`-invariant of every branch of the Katz measure — the "zeroth jet"
analogue of the paper's own second-jet question), sketches the shape of
Sinnott's proof, and states the three Bannai–Kobayashi structural theorems
(BK1)–(BK3) (generating function, algebraicity, `p`-adic interpolation) that
package the Katz measure's moments as Eisenstein–Kronecker numbers. None of it
is presented as new — every result is attributed (Katz, Sinnott, Gillard,
Bannai–Kobayashi, de Shalit) — and its purpose in the paper is motivational:
explaining *why* one might hope the paper's second-jet question is horizontally
rigid, by exhibiting the zeroth-jet case as an established instance.

**`thm:gillard` itself is not needed anywhere in the Lean interface** — checked
directly: no interface field cites Gillard's theorem as a `SOURCE`. The
Iwasawa-module structure the formalization actually needs
(`IwasawaData.rubin_structure`) cites Washington GTM 83 Thm. 13.12 fused with
Rubin's cyclotomic main conjecture (Invent. Math. 103 (1991), Thm. 12.3), a
different, two-variable-to-cyclotomic-line result; the zeroth-jet vanishing
that Gillard's theorem supplies is simply not a hypothesis of any theorem in
this project. **(BK1)–(BK3)** fare slightly differently: they are the informal
justification behind two citation-grade interface fields already logged in
§2 — `lem:comparison` (`KatzData.comparison`, `SOURCE: Bannai–Kobayashi
Cor. 3.12`) and `grading_congr`/`hyp:sinnott` (`SOURCE: Bannai–Kobayashi
Prop. 3.3/Thm. 3.7`, `§§2–3 calculus`) — but the *general* structural theorems
(BK1)–(BK3), stated for an arbitrary CM lattice and arbitrary torsion
parameters, are not themselves rendered as Lean propositions; only their
specific consequences for this curve are, as the two fields just named. This
is the same descope already accounted for in §5.2 under a different name, not
an additional one.

**Effect on the headline results.** None whatsoever, on two independent
grounds: (1) `thm:gillard` is not cited by any interface field in the project,
kernel-proved or otherwise; (2) the two BK-derived fields it partially
motivates (`comparison`, `grading_congr`) live in `KatzData`, which — per
§5.1 — is untouched by `prop_consequence`, `prop_dictionary`, `cor_sha5`, and
`cor_sha13`. §`sec:gillard` could be deleted from `main.tex` entirely without
changing a single Lean declaration.

### 5.6 §6: the 508-prime horizontal regulator scan

**(exposition — an experiment, not a claim with a proof obligation)**

`main.tex` §`sec:scan` computes `v_𝔭(Reg_𝔭)` at 508 split primes in four
contiguous windows (up to `p = 16889`), all via PARI's `ellpadicregulator`,
finding the generic value `2` at every one, with zero escalations under the
paper's own precision-margin protocol. By `prop:dictionary`, a clean scan
result is *necessary* (not sufficient — it tests only the regulator half of
the unit-condition conjunction, not the Ш half) for the strong conjecture to
survive as a falsification test; an abundance of exceptions would refute it
outright.

This is a numerical experiment, not a theorem: it has no proof obligation to
discharge, and "not formalized" here means exactly what it says — the 508
individual PARI computations are not reproduced in Lean, and there is no
`Certificates`-style structure recording them. Formalizing even a handful of
them would require generalizing the `Certificates` design (currently exactly
two primes, `p = 5, 13`) to a scan-scale structure, at a cost proportional to
the number of primes and with zero return in kernel-checked content beyond
what the two anchor primes already deliver — because, as noted in §5.5's
counterpart discussion, the scan's algebraic meaning (`rmk:correlation`) is
tied to `thm_reduction`, the conditional theorem, not to `cor_sha5`/`cor_sha13`.

**Effect on the headline results.** None: `cor_sha5` and `cor_sha13` are
proved at exactly the two primes `p = 5, 13`, via `Certificates`, independently
of anything the scan measures at the other 506 primes. A referee evaluating
*only* the two anchor corollaries can disregard §`sec:scan` entirely. A
referee evaluating the paper's broader case for `conj:strong` (the conjecture,
not the theorems) should read the scan exactly as the paper presents it: real,
independently-reproducible PARI computation, offered as evidence for a stated
conjecture, and not claimed by the paper — or by this document — to be a
proof of anything.

### 5.7 §9: the outlook section

**(exposition — forward-looking discussion, no propositions to check)**

`main.tex` §`sec:outlook` discusses the inert-prime analogue of the paper's
question (supersingular reduction, no unit root, no classical Katz measure —
citing Burungale–Kobayashi–Ota's proof of Rubin's local-units conjecture and
Pollack–Rubin's supersingular CM main conjecture as the relevant foundations,
while noting the correct formulation of generic `±`-regulator valuation at
rank two is "not in the literature"), poses "Bertrand for determinants" as an
open problem (nonvanishing of the determinant of the height pairing matrix at
almost all split primes for a rank-two curve — no case known, for any curve),
and discusses what a proof of the weak conjecture would and would not deliver.

None of this states a proposition about the paper's own results that a Lean
proof could discharge; it is explicitly a discussion of what is *not yet
known*, posed as open problems for future work. There is nothing here with a
truth value to formalize.

**Effect on the headline results.** None: §`sec:outlook` makes no claim about
`E : y² = x³ − 56x` or about `cor:sha5`/`cor:sha13` that the formalization
could either support or undermine. Its only connection to the rest of this
document is that "Bertrand for determinants," if proved for the testbed curve
at almost all split primes, would settle the height-nondegeneracy half of
`conj:weak` unconditionally — a fact the paper states about a hypothetical
future proof, not about anything proved here.

### 5.8 The five prose remarks: `cav:failure`, `rmk:KL`, `rmk:fq`, `rmk:modesnow`, `rmk:correlation`

**(exposition, in every case — but each is worth a sentence on *why* it has no proof obligation)**

* **`cav:failure`** names two failure modes for `conj:strong`: (A) irreducible
  `𝔭`-dependence of the cyclotomic-direction jet, and (B) a Wieferich-type
  collapse of `δ_E`. This is a risk taxonomy for a conjecture, not a
  proposition; its mathematical content is exactly what §1.4's epistemic split
  already renders formally, by isolating `hyp:sinnott` (mode A) and `conj:EK`
  (a necessary condition against mode B) as the project's only two conjectural
  hypotheses. Formalizing the taxonomy itself would mean formalizing a
  classification of *ways a conjecture could fail* — not a mathematical claim.
* **`rmk:KL`** is a comparative discussion of the Kubota–Leopoldt setting
  (Ferrero–Washington rigidity of the `μ`-invariant vs. Iwasawa-invariant
  irregularity governed by wandering Bernoulli numbers) offered as an analogy
  and a cautionary precedent for failure mode (B). It is folklore from a
  different, classical body of Iwasawa theory, cited but not used in any proof
  step of this paper; formalizing it would mean formalizing Kubota–Leopoldt
  `p`-adic `L`-functions and Ferrero–Washington's theorem, an unrelated project.
* **`rmk:fq`** explains *why* `lem:decoupling` matters: at a double zero, the
  product rule kills first-order (Fermat-quotient-carrying) contributions from
  the comparison and Euler factors. The mathematical content of this remark
  is `lem:decoupling` itself, which **is** kernel-proved
  (`Kernel/Decoupling.lean`, ring-generic — §2 above). The remark is framing
  around an already-formalized lemma; there is no separate proposition beyond
  the lemma's own statement.
* **`rmk:modesnow`** identifies mode (A) with the failure of `hyp:sinnott` and
  explains that mode (B) would have to act through the trace itself, since
  `lem:decoupling` (again, kernel-proved) already rules it out of the two
  visible channels. This is commentary connecting two pieces already present
  in the formalization — the hypothesis-position status of `SinnottHyp`
  (§1.4) and the proof of `lem:decoupling` — not new content.
* **`rmk:correlation`** explains how the 508-prime scan (§5.6) acquires
  "algebraic meaning" through `thm:reduction`, and flags that computing `δ_E`
  for the testbed curve is "phase two of this programme" — i.e., explicitly
  future work, not yet done even informally. Its content is the D_E/`δ_E`
  descope of §5.3, restated in interpretive terms; nothing further to add.

**Effect on the headline results.** None of these five items states a
mathematical proposition that feeds into any proof step of
`prop_consequence`, `prop_dictionary`, `thm_reduction`, `cor_sha5`, or
`cor_sha13`. This is exactly why `TASK_BOARD.md` §4 dispositions all five as
"prose → FORMALIZATION.md" rather than assigning any of them a proof task:
they were never claims requiring proof, only commentary a referee should be
able to read once, here, rather than reconstruct from the paper.

### 5.9 Two loose ends closed: `rmk:nofinitesub` and `rmk:normalisation`(ii)–(iii)

§2's table tags `rmk:nofinitesub` **descoped (prose)** with a pointer back to
this section; unlike the seven items above, its underlying mathematical
content is *not* actually absent from the formalization, so it deserves a
one-paragraph correction rather than a fresh entry in the ledger of §5.10.

`rmk:nofinitesub` is a remark about *proof strategy*: it observes that the
paper's proof of `prop:consequence` avoids the `p`-adic leading-term formalism
at Step 3–4 by using the elementary structure argument "no finite submodule +
rank forcing `M = 0`" instead. The fact this remark discusses,
`IwasawaData.no_finite_submodule` (`SOURCE: Greenberg, LNM 1716, Prop. 4.14`),
**is** a genuine interface field, and it **is** consumed by the kernel-proved
`prop_consequence` (Step 3, per its own `PAPER` docstring pointer). So only the
remark's own English commentary — "the proof deliberately avoids the leading-
term formalism" — has no separate Lean rendering; the mathematics it is
commenting on is already visible in §2's `prop:consequence` row via
`no_finite_submodule`'s citation. Zero trust shift here: a referee checking
`no_finite_submodule` against Greenberg's Prop. 4.14 has already checked
everything `rmk:nofinitesub` refers to.

`rmk:normalisation` has three parts; §2 names only part (i) as a kernel-proved
lemma (`isPUnit_c2tilde_iff_of_split`). Parts (ii) and (iii) need no separate
row: (ii) is a restatement, in words, of exactly the identity `eq:padicbsd`
already states and that `HeightData.spr_padicBSD`/`spr_nondeg` already carry
as citation-grade fields (§2, §5.4) — it adds no content beyond framing. Part
(iii) — integrality of `c₂(p)` — needs no interface field at all, because it
is **automatically true by the Lean type**: `AnalyticData.Lp : Λ p` where
`Λ p := PowerSeries ℤ_[p]` (`Defs.lean`), so every coefficient of `Lp`,
including `coeff 2 Lp`, is by construction already an honest element of
`ℤ_[p]` — there is no separate "integrality" hypothesis to assume or prove,
exactly matching the paper's own assessment that "the integrality assertion
… is therefore not the substance of the conjecture; the unit assertion is."

### 5.10 Summary: where the trust actually sits

| Item | Category | Trust lands on | Touches anchor corollaries? |
|---|---|---|---|
| `prop:jetformula` integral content (§5.2) | citation, self-flagged | Bannai–Kobayashi §§2–3 calculus, via `grading_congr` | No — `thm_reduction` only |
| `D_E` geometry / `δ_E` (§5.3) | citation (shape) + open (nonvanishing) | resultant-norm classical fact; `conj:EK` itself is open | No — `thm_reduction` only |
| Heights analytics, `Reg_γ`'s digit expansion (§5.4) | citation | Schneider/Perrin-Riou via Stein–Wuthrich Thm 6.1 (`spr_nondeg`) | **Yes, via the citation** — but not via the digit expansion itself |
| §3 background, `thm:gillard`/(BK1)–(BK3) (§5.5) | exposition (+ overlaps §5.2's citation) | nothing beyond §5.2's citation | No |
| §6 the 508-prime scan (§5.6) | exposition | nothing — an experiment, not a claim | No |
| §9 outlook (§5.7) | exposition | nothing — open problems | No |
| Five prose remarks (§5.8) | exposition | nothing beyond already-logged citations/lemmas | No |
| `rmk:nofinitesub` (§5.9) | already formalized, mislabelled by nothing but its own prose | `no_finite_submodule` (Greenberg LNM 1716) | Yes — but via a row already in §2 |
| `rmk:normalisation`(ii)–(iii) (§5.9) | (ii) restates `eq:padicbsd`; (iii) automatic by type | nothing new | Yes — but via rows already in §2 |

The pattern is deliberate, not coincidental: every descope that reaches the two
unconditional anchor corollaries (`cor_sha5`, `cor_sha13`) does so **only**
through material already carried as a named, sourced field of
`ClassicalInputs` — never through an unexamined gap. The descopes that involve
a genuinely open question (`conj:EK`'s nonvanishing, and by extension
`hyp:sinnott`) are confined to `thm_reduction`, exactly where the paper itself
places them. Nothing in this section should be read as "harmless because
unimportant" — §5.4 in particular is load-bearing mathematics that this
project chose to trust as a citation rather than reconstruct; "harmless" here
means specifically *harmless to the unconditional status of `cor_sha5` and
`cor_sha13`*, which is the claim §1–§4 make and the claim this section has now
checked, item by item, rather than asserted.

---

## 6. Build and audit instructions

### 6.1 Toolchain and dependencies

All commands below are run from the `formal/` directory — the root of this
repository (§3.1: the parent project's `main.tex`, `data/`, and top-level
`scripts/` are **not** part of this repository and are not needed to run the
audit).

* **Lean toolchain**: pinned by `formal/lean-toolchain`, which reads
  ```
  leanprover/lean4:v4.33.1
  ```
  `elan` (the standard Lean version manager) reads this file automatically on
  `lake build`/`lake exe`; a referee with `elan` installed does not need to set
  anything by hand.
* **Mathlib**: pinned by `formal/lake-manifest.json`, whose `mathlib` entry
  records
  ```
  "rev": "0df444a360eaa60ab8c11dca51a86af692955474"
  ```
  (`inputRev: "v4.33.1"`). This is the exact commit every one of the 74 audited
  declarations was checked against (§1.2). **Do not run `lake update`** —
  it re-resolves the manifest and can move this pin; the project has an open
  PM decision (`TASK_BOARD.md`, carried forward) to leave `lake update`
  untouched precisely to avoid disturbing it. Re-cloning or checking out this
  repository fresh reproduces the pin automatically, since `lake-manifest.json`
  is tracked.

With those two files in place, the three commands below are all a referee
needs to run, in order, from `formal/`.

### 6.2 `lake exe cache get`

```
$ lake exe cache get
Current branch: HEAD
Using cache from origin: (some leanprover-community/mathlib4)
No files to download
Already decompressed 8690 file(s)
```

This downloads precompiled `.olean` files for mathlib (and its own
dependencies) at the pinned revision from the mathlib community's public
cache, so a referee does not have to compile all of mathlib from source —
compiling mathlib itself, rather than just this project's own files, is the
dominant cost of a genuinely cold build and can take on the order of an hour
or more on ordinary hardware if the cache step is skipped or unavailable.
**On a cold clone**, this step downloads and decompresses several thousand
`.olean` files (a multi-gigabyte transfer); its wall time is therefore
dominated by network bandwidth, not CPU, and is not something this run can
honestly report a number for. **The run quoted above is warm** — this
project's `.lake` directory already had every mathlib file decompressed from
earlier work in this session, so `cache get` correctly reports "No files to
download" and finishes in about ten seconds, all of it local decompression
bookkeeping. A referee starting from a fresh clone should expect a real
download here; everyone after that first run gets the fast path shown above.

### 6.3 `lake build`

```
$ lake build
Build completed successfully (8736 jobs).
```
(Observed wall time: 4.5s.)

**Honesty note, as instructed:** this repository's tree was already fully
built when this command was run — `formal/.lake/build` already held every
`.olean` from this project's own files (`FinShaRank2/`) as well as mathlib's,
left over from earlier work in this session. `lake build` therefore did no
compilation at all here; it walked the dependency graph, found all 8736 jobs
(mathlib's plus this project's own) already up to date, and reported success
immediately. This is a **warm no-op**, not a from-scratch timing, and this
document does not claim otherwise. A referee running this on a genuinely cold
`.lake` (after `cache get` has restored mathlib's precompiled `.olean`s, as
in §6.2) will see `lake build` actually compile this project's own files —
`FinShaRank2/` is not a large library by mathlib standards, so with mathlib
already cached this step should be substantially faster than the mathlib
download itself, but this document reports no specific cold number for it,
since producing one would require clearing `.lake` — an operation this task
was explicitly instructed not to perform, to avoid disturbing the pinned
mathlib build. If `lake build` is ever run before `lake exe cache get` on a
cold clone, expect it to instead compile mathlib from source, which is the
hour-plus cost §6.2 describes.

### 6.4 `./scripts/audit.sh`

The full, unedited output of `./scripts/audit.sh` (run from `formal/`),
observed wall time 19.1s (warm — see §6.3's caveat; step [1/3] alone is the
`lake build` of §6.3):

```
=== [1/3] lake build ===
Build completed successfully (8736 jobs).
[1/3] OK: lake build green

=== [2/3] sorry/admit scan (FinShaRank2/, excluding Scratch/) ===
[2/3] OK: no disallowed sorry/admit

=== [3/3] axiom audit (FinShaRank2/AxiomAudit.lean) ===
AxiomAudit OK: FinShaRank2.constantCoeff_σ uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.coeff_one_σ uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.hasSubst_σ uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.isUnit_one_sub_alphaInv_iff uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.isPUnit_one_sub_alphaInv_iff uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.ap_ne_one_of_hasse uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.neg_two_ne_one_zmod_five uses only [propext, Quot.sound]
AxiomAudit OK: FinShaRank2.two_dvd_ap uses only []
AxiomAudit OK: FinShaRank2.noAnomalous uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Decoupling.coeff_two_mul uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Decoupling.coeff_two_mul_of_snd_low uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Decoupling.coeff_two_mul_of_fst_low uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Decoupling.coeff_smul_eq_mul uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Decoupling.coeff_eq_zero_of_map_eq_zero uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Decoupling.isUnit_coeff_two_map_iff uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Decoupling.isUnit_coeff_two_of_comparison uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.σR uses only [propext, Quot.sound]
AxiomAudit OK: FinShaRank2.constantCoeff_σR uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.coeff_one_σR uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.hasSubst_σR uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.oneAddX_mul_σR uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.coeff_one_σR_pow_of_ne uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.coeff_one_subst_σR uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.coeff_one_eq_zero_of_functionalEquation uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.coeff_one_Lp_eq_zero uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.dvd_of_pow_mul_mem_span_pow_succ uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.isUnit_iff_residue_ne_zero_of_grading_congr uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.selmer_dual_structure uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.quotient_collapse uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.rank_lower_bound uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.isPUnit_c2tilde_iff uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.isUnit_of_toZModPow_cert uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.isUnit_of_toZModPow_cert' uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.isUnit_of_cert_five uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.isUnit_of_cert_thirteen uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.eq_five_or_thirteen_le uses only [propext, Quot.sound]
AxiomAudit OK: FinShaRank2.isPUnit_one_sub_alphaInv_of_split uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.isPUnit_c2tilde_iff_of_split uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.sha_endgame uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.sha_endgame_of_nonempty uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.tsq_factor uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.order_eq_two_of_factored uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.muZero_of_factored uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.lambdaAn_eq_two_of_factored uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.associated_X_sq_of_factored uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.order_eq_two_of_coeffs uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.muZero_of_coeffs uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.lambdaAn_eq_two_of_coeffs uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.associated_X_sq_of_coeffs uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.coeffs_X_sq uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.c0_eq_zero uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.c1_eq_zero uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.prop_consequence uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.prop_dictionary uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.thm_reduction uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.cor_sha5 uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.cor_sha13 uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Toy.toyAnalytic uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Toy.toySelmer uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Toy.toyIwasawa uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Toy.toyHeight uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Toy.toyKatz uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Toy.toyPrimeData uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Toy.shaAnalytic uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Toy.shaSelmer uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Toy.shaIwasawa uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Toy.shaHeight uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Toy.shaKatz uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Toy.shaPrimeData uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.ToySha uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.interface_does_not_force_sha_trivial uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.toySha_conclusions_fail uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.isEmpty_certificates_toySha uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.ToyTrivial uses only [propext, Classical.choice, Quot.sound]
AxiomAudit: all 74 audited declaration(s) clean
[3/3] OK: axiom whitelist holds for all audited decls

AUDIT: PASS
```

Reproduced verbatim from a run of `./scripts/audit.sh` on this session's tree,
HEAD `f22e1bf`, on 2026-08-18.

### 6.5 Reading a PASS

`scripts/audit.sh` runs three independent checks, in order, and each has to
pass before the next runs meaningfully (the script exits immediately on a
`[1/3]` failure; `[2/3]` and `[3/3]` both run and both must report `OK` for
the final `AUDIT: PASS`):

* **`[1/3] lake build`** — the whole project, including mathlib, must
  typecheck with no errors. This is the ordinary Lean compiler; a failure here
  means the code does not even parse/elaborate, and nothing downstream is
  meaningful. `[1/3] OK: lake build green` is Lean's kernel having accepted
  every declaration's *type*; it says nothing yet about `sorry` or axioms.
* **`[2/3]` the no-incomplete-proof scan** — `grep -rnE '\b(sorry|admit)\b'`
  over `FinShaRank2.lean` and `FinShaRank2/` (excluding the scratch directory
  `FinShaRank2/Scratch/`, which is explicitly not part of the audited
  library), with any match checked against `scripts/sorry-allowlist.txt`.
  **That allowlist is currently empty** (19 lines, all comments — see the file
  itself for the historical note explaining it was nonempty only during the
  T15→T34 statement-freeze window and was emptied once every frozen signature
  was proved). An empty allowlist means step `[2/3]` accepts **zero**
  `sorry`/`admit` anywhere under `FinShaRank2/` outside `Scratch/` — this is
  the single strongest, most literally-checkable claim in this whole document:
  not "the headline theorems are sorry-free" (which the allowlist mechanism
  could in principle hide exceptions from) but "nothing under active
  development is sorry-free", full stop, because there is nothing left on the
  allowlist to hide behind. `[2/3] OK: no disallowed sorry/admit` in the
  transcript above is exactly this: the grep found nothing to flag.
* **`[3/3]` the axiom gate** — `lake env lean FinShaRank2/AxiomAudit.lean`
  elaborates a small program that calls Lean's own `Lean.collectAxioms` on
  each of the 74 names in `AxiomAudit.auditedDecls` (the five headline
  theorems, both toy instances layer-by-layer, and every kernel lemma feeding
  them — the full list is visible in the file, organized by task) and fails
  elaboration — hence fails the whole script — if any declaration is missing
  or transitively depends on an axiom outside `{propext, Classical.choice,
  Quot.sound}`. This also catches `native_decide` (which would otherwise
  silently introduce `Lean.ofReduceBool`, a form of trust this project
  deliberately excludes). Each `AxiomAudit OK: … uses only […]` line in the
  transcript is one declaration's individual result; the summary line
  `AxiomAudit: all 74 audited declaration(s) clean` is what a referee should
  actually look for — it is machine-generated from the same `auditedDecls`
  list, so its count (`74`) is directly checkable against the file, not a
  number this document could misreport without the two disagreeing.

The final `AUDIT: PASS` on its own line is the conjunction of all three. A
referee reproducing this document's claims needs to see exactly that line,
together with the empty-allowlist fact and the `74` count, to have checked
everything §1.2 asserts about this repository by mechanical means rather than
by trusting this document's prose.

### 6.6 Checking the epistemic split mechanically: a transitive-constant scan

`scripts/audit.sh` certifies *axiom-cleanliness* — that nothing outside the
three standard axioms is used. It does not, by itself, certify the *narrower*
and arguably more interesting claim of §1.4/§5.1: that the two anchor
corollaries' proofs never touch the conjectural surface (`KatzData`, `δ_E`'s
nonvanishing, `SinnottHyp`) at all, as opposed to touching it and happening to
avoid the two named conjectural hypotheses specifically. That claim is
checkable by walking the full transitive closure of constants each
declaration's *type and proof term* depend on and testing which of them mention
Katz/Sinnott/δ_E-flavoured names. The following program does exactly that; it
is not part of the audited library (it imports `FinShaRank2` as a client, and
belongs in a scratch file — e.g. `formal/Scratch/AxiomScan.lean` — never under
`FinShaRank2/`, so it is not itself subject to `scripts/audit.sh`'s sorry scan
or axiom gate):

```lean
import FinShaRank2

open Lean in
partial def deps (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  match env.find? n with
  | some ci =>
      for c in ci.type.getUsedConstants do deps env c
      match ci.value? with
      | some v => for c in v.getUsedConstants do deps env c
      | none => pure ()
  | none => pure ()

def has (s t : String) : Bool := ((s.splitOn t).length > 1)

def markers : List String :=
  ["KatzData", "deltaE", "SinnottHyp", "Sinnott", "NonvanishingOnDE",
   "thm_reduction", "ConjStrong", "ConjWeak", "jetformula", "traceClass", "m2core"]

open Lean Elab Command in
elab "#scan " id:ident : command => do
  let env ← getEnv
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  let (_, s) := (deps env n).run {}
  let bad := s.toList.filter (fun m => markers.any (has m.toString))
  logInfo m!"{n}: total deps = {s.size}, conjectural deps = {bad}"

#scan FinShaRank2.cor_sha5
#scan FinShaRank2.cor_sha13
#scan FinShaRank2.thm_reduction
```

Save this as, e.g., `Scratch/AxiomScan.lean` under `formal/` and run it as
`lake env lean Scratch/AxiomScan.lean` from `formal/` (`lake env` sets up the
environment for the current package; the file itself need not live under
`FinShaRank2/`). Reproduced verbatim from a run on this session's tree, HEAD
`f22e1bf`:

```
FinShaRank2.cor_sha5: total deps = 2609, conjectural deps = [FinShaRank2.ClassicalInputs.deltaE]
FinShaRank2.cor_sha13: total deps = 2610, conjectural deps = [FinShaRank2.ClassicalInputs.deltaE]
FinShaRank2.thm_reduction: total deps = 2024, conjectural deps = [FinShaRank2.KatzData,
 FinShaRank2.ConjStrong,
 FinShaRank2.ConjStrong._proof_1,
 FinShaRank2.thm_reduction,
 FinShaRank2.SinnottHyp,
 FinShaRank2.ClassicalInputs.deltaE]
```

**How to read this.** `deps` is a plain worklist closure over
`Expr.getUsedConstants`, applied to both a declaration's *type* and its
*value* (proof term), recursively over everything it finds — so the `total
deps` count (2609–2610 for the anchor corollaries, 2024 for `thm_reduction`,
overwhelmingly mathlib) is the complete set of constants each declaration's
statement-plus-proof rests on. `markers` is a coarse substring filter for
anything Katz/Sinnott/δ_E-flavoured; `conjectural deps` is that filter applied
to the closure. Two things to check in the output:

1. **The asymmetry is exactly §1.4's claim, made mechanical.**
   `thm_reduction`'s closure genuinely contains `KatzData`, `ConjStrong`
   (twice, once for its `_proof_1` auto-generated companion), and `SinnottHyp`
   — the real conjectural surface, present because `thm_reduction` really does
   consume it. The two anchor corollaries' closures contain **none** of these;
   their only hit is `ClassicalInputs.deltaE`, and it is not the same kind of
   hit.
2. **`ClassicalInputs.deltaE` in the anchor corollaries is an inert
   type-level index, not an assumption.** Splitting the same closure by
   *where* `deltaE` is found — in a node's type versus in a node's value —
   shows it occurs only in the *type* of `cor_sha5` (its statement mentions
   `H.dataAt 5 …`) and in the *type* of `ClassicalInputs.dataAt` (whose
   signature is `∀ p hp hsplit, p ∉ S → @PrimeData p _ hsplit deltaE
   torsSqOverTam`, `Interface/Global.lean:229` — `δ_E` threaded purely so
   `deltaE_tie` can weld the Katz-layer local avatar to the global datum for
   `thm_reduction`'s benefit). It occurs in the *value* — the actual proof
   term — of **nothing** in `cor_sha5`'s closure: no hypothesis about `δ_E`
   is assumed, and no proof step inspects it. A referee who wants to check
   this split directly can adapt `#scan` to record, for each node in the
   closure, whether the marker constant appears in `ci.type.getUsedConstants`
   or in `ci.value?.getUsedConstants` separately, rather than merging both as
   `deps` does above.

This is the check a referee should run if §1.4's three-way split is the one
claim in this document they want mechanical evidence for, rather than a
reading of `Main/Corollaries.lean` and `Interface/Global.lean` by eye.
