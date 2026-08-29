# FORMALIZATION.md — Referee guide to the Lean formalisation

*Companion to "Second derivatives of $p$-adic $L$-functions and the
Shafarevich–Tate group of rank-two CM elliptic curves". This document records
what has been checked by the Lean 4 kernel against mathlib (pinned to release
`v4.33.1`), what is assumed and on whose authority, and how to reproduce every
check from a fresh clone of this repository.*

Last rebuilt 2026-08-29 (task R3doc), against commit `3b54e41` of the Lean tree.

> **State of the tree, 2026-08-29.** The Lean sources were resynchronised with
> version 2 of the paper on this date, in eight commits. Four changes matter to a
> reader of this document.
>
> 1. **The anchor corollaries are retired.** `cor_sha5` and `cor_sha13` — the
>    statements that Ш(E/ℚ)[5^∞] = 0 and Ш(E/ℚ)[13^∞] = 0 for the testbed curve —
>    together with the `Certificates` structure and the four digit-extraction
>    lemmas, were moved to `legacy/Anchors.lean`, which is outside Lake's build,
>    outside the audit, and outside the shipped repository — `legacy/` is
>    gitignored. Coates, Liang and Sujatha proved Ш(E₁/ℚ)[p^∞] = 0 at
>    every split p < 30,000 for the 2-isogenous partner E₁ : y² = x³ + 14x
>    (J. Algebra 322 (2009) 657–674; Milan J. Math. 78 (2010) 395–416, Thm. 1.3),
>    and odd-primary Ш is invariant under a 2-isogeny, so both corollaries are
>    subsumed. Paper v2 withdrew them and the displays `eq:match5` and
>    `eq:pred13` with them. §3 below records what the certificates were and why
>    the record is kept.
> 2. **`δ_E` became the family `δ_E(c)`, and is a definition rather than a
>    datum.** `EKPackage.deltaE` computes the resultant ∏_{t ∈ D_E} F_c(t) from
>    the divisor, the six sections and the coefficient vector. Three assumed
>    interface fields — `KatzData.deltaE_local`, `NonvanishingOnDE` and
>    `resultant_link` — were deleted; the content of `resultant_link` is now the
>    proved lemma `Resultant.forall_eq_one_of_prod_eq_one`.
> 3. **The paper's three lettered results are all formalised.** Theorem A is
>    `cor_horizontal`, Theorem B is `prop_consequence`, Theorem C is
>    `thm_reduction`. Theorem A had no Lean counterpart before 2026-08-29.
> 4. **The residual hypothesis `h5 : p = 5 → a_p = -2` is gone** from every
>    headline theorem: `ClassicalInputs.notAnomalous` renders the `S_an` clause of
>    `eq:Sexc`, which supplies non-anomality at every split p ∉ S.
>
> Version 2 of the paper carries a section headed *Formalisation*
> (`sec:formalisation`), which is at present a placeholder. Until it is written,
> this document is the only account of the formalisation. Statement numbering
> below refers to paper v2 throughout, by label rather than by printed number.

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

This paper was produced by AI agents. A referee's trust should therefore be
conditional and checkable rather than granted. The formalisation reduces the
check to two finite tasks.

1. **Read the tree of assumption *statements*** — plain mathematical
   propositions, each carrying a pinpoint literature citation — and judge whether
   they are true. The two conjectural items are not among them: they sit in
   hypothesis position, and §1.4 says where.
2. **Read the five headline Lean statements beside the corresponding statements
   in the paper**, and judge whether the Lean sentence says what the paper
   sentence says.

Once those two checks pass, the referee does not need to check the algebra, the
module theory, the case splits, or the bookkeeping in between: the Lean kernel
has verified that the conclusion follows from the stated assumptions. §1.7 says
what that does not cover.

The five headline declarations are

| Lean declaration | File | Paper |
|---|---|---|
| `cor_horizontal` | `FinShaRank2/Main/Horizontal.lean` | Theorem A = `cor:horizontal` |
| `prop_consequence` | `FinShaRank2/Main/Consequence.lean` | Theorem B = `prop:consequence` |
| `thm_reduction` | `FinShaRank2/Main/Reduction.lean` | Theorem C = `thm:reduction` |
| `thm_reduction_of_conjEK` | `FinShaRank2/Main/Reduction.lean` | Theorem C with input (i) supplied by `conj:EK` |
| `prop_dictionary` | `FinShaRank2/Main/Dictionary.lean` | `prop:dictionary` |

### 1.2 What "formally verified" means concretely

Every proof in this repository is checked by the Lean 4 kernel against mathlib,
pinned to release `v4.33.1`, mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474` (§6). Concretely:

* **There are no global `axiom` declarations in the project.** Every assumed
  mathematical input — every classical theorem, every numerical value, every open
  conjecture the argument depends on — is a field of an explicit Lean structure or
  a hypothesis of a theorem, and each headline theorem is a literal implication of
  the form
  ```
  theorem prop_consequence (H : ClassicalInputs) … (hc2 : IsPUnit …) : … := by …
  ```
  that is, "given data `H` satisfying these named properties, the conclusion
  holds".
* **`#print axioms` on every audited declaration shows `propext`,
  `Classical.choice`, `Quot.sound` and nothing else.** These three are mathlib's
  standing background axioms; they are not project-specific assumptions. Four
  audited declarations use fewer: `two_dvd_ap` uses none, and
  `neg_two_ne_one_zmod_five`, `eq_five_or_thirteen_le` and
  `Orbit.forall_eq_zero_of_exists_eq_zero` use only `propext` and `Quot.sound`.
* **The gate `scripts/audit.sh` is mechanical.** It (1) rebuilds the project,
  (2) greps every audited file for the substrings that mark an incomplete proof,
  against an allowlist file that is empty, and (3) elaborates a program that calls
  Lean's own `Lean.collectAxioms` on a fixed list of **82** declarations and fails
  the build if any of them uses anything outside the three-axiom whitelist. The
  output is quoted in full in §6.4.

### 1.3 Why an interface-first design

A from-scratch formalisation of this paper — one that constructs Selmer groups,
the Shafarevich–Tate group, Katz's two-variable p-adic L-functions and cyclotomic
p-adic heights as mathlib objects and proves Mazur's control theorem, Rubin's main
conjecture for CM fields and the Bannai–Kobayashi comparison theorem inside Lean —
is a multi-year formalisation project of its own. At the mathlib pin used here,
mathlib has none of that machinery. A referee can check this by source search over
`.lake/packages/mathlib/Mathlib/`: there is no definition of the Shafarevich–Tate
group, of the Weil–Châtelet group, or of the Selmer group of an elliptic curve.
(`Mathlib/RingTheory/DedekindDomain/SelmerGroup.lean` defines the `S`-Selmer group
`K(S,n)` of a fraction field, a different object; `Mathlib/RingTheory/Polynomial/Selmer.lean`
is about the polynomials `X^n − X − 1`.) Continuous-group cohomology has begun to
land — `Mathlib/RepresentationTheory/Homological/ContCohomology/` — and there is an
abstract-measure framework at `Mathlib/NumberTheory/Padics/Measure/`, but neither
reaches the objects this paper works with.

Formalising all of that would not be formalising *this paper*; it would be
formalising a large part of twentieth-century algebraic number theory that the
paper treats as known background, citable by theorem number. What is new — and
what a referee needs to scrutinise — is the paper's own chain of deductions.

The design therefore treats every classical theorem the paper cites (Rubin,
Mazur, Greenberg, Washington, Mazur–Tate–Teitelbaum, Bannai–Kobayashi, de Shalit,
Schneider, Perrin-Riou, Hasse, …) as an explicit assumption — a Lean structure
field with a docstring naming the theorem, the paper, and the page or theorem
number — and asks the kernel to certify only what the paper's own argument deduces
from those inputs. This makes the classical dependencies of the paper's claims more
explicit than the paper itself does (§1.4, §2).

### 1.4 The epistemic split

Every fact the formalisation consumes falls into one of two categories in the
imported tree, and the category is visible in the source by construction.

1. **`ClassicalInputs`** (`FinShaRank2/Interface/Global.lean`) — the aggregate
   structure of citable published theorems, each a field with a
   `SOURCE: … PAPER: … STATUS: …` docstring pinning it to a citation and to the
   paper label and proof step that uses it. Consumed as an ordinary hypothesis
   `H : ClassicalInputs` by every headline theorem. It has six fields: the
   excluded set `S` of `eq:Sexc`, the Eisenstein–Kronecker package `ek`, the
   rational factor `torsSqOverTam` with its defining equation, the per-prime
   bundle `dataAt`, and the non-anomality clause `notAnomalous`. `dataAt` supplies
   a `PrimeData` at every split `p ∉ S`, which aggregates five layers:
   `AnalyticData`, `SelmerData`, `IwasawaData`, `HeightData`, `KatzData`.
2. **Conjectural hypotheses** — exactly two: `hyp:sinnott` (the Lean structure
   `SinnottHyp`, `Interface/Katz.lean`) and `conj:EK` (the Lean proposition
   `ConjEK`, `Statements.lean`). Both occur only in hypothesis position, and only
   in `FinShaRank2/Main/Reduction.lean`. Neither is a field of any structure that
   can be instantiated. `SinnottHyp` occurs as a code term at its own declaration
   and at `Main/Reduction.lean` alone; `ConjEK` occurs at its own declaration and
   at `thm_reduction_of_conjEK` alone. Both are checkable by grep.

A third category, `Certificates H`, held this project's own machine-verified
numerics — the traces of Frobenius `a_5 = -2`, `a_13 = -6`, and the leading
p-adic digit expansions of `c₂(p)` at `p = 5, 13`. It was retired on 2026-08-29
together with the two anchor corollaries it served, because Coates–Liang–Sujatha
had already proved their conclusions. The declarations went to
`legacy/Anchors.lean`, which is gitignored and so is not in the repository a
referee clones; §3 is the record of what they were.
No declaration in the imported tree consumes a certificate. One numerical datum
survives in the imported tree — the seven 5-adic digits of `c₂(5)`, inside
`toySha_fails_c2_5_certificate` — and §3.6 says what its status is.

The consequence for a referee: **`prop_consequence`, `prop_dictionary` and
`cor_horizontal` use no conjectural item beyond `cor_horizontal`'s own hypothesis
`ConjWeak`, which is the hypothesis the paper's Theorem A also assumes.** This is
checked mechanically in §6.6, not by eye: a metaprogram walks the transitive
closure of constants each declaration's type and proof term depend on and reports
which of them are Katz- or Sinnott- or `δ_E`-flavoured. `thm_reduction` is the one
place the general conjectural reduction is rendered, and it is conditional exactly
as the paper presents it.

### 1.5 Translation and design conventions

These conventions govern how a paper statement becomes a Lean statement. They are
binding on the Lean sources, whose docstrings cite them; this section is their
public statement.

**Dual side.** The formalisation works with Pontryagin duals as finitely generated
`ℤ_[p]`- or `Λ`-modules, because that is where mathlib is strong; divisible
discrete modules and their coranks are not. The translations are:

| paper | Lean |
|---|---|
| `Ш(E/ℚ)[p^∞] = 0` | `Subsingleton (…).selmer.ShaDual` |
| `corank_{ℤ_p} Sel_{p^∞}(E/ℚ) = 2` | `Module.finrank ℤ_[p] (…).selmer.SelDual = 2` |
| `X := Sel_{p^∞}(E/ℚ_∞)^∨` | the `Λ`-module `IwasawaData.X` |
| `c̃₂(p) ∈ ℤ_p^×` | `IsPUnit (…).c2tilde` (the norm-one predicate on `ℚ_[p]`, `Defs.lean`) |
| `v_𝔭(x) ≥ 0` | `H.ek.v p x ≤ 1` |
| `v_𝔭(x) = 0`, i.e. `𝔭 ∤ x` | `H.ek.v p x = 1` |
| split prime | the binder `hsplit : p % 4 = 1` (throughout, `K = ℚ(i)`) |

The valuation direction reverses because mathlib's `Valuation` is multiplicative:
it is a monoid-with-zero homomorphism into a linearly ordered commutative monoid
with zero. `AddValuation` would preserve the paper's direction but has no product
lemma at this pin, and `δ_E(c)` is a product, so the multiplicative encoding is
used. The same dictionary is stated in the module docstrings of
`Interface/EK.lean`, `Interface/Katz.lean` and `Kernel/Resultant.lean`.

**Junk values, and the `MuZero`/`lambdaAn` pairing.** `c2tilde : ℚ_[p]` is a total
function: it divides by `(1 − α_p⁻¹)²`, which is zero at an anomalous prime, so at
an anomalous prime its value is junk. Every statement about `c2tilde` therefore
carries non-anomality, either as a hypothesis or — as now — through
`ClassicalInputs.notAnomalous`. Likewise `lambdaAn` is a `sInf` over the set of
indices with unit coefficient, which is junk (namely `0`) when that set is empty.
`lambdaAn` is meaningful only under `MuZero`, so the two are kept adjacent in every
statement that reports either. `thm_reduction` and `prop_consequence` both report
`MuZero` alongside `lambdaAn = 2`, where the paper's display names only
`λ_an(𝔭) = 2`.

**No conclusion vocabulary in assumptions.** No interface field may mention
`Subsingleton ShaDual`, `IsUnit (coeff 2 Lp)` or `finrank SelDual`. An assumption
that named the conclusion would make the headline theorems restatements. There is
one sanctioned exception and one sanctioned proxy-meaning assignment:

* `HeightData.spr_nondeg : IsPUnit c2norm ↔ (heightNondeg ∧ IsPUnit Reg_γ ∧ IsPUnit shaOrd)`
  is the exception. The cited theorem (Schneider; Perrin-Riou; packaged as
  Stein–Wuthrich Thm. 6.1) genuinely has that shape. It is phrased over
  `HeightData`'s own proxies `c2norm`, `shaOrd`, never over `IsUnit (coeff 2 Lp)`
  or `Subsingleton ShaDual` directly.
* `PrimeData.shaOrd_tie : IsPUnit height.shaOrd ↔ Subsingleton selmer.ShaDual`
  is the proxy-meaning assignment: it fixes what the proxy `shaOrd` means, rather
  than assuming a theorem about it. `shaOrd` is the order `#Ш(E/ℚ)[p^∞]`, a power
  of `p`, cast to `ℚ_[p]`; it is a unit iff it is `1` iff Ш`[p^∞] = 0`.

The tripwire for both is `ToySha` (§4.3): a world satisfying every interface field
in which the conclusion is false. It stays constructible — a non-unit `shaOrd`
paired with a nontrivial `ShaDual` satisfies the iff — and if a future edit
strengthened a field until it entailed the conclusion, `Toy/ShaTrivial.lean` would
stop compiling.

**Data equations rather than bare propositions.** Where possible a field is an
equation between data, so that downstream facts are derived rather than assumed.
The MTT interpolation formula is the field
`interp : ((constantCoeff Lp : ℤ_[p]) : ℚ_[p]) = (1 − α⁻¹)² * (modularSymbol0 : ℚ_[p])`,
with a separate field `msymb_zero : modularSymbol0 = 0`; then `c₀ = 0` is a theorem
(`c0_eq_zero`, half of `lem:c0c1`), not an assumption. Likewise
`torsSqOverTam_eq : torsSqOverTam = 1` keeps the normalisation value a checkable
datum rather than a constant baked into a definition.

**Docstring discipline.** Every interface field carries
```
SOURCE: [pinpoint citation]
PAPER:  [tex label + step]
STATUS: classical | consequence-form | data
```
`consequence-form` means the field states the consequence the paper's proof
extracts from the cited theorem, quoted in the docstring, rather than the cited
theorem in its published generality. `data` means an opaque datum whose truth is
not asserted.

**Paper labels, not printed numbers.** Docstrings and blueprint nodes key on tex
labels (`lem:c0c1`, `prop:consequence`, …), since printed numbers move between
drafts.

**No `native_decide`.** No audited file uses it; `decide` and `norm_num` only. The
axiom gate would catch a violation, since `native_decide` introduces
`Lean.ofReduceBool`.

*Residual problem.* The Lean docstrings cite `TASK_BOARD.md` in 37 places, and
`NOTES/MathlibAudit.md` in 5. `NOTES/` is part of this repository, so those
citations resolve. `TASK_BOARD.md` is not: it lives in the authors' private
working directory. Every *convention* those citations refer to is stated in this
section, and the epistemic split they refer to is §1.4; what remains unresolvable
is the internal task numbering (`T11`, `T24`, `R1β`, …), which records which agent
built what and carries no mathematical content.

### 1.6 Non-vacuity, proved rather than asserted

A structure with enough fields can be vacuous — self-contradictory, so that every
theorem proved from it is proved from a false premise. This formalisation does not
leave that to inspection. `FinShaRank2.ToyTrivial` is a complete, sorry-free
instance of `ClassicalInputs` in a simplified algebraic world, which proves the
assumption bundle is consistent. `FinShaRank2.ToySha` is a second complete
instance, satisfying every interface field as written, in which Ш is not trivial,
which proves the interface does not contain its own conclusion. Both are explained
for a non-Lean reader in §4; both are audited (§6).

### 1.7 What "formally verified" does *not* mean here

* It does **not** mean the cited classical theorems have themselves been formally
  verified. They are trusted the way a referee trusts a citation: by checking that
  the cited statement is real, correctly attributed and correctly used. Every
  citation is pinned to a paper, a theorem number and, where relevant, a page, so
  that check is quick (§2).
* It does **not** mean the paper's exposition, its background survey, its
  computational scan, or its outlook section have been checked in any formal
  sense. They were not claims requiring proof; §5 records this item by item.
* It does **not** mean the Lean statements are self-evidently the right rendering
  of the paper's mathematics. That is the second check of §1.1, and §2 exists to
  make it fast.
* It does **not** extend to `hyp:sinnott` and `conj:EK`, which remain as open as
  the paper says they are (§1.4).

---

## 2. Statement-by-statement table

Labels are those of paper v2. Every declaration name below was checked against
the Lean source on 2026-08-29; the file paths are given, and a referee can confirm
a name exists with `grep -rn '<name>' FinShaRank2/`. The **status** column takes
six values:

* **kernel-proved** — a Lean `theorem`, sorry-free, proved from the interface and
  kernel layers, and covered by `AxiomAudit.lean`.
* **formal def** — a Lean `def` rendering a paper definition or conjecture as a
  proposition. A `def` asserts nothing; what is asserted is whatever consumes it.
* **interface field + citation** — a field of an interface structure carrying a
  `SOURCE`/`PAPER`/`STATUS` docstring. Not proved in Lean: it *is* the assumption.
* **data field** — a field that is opaque data, not a proposition.
* **conjectural hypothesis** — occurs only in hypothesis position, only in
  `Main/Reduction.lean`.
* **no counterpart** — not formalised. §5 says why, item by item.

| Paper label | Lean declaration(s) | File | Status | Notes |
|---|---|---|---|---|
| `def:horizontal` | `HorizontalControl` | `Statements.lean` | formal def | A predicate on a set of primes `P` and a per-prime triviality predicate: the set of `p ∈ P` at which the predicate fails is finite. That is "for all but finitely many `p ∈ 𝒫`" verbatim. Deliberately standalone, as in the paper, where the definition precedes all data. |
| `lem:c0c1` | `c0_eq_zero`, `c1_eq_zero` | `Main/Lemma41.lean` | **kernel-proved** | Stated over a bare `AnalyticData p hsplit`, not over `ClassicalInputs`; `prop_consequence` applies them downstream. `c₀ = 0` follows from `interp` together with `msymb_zero`; `c₁ = 0` follows from `funct_eq` through the kernel lemma `coeff_one_Lp_eq_zero`. |
| `def:c2tilde` | `c2tilde`; `PrimeData.c2tilde` | `Defs.lean`; `Statements.lean` | formal def | `c2tilde c₂ α⁻¹ t = c₂ · (1 − α⁻¹)⁻² · t`, a total function with a junk value at anomalous primes (§1.5). `PrimeData.c2tilde` instantiates it at a bundle's own analytic data. The factor `(#tors)²/∏c_v` is the field `ClassicalInputs.torsSqOverTam`, pinned `= 1` by `torsSqOverTam_eq` — a checkable datum rather than a constant baked in. |
| `prop:normalisation` | `isPUnit_c2tilde_iff`; `isPUnit_c2tilde_iff_of_split`; `ClassicalInputs.isPUnit_one_sub_alphaInv` | `Kernel/Normalization.lean`; `Main/Consequence.lean` | **kernel-proved** | `IsPUnit c̃₂(p) ↔ IsUnit (coeff 2 Lp)`, given that `1 − α_p⁻¹` is a `p`-adic unit and that the rational factor is `1`. `ClassicalInputs.isPUnit_one_sub_alphaInv` supplies the first hypothesis from `notAnomalous`, so no residual `p = 5` hypothesis is carried. `isPUnit_c2tilde_iff_of_split` derives the same conclusion from the raw `AnalyticData` fields plus `p = 5 → a_p = -2`; it is no longer on the route the headline theorems take and is kept because it bounds what `notAnomalous` assumes beyond the proved `lem:noanomalous`(2). |
| `rmk:integrality` | — | — | **no counterpart** (automatic) | Integrality of `c₂(p)` needs no field: `AnalyticData.Lp : Λ p` with `Λ p := PowerSeries ℤ_[p]` (`Defs.lean`), so every coefficient is an element of `ℤ_[p]` by construction. The remark's own content — that integrality follows from integrality of modular symbols, citing Greenberg–Vatsal Prop. 3.7 and Stein–Wuthrich Prop. 3.7, with reducibility of `ρ̄_{E,p}` excluded for all but finitely many `p` by Mazur — is not rendered, and nothing in the Lean tree needs it. See §5.12. |
| `conj:strong` | `ConjStrong` | `Statements.lean` | formal def | An existential, as the conjecture is: `∃ (δ : H.ek.L) (Sig : Finset ℕ), δ ≠ 0 ∧ ∀ split p ∉ H.S ∪ Sig with H.ek.v p δ = 1, IsPUnit (…).c2tilde`. The paper's `Σ` is `H.S ∪ Sig`. `thm_reduction` witnesses it with `δ := H.ek.deltaE c` and `Sig := H.ek.supp c`. The integrality clause of `conj:strong` is not part of the predicate; by `rmk:integrality` it is classical and, in the paper's words, not the substance of the conjecture. Until 2026-08-29 this predicate pinned `δ` and `Σ` to data carried by `ClassicalInputs`, which discharged the existential by fiat. |
| `conj:weak` | `ConjWeak` | `Statements.lean` | formal def | `∃ T : Finset ℕ, ∀ split p ∉ H.S with p ∉ T, IsPUnit (…).c2tilde`. This is the `∃ finite T, ∀ p ∉ T` form of "for all but finitely many split primes", which is the form `cor_horizontal` consumes. |
| `conj:EK` | `ConjEK` | `Statements.lean` | formal def (conjectural) | `∀ c : Fin 6 → H.ek.K, c ≠ 0 → H.ek.deltaE c ≠ 0`. Occurs in hypothesis position of `thm_reduction_of_conjEK` and nowhere else. The hypothesis `#Cl_𝔣(K) ≥ 6` is **not** rendered; dropping it widens what `ConjEK` asserts, so `ConjEK H` renders `conj:EK` only for those `H` whose package meets the paper's hypothesis. See §5.6. |
| `lem:comparison` | `KatzData.comparison` | `Interface/Katz.lean` | **interface field + citation** | SOURCE: Bannai–Kobayashi, Duke Math. J. 153 (2010), Cor. 3.12, with de Shalit, *Iwasawa theory of elliptic curves with CM*, Perspectives in Math. 3, II §4, for the local terms. Consequence-form: the constant `c_p` and the series `u(T)` are taken already as units in `Wˣ` and `(W⟦T⟧)ˣ`, which folds in the lemma's own conclusion `v_p(c_p) = 0` for `p ∉ S_cmp`, `S_cmp` being one of the five membership reasons of `eq:Sexc`. Flagged in-file as consequence-form rather than as a strengthening. |
| `prop:consequence` (= **Theorem B**) | `prop_consequence` | `Main/Consequence.lean` | **kernel-proved** | Hypotheses: `H : ClassicalInputs`, `hsplit : p % 4 = 1`, `hpS : p ∉ H.S`, `hc2 : IsPUnit (…).c2tilde`. Conclusions in the order `MuZero`, `lambdaAn = 2`, `finrank ℤ_[p] SelDual = 2`, `Subsingleton ShaDual` — the paper's (1), (2), (3) with the μ/λ pair split and kept adjacent (§1.5). No conjectural hypothesis appears. "Non-anomalous" is not assumed: it is `H.notAnomalous` at `p`, a clause of the definition of `S`. |
| `cor:horizontal` (= **Theorem A**) | `cor_horizontal` | `Main/Horizontal.lean` | **kernel-proved** (conditional on `conj:weak`) | `HorizontalControl {p | p.Prime ∧ p % 4 = 1} (fun p ↦ … Subsingleton (…).selmer.ShaDual)` from `hweak : ConjWeak H`. Three differences from the paper, all recorded in the file: (a) the per-prime predicate supplied is `Ш[p^∞] = 0`, where `def:horizontal` asks for `Ш[p] = 0`, so what is proved implies what is stated; (b) the paper's hypothesis "finitely many anomalous split primes", and the step of its proof that uses it to make `S_E` finite, have no counterpart — `ClassicalInputs.S : Finset ℕ` is finite by construction and `notAnomalous` puts every anomalous split prime inside `S`, which is a simplification the encoding makes rather than something proved; (c) the curve-level hypotheses are carried by `H`. |
| `prop:dictionary` | `prop_dictionary` | `Main/Dictionary.lean` | **kernel-proved** | `IsPUnit (…).c2tilde ↔ (heightNondeg ∧ IsPUnit Reg_γ ∧ Subsingleton ShaDual)`. Carries no non-anomality hypothesis, where the paper states the dictionary at non-anomalous `p`: against the frozen interface both directions come from `c2norm_tie`, `spr_nondeg` and `shaOrd_tie`, and no anomality-sensitive step is needed. That is a strengthening, not a weakening. The proof is three rewrites. |
| `lem:noanomalous` | part (2): `anomalous_iff_five`, `noAnomalous`, `ap_ne_one_of_hasse`, `isPUnit_one_sub_alphaInv_iff`, `two_dvd_ap`, `eq_five_or_thirteen_le`; part (1): — | `Kernel/Anomalous.lean` | part (2) **kernel-proved**; part (1) **no counterpart** | Part (2) is proved in the strengthened form the paper states: for `p ≡ 1 (mod 4)` and `a` even with `a² ≤ 4p`, `a ≡ 1 (mod p)` iff `p = 5` and `a = -4`. The conclusion is delivered as `IsPUnit (1 − α_p⁻¹)` (norm one), not the weaker bare `IsUnit` in `ℚ_[p]`. Part (1) — `p ≢ 1 (mod 4)` implies `p ∣ a_p` — reduces to Deuring's reduction criterion, which mathlib does not have; see §5.5. |
| `eq:Sexc` | `ClassicalInputs.S`, `ClassicalInputs.notAnomalous` | `Interface/Global.lean` | data field + **interface field** | `S : Finset ℕ` is opaque data; its five membership reasons (`S_bad`, `S_an`, `S_red`, `S_cmp`, `S_cl`) are recorded in the field's docstring. Only `S_an` has formal content downstream, and it is carried by `notAnomalous : ∀ split p ∉ S, ¬ ((a_p : ZMod p) = 1)`. Adding this field removed the residual hypothesis `h5 : p = 5 → a_p = -2` from every headline theorem. What it assumes beyond the proved `anomalous_iff_five` is a single numerical value, `a₅ ≠ -4`. |
| `eq:padicbsd` | `HeightData.spr_padicBSD`, `HeightData.spr_nondeg` | `Interface/Heights.lean` | **interface field + citation** | SOURCE: Schneider, Invent. Math. 79 (1985), Thms. 2, 2′; Perrin-Riou, Invent. Math. 109 (1992), §§3.4.2–3.4.3; packaged as Stein–Wuthrich, Math. Comp. 82 (2013), Thm. 6.1. `spr_nondeg` is the one sanctioned exception to the no-conclusion-vocabulary rule (§1.5): the cited theorem genuinely has iff shape. It is phrased over `HeightData`'s own proxies, which is what keeps `ToySha` constructible. |
| `prop:jetformula` | `KatzData.grading_congr` (docstring only) | `Interface/Katz.lean` | **interface field** (partial) | The field records only the resulting algebraic congruence `∃ κ₀ : Wˣ, p²·(κ₀·coeff 2 LKatz − m2core) ∈ (p³)`. The Eisenstein–Kronecker second-moment bookkeeping that derives it is not carried into Lean, and the field's docstring says so. See §5.2. |
| `prop:grading` | part (2): `isUnit_iff_residue_ne_zero_of_grading_congr`; part (1): `KatzData.grading_congr`, `KatzData.m2core`, `KatzData.criterionClass` | `Kernel/GradingValuation.lean`; `Interface/Katz.lean` | part (2) **kernel-proved**; part (1) **interface field** | Part (2) is a ring-generic lemma in a local domain: unit iff nonzero residue, given the congruence. Part (1), the congruence itself, is assumed as data. `m2core : W` is the `p^{-2}` lift of the grade-two moment sum; `criterionClass` is a **def**, not a field: `IsLocalRing.residue K.W K.m2core`. |
| `lem:decoupling` | `Decoupling.coeff_two_mul`, `coeff_two_mul_of_snd_low`, `coeff_two_mul_of_fst_low`, `coeff_smul_eq_mul`, `coeff_eq_zero_of_map_eq_zero`, `isUnit_coeff_two_map_iff`, `isUnit_coeff_two_of_comparison` | `Kernel/Decoupling.lean` | **kernel-proved** | Ring-generic — an arbitrary commutative ring, no project data: the three-term coefficient-of-product formula and its unit-transfer corollary along an injective local ring homomorphism. |
| `lem:orbit` | `Orbit.prod_mem_range_algebraMap` (part 1), `Orbit.forall_eq_zero_of_exists_eq_zero` (part 2) | `Kernel/Orbit.lean` | **kernel-proved** | Both parts are proved in full generality, for a Galois extension `L/K` and a finite set `D` with a `Gal(L/K)`-action. Part (2) uses neither finiteness of `D` nor the Galois hypothesis. What is *assumed* is the equivariance `F(σt) = σ(F(t))` for the package, which the paper also assumes rather than proves; §5.7. `thm_reduction` does not use `lem:orbit`. |
| `eq:DEdef` | `EKPackage.ι`, `EKPackage.D`, `EKPackage.D_nonempty` | `Interface/EK.lean` | data fields | The divisor `D_E = Cl_𝔣(K)` as an abstract finite set of points with a nonemptiness proof. The class-group structure and the simply transitive Galois action are not rendered; the consequences are §5.6 and §5.7. |
| `eq:jetpackage` | `EKPackage.r`; `jetIndex`, `jetIndex_image`, `jetIndex_injective` | `Interface/EK.lean` | data field + **kernel-proved** | `r : Fin 6 → ι → L` is the package `𝓡_E` as data. `jetIndex` records which of the six slots is which pair `(a,b)`; `jetIndex_image` proves the enumeration is exactly the index set `{(a,b) : b ≥ 1, a + b ≤ 3}` and `jetIndex_injective` that the six slots are distinct. Both by `decide`. |
| `def:deltaE` | `EKPackage.Fc`, `EKPackage.deltaE`, `deltaE_def`, `Fc_def`, `deltaE_ne_zero_iff`, `deltaE_singleton` | `Interface/EK.lean` | formal def + **kernel-proved** | `δ_E(c) := ∏_{t ∈ D_E} F_c(t)` with `F_c(t) = ∑ᵢ cᵢ • rᵢ(t)`, a definition rather than a datum. `deltaE_ne_zero_iff` proves the sentence following the paper's definition — `δ_E(c) ≠ 0` exactly when `F_c` vanishes nowhere on `D_E` — by unfolding. `δ_E(c)` lands in `P.L`, the paper's `Q̄`, and is **not** proved rational: that is `lem:orbit`(1), which needs the equivariance input (§5.7), and `thm_reduction` does not use it. The structure this replaced carried `δ_E` as an opaque rational `ClassicalInputs.deltaE : ℚ` welded to a `KatzData` field `deltaE_local`, together with an assumed implication `resultant_link`; all three are gone. |
| `hyp:sinnott` | `SinnottHyp` (fields `integral`, `presentation`, `nonvanishing`) | `Interface/Katz.lean` | **conjectural hypothesis** | A `Prop`-valued structure over a `KatzData`, an `EKPackage` and a coefficient vector. `integral` is the `𝔭`-integrality clause of (i), `∀ t ∈ D_E, v_𝔭(F_c(t)) ≤ 1`; `presentation` is the presentation clause of (i); `nonvanishing` is (ii). It is a field of no instantiable structure. Until 2026-08-29 the integrality clause was baked into the `KatzData` field `resultant_link`, an unproved implication carried on the instantiable assumption surface under `STATUS: classical`; it is now in hypothesis position, where the paper puts it, and the step it fed is the proved `Resultant.forall_eq_one_of_prod_eq_one`. |
| `thm:reduction` (= **Theorem C**) | `thm_reduction`; `thm_reduction_of_conjEK`; `Resultant.forall_eq_one_of_prod_eq_one`, `Resultant.prod_ne_zero_of_prod_eq_one` | `Main/Reduction.lean`; `Kernel/Resultant.lean` | **kernel-proved** (conditional) | The only declarations that mention conjectural input, and they do so in hypothesis position: `hEK : H.ek.deltaE c ≠ 0` and `hsin`, the `SinnottHyp` quantified over split `p ∉ H.S ∪ supp(c)`. `thm_reduction_of_conjEK` takes `ConjEK H` and a nonzero `c` in place of `hEK`. The conclusion is the per-prime statement conjoined with `ConjStrong H`, which `thm_reduction` now *proves* rather than receiving from the interface. The paper's condition "if `S_E` is finite" disappears: `H.S : Finset ℕ` is finite by construction. The deduction chain is `hsin.integral` + `𝔭 ∤ δ_E(c)` → `Resultant.forall_eq_one_of_prod_eq_one` → `hsin.nonvanishing` → `hsin.presentation` → grading-valuation kernel → `comparison` + decoupling → `prop:normalisation` → `prop_consequence`. |
| `thm:padicbsdunits` | — | — | **no counterpart** | New in paper v2. It states that `v_𝔭(c̃₂(p)) = v_p(Reg_γ) + v_p(#Ш(E/ℚ)[p^∞])` under finiteness of Ш and nondegeneracy of the height pairing, combining Rubin's main conjecture with Schneider's leading-term theorem. Nothing in the Lean tree renders it. Its Lean-side content is absorbed by the interface fields `HeightData.spr_padicBSD` and `spr_nondeg`, which are the packaged Schneider/Perrin-Riou consequence-forms, and by `IwasawaData.rubin_structure`. |
| `lem:msdmtt` | — | — | **no counterpart** | New in paper v2. It identifies the ideal generated by the Mazur–Swinnerton-Dyer `p`-adic `L`-series with `(L_p(E,T))`, which is what lets Rubin's theorem be applied to the MTT normalisation. In the Lean encoding the identification is not needed and is not stated: `IwasawaData.rubin_structure` is the fused consequence-form `car_Λ(X) = (∏ᵢ fᵢ) = (L_p)`, already expressed in terms of the `AnalyticData` field `Lp`, so the normalisation comparison is inside the citation rather than in front of it. |

Three points belong with the table.

* **The paper's Theorems A, B, C are stated for a curve; the Lean statements are
  conditional on `H : ClassicalInputs`.** That is the design of §1.3, not a
  weakening. The paper's own proofs depend on Rubin's main conjecture, Mazur's
  control theorem, the MTT interpolation formula and half a dozen further
  classical results; the Lean rendering makes those dependencies explicit typed
  hypotheses, so a referee sees them in one place instead of reconstructing them
  from a citation trail.
* **`prop_consequence` and `prop_dictionary` each drop a hypothesis the paper
  states.** `prop_consequence` does not assume non-anomality, which
  `ClassicalInputs.notAnomalous` supplies; `prop_dictionary` does not assume it
  either, because its proof does not need it. Both deviations run in the safe
  direction — fewer hypotheses, the same conclusions. `cor_horizontal` drops the
  paper's hypothesis on anomalous primes for the reason given in its row, which is
  an encoding simplification rather than a strengthening, and the row says so.
* **Six interface fields are carried but consumed by no proof in the imported
  tree.** They are `AnalyticData.ap_from_CM`, `AnalyticData.hasse`,
  `HeightData.reg_integral`, `HeightData.sha_integral`, `HeightData.spr_padicBSD`
  and `EKPackage.D_nonempty`. A referee auditing the interface field by field
  should read these six as accounted for rather than overlooked; each has its own
  `SOURCE`/`PAPER`/`STATUS` docstring in its home file. The
  check is `grep -rn '\.<field>' FinShaRank2/` with `Interface/`, `Toy/` and
  `Scratch/` excluded: for these six the result is empty apart from one docstring
  mention of `reg_integral` in `Main/Dictionary.lean`. `hasse` and `ap_from_CM`
  are the Hasse bound and CM evenness of `a_p`; the kernel lemmas `noAnomalous`,
  `anomalous_iff_five` and `isPUnit_c2tilde_iff_of_split` prove statements of
  exactly their shape and are audited, but the route the headline theorems now
  take runs through `ClassicalInputs.notAnomalous` instead, so the fields
  themselves are not projected. `spr_padicBSD` is the norm identity
  `‖c2norm‖ = ‖Reg_γ‖·‖shaOrd‖`, and `reg_integral`, `sha_integral` its two
  integrality companions; `prop_dictionary` reaches its conclusion through the
  tie-equations and `spr_nondeg` and needs none of the three. `D_nonempty` records
  that `D_E` is nonempty, which no step uses. An unused field can only make
  `ClassicalInputs` harder to satisfy — one more obligation `ToyTrivial` and
  `ToySha` had to discharge — never easier, and it cannot contribute to a
  conclusion it plays no part in deriving. Two further fields,
  `AnalyticData.modularSymbol0` and `HeightData.shaOrd`, are not projected either,
  but their content is consumed through the types of fields that are: `interp` and
  `msymb_zero` for the first, `shaOrd_tie` for the second.

---

## 3. Certificate provenance

### 3.1 What the certificates were

`Certificates H` packaged six facts about the testbed curve `E : y² = x³ − 56x` at
the two anchor primes `p = 5, 13`: this project's own numerical computations, kept
in a structure separate from `ClassicalInputs` so that a referee could tell at a
glance which facts were citable published mathematics and which were this project's
arithmetic. Two theorems consumed them, `cor_sha5` and `cor_sha13`, which concluded
Ш(E/ℚ)[5^∞] = 0 and Ш(E/ℚ)[13^∞] = 0.

**Both corollaries and the `Certificates` structure were retired on 2026-08-29**
into `legacy/Anchors.lean`. §3.5 gives the reason. That file is outside Lake's
build, outside the audit, and — since `legacy/` is ignored by the repository's
`.gitignore` — outside the shipped repository: a referee cloning this repository
will not have it. **This section is therefore the whole of the record.** The
computations were correct and their provenance is worth keeping, whatever the
status of the conclusions they were used to reach.

The computer algebra that produced the numbers — the PARI/GP and SageMath scripts
and the output of every run — is in `../code`; see `../code/README.md`. What
follows records the certificate values and their provenance inline, so that a
referee holding only this repository has the record.

### 3.2 The six fields, verbatim

Reproduced from `legacy/Anchors.lean`, with the `Fact` and membership arguments
elided:

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

**Frobenius traces (`a5`, `a13`).** Verified against PARI/GP
(`ellinit([0,0,0,-56,0])`):
```
$ echo 'ellap(ellinit([0,0,0,-56,0]),5)'  | gp -q
-2
$ echo 'ellap(ellinit([0,0,0,-56,0]),13)' | gp -q
-6
```
So `a_5 = -2` and `a_13 = -6`. Both are even, as CM evenness of `a_p` requires.
`a_5` closed the one residual case `lem:noanomalous` could not close
unconditionally; that role is now played by `ClassicalInputs.notAnomalous`, and
what it assumes beyond the proved `anomalous_iff_five` is the single value
`a₅ ≠ -4`.

**Digit congruences (`c2_5`, `c2_13`).** Each states that the second Taylor
coefficient `c₂(p) = coeff 2 Lp ∈ ℤ_[p]` reduces mod `p^k` to an explicit digit
sum whose leading digit is `1` — so the value is not divisible by `p`, so
`coeff 2 Lp` is a `p`-adic unit:

* `c₂(5) ≡ 1 + 4·5 + 3·5² + 5³ + 5⁵ + 5⁶ (mod 5⁷)`, seven 5-adic digits;
* `c₂(13) ≡ 1 + 11·13 + 13² + 13³ + 10·13⁴ (mod 13⁵)`, five 13-adic digits.

The shape was deliberately a congruence — an equality of `PadicInt.toZModPow k`
images in `ZMod (p^k)` — rather than a bare `IsUnit` assertion, so that a referee
could check the digit string against an independent computation instead of
trusting an opaque Boolean. The extraction from congruence to unit
(`isUnit_of_toZModPow_cert`, specialised to `isUnit_of_cert_five` and
`isUnit_of_cert_thirteen`; all three now in `legacy/Anchors.lean`) reduced the
digit sum further along `ZMod.castHom → ZMod p`, observed that the leading digit
`1` survives, and concluded via `PadicInt.isUnit_iff`.

In paper v1 these two displays were labelled `eq:match5` and `eq:pred13`. Neither
label exists in paper v2.

### 3.3 Two independent implementations

`c2_5` was produced by two independent computational routes that agree
digit-for-digit: a PARI computation of the p-adic sigma-height side, and a Sage
computation of modular symbols on the L-function side. A coding error in either
implementation would have had to produce the same wrong seven-digit expansion in
both to survive the check.

### 3.4 The p = 13 certificate: a prediction, not a fit

* **2026-06-12** — the full 13-adic digit expansion `c2_13` was pre-registered:
  computed and recorded from the height side, before any modular-symbol
  computation of `L_13(E,T)` existed.
* **2026-07-02** — an independent modular-symbol computation of `L_13(E,T)` at
  level `12544` was carried out, and every computed digit agreed with the
  pre-registered prediction.

The `p = 13` digits were therefore a prediction confirmed after the fact by an
independent method, not a coincidence found by searching until something matched.
That remains true of the computation whether or not the corollary it served is
subsumed, which is why the record is kept here rather than deleted with the
declarations.

### 3.5 Why the corollaries and the certificate structure were retired

Coates, Liang and Sujatha proved Ш(E₁/ℚ)[p^∞] = 0 at every split prime
p < 30,000 for the curve E₁ : y² = x³ + 14x (J. Algebra 322 (2009) 657–674; Milan
J. Math. 78 (2010) 395–416, Thm. 1.3). Paper v2 states this as `thm:cls` and
credits Wuthrich alongside them; the transfer across the isogeny is its
`lem:isogeny` and the resulting statement about the testbed curve is
`cor:shavanishing`. E₁ is 2-isogenous to the testbed curve
E : y² = x³ − 56x, and the odd-primary part of Ш is invariant under a 2-isogeny,
so their result gives Ш(E/ℚ)[5^∞] = 0 and Ш(E/ℚ)[13^∞] = 0 — the conclusions of
`cor_sha5` and `cor_sha13` — fifteen years earlier and over a far larger range of
primes.

Paper v2 therefore withdrew both corollaries and the displays `eq:match5` and
`eq:pred13`. The labels no longer exist in the manuscript, so the formalisation
must not present the corollaries as its own results either. The declarations were
moved rather than deleted: `legacy/Anchors.lean` holds the `Certificates`
structure, the two `Fact` instances, the four digit-extraction lemmas
(`isUnit_of_toZModPow_cert` and its primed variant, `isUnit_of_cert_five`,
`isUnit_of_cert_thirteen`), the two corollaries, and the toy-model fact
`isEmpty_certificates_toySha`. That file is unmaintained and unshipped: `legacy/`
is in the repository's `.gitignore`, so it exists in the authors' working tree
only. It was written against mathlib `v4.32.0` and the bump to `v4.33.1` may have
broken it; it can be checked with `lake env lean legacy/Anchors.lean`, but nothing
in the audit does so, and a referee should not expect to find it.

What stayed in the imported tree: `Kernel/Normalization.lean` keeps
`isPUnit_c2tilde_iff`, `eq_five_or_thirteen_le`, `isPUnit_one_sub_alphaInv_of_split`
and `isPUnit_c2tilde_iff_of_split`, which feed surviving results;
`Toy/ShaTrivial.lean` keeps the anti-vacuity argument, now carried by the
certificate-free `toySha_fails_c2_5_certificate` (§4.3).

### 3.6 The one surviving use of the `c₂(5)` digits

`toySha_fails_c2_5_certificate` (`Toy/ShaTrivial.lean`) is now the only place in
the imported tree where the seven 5-adic digits of `c₂(5)` appear. It states that
the seven-digit congruence fails for the anti-vacuity world, where
`coeff 2 (shaLp 5) = 5`, and its role is to identify the datum that excludes that
world (§4.3).

**A referee will find no cross-reference for those digits in the paper.** The
display went out of paper v2 with `eq:match5`. The digits are this project's own
computation, and the lemma's docstring says so explicitly (`PAPER: none`). This
section is their citable home: the value, the two independent implementations that
produced it (§3.3), and the date.

*Recommendation.* Keep the digits in the lemma, and treat §3.2–§3.3 of this
document as the reference for them. The alternative — restating the lemma against
the weaker datum `¬ IsUnit (coeff 2 (shaLp 5))` — would compile and would still
witness that `ToySha` fails a numerical condition, but it would lose the point the
lemma exists to make: that it is *exactly* the computed `c₂` digit string, and not
some vaguer weakness of the interface, that rules this world out. If the paper's
section `sec:formalisation` is written, the display belongs there, and the lemma's
docstring should then cite it instead of this document.

---

## 4. The ToyTrivial / ToySha argument

### 4.1 The question this section answers

`ClassicalInputs` is large: six top-level fields, one of which supplies at every
split prime a five-layer bundle with about forty fields between the layers. Two
questions should be asked of any such assumption bundle before theorems proved
from it are trusted.

* **Consistency.** Could the bundle be self-contradictory? If so, every theorem
  proved from it is proved from a false premise and worth nothing.
* **Question-begging.** Does the bundle already contain its own conclusion? If
  some field forces Ш = 0 as a side effect of looking innocuous, then the
  conclusions are definitions rather than theorems.

Both are answered by construction: two complete, kernel-checked example worlds.

### 4.2 `ToyTrivial` — the assumption bundle is consistent

`FinShaRank2.ToyTrivial : ClassicalInputs` (`Toy/Trivial.lean`, built from
`Toy/Analytic.lean`, `Toy/EK.lean`, `Toy/Iwasawa.lean`, `Toy/Heights.lean`,
`Toy/Katz.lean`) is a complete instance of `ClassicalInputs` in a simplified
algebraic world. It is not the testbed curve and no claim is made that it models
one. Its job is to witness that the assumption bundle can be satisfied at all,
with every field proved:

| Interface datum | Toy value |
|---|---|
| excluded set `S` | `∅` (every split prime carries data) |
| `(#tors)²/∏c_v` | `1` |
| `ek` (`D_E`, `𝓡_E`, `v_𝔭`, `supp`) | one point over `ℚ`, all six sections constantly `1`, trivial valuation, empty support |
| p-adic L-function `L_p` | `X²` |
| `a_p`, unit root `α` | `a_p = 2a` from a two-squares decomposition `p = a² + b²`; `α` the Hensel root |
| Iwasawa module `X` | `(Λ/(X))²` |
| Selmer and Ш duals | `SelDual = ℤ_[p]²`, `ShaDual = PUnit` |
| regulator, Ш-order proxy, height nondegeneracy | `1`, `1`, `True` |
| Katz coefficient ring, `L^{Katz}`, grade-two core | `ℤ_[p]`, `X²`, `1` |

Three points from the construction are worth relaying rather than taking on
faith. `no_finite_submodule` was not free: it needed `ℤ_[p]`-torsion-freeness of
`(Λ/(X))²`, proved rather than assumed away. The height-side proxy `c2norm` is
*forced* by the mandatory tie-equation `c2norm_tie` to equal `(1 − α⁻¹)⁻²`; it
cannot be chosen to make the height fields trivially satisfiable, and the
construction had to show the forced value still satisfies `spr_padicBSD` and
`spr_nondeg`. And `notAnomalous` is discharged from the toy arithmetic itself
(`Toy.Setup.ap_ne_one`): `a_p = 2a` with `1 ≤ a` and `2a < p`, so `2a ≢ 1 (mod p)`.

`ToyTrivial` is declared as `noncomputable def ToyTrivial : ClassicalInputs where
…`, so its type is checked at the definition and every field obligation is
discharged there; the audit reports
`ToyTrivial uses only [propext, Classical.choice, Quot.sound]`. The assumption
surface is consistent.

### 4.3 `ToySha` — the assumption bundle does not beg the question

`FinShaRank2.ToySha : ClassicalInputs` (`Toy/ShaTrivial.lean`, layers in
`Toy/ShaAnalytic.lean`, `Toy/ShaIwasawa.lean`, `Toy/ShaHeights.lean`,
`Toy/ShaKatz.lean`, sharing `Toy/EK.lean`) is a second complete instance — every
field satisfied as written, none weakened — built so that the conclusion fails:

| Interface datum | `ToySha` value | `ToyTrivial` value |
|---|---|---|
| p-adic L-function `L_p` | `C p · X²`, so `coeff 2 L_p = p`, a non-unit | `X²`, `coeff 2 = 1`, a unit |
| Iwasawa module `X` | `Λ/(X) × Λ/(X) × Λ/(C p)` | `(Λ/(X))²` |
| Selmer and Ш duals | `ℤ_[p]² × ℤ_[p]/(p)`, `ℤ_[p]/(p)` (nontrivial) | `ℤ_[p]²`, `PUnit` |
| Ш-order proxy `shaOrd` | `p`, a non-unit | `1`, a unit |
| grade-two core `m2core` | `p` | `1` |

Everything else — `S = ∅`, the Eisenstein–Kronecker package, the regulator,
`heightNondeg`, and every citation-grade field — is satisfied as in `ToyTrivial`.
The values above are forced rather than chosen, and the file says how: `shaOrd_tie`
forces `shaOrd` to be a non-unit once `ShaDual` is nontrivial; `spr_padicBSD` and
`c2norm_tie` then force `coeff 2 L_p` to be a non-unit at the toy prime; and
`rubin_structure` forces the elementary divisors of `X` to multiply to `L_p`,
which with `π_surj` (rank two) and a nontrivial `ShaDual` pins the multiset to
`(X, X, C p)`. The anti-vacuity witness is therefore close to the only way to
falsify the conclusion while honouring every interface field.

Three declarations make the point precise.

* **`interface_does_not_force_sha_trivial`** — there is no proof, from
  `H : ClassicalInputs` and splitness alone, that `Subsingleton ShaDual` at every
  split prime. Witnessed by `ToySha` at `p = 5`.
* **`toySha_conclusions_fail`** — stronger: three of the conclusions fail at
  *every* split prime of the `ToySha` world at once. Ш is not trivial, `MuZero`
  fails, and `lambdaAn ≠ 2`. This is a systematic failure, not one cherry-picked
  prime.
* **`toySha_fails_c2_5_certificate`** — the numerical datum that excludes the
  world. Its proof reduces `coeff 2 (shaLp 5) = 5` mod `5⁷` and closes by `decide`
  against the seven computed 5-adic digits of `c₂(5)`, whose leading digit is `1`
  where the toy value's is `0`. So it is not that the interface is too weak in some
  vague sense to pin down Ш; it is the computed `c₂` digit string that rules this
  world out, and that string genuinely fails for it.

The third of these replaced `isEmpty_certificates_toySha`, which proved
`IsEmpty (Certificates ToySha)` and went to `legacy/Anchors.lean` with the
structure it mentions. The replacement carries the same content without the
retired structure. The provenance of the digits it uses, and their status now that
paper v2 no longer displays them, are §3.2–§3.3 and §3.6.

### 4.4 Why a referee should care about both halves

`ToyTrivial` excludes "this structure is quietly unsatisfiable, so the headline
theorems are vacuously true". It has a model.

`ToySha` excludes the opposite concern, which is the more common failure mode of
an interface-first formalisation: "some field was worded just strongly enough to
make the proof go through, and assumes the conclusion". There is a model of the
interface in which the conclusion is false, so the interface is logically weaker
than its conclusion, as an assumption bundle should be.

Both instances are in `AxiomAudit.auditedDecls` layer by layer — `toyAnalytic`,
`toySelmer`, `toyIwasawa`, `toyHeight`, `toyKatz`, `toyEK`, `Setup.ap_ne_one`,
`toyPrimeData`, `ToyTrivial`; and `shaAnalytic`, `shaSelmer`, `shaIwasawa`,
`shaHeight`, `shaKatz`, `shaPrimeData`, `ToySha` — so a regression in either
pinpoints its layer (§6.4).

---

## 5. Known descopes and why they are harmless

### 5.1 How to read this section

§2 tags some rows **no counterpart**. This section says, for each such item, what
it is, why an interface-first formalisation does not attempt it, and which
theorems are affected by its absence and which are not.

The governing fact, stated once here rather than repeated: **`KatzData`,
`SinnottHyp`, `ConjStrong`, `ConjEK` and `EKPackage.deltaE` are absent from the
transitive-constant closures of `prop_consequence` and `prop_dictionary`, and
`cor_horizontal`'s closure contains none of them either — its only conjectural
entry is its own hypothesis `ConjWeak`, which is what the paper's Theorem A also
assumes.** §6.6 reproduces the check and states its limits.

Three categories recur, and each item is labelled with one on introduction:
**(exposition)** — prose with no proposition to formalise; **(citation)** — real
mathematics, but exactly what the interface exists to absorb as a named sourced
assumption, so "not formalised" means "assumed, visibly, per §1.3" rather than
"missing"; **(open)** — content the paper does not claim to have proved.

### 5.2 The integral content of `prop:jetformula` (and the bookkeeping behind `hyp:sinnott`(i))

**(citation, flagged as such by the paper itself)**

`prop:jetformula` proves the identity
`c₂(L^K) = (1/2 log_p(1+p)²) ∫ ℓ(g)² dμ_ψ(g)`, obtained by expanding
`(1+T)^{m(g)}` in binomial coefficients of a `ℤ_p`-valued exponent and integrating
termwise against the Katz measure. `prop:grading`(1) reduces the integral, coset by
coset, to the grade-two moment sum `M₂(𝔭)`, and §`ssec:moments` identifies `M₂(𝔭)`
with an explicit unit-linear combination of Eisenstein–Kronecker numbers through
the Bannai–Kobayashi interpolation property.

None of that exists in mathlib or in this project: not the construction of the
Katz measure from elliptic units, not its integration theory, not the
Amice–Mahler correspondence, not the Fourier and Kummer-congruence bookkeeping
that turns polynomial moments into Eisenstein–Kronecker numbers. mathlib at this
pin does have an abstract-measure framework
(`Mathlib/NumberTheory/Padics/Measure/`, defining an `R`-valued measure on `X` as
a continuous `R`-linear functional on `C(X,R)`), which is where a formalisation of
the Iwasawa algebra would start; it does not reach the Katz measure or elliptic
units.

What is formalised instead is the resulting algebraic congruence:
`KatzData.grading_congr : ∃ κ₀ : Wˣ, p²·(κ₀·coeff 2 LKatz − m2core) ∈ (p³)`, an
interface field with `SOURCE: Bannai–Kobayashi Prop. 3.3 / Thm. 3.7 (Duke Math. J.
153 (2010)) + de Shalit II §4`, `STATUS: consequence-form`. Its docstring is
explicit about the boundary: the bookkeeping identifying `M₂(𝔭)` with `m2core` "to
the last constant" is not carried in Lean, and the field records only the
congruence. That is the same admission the paper makes about `hyp:sinnott`(i),
which it states as a hypothesis for exactly this reason.

**Effect.** `KatzData`, hence `grading_congr`, is destructured by exactly one
declaration, `thm_reduction` (checkable: `grep -rn '\.katz' FinShaRank2/Main/`
returns `Main/Reduction.lean` only). `thm_reduction` has always been conditional on
`hyp:sinnott` and `conj:EK`. So this descope shifts trust onto a citation inside a
declaration that was already conditional.

### 5.3 The geometry of `D_E` and the values of the package

**(citation for the definitional shape; `δ_E(c) ≠ 0` itself is `conj:EK`, open)**

`eq:DEdef` constructs `D_E` as the ray class group `Cl_𝔣(K) = (𝒪_K/𝔣)^×/μ_K`, on
which `Gal(K(𝔣)/K)` acts simply transitively through the Artin map. `eq:jetpackage`
constructs the six functions `r_{a,b}([g]) = ε(g)^{-(a+b)} e^*_{a,b}(t_g,0)/A(Γ)^a`
as the grade-≤2 jet of the reduced theta function along the `𝔣`-division values;
in coordinates these are expressions in `E₁^*`, `℘`, `℘′` and the quasi-period
`s₂`. `def:deltaE` then sets `δ_E(c) = ∏_{t ∈ D_E} F_c(t)`.

The Lean rendering keeps the resultant and abstracts the geometry:
`EKPackage` carries `ι` (a type of points), `D : Finset ι`, `r : Fin 6 → ι → L`
and `v : ℕ → Valuation L Γ` as data, and `δ_E(c)` is then the definition
`EKPackage.deltaE`, computed rather than assumed. What is *not* rendered is
everything that makes `D_E` a ray class group and `r` a jet of a theta function:
the class-group structure, the Galois action, the equivariance, the algebraic
theta machinery, and the Weierstrass and quasi-period expressions. mathlib has none
of it, and the paper does not carry out the evaluation for the testbed curve either
— `rmk:correlation` and §`sec:deltaEnumerics` treat computing the invariant as the
next step of the programme.

Two specific consequences of this abstraction are §5.6 and §5.7; they are the two
places where the abstraction is not conservative, and each says which way it cuts.

**Effect.** `EKPackage`, `δ_E(c)` and `supp` are consumed only by `thm_reduction`
and `thm_reduction_of_conjEK`. A referee should not expect the Lean repository to
contain evidence, numerical or formal, that `δ_E(c) ≠ 0` for the testbed curve; the
paper does not claim to have that evidence either, and `thm_reduction`'s
conditional status signals this at the type level.

### 5.4 The heights analytics: what `Reg_γ` does and does not carry into the kernel

**(citation — the one descope in this section that `prop_dictionary` depends on)**

The paper computes the cyclotomic `p`-adic regulator of the fixed basis
`{P₁, P₂}` through the `p`-adic sigma function of Mazur–Stein–Tate, by two
independent implementations (PARI's `ellpadicregulator`, Sage's `padic_regulator`)
that agree digit for digit. That computation is not reproduced or re-verified
anywhere in this repository.

`HeightData.Reg_γ : ℚ_[p]` is opaque data: there is no sigma-function
construction behind it in Lean. `spr_padicBSD` and `spr_nondeg` are
citation-grade fields (SOURCE: Schneider, Invent. Math. 79 (1985); Perrin-Riou,
Invent. Math. 109 (1992); packaged as Stein–Wuthrich Thm. 6.1). `prop_dictionary`
is proved by three rewrites: `c2norm_tie` identifies the height-side proxy with
the normalised jet, `spr_nondeg` is read as an iff, `shaOrd_tie` converts the
Ш-order proxy. The proof never needs `Reg_γ`'s numeric value or its digit
expansion — only that some element of `ℚ_[p]` exists satisfying the cited
equations.

So the digit strings displayed in the paper play no part in any Lean proof. In the
paper they serve a real purpose, as an independent numerical route to the same
conclusion; that purpose is external to the Lean chain. The height side enters the
formalisation solely as the citation `spr_padicBSD`/`spr_nondeg`, exactly as any
other classical theorem in `ClassicalInputs` does.

### 5.5 `lem:noanomalous`(1): Deuring's reduction criterion

**(citation)**

Part (2) of `lem:noanomalous` is kernel-proved, in the strengthened form the paper
states (§2). Part (1) — if `p ≢ 1 (mod 4)` then `p ∣ a_p`, so `p` is not anomalous
— is not formalised. Its proof reduces to Deuring's reduction criterion: a prime
inert or ramified in the CM field has supersingular reduction, and supersingular
reduction means `p ∣ a_p`. mathlib has neither Deuring's criterion nor the
reduction of an elliptic curve with complex multiplication at a non-split prime, so
formalising part (1) means formalising the reduction theory of CM elliptic curves.

**Effect.** None on any declaration in the tree. Every statement in the
formalisation quantifies over split primes, `hsplit : p % 4 = 1`, so part (1) is
never in the antecedent of anything the kernel checks. Its role in the paper is to
support the hypothesis of Theorem A that only finitely many split primes are
anomalous, which the Lean encoding obtains differently (§2, `cor:horizontal` row).

### 5.6 `conj:EK`: the hypothesis `#Cl_𝔣(K) ≥ 6` is not rendered

**(descope that widens the rendered statement — read this one carefully)**

`conj:EK` in the paper assumes `#Cl_𝔣(K) ≥ 6`, and the paper explains that the
hypothesis is forced: the equivariant functions on the torsor `D_E` form a
`K`-space of dimension `#Cl_𝔣(K)`, so with fewer classes than sections some
combination of the six sections vanishes identically on `D_E`, and `δ_E(c) = 0` for
that `c`.

`ConjEK H` does not carry the hypothesis, because in this encoding there is
nothing to attach it to: `EKPackage.D` is an abstract `Finset ι` with no class
group and no equivariance. Dropping a hypothesis from a conjecture **widens** what
the conjecture asserts. A package with `#D < 6` makes `ConjEK` false, and nothing
in the encoding rules such a package out. So `ConjEK H` renders `conj:EK` only for
those `H` whose package meets the paper's hypothesis.

This is recorded in `ConjEK`'s own docstring in `Statements.lean`, in the same
terms. Elsewhere in the formalisation a dropped hypothesis is safe, because the
Lean proof establishes the stronger statement (`prop_consequence`,
`prop_dictionary`, §2). Here nothing is proved: a conjecture is stated in a wider
form than the paper states it. A referee should treat `thm_reduction_of_conjEK` as
conditional on `ConjEK H` for a package satisfying `#D ≥ 6`, which is a hypothesis
about `H` that the Lean statement does not itself express.

`thm_reduction` is unaffected: it takes the single instance
`hEK : H.ek.deltaE c ≠ 0` rather than the conjecture.

### 5.7 `lem:orbit`: proved, but on an input the paper assumes

**(citation, with the assumption on the paper's side)**

Both parts of `lem:orbit` are kernel-proved in `Kernel/Orbit.lean`, in full
generality: for a Galois extension `L/K` and a finite set `D` with a
`Gal(L/K)`-action, an equivariant `F : D → L` has `∏_{t ∈ D} F(t) ∈ K`, and if the
action is transitive then `F` vanishes either everywhere on `D` or nowhere.

What the lemma needs, and what neither the paper nor the formalisation proves, is
that its hypotheses hold for `D_E` and the package: the equivariance
`r_{a,b}(σt) = σ(r_{a,b}(t))`. The paper says so — it grants the equivariance as an
input, citing Bannai–Kobayashi Thm. 2.9 and Cor. 2.11 for the algebraicity of the
section values and the simply transitive action of `Gal(K(𝔣)/K)` on
`D_E = Cl_𝔣(K)`, but it does not verify the equivariance itself. The Lean encoding
inherits this: `EKPackage` carries no group action, so `lem:orbit` cannot be
applied to a package at all.

**Effect.** The visible consequence is that `δ_E(c)` is **not** proved to lie in
`K`. `EKPackage.deltaE` lands in `P.L`, the paper's `Q̄`, and the divisibility
condition `𝔭 ∤ δ_E(c)` is therefore not symmetric in `𝔭` and `𝔭̄`. The structure
this replaced tested that condition with `padicValRat`, which asserted a
rationality that is not available. `thm_reduction` does not use `lem:orbit`, and it
does not need to: its side condition is the valuation statement
`H.ek.v p (H.ek.deltaE c) = 1` at the fixed prime `𝔭` of the embedding.

### 5.8 §3 background: the Sinnott–Gillard mechanism and (BK1)–(BK3)

**(exposition, with two partial exceptions already accounted for as citations)**

The paper's background section is labelled expository by the paper itself. It
recalls the Katz measure's construction from elliptic units, states Gillard's
theorem (`thm:gillard`: the vanishing of the `μ`-invariant of every branch of the
Katz measure — the zeroth-jet analogue of the paper's second-jet question),
sketches Sinnott's proof, and states the three Bannai–Kobayashi structural theorems
that package the Katz measure's moments as Eisenstein–Kronecker numbers. Nothing in
it is presented as new; its role is to explain why one might expect the second-jet
question to be horizontally rigid.

`thm:gillard` is not needed anywhere in the Lean interface: no field cites
Gillard's theorem as a `SOURCE`. The Iwasawa-module structure the formalisation
needs is `IwasawaData.rubin_structure`, which cites Washington GTM 83 Thm. 13.12
fused with Rubin, Invent. Math. 103 (1991), Thm. 12.3 (via Yager) — a different
result. The Bannai–Kobayashi structural theorems fare differently: they are the
justification behind two citation-grade fields already logged in §2,
`KatzData.comparison` and `KatzData.grading_congr`, but the general structural
theorems, stated for an arbitrary CM lattice, are not themselves rendered. That is
§5.2's descope under another name, not an additional one.

**Effect.** None. `thm:gillard` is cited by no field; the two Bannai–Kobayashi
fields live in `KatzData`, which only `thm_reduction` destructures.

### 5.9 The evidence part: the scan, and the Coates–Liang–Sujatha input

**(exposition — computations and citations, not claims with proof obligations)**

Paper v2's evidence part computes `v_𝔭(Reg_𝔭)` at 508 split primes in four
segments, up to `p = 16889`, through PARI's `ellpadicregulator`, finding the
generic value `2` at every one, with zero exceptions and zero escalations under the
paper's precision protocol. It also states the Coates–Liang–Sujatha input
(`thm:cls`), the isogeny transfer (`lem:isogeny`), the resulting vanishing
`cor:shavanishing` — Ш(E/ℚ)[p^∞] = 0 at every split `p < 30,000` for the testbed
curve — and `prop:scaneq`, which says that below 30,000 the unit condition reduces
to a condition on the regulator alone.

None of this is formalised, and none of it has a proof obligation the kernel could
discharge. The 508 PARI computations are not reproduced in Lean; formalising even a
few would need a scan-scale certificate structure, at a cost proportional to the
number of primes. `thm:cls`, `lem:isogeny` and `cor:shavanishing` are citations and
a transfer argument about a specific curve; `prop:scaneq` combines them with
`prop:dictionary`, whose Lean counterpart is `prop_dictionary`.

**Effect.** None on any Lean declaration. A referee evaluating the formalisation
can disregard the evidence part; a referee evaluating the paper's case for
`conj:strong` should read the scan as the paper presents it — reproducible PARI
computation offered as evidence for a stated conjecture, not claimed as a proof.
The scripts and data are in `../code`.

### 5.10 The outlook section

**(exposition — open problems, nothing with a truth value to formalise)**

The outlook discusses the inert-prime analogue (supersingular reduction, no unit
root, no classical Katz measure), citing Burungale–Kobayashi–Ota and
Pollack–Rubin as the relevant foundations and noting that the correct formulation
of generic `±`-regulator valuation at rank two is not in the literature; it poses
the nonvanishing of the determinant of the height pairing matrix at almost all
split primes as an open problem, for which no case is known for any curve; and it
discusses what a proof of the weak conjecture would and would not give.

**Effect.** None. The section states no proposition about the paper's own results
that the formalisation could support or undermine.

### 5.11 The prose remarks

**(exposition in every case)**

* **`ssec:failuremodes`** classifies two ways `conj:strong` could fail: irreducible
  `𝔭`-dependence of the cyclotomic-direction jet, and a Wieferich-type collapse of
  `δ_E`. A taxonomy of ways a conjecture could fail is not a proposition. Its
  content is what §1.4's split already renders, by isolating `hyp:sinnott` and
  `conj:EK` as the only two conjectural hypotheses.
* **`rmk:fq`** explains what the decoupling excludes: at a double zero the product
  rule kills the first-order contributions of the comparison and Euler factors. Its
  mathematical content is `lem:decoupling` itself, which is kernel-proved and
  ring-generic (`Kernel/Decoupling.lean`). The remark is framing around a
  formalised lemma.
* **`rmk:modesnow`** identifies the two failure modes with the two named inputs of
  `thm:reduction`. This is commentary connecting the hypothesis-position status of
  `SinnottHyp` (§1.4) with the proof of `lem:decoupling`; no new content.
* **`rmk:correlation`** explains how the scan acquires an algebraic reading through
  `thm:reduction`. Its content is §5.3 and §5.9 restated in interpretive terms.
* **`cav:deltaEscope`** separates what the numerical work on `δ_E(c)` settles from
  what it does not, beginning with the fact that it does not identify the vector —
  which is `hyp:sinnott`(i), the conjectural hypothesis. It is a scope statement
  about evidence, with no proposition to discharge.

**Effect.** None of these states a proposition feeding any proof step of
`prop_consequence`, `prop_dictionary`, `cor_horizontal` or `thm_reduction`.

### 5.12 Two loose ends: `rmk:nofinitesub` and `rmk:integrality`

`rmk:nofinitesub` is a remark about proof strategy: the proof of
`prop:consequence` avoids the `p`-adic leading-term formalism by using "no finite
`Λ`-submodule, then rank forcing `M = 0`" instead. The fact it discusses,
`IwasawaData.no_finite_submodule` (SOURCE: Greenberg, LNM 1716, Prop. 4.14), is a
genuine interface field and is consumed by `prop_consequence` at step 6. Only the
remark's English commentary has no Lean rendering. A referee who has checked
`no_finite_submodule` against Greenberg's Prop. 4.14 has checked everything the
remark refers to.

`rmk:integrality` asserts integrality of `c₂(p)` for all split `p` outside an
explicit finite set, deriving it from integrality of the modular symbols of `E`
(Greenberg–Vatsal Prop. 3.7; the elliptic-curve form is Stein–Wuthrich Prop. 3.7),
together with the fact that `ρ̄_{E,p}` is reducible for only finitely many `p`
(Mazur 1978). In the Lean encoding integrality is not a hypothesis anywhere,
because it is automatic: `AnalyticData.Lp : Λ p` with `Λ p := PowerSeries ℤ_[p]`,
so `coeff 2 Lp ∈ ℤ_[p]` by construction. The remark's citations are therefore not
carried in the tree — nothing needs them. This is a genuine difference of shape
rather than a shared claim: the paper must prove integrality because its `c₂(p)` is
a priori a `p`-adic number, and the formalisation gets it from the type of `Lp`, at
the cost of building integrality into the interface rather than deriving it. The
same remark is why `ConjStrong` omits the integrality clause of `conj:strong`; the
paper's own assessment is that the integrality assertion is not the conjecture's
substance, the unit assertion is.

### 5.13 Summary: where the trust sits

| Item | Category | Trust lands on | Affects `prop_consequence`, `prop_dictionary` or `cor_horizontal`? |
|---|---|---|---|
| `prop:jetformula` integral content (§5.2) | citation, self-flagged | Bannai–Kobayashi §§2–3, via `grading_congr` | No — `thm_reduction` only |
| `D_E` geometry and the package (§5.3) | citation (shape) + open (nonvanishing) | the paper's own construction; `conj:EK` is open | No — `thm_reduction` only |
| Heights analytics, `Reg_γ` (§5.4) | citation | Schneider/Perrin-Riou via Stein–Wuthrich Thm. 6.1 | **Yes**, for `prop_dictionary`, through the citation — not through the digit expansion |
| `lem:noanomalous`(1) (§5.5) | citation | Deuring's criterion, absent from mathlib | No — every statement quantifies over split primes |
| `conj:EK`'s hypothesis `#Cl_𝔣(K) ≥ 6` (§5.6) | descope that widens | the reader, who must supply the hypothesis about `H` | No — `thm_reduction_of_conjEK` only |
| `lem:orbit`'s equivariance input (§5.7) | assumption on the paper's side | Bannai–Kobayashi Thm. 2.9, Cor. 2.11, plus an unverified equivariance | No — `lem:orbit` is proved and unused by `thm_reduction` |
| Background: `thm:gillard`, (BK1)–(BK3) (§5.8) | exposition (overlaps §5.2) | nothing beyond §5.2 | No |
| The scan and the CLS input (§5.9) | exposition + citation | PARI, and Coates–Liang–Sujatha for `cor:shavanishing` | No |
| The outlook (§5.10) | exposition | nothing — open problems | No |
| The prose remarks (§5.11) | exposition | nothing beyond already-logged citations and lemmas | No |
| `rmk:nofinitesub` (§5.12) | already formalised | `no_finite_submodule` (Greenberg LNM 1716) | Yes — through a row already in §2 |
| `rmk:integrality` (§5.12) | different shape in Lean | the type `Λ p := PowerSeries ℤ_[p]` | Yes — but nothing is assumed |

Every descope that reaches `prop_consequence`, `prop_dictionary` or
`cor_horizontal` does so through material carried as a named, sourced field of
`ClassicalInputs`. The descopes involving a genuinely open question are confined
to `thm_reduction` and `thm_reduction_of_conjEK`, which is where the paper places
them. "Harmless" here means harmless to the status of the theorems that carry no
conjectural hypothesis. It does not mean unimportant: §5.4 is mathematics
`prop_dictionary` depends on and this project trusts as a citation rather than
reconstructs, and §5.6 states a conjecture in a wider form than the paper does.
Each says so.

---

## 6. Build and audit instructions

### 6.1 Toolchain and dependencies

All commands below are run from `formalisation/`, the root of this Lake project.
The manuscript is not part of this repository, and the computer algebra behind
the paper's evidence part is in `../code`; neither is needed to run the audit.

* **Lean toolchain**: pinned by `lean-toolchain`, which reads
  ```
  leanprover/lean4:v4.33.1
  ```
  `elan` reads this file automatically on `lake build` and `lake exe`; a referee
  with `elan` installed need set nothing by hand.
* **Mathlib**: pinned by `lake-manifest.json`, whose `mathlib` entry records
  ```
  "rev": "0df444a360eaa60ab8c11dca51a86af692955474"
  ```
  with `"inputRev": "v4.33.1"`. This is the commit all 82 audited declarations
  were checked against. **Do not run `lake update`**: it re-resolves the manifest
  and can move the pin. A fresh clone or checkout reproduces the pin
  automatically, since `lake-manifest.json` is tracked.

With those two files in place, the three commands below are all a referee needs to
run, in order.

### 6.2 `lake exe cache get`

```
$ lake exe cache get
Current branch: HEAD
Using cache from origin: (some leanprover-community/mathlib4)
No files to download
Already decompressed 8690 file(s)
```

This downloads precompiled `.olean` files for mathlib at the pinned revision from
the mathlib community's public cache, so that a referee does not compile mathlib
from source. On a cold clone it downloads and decompresses several thousand files,
a multi-gigabyte transfer whose wall time is dominated by network bandwidth; this
document reports no number for that. **The run above is warm** — this tree already
had every mathlib file decompressed — so `cache get` correctly reports "No files
to download" and finishes in about nine seconds of local bookkeeping.

### 6.3 `lake build`

```
$ lake build
Build completed successfully (8741 jobs).
```
Observed wall time 4.4s. The build emits no warnings.

**Honesty note.** This tree was already fully built when the command was run:
`.lake/build` held every `.olean` from this project's own files as well as
mathlib's. `lake build` therefore compiled nothing; it walked the dependency
graph, found all 8741 jobs up to date, and reported success. That is a warm
no-op, not a from-scratch timing, and this document does not claim otherwise. A
referee running it on a cold `.lake` — after `lake exe cache get` has restored
mathlib's `.olean` files, as in §6.2 — will see it compile this project's own
files, which is a small library by mathlib's standards. If `lake build` is run
*before* `lake exe cache get` on a cold clone, it will compile mathlib from
source, which is the hour-plus cost §6.2 describes.

### 6.4 `./scripts/audit.sh`

The full, unedited output of `./scripts/audit.sh`, run from `formalisation/` on
2026-08-29 against commit `3b54e41`. Observed wall time 22.4s, of which step
[1/3] is the `lake build` of §6.3.

```
=== [1/3] lake build ===
Build completed successfully (8741 jobs).
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
AxiomAudit OK: FinShaRank2.σR uses only [propext, Classical.choice, Quot.sound]
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
AxiomAudit OK: FinShaRank2.ClassicalInputs.isPUnit_one_sub_alphaInv uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.cor_horizontal uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.thm_reduction_of_conjEK uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Toy.toyAnalytic uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Toy.toySelmer uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Toy.toyIwasawa uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Toy.toyHeight uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Toy.toyKatz uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Toy.toyEK uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Toy.Setup.ap_ne_one uses only [propext, Classical.choice, Quot.sound]
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
AxiomAudit OK: FinShaRank2.toySha_fails_c2_5_certificate uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.ToyTrivial uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Resultant.forall_eq_one_of_prod_eq_one uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Resultant.prod_ne_zero_of_prod_eq_one uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Orbit.prod_mem_range_algebraMap uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.Orbit.forall_eq_zero_of_exists_eq_zero uses only [propext, Quot.sound]
AxiomAudit OK: FinShaRank2.anomalous_iff_five uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.jetIndex_image uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.jetIndex_injective uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.EKPackage.deltaE_ne_zero_iff uses only [propext, Classical.choice, Quot.sound]
AxiomAudit OK: FinShaRank2.EKPackage.deltaE_singleton uses only [propext, Classical.choice, Quot.sound]
AxiomAudit: all 82 audited declaration(s) clean
[3/3] OK: axiom whitelist holds for all audited decls

AUDIT: PASS
```

### 6.5 Reading a PASS

`scripts/audit.sh` runs three checks in order. It exits immediately on a `[1/3]`
failure; `[2/3]` and `[3/3]` both run, and both must report `OK` for the final
`AUDIT: PASS`.

* **`[1/3] lake build`** — the whole project, mathlib included, must typecheck.
  This is the ordinary Lean compiler. `[1/3] OK: lake build green` is the kernel
  having accepted every declaration's type; it says nothing yet about incomplete
  proofs or axioms.
* **`[2/3]` the no-incomplete-proof scan** — `grep -rnE '\b(sorry|admit)\b'` over
  `FinShaRank2.lean` and `FinShaRank2/`, excluding
  `FinShaRank2/Scratch/`, with any match checked against
  `scripts/sorry-allowlist.txt`. **That allowlist is empty**: 19 lines, all
  comments or blank, carrying a note that it was non-empty only during the
  statement-freeze window and was emptied once every frozen signature was proved.
  An empty allowlist means step `[2/3]` accepts no incomplete proof anywhere under
  `FinShaRank2/` outside `Scratch/`. This is the most literally checkable claim in
  this document: not "the headline theorems are complete", which an allowlist could
  hide exceptions from, but "nothing in the imported tree is incomplete", because
  there is nothing on the allowlist to hide behind.
* **`[3/3]` the axiom gate** — `lake env lean FinShaRank2/AxiomAudit.lean`
  elaborates a program that calls Lean's own `Lean.collectAxioms` on each of the
  82 names in `AxiomAudit.auditedDecls` — the five headline theorems, both toy
  instances layer by layer, and every kernel lemma feeding them — and fails
  elaboration, hence the script, if any declaration is **missing** or transitively
  depends on an axiom outside `{propext, Classical.choice, Quot.sound}`. Because
  it fails on a missing declaration, the list doubles as a rename tripwire. It
  also catches `native_decide`, which would introduce `Lean.ofReduceBool`. Each
  `AxiomAudit OK: …` line is one declaration's result; the summary line
  `AxiomAudit: all 82 audited declaration(s) clean` is what a referee should look
  for. The count is machine-generated from `auditedDecls`, so this document cannot
  misreport it without the two disagreeing.

The final `AUDIT: PASS` is the conjunction of the three. A referee reproducing
this document's claims needs that line, the empty allowlist, and the count 82.

### 6.6 Checking the epistemic split mechanically: a transitive-constant scan

`scripts/audit.sh` certifies axiom-cleanliness. It does not by itself certify the
narrower claim of §1.4 and §5.1: that the proofs of `prop_consequence`,
`prop_dictionary` and `cor_horizontal` do not touch the conjectural surface at
all, as opposed to touching it and happening to avoid the named conjectural
hypotheses. That is checkable by walking the transitive closure of constants each
declaration's type and proof term depend on. The program below does it. It is not
part of the audited library — it imports `FinShaRank2` as a client — and belongs
in a file outside `FinShaRank2/`, so that the scans of `audit.sh` do not see it:

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
  ["KatzData", "SinnottHyp", "ConjStrong", "ConjWeak", "ConjEK",
   "EKPackage.deltaE", "traceClass", "m2core", "criterionClass"]

open Lean Elab Command in
elab "#scan " id:ident : command => do
  let env ← getEnv
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  let (_, s) := (deps env n).run {}
  let bad := s.toList.filter (fun m => markers.any (has m.toString))
  logInfo m!"{n}: total deps = {s.size}, conjectural-surface deps = {bad}"

#scan FinShaRank2.prop_consequence
#scan FinShaRank2.prop_dictionary
#scan FinShaRank2.cor_horizontal
#scan FinShaRank2.thm_reduction
#scan FinShaRank2.thm_reduction_of_conjEK
```

Save it as, say, `Scratch/AxiomScan.lean` and run
`lake env lean Scratch/AxiomScan.lean` from `formalisation/`. Reproduced verbatim
from a run on 2026-08-29 against commit `3b54e41`:

```
FinShaRank2.prop_consequence: total deps = 2591, conjectural-surface deps = []
FinShaRank2.prop_dictionary: total deps = 1985, conjectural-surface deps = []
FinShaRank2.cor_horizontal: total deps = 1983, conjectural-surface deps = [FinShaRank2.ConjStrong._proof_1,
 FinShaRank2.ConjWeak]
FinShaRank2.thm_reduction: total deps = 2093, conjectural-surface deps = [FinShaRank2.EKPackage.deltaE,
 FinShaRank2.KatzData,
 FinShaRank2.ConjStrong,
 FinShaRank2.ConjStrong._proof_1,
 FinShaRank2.SinnottHyp]
FinShaRank2.thm_reduction_of_conjEK: total deps = 2094, conjectural-surface deps = [FinShaRank2.EKPackage.deltaE,
 FinShaRank2.KatzData,
 FinShaRank2.ConjStrong,
 FinShaRank2.ConjStrong._proof_1,
 FinShaRank2.SinnottHyp,
 FinShaRank2.ConjEK]
```

**How to read this.** `deps` is a worklist closure over `Expr.getUsedConstants`,
applied to a declaration's type and to its proof term, recursively. The total
count — 1983 to 2591, overwhelmingly mathlib — is the set of constants each
declaration's statement and proof rest on. `markers` is a substring filter for
anything Katz-, Sinnott- or `δ_E`-flavoured. Three things to note in the output.

1. **The asymmetry is §1.4's claim, made mechanical.** `thm_reduction`'s closure
   contains `KatzData`, `SinnottHyp` and `ConjStrong`, and
   `thm_reduction_of_conjEK`'s contains `ConjEK` as well; those are really
   consumed. The closures of `prop_consequence` and `prop_dictionary` contain none
   of them.
2. **`cor_horizontal`'s two entries are not conjectural surface.** `ConjWeak` is
   its own hypothesis, which is the hypothesis the paper's Theorem A also assumes.
   `ConjStrong._proof_1` is an auto-generated auxiliary lemma,
   `∀ p, Nat.Prime p → Fact (Nat.Prime p)`, elaborated first at `ConjStrong` and
   reused by `ConjWeak`; it is named after `ConjStrong` and carries none of its
   content. `#print FinShaRank2.ConjStrong._proof_1` shows this in one line.
3. **The scan does not see structure projections, and cannot be used to argue
   that an interface field is unused.** In Lean 4 a structure projection appears
   in a proof term as an `Expr.proj` node rather than as a constant application,
   so `getUsedConstants` does not report it. Running the same closure with
   interface-field names as markers therefore reports almost every field as
   absent, whether or not a proof uses it. The check for field usage is a source
   grep, `grep -rn '\.<field>' FinShaRank2/` with `Interface/`, `Toy/` and
   `Scratch/` excluded; that is how the six unused fields listed at the end of §2
   were identified. What the closure scan does see, and what makes it useful here,
   is structure *type* names and non-projection constants — `KatzData`,
   `SinnottHyp`, `ConjStrong`, `ConjEK`, and the def `EKPackage.deltaE`.

One name is deliberately absent from the marker list: `EKPackage` itself, which
appears in all five closures, because `ClassicalInputs.ek : EKPackage` is a field
and every statement about a `ClassicalInputs` mentions its type. Including it would
report a hit for every declaration and distinguish nothing. The distinguishing
marker is the def `EKPackage.deltaE`, which appears only in the two
`thm_reduction` closures.
