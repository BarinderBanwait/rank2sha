# FinShaRank2 — the Lean formalisation

A Lean 4 formalisation of the main statements of *Second derivatives of $p$-adic
$L$-functions and the Shafarevich–Tate group of rank-two CM elliptic curves*,
together with a blueprint linking the informal argument to the Lean declarations.

Part 3 of the paper (§§8–12) says what the formalisation establishes and what it
does not. This file is how you navigate it: what to read, what to run, and where
the Lean differs from the paper.

This directory holds the Lean project and nothing else. The computer algebra —
the PARI/GP and SageMath scripts behind Part 2 of the paper, and the output of
every run — is in `../code`; see `../code/README.md`. The manuscript itself is
not part of this repository.

| Path | What it is |
|---|---|
| `FinShaRank2/` | the Lean sources: interface, kernel lemmas, main theorems |
| `FinShaRank2/Interface/` | the assumption surface — the six files §3 asks you to read |
| `FinShaRank2/Scratch/` | working files, excluded from the build and the audit gate |
| `FinShaRank2/Toy/` | the two witness worlds of §7 |
| `blueprint/` | the blueprint; see §9 |
| `scripts/` | `audit.sh` and the (empty) sorry allowlist |

Paper statements are referred to by their printed numbers, as the PDF prints
them, and the three lettered results by both — Theorem A (Theorem 4.9), Theorem C
(Theorem 5.10). The docstrings in the Lean sources do the same, and each keeps
its TeX label on the `PAPER:` line, so a renumbering can be tracked down rather
than hunted for. Declarations are referred to by name and file; there are no line
numbers here, because they rot. Everything below is greppable from
`formalisation/`.

## 1. What is proved and what is assumed

Mathlib has no Shafarevich–Tate group, no Selmer group of an elliptic curve, and
no $p$-adic $L$-function of any kind. Supplying them is a project of several
years. So this is a formalisation *modulo the literature*: the classical theorems
the paper takes from other authors are assumed, as explicitly stated fields of one
structure, and everything the paper deduces from them is machine-checked.

Two categories, and which one a fact belongs to is visible in the source.

**`ClassicalInputs`** (`Interface/Global.lean`) is the assumed classical
material. Six fields: the excluded set `S` of (10); the Eisenstein–Kronecker
package `ek`; the rational factor `torsSqOverTam` with its defining equation
`torsSqOverTam_eq`; the per-prime bundle `dataAt`, which supplies a `PrimeData` at
every split `p ∉ S`; and `notAnomalous`. `PrimeData` in turn aggregates five
layers — `AnalyticData`, `SelmerData`, `IwasawaData`, `HeightData`, `KatzData`.
Every headline theorem takes `H : ClassicalInputs` as an ordinary hypothesis.

**Conjectural hypotheses** are three, and none is a field of `ClassicalInputs` or
of any structure that is ever instantiated: `SinnottHyp` (Hypothesis 5.8,
`Interface/Katz.lean`), `ConjEK` (Conjecture 5.9, `Statements.lean`) and `ConjWeak`
(Conjecture 4.7, `Statements.lean`). Each occurs in hypothesis position only. Figure
2 of the paper shows which declarations take which; §8 below is the machine check.

There are no `axiom` declarations anywhere in the project. Every assumed input is
a structure field or a hypothesis, so it appears in the statement of any theorem
that uses it. `#print axioms` on any of the audited declarations reports only
Lean's own three; §2 says how that is checked and which declarations are covered.

### What this does not mean

* The cited classical theorems have not themselves been formally verified. They
  are trusted the way you trust a citation. Checking that each is real, correctly
  attributed and correctly used is the human task, and §3–§4 are about doing it.
* It does not mean the Lean statements are self-evidently the right rendering of
  the paper's mathematics. Same human task.
* Hypothesis 5.8 and Conjecture 5.9 are exactly as open as the paper says they are.
* Part 2 of the paper — the computations — is not formalised. Neither is the
  background survey of §2 nor the outlook of Part 4.

### Three conventions you need in order to read the statements

**Dual side.** Everything is phrased on the Pontryagin-dual side, as finitely
generated `ℤ_[p]`- or `Λ`-modules, where mathlib is strong. `SelDual` is
`Sel_{p^∞}(E/ℚ)^∨` and `ShaDual` is `Ш(E/ℚ)[p^∞]^∨`. The conclusion `Ш = 0`
appears as `Subsingleton ShaDual`.

**Valuations are multiplicative.** `EKPackage.v p` is a `Valuation` in mathlib's
sense, so the paper's `v_𝔭(x) ≥ 0` is `P.v p x ≤ 1`, and the paper's
`v_𝔭(x) = 0` — that `x` is a `𝔭`-unit — is `P.v p x = 1`. Read `SinnottHyp` with
this in mind or it will look inverted.

**No conclusion vocabulary in assumptions.** No interface field mentions `Ш`,
`Subsingleton ShaDual`, `MuZero` or `lambdaAn`. This is what keeps the conclusion
out of the hypotheses; §7 and §8 are two independent checks that it worked.

## 2. Build it and run the audit

The toolchain is pinned in `lean-toolchain` and `elan` installs it on demand. If
you do not have `elan`:

```sh
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

Then, from `formalisation/`:

```sh
lake exe cache get   # prebuilt mathlib oleans, so this takes minutes not hours
lake build
scripts/audit.sh
```

`audit.sh` runs three steps and prints `AUDIT: PASS` or fails loudly:

1. `lake build` is green.
2. No `sorry` and no `admit` anywhere in `FinShaRank2/` outside `Scratch/`,
   modulo `scripts/sorry-allowlist.txt` — **which is empty**, so no incomplete
   proof is tolerated in the imported tree.
3. Every declaration listed in `FinShaRank2/AxiomAudit.lean` depends on no axiom
   beyond `propext`, `Classical.choice` and `Quot.sound`. In particular nothing
   uses `native_decide`, which would move trust into the compiler.

The tail of a passing run:

```
AxiomAudit: all 82 audited declaration(s) clean
[3/3] OK: axiom whitelist holds for all audited decls

AUDIT: PASS
```

The whole thing takes well under a minute from a warm cache. If you want to see
which declarations are covered, read `AxiomAudit.lean`: the list is explicit, not
a wildcard.

## 3. What you actually have to read

Lean certifies that the conclusions follow from the assumptions. It cannot
certify that the assumptions are true, or that they say what the cited papers
say. That is the check left to you, and it is finite: the six files in
`FinShaRank2/Interface/`, and nothing else.

Every field in them carries a docstring in a fixed form:

```
SOURCE: <author, work, theorem number, page where relevant>
PAPER:  <the paper label and proof step that consumes it>
STATUS: classical | data | ...
```

So the question for each field is a narrow one: does the Lean statement say what
the cited theorem says, and is it used where the docstring claims? §4 walks
through one field end to end.

| File | Layer | What is assumed, and from whom |
|---|---|---|
| `Interface/Analytic.lean` | `AnalyticData p hsplit` | the Mazur–Tate–Teitelbaum $p$-adic $L$-function `L_p(E,T)`, its interpolation at the trivial character, the $p$-adic functional equation with sign `w(E) = +1`, unit-root data for `X² − a_p X + p`, evenness of `a_p` under CM, and the Hasse bound |
| `Interface/Iwasawa.lean` | `IwasawaData p`, `SelmerData p` | Greenberg's no-nonzero-finite-submodule (LNM 1716, Prop. 4.14); the fused structure-theorem-plus-Rubin field `rubin_structure`; Mazur control in consequence form; the dualised descent sequence |
| `Interface/Heights.lean` | `HeightData p` | the normalised cyclotomic $p$-adic regulator `Reg_γ` as opaque data, the nondegeneracy predicate, and Schneider/Perrin-Riou's leading-term theorem in the two consequence forms Proposition 4.13 uses, packaged as Stein–Wuthrich Thm. 6.1 |
| `Interface/Katz.lean` | `KatzData p Lp`, `SinnottHyp` | the comparison `L_p = c_p · u(T) · L^{Katz}_𝔭` of Lemma 4.4, the grading congruence behind Proposition 5.1 and Proposition 5.2, and the mod-`𝔭` trace class. `SinnottHyp` is declared here but is a field of nothing |
| `Interface/EK.lean` | `EKPackage` | the divisor `D_E`, the six sections `𝓡_E`, a valuation at each rational prime, and `supp`. `δ_E(c)` is a definition on top of these, not assumed data |
| `Interface/Global.lean` | `PrimeData`, `ClassicalInputs` | no new mathematics: the aggregation of the five layers and the tie-equations welding them together |

One caveat while you read: some docstrings cite `TASK_BOARD.md`, a working file
that is not in this repository. The conventions it holds are the three stated in
§1 above; nothing else in it bears on the statements.

## 4. A worked example: checking one assumption end to end

Say you want to satisfy yourself that Rubin's main conjecture enters the argument
correctly. Here is the whole procedure.

**Step 1. Find where it enters.**

```sh
grep -rn 'Rubin' FinShaRank2/Interface/
```

One field comes back: `rubin_structure`, in `Interface/Iwasawa.lean`. That is the
only place Rubin is assumed.

**Step 2. Read its docstring.** `SOURCE` names two works, because this field is
*fused*: Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM **83**,
Thm. 13.12, together with Rubin, *The "main conjectures" of Iwasawa theory for
imaginary quadratic fields*, Invent. math. **103** (1991), 25–68, Thm. 12.3,
through Yager's identification of the two-variable characteristic ideal with the
Katz measure restricted to the cyclotomic line. `PAPER` says Theorem A (Theorem 4.9)
Step 2, feeding Step 3. `STATUS` says classical.

**Step 3. Read the Lean statement and say it back in words.** Stripped of syntax,
`rubin_structure` asserts: there are an `n`, elements `f : Fin n → Λ`, and a map
`φ : X → ∏ᵢ Λ/(fᵢ)` whose kernel and cokernel are both finite — a
pseudo-isomorphism — such that `∏ᵢ fᵢ` is associated to `Lp`.

**Step 4. Compare with the sources.** Washington 13.12 gives the
pseudo-isomorphism onto a product of elementary quotients. Rubin 12.3, through
Yager, gives `car_Λ(X) = (Lp)`, which is the `Associated` clause. The question to
ask of a fused field is whether the conjunction asserts anything neither citation
supports on its own — that is where a fused field can go wrong, and it is why
this one is the example.

**Step 5. Check it is used where the docstring says.**

```sh
grep -rn 'rubin_structure' FinShaRank2/
```

The live use is in `Main/Consequence.lean`, where it is destructured and fed to
`selmer_dual_structure` — Theorem A (Theorem 4.9) Step 3, matching the `PAPER` line.
The remaining hits are the toy worlds of §7 and files under `Scratch/`, which is
excluded from the build and from the audit.

**Step 6. Decide.** If the field says what the two theorems say, that assumption
is discharged, and nothing downstream of it needs your attention: the kernel
checked the rest. If it says more than they support, that is a defect worth
reporting — and note what kind. Because the field is a *hypothesis*, an
overstated field does not make any Lean proof wrong; it makes the theorem
inapplicable to the curve, which is a claim about the paper rather than about the
formalisation.

Repeat for the other fields. What you never have to do is read a Lean proof, or
check a case analysis, a module-theoretic step, or any valuation bookkeeping.

## 5. Statement by statement

Every declaration name below exists in the tree; `grep -rn '<name>' FinShaRank2/`
confirms it. The status column takes six values:

* **kernel-proved** — a `theorem`, sorry-free, proved from the interface and
  kernel layers, and covered by `AxiomAudit.lean`.
* **formal def** — a `def` rendering a paper definition or conjecture as a
  proposition. A `def` asserts nothing; what asserts is whatever consumes it.
* **interface field + citation** — a field carrying a `SOURCE`/`PAPER`/`STATUS`
  docstring. Not proved: it *is* the assumption.
* **data field** — opaque data, not a proposition.
* **conjectural hypothesis** — occurs in hypothesis position only.
* **no counterpart** — not formalised; §6 says why.

| Paper statement | Lean declaration(s) | File | Status |
|---|---|---|---|
| (9) | `HeightData.spr_padicBSD`, `HeightData.spr_nondeg` | `Interface/Heights.lean` | **interface field + citation** |
| (10) | `ClassicalInputs.S`, `ClassicalInputs.notAnomalous` | `Interface/Global.lean` | data field + **interface field** |
| (6) | `EKPackage.ι`, `EKPackage.D`, `EKPackage.D_nonempty` | `Interface/EK.lean` | data fields |
| (7) | `EKPackage.r`; `jetIndex`, `jetIndex_image`, `jetIndex_injective` | `Interface/EK.lean` | data field + **kernel-proved** |
| Definition 2.1 | `HorizontalControl` | `Statements.lean` | formal def |
| Lemma 2.3 | (2) `anomalous_iff_five`, `noAnomalous`, `ap_ne_one_of_hasse`, `two_dvd_ap` and two more; (1) — | `Kernel/Anomalous.lean` | (2) **kernel-proved**; (1) **no counterpart** |
| Lemma 4.1 | `c0_eq_zero`, `c1_eq_zero` | `Main/Lemma41.lean` | **kernel-proved** |
| Definition 4.2 | `c2tilde`; `PrimeData.c2tilde` | `Defs.lean`; `Statements.lean` | formal def |
| Proposition 4.3 | `isPUnit_c2tilde_iff`; `ClassicalInputs.isPUnit_one_sub_alphaInv` | `Kernel/Normalization.lean`; `Main/Consequence.lean` | **kernel-proved** |
| — (the strong form, withdrawn from the paper on 2026-09-03) | `ConjStrong`; `ConjStrongAt` | `Statements.lean` | formal def; `ConjStrongAt H c` is the conclusion of Theorem C at the vector `c`, `ConjStrong` renders no statement of the paper; see the note below |
| Conjecture 4.7 | `ConjWeak` | `Statements.lean` | formal def (conjectural) |
| Remark 4.8 | — | — | **no counterpart** (automatic: `Λ p := PowerSeries ℤ_[p]`) |
| Lemma 4.4 | `KatzData.comparison` | `Interface/Katz.lean` | **interface field + citation** |
| Lemma 4.5 | — | — | **no counterpart** |
| Theorem A (Theorem 4.9) | `prop_consequence` | `Main/Consequence.lean` | **kernel-proved** |
| Corollary B (Corollary 4.10) | `cor_horizontal` | `Main/Horizontal.lean` | **kernel-proved**, conditional on Conjecture 4.7 |
| Theorem 4.12 | — | — | **no counterpart** |
| Proposition 4.13 | `prop_dictionary` | `Main/Dictionary.lean` | **kernel-proved** |
| Proposition 5.1 | `KatzData.grading_congr` | `Interface/Katz.lean` | **interface field** (the integral content is assumed, not derived) |
| Proposition 5.2 | (2) `isUnit_iff_residue_ne_zero_of_grading_congr`; (1) `KatzData.grading_congr`, `m2core`, `criterionClass` | `Kernel/GradingValuation.lean`; `Interface/Katz.lean` | (2) **kernel-proved**; (1) **interface field** |
| Lemma 5.3 | `Decoupling.coeff_two_mul` and six further lemmas | `Kernel/Decoupling.lean` | **kernel-proved** |
| Definition 3.1 | `EKPackage.Fc`, `EKPackage.deltaE`, `deltaE_def`, `deltaE_ne_zero_iff` | `Interface/EK.lean` | formal def + **kernel-proved** |
| Lemma 3.2 | `Orbit.prod_mem_range_algebraMap` (1), `Orbit.forall_eq_zero_of_exists_eq_zero` (2) | `Kernel/Orbit.lean` | **kernel-proved** |
| Hypothesis 5.8 | `SinnottHyp` (fields `integral`, `presentation`, `nonvanishing`) | `Interface/Katz.lean` | **conjectural hypothesis** |
| Conjecture 5.9 | `ConjEK` | `Statements.lean` | formal def (conjectural) |
| Theorem C (Theorem 5.10) | `thm_reduction`; `thm_reduction_of_conjEK`; `Resultant.forall_eq_one_of_prod_eq_one` | `Main/Reduction.lean`; `Kernel/Resultant.lean` | **kernel-proved**, conditional on Hypothesis 5.8; concludes the unit condition at the given vector (`ConjStrongAt H c`) |

## 6. Where the Lean differs from the paper

Six differences change what is established. Read these before concluding
anything from a green audit.

**Theorem C's conclusion is the per-vector predicate `ConjStrongAt`, and its final
clause is not rendered.** `ConjStrongAt H c` asserts the unit condition at every split
`p ∉ H.S ∪ supp(c)` with `𝔭 ∤ δ_E(c)`, which is the display of Theorem C at the vector
`c`; `thm_reduction` proves it at the vector Hypothesis 5.8(i) presents. Its universal
closure `ConjStrong H`, that is `∀ c ≠ 0, ConjStrongAt H c`, rendered the strong form
of the conjecture, which the paper withdrew on 2026-09-03; it is kept as a definition,
is proved by no declaration, and renders no statement of the paper. Theorem C's final clause,
"if `S_E` is finite, Conjecture 4.7 holds for `E`", is absent: deriving it needs
`{p | 𝔭 ∣ δ_E(c)}` to be finite, which holds in the paper because `δ_E(c)` is a
nonzero algebraic number, but `EKPackage.v` is an abstract family of valuations
carrying no such field. So `ConjWeak` is never concluded in this project, only
consumed (by `cor_horizontal`).

**Conjecture 5.9 is rendered in a wider form.** The paper's conjecture assumes
`#Cl_𝔣(K) ≥ 6`, and explains that the hypothesis is forced: the equivariant
functions on `D_E` form a `K`-space of dimension `#Cl_𝔣(K)`, so with fewer classes
than sections some combination vanishes identically and `δ_E(c) = 0`. `ConjEK`
carries no such hypothesis, because `EKPackage.D` is an abstract `Finset` with no
class group to attach it to. Dropping a hypothesis from a conjecture *widens* it:
a package with `#D < 6` makes `ConjEK` false, and nothing in the encoding
excludes such a package. So `ConjEK H` renders Conjecture 5.9 only for those `H` whose
package meets the paper's hypothesis, and `thm_reduction_of_conjEK` should be
read as conditional on that. `thm_reduction` is unaffected — it takes the single
instance `δ_E(c) ≠ 0`, not the conjecture.

**Lemma 2.3(1) is not formalised.** It reduces to Deuring's reduction
criterion, which mathlib does not have. Nothing depends on it: every statement in
the project quantifies over split primes, where part (2) — which *is*
kernel-proved, in the strengthened form the paper states — applies.

**Lemma 3.2 is proved, but on an input the paper assumes.** Both parts are
proved in full generality, for a Galois extension and a finite set with a Galois
action. What is assumed is the equivariance `r_{a,b}(σt) = σ(r_{a,b}(t))` for the
package, which the paper also assumes rather than proves. `thm_reduction` does not
use Lemma 3.2.

**`cor_horizontal` proves more than Definition 2.1 asks.** The per-prime
predicate supplied is `Ш[p^∞] = 0`, where the paper's definition asks for
`Ш[p] = 0`. What is proved implies what is stated. Separately, the paper's
hypothesis that there are finitely many anomalous split primes has no counterpart:
`ClassicalInputs.S : Finset ℕ` is finite by construction and `notAnomalous` puts
every anomalous split prime inside it. That is a simplification the encoding
makes, not something proved.

**`thm_reduction` loses the clause "if `S_E` is finite"** for the same reason:
`H.S` is a `Finset`, so finiteness is not a hypothesis anyone can fail to meet.

Two statements in the table are marked **no counterpart** for a reason that is
not a descope. Theorem 4.12 is not the paper's own result — it combines
Rubin's main conjecture with Schneider's leading-term theorem — and the two
consequences of it that the argument uses are assumed directly, as
`HeightData.spr_padicBSD` and `spr_nondeg`, so there is nothing left to state
separately. Lemma 4.5 compares the Mazur–Swinnerton-Dyer and
Mazur–Tate–Teitelbaum normalisations; `AnalyticData` starts from the MTT
`L`-function, so the comparison never arises in Lean.

Two further points about where trust sits, neither a defect. The integral content
behind Proposition 5.1 is assumed as `KatzData.grading_congr` and rests on
Bannai–Kobayashi §§2–3; the paper flags this itself. And the height side enters
only as the citations `spr_padicBSD` and `spr_nondeg`: `Reg_γ` is opaque data,
there is no sigma-function construction in Lean, and no proof here needs its
numeric value. The regulator digits the paper displays play no part in any Lean
proof.

## 7. The assumptions are consistent, and do not contain the conclusion

Two constructions, both kernel-checked, guard the two ways an interface-first
formalisation can be worthless.

`ToyTrivial : ClassicalInputs` (`Toy/Trivial.lean`) is a value in which every
field is proved: `S = ∅`, `D_E` a single point over `ℚ`, sections `1`, `Lp = X²`,
`SelDual = ℤ_[p]²`, `ShaDual` trivial. A structure with a value is satisfiable, so
the assumptions are not contradictory — and so the main theorems are not
vacuously true.

`ToySha : ClassicalInputs` (`Toy/ShaTrivial.lean`) is a second value in which the
conclusion *fails*: `ShaDual` is `ℤ_[p]/(p)`, the μ-invariant does not vanish and
`λ_an ≠ 2`. Since it too satisfies every field, no combination of the assumptions
entails `Ш[p^∞] = 0`. It is a tripwire: strengthen an interface field until it
does entail the conclusion, and this file stops compiling.

One loose end you will meet in that file. `toySha_fails_c2_5_certificate` contains
the seven leading 5-adic digits of `c₂(5)`, and identifies the datum that excludes
the anti-vacuity world. Those digits are this project's own computation,
cross-checked by two independent implementations (PARI and Sage), and they
correspond to no display in the paper; the lemma's docstring says so.

## 8. Checking the conjectural surface mechanically

`audit.sh` certifies axiom-cleanliness. It does not by itself certify the
narrower claim that `prop_consequence`, `prop_dictionary` and `cor_horizontal`
never touch the conjectural surface — as opposed to touching it and happening to
avoid the named hypotheses. That is checkable by walking the transitive closure of
constants each declaration's type and proof term depend on.

Save this outside `FinShaRank2/`, so the audit's scans do not see it, and run
`lake env lean <file>` from `formalisation/`:

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

The closures of `prop_consequence` and `prop_dictionary` contain none of the
markers. `cor_horizontal`'s contains `ConjWeak`, which is its own hypothesis and
the one the paper's Corollary B also assumes. `thm_reduction`'s contains
`SinnottHyp`, `KatzData`, `ConjStrong` and `EKPackage.deltaE`;
`thm_reduction_of_conjEK`'s contains `ConjEK` as well. Those are consumed, and
the paper says so.

Three limits on what the scan shows. `ConjStrong` appears in `thm_reduction`'s
closure because it is in the *conclusion*, not the hypotheses. The marker list is
a substring filter, so it over-reports rather than under-reports. And the scan
sees constants, not structure projections, so it cannot be used to argue that a
declaration avoids some particular *field* of a structure it mentions.

## 9. The blueprint

`blueprint/` holds a blueprint in the usual Lean style, stating each result
informally beside the declaration that formalises it. Build it locally with

```sh
blueprint/bp pdf   # writes blueprint/print/print.pdf
blueprint/bp web   # writes blueprint/web/
```

See `blueprint/README.md` for the dependencies. The GitHub Pages workflow at
`.github/workflows/blueprint.yml` in the repository root runs the same two
commands, on manual dispatch only.
