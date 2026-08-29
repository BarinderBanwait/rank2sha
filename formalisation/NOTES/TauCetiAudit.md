# T04 — Tau Ceti consult audit

**Date:** 2026-07-15 · **Agent:** W1-C · **Repos surveyed:**
[TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti) (full file tree, 572 blobs / ~400 `.lean` files, enumerated via GitHub git-trees API, `truncated: false`) and
[TauCetiProject/TauCetiRoadmap](https://github.com/TauCetiProject/TauCetiRoadmap) (roadmap survey).

## Verdict

**UPHOLD consult-only (no `lake require`).** In fact the audit supports a stronger
conclusion: there is **nothing to reuse-by-adaptation** — the library's mathematical
coverage is essentially disjoint from this project's needs. Exactly one artifact is
worth consulting (their axiom-audit executable, for T02), and it is engineering, not
mathematics.

Three independent reasons, any one of which would suffice:

1. **Reproducibility (the standing reason, confirmed).** `lakefile.toml` requires
   mathlib with `rev = "master"` by design; the per-commit pin lives only in
   `lake-manifest.json` (currently `faaff5e5590ad6b6878f66d30a33ded94cd97cf6`) and is
   moved **forward daily** by an automated bump pipeline (`bump-guard`,
   `.github/workflows/update.yml`). Toolchain is `leanprover/lean4:v4.32.0-rc1` — a
   release candidate, ahead of any mathlib stable release we would pin at T01. A
   dependency would chain us to mathlib master churn. Confirmed poison.
2. **Coverage is empty where we need it.** Zero files on: power series (T10, T20–T22),
   p-adics / `ℤ_[p]` (T24, T26), Λ-modules / Iwasawa theory (T23), PID module structure
   theory (T23, T27), local rings (T25), Gaussian integers (T24), quotient modules over
   commutative rings (T23), elliptic curves, or L-functions. `RingTheory/` contains
   exactly one file (Hermite polynomial derivatives). The 13 roadmaps (universal covers,
   Jacobian challenge, reductive groups, PDEs, Heegaard Floer ×2, multiquadratic fields,
   Kirby problems, semigroups, de Finetti, conformal maps, orthogonal L² bases, contour
   integration) contain nothing p-adic or Iwasawa-adjacent, existing or planned.
3. **Mechanical incompatibility.** Every TauCeti file uses the new Lean module system
   (`module` / `public import` / `public section`) on the v4.32.0-rc1 toolchain, and
   declarations live in the `TauCeti.*` namespace. Verbatim copies would not compile in
   a mathlib-release-pinned project without systematic rework — so even hypothetical
   reuse would be by re-proving, not copying.

## Repo quality / trust assessment (for the record)

Better than expected for an AI-authored library; Lean-FRO-incubated. CI enforces: no
`sorry`, axiom allowlist exactly `propext, Classical.choice, Quot.sound` (kernel-level
check via `lake exe axioms`, so `native_decide` and hidden axioms are caught), full
mathlib linter set, `warningAsError`, file-length caps. PRs pass adversarial AI review
rubrics (TauCetiReview repo: correctness, mis-formalization, vacuity, reuse, naming,
placement) before auto-merge; humans own the rubrics and CI, AIs own the code. Files
skimmed were clean, well-documented, with provenance notes. **Conclusion:** if TauCeti
*did* cover our material, adapt-with-verification would be defensible. It does not, so
the question is moot. Trust caveat: their own README concedes "AI formalized
definitions are, a priori, untrustworthy" — anything ever taken from there must be
re-reviewed against our conventions (esp. board conv. 2 docstring discipline).

## Per-file findings

Files individually fetched and skimmed (all others triaged at directory level — see
second table). Board tasks that could plausibly have been helped are listed even when
the verdict is irrelevant, to show the mapping was checked.

| File | Content (one line) | Verdict | Board task |
|---|---|---|---|
| `scripts/Axioms.lean` | Axiom-allowlist audit executable: walks compiled env, memoized `collectAxioms`-style traversal, fails on any axiom outside `propext/Classical.choice/Quot.sound`; documents the `trustLevel := 1024` soundness caveat (audit runs *after* a kernel-checking `lake build`) | **consult-later** (the one useful item; ideas, not a dependency — it is Apache-2.0, human-owned governance code) | T02 |
| `NumberTheory/NumberField/SplitsCompletely.lean` | p splits completely in Galois K/ℚ ⟺ e = f = 1, count form of the fundamental identity | irrelevant — our "split p" is p ≡ 1 (mod 4) in ℤ[i], handled by mathlib `Nat.Prime.sq_add_sq` + `GaussianInt`; we never count primesOver | (T24) |
| `NumberTheory/NumberField/QuadraticSplitting.lean` | splitting law for ℚ(√d) via Legendre symbol + Kummer–Dedekind | irrelevant — same reason | (T24) |
| `NumberTheory/Multiquadratic/CMField.lean` (+ 35 sibling `Multiquadratic/*` files) | degrees/Galois groups of ℚ(i, √p₁, …, √pₙ); "CM" here means totally imaginary multiquadratic — no CM elliptic curves, no Hecke characters | irrelevant — our CM input is the interface field `ap_from_CM` over mathlib's `GaussianInt` | (T11, T24) |
| `NumberTheory/DedekindDomain/RamificationInertia.lean` | deprecated compatibility wrapper | irrelevant | — |
| `NumberTheory/LegendreSymbol/SquareClass.lean` | Legendre symbol invariant under multiplication by u² | irrelevant | — |
| `NumberTheory/EffectiveBounds/*` (21 files, incl. `WorkedExamples.lean`) | Minkowski-style discriminant/class-number bounds; worked examples on ℚ(i) (as `CyclotomicField 4 ℚ`) and ℚ(√−5) | irrelevant — the ℚ(i) content is discriminant arithmetic, not Gaussian-norm arithmetic; our numeric certificates are `ZMod` congruences + `decide`, fully covered by mathlib | (T26, T34, T60) |
| `NumberTheory/NumberField/Internal/PrimeDivisibility.lean` | distinct primes coprime after `Int` cast (one lemma) | irrelevant — mathlib | — |
| `NumberTheory/NumberField/Internal/QuadraticIntegralBasis.lean` | `{1, x}` ℚ-basis of a quadratic field with integral vectors | irrelevant | — |
| `NumberTheory/ClassGroup/ElementaryTwoQuotient.lean`, `NumberField/ClassGroupElementaryTwoQuotient.lean`, `RamificationInertia/Galois.lean`, `GeometryOfNumbers/{Doubling,RankTwoDoubling}.lean` | class-group 2-torsion quotients; Galois e/f counting; lattice doubling | irrelevant | — |
| `FieldTheory/Trace.lean` | Tr(x) = 0 for x² ∈ ℚ, x ∉ ℚ; discriminant of {1, x} | irrelevant — our Sinnott trace (`traceClass`) is opaque interface data by design | (T13) |
| `FieldTheory/{IntermediateField/Card,IntermediateField/Quadratic,SquareClassGroup}.lean` | subfield counting, square-class groups | irrelevant | — |
| `AlgebraicGeometry/AbelianVariety/Basic.lean` | abelian variety = proper geometrically integral group scheme; commutativity via rigidity; base change | irrelevant — scheme-theoretic; our project deliberately never formalizes EC geometry (interface-only). Not even consult-later: no overlap with any board task | — |
| `AlgebraicGeometry/WeilDivisor/*` (28 files) | Weil divisors, Abel–Jacobi map to the class group, degree splitting (Jacobian-challenge Layer work) | irrelevant — same reason | — |
| `RingTheory/Polynomial/Hermite/Derivative.lean` | Hermite polynomial lowering identity, three-term recurrence — the **entire** `RingTheory/` directory | irrelevant | — |
| `Data/Setoid/Basic.lean`, `Data/Sym/Basic.lean` | one-lemma setoid-quotient / symmetric-power helpers | irrelevant — not module quotients; T23/T27 need `Submodule`/`Ideal.Quotient` API, which is mathlib's | (T23) |
| `Algebra/Group/ZMultiples.lean` | `ℤ ≃+ zmultiples p` for non-torsion p | irrelevant | — |
| `Algebra/Squarefree.lean`, `Algebra/Polynomial/{CardBoundedCoeff,CardRootSetUnion}.lean` | squarefree non-unit not a square; polynomial root counting | irrelevant | — |

Directory-level triage of everything else (no plausible task mapping, so not
individually fetched):

| Directory (file count) | Topic | Verdict |
|---|---|---|
| `Algebra/AlgebraicGroup` (34), `Algebra/{Bialgebra,Coalgebra,HopfAlgebra}` (~40), `Algebra/Category` (1) | Hopf-algebraic affine group schemes, comodules | irrelevant |
| `Algebra/{Group,GroupAction}` (10) | quotient-group / group-action lemmas | irrelevant |
| `AlgebraicTopology` (26), `Topology` (12), `LowDimTopology` (12), `KnotTheory/Grid` (28) | covering spaces, isotopy, plumbing, grid homology | irrelevant |
| `Analysis` (~90) | contour integration, PDEs, semigroups, positive-definite kernels, Hermite functions | irrelevant |
| `Geometry` (~35), `LinearAlgebra` (3) | symplectic/J-holomorphic, diffeomorphism groups, complex finrank | irrelevant |
| `MeasureTheory` (7), `Probability` (~40) | Prokhorov, de Finetti, martingales | irrelevant |

## Top reusable items

Asked for the top 3; honestly there is **one**, plus two process observations:

1. **`scripts/Axioms.lean` → T02** (consult-later, the only concrete item). Three ideas
   worth stealing when writing our `AxiomAudit.lean` + `scripts/audit.sh`:
   (a) audit the *compiled environment*, not source text — catches `sorryAx`,
   `Lean.ofReduceBool` (`native_decide`), and axioms smuggled through imports, which
   grep cannot; (b) their documented soundness caveat: with `trustLevel := 1024` the
   audit must run *after* a kernel-checking `lake build`, and is not a defense against
   stale/forged `.olean`s — our `audit.sh` should order steps the same way and say so;
   (c) enumerate the audited decls explicitly rather than trusting a root import (their
   version enumerates the source tree; ours should hard-code the 5 headline decls + 2
   toys per T42). Their memoized shared-cache traversal is a performance trick we do
   **not** need at our scale — stock `Lean.collectAxioms` on 7 declarations is fine.
2. **(Process, no action)** Their CI gate — build, then axiom audit, then linter set,
   `warningAsError` — is independent confirmation that our T02 gate design
   (build + sorry-grep + axiom whitelist) matches current best practice.
3. **(Negative result, worth recording)** Nobody in the AI-formalization ecosystem has
   public Lean for Iwasawa-adjacent material (Λ-modules, p-adic L-functions, Katz
   measures). T23's risk-register status as "highest risk, start first" is reaffirmed:
   there is no external code to fall back on beyond mathlib itself.

## Method note

Enumeration: GitHub git-trees API (`?recursive=1`, `truncated: false`, 572 blobs).
Skimmed in full or in header: 17 individual files + `lakefile.toml`,
`lake-manifest.json`, `lean-toolchain`, `AGENTS.md`, `README.md`. Repo was not cloned.
No project files touched other than this note. T04 accept criterion (explicit
reuse/no-reuse verdict per relevant file) is met by the tables above; the board asked
for this as a section of `NOTES/MathlibAudit.md` — filed as a standalone
`NOTES/TauCetiAudit.md` per PM instruction, so T03's file stays single-owner; T03's
author may link here.
