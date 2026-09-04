import FinShaRank2.Interface.Global

/-!
# Frozen paper statements: `HorizontalControl`, `ConjStrong`, `ConjWeak`

The formal renderings of the paper's *definitions and conjectures* for *Second
derivatives of p-adic L-functions and the Shafarevich–Tate group of rank-two CM
elliptic curves*.

Faithfulness is the deliverable; each declaration's docstring names the statement it renders
and the translation conventions used (dual side, junk values, the multiplicative
rendering of `v_𝔭`).

## Dual-side / valuation translations

* "`Ш(E/ℚ)[p^∞] = 0`" ⇔ `Subsingleton (…).selmer.ShaDual` (dual side).
* "`c̃₂(p) ∈ ℤ_p^×`" ⇔ `IsPUnit (…).c2tilde` — the p-adic unit predicate `‖·‖ = 1`
  on `ℚ_[p]` (`Defs.IsPUnit`), applied to the normalised second jet Definition 3.2.
* "`𝔭 ∤ δ`", i.e. `v_𝔭(ι_p δ) = 0` (§2.1), ⇔ `H.ek.v p δ = 1`. Mathlib's
  `Valuation` is multiplicative, so the paper's `v_𝔭(x) = 0` is `v x = 1` here; see
  the module docstring of `Interface/EK.lean`.

Paper statements rendered here: Definition 2.1, Conjecture 5.1, Conjecture 7.9; and
`ConjStrong`, the strong form of the conjecture withdrawn from the paper on 2026-09-03.
-/

open PowerSeries

namespace FinShaRank2

/-- The normalised second jet `c̃₂(p)` (Definition 3.2) attached to a `PrimeData`
value, built from that value's own genuine analytic data.

Unfolds to `c2tilde ((coeff 2 Lp : ℤ_[p]) : ℚ_[p]) (((α : ℤ_[p]) : ℚ_[p])⁻¹) tst`
with `Lp = D.analytic.Lp`, `α = D.analytic.α`, and `tst = D.torsSqOverTam` (the
`PrimeData` parameter). This is exactly Definition 3.2 applied to `D`'s MTT
L-function; the double coercion `((… : ℤ_[p]) : ℚ_[p])` is mandatory (the
single-coercion form mis-elaborates — `AnalyticData` gotcha, `NOTES/MathlibAudit.md`).

By `PrimeData.c2norm_tie` this equals the height-side proxy `D.height.c2norm`, so
statements phrased through this jet transfer to the height dictionary
(Proposition 4.2) and back with a single rewrite.

TRANSLATION: `c̃₂(p)` of Definition 3.2 on the dual/analytic side. -/
noncomputable def PrimeData.c2tilde {p : ℕ} [Fact p.Prime] {hsplit : p % 4 = 1}
    {tst : ℚ} (D : PrimeData p hsplit tst) : ℚ_[p] :=
  _root_.FinShaRank2.c2tilde ((PowerSeries.coeff 2 D.analytic.Lp : ℤ_[p]) : ℚ_[p])
    (((D.analytic.α : ℤ_[p]) : ℚ_[p])⁻¹) tst

/-- **Definition 2.1 — horizontal control.**

> *We say horizontal control holds for `E` along a set `𝒫` of primes if*
> *`Ш(E/ℚ)[p] = 0` for all but finitely many `p ∈ 𝒫`.*

Rendered as a predicate on a set of primes `P` and a per-prime triviality
predicate `shaVanishes`: the set of `p ∈ P` at which vanishing *fails* is finite.
This is "holds for all but finitely many `p ∈ P`" verbatim.

The paper's conclusion is about the `p`-torsion `Ш(E/ℚ)[p]`. On the dual side
`shaVanishes p` is supplied as `Subsingleton (…).selmer.ShaDual`, which renders
`Ш(E/ℚ)[p^∞] = 0` (dual side) and so is the stronger statement; substituting it
gives a stronger conclusion than Definition 2.1 asks for.

The definition is deliberately standalone and general — Definition 2.1 in the
paper precedes all interface data — so any concrete triviality predicate can be
substituted. Theorem A (Theorem 3.8) supplies the concrete `shaVanishes` through the
Selmer-dual layer.

TRANSLATION: `𝒫 ↦ P`; "`Ш(E/ℚ)[p] = 0`" ↦ `shaVanishes p`; "all but finitely many"
↦ finiteness of the failure set. -/
def HorizontalControl (P : Set ℕ) (shaVanishes : ℕ → Prop) : Prop :=
  {p | p ∈ P ∧ ¬ shaVanishes p}.Finite

/-- The **unit condition at a single coefficient vector** `c`:
`c̃₂(p) ∈ ℤ_p^×` at every split `p ∉ S_E ∪ supp(c)` with `𝔭 ∤ δ_E(c)`.

This is the display of Theorem C (Theorem 7.10), proved at the vector Hypothesis 7.8(i)
presents. `ConjStrong` quantifies it over every nonzero `c`: the strong form of the
conjecture, withdrawn from the paper on 2026-09-03.

TRANSLATION: `Σ ↦ H.S ∪ H.ek.supp c`, `H.S` being the standing exclusion of every
statement about `H`; "`𝔭 ∤ δ_E(c)`" ↦ `H.ek.v p (H.ek.deltaE c) = 1` (multiplicative
valuation); "`c̃₂(p) ∈ ℤ_p^×`" ↦ `IsPUnit (…).c2tilde`. -/
def ConjStrongAt (H : ClassicalInputs) (c : Fin 6 → H.ek.K) : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1) (hpS : p ∉ H.S),
    p ∉ H.ek.supp c → H.ek.v p (H.ek.deltaE c) = 1 →
      letI : Fact p.Prime := ⟨hp⟩
      IsPUnit (H.dataAt p hp hsplit hpS).c2tilde

/-- **The strong form of horizontal rigidity, withdrawn from the paper on 2026-09-03**,
relative to the fixed classical inputs `H`: kept as a definition, proved by no
declaration, rendering no statement of the paper. The withdrawn statement read:

> *Let `S_E` be the set (7), and let `δ_E(c)`, `c ∈ K⁶`, be the invariants of*
> *Definition 6.2. Then `c̃₂(p) ∈ ℤ_p` for every split `p ∉ S_E`, and for every*
> *nonzero `c ∈ K⁶`, `c̃₂(p) ∈ ℤ_p^×` for every split `p ∉ S_E ∪ supp(c)` with*
> *`𝔭 ∤ δ_E(c)`.*

The predicate is universal in `c`, matching `ConjEK`'s
quantifier pattern. The invariants are `EKPackage.deltaE` (`Interface/EK.lean`), so
what is quantified over is the package `H.ek` itself and not an unconstrained field
element.

The integrality clause "`c̃₂(p) ∈ ℤ_p`" is *not* part of this predicate: by
Remark 3.4 integrality is classical (modular-symbol integrality for `p ∉ S`), so
only the unit assertion has content. This predicate captures the unit assertion,
which is what the arithmetic consequences (Theorem A (Theorem 3.8)) and Theorem C
consume.

Theorem C (Theorem 7.10) proves `ConjStrongAt H c` at one vector, not `ConjStrong H`.

TRANSLATION: `c ∈ K⁶` ↦ `c : Fin 6 → H.ek.K`; "every nonzero `c`" ↦ `∀ c, c ≠ 0 → …`;
the per-vector assertion ↦ `ConjStrongAt`. -/
def ConjStrong (H : ClassicalInputs) : Prop :=
  ∀ c : Fin 6 → H.ek.K, c ≠ 0 → ConjStrongAt H c

/-- **Conjecture 5.1 — horizontal rigidity**, relative to `H`.

> *`c̃₂(p) ∈ ℤ_p^×` for all but finitely many split primes `p` of good reduction.*

Rendered as: there is a finite exceptional set `T` such that every split prime
`p ∉ S` (good reduction is subsumed by `p ∉ S`) outside `T` has `c̃₂(p)` a p-adic
unit. This is the `∃ finite T, ∀ p ∉ T`-form of "for all but finitely many split
primes", the form Theorem A (Theorem 3.8)'s proof consumes ("Conjecture 5.1 supplies
`c̃₂(p) ∈ ℤ_p^×` at all but finitely many split `p`").

`ConjStrong H` implies this whenever `H.S` is finite and `H.ek.deltaE c ≠ 0` for some
nonzero `c`: the exceptional set is then contained in the finite set
`H.S ∪ H.ek.supp c ∪ {p | H.ek.v p (H.ek.deltaE c) ≠ 1}`. Neither implication is
formalised here — the finiteness of the last set is not available, `H.ek.v` being an
abstract family of valuations. The converse does not follow: finiteness of the
exceptional set says nothing about which primes lie in it.

TRANSLATION: "all but finitely many split primes" ↦ `∃ T : Finset ℕ, ∀ split p ∉ S,
p ∉ T → …`; "`c̃₂(p) ∈ ℤ_p^×`" ↦ `IsPUnit (…).c2tilde`. -/
def ConjWeak (H : ClassicalInputs) : Prop :=
  ∃ T : Finset ℕ, ∀ (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1) (_hpS : p ∉ H.S),
    p ∉ T →
      letI : Fact p.Prime := ⟨hp⟩
      IsPUnit (H.dataAt p hp hsplit _hpS).c2tilde

/-- **Conjecture 7.9 — Eisenstein–Kronecker nonvanishing**, relative to `H`.

> *Let `E/ℚ` have CM by the maximal order `𝒪_K` of an imaginary quadratic field*
> *`K`, with `L(E,1) = 0`, `w(E) = +1` and `#Cl_𝔣(K) ≥ 6`, and let `δ_E(c)` be the*
> *invariants of Definition 6.2. Then `δ_E(c) ≠ 0` for every nonzero*
> *`c ∈ K⁶`.*

`δ_E(c)` is the def `EKPackage.deltaE H.ek c` (`Interface/EK.lean`), so the
conjecture is a statement about the package `H.ek` alone. The curve-level
hypotheses `L(E,1) = 0` and `w(E) = +1` and CM by the maximal order are carried by
`H` and its per-prime bundles, as everywhere else in this project, and are not
restated.

**Descope — the hypothesis `#Cl_𝔣(K) ≥ 6` is not rendered.** The paper carries it
and explains that it is forced: the equivariant functions on the torsor `D_E` form
a `K`-space of dimension `#Cl_𝔣(K)`, so with fewer classes than sections some
combination of the six sections vanishes identically on `D_E`, and `δ_E(c) = 0`
for that `c`. In this encoding `EKPackage.D` is an abstract `Finset` with no class
group and no equivariance, so the hypothesis has nothing to attach to. Dropping it
widens what `ConjEK` asserts: a package with `#D < 6` makes `ConjEK` false, and
nothing in this encoding rules such a package out. `ConjEK H` therefore renders
Conjecture 7.9 only for those `H` whose package meets the paper's hypothesis.

`ConjEK` is conjectural. It occurs in hypothesis position of
`thm_reduction_of_conjEK` and nowhere else: it is not a field of any structure and
does not appear in `prop_consequence`, `prop_dictionary` or `cor_horizontal`.

TRANSLATION: `c ∈ K⁶` ↦ `c : Fin 6 → H.ek.K`; "nonzero `c`" ↦ `c ≠ 0`;
`δ_E(c)` ↦ `H.ek.deltaE c`; `#Cl_𝔣(K) ≥ 6` ↦ not rendered (descope, above). -/
def ConjEK (H : ClassicalInputs) : Prop :=
  ∀ c : Fin 6 → H.ek.K, c ≠ 0 → H.ek.deltaE c ≠ 0

end FinShaRank2
