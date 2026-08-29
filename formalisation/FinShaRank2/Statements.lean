import FinShaRank2.Interface.Global

/-!
# Frozen paper statements (task T15): `HorizontalControl`, `ConjStrong`, `ConjWeak`

The formal renderings of the paper's *definitions and conjectures* for *Horizontal
rigidity for second jets of Katz p-adic L-functions, with applications to the
Tate–Shafarevich group in rank two*. These three declarations are part of the T15
**statement freeze**: their shapes are a contract (`TASK_BOARD.md` §2 conv. 7).

Faithfulness is the deliverable; each declaration is docstringed with its tex label
and the translation conventions used (dual side, junk values, the multiplicative
rendering of `v_𝔭`).

## Dual-side / valuation translations (`TASK_BOARD.md` §2)

* "`Ш(E/ℚ)[p^∞] = 0`" ⇔ `Subsingleton (…).selmer.ShaDual` (conv. 1).
* "`c̃₂(p) ∈ ℤ_p^×`" ⇔ `IsPUnit (…).c2tilde` — the p-adic unit predicate `‖·‖ = 1`
  on `ℚ_[p]` (`Defs.IsPUnit`), applied to the normalised second jet `def:c2tilde`.
* "`𝔭 ∤ δ`", i.e. `v_𝔭(ι_p δ) = 0` (`ssec:notation`), ⇔ `H.ek.v p δ = 1`. Mathlib's
  `Valuation` is multiplicative, so the paper's `v_𝔭(x) = 0` is `v x = 1` here; see
  the module docstring of `Interface/EK.lean`.

Paper labels rendered here: `def:horizontal`, `conj:strong`, `conj:weak`.
-/

open PowerSeries

namespace FinShaRank2

/-- The normalised second jet `c̃₂(p)` (`def:c2tilde`) attached to a `PrimeData`
value, built from that value's own genuine analytic data.

Unfolds to `c2tilde ((coeff 2 Lp : ℤ_[p]) : ℚ_[p]) (((α : ℤ_[p]) : ℚ_[p])⁻¹) tst`
with `Lp = D.analytic.Lp`, `α = D.analytic.α`, and `tst = D.torsSqOverTam` (the
`PrimeData` parameter). This is exactly `def:c2tilde` applied to `D`'s MTT
L-function; the double coercion `((… : ℤ_[p]) : ℚ_[p])` is mandatory (the
single-coercion form mis-elaborates — T11 gotcha, `NOTES/MathlibAudit.md`).

By `PrimeData.c2norm_tie` this equals the height-side proxy `D.height.c2norm`, so
statements phrased through this jet transfer to the height dictionary
(`prop:dictionary`) and back with a single rewrite.

TRANSLATION: `c̃₂(p)` of `def:c2tilde` on the dual/analytic side. -/
noncomputable def PrimeData.c2tilde {p : ℕ} [Fact p.Prime] {hsplit : p % 4 = 1}
    {tst : ℚ} (D : PrimeData p hsplit tst) : ℚ_[p] :=
  _root_.FinShaRank2.c2tilde ((PowerSeries.coeff 2 D.analytic.Lp : ℤ_[p]) : ℚ_[p])
    (((D.analytic.α : ℤ_[p]) : ℚ_[p])⁻¹) tst

/-- **`def:horizontal` — horizontal control.**

> *We say horizontal control holds for `E` along a set `𝒫` of primes if*
> *`Ш(E/ℚ)[p] = 0` for all but finitely many `p ∈ 𝒫`.*

Rendered as a predicate on a set of primes `P` and a per-prime triviality
predicate `shaVanishes`: the set of `p ∈ P` at which vanishing *fails* is finite.
This is "holds for all but finitely many `p ∈ P`" verbatim.

The paper's conclusion is about the `p`-torsion `Ш(E/ℚ)[p]`. On the dual side
`shaVanishes p` is supplied as `Subsingleton (…).selmer.ShaDual`, which renders
`Ш(E/ℚ)[p^∞] = 0` (conv. 1) and so is the stronger statement; substituting it
gives a stronger conclusion than `def:horizontal` asks for.

The definition is deliberately standalone and general — `def:horizontal` in the
paper precedes all interface data — so any concrete triviality predicate can be
substituted. `prop:consequence` supplies the concrete `shaVanishes` through the
Selmer-dual layer.

TRANSLATION: `𝒫 ↦ P`; "`Ш(E/ℚ)[p] = 0`" ↦ `shaVanishes p`; "all but finitely many"
↦ finiteness of the failure set. -/
def HorizontalControl (P : Set ℕ) (shaVanishes : ℕ → Prop) : Prop :=
  {p | p ∈ P ∧ ¬ shaVanishes p}.Finite

/-- **`conj:strong` — horizontal rigidity, strong form**, relative to the fixed
classical inputs `H`.

> *There exists a nonzero `δ_E ∈ ℚ̄^×` … and a finite explicit set `Σ` of primes,*
> *such that `c̃₂(p) ∈ ℤ_p` for every split `p ∉ Σ`, and `c̃₂(p) ∈ ℤ_p^×` for every*
> *split `p ∉ Σ` with `𝔭 ∤ δ_E`.*

The conjecture is an existential and is rendered as one: `δ` ranges over `H.ek.L`,
the paper's `Q̄`, and `Sig` over finite sets of primes. The paper's `Σ` is
`H.S ∪ Sig`: `H.S` is already the standing exclusion of every statement about `H`,
so the predicate quantifies over split `p ∉ H.S` with `p ∉ Sig` in addition.
`thm:reduction` witnesses the existential with `δ := H.ek.deltaE c` and
`Sig := H.ek.supp c`, which is the paper's `Σ = S_E ∪ supp(c)`.

Until R2a this predicate pinned `δ := H.deltaE` and `Σ := H.S` from the data
carried by `ClassicalInputs`, discharging the existential by fiat.

The integrality clause "`c̃₂(p) ∈ ℤ_p`" is *not* part of this predicate: by
`rmk:integrality` integrality is classical (modular-symbol integrality for
`p ∉ S`) and "the integrality assertion is therefore not its substance; the unit
assertion is". This predicate captures the unit assertion, which is what the
arithmetic consequences (`prop:consequence`) and `thm:reduction` consume.

TRANSLATION: `Σ ↦ H.S ∪ Sig`; nonzero `δ_E ↦ δ : H.ek.L` with `δ ≠ 0`;
"`𝔭 ∤ δ_E`" ↦ `H.ek.v p δ = 1` (multiplicative valuation); "`c̃₂(p) ∈ ℤ_p^×`" ↦
`IsPUnit (…).c2tilde`. -/
def ConjStrong (H : ClassicalInputs) : Prop :=
  ∃ (δ : H.ek.L) (Sig : Finset ℕ), δ ≠ 0 ∧
    ∀ (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1) (hpS : p ∉ H.S) (_ : p ∉ Sig),
      H.ek.v p δ = 1 →
        letI : Fact p.Prime := ⟨hp⟩
        IsPUnit (H.dataAt p hp hsplit hpS).c2tilde

/-- **`conj:weak` — horizontal rigidity, weak form**, relative to `H`.

> *`c̃₂(p) ∈ ℤ_p^×` for all but finitely many split primes `p` of good reduction.*

Rendered as: there is a finite exceptional set `T` such that every split prime
`p ∉ S` (good reduction is subsumed by `p ∉ S`) outside `T` has `c̃₂(p)` a p-adic
unit. This is the `∃ finite T, ∀ p ∉ T`-form of "for all but finitely many split
primes", the form `prop:consequence`'s proof consumes ("`conj:weak` supplies
`c̃₂(p) ∈ ℤ_p^×` at all but finitely many split `p`").

Weaker than `ConjStrong H` (which controls the exceptional set by `δ_E`): here the
exceptional set is merely asserted finite, with no algebraic generator.

TRANSLATION: "all but finitely many split primes" ↦ `∃ T : Finset ℕ, ∀ split p ∉ S,
p ∉ T → …`; "`c̃₂(p) ∈ ℤ_p^×`" ↦ `IsPUnit (…).c2tilde`. -/
def ConjWeak (H : ClassicalInputs) : Prop :=
  ∃ T : Finset ℕ, ∀ (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1) (_hpS : p ∉ H.S),
    p ∉ T →
      letI : Fact p.Prime := ⟨hp⟩
      IsPUnit (H.dataAt p hp hsplit _hpS).c2tilde

end FinShaRank2
