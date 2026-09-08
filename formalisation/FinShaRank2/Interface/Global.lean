import Mathlib
import FinShaRank2.Defs
import FinShaRank2.Interface.Analytic
import FinShaRank2.Interface.Iwasawa
import FinShaRank2.Interface.Heights
import FinShaRank2.Interface.EK
import FinShaRank2.Interface.Katz

/-!
# Global aggregation: `PrimeData p` and `ClassicalInputs`

The top of the assumption surface for *Second derivatives of p-adic L-functions
and the Shafarevich–Tate group of rank-two CM elliptic curves*.

`PrimeData` collects the four per-prime interface layers — `AnalyticData`,
`SelmerData`/`IwasawaData`, `HeightData`, `KatzData` — into a single bundle and
welds them together with the **definitional tie-equations** each layer leaves
open, so that the layers can be read one at a time. `ClassicalInputs` then quantifies
`PrimeData` over
every split prime outside the excluded set (8), together with the global
Eisenstein–Kronecker package `ek` and the rational datum `(#tors)²/∏cᵥ`.

Nothing here is a global axiom: `ClassicalInputs` is a structure consumed as a
hypothesis `H` by the main theorems. No conjectural statement is a field of it.

## Aggregation vs. `extends`

`PrimeData` **aggregates** the layers as fields rather than `extends`-ing them,
because the layers have heterogeneous parameter signatures: `AnalyticData` is
parameterized over `hsplit : p % 4 = 1`, `KatzData`/`IwasawaData` over the
L-function `Lp : Λ p`, and `IwasawaData` additionally over the Selmer-dual type.
Field order is load-bearing: `analytic` and `selmer` come first because the later
fields' *types* mention them —

* `iwasawa : IwasawaData p analytic.Lp selmer.SelDual` shares the single `SelDual`
  of `selmer` with the control isomorphism (`IwasawaData` contract: no bridge equivalence);
* `katz : KatzData p analytic.Lp` reuses the genuine MTT `Lp` of `analytic`, so
  `comparison` relates the real `L_p` to `LKatz` with no divergent copy (`KatzData`
  contract).

## The two tie-equations

The standalone `HeightData` layer exposes two `ℚ_[p]` proxies (`c2norm`,
`shaOrd`); `ClassicalInputs` pins them to the genuine objects:

* `c2norm_tie` : `height.c2norm = c2tilde (coeff 2 analytic.Lp) alphaInv
  torsSqOverTam`, with `alphaInv := ((α : ℤ_[p]) : ℚ_[p])⁻¹` **verbatim** per the
  `AnalyticData` elaboration note; the double coercion `((… : ℤ_[p]) : ℚ_[p])` is mandatory
  (the single-coercion form mis-elaborates — `AnalyticData` gotcha). This routes the height
  dictionary (Proposition 4.2) onto the analytic jet.
* `shaOrd_tie` : `IsPUnit height.shaOrd ↔ Subsingleton selmer.ShaDual` — a p-power
  order factor is a p-adic unit iff it is `1` iff Ш`[p^∞]` vanishes. This is a
  **proxy-meaning assignment**, documented as such: it touches conclusion vocabulary
  (`Subsingleton ShaDual`) as the
  sanctioned `KatzData`-mandated tie, NOT as an assumed theorem. Anti-vacuity is
  preserved — a non-unit `shaOrd` paired with a nontrivial `ShaDual` still
  satisfies it (`ToySha`).

## The Eisenstein–Kronecker package is not threaded through `PrimeData`

`ek : EKPackage` is a global field of `ClassicalInputs`, not a per-prime layer,
so there is nothing to weld: a statement about it reads `H.ek` directly. The
rational factor `torsSqOverTam` is a `PrimeData` parameter.

Paper statements quoted below: (8), Definition 3.2, Proposition 4.2,
(7), Definition 2.1, Theorem A (Theorem 3.8).
-/

open PowerSeries

namespace FinShaRank2

/-- **Per-prime data at a split prime `p`** — the four interface layers of
the four per-prime layers fused with the three definitional tie-equations.

Parameterized over the split hypothesis `hsplit : p % 4 = 1` (threaded into
`AnalyticData`) and over the global rational `torsSqOverTam` (threaded into
`c2norm_tie`). See the module docstring for the aggregation rationale.

SOURCE: aggregate of `AnalyticData` (`AnalyticData`), `SelmerData`/`IwasawaData` (`IwasawaData`),
`HeightData`/`KatzData` (`KatzData`); per-field citations live in those layers.
PAPER:  Theorem A (Theorem 3.8, `prop:consequence`), Proposition 4.2
(`prop:dictionary`) (the per-prime hypotheses these theorems consume).
STATUS: interface aggregate (two welded data-equations; per-layer STATUS in the
        component structures). -/
structure PrimeData (p : ℕ) [Fact p.Prime] (hsplit : p % 4 = 1)
    (torsSqOverTam : ℚ) where
  /-- The analytic layer: the MTT p-adic L-function `Lp` and its classical facts
  (`AnalyticData`, `AnalyticData`). Supplies the genuine `Lp : Λ p` reused by `iwasawa` and
  `katz`.
  SOURCE: `AnalyticData` (`AnalyticData`). PAPER: Lemma 3.1 (`lem:c0c1`), Lemma 2.2
  (`lem:noanomalous`).
  STATUS: interface (see `AnalyticData`). -/
  analytic : AnalyticData p hsplit
  /-- The descent layer: the Selmer/Ш duals and the dualized Mordell–Weil
  sequence (`SelmerData`, `IwasawaData`). Supplies the single `SelDual` reused by `iwasawa`.
  SOURCE: `SelmerData` (`IwasawaData`). PAPER: Theorem A (Theorem 3.8, `prop:consequence`) Step 5.
  STATUS: interface (see `SelmerData`). -/
  selmer : SelmerData p
  /-- The Iwasawa layer over the shared `analytic.Lp` and `selmer.SelDual`
  (`IwasawaData`, `IwasawaData`). Sharing `selmer.SelDual` here is the `IwasawaData` contract that
  lets `control` and `mw_sha_exact` speak about one object with no bridge equiv.
  SOURCE: `IwasawaData` (`IwasawaData`). PAPER: Theorem A (Theorem 3.8,
  `prop:consequence`) Steps 3–4.
  STATUS: interface (see `IwasawaData`). -/
  iwasawa : IwasawaData p analytic.Lp selmer.SelDual
  /-- The height / p-adic-BSD layer (`HeightData`, `KatzData`). Its `ℚ_[p]` proxies
  `c2norm`, `shaOrd` are tied to the genuine objects by `c2norm_tie`, `shaOrd_tie`.
  SOURCE: `HeightData` (`KatzData`). PAPER: Proposition 4.2 (`prop:dictionary`), (7)
  (`eq:padicbsd`).
  STATUS: interface (see `HeightData`). -/
  height : HeightData p
  /-- The Katz-measure layer over the shared `analytic.Lp` (`KatzData`,
  `KatzData`). Reusing `analytic.Lp` is the `KatzData` contract that makes `comparison` relate
  the real MTT `L_p` to `LKatz` with no divergent copy.
  SOURCE: `KatzData` (`KatzData`). PAPER: Lemma 3.5 (`lem:comparison`), Proposition 6.2
  (`prop:grading`).
  STATUS: interface (see `KatzData`). -/
  katz : KatzData p analytic.Lp
  /-- **Tie-equation for the second-jet proxy** (`ClassicalInputs` mandate; Definition 3.2,
  Proposition 4.2(1)): the height-side proxy `c2norm` equals the normalised
  analytic jet `c̃₂(p)` built from the genuine `coeff 2 Lp`, the inverse unit root
  `alphaInv = ((α : ℤ_[p]) : ℚ_[p])⁻¹` (`AnalyticData` verbatim instantiation), and the
  global rational factor `torsSqOverTam`.

  The double coercion `((coeff 2 analytic.Lp : ℤ_[p]) : ℚ_[p])` is mandatory: the
  single-coercion form mis-elaborates (`AnalyticData` gotcha, `NOTES/MathlibAudit.md`). This
  routes the `HeightData` dictionary onto the analytic jet so that
  Proposition 4.2 about `c2norm` becomes a statement about `coeff 2 Lp`.
  SOURCE: Definition 3.2 (`def:c2tilde`) (the normalisation) tying the `KatzData` proxy
  to the `AnalyticData` jet.
  PAPER:  Definition 3.2 (`def:c2tilde`), Proposition 4.2 (`prop:dictionary`)(1).
  STATUS: data (definitional tie-equation). -/
  c2norm_tie : height.c2norm
      = c2tilde ((PowerSeries.coeff 2 analytic.Lp : ℤ_[p]) : ℚ_[p])
          (((analytic.α : ℤ_[p]) : ℚ_[p])⁻¹) torsSqOverTam
  /-- **Tie-equation for the Ш-order proxy** (`ClassicalInputs` mandate; (7)): the
  height-side proxy `shaOrd` is a p-adic unit exactly when the Selmer-dual Ш
  vanishes. Since `shaOrd` is the group order `#Ш(E/ℚ)[p^∞]` (a power of `p`) cast
  to `ℚ_[p]`, it is a p-adic unit iff it equals `1` iff `Ш[p^∞] = 0` iff
  `Subsingleton ShaDual`.

  This is a **proxy-meaning assignment**, the
  `KatzData`-sanctioned exception to the conclusion-vocabulary ban: it *defines* the
  meaning of the proxy `shaOrd`, it does not assume a
  theorem. `ToySha` (`ToySha`) stays constructible — a non-unit `shaOrd` with a
  nontrivial `ShaDual` satisfies this iff.
  SOURCE: proxy-meaning assignment tying the `KatzData` proxy to `SelmerData.ShaDual`.
  PAPER:  (7) (`eq:padicbsd`) (`#Ш(E/ℚ)[p^∞]` factor).
  STATUS: data (definitional tie-equation; `KatzData` proxy-meaning, the
  conclusion-vocabulary ban exception). -/
  shaOrd_tie : IsPUnit height.shaOrd ↔ Subsingleton selmer.ShaDual

/-- **The classical-inputs assumption surface** — the top-level hypothesis `H`
consumed by every headline theorem. It quantifies the
per-prime bundle `PrimeData` over all split primes outside the excluded set,
carries the global Eisenstein–Kronecker package, pins the rational factor of the
normalisation, and records the non-anomality content of (8).

No global axioms: this is an ordinary structure; the main theorems are literal
implications `theorem … (H : ClassicalInputs) … : …`. No conjectural statement of
the paper is a field of it.

SOURCE: the paper's standing hypotheses ((8) (`eq:Sexc`); `#tors²/∏cᵥ = 1` for the
        testbed; the Eisenstein–Kronecker data of the Bannai–Kobayashi jet).
PAPER:  (8) (`eq:Sexc`), (10) (`eq:DEdef`), Definition 5.1 (`def:classsums`), Theorem A
(Theorem 3.8, `prop:consequence`).
STATUS: interface aggregate. -/
structure ClassicalInputs where
  /-- The **excluded set** `S ⊆ ℕ` of (8). Downstream code uses `p ∉ S`
  together with `notAnomalous` below; the five membership reasons are recorded
  here for the referee.

  A prime `p` lies in `S` iff at least one of:
  1. `S_bad`: `p ∣ 6N · ∏_v c_v · #E(ℚ)_tors · d_K` (bad-reduction / torsion /
     discriminant primes; here `N = 12544`, `∏c_v = 4`, `#tors = 2`, `d_K = -4`);
  2. `S_an`: `p` is **anomalous**, `a_p ≡ 1 (mod p)` (Definition 2.1; for
     `K = ℚ(i)` this excludes no split prime — Lemma 2.2);
  3. `S_red`: the residual representation `ρ̄_{E,p}` is **reducible** (a rational
     `p`-isogeny exists — finitely many `p`);
  4. `S_cmp`: `p` lies in the finite set of Lemma 3.5 (where the comparison
     constant `c_p` could fail to be a `p`-adic unit; for the testbed the period
     ratio is supported on `{2, 7}`, so this excludes no split `p`);
  5. `S_cl`: `p ∣ #Cl_𝔣(K)`, the order of the ray class group of `K` modulo the
     conductor `𝔣`.

  Only clause 2 has formal content downstream; it is carried by `notAnomalous`.
  SOURCE: (8) (`eq:Sexc`) (explicit definition of `S` for the fixed curve `E`).
  PAPER:  (8) (`eq:Sexc`); Theorem A (Theorem 3.8, `prop:consequence`) (quantifies over `p ∉ S`).
  STATUS: data. -/
  S : Finset ℕ
  /-- The **Eisenstein–Kronecker package** of the Bannai–Kobayashi jet: the divisor
  `D_E` ((10)), six class functions `r_{a,b}` (Definition 5.1), and the valuations
  `v_𝔭`. No theorem of this project reads a section value; see `Interface/EK.lean`.
  SOURCE: `EKPackage` (`Interface/EK.lean`); per-field citations live there.
  PAPER:  (10) (`eq:DEdef`), Definition 5.1 (`def:classsums`), (12) (`eq:classsums`).
  STATUS: data. -/
  ek : EKPackage
  /-- The global rational factor `(#E(ℚ)_tors)² / ∏_v c_v` of Definition 3.2,
  pinned `= 1` for the testbed curve by `torsSqOverTam_eq`.
  SOURCE: Definition 3.2 (`def:c2tilde`); testbed data `#tors = 2`, `∏c_v = 4`, so `4/4 = 1`.
  PAPER:  Definition 3.2 (`def:c2tilde`), §7.1 (`ssec:testbed`).
  STATUS: data (value pinned by `torsSqOverTam_eq`). -/
  torsSqOverTam : ℚ
  /-- **Defining equation** pinning `torsSqOverTam = 1` (Definition 3.2, testbed
  data `(#tors)²/∏cᵥ = 2²/4 = 1`). Kept as a separate field (data + equation, conv.
  3) so the normalisation value is a checkable datum rather than baked in.
  SOURCE: testbed arithmetic `2² / 4 = 1`. PAPER: Definition 3.2 (`def:c2tilde`), §7.1
  (`ssec:testbed`).
  STATUS: data (defining equation). -/
  torsSqOverTam_eq : torsSqOverTam = 1
  /-- The **per-prime data** at every split prime `p ∉ S`. The instance
  `[Fact p.Prime]` needed by `PrimeData` is supplied explicitly as `Fact.mk hp`
  from the prime witness `hp` (`Fact` is a `Prop`, so this is defeq by proof
  irrelevance to any other `Fact p.Prime` instance). `hsplit : p % 4 = 1` and the
  membership `p ∉ S` are explicit arrows, composing with `AnalyticData`'s binder
  design (`AnalyticData`).
  SOURCE: aggregate of the per-prime interface layers.
  PAPER:  Theorem A (Theorem 3.8, `prop:consequence`) (quantified over split
  `p ∉ S`).
  STATUS: interface aggregate. -/
  dataAt : ∀ (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1), p ∉ S →
    @PrimeData p (Fact.mk hp) hsplit torsSqOverTam
  /-- The `S_an` clause of (8): no prime outside `S` is anomalous. Stated
  in the spelling of `Kernel/Anomalous.isUnit_one_sub_alphaInv_iff`, so it feeds
  that lemma with no adapter.

  This is the one membership reason of (8) with formal content downstream.
  Without it `p ∉ S` says nothing — `S` is opaque `Finset` data — and every
  headline theorem had to carry the curve-specific residual hypothesis
  `p = 5 → a_p = −2` in its place. Lemma 2.2(2), formalised as
  `Kernel/Anomalous.anomalous_iff_five`, proves this clause outright at every
  split `p ≥ 13` and reduces it at `p = 5` to `a₅ ≠ −4`, so what is assumed here
  beyond the proved lemma is a single numerical value.
  SOURCE: (8) (`eq:Sexc`) (`S_an`), Definition 2.1 (`def:anomalous`).
  PAPER:  (8) (`eq:Sexc`), Definition 2.1 (`def:anomalous`), Lemma 2.2 (`lem:noanomalous`).
  STATUS: data (a clause of the definition of `S`). -/
  notAnomalous : ∀ (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1) (hpS : p ∉ S),
    letI : Fact p.Prime := ⟨hp⟩
    ¬ ((((dataAt p hp hsplit hpS).analytic.ap : ℤ) : ZMod p) = 1)

end FinShaRank2
