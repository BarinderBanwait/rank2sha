import Mathlib
import FinShaRank2.Defs
import FinShaRank2.Interface.Analytic
import FinShaRank2.Interface.Iwasawa
import FinShaRank2.Interface.Heights
import FinShaRank2.Interface.EK
import FinShaRank2.Interface.Katz

/-!
# Global aggregation: `PrimeData p` and `ClassicalInputs` (task T14)

The top of the assumption surface for *Horizontal rigidity for second jets of
Katz p-adic L-functions, with applications to the Tate–Shafarevich group in rank
two*.

`PrimeData` collects the four per-prime interface layers built in T11–T13 into a
single per-prime bundle and welds them together with the **definitional
tie-equations** the individual layers deliberately left open (so that each layer
could be authored standalone). `ClassicalInputs` then quantifies `PrimeData` over
every split prime outside the excluded set `eq:Sexc`, together with the global
Eisenstein–Kronecker package `ek` and the rational datum `(#tors)²/∏cᵥ`.

Nothing here is a global axiom: `ClassicalInputs` is a structure consumed as a
hypothesis `H` by the main theorems (`TASK_BOARD.md` §1). The conjectural content
(`hyp:sinnott`, `conj:EK`) stays out — it lives only in `SinnottHyp`
(hypothesis-position) and in the hypothesis `H.ek.deltaE c ≠ 0` of
`thm:reduction`.

## Aggregation vs. `extends`

`PrimeData` **aggregates** the layers as fields rather than `extends`-ing them,
because the layers have heterogeneous parameter signatures: `AnalyticData` is
parameterized over `hsplit : p % 4 = 1`, `KatzData`/`IwasawaData` over the
L-function `Lp : Λ p`, and `IwasawaData` additionally over the Selmer-dual type.
Field order is load-bearing: `analytic` and `selmer` come first because the later
fields' *types* mention them —

* `iwasawa : IwasawaData p analytic.Lp selmer.SelDual` shares the single `SelDual`
  of `selmer` with the control isomorphism (T12 contract: no bridge equivalence);
* `katz : KatzData p analytic.Lp` reuses the genuine MTT `Lp` of `analytic`, so
  `comparison` relates the real `L_p` to `LKatz` with no divergent copy (T13
  contract).

## The two tie-equations

The standalone `HeightData` layer exposes two `ℚ_[p]` proxies (`c2norm`,
`shaOrd`); T14 pins them to the genuine objects:

* `c2norm_tie` : `height.c2norm = c2tilde (coeff 2 analytic.Lp) alphaInv
  torsSqOverTam`, with `alphaInv := ((α : ℤ_[p]) : ℚ_[p])⁻¹` **verbatim** per the
  T11 elaboration note; the double coercion `((… : ℤ_[p]) : ℚ_[p])` is mandatory
  (the single-coercion form mis-elaborates — T11 gotcha). This routes the height
  dictionary (`prop:dictionary`) onto the analytic jet.
* `shaOrd_tie` : `IsPUnit height.shaOrd ↔ Subsingleton selmer.ShaDual` — a p-power
  order factor is a p-adic unit iff it is `1` iff Ш`[p^∞]` vanishes. This is a
  **proxy-meaning assignment**, documented as such (`TASK_BOARD.md` T13 status
  note): it touches conclusion vocabulary (`Subsingleton ShaDual`) as the
  sanctioned T13-mandated tie, NOT as an assumed theorem. Anti-vacuity is
  preserved — a non-unit `shaOrd` paired with a nontrivial `ShaDual` still
  satisfies it (`ToySha`, task T41).

## δ_E is no longer threaded through `PrimeData`

`δ_E` used to be a `ℚ`-parameter of `PrimeData`, welded by a third tie-equation
to a `KatzData` field `deltaE_local`. Both are gone. `δ_E(c)` is now the def
`EKPackage.deltaE` computed from the global field `ek : EKPackage` and a
coefficient vector `c`, so there is nothing per-prime to weld: `thm:reduction`
reads `H.ek.deltaE c` directly and its `𝔭 ∤ δ_E(c)` side condition is the
valuation statement `H.ek.v p (H.ek.deltaE c) = 1`. The rational factor
`torsSqOverTam` is still a `PrimeData` parameter.

Paper labels quoted below: `eq:Sexc`, `def:c2tilde`, `prop:dictionary`,
`eq:padicbsd`, `def:deltaE`, `def:anomalous`, `prop:consequence`,
`thm:reduction`.
-/

open PowerSeries

namespace FinShaRank2

/-- **Per-prime data at a split prime `p`** — the four interface layers of
T11–T13 fused with the three definitional tie-equations.

Parameterized over the split hypothesis `hsplit : p % 4 = 1` (threaded into
`AnalyticData`) and over the global rational `torsSqOverTam` (threaded into
`c2norm_tie`). See the module docstring for the aggregation rationale.

SOURCE: aggregate of `AnalyticData` (T11), `SelmerData`/`IwasawaData` (T12),
`HeightData`/`KatzData` (T13); per-field citations live in those layers.
PAPER:  `prop:consequence`, `prop:dictionary`, `thm:reduction` (the per-prime
        hypotheses these theorems consume).
STATUS: interface aggregate (two welded data-equations; per-layer STATUS in the
        component structures). -/
structure PrimeData (p : ℕ) [Fact p.Prime] (hsplit : p % 4 = 1)
    (torsSqOverTam : ℚ) where
  /-- The analytic layer: the MTT p-adic L-function `Lp` and its classical facts
  (`AnalyticData`, T11). Supplies the genuine `Lp : Λ p` reused by `iwasawa` and
  `katz`.
  SOURCE: `AnalyticData` (T11). PAPER: `lem:c0c1`, `lem:noanomalous`.
  STATUS: interface (see `AnalyticData`). -/
  analytic : AnalyticData p hsplit
  /-- The descent layer: the Selmer/Ш duals and the dualized Mordell–Weil
  sequence (`SelmerData`, T12). Supplies the single `SelDual` reused by `iwasawa`.
  SOURCE: `SelmerData` (T12). PAPER: `prop:consequence` Step 5.
  STATUS: interface (see `SelmerData`). -/
  selmer : SelmerData p
  /-- The Iwasawa layer over the shared `analytic.Lp` and `selmer.SelDual`
  (`IwasawaData`, T12). Sharing `selmer.SelDual` here is the T12 contract that
  lets `control` and `mw_sha_exact` speak about one object with no bridge equiv.
  SOURCE: `IwasawaData` (T12). PAPER: `prop:consequence` Steps 3–4.
  STATUS: interface (see `IwasawaData`). -/
  iwasawa : IwasawaData p analytic.Lp selmer.SelDual
  /-- The height / p-adic-BSD layer (`HeightData`, T13). Its `ℚ_[p]` proxies
  `c2norm`, `shaOrd` are tied to the genuine objects by `c2norm_tie`, `shaOrd_tie`.
  SOURCE: `HeightData` (T13). PAPER: `prop:dictionary`, `eq:padicbsd`.
  STATUS: interface (see `HeightData`). -/
  height : HeightData p
  /-- The Katz-measure / δ_E layer over the shared `analytic.Lp` (`KatzData`,
  T13). Reusing `analytic.Lp` is the T13 contract that makes `comparison` relate
  the real MTT `L_p` to `LKatz` with no divergent copy.
  SOURCE: `KatzData` (T13). PAPER: `lem:comparison`, `prop:grading`, `def:deltaE`.
  STATUS: interface (see `KatzData`). -/
  katz : KatzData p analytic.Lp
  /-- **Tie-equation for the second-jet proxy** (T14 mandate; `def:c2tilde`,
  `prop:dictionary`(1)): the height-side proxy `c2norm` equals the normalised
  analytic jet `c̃₂(p)` built from the genuine `coeff 2 Lp`, the inverse unit root
  `alphaInv = ((α : ℤ_[p]) : ℚ_[p])⁻¹` (T11 verbatim instantiation), and the
  global rational factor `torsSqOverTam`.

  The double coercion `((coeff 2 analytic.Lp : ℤ_[p]) : ℚ_[p])` is mandatory: the
  single-coercion form mis-elaborates (T11 gotcha, `NOTES/MathlibAudit.md`). This
  routes the `HeightData` dictionary onto the analytic jet so that
  `prop:dictionary` about `c2norm` becomes a statement about `coeff 2 Lp`.
  SOURCE: `def:c2tilde` (the normalisation) tying the T13 proxy to the T11 jet.
  PAPER:  `def:c2tilde`, `prop:dictionary`(1).
  STATUS: data (definitional tie-equation). -/
  c2norm_tie : height.c2norm
      = c2tilde ((PowerSeries.coeff 2 analytic.Lp : ℤ_[p]) : ℚ_[p])
          (((analytic.α : ℤ_[p]) : ℚ_[p])⁻¹) torsSqOverTam
  /-- **Tie-equation for the Ш-order proxy** (T14 mandate; `eq:padicbsd`): the
  height-side proxy `shaOrd` is a p-adic unit exactly when the Selmer-dual Ш
  vanishes. Since `shaOrd` is the group order `#Ш(E/ℚ)[p^∞]` (a power of `p`) cast
  to `ℚ_[p]`, it is a p-adic unit iff it equals `1` iff `Ш[p^∞] = 0` iff
  `Subsingleton ShaDual`.

  This is a **proxy-meaning assignment** (`TASK_BOARD.md` T13 status note), the
  T13-sanctioned exception to the conclusion-vocabulary ban (`TASK_BOARD.md` §2
  conv. 4): it *defines* the meaning of the proxy `shaOrd`, it does not assume a
  theorem. `ToySha` (T41) stays constructible — a non-unit `shaOrd` with a
  nontrivial `ShaDual` satisfies this iff.
  SOURCE: proxy-meaning assignment tying the T13 proxy to `SelmerData.ShaDual`.
  PAPER:  `eq:padicbsd` (`#Ш(E/ℚ)[p^∞]` factor).
  STATUS: data (definitional tie-equation; T13 proxy-meaning, conv. 4 exception). -/
  shaOrd_tie : IsPUnit height.shaOrd ↔ Subsingleton selmer.ShaDual

/-- **The classical-inputs assumption surface** — the top-level hypothesis `H`
consumed by every headline theorem (`TASK_BOARD.md` §1). It quantifies the
per-prime bundle `PrimeData` over all split primes outside the excluded set,
carries the global Eisenstein–Kronecker package, pins the rational factor of the
normalisation, and records the non-anomality content of `eq:Sexc`.

No global axioms: this is an ordinary structure; the main theorems are literal
implications `theorem … (H : ClassicalInputs) … : …`. The conjectural content of
the paper is *not* here (it stays in `SinnottHyp` / the `H.ek.deltaE c ≠ 0`
hypothesis).

SOURCE: the paper's standing hypotheses (`eq:Sexc`; `#tors²/∏cᵥ = 1` for the
        testbed; the Eisenstein–Kronecker data of `def:deltaE`).
PAPER:  `eq:Sexc`, `def:deltaE`, `prop:consequence`, `thm:reduction`.
STATUS: interface aggregate. -/
structure ClassicalInputs where
  /-- The **excluded set** `S ⊆ ℕ` of `eq:Sexc`. Downstream code uses `p ∉ S`
  together with `notAnomalous` below; the five membership reasons are recorded
  here for the referee.

  A prime `p` lies in `S` iff at least one of:
  1. `S_bad`: `p ∣ 6N · ∏_v c_v · #E(ℚ)_tors · d_K` (bad-reduction / torsion /
     discriminant primes; here `N = 12544`, `∏c_v = 4`, `#tors = 2`, `d_K = -4`);
  2. `S_an`: `p` is **anomalous**, `a_p ≡ 1 (mod p)` (`def:anomalous`; for
     `K = ℚ(i)` this excludes no split prime — `lem:noanomalous`);
  3. `S_red`: the residual representation `ρ̄_{E,p}` is **reducible** (a rational
     `p`-isogeny exists — finitely many `p`, none for `p ∈ {5, 13}`);
  4. `S_cmp`: `p` lies in the finite set of `lem:comparison` (where the comparison
     constant `c_p` could fail to be a `p`-adic unit; for the testbed the period
     ratio is supported on `{2, 7}`, so this excludes no split `p`);
  5. `S_cl`: `p ∣ #Cl_𝔣(K)`, the order of the ray class group of `K` modulo the
     conductor `𝔣`.

  Only clause 2 has formal content downstream; it is carried by `notAnomalous`.
  SOURCE: `eq:Sexc` (explicit definition of `S` for the fixed curve `E`).
  PAPER:  `eq:Sexc`; `prop:consequence` (quantifies over `p ∉ S`).
  STATUS: data. -/
  S : Finset ℕ
  /-- The **Eisenstein–Kronecker package** of `def:deltaE`: the divisor `D_E`
  (`eq:DEdef`), the six-function package `𝓡_E` (`eq:jetpackage`), the valuations
  `v_𝔭`, and the support function of `hyp:sinnott`. The candidate invariant
  `δ_E(c)` is the def `EKPackage.deltaE ek c`, not a datum; its nonvanishing is
  `conj:EK`, appearing only as a hypothesis of `thm:reduction` — never asserted
  here.
  SOURCE: `EKPackage` (`Interface/EK.lean`); per-field citations live there.
  PAPER:  `def:deltaE`, `eq:DEdef`, `eq:jetpackage`, `conj:EK`, `thm:reduction`.
  STATUS: data. -/
  ek : EKPackage
  /-- The global rational factor `(#E(ℚ)_tors)² / ∏_v c_v` of `def:c2tilde`,
  pinned `= 1` for the testbed curve by `torsSqOverTam_eq`.
  SOURCE: `def:c2tilde`; testbed data `#tors = 2`, `∏c_v = 4`, so `4/4 = 1`.
  PAPER:  `def:c2tilde`, `sec:testbed`.
  STATUS: data (value pinned by `torsSqOverTam_eq`). -/
  torsSqOverTam : ℚ
  /-- **Defining equation** pinning `torsSqOverTam = 1` (`def:c2tilde`, testbed
  data `(#tors)²/∏cᵥ = 2²/4 = 1`). Kept as a separate field (data + equation, conv.
  3) so the normalisation value is a checkable datum rather than baked in.
  SOURCE: testbed arithmetic `2² / 4 = 1`. PAPER: `def:c2tilde`, `sec:testbed`.
  STATUS: data (defining equation). -/
  torsSqOverTam_eq : torsSqOverTam = 1
  /-- The **per-prime data** at every split prime `p ∉ S`. The instance
  `[Fact p.Prime]` needed by `PrimeData` is supplied explicitly as `Fact.mk hp`
  from the prime witness `hp` (`Fact` is a `Prop`, so this is defeq by proof
  irrelevance to any other `Fact p.Prime` instance). `hsplit : p % 4 = 1` and the
  membership `p ∉ S` are explicit arrows, composing with `AnalyticData`'s binder
  design (T11).
  SOURCE: aggregate of the per-prime interface layers.
  PAPER:  `prop:consequence`, `thm:reduction` (quantified over split `p ∉ S`).
  STATUS: interface aggregate. -/
  dataAt : ∀ (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1), p ∉ S →
    @PrimeData p (Fact.mk hp) hsplit torsSqOverTam
  /-- The `S_an` clause of `eq:Sexc`: no prime outside `S` is anomalous. Stated
  in the spelling of `Kernel/Anomalous.isUnit_one_sub_alphaInv_iff`, so it feeds
  that lemma with no adapter.

  This is the one membership reason of `eq:Sexc` with formal content downstream.
  Without it `p ∉ S` says nothing — `S` is opaque `Finset` data — and every
  headline theorem had to carry the curve-specific residual hypothesis
  `p = 5 → a_p = −2` in its place. `lem:noanomalous`(2), formalised as
  `Kernel/Anomalous.anomalous_iff_five`, proves this clause outright at every
  split `p ≥ 13` and reduces it at `p = 5` to `a₅ ≠ −4`, so what is assumed here
  beyond the proved lemma is a single numerical value.
  SOURCE: `eq:Sexc` (`S_an`), `def:anomalous`.
  PAPER:  `eq:Sexc`, `def:anomalous`, `lem:noanomalous`.
  STATUS: data (a clause of the definition of `S`). -/
  notAnomalous : ∀ (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1) (hpS : p ∉ S),
    letI : Fact p.Prime := ⟨hp⟩
    ¬ ((((dataAt p hp hsplit hpS).analytic.ap : ℤ) : ZMod p) = 1)

end FinShaRank2
