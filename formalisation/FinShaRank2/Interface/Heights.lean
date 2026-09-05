import Mathlib
import FinShaRank2.Defs

/-!
# Height interface: `HeightData p`

The per-prime height layer of the assumption surface for
*Second derivatives of p-adic L-functions and the Shafarevich–Tate group of
rank-two CM elliptic curves*.

`HeightData p` packages the **leading-term / p-adic BSD** side of the paper's
normalisation dictionary (Proposition 4.2, (7)): the normalised
cyclotomic p-adic regulator `Reg_γ`, the nondegeneracy predicate for the
cyclotomic p-adic height pairing, and the Schneider/Perrin-Riou leading-term
theorem (packaged as Stein–Wuthrich Thm 6.1) in the two consequence forms the
proof of Proposition 4.2 extracts.

## Epistemic placement

Every field carries a `SOURCE`/`PAPER`/`STATUS` docstring. The two `spr_*`
fields are the **single sanctioned exception** to the conclusion-vocabulary
ban: the cited theorem of Schneider and Perrin-Riou
*genuinely has the shape of an iff* between the leading-coefficient unit
condition and the conjunction (height nondegenerate ∧ `v_p(Reg_γ) = 0` ∧ the
Ш-order factor a unit), so `spr_nondeg` is allowed to state that iff. It is
phrased over `HeightData`'s **own data proxies** (`c2norm`, `shaOrd`), never
over `IsUnit (coeff 2 Lp)` or `Subsingleton ShaDual`; the `ToySha`
anti-vacuity tripwire therefore stays constructible — a non-unit
`c2norm` paired with a non-unit `shaOrd` satisfies both `spr_*` fields.

## Contract for `ClassicalInputs` (`PrimeData`) and `prop_dictionary` (Proposition 4.2)

`HeightData` is a **standalone** per-prime layer (over `(p : ℕ) [Fact p.Prime]`
only; it does not take `AnalyticData`/`SelmerData`). It therefore carries two
`ℚ_[p]` proxies which `PrimeData` (`ClassicalInputs`) ties to the other layers by
data-equations (a data-equation, not a bare proposition):

* `c2norm` — the normalised second jet `c̃₂(p)`; `ClassicalInputs` imposes
  `c2norm = c2tilde (coeff 2 Lp : ℚ_[p]) alphaInv torsSqOverTam`.
* `shaOrd` — the `#Ш(E/ℚ)[p^∞]` factor of (7), cast to `ℚ_[p]`; `ClassicalInputs`
  imposes `IsPUnit shaOrd ↔ Subsingleton SelmerData.ShaDual` (a p-power is a
  p-adic unit iff it is `1`).

Paper statements quoted below: Proposition 4.2, (7), Lemma 3.5.
-/

namespace FinShaRank2

/-- **Height data at a split prime `p`** (paper Proposition 4.2,
(7)).

Bundles the height / p-adic-BSD side of the normalisation dictionary: the
normalised cyclotomic p-adic regulator of the fixed rank-2 Mordell–Weil basis,
the nondegeneracy predicate of the cyclotomic p-adic height pairing, and the
Schneider/Perrin-Riou leading-term theorem (Stein–Wuthrich Thm 6.1) in the
consequence forms the proof of Proposition 4.2 extracts.

The two `ℚ_[p]` proxies `c2norm`, `shaOrd` decouple this layer from
`AnalyticData`/`SelmerData`; `PrimeData` (`ClassicalInputs`) ties them by data-equations
(see the module docstring). -/
structure HeightData (p : ℕ) [Fact p.Prime] where
  /-- The **normalised cyclotomic p-adic regulator** `Reg_γ(E/ℚ)` of the fixed
  rank-2 Mordell–Weil basis `{P₁, P₂}`, as it enters (7).

  SOURCE: Mazur–Stein–Tate cyclotomic p-adic heights via the p-adic sigma
  function [B. Mazur, W. Stein and J. Tate, *Computation of p-adic heights and
  log convergence*, Doc. Math. (2006), Extra Vol.: John H. Coates' Sixtieth
  Birthday, 577–614].
  PAPER: Proposition 4.2 (`prop:dictionary`)(2), (7) (`eq:padicbsd`) (the factor
  `Reg_p/log_p(1+p)²`).
  STATUS: data. -/
  Reg_γ : ℚ_[p]
  /-- **Nondegeneracy** of the cyclotomic p-adic height pairing on `E(ℚ)`
  (opaque predicate — no internal structure is exposed to the kernel).

  SOURCE: Schneider [P. Schneider, *p-adic height pairings II*, Invent. Math. 79
  (1985), no. 2, 329–374]; Perrin-Riou [B. Perrin-Riou, *Théorie d'Iwasawa et
  hauteurs p-adiques*, Invent. Math. 109 (1992), no. 1, 137–185].
  PAPER: Proposition 4.2 (`prop:dictionary`)(2) ("the cyclotomic p-adic height pairing on `E(ℚ)`
  is nondegenerate").
  STATUS: opaque assumption. -/
  heightNondeg : Prop
  /-- Proxy for the **`#Ш(E/ℚ)[p^∞]` order factor** of (7), realised
  in `ℚ_[p]` (the group order — a power of `p` — cast to `ℚ_[p]`).

  Used only to phrase the leading-term consequence forms without referencing
  `SelmerData.ShaDual`; `PrimeData` (`ClassicalInputs`) imposes
  `IsPUnit shaOrd ↔ Subsingleton ShaDual` (a data-equation, not a bare proposition).
  SOURCE: (7) (`eq:padicbsd`) (`#Ш(E/ℚ)[p^∞]` factor).
  PAPER: Proposition 4.2 (`prop:dictionary`)(2), (7) (`eq:padicbsd`).
  STATUS: data (proxy; tied downstream). -/
  shaOrd : ℚ_[p]
  /-- Proxy for the **normalised second jet `c̃₂(p)`** predicted by the height
  side of (7).

  `PrimeData` (`ClassicalInputs`) imposes `c2norm = c2tilde (coeff 2 Lp) alphaInv
  torsSqOverTam` (a data-equation, not a bare proposition), so the dictionary about the analytic jet
  follows from the dictionary about this proxy.
  SOURCE: (7) (`eq:padicbsd`) (the height-side prediction of `c₂(p)`).
  PAPER: Definition 3.2 (`def:c2tilde`), Proposition 4.2 (`prop:dictionary`)(1).
  STATUS: data (proxy; tied downstream). -/
  c2norm : ℚ_[p]
  /-- **Integrality of the regulator**: `‖Reg_γ‖ ≤ 1`, i.e. `v_p(Reg_γ) ≥ 0`.

  Extracted in the proof of Proposition 4.2 from integrality of the p-adic
  sigma function: for `P ∈ E°(ℚ)`, `σ_p(P)/d(P) ∈ ℤ_p^×`, so `v_p(h(P)) ≥ 1`,
  whence `v_p(Reg_p) ≥ 2` and `Reg_γ ∈ ℤ_p`. This field asserts only the
  inequality, not the exact unit constant.
  SOURCE: Mazur–Stein–Tate sigma-function integrality [MST, Doc. Math. (2006),
  577–614].
  PAPER: Proposition 4.2 (`prop:dictionary`) proof ("`Reg_γ ∈ ℤ_p`").
  STATUS: consequence-form (of the classical integrality). -/
  reg_integral : ‖Reg_γ‖ ≤ 1
  /-- **Integrality of the Ш-order factor**: `‖shaOrd‖ ≤ 1`, i.e.
  `v_p(shaOrd) ≥ 0` — automatic because `#Ш(E/ℚ)[p^∞]` is a positive integer.

  Paired with `reg_integral` this supplies the two nonnegative summands of the
  valuation split `v_p(c̃₂) = v_p(Reg_γ) + v_p(#Ш[p^∞])` that `prop_dictionary` collapses.
  SOURCE: `#Ш(E/ℚ)[p^∞]` is a positive integer (a power of `p`).
  PAPER: (7) (`eq:padicbsd`).
  STATUS: consequence-form (of the classical integrality). -/
  sha_integral : ‖shaOrd‖ ≤ 1
  /-- **Leading-coefficient identity** ((7)), in the valuation form the
  proof of Proposition 4.2 extracts: `‖c2norm‖ = ‖Reg_γ‖ * ‖shaOrd‖`.

  This is the norm avatar of `c₂(p) = (1-α_p⁻¹)² · Reg_p/log_p(1+p)² ·
  #Ш(E/ℚ)[p^∞]` "up to a p-adic unit"; taking `‖·‖` makes the unit factor and
  the interpolation factor `(1-α_p⁻¹)²` (a unit at non-anomalous `p`) exact,
  realising `v_p(c̃₂) = v_p(Reg_γ) + v_p(#Ш[p^∞])`.
  SOURCE: leading-term theorem of Schneider (Thms 2, 2') and Perrin-Riou
  (§§3.4.2–3.4.3), packaged as Stein–Wuthrich Thm 6.1 [W. Stein and C. Wuthrich,
  *Algorithms for the arithmetic of elliptic curves using Iwasawa theory*, Math.
  Comp. 82 (2013), no. 283, 1757–1792]. Stein–Wuthrich exclude CM curves from
  their §3 onward; the paper cites Thm 6.1 for the normalisation only, the
  underlying Schneider / Perrin-Riou theorems applying to CM (main.tex,
  Proposition 4.2 proof).
  PAPER: (7) (`eq:padicbsd`), Proposition 4.2 (`prop:dictionary`) proof.
  STATUS: consequence-form. -/
  spr_padicBSD : ‖c2norm‖ = ‖Reg_γ‖ * ‖shaOrd‖
  /-- **Leading-term dictionary** (the order-equality / nondegeneracy clause of
  Stein–Wuthrich Thm 6.1), specialised to the second-jet situation:
  `IsPUnit c2norm ↔ (heightNondeg ∧ IsPUnit Reg_γ ∧ IsPUnit shaOrd)`.

  Mirrors Proposition 4.2 exactly: the normalised jet is a p-adic unit iff the
  height pairing is nondegenerate, `v_p(Reg_γ) = 0`, and the Ш-order factor is a
  unit. This is the theorem's equality clause `ord_{T=0} char(X) =
  corank Sel_{p^∞} ⟺ (Ш[p^∞] finite ∧ pairing nondegenerate)` read through the
  leading-coefficient formula.

  Exception to the conclusion-vocabulary ban: this is the **only** place a field states
  an iff with conclusion-adjacent vocabulary, permitted because the cited
  theorem genuinely has this shape. Faithfulness is preserved and `ToySha`
  stays constructible because the iff is over the proxies `c2norm`, `shaOrd`,
  not over `IsUnit (coeff 2 Lp)` or `Subsingleton ShaDual`.
  SOURCE: Schneider (Thms 2, 2'), Perrin-Riou (§§3.4.2–3.4.3), packaged as
  Stein–Wuthrich Thm 6.1 [Math. Comp. 82 (2013), 1757–1792] (CM caveat as in
  `spr_padicBSD`).
  PAPER: Proposition 4.2 (`prop:dictionary`) (the stated equivalence (1) ⟺ (2)).
  STATUS: consequence-form (iff; convention-4 sanctioned exception). -/
  spr_nondeg : IsPUnit c2norm ↔ (heightNondeg ∧ IsPUnit Reg_γ ∧ IsPUnit shaOrd)

end FinShaRank2
