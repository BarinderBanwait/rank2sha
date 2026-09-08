import FinShaRank2.Interface.Global

/-!
# The normalised second jet on a per-prime bundle

`PrimeData.c2tilde` renders the paper's `c̃₂(p)` (Definition 3.2) at a
`PrimeData` value of *Second derivatives of p-adic L-functions and the
Shafarevich–Tate group of rank-two CM elliptic curves*.

Faithfulness is the deliverable; the docstring below names the statement it renders
and the translation conventions used (dual side, junk values).

## Dual-side translations

* "`Ш(E/ℚ)[p^∞] = 0`" ⇔ `Subsingleton (…).selmer.ShaDual` (dual side).
* "`c̃₂(p) ∈ ℤ_p^×`" ⇔ `IsPUnit (…).c2tilde`, the p-adic unit predicate `‖·‖ = 1`
  on `ℚ_[p]` (`Defs.IsPUnit`), applied to the normalised second jet Definition 3.2.

Paper statements rendered here: Definition 3.2.
-/

open PowerSeries

namespace FinShaRank2

/-- The normalised second jet `c̃₂(p)` (Definition 3.2) attached to a `PrimeData`
value, built from that value's own genuine analytic data.

Unfolds to `c2tilde ((coeff 2 Lp : ℤ_[p]) : ℚ_[p]) (((α : ℤ_[p]) : ℚ_[p])⁻¹) tst`
with `Lp = D.analytic.Lp`, `α = D.analytic.α`, and `tst = D.torsSqOverTam` (the
`PrimeData` parameter). This is exactly Definition 3.2 applied to `D`'s MTT
L-function; the double coercion `((… : ℤ_[p]) : ℚ_[p])` is mandatory (the
single-coercion form mis-elaborates).

By `PrimeData.c2norm_tie` this equals the height-side proxy `D.height.c2norm`, so
statements phrased through this jet transfer to the height dictionary
(Proposition 4.2) and back with a single rewrite.

TRANSLATION: `c̃₂(p)` of Definition 3.2 on the dual/analytic side. -/
noncomputable def PrimeData.c2tilde {p : ℕ} [Fact p.Prime] {hsplit : p % 4 = 1}
    {tst : ℚ} (D : PrimeData p hsplit tst) : ℚ_[p] :=
  _root_.FinShaRank2.c2tilde ((PowerSeries.coeff 2 D.analytic.Lp : ℤ_[p]) : ℚ_[p])
    (((D.analytic.α : ℤ_[p]) : ℚ_[p])⁻¹) tst

end FinShaRank2
