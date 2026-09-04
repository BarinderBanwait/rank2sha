import Mathlib
import FinShaRank2.Defs

/-!
# `IwasawaData p` and `SelmerData p`

The Iwasawa-theoretic and descent inputs to the proof of Theorem A (Theorem 3.8) in
*Second derivatives of p-adic L-functions and the Shafarevich–Tate group of
rank-two CM elliptic curves*.

Both structures package **classical, citable theorems** as explicit fields, per
the trust story of the formalization: the skeptical referee
checks the field *statements* against the cited literature and against the
paper's proof of Theorem A, and Lean's kernel certifies everything the
main theorems deduce from them. There are no global axioms.

## Dual-side conventions

Everything is phrased on the **Pontryagin-dual side** as finitely generated
`ℤ_[p]`- or `Λ`-modules, where mathlib is strong:

* `X = Sel_{p^∞}(E/ℚ_∞)^∨` — the compact dual of the discrete Selmer group over
  the cyclotomic ℤ_p-extension; a finitely generated `Λ = ℤ_[p]⟦T⟧`-module.
* `SelDual = Sel_{p^∞}(E/ℚ)^∨` — the dual of the discrete Selmer group over ℚ.
* `ShaDual = Ш(E/ℚ)[p^∞]^∨` — the dual of the p-divisible part of Ш.

The paper's discrete statements translate as
`corank_{ℤ_p} Sel_{p^∞}(E/ℚ) = 2 ↔ Module.finrank ℤ_[p] SelDual = 2` and
`Ш(E/ℚ)[p^∞] = 0 ↔ Subsingleton ShaDual`. **Neither translation appears in any
field type below** (no conclusion vocabulary): the fields carry
only the *inputs* the proof consumes, and the conclusions are theorems
`prop_consequence` and `cor_horizontal`
derive from them.

## Instance-field plumbing

`X` carries four scalar structures wired by a scalar tower: it is a
`Λ`-module (the Iwasawa action of `T = PowerSeries.X`) that is finitely
generated over `Λ`, and simultaneously a `ℤ_[p]`-module via restriction of
scalars along `algebraMap ℤ_[p] (Λ p)`, compatibly
(`IsScalarTower ℤ_[p] (Λ p) X`). The `ℤ_[p]`-structure is what lets us speak of
`Module.finrank ℤ_[p] X` and of the `ℤ_[p]`-linear control isomorphism. These
are declared as instance-implicit fields and re-exported as instances just
below each structure (the working pattern verified in
`Scratch/NameCheck.lean` §8). `SelDual` and `ShaDual` are finitely generated
`ℤ_[p]`-modules.

## The Γ-coinvariants term

The control isomorphism is stated against the **Γ-coinvariants**
`X_Γ = X / T·X`, realized here by the literal submodule
`Ideal.span {(PowerSeries.X : Λ p)} • (⊤ : Submodule (Λ p) X)` (the image of the
`T`-multiplication, i.e. `T·X`). The kernel lemma `selmer_dual_structure` states the same theorem
independently, against this exact term, so the two compose directly. The `ℤ_[p]`-module
structure on the quotient is inferred from the tower via
`Submodule.Quotient.module'`.

## Design notes

* `IwasawaData` is parameterized over `Lp : Λ p` (the p-adic L-function, owned by
  `AnalyticData`, `AnalyticData`) and over the Selmer-dual type `SelDual` (owned by
  `SelmerData`). This threads a *single* `SelDual` through both structures: `ClassicalInputs`
  builds `SelmerData` first and forms `IwasawaData p analytic.Lp selmer.SelDual`,
  so `control` and `mw_sha_exact` speak about the same object with no bridge.
* `control` is provided as *data* (an actual `LinearEquiv`), faithful to Mazur's
  control theorem, which produces the isomorphism, and convenient for `prop_consequence`.

Paper statements quoted below: Theorem A (Steps 3–4), Remark 3.9.
-/

open PowerSeries

namespace FinShaRank2

/-- **Iwasawa-module data at `p`** (dual side): the finitely generated
`Λ = ℤ_[p]⟦T⟧`-module `X = Sel_{p^∞}(E/ℚ_∞)^∨` together with the two structural
inputs Steps 3–4 of Theorem A (Theorem 3.8) extract from the literature and the
Mazur-control isomorphism onto the Selmer dual `SelDual`.

Parameterized over `Lp : Λ p` (the p-adic L-function, whose characteristic-ideal
role is recorded in `rubin_structure`) and over the Selmer-dual type `SelDual`
(supplied by `SelmerData`), so a single `SelDual` is shared with the descent
sequence. -/
structure IwasawaData (p : ℕ) [Fact p.Prime] (Lp : Λ p)
    (SelDual : Type) [AddCommGroup SelDual] [Module ℤ_[p] SelDual] where
  /-- `X = Sel_{p^∞}(E/ℚ_∞)^∨`, the compact Pontryagin dual of the discrete
  Selmer group over the cyclotomic ℤ_p-extension. -/
  X : Type
  /-- Additive structure on `X`. -/
  [addCommGroupX : AddCommGroup X]
  /-- The Iwasawa `Λ = ℤ_[p]⟦T⟧`-action on `X`; `T = PowerSeries.X` is the
  topological generator `γ − 1` of `Gal(ℚ_∞/ℚ)`. -/
  [moduleΛ : Module (Λ p) X]
  /-- `X` is finitely generated over `Λ` (compact dual of a cofinitely generated
  discrete module). -/
  [finiteΛ : Module.Finite (Λ p) X]
  /-- The restricted `ℤ_[p]`-action on `X` (scalars along `algebraMap ℤ_[p] Λ`),
  used to phrase ranks and the control isomorphism. -/
  [moduleℤp : Module ℤ_[p] X]
  /-- Compatibility of the `ℤ_[p]`- and `Λ`-actions on `X`. -/
  [towerℤp : IsScalarTower ℤ_[p] (Λ p) X]
  /-- `X` has no nonzero finite `Λ`-submodule.

  SOURCE: Greenberg, *Iwasawa theory for elliptic curves*, LNM **1716**
  (Springer, 1999), Prop. 4.14. The cited hypotheses — that
  `Sel_{p^∞}(E/ℚ_∞)` is `Λ`-cotorsion (established in Step 2 from
  `car_Λ(X) = (L_p) = (T²)`) and that `E(ℚ)[p] = 0` (as
  `p ∤ #E(ℚ)_tors`; equivalently Prop. 4.15(ii) applies with ramification
  index `e_{v_0} = 1 ≤ p − 2`) — are recorded here and discharged for the
  testbed curve by the surrounding data.
  PAPER: Theorem A (Theorem 3.8, `prop:consequence`) Step 3.
  STATUS: classical. -/
  no_finite_submodule : ∀ N : Submodule (Λ p) X, Finite N → N = ⊥
  /-- **Fused structure input**: a pseudo-isomorphism of `X` onto a product of
  elementary quotients `∏ᵢ Λ/(fᵢ)` whose defining product `∏ᵢ fᵢ` generates the
  characteristic ideal, together with the identification of that ideal with
  `(L_p)`.

  This composes **two citable classical theorems**:

  * the structure theorem for finitely generated `Λ`-modules — Washington,
    *Introduction to Cyclotomic Fields*, 2nd ed., GTM **83** (Springer, 1997),
    Thm. 13.12 — giving `φ : X → ∏ᵢ Λ/(fᵢ)` with finite kernel and cokernel
    (a pseudo-isomorphism), and

  * Rubin's cyclotomic main conjecture for CM elliptic curves — Rubin, *The
    "main conjectures" of Iwasawa theory for imaginary quadratic fields*,
    Invent. math. **103** (1991), no. 1, 25–68, Thm. 12.3 (via Yager's
    identification of the two-variable characteristic ideal with the Katz
    measure, restricted to the cyclotomic line) — giving
    `car_Λ(X) = (∏ᵢ fᵢ) = (L_p)`, hence `Associated (∏ᵢ fᵢ) Lp`.

  SOURCE: Washington GTM 83, Thm. 13.12, fused with Rubin, Invent. math. 103
  (1991), Thm. 12.3 (via Yager).
  PAPER: Theorem A (Theorem 3.8, `prop:consequence`) Step 2 (characteristic ideal) feeding Step 3.
  STATUS: classical. -/
  rubin_structure : ∃ (n : ℕ) (f : Fin n → Λ p)
      (φ : X →ₗ[Λ p] Π i, (Λ p) ⧸ Ideal.span {f i}),
        Finite (LinearMap.ker φ) ∧
        Finite ((Π i, (Λ p) ⧸ Ideal.span {f i}) ⧸ LinearMap.range φ) ∧
        Associated (∏ i, f i) Lp
  /-- **Mazur control, consequence form**: a `ℤ_[p]`-linear isomorphism from the
  Γ-coinvariants `X_Γ = X / T·X` onto the Selmer dual `SelDual`.

  The coinvariants are the literal quotient
  `X ⧸ (Ideal.span {T} • ⊤)` with `T = PowerSeries.X` (so `Ideal.span {T} • ⊤`
  is `T·X`); its `ℤ_[p]`-structure comes from the scalar tower.

  SOURCE: Mazur, *Rational points of abelian varieties with values in towers of
  number fields*, Invent. math. **18** (1972), 183–266; in the exact
  (dualized) form of Greenberg, LNM **1716** (1999), Thm. 1.2 and §3. The
  vanishing hypotheses making the control map an isomorphism —
  `E(ℚ_∞)[p^∞] = 0`, triviality of the `p`-parts of the Tamagawa numbers
  `c_v` (here `= 1`, as `p ∉ S`), and non-anomalicity at `p`
  (`Ẽ(𝔽_p)[p^∞] = 0`) — are recorded here and supplied by the surrounding
  data for the testbed curve.
  PAPER: Theorem A (Theorem 3.8, `prop:consequence`) Step 4 (the isomorphism `X_Γ ≅
  Sel_{p^∞}(E/ℚ)^∨`).
  STATUS: classical (consequence form). -/
  control : (X ⧸ (Ideal.span {(PowerSeries.X : Λ p)} • (⊤ : Submodule (Λ p) X)))
      ≃ₗ[ℤ_[p]] SelDual

attribute [instance] IwasawaData.addCommGroupX IwasawaData.moduleΛ IwasawaData.finiteΛ
  IwasawaData.moduleℤp IwasawaData.towerℤp

/-- **Descent (Mordell–Weil / Ш) data at `p`** (dual side): the finitely
generated `ℤ_[p]`-modules `SelDual = Sel_{p^∞}(E/ℚ)^∨` and
`ShaDual = Ш(E/ℚ)[p^∞]^∨`, together with the Pontryagin-dual of the descent
sequence.

The Kummer/descent sequence
`0 → E(ℚ)⊗ℚ_p/ℤ_p → Sel_{p^∞}(E/ℚ) → Ш(E/ℚ)[p^∞] → 0`
dualizes (Pontryagin duality is exact and contravariant) to
`0 → Ш(E/ℚ)[p^∞]^∨ → Sel_{p^∞}(E/ℚ)^∨ → (E(ℚ)⊗ℚ_p/ℤ_p)^∨ → 0`,
and `(E(ℚ)⊗ℚ_p/ℤ_p)^∨ ≅ ℤ_p^{rank E(ℚ)} = ℤ_p^2` for the testbed curve. Hence
`ShaDual` embeds as a **submodule** of `SelDual` with quotient `ℤ_p^2`. -/
structure SelmerData (p : ℕ) [Fact p.Prime] where
  /-- `SelDual = Sel_{p^∞}(E/ℚ)^∨`, dual of the discrete Selmer group over ℚ. -/
  SelDual : Type
  /-- Additive structure on `SelDual`. -/
  [addCommGroupSel : AddCommGroup SelDual]
  /-- The `ℤ_[p]`-module structure on `SelDual`. -/
  [moduleSel : Module ℤ_[p] SelDual]
  /-- `SelDual` is finitely generated over `ℤ_[p]`. -/
  [finiteSel : Module.Finite ℤ_[p] SelDual]
  /-- `ShaDual = Ш(E/ℚ)[p^∞]^∨`, dual of the p-divisible part of Ш. -/
  ShaDual : Type
  /-- Additive structure on `ShaDual`. -/
  [addCommGroupSha : AddCommGroup ShaDual]
  /-- The `ℤ_[p]`-module structure on `ShaDual`. -/
  [moduleSha : Module ℤ_[p] ShaDual]
  /-- `ShaDual` is finitely generated over `ℤ_[p]`. -/
  [finiteSha : Module.Finite ℤ_[p] ShaDual]
  /-- The inclusion `Ш^∨ ↪ Sel^∨` (dual of the surjection `Sel ↠ Ш[p^∞]`).

  SOURCE: Pontryagin dual of the descent sequence
  `0 → E(ℚ)⊗ℚ_p/ℤ_p → Sel_{p^∞}(E/ℚ) → Ш(E/ℚ)[p^∞] → 0`.
  PAPER: Theorem A (Theorem 3.8, `prop:consequence`) Step 5 (the exact sequence of coranks).
  STATUS: classical. -/
  ι : ShaDual →ₗ[ℤ_[p]] SelDual
  /-- The surjection `Sel^∨ ↠ (E(ℚ)⊗ℚ_p/ℤ_p)^∨ ≅ ℤ_p^2` (dual of the inclusion
  `E(ℚ)⊗ℚ_p/ℤ_p ↪ Sel`).

  The target `Fin 2 → ℤ_[p]` is the dual of the Mordell–Weil part. Its rank `2`
  is the **certified Mordell–Weil rank** of the testbed curve, established by
  2-descent together with saturation (`main.tex` §6); it is *not* the Selmer
  corank of the conclusion (which is `Module.finrank ℤ_[p] SelDual`, a theorem
  derived downstream, not assumed here).

  SOURCE: Pontryagin dual of the descent sequence; rank from 2-descent +
  saturation of `E(ℚ)`.
  PAPER: Theorem A (Theorem 3.8, `prop:consequence`) Step 5; `main.tex` §6 (rank-2 testbed).
  STATUS: classical (rank from certified data). -/
  π : SelDual →ₗ[ℤ_[p]] (Fin 2 → ℤ_[p])
  /-- `ι` is injective. SOURCE / PAPER / STATUS as for `ι`. -/
  ι_inj : Function.Injective ι
  /-- `π` is surjective. SOURCE / PAPER / STATUS as for `π`. -/
  π_surj : Function.Surjective π
  /-- Exactness at `Sel^∨`: `range ι = ker π`.

  SOURCE: exactness of the dualized descent sequence (Pontryagin duality is
  exact).
  PAPER: Theorem A (Theorem 3.8, `prop:consequence`) Step 5.
  STATUS: classical. -/
  mw_sha_exact : LinearMap.range ι = LinearMap.ker π

attribute [instance] SelmerData.addCommGroupSel SelmerData.moduleSel SelmerData.finiteSel
  SelmerData.addCommGroupSha SelmerData.moduleSha SelmerData.finiteSha

end FinShaRank2
