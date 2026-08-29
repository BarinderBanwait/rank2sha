# T03 — Mathlib name audit

**Date:** 2026-07-15 · **Agent:** W1-B ·
**Audited against the then-current project pin:** mathlib **v4.32.0**
(rev `81a5d257c8e410db227a6665ed08f64fea08e997`), toolchain `leanprover/lean4:v4.32.0`
(from `formal/lake-manifest.json` / `lean-toolchain`).
Phase A cross-checked on mathlib master via loogle (2026-07-15); Phase B verified every
name against the pinned checkout (`.lake/packages/mathlib`) and by compiling
[`FinShaRank2/Scratch/NameCheck.lean`](../FinShaRank2/Scratch/NameCheck.lean)
(`lake env lean FinShaRank2/Scratch/NameCheck.lean` — **0 errors**). Master and v4.32.0
agree on every audited name; the gotchas in §3 are board-sketch-vs-mathlib, not
master-vs-pin.

**Headline:** every load-bearing declaration on the T03 list **exists in v4.32.0**.
Two micro-gaps (§2), both *proved as workarounds inside NameCheck.lean* (3 lines + 2
lines), owned by T23. No unowned gaps. Risks 1–2 of the board register are lower than
budgeted (§4).

**Re-verified 2026-08-29 against mathlib v4.33.1** (rev
`0df444a360eaa60ab8c11dca51a86af692955474`, toolchain `leanprover/lean4:v4.33.1`), on
task R0b. Every name in §1 still resolves; both §2 workarounds still compile verbatim;
all eight §3 gotchas still hold. `FinShaRank2/Scratch/NameCheck.lean` compiles with 0
errors against the new pin. Three items in the tree needed edits — see §3.9–§3.11.

---

## 1. Verdict table

✓ = exists, exact name verified in the pin and exercised in NameCheck.lean.
✓(sig) = exists; signature differs from the board sketch — see note.
GAP = no direct decl; workaround in §2.

### 1.1 Power series: substitution (T10, T20 — board risk 2)

| Sought | Verdict | Found as (v4.32.0) |
|---|---|---|
| `PowerSeries.subst` | ✓ | `subst (a : MvPowerSeries τ S) (f : PowerSeries R) : MvPowerSeries τ S` — for `a : S⟦X⟧` lands in `S⟦X⟧` definitionally (`Mathlib.RingTheory.PowerSeries.Substitution`) |
| `PowerSeries.HasSubst` | ✓ | `HasSubst (a : MvPowerSeries τ S) : Prop`; σ-witness: **`HasSubst.of_constantCoeff_zero'`** (`constantCoeff a = 0 → HasSubst a`, single-var); also `.of_constantCoeff_zero` (Mv), `.X_pow`, `.monomial'`, `.add`, `.smul_X'` |
| `PowerSeries.coeff_subst` | ✓ | Mv form `(e : τ →₀ ℕ)`; **single-variable `coeff_subst'`** `(hb : HasSubst b) (f) (e : ℕ) : coeff e (f.subst b) = ∑ᶠ d, coeff d f • coeff e (b ^ d)` ← T20 workhorse; finiteness `coeff_subst_finite'` |
| subst ring laws | ✓ | `subst_add`, `subst_mul`, `subst_pow`, `subst_smul`, `substAlgHom (ha) : R⟦X⟧ →ₐ[R] _`, `coe_substAlgHom` |
| subst of/at X, constants | ✓ | `subst_X`, `X_subst`, `subst_C`, `constantCoeff_subst`, `constantCoeff_subst_eq_zero`, `map_algebraMap_eq_subst_X` |
| order under subst | ✓ | `le_order_subst`, `le_order_subst_left'`, `le_order_subst_right'` |
| compositional inverse (bonus) | ✓ | `substInvOfIsUnit`, `subst_substInvOfIsUnit_left/right`, `HasSubst.substInvOfIsUnit` — an alternative handle on σ (coeff 1 σ = −1 is a unit) |

T20 recipe for `coeff 1 (f.subst σ) = coeff 1 f * coeff 1 σ`: `coeff_subst'` +
`finsum_eq_single` (d = 0 dies by `coeff_one`; d ≥ 2 dies via `X_dvd_iff` →
`pow_dvd_pow_of_dvd` → `X_pow_dvd_iff`). Mathlib's own `coeff_subst_X_pow` proof is a
worked template for exactly this finsum computation.

### 1.2 Power series: basics, order, units, primality (T20–T23)

| Sought | Verdict | Found as |
|---|---|---|
| `PowerSeries.X_pow_dvd_iff` | ✓ | `X ^ n ∣ φ ↔ ∀ m < n, coeff m φ = 0` (`…PowerSeries.Basic`) |
| `X_dvd_iff` | ✓ | `X ∣ φ ↔ constantCoeff φ = 0` |
| unit ↔ constant-coeff unit | ✓ | `PowerSeries.isUnit_iff_constantCoeff` (any `[Ring R]`, `…PowerSeries.Inverse`); one-way `isUnit_constantCoeff` (Basic) |
| `PowerSeries.order` | ✓(sig) | `order (φ : R⟦X⟧) : ℕ∞` — **`ℕ∞`, not `PartENat`**; API: `order_eq_nat`, `order_eq_top (↔ φ=0)`, `order_X_pow`, `order_mul` (`[NoZeroDivisors]`), `X_pow_order_dvd`, `coeff_order`, `order_le` |
| `Prime (X : R⟦X⟧)` | ✓ | `PowerSeries.X_prime` (`[CommRing R] [IsDomain R]`, `…PowerSeries.NoZeroDivisors`) — **no gap**; also `IsLocalRing ℤ_[p]⟦X⟧` via `MvPowerSeries.instIsLocalRing` |
| coeff bookkeeping | ✓ | `coeff_mul` (antidiagonal), `coeff_X_pow_mul` (+ `'`), `coeff_mk`, `constantCoeff_mk`, `coeff_map`, `constantCoeff_surj` |
| `trunc` (T20 fallback) | ✓ | `trunc (n) (φ) : Polynomial R`, `coeff_trunc` — fallback available but should be unnecessary |
| Noetherian Λ | ✓ | `PowerSeries.instIsNoetherianRing` |
| ker(constantCoeff) = (X), general R | **GAP → proved** | §2 G1 |

### 1.3 Weierstrass preparation (entry points audited; main chain does not need them)

`Mathlib.RingTheory.PowerSeries.WeierstrassPreparation` +
`Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished`, over
`[CommRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]` — **all instances
resolve at A = ℤ_[p]** (NameCheck §3): `Polynomial.IsDistinguishedAt`,
`IsWeierstrassDivision(At)` (+ `_iff`), `IsWeierstrassFactorization(At)` (+ `_iff`,
`.isUnit`), `exists_isWeierstrassDivision`, `exists_isWeierstrassFactorization`,
`weierstrassDiv`/`weierstrassMod` (`/ʷ`, `%ʷ`), `weierstrassDistinguished`,
`weierstrassUnit` (+ `_mul`, `_smul`). μ = 0 enters as
`g.map (IsLocalRing.residue A) ≠ 0`.

### 1.4 p-adics (T11, T24, T26, T40)

| Sought | Verdict | Found as |
|---|---|---|
| `hensels_lemma` | ✓(sig) | root-level, `Mathlib.NumberTheory.Padics.Hensel` — **aeval-generalized**: `{R} [CommSemiring R] [Algebra R ℤ_[p]] {F : Polynomial R} {a : ℤ_[p]} (hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2) : ∃ z, F.aeval z = 0 ∧ ‖z−a‖ < ‖F.derivative.aeval a‖ ∧ … ∧ (uniqueness in the ball)`. T40: use `R := ℤ_[p]` |
| `PadicInt.isUnit_iff` | ✓ | `IsUnit z ↔ ‖z‖ = 1` (`…Padics.PadicIntegers`) |
| max ideal / units | ✓ | `PadicInt.maximalIdeal_eq_span_p`, `PadicInt.norm_lt_one_iff_dvd` |
| instance stack | ✓ | `IsDomain`, `IsDiscreteValuationRing` (**rename**: not `DiscreteValuationRing`), ⟹ `IsPrincipalIdealRing`, `IsLocalRing`, `IsAdicComplete (maximalIdeal ℤ_[p]) ℤ_[p]` — all `inferInstance` (NameCheck §4) |
| ℚ_[p] fraction field | ✓ | `PadicInt.algebra : Algebra ℤ_[p] ℚ_[p]`, `PadicInt.isFractionRing` |
| digit certificates | ✓ | **`PadicInt.toZModPow (n) : ℤ_[p] →+* ZMod (p^n)`**, `ker_toZModPow = span {↑p^n}`; mod-p: `toZMod`, `ker_toZMod = maximalIdeal` (`…Padics.RingHoms`). Recommended certificate shape for T14: `toZModPow k (coeff 2 Lp) = (digits : ZMod (p^k))` |
| `padicValRat` | ✓ | `padicValRat (p : ℕ) (q : ℚ) : ℤ` (`…Padics.PadicVal.Basic`) |
| `GaussianInt` | ✓ | `abbrev GaussianInt := Zsqrtd (-1)` (`…Zsqrtd.GaussianInt`); `.re`, `.im : ℤ`; norm is `Zsqrtd.norm : ℤ` |
| `Nat.Prime.sq_add_sq` | ✓ | `[Fact p.Prime] (hp : p % 4 ≠ 3) : ∃ a b : ℕ, a ^ 2 + b ^ 2 = p` (`Mathlib.NumberTheory.SumTwoSquares`) |
| ZMod casts (T24/T26) | ✓ | `ZMod.intCast_zmod_eq_zero_iff_dvd`, `Int.ModEq`/`[ZMOD n]` machinery |

### 1.5 Modules over PIDs, rank, structure (T12, T23, T27)

| Sought | Verdict | Found as |
|---|---|---|
| `Submodule.basisOfPid` | ✓(sig) | `(b : Module.Basis ι R M) (N : Submodule R M) : (n : ℕ) × Module.Basis (Fin n) R N` — **`Basis` is `Module.Basis`** in this rev (`Mathlib.LinearAlgebra.FreeModule.PID`); also `basisOfPidOfLE` |
| f.g. + torsion-free ⟹ free | ✓(sig) | `Module.free_of_finite_type_torsion_free'` — now an **instance** keyed on `[Module.Finite R M] [Module.IsTorsionFree R M]`; constructor `Module.IsTorsionFree.of_smul_eq_zero` |
| PID structure theorem | ✓ | `Module.equiv_free_prod_directSum` (`Mathlib.Algebra.Module.PID`) — available but T23 plan avoids it |
| surjective endo ⟹ injective | ✓ | `OrzechProperty.injective_of_surjective_endomorphism` (CommRing ⟹ OrzechProperty); `IsNoetherian.injective_of_surjective_endomorphism` — **T27 preferred route** |
| finrank additivity | ✓ | `Submodule.finrank_quotient_add_finrank` (RankNullity.lean:248) needs `[HasRankNullity R] [StrongRankCondition R] [Module.Finite R M]`; **`IsDomain.hasRankNullity`** + `commRing_strongRankCondition` ⟹ works **directly over ℤ_[p]** (NameCheck §6 example compiles) — base change not load-bearing |
| finrank via ℚ_[p] base change | ✓ | `Module.finrank_baseChange : finrank R (R ⊗[S] M') = finrank S M'` (`[Module.Free S M']`); NameCheck §6 proves `finrank ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] (Fin 2 → ℤ_[p])) = 2`; field rank-nullity `LinearMap.finrank_range_add_finrank_ker` |
| `finrank_pi` / `finrank_fin_fun` | ✓(sig) | `Module.finrank_pi`, `Module.finrank_fin_fun` — **`R` is explicit**: write `Module.finrank_fin_fun ℤ_[p]` |
| quotient API Λ ⧸ span {f} | ✓ | `Ideal.Quotient.mk/lift` (note new `[I.IsTwoSided]` instance arg — automatic in comm rings), `Ideal.mem_span_singleton (x ∈ span {y} ↔ y ∣ x)`, `Ideal.quotEquivOfEq`, `RingHom.quotientKerEquivOfSurjective`, `Submodule.liftQ/mapQ`; Λ-module structure on `Λ ⧸ span {f}` is found by TC inference (NameCheck §7) |
| maps into Pi of quotients | ✓ | `LinearMap.pi`, `LinearMap.proj`, `LinearMap.ker_pi`; **the fused `rubin_structure` field type elaborates verbatim** (NameCheck §7 — key de-risk for T12 ↔ T23 composition) |
| `Module.Finite` plumbing | ✓ | `Module.Finite.pi` (+ `pi_iff`, `of_pi`), `Module.Finite.quotient`, `Module.Finite.of_submodule_quotient`, and the **T-coinvariants instance** `Module.Finite (R ⧸ I) (M ⧸ I • ⊤)` (`Mathlib.Algebra.Module.Torsion.Basic`; anonymous name — use `inferInstance`) |
| `Associated` API | ✓ | `Associated.isUnit_iff`, `associated_one_iff_isUnit`, `associated_mul_unit_left/right` (+ `_iff` variants), `associated_of_dvd_dvd`, `isUnit_of_associated_mul`, `Irreducible.dvd_iff`, `Prime.dvd_of_dvd_pow` |
| Λ ⧸ (X) ≃ ℤ_[p] | **GAP → proved** | §2 G2 |

### 1.6 Towers, residue fields, local homs, audit tooling

| Sought | Verdict | Found as |
|---|---|---|
| `Algebra ℤ_[p] (Λ p)` | ✓ | anonymous instance `Algebra R (MvPowerSeries σ A)` (`…MvPowerSeries.Basic:774`) — resolves for `ℤ_[p]⟦X⟧` (NameCheck §8); `algebraMap = C ∘ algebraMap`; `PowerSeries.C : R →+* R⟦X⟧` (R implicit) |
| `IsScalarTower ℤ_[p] Λ X` | ✓ | standard class; `IsScalarTower ℤ_[p] Λ Λ` is found by inference; T12 carries the instance fields for abstract `X` (NameCheck §8 shape compiles) |
| `IsLocalRing.ResidueField` / `residue` | ✓ | `ResidueField R := R ⧸ maximalIdeal R`, `residue (R) : R →+* ResidueField R` (`Mathlib.RingTheory.LocalRing.ResidueField.Defs`). **Renames**: `IsLocalRing` (not `LocalRing`), `IsLocalHom` (not `IsLocalRingHom`) |
| unit transfer (T22) | ✓ | `isUnit_map_iff (f) [IsLocalHom f] : IsUnit (f a) ↔ IsUnit a` + `PowerSeries.coeff_map`; T13 should make `IsLocalHom (algebraMap ℤ_[p] W)` derivable (e.g. from `maxIdeal_eq_p`) or carry it |
| `Lean.collectAxioms` | ✓ | `Lean.collectAxioms {m} [Monad m] [MonadEnv m] (constName : Name) : m (Array Name)` — NameCheck §12 has a compiling `#eval show CommandElabM Unit` template; on `PowerSeries.X_prime` it prints exactly `[propext, Classical.choice, Quot.sound]` — direct blueprint for T02's `AxiomAudit.lean` |

---

## 2. Gaps and workarounds (both PROVED in NameCheck.lean §11)

**G1 — `RingHom.ker (constantCoeff : R⟦X⟧ →+* R) = Ideal.span {X}` for general R.**
Mathlib has only the field case (`PowerSeries.ker_coeff_eq_max_ideal`, stated against
`maximalIdeal k⟦X⟧`). Workaround, compiles against the pin:
```lean
ext f; simp [RingHom.mem_ker, Ideal.mem_span_singleton, X_dvd_iff]
```
**Owner: T23 (internal split (a));** also handy for T10.

**G2 — `Λ ⧸ Ideal.span {X} ≃+* ℤ_[p]`.**
Assemble exactly like mathlib's own field-case `PowerSeries.residueFieldOfPowerSeries`:
```lean
(Ideal.quotEquivOfEq G1.symm).trans
  (RingHom.quotientKerEquivOfSurjective constantCoeff_surj)
```
Compiles against the pin (NameCheck `NameCheck.quotSpanXEquiv`). The ℤ_[p]-**linear**
upgrade T23(c) needs is a small extra step (`AlgEquiv.ofRingEquiv` over ℤ_[p], or
`Submodule.liftQ` directly). **Owner: T23 (internal split (a)).**

No other gaps. No fallback-ladder invocation needed on current evidence.

---

## 3. Gotchas: board sketches vs actual API

Items 1–8 record board sketches against the v4.32.0 API. The board (§5 task specs) was
drafted against older conventions. Master (2026-07-15), the old pin v4.32.0 and the
current pin v4.33.1 **agree** on all eight; it is the *board text* that needs adapting
when tasks are implemented. Items 9–11 are v4.33.1 changes, recorded on task R0b.

1. **`PowerSeries.coeff` / `constantCoeff` ring argument is implicit.** Board writes
   `PowerSeries.coeff ℤ_[p] n f` (T10, T12) — in v4.32.0 write `PowerSeries.coeff n f`
   (or `coeff (R := ℤ_[p]) n`). Same for `constantCoeff`.
2. **`Basis` → `Module.Basis`** (affects T23's explicit bases).
3. **`PowerSeries.order : ℕ∞`** (`WithTop ℕ`), not `PartENat` (T21 corollaries: use
   `Nat.cast` / `ENat` lemmas).
4. **`DiscreteValuationRing` → `IsDiscreteValuationRing`**, **`LocalRing` →
   `IsLocalRing`**, **`IsLocalRingHom` → `IsLocalHom`** (T13 `KatzData` fields
   `IsLocalRing W`, `IsLocalRing.ResidueField W` are the correct modern spellings —
   board already uses them).
5. **`hensels_lemma` is aeval-based** with `[Algebra R ℤ_[p]]` (T40: instantiate
   `R := ℤ_[p]`, `aeval` collapses to `eval` via `Polynomial.aeval_def`/`eval` lemmas).
6. **`Module.finrank_fin_fun`/`finrank_pi` take `R` explicitly.**
7. **`Ideal.Quotient.mk I` carries `[I.IsTwoSided]`** — silent/automatic in
   commutative rings; only visible if stating things for noncomm generality (we don't).
8. **`Module.free_of_finite_type_torsion_free'` is an instance** keyed on
   `[Module.IsTorsionFree R M]` — for T23(d), provide `Module.IsTorsionFree ℤ_[p] X`
   (e.g. via `of_smul_eq_zero` from the injection into `Fin 2 → ℤ_[p]`), then
   `Module.Free` is inferred.
9. **`Prime.not_unit` → `Prime.not_isUnit`** (v4.33.1;
   `Mathlib/Algebra/Prime/Defs.lean`, `@[deprecated (since := "2026-08-02")] alias`).
   Statement unchanged. Fixed at `Kernel/LambdaModule.lean:72`.
10. **`setOf` → `Set.ofPred`, so `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`** (v4.33.1;
    `Mathlib/Data/Set/Operations.lean:82`, `@[deprecated (since := "2026-07-09")]
    alias`). Statement unchanged: `(x ∈ {y | p y}) = p x`, still `@[simp]`. Fixed at
    `Kernel/TsqUnit.lean:130` and `Toy/ShaTrivial.lean:94`. The `{n | …}` set-builder
    notation itself is unaffected.
11. **New linter `linter.style.haveILetI`** (`Mathlib/Tactic/Linter/HaveILetI.lean`,
    mathlib #41657; absent at v4.32.0, `defValue := true`). It flags `haveI`/`letI` in a
    proof of a `Prop` and suggests `have`/`let`. Warning only. Thirteen sites in the tree
    emit it — `Kernel/LambdaModule.lean` (151, 153, 155, 174, 175, 177),
    `Main/Reduction.lean` (122, 147, 191), `Toy/Iwasawa.lean` (102, 128),
    `Toy/ShaIwasawa.lean` (286, 323), `Toy/ShaTrivial.lean` (130, 179). Left as they
    are: those files are on the R2a/R2b rewrite list.

Nothing else in the tree needed a change. The v4.32.0 → v4.33.1 bump produced no
compilation errors: the first `lake build` after repinning was green.

## 4. Risk read-out for Phase 2 kernel tasks

- **T20 (board risk 2 — subst friction): LOW.** Single-variable API is complete
  (`coeff_subst'`, `coeff_subst_finite'`, `constantCoeff_subst`); NameCheck compiles the
  exact coefficient formula at Λ. `finsum` (`∑ᶠ`) is the only mild novelty; mathlib's
  `coeff_subst_X_pow` proof is a copy-paste-adaptable template. `trunc` fallback exists
  but should not be needed. **No board note / fallback anticipated.**
- **T21: LOW.** `X_pow_dvd_iff` + `coeff_X_pow_mul` + `isUnit_iff_constantCoeff`;
  order corollaries via `order_eq_nat` (mind ℕ∞).
- **T22: LOW.** `coeff_mul` + `coeff_map` + `isUnit_map_iff [IsLocalHom]`.
- **T23 (board risk 1): reduced to MEDIUM-LOW on the API axis.** Every ingredient
  verified: `X_prime`, G1/G2 (proved), `Module.Finite.pi/quotient`, coinvariants
  instance, `basisOfPid` / torsion-free-⟹-free instance, rank-nullity **directly over
  ℤ_[p]** (`IsDomain.hasRankNullity`), full Associated/Prime kit for the `∏ fᵢ ~ X²`
  case split, and the fused `rubin_structure` type elaborates verbatim. Residual risk
  is genuine proof-engineering (case split up to units, matrix-of-action argument),
  not API archaeology.
- **T27: LOW.** Preferred: Orzech route (`injective_of_surjective_endomorphism`) —
  no rank theory. Rank additivity over ℤ_[p] and ℚ_[p]-base-change both compile as
  alternates (NameCheck §6).
- **T24/T26: LOW.** `toZModPow`/`ker_toZModPow` + `maximalIdeal_eq_span_p` +
  `norm_lt_one_iff_dvd` + `isUnit_iff` connect digit certificates to units.
- **T02: LOW.** `collectAxioms` template compiles and prints exactly the whitelist.

## 5. T04 — TauCeti consult audit

Delivered separately by agent W1-C in [`NOTES/TauCetiAudit.md`](TauCetiAudit.md)
(verdict: consult-only upheld; no reusable mathematics).
