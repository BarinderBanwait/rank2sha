import Mathlib

/-!
# T03 — Mathlib name audit: NameCheck

Compiling witness for `NOTES/MathlibAudit.md`. Every load-bearing mathlib
declaration on the T03 list is exercised below by a `#check` (existence +
exact fully-qualified name) and, where instances or unification could bite,
by an `example` (signature really composes at our types).

Audited against the project pin: mathlib `v4.33.1`
(rev `0df444a360eaa60ab8c11dca51a86af692955474`), toolchain `leanprover/lean4:v4.33.1`.
Re-checked at that pin on 2026-08-29 (task R2d); every name below still resolves.

This file lives in `Scratch/` — NOT imported by the root module, excluded from
audit. Compile directly:
`cd formalisation && lake build FinShaRank2.Scratch.NameCheck`
-/

noncomputable section

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-! ## §1 Power series substitution (T10, T20 — board risk 2) -/

#check @PowerSeries.subst
#check @PowerSeries.HasSubst
#check @PowerSeries.HasSubst.of_constantCoeff_zero'
#check @PowerSeries.HasSubst.of_constantCoeff_zero
#check @PowerSeries.HasSubst.X_pow
#check @PowerSeries.coeff_subst          -- Mv target, e : τ →₀ ℕ
#check @PowerSeries.coeff_subst'         -- single-variable, e : ℕ  ← T20 workhorse
#check @PowerSeries.coeff_subst_finite'
#check @PowerSeries.constantCoeff_subst
#check @PowerSeries.subst_add
#check @PowerSeries.subst_mul
#check @PowerSeries.subst_pow
#check @PowerSeries.substAlgHom
#check @PowerSeries.coe_substAlgHom
#check @PowerSeries.subst_X
#check @PowerSeries.X_subst
#check @PowerSeries.le_order_subst_left'
#check @PowerSeries.substInvOfIsUnit     -- compositional inverse (bonus for σ)
#check @PowerSeries.subst_substInvOfIsUnit_left
#check @PowerSeries.map_algebraMap_eq_subst_X

-- the T10 FE-substitution σ = (1+T)⁻¹ − 1 has a legal `HasSubst` witness:
example : HasSubst (PowerSeries.mk fun n => if n = 0 then (0 : ℤ_[p]) else (-1) ^ n) :=
  HasSubst.of_constantCoeff_zero' (by simp [constantCoeff_mk])

-- subst is multiplicative at our concrete types (Algebra ℤ_[p] ℤ_[p], τ = Unit):
example (f g h : ℤ_[p]⟦X⟧) (hh : constantCoeff h = 0) :
    subst h (f * g) = subst h f * subst h g :=
  subst_mul (HasSubst.of_constantCoeff_zero' hh) f g

-- single-variable coefficient formula lands in ℤ_[p] as expected:
example (f h : ℤ_[p]⟦X⟧) (hh : constantCoeff h = 0) :
    coeff 1 (f.subst h) = ∑ᶠ d : ℕ, coeff d f • coeff 1 (h ^ d) :=
  coeff_subst' (HasSubst.of_constantCoeff_zero' hh) f 1

/-! ## §2 Power series basics, order, units, primality (T20–T22, T23a) -/

#check @PowerSeries.X_pow_dvd_iff
#check @PowerSeries.X_dvd_iff
#check @PowerSeries.isUnit_iff_constantCoeff   -- any [Ring R]
#check @PowerSeries.isUnit_constantCoeff
#check @PowerSeries.order                       -- : ℕ∞ (not PartENat)
#check @PowerSeries.order_eq_nat
#check @PowerSeries.order_eq_top
#check @PowerSeries.order_X_pow
#check @PowerSeries.order_mul                   -- [NoZeroDivisors R]
#check @PowerSeries.X_pow_order_dvd
#check @PowerSeries.coeff_order
#check @PowerSeries.coeff_mul
#check @PowerSeries.coeff_X_pow_mul
#check @PowerSeries.coeff_mk
#check @PowerSeries.constantCoeff_mk
#check @PowerSeries.coeff_map
#check @PowerSeries.constantCoeff_surj
#check @PowerSeries.trunc                       -- T20 fallback route
#check @PowerSeries.coeff_trunc
#check @PowerSeries.instIsNoetherianRing

example : Prime (X : ℤ_[p]⟦X⟧) := X_prime          -- needs IsDomain ℤ_[p] ✓
example : IsLocalRing (ℤ_[p]⟦X⟧) := inferInstance   -- via MvPowerSeries.instIsLocalRing

/-! ## §3 Weierstrass preparation (audited entry points; main chain avoids it) -/

#check @Polynomial.IsDistinguishedAt
#check @PowerSeries.IsWeierstrassDivision
#check @PowerSeries.IsWeierstrassDivisionAt
#check @PowerSeries.IsWeierstrassFactorization
#check @PowerSeries.IsWeierstrassFactorizationAt
#check @PowerSeries.exists_isWeierstrassDivision
#check @PowerSeries.exists_isWeierstrassFactorization
#check @PowerSeries.weierstrassDistinguished
#check @PowerSeries.weierstrassUnit

-- instances line up at A := ℤ_[p] (IsLocalRing + IsAdicComplete both found):
example (g : ℤ_[p]⟦X⟧) (hg : g.map (IsLocalRing.residue ℤ_[p]) ≠ 0) :
    ∃ f h, g.IsWeierstrassFactorization f h :=
  PowerSeries.exists_isWeierstrassFactorization hg

/-! ## §4 p-adics (T11, T24, T26, T40) -/

#check @hensels_lemma                       -- aeval form, [Algebra R ℤ_[p]]
#check @PadicInt.isUnit_iff
#check @PadicInt.maximalIdeal_eq_span_p
#check @PadicInt.norm_lt_one_iff_dvd
#check @PadicInt.toZMod
#check @PadicInt.ker_toZMod
#check @PadicInt.toZModPow                  -- certificate vehicle (T14/T26)
#check @PadicInt.ker_toZModPow
#check @padicValRat

example : IsDomain ℤ_[p] := inferInstance
example : IsDiscreteValuationRing ℤ_[p] := inferInstance
example : IsPrincipalIdealRing ℤ_[p] := inferInstance
example : IsLocalRing ℤ_[p] := inferInstance
example : IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p] := inferInstance
example : Algebra ℤ_[p] ℚ_[p] := inferInstance
example : IsFractionRing ℤ_[p] ℚ_[p] := inferInstance

/-! ## §5 Gaussian integers (T11 `ap_from_CM`, T24) -/

#check GaussianInt                          -- abbrev for Zsqrtd (-1)
#check @Nat.Prime.sq_add_sq                 -- p % 4 ≠ 3 → ∃ a b : ℕ, a² + b² = p
example (x : GaussianInt) : ℤ := x.re
example (x : GaussianInt) : ℤ := x.im
example (x : GaussianInt) : ℤ := Zsqrtd.norm x

/-! ## §6 Modules over PIDs, rank, structure theory (T12, T23, T27) -/

#check @Module.Basis                        -- NB: `Basis` → `Module.Basis` in this rev
#check @Submodule.basisOfPid
#check @Module.free_of_finite_type_torsion_free'   -- instance, [Module.IsTorsionFree R M]
#check @Module.IsTorsionFree
#check @Module.IsTorsionFree.of_smul_eq_zero
#check @Module.equiv_free_prod_directSum
#check @OrzechProperty.injective_of_surjective_endomorphism  -- T27 preferred route
#check @IsNoetherian.injective_of_surjective_endomorphism
#check @Submodule.finrank_quotient_add_finrank
#check @IsDomain.hasRankNullity             -- rank-nullity directly over ℤ_[p]
#check @LinearMap.finrank_range_add_finrank_ker   -- division-ring version (ℚ_[p])
#check @Module.finrank_baseChange
#check @Module.finrank_pi
#check @Module.finrank_fin_fun
#check @commRing_strongRankCondition

example : Module.finrank ℤ_[p] (Fin 2 → ℤ_[p]) = 2 := Module.finrank_fin_fun ℤ_[p]

-- rank-nullity over ℤ_[p] itself (HasRankNullity via IsDomain — no base change needed):
example (N : Submodule ℤ_[p] (Fin 2 → ℤ_[p])) :
    Module.finrank ℤ_[p] ((Fin 2 → ℤ_[p]) ⧸ N) + Module.finrank ℤ_[p] N = 2 := by
  rw [Submodule.finrank_quotient_add_finrank, Module.finrank_fin_fun]

-- finrank additivity via ℚ_[p] base change (T27 alternative route):
open scoped TensorProduct in
example : Module.finrank ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] (Fin 2 → ℤ_[p])) = 2 := by
  rw [Module.finrank_baseChange, Module.finrank_fin_fun]

/-! ## §7 Quotient modules Λ ⧸ (f), Pi types, Module.Finite (T12, T23) -/

#check @Ideal.Quotient.mk
#check @Ideal.Quotient.lift
#check @Ideal.mem_span_singleton
#check @Ideal.quotEquivOfEq
#check @RingHom.quotientKerEquivOfSurjective
#check @Submodule.liftQ
#check @Submodule.mapQ
#check @LinearMap.pi
#check @LinearMap.proj
#check @LinearMap.ker_pi
#check @Module.Finite.pi
#check @Module.Finite.quotient
#check @Module.Finite.of_submodule_quotient

-- module instances on Λ ⧸ span {f} resolve:
example (f : ℤ_[p]⟦X⟧) : Module (ℤ_[p]⟦X⟧) (ℤ_[p]⟦X⟧ ⧸ Ideal.span {f}) := inferInstance

-- THE composition test for T12's fused `rubin_structure` field ↔ T23's kernel
-- signature (board §5 T23): the Prop elaborates as written on the board.
example (n : ℕ) (f : Fin n → ℤ_[p]⟦X⟧) (X : Type) [AddCommGroup X]
    [Module (ℤ_[p]⟦X⟧) X] : Prop :=
  ∃ φ : X →ₗ[ℤ_[p]⟦X⟧] Π i, ℤ_[p]⟦X⟧ ⧸ Ideal.span {f i},
    Finite (LinearMap.ker φ) ∧
    Finite ((Π i, ℤ_[p]⟦X⟧ ⧸ Ideal.span {f i}) ⧸ LinearMap.range φ) ∧
    Associated (∏ i, f i) (PowerSeries.X ^ 2 : ℤ_[p]⟦X⟧)

-- T-coinvariants shape used by `control` (T12) — instance found:
example (I : Ideal (ℤ_[p]⟦X⟧)) (X : Type) [AddCommGroup X] [Module (ℤ_[p]⟦X⟧) X]
    [Module.Finite (ℤ_[p]⟦X⟧) X] :
    Module.Finite (ℤ_[p]⟦X⟧ ⧸ I) (X ⧸ I • (⊤ : Submodule (ℤ_[p]⟦X⟧) X)) :=
  inferInstance

/-! ## §8 Scalar-tower plumbing ℤ_[p] → Λ (T12) -/

example : Algebra ℤ_[p] (ℤ_[p]⟦X⟧) := inferInstance      -- MvPowerSeries.instAlgebra
example : IsScalarTower ℤ_[p] (ℤ_[p]⟦X⟧) (ℤ_[p]⟦X⟧) := inferInstance
example (X : Type) [AddCommGroup X] [Module (ℤ_[p]⟦X⟧) X] [Module ℤ_[p] X]
    [IsScalarTower ℤ_[p] (ℤ_[p]⟦X⟧) X] : True := trivial

/-! ## §9 Residue fields, local homs, unit transfer (T13, T22, T25) -/

#check @IsLocalRing.ResidueField
#check @IsLocalRing.residue
#check @IsLocalHom                          -- NB: renamed from IsLocalRingHom
#check @isUnit_map_iff

example (w : ℤ_[p]) : IsLocalRing.ResidueField ℤ_[p] := IsLocalRing.residue ℤ_[p] w

-- unit transfer along a local hom (T22 corollary shape):
example (W : Type) [CommRing W] (ι : ℤ_[p] →+* W) [IsLocalHom ι] (x : ℤ_[p]) :
    IsUnit (ι x) ↔ IsUnit x :=
  isUnit_map_iff ι x

/-! ## §10 Associated API (T21, T23) -/

#check @Associated
#check @Associated.isUnit_iff
#check @associated_one_iff_isUnit
#check @associated_mul_unit_left
#check @associated_of_dvd_dvd
#check @isUnit_of_associated_mul
#check @Prime.dvd_of_dvd_pow
#check @Irreducible.dvd_iff

/-! ## §11 Gap workarounds (G1, G2 of MathlibAudit.md — owner T23(a)) -/

-- G1: ker(constantCoeff) = (X) over any comm ring (mathlib has only the field case).
theorem NameCheck.ker_constantCoeff_eq_span_X :
    RingHom.ker (constantCoeff (R := ℤ_[p])) = Ideal.span {(X : ℤ_[p]⟦X⟧)} := by
  ext f
  simp [RingHom.mem_ker, Ideal.mem_span_singleton, X_dvd_iff]

-- G2: Λ ⧸ (X) ≃+* ℤ_[p], mirroring mathlib's `residueFieldOfPowerSeries`:
def NameCheck.quotSpanXEquiv : (ℤ_[p]⟦X⟧ ⧸ Ideal.span {(X : ℤ_[p]⟦X⟧)}) ≃+* ℤ_[p] :=
  (Ideal.quotEquivOfEq NameCheck.ker_constantCoeff_eq_span_X.symm).trans
    (RingHom.quotientKerEquivOfSurjective constantCoeff_surj)

/-! ## §12 Axiom audit tooling (T02) -/

#check @Lean.collectAxioms

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let axs ← Lean.collectAxioms ``PowerSeries.X_prime
  logInfo m!"axioms of PowerSeries.X_prime: {axs.toList}"

end
