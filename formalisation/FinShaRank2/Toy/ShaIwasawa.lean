import FinShaRank2.Toy.Iwasawa
import FinShaRank2.Toy.ShaAnalytic

/-!
# Anti-vacuity Iwasawa / descent layers (task T41): `Toy.shaSelmer`, `Toy.shaIwasawa`

The Λ-module and descent layers of the anti-vacuity instance `ToySha`. Where the
T40 layers (`Toy/Iwasawa.lean`) took `X := (Λ/(X))²` and a *trivial* `ShaDual`,
here the elementary divisors of `X` are forced by `Lp = C p · X²`:

* `shaF := ![X, X, C p]`, so `∏ᵢ shaF i = X · X · C p = Lp` **on the nose**;
* `X := ∏ᵢ Λ/(shaF i) = Λ/(X) × Λ/(X) × Λ/(C p)`;
* `SelDual := X_Γ = X/T·X ≅ ℤ_[p]² × ℤ_[p]/(p)`;
* `ShaDual := ℤ_[p]/(p)`, which is **not** subsingleton (`p` is not a unit of
  `ℤ_[p]`) — the whole point of the task.

`(X, X, C p)` is the only elementary-divisor multiset with product `C p · X²`
whose Γ-coinvariants have `ℤ_[p]`-rank `2` (needed for `SelmerData.π_surj`) *and*
nontrivial torsion (needed for a nontrivial `ShaDual`): `(X, C p·X)` and
`(C p·X²)` and `(X², C p)` all fail one of the two.

## Contents

* `Toy.shaF`, `Toy.ShaX`, `Toy.ShaK`, `Toy.ShaSel` — the elementary divisors, the
  Iwasawa module, `ℤ_[p]/(p)`, and the Selmer dual.
* `Toy.shaToK`, `Toy.shaMk`, `Toy.shaPhi` — the coinvariant map
  `X → ℤ_[p]² × ℤ_[p]/(p)` and the tautological presentation `Λ³ ↠ X`.
* `Toy.shaPhi_surjective`, `Toy.ker_shaPhi` — surjectivity and
  `ker Φ = T·X`, giving the control isomorphism.
* `Toy.sha_no_finite_submodule` — Greenberg's input, here a theorem.
* `Toy.shaSelmer`, `Toy.shaIwasawa`, `Toy.not_subsingleton_ShaK`.
-/

open PowerSeries

namespace FinShaRank2

namespace Toy

variable {p : ℕ} [Fact p.Prime]

/-- elementary divisors -/
noncomputable def shaF (p : ℕ) [Fact p.Prime] : Fin 3 → Λ p := ![X, X, C (p : ℤ_[p])]

noncomputable abbrev ShaX (p : ℕ) [Fact p.Prime] : Type :=
  ∀ i : Fin 3, (Λ p) ⧸ Ideal.span {shaF p i}

noncomputable abbrev ShaK (p : ℕ) [Fact p.Prime] : Type := ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}

noncomputable abbrev ShaSel (p : ℕ) [Fact p.Prime] : Type := (Fin 2 → ℤ_[p]) × ShaK p

/-- `Λ ⧸ (C p) → ℤ_[p] ⧸ (p)`, induced by the constant coefficient. -/
noncomputable def shaToK (p : ℕ) [Fact p.Prime] :
    ((Λ p) ⧸ Ideal.span {(C (p : ℤ_[p]) : Λ p)}) →ₗ[ℤ_[p]] ShaK p :=
  (Submodule.liftQ ((Ideal.span {(C (p : ℤ_[p]) : Λ p)}).restrictScalars ℤ_[p])
      ((Ideal.span {(p : ℤ_[p])}).mkQ ∘ₗ (PowerSeries.coeff 0 : Λ p →ₗ[ℤ_[p]] ℤ_[p]))
      (by
        rintro g hg
        simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton] at hg
        obtain ⟨h, rfl⟩ := hg
        simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
          Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton,
          coeff_C_mul]
        exact ⟨coeff 0 h, rfl⟩)).comp
    (Submodule.Quotient.restrictScalarsEquiv ℤ_[p]
      (Ideal.span {(C (p : ℤ_[p]) : Λ p)})).symm.toLinearMap

theorem shaToK_mk (g : Λ p) :
    shaToK p (Submodule.Quotient.mk g) = Submodule.Quotient.mk (coeff 0 g) := rfl


/-- The tautological Λ-linear surjection `Λ³ ↠ X`. -/
noncomputable def shaMk (p : ℕ) [Fact p.Prime] : (Fin 3 → Λ p) →ₗ[Λ p] ShaX p :=
  LinearMap.pi fun i => (Ideal.span {shaF p i}).mkQ ∘ₗ LinearMap.proj i

theorem shaMk_apply (v : Fin 3 → Λ p) (i : Fin 3) :
    shaMk p v i = Submodule.Quotient.mk (v i) := rfl

theorem shaMk_surjective (x : ShaX p) : ∃ v : Fin 3 → Λ p, shaMk p v = x := by
  choose v hv using fun i => Submodule.Quotient.mk_surjective (Ideal.span {shaF p i}) (x i)
  exact ⟨v, funext fun i => hv i⟩

/-- The Γ-coinvariant map `X → ℤ_[p]² × (ℤ_[p]/p)`. -/
noncomputable def shaPhi (p : ℕ) [Fact p.Prime] : ShaX p →ₗ[ℤ_[p]] ShaSel p :=
  LinearMap.prod
    (LinearMap.pi ![(quotXEquiv p).toLinearMap ∘ₗ LinearMap.proj (0 : Fin 3),
      (quotXEquiv p).toLinearMap ∘ₗ LinearMap.proj (1 : Fin 3)])
    (shaToK p ∘ₗ LinearMap.proj (2 : Fin 3))

theorem shaPhi_apply (x : ShaX p) :
    shaPhi p x = (![quotXEquiv p (x 0), quotXEquiv p (x 1)], shaToK p (x 2)) := by
  refine Prod.ext ?_ rfl
  funext i
  fin_cases i <;> rfl


/-- membership in `span{r} • ⊤` -/
theorem mem_span_smul_top_iff {M : Type} [AddCommGroup M] [Module (Λ p) M] (r : Λ p) (z : M) :
    z ∈ Ideal.span {r} • (⊤ : Submodule (Λ p) M) ↔ ∃ y : M, z = r • y := by
  constructor
  · intro hz
    refine Submodule.smul_induction_on hz ?_ ?_
    · intro a ha m _
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp ha
      exact ⟨g • m, by rw [mul_smul]⟩
    · rintro u v ⟨a, rfl⟩ ⟨b, rfl⟩
      exact ⟨a + b, by rw [smul_add]⟩
  · rintro ⟨y, rfl⟩
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self r) Submodule.mem_top

theorem shaPhi_mk (v : Fin 3 → Λ p) :
    shaPhi p (shaMk p v)
      = (![coeff 0 (v 0), coeff 0 (v 1)], Submodule.Quotient.mk (coeff 0 (v 2))) := by
  rw [shaPhi_apply]; rfl

theorem shaPhi_surjective : Function.Surjective (shaPhi p) := by
  rintro ⟨w, k⟩
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective (Ideal.span {(p : ℤ_[p])}) k
  refine ⟨shaMk p ![C (w 0), C (w 1), C c], ?_⟩
  rw [shaPhi_mk]
  have hw : (![coeff 0 ((![C (w 0), C (w 1), C c] : Fin 3 → Λ p) 0),
      coeff 0 ((![C (w 0), C (w 1), C c] : Fin 3 → Λ p) 1)] : Fin 2 → ℤ_[p]) = w := by
    funext i
    fin_cases i
    · show coeff 0 (C (w 0) : Λ p) = w 0
      simp
    · show coeff 0 (C (w 1) : Λ p) = w 1
      simp
  have hc2 : coeff 0 ((![C (w 0), C (w 1), C c] : Fin 3 → Λ p) 2) = c := by
    show coeff 0 (C c : Λ p) = c
    simp
  rw [hw, hc2]

/-- `X • shaMk v = shaMk (X • v)`. -/
theorem smul_shaMk (v : Fin 3 → Λ p) :
    (X : Λ p) • shaMk p v = shaMk p (fun i => X * v i) := by
  rw [← map_smul]; rfl

theorem ker_shaPhi :
    LinearMap.ker (shaPhi p)
      = (Ideal.span {(X : Λ p)} • (⊤ : Submodule (Λ p) (ShaX p))).restrictScalars ℤ_[p] := by
  ext x
  rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, mem_span_smul_top_iff]
  obtain ⟨v, rfl⟩ := shaMk_surjective x
  rw [shaPhi_mk]
  constructor
  · intro hx
    have h1 : (![coeff 0 (v 0), coeff 0 (v 1)] : Fin 2 → ℤ_[p]) = 0 := congrArg Prod.fst hx
    have h2 : (Submodule.Quotient.mk (coeff 0 (v 2)) : ShaK p) = 0 := congrArg Prod.snd hx
    have e0 : coeff 0 (v 0) = 0 := by simpa using congrFun h1 0
    have e1 : coeff 0 (v 1) = 0 := by simpa using congrFun h1 1
    have e2 : (p : ℤ_[p]) ∣ coeff 0 (v 2) := by
      rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton] at h2
      exact h2
    obtain ⟨h0, hh0⟩ : (X : Λ p) ∣ v 0 := by
      rw [PowerSeries.X_dvd_iff, ← coeff_zero_eq_constantCoeff_apply]; exact e0
    obtain ⟨h1', hh1⟩ : (X : Λ p) ∣ v 1 := by
      rw [PowerSeries.X_dvd_iff, ← coeff_zero_eq_constantCoeff_apply]; exact e1
    obtain ⟨c, hc⟩ := e2
    obtain ⟨h2', hh2⟩ : (X : Λ p) ∣ (v 2 - C ((p : ℤ_[p]) * c)) := by
      rw [PowerSeries.X_dvd_iff, map_sub, constantCoeff_C,
        ← coeff_zero_eq_constantCoeff_apply, ← hc, sub_self]
    refine ⟨shaMk p ![h0, h1', h2'], ?_⟩
    rw [smul_shaMk]
    funext i
    fin_cases i
    · exact congrArg _ hh0
    · exact congrArg _ hh1
    · show Submodule.Quotient.mk (v 2) = Submodule.Quotient.mk (X * h2')
      rw [Submodule.Quotient.eq]
      have hsub : v 2 - X * h2' = C ((p : ℤ_[p]) * c) := by
        rw [← hh2]; ring
      rw [hsub]
      exact Ideal.mem_span_singleton.mpr ⟨C c, map_mul C _ _⟩
  · rintro ⟨y, hy⟩
    obtain ⟨u, rfl⟩ := shaMk_surjective y
    rw [smul_shaMk] at hy
    have key : ∀ i : Fin 3, v i - X * u i ∈ Ideal.span {shaF p i} := by
      intro i
      have h := congrFun hy i
      rw [shaMk_apply, shaMk_apply, Submodule.Quotient.eq] at h
      exact h
    have hzero : ∀ j : Fin 3, shaF p j = (X : Λ p) → coeff 0 (v j) = 0 := by
      intro j hj
      have h := key j
      rw [hj, Ideal.mem_span_singleton] at h
      obtain ⟨w, hw⟩ := h
      have : v j = X * (u j + w) := by rw [mul_add, ← hw]; ring
      rw [this, coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_X, zero_mul]
    have hfst : (![coeff 0 (v 0), coeff 0 (v 1)] : Fin 2 → ℤ_[p]) = 0 := by
      funext i
      fin_cases i
      · simpa using hzero 0 rfl
      · simpa using hzero 1 rfl
    have hsnd : (Submodule.Quotient.mk (coeff 0 (v 2)) : ShaK p) = 0 := by
      have h := key 2
      rw [show Ideal.span {shaF p 2} = Ideal.span {(C (p : ℤ_[p]) : Λ p)} from rfl,
        Ideal.mem_span_singleton] at h
      obtain ⟨w, hw⟩ := h
      have hv2 : coeff 0 (v 2) = (p : ℤ_[p]) * coeff 0 w := by
        have : v 2 = X * u 2 + C (p : ℤ_[p]) * w := by rw [← hw]; ring
        rw [this, map_add, coeff_C_mul, coeff_zero_eq_constantCoeff_apply, map_mul,
          constantCoeff_X, zero_mul, zero_add]
      rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
      exact ⟨coeff 0 w, hv2⟩
    rw [hfst, hsnd]
    rfl


/-! ### No nonzero finite submodule -/

/-- `C p` divides a power series iff it divides all coefficients. -/
theorem C_p_dvd_iff (g : Λ p) :
    (C (p : ℤ_[p]) : Λ p) ∣ g ↔ ∀ n, (p : ℤ_[p]) ∣ coeff n g := by
  constructor
  · rintro ⟨h, rfl⟩ n
    exact ⟨coeff n h, by rw [coeff_C_mul]⟩
  · intro h
    choose c hc using h
    exact ⟨PowerSeries.mk c, by ext n; rw [coeff_C_mul, coeff_mk]; exact hc n⟩

theorem smul_quot_mk {I : Ideal (Λ p)} (r a : Λ p) :
    r • (Submodule.Quotient.mk a : Λ p ⧸ I) = Submodule.Quotient.mk (r * a) := rfl

/-- On `Λ/(X) ≅ ℤ_[p]` the natural multiples of a nonzero element are distinct. -/
theorem injective_natCast_smul_quotX {y : Λ p ⧸ Ideal.span {(X : Λ p)}} (hy : y ≠ 0) :
    Function.Injective (fun k : ℕ => (k : Λ p) • y) := by
  have hy' : quotXEquiv p y ≠ 0 := fun h => hy ((quotXEquiv p).map_eq_zero_iff.mp h)
  intro k l hkl
  simp only at hkl
  have h1 : (k : ℕ) • y = (l : ℕ) • y := by
    rw [← Nat.cast_smul_eq_nsmul (Λ p) k y, ← Nat.cast_smul_eq_nsmul (Λ p) l y]; exact hkl
  have h2 : (k : ℤ_[p]) * quotXEquiv p y = (l : ℤ_[p]) * quotXEquiv p y := by
    have h := congrArg (quotXEquiv p) h1
    rwa [map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul] at h
  have h4 : ((k : ℤ_[p]) - (l : ℤ_[p])) * quotXEquiv p y = 0 := by rw [sub_mul, h2, sub_self]
  rcases mul_eq_zero.mp h4 with h5 | h5
  · exact Nat.cast_injective (sub_eq_zero.mp h5)
  · exact absurd h5 hy'

/-- On `Λ/(C p) ≅ 𝔽_p⟦T⟧` the powers `Xʲ · y` of a nonzero element are distinct. -/
theorem injective_X_pow_smul_quotCp {y : Λ p ⧸ Ideal.span {(C (p : ℤ_[p]) : Λ p)}}
    (hy : y ≠ 0) : Function.Injective (fun j : ℕ => ((X : Λ p) ^ j) • y) := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective (Ideal.span {(C (p : ℤ_[p]) : Λ p)}) y
  have hg : ¬ ((C (p : ℤ_[p]) : Λ p) ∣ g) := fun h =>
    hy (by rw [Submodule.Quotient.mk_eq_zero]; exact Ideal.mem_span_singleton.mpr h)
  have key : ∀ a b : ℕ, a < b →
      ((X : Λ p) ^ a) • (Submodule.Quotient.mk g : Λ p ⧸ Ideal.span {(C (p : ℤ_[p]) : Λ p)})
        ≠ ((X : Λ p) ^ b) • (Submodule.Quotient.mk g) := by
    intro a b hab heq
    rw [smul_quot_mk, smul_quot_mk, Submodule.Quotient.eq, Ideal.mem_span_singleton] at heq
    obtain ⟨m, hm⟩ : ∃ m : ℕ, b = a + (m + 1) := ⟨b - a - 1, by omega⟩
    have hfac : (X : Λ p) ^ a * g - X ^ b * g = (X ^ a * g) * (1 - X ^ (m + 1)) := by
      rw [hm, pow_add]; ring
    have hunit : IsUnit ((1 : Λ p) - X ^ (m + 1)) := by
      refine isUnit_iff_constantCoeff.mpr ?_
      rw [map_sub, map_one, map_pow, constantCoeff_X, zero_pow (by omega), sub_zero]
      exact isUnit_one
    rw [hfac] at heq
    have hdvd : (C (p : ℤ_[p]) : Λ p) ∣ (X : Λ p) ^ a * g :=
      (hunit.dvd_mul_right).mp heq
    refine hg ((C_p_dvd_iff g).mpr fun n => ?_)
    have h := (C_p_dvd_iff _).mp hdvd (n + a)
    rwa [coeff_X_pow_mul] at h
  intro j l hjl
  simp only at hjl
  rcases lt_trichotomy j l with h | h | h
  · exact absurd hjl (key j l h)
  · exact h
  · exact absurd hjl.symm (key l j h)


/-- **No nonzero finite Λ-submodule** for the anti-vacuity module
`X = Λ/(X) × Λ/(X) × Λ/(C p)`. On the two `Λ/(X) ≅ ℤ_[p]` factors the natural
multiples of a nonzero element are distinct; on `Λ/(C p) ≅ 𝔽_p⟦T⟧` the
`X`-multiples are. Either way a nonzero submodule contains a copy of `ℕ`. -/
theorem sha_no_finite_submodule (N : Submodule (Λ p) (ShaX p)) (hN : Finite N) : N = ⊥ := by
  by_contra hne
  obtain ⟨x, hxN, hx0⟩ := (Submodule.ne_bot_iff N).mp hne
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
  rw [Pi.zero_apply] at hi
  have main : ∀ r : ℕ → Λ p, Function.Injective (fun k : ℕ => r k • x) → False := by
    intro r hinj
    have h : Function.Injective (fun k : ℕ => (⟨r k • x, N.smul_mem _ hxN⟩ : N)) :=
      fun k l hkl => hinj (congrArg Subtype.val hkl)
    haveI : Finite ℕ := Finite.of_injective _ h
    exact not_finite ℕ
  fin_cases i
  · exact main (fun k => (k : Λ p)) fun k l hkl =>
      injective_natCast_smul_quotX hi (congrFun hkl 0)
  · exact main (fun k => (k : Λ p)) fun k l hkl =>
      injective_natCast_smul_quotX hi (congrFun hkl 1)
  · exact main (fun k => (X : Λ p) ^ k) fun k l hkl =>
      injective_X_pow_smul_quotCp hi (congrFun hkl 2)


/-! ### Assembly -/

theorem prod_shaF : ∏ i, shaF p i = shaLp p := by
  rw [Fin.prod_univ_three]
  show (X : Λ p) * X * C (p : ℤ_[p]) = C (p : ℤ_[p]) * X ^ 2
  ring

/-- **Anti-vacuity `SelmerData`**: `SelDual = ℤ_[p]² × ℤ_[p]/(p)`,
`ShaDual = ℤ_[p]/(p)` — *not* subsingleton. -/
noncomputable def shaSelmer (p : ℕ) [Fact p.Prime] : SelmerData p where
  SelDual := ShaSel p
  ShaDual := ShaK p
  ι := LinearMap.inr ℤ_[p] _ _
  π := LinearMap.fst ℤ_[p] _ _
  ι_inj := fun a b h => by simpa using congrArg Prod.snd h
  π_surj := fun w => ⟨(w, 0), rfl⟩
  mw_sha_exact := LinearMap.range_inr ℤ_[p] _ _

/-- **Anti-vacuity `IwasawaData`** over `Lp = C p · X²`. -/
noncomputable def shaIwasawa (p : ℕ) [Fact p.Prime] :
    IwasawaData p (shaLp p) (ShaSel p) where
  X := ShaX p
  no_finite_submodule := sha_no_finite_submodule
  rubin_structure := by
    refine ⟨3, shaF p, LinearMap.id, ?_, ?_, ?_⟩
    · rw [LinearMap.ker_id]; infer_instance
    · haveI : Subsingleton
          ((∀ i : Fin 3, (Λ p) ⧸ Ideal.span {shaF p i}) ⧸
            LinearMap.range (LinearMap.id : ShaX p →ₗ[Λ p] ShaX p)) :=
        Submodule.Quotient.subsingleton_iff.mpr LinearMap.range_id
      infer_instance
    · rw [prod_shaF]
  control :=
    ((Submodule.Quotient.restrictScalarsEquiv ℤ_[p]
        (Ideal.span {(X : Λ p)} • (⊤ : Submodule (Λ p) (ShaX p)))).symm.trans
      ((Submodule.quotEquivOfEq _ _ ker_shaPhi.symm).trans
        (LinearMap.quotKerEquivOfSurjective _ shaPhi_surjective)))

theorem not_subsingleton_ShaK : ¬ Subsingleton (ShaK p) := by
  intro h
  have h1 : (Submodule.Quotient.mk (1 : ℤ_[p]) : ShaK p) = 0 := Subsingleton.elim _ _
  rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton] at h1
  exact mem_nonunits_iff.mp PadicInt.p_nonunit (isUnit_of_dvd_one h1)

end Toy

end FinShaRank2
