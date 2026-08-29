import FinShaRank2.Kernel.GradingValuation

/-!
# T25 composition + axiom check (scratch, not audited)

Demonstrates that `FinShaRank2.isUnit_iff_residue_ne_zero_of_grading_congr`
consumes T13's `grading_congr` field shape verbatim. We reproduce the exact
existential shape of `KatzData.grading_congr`
(`∃ κ₀ : Wˣ, (q:W)^2 * ((κ₀:W) * c − m) ∈ span {(q:W)^3}`) against a *generic*
`q : ℕ` with `(q : W) ≠ 0` — no `KatzData`/`Defs` import — destructure it, and
apply the headline. The implicit generator `ϖ` is inferred from the maximal-ideal
hypothesis as `(q : W)`, matching how T33 will pass `ϖ := (p : W)`.
-/

open FinShaRank2

/-- Composition test: the headline accepts a `grading_congr`-shaped hypothesis. -/
example {W : Type*} [CommRing W] [IsDomain W] [IsLocalRing W] {q : ℕ}
    (hmax : IsLocalRing.maximalIdeal W = Ideal.span {(q : W)}) (hq : (q : W) ≠ 0)
    (c m : W)
    (hgr : ∃ κ₀ : Wˣ,
      (q : W) ^ 2 * ((κ₀ : W) * c - m) ∈ Ideal.span {(q : W) ^ 3}) :
    IsUnit c ↔ IsLocalRing.residue W m ≠ 0 := by
  obtain ⟨κ₀, hcong⟩ := hgr
  exact isUnit_iff_residue_ne_zero_of_grading_congr hmax hq κ₀ c m hcong

-- Axiom whitelist check on both public declarations.
#print axioms FinShaRank2.dvd_of_pow_mul_mem_span_pow_succ
#print axioms FinShaRank2.isUnit_iff_residue_ne_zero_of_grading_congr
