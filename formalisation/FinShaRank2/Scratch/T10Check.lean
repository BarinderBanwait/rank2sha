import Mathlib

/-! T10 scratch: verify every intended `Defs.lean` declaration compiles. -/

noncomputable section
open PowerSeries

namespace T10Check

abbrev Λ (p : ℕ) [Fact p.Prime] : Type := PowerSeries ℤ_[p]

variable {p : ℕ} [Fact p.Prime]

noncomputable def σ : Λ p := PowerSeries.mk fun n => if n = 0 then 0 else (-1) ^ n

theorem constantCoeff_σ : constantCoeff (σ : Λ p) = 0 := by
  simp [σ, constantCoeff_mk]

theorem coeff_one_σ : coeff 1 (σ : Λ p) = -1 := by
  simp [σ, coeff_mk]

theorem hasSubst_σ : HasSubst (σ : Λ p) :=
  HasSubst.of_constantCoeff_zero' (by simp [σ, constantCoeff_mk])

-- optional characterizing identity (1 + X) * σ = -X
theorem oneAddX_mul_σ : (1 + X) * (σ : Λ p) = -X := by
  rw [add_mul, one_mul]
  ext n
  rw [map_add, map_neg, coeff_X]
  obtain _ | _ | m := n
  · simp [σ]
  · simp [σ, coeff_succ_X_mul]
  · rw [show m + 2 = (m + 1) + 1 from rfl, coeff_succ_X_mul]
    simp only [σ, coeff_mk, Nat.succ_ne_zero, if_false, if_neg (show m + 2 ≠ 1 by omega)]
    rw [pow_succ]; ring

def IsPUnit (x : ℚ_[p]) : Prop := ‖x‖ = 1

theorem isPUnit_coe_iff {x : ℤ_[p]} : IsPUnit (x : ℚ_[p]) ↔ IsUnit x := by
  rw [IsPUnit, PadicInt.padic_norm_e_of_padicInt, PadicInt.isUnit_iff]

def MuZero (f : Λ p) : Prop := ∃ n, IsUnit (PowerSeries.coeff n f)

noncomputable def lambdaAn (f : Λ p) : ℕ := sInf {n | IsUnit (PowerSeries.coeff n f)}

noncomputable def c2tilde (c2 alphaInv : ℚ_[p]) (torsSqOverTam : ℚ) : ℚ_[p] :=
  c2 * (1 - alphaInv)⁻¹ ^ 2 * (torsSqOverTam : ℚ_[p])

abbrev corank (M : Type*) [AddCommGroup M] [Module ℤ_[p] M] : ℕ := Module.finrank ℤ_[p] M

-- #check every public declaration
#check @Λ
#check @σ
#check @constantCoeff_σ
#check @coeff_one_σ
#check @hasSubst_σ
#check @oneAddX_mul_σ
#check @IsPUnit
#check @isPUnit_coe_iff
#check @MuZero
#check @lambdaAn
#check @c2tilde
#check @corank

end T10Check
end
