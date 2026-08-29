import Mathlib

/-!
# Decoupling of the second jet (`lem:decoupling`, task T22)

Pure power-series algebra behind `lem:decoupling` of *Second derivatives of
p-adic L-functions and the Shafarevich–Tate group of rank-two CM elliptic
curves*. The paper's decoupling step observes
that when the low coefficients of one factor vanish, the second Taylor
coefficient of a product `A · B` collapses to a single term, so that
"grade-two units" transfer between comparison partners.

Everything here is **ring-generic** (`CommRing`) and mathlib-only. The results
are consumed by `thm:reduction` (task T33), whose comparison field has the shape
`Lp.map ι = (c : W) • (↑u * LKatz)` with `ι = algebraMap ℤ_[p] W` (a local,
injective ring hom by `KatzData.algMap_isLocalHom` / `KatzData.algInj`).

Contents (all in namespace `FinShaRank2.Decoupling`):

* `coeff_two_mul` — the grade-two product formula
  `c₂(AB) = c₀A·c₂B + c₁A·c₁B + c₂A·c₀B`.
* `coeff_two_mul_of_snd_low` / `coeff_two_mul_of_fst_low` — its collapse when the
  low coefficients of the second / first factor vanish (`lem:decoupling`
  proper). The unit `u` of T33's comparison sits on the **left**, `LKatz` on the
  right, so `_of_snd_low` (vanishing on the right factor) is the variant T33
  applies.
* `coeff_smul_eq_mul` — `cₙ(a • F) = a · cₙF` (scalar pushes through `coeff`).
* `coeff_eq_zero_of_map_eq_zero` — downward low-coefficient transfer along an
  injective ring hom: `cₖ(f.map ι) = 0 → cₖ f = 0`.
* `isUnit_coeff_two_map_iff` — unit transfer along a **local** ring hom:
  `IsUnit (c₂(f.map ι)) ↔ IsUnit (c₂ f)`.
* `isUnit_coeff_two_of_comparison` — the fully composed forward transfer T33
  invokes: from a comparison `f.map ι = c • (↑u · G)` with `c₀G = c₁G = 0` and
  `IsUnit (c₂G)`, conclude `IsUnit (c₂ f)`.

Paper labels quoted below: `lem:decoupling`, `lem:comparison`, `thm:reduction`.
-/

open PowerSeries

namespace FinShaRank2.Decoupling

variable {R S : Type*} [CommRing R] [CommRing S]

/-- **Grade-two product formula.** The second Taylor coefficient of a product of
power series decouples into the three grade-two pairings of the factors:
`coeff 2 (A * B) = coeff 0 A * coeff 2 B + coeff 1 A * coeff 1 B + coeff 2 A * coeff 0 B`.

This is the ring-generic core of `lem:decoupling`; the antidiagonal of `2` is
`{(0,2), (1,1), (2,0)}`. PAPER: `lem:decoupling`. -/
theorem coeff_two_mul (A B : PowerSeries R) :
    coeff 2 (A * B)
      = coeff 0 A * coeff 2 B + coeff 1 A * coeff 1 B + coeff 2 A * coeff 0 B := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

/-- **Decoupling, second factor.** If the constant and linear coefficients of the
*right* factor vanish, then `coeff 2 (A * B) = coeff 0 A * coeff 2 B`.

This is the shape `thm:reduction` (T33) uses: its comparison is
`Lp.map ι = c • (↑u * LKatz)`, so with `A := ↑u`, `B := LKatz` (and
`coeff 0 LKatz = coeff 1 LKatz = 0`) the grade-two coefficient of `↑u * LKatz`
is `coeff 0 ↑u * coeff 2 LKatz`. PAPER: `lem:decoupling`. -/
theorem coeff_two_mul_of_snd_low (A B : PowerSeries R)
    (hB0 : coeff 0 B = 0) (hB1 : coeff 1 B = 0) :
    coeff 2 (A * B) = coeff 0 A * coeff 2 B := by
  rw [coeff_two_mul, hB0, hB1]; ring

/-- **Decoupling, first factor** (mirror of `coeff_two_mul_of_snd_low`). If the
constant and linear coefficients of the *left* factor vanish, then
`coeff 2 (A * B) = coeff 2 A * coeff 0 B`. PAPER: `lem:decoupling`. -/
theorem coeff_two_mul_of_fst_low (A B : PowerSeries R)
    (hA0 : coeff 0 A = 0) (hA1 : coeff 1 A = 0) :
    coeff 2 (A * B) = coeff 2 A * coeff 0 B := by
  rw [coeff_two_mul, hA0, hA1]; ring

/-- A scalar pushes through `coeff`: `coeff n (a • F) = a * coeff n F`, since
`coeff n` is `R`-linear and `R` acts on itself by multiplication.

Item (b) for T33: it turns the constant `c` of the comparison
`Lp.map ι = c • (↑u * LKatz)` into an honest ring multiplication when reading off
coefficients. -/
theorem coeff_smul_eq_mul (n : ℕ) (a : R) (F : PowerSeries R) :
    coeff n (a • F) = a * coeff n F := by
  rw [map_smul, smul_eq_mul]

/-- **Downward low-coefficient transfer along an injective ring hom.** If
`coeff k (f.map ι) = 0` and `ι` is injective, then `coeff k f = 0`.

Item (a) for T33: combined with `coeff_smul_eq_mul` and the constant-coefficient
bookkeeping on the unit series `u`, this pushes `coeff 0 Lp = coeff 1 Lp = 0`
through the comparison to `coeff 0 LKatz = coeff 1 LKatz = 0`. -/
theorem coeff_eq_zero_of_map_eq_zero (ι : R →+* S) (hι : Function.Injective ι)
    {f : PowerSeries R} {k : ℕ} (h : coeff k (f.map ι) = 0) : coeff k f = 0 := by
  have hmap : ι (coeff k f) = ι 0 := by rw [← coeff_map, h, map_zero]
  exact hι hmap

/-- **Grade-two unit transfer along a local ring hom.** For a ring hom
`ι : R →+* S` that is a local hom (`IsLocalHom`),
`IsUnit (coeff 2 (f.map ι)) ↔ IsUnit (coeff 2 f)`.

This is the unit-transfer corollary of `lem:decoupling`. `thm:reduction` (T33)
applies it with `R := ℤ_[p]`, `S := W`, `ι := algebraMap ℤ_[p] W`, taking the
`IsLocalHom` instance from `KatzData.algMap_isLocalHom`; the equivalence then
moves grade-two unit-ness between `LKatz` (via `coeff_two_mul_of_snd_low`) and
the MTT series `Lp`. Tools: `PowerSeries.coeff_map`, `isUnit_map_iff`. -/
theorem isUnit_coeff_two_map_iff (ι : R →+* S) [IsLocalHom ι] (f : PowerSeries R) :
    IsUnit (coeff 2 (f.map ι)) ↔ IsUnit (coeff 2 f) := by
  rw [coeff_map]
  exact isUnit_map_iff ι (coeff 2 f)

/-- **Fully composed grade-two transfer** for `thm:reduction` (T33). Given a
comparison `f.map ι = c • (↑u * G)` with `ι` a local ring hom, `c : Sˣ`,
`u : (S⟦X⟧)ˣ`, the low coefficients of `G` vanishing (`coeff 0 G = coeff 1 G =
0`), and `IsUnit (coeff 2 G)`, one concludes `IsUnit (coeff 2 f)`.

Reading coefficients: `coeff 2 (f.map ι) = c * (coeff 0 ↑u * coeff 2 G)` by
`coeff_smul_eq_mul` and `coeff_two_mul_of_snd_low`; each factor is a unit (`c` a
unit, `coeff 0 ↑u` a unit since `u` is a unit series, `coeff 2 G` a unit), so the
product is a unit, and `isUnit_coeff_two_map_iff` transfers it back to `f`.

The derivation of the hypotheses `coeff 0 G = coeff 1 G = 0` — the
constant-coefficient bookkeeping on the unit series `u` — is left to T33 (it
combines `coeff_eq_zero_of_map_eq_zero`, `coeff_smul_eq_mul`, and `map_mul` on
`constantCoeff`). PAPER: `lem:decoupling`, `lem:comparison`, `thm:reduction`. -/
theorem isUnit_coeff_two_of_comparison (ι : R →+* S) [IsLocalHom ι]
    (f : PowerSeries R) (G : PowerSeries S) (c : Sˣ) (u : (PowerSeries S)ˣ)
    (hmap : f.map ι = (c : S) • ((u : PowerSeries S) * G))
    (hG0 : coeff 0 G = 0) (hG1 : coeff 1 G = 0) (hG2 : IsUnit (coeff 2 G)) :
    IsUnit (coeff 2 f) := by
  rw [← isUnit_coeff_two_map_iff ι f, hmap, coeff_smul_eq_mul,
    coeff_two_mul_of_snd_low _ _ hG0 hG1]
  have hu0 : IsUnit (coeff 0 (u : PowerSeries S)) := by
    rw [coeff_zero_eq_constantCoeff]
    exact u.isUnit.map (constantCoeff (R := S))
  exact c.isUnit.mul (hu0.mul hG2)

end FinShaRank2.Decoupling
