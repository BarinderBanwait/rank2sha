import FinShaRank2.Defs

/-!
# Analytic interface: `AnalyticData p`

The per-prime **analytic** input layer for the formalization of *Second
derivatives of p-adic L-functions and the Shafarevich–Tate group of rank-two CM
elliptic curves*.

`AnalyticData p hsplit` bundles the Mazur–Tate–Teitelbaum (MTT) p-adic
L-function `L_p(E, T)` of the testbed curve `E : y² = x³ − 56x` together with
the small set of classical facts about it that the paper's Lemma 3.1 and
Lemma 2.3 consume: the interpolation formula at the trivial character,
the p-adic functional equation with sign `w(E) = +1`, the unit-root data of the
Frobenius polynomial `X² − a_p X + p`, the CM evenness of `a_p`, and the Hasse
bound. Each field is either a datum or a citable classical statement rendered —
where the conventions ask for it — as an equation
between data, so that the downstream conclusions (`c₀ = c₁ = 0`, non-anomalous
primes) are *derived* rather than assumed.

Nothing here mentions the paper's conclusions (µ = 0, λ = 2, Selmer corank,
triviality of Ш): those live strictly downstream.

## Binder design

`hsplit : p % 4 = 1` is carried as an **explicit hypothesis parameter**, matching
the paper's standing assumption that `p` is split in `K = ℚ(i)` (for this curve,
`p ≡ 1 (mod 4)` is exactly splitness, and forces good reduction — see
Lemma 2.3). It is passed explicitly rather than as a `Fact`-style
instance so that it composes directly with the aggregator's
`dataAt : ∀ p, p.Prime → p % 4 = 1 → p ∉ S → PrimeData p`, whose
`p % 4 = 1` argument is likewise an explicit arrow; a `Fact` would force
instance juggling at every call site. The hypothesis is a standing side
condition of the whole structure and is not consumed by any individual field
type.

Paper statements quoted below: §2.1, Lemma 3.1, Definition 3.2,
Remark 3.4, Lemma 2.3, §7.1.
-/

open PowerSeries

namespace FinShaRank2

/-- **Analytic data at a split prime `p`.**

The Mazur–Tate–Teitelbaum p-adic L-function of the testbed curve together with
the classical facts about it consumed by Lemma 3.1 and Lemma 2.3. The
split hypothesis `hsplit : p % 4 = 1` is the paper's standing assumption on `p`
(splitness in `K = ℚ(i)`); see the module docstring for the binder rationale.

SOURCE: Mazur–Tate–Teitelbaum, Invent. math. 84 (1986), 1–48; Stein–Wuthrich,
Math. Comp. 82 (2013), no. 283, 1757–1792.
PAPER:  §2.1 (`ssec:notation`), Lemma 3.1 (`lem:c0c1`), Lemma 2.3 (`lem:noanomalous`).
STATUS: interface aggregate (per-field SOURCE/PAPER/STATUS below). -/
structure AnalyticData (p : ℕ) [Fact p.Prime] (hsplit : p % 4 = 1) where
  /-- The MTT p-adic L-function `L_p(E, T) ∈ Λ = ℤ_[p]⟦X⟧` of the testbed curve,
  Néron-normalised as in MTT / Stein–Wuthrich. Its Taylor coefficients at `T = 0`
  are the `c_j(p)` of the paper (`coeff j Lp`). Integrality of `L_p` (its
  coefficients lie in `ℤ_[p]`) holds for all split `p` outside an explicit finite
  set, by integrality of the modular symbols of `E` at primes of irreducible
  residual representation — for split CM curves the mod-`𝔭` representation is
  irreducible for all but finitely many split `𝔭` (Remark 3.4);
  encoded here by the field type `Λ p` landing in `ℤ_[p]⟦X⟧`.

  SOURCE: Mazur–Tate–Teitelbaum, Invent. math. 84 (1986), 1–48 (construction);
          Stein–Wuthrich, Math. Comp. 82 (2013) (normalisation).
  PAPER:  §2.1 (`ssec:notation`) (definition of `L_p`); Remark 3.4 (`rmk:integrality`)
  (integrality).
  STATUS: data. -/
  Lp : Λ p
  /-- The trace of Frobenius `a_p = p + 1 − #Ẽ(𝔽_p) ∈ ℤ`. For the testbed curve
  it is even (`ap_from_CM`) and satisfies the Hasse bound (`hasse`); its unit root
  is `α` (`alpha_root`).

  SOURCE: classical (Frobenius trace of `E` at `p`).
  PAPER:  §2.1 (`ssec:notation`).
  STATUS: data. -/
  ap : ℤ
  /-- The unit root `α = α_p ∈ ℤ_[p]ˣ` of the Frobenius polynomial
  `X² − a_p X + p` under the fixed embedding `ι_p`. Because `p` is split, `E` is
  ordinary at `p`, so this polynomial has exactly one root that is a p-adic unit;
  `α` is that root (its defining equation is `alpha_root`).

  SOURCE: MTT, Invent. math. 84 (1986) (ordinary reduction: unit-root splitting).
  PAPER:  §2.1 (`ssec:notation`).
  STATUS: data. -/
  α : ℤ_[p]ˣ
  /-- `α` is a root of the Frobenius polynomial: `α² − a_p·α + p = 0` in `ℤ_[p]`.
  This is the defining relation of the unit root at a good ordinary prime, where
  `X² − a_p X + p` factors over `ℤ_[p]` (Hensel) into a unit root `α` and a
  non-unit root `p/α`.

  SOURCE: classical (Hensel factorization at a good ordinary prime; MTT,
          Invent. math. 84 (1986)).
  PAPER:  §2.1 (`ssec:notation`); Definition 3.2 (`def:c2tilde`) (`α_p` the unit root of
  `X² − a_pX + p`).
  STATUS: classical. -/
  alpha_root : (α : ℤ_[p]) ^ 2 - (ap : ℤ_[p]) * (α : ℤ_[p]) + (p : ℤ_[p]) = 0
  /-- The rank-zero modular symbol `L(E,1)/Ω_E ∈ ℚ`, a rational number computed
  exactly as a finite linear combination of modular symbols (eclib/Sage and PARI).
  Its interpolation into `L_p` is `interp`; its exact value for the testbed curve
  is `msymb_zero`.

  SOURCE: classical (modular symbol `L(E,1)/Ω_E`); Stein–Wuthrich, Math. Comp. 82
          (2013).
  PAPER:  Lemma 3.1 (`lem:c0c1`); §7.1 (`ssec:testbed`) (exact evaluation).
  STATUS: data. -/
  modularSymbol0 : ℚ
  /-- **MTT interpolation at the trivial character**, as a data-equation: the constant coefficient of `L_p` equals
  `(1 − α_p⁻¹)² · L(E,1)/Ω_E`. Combined with `msymb_zero` this *derives*
  `c₀(p) = 0`, rather than assuming it.

  The equation lives in `ℚ_[p]`, not `ℤ_[p]`: `modularSymbol0 ∈ ℚ` may carry `p`
  in its denominator, so it is coerced along `ℚ ↪ ℚ_[p]`; the left side
  `constantCoeff Lp ∈ ℤ_[p]` is coerced along `ℤ_[p] ↪ ℚ_[p]`, and `α_p⁻¹` is the
  field inverse of `(α : ℤ_[p]) : ℚ_[p]`.

  SOURCE: Mazur–Tate–Teitelbaum, Invent. math. 84 (1986), 1–48 (interpolation
          formula at the trivial character).
  PAPER:  Lemma 3.1 (`lem:c0c1`) (`c₀(p) = L_p(E,0) = (1 − α_p⁻¹)² L(E,1)/Ω_E`).
  STATUS: classical (rendered as a data-equation, a data-equation, not a bare proposition). -/
  interp : ((constantCoeff Lp : ℤ_[p]) : ℚ_[p])
      = (1 - ((α : ℤ_[p]) : ℚ_[p])⁻¹) ^ 2 * (modularSymbol0 : ℚ_[p])
  /-- **Exact vanishing of the modular symbol**: `L(E,1)/Ω_E = 0`. For the
  testbed curve `L(E,1) = 0` holds exactly — the rational `L(E,1)/Ω_E` is computed
  by exact linear algebra (eclib/Sage and PARI) and equals `0`; since
  `w(E) = +1` the order of vanishing at `s = 1` is even. This is the certificate
  half of the interpolation split (paired with `interp`): together they give
  `c₀(p) = 0` with no numerical dependence in the interpolation step itself.

  SOURCE: exact computation for `E : y² = x³ − 56x` (eclib/Sage modular symbols,
          cross-checked in PARI/GP).
  PAPER:  Lemma 3.1 (`lem:c0c1`) (hypothesis `L(E,1) = 0`); §7.1 (`ssec:testbed`) (certification).
  STATUS: certificate. -/
  msymb_zero : modularSymbol0 = 0
  /-- **MTT p-adic functional equation** with the root number `w(E) = +1` folded
  in: there is a unit power series `U ∈ Λˣ` with `U(0) = 1` such that
  substituting `σ = (1+T)⁻¹ − 1` into `L_p` gives `U · L_p`. (The general MTT
  identity is `L_p(E, (1+T)⁻¹ − 1) = w(E)·U(T)·L_p(E,T)`; here `w(E) = +1`.) The
  substitution `Lp.subst σ` is well defined because `σ` has vanishing constant
  term (`FinShaRank2.hasSubst_σ`). Comparing linear coefficients turns this into
  `−c₁ = c₁`, so `c₁(p) = 0`.

  SOURCE: Mazur–Tate–Teitelbaum, Invent. math. 84 (1986), 1–48 (p-adic functional
          equation).
  PAPER:  Lemma 3.1 (`lem:c0c1`) (`L_p(E,(1+T)⁻¹−1) = w(E)·U(T)·L_p(E,T)`, `w(E) = +1`).
  STATUS: classical. -/
  funct_eq : ∃ U : Λ p, IsUnit U ∧ constantCoeff U = 1 ∧ Lp.subst σ = U * Lp
  /-- **CM evenness of `a_p`.** For `E` with CM by `ℤ[i]` and `p` split, complex
  multiplication gives `a_p = π + π̄ = 2·Re(π)` for a generator `π` of the prime
  `𝔭 = (π)` above `p`, with `N(π) = π π̄ = p`. Encoded as: there is a Gaussian
  integer `π` of norm `p` with `a_p = 2·Re(π)`. This yields `2 ∣ a_p` immediately
  (witness `⟨π.re, ·⟩`), the arithmetic input to Lemma 2.3.

  SOURCE: complex-multiplication theory (Deuring): `a_p = π + π̄`, `p = π π̄` in
          `ℤ[i]`.
  PAPER:  Lemma 2.3 (`lem:noanomalous`) (`a_p ∈ 2ℤ`).
  STATUS: classical. -/
  ap_from_CM : ∃ π : GaussianInt, π.norm = (p : ℤ) ∧ ap = 2 * π.re
  /-- **Hasse bound** `a_p² ≤ 4p` (equivalently `|a_p| ≤ 2√p`). Together with the
  evenness from `ap_from_CM` this drives the Hasse squeeze of Lemma 2.3
  ruling out anomalous primes (`a_p ≢ 1 mod p`).

  SOURCE: Hasse bound on the Frobenius trace of an elliptic curve over `𝔽_p`.
  PAPER:  Lemma 2.3 (`lem:noanomalous`) (Hasse-bound step).
  STATUS: classical. -/
  hasse : ap ^ 2 ≤ 4 * (p : ℤ)

end FinShaRank2
