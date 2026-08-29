# R2a checkpoint — interface rewiring (EKPackage into KatzData/Global/Statements/Main/Toy)

Recovery unit. Append after every step that typechecks.

## Order of work

1. `Interface/Katz.lean`  — delete 3 fields, restate `SinnottHyp`
2. `Interface/Global.lean` — drop `deltaE` param + `deltaE_tie`; add `ek`, `notAnomalous`
3. `Statements.lean`      — `HorizontalControl`, existential `ConjStrong`
4. `Main/Consequence.lean` — drop `h5`, route non-anomality through `notAnomalous`
5. `Main/Dictionary.lean` — knock-on only
6. `Main/Reduction.lean`  — new `thm_reduction` shape, Resultant step at the front
7. `Toy/EK.lean` (new), `Toy/Katz.lean`, `Toy/ShaKatz.lean`, `Toy/Trivial.lean`,
   `Toy/ShaTrivial.lean`, `Toy/Analytic.lean` (`Setup.ap_ne_one` helper)
8. `AxiomAudit.lean`

## Target shapes

```lean
-- Interface/Katz.lean
structure SinnottHyp (p : ℕ) [Fact p.Prime] (Lp : Λ p) (Kd : KatzData p Lp)
    (P : EKPackage) (c : Fin 6 → P.K) : Prop where
  integral     : ∀ t ∈ P.D, P.v p (P.Fc c t) ≤ 1
  presentation : IsLocalRing.residue Kd.W Kd.m2core = Kd.traceClass
  nonvanishing : (∀ t ∈ P.D, P.v p (P.Fc c t) = 1) → Kd.traceClass ≠ 0

-- Interface/Global.lean
structure PrimeData (p : ℕ) [Fact p.Prime] (hsplit : p % 4 = 1) (torsSqOverTam : ℚ)
-- fields: analytic selmer iwasawa height katz c2norm_tie shaOrd_tie   (deltaE_tie gone)

structure ClassicalInputs where
  S : Finset ℕ
  ek : EKPackage
  torsSqOverTam : ℚ
  torsSqOverTam_eq : torsSqOverTam = 1
  dataAt : ∀ p hp hsplit, p ∉ S → @PrimeData p (Fact.mk hp) hsplit torsSqOverTam
  notAnomalous : ∀ p hp hsplit hpS, ¬ (((dataAt p hp hsplit hpS).analytic.ap : ZMod p) = 1)

-- Statements.lean
def HorizontalControl (P : Set ℕ) (shaVanishes : ℕ → Prop) : Prop := ...
def ConjStrong (H : ClassicalInputs) : Prop :=
  ∃ (δ : H.ek.L) (Sig : Finset ℕ), δ ≠ 0 ∧
    ∀ p hp hsplit (hpS : p ∉ H.S) (_ : p ∉ Sig), H.ek.v p δ = 1 →
      letI : Fact p.Prime := ⟨hp⟩; IsPUnit (H.dataAt p hp hsplit hpS).c2tilde

-- Main/Reduction.lean
theorem thm_reduction (H : ClassicalInputs) (c : Fin 6 → H.ek.K)
    (hEK : H.ek.deltaE c ≠ 0) (hsin : ∀ p hp hsplit hpS, p ∉ H.ek.supp c → SinnottHyp …) :
    (∀ p hp hsplit hpS, p ∉ H.ek.supp c → H.ek.v p (H.ek.deltaE c) = 1 →
       IsPUnit c2tilde ∧ MuZero Lp ∧ lambdaAn Lp = 2 ∧ Subsingleton ShaDual)
    ∧ ConjStrong H
```

Front of the `thm_reduction` proof (replaces `resultant_link`):

```lean
have hval' : H.ek.v p (∏ t ∈ H.ek.D, H.ek.Fc c t) = 1 := by
  rw [← H.ek.deltaE_def c]; exact hval
have hfac := Resultant.forall_eq_one_of_prod_eq_one (H.ek.v p) H.ek.D (H.ek.Fc c)
  (hsin p hp hsplit hpS hsupp).integral hval'
have htr : D.katz.traceClass ≠ 0 := (hsin p hp hsplit hpS hsupp).nonvanishing hfac
```

Everything from `htr` downstream is lifted verbatim.

Non-anomality route replacing `h5`:
`isPUnit_one_sub_alphaInv_iff D.analytic.alpha_root |>.mpr (H.notAnomalous p …)`
then `isPUnit_c2tilde_iff` (NOT `_of_split`).

Toy `notAnomalous`: both toys have `ap = 2 * s.a` with `1 ≤ s.a` and `2 * s.a < p`
(`Toy.Setup.ha_pos`, `Toy.Setup.ha_lt`), so `(2a : ZMod p) = 1` would give
`p ∣ 2a − 1` with `0 < 2a − 1 < p`. No toy `ap` needs changing.

## Progress log

- (start) nothing written yet; all files read.

- **Step 1 DONE** `Interface/Katz.lean`: `deltaE_local`/`NonvanishingOnDE`/`resultant_link`
  deleted; `SinnottHyp p Lp Kd P c` with `integral`/`presentation`/`nonvanishing`.
  Added `import FinShaRank2.Interface.EK`. Builds.
- **Step 2 DONE** `Interface/Global.lean`: `PrimeData p hsplit torsSqOverTam` (deltaE param
  and `deltaE_tie` gone); `ClassicalInputs` = `S`, `ek`, `torsSqOverTam`, `torsSqOverTam_eq`,
  `dataAt`, `notAnomalous`. `notAnomalous` needs `letI : Fact p.Prime := ⟨hp⟩` in its own
  type before `(dataAt …).analytic` elaborates. `S` docstring now lists all five `eq:Sexc`
  clauses. Builds.
- **Step 3 DONE** `Statements.lean`: `HorizontalControl`; `PrimeData.c2tilde {tst : ℚ}`;
  `ConjStrong` is `∃ δ Sig, δ ≠ 0 ∧ ∀ p … p ∉ Sig → H.ek.v p δ = 1 → IsPUnit c2tilde`.
  `rmk:normalisation`(iii) → `rmk:integrality`. `lake build FinShaRank2.Statements` green.
  NOTE: run `lake build <module>` not `lake env lean <file>` — the latter reads stale oleans.
- **Step 4 DONE** `Main/Consequence.lean`: `h5` gone from `prop_consequence`; new bridge
  `ClassicalInputs.isPUnit_one_sub_alphaInv` (notAnomalous + `alpha_root` →
  `IsPUnit (1 − α⁻¹)`); step 1 now calls `isPUnit_c2tilde_iff`, not `_of_split`.
  Stale `Kernel.Normalization.eq_five_or_thirteen_le` reference removed with the `h5`
  section. Builds.
- **Step 5 DONE** `Main/Dictionary.lean`: needed no edit at all; builds unchanged.
- **Step 6 DONE** `Main/Reduction.lean`: new `thm_reduction (H) (c) (hEK) (hsin)` with
  conclusion `(∀ p … → IsPUnit ∧ MuZero ∧ lambdaAn = 2 ∧ Subsingleton) ∧ ConjStrong H`.
  Front of proof = `deltaE_def` + `Resultant.forall_eq_one_of_prod_eq_one`; tail from
  `hres` verbatim except step 6 (`isPUnit_c2tilde_iff` + `isPUnit_one_sub_alphaInv`).
  `ConjStrong` witnessed by `⟨H.ek.deltaE c, H.ek.supp c, hEK, …⟩`. Builds.
  NEXT: Toy/ layers (need a built home for `toyEK`), then AxiomAudit.
- **Steps 7–8 DONE.** New file `FinShaRank2/Toy/EK.lean` (`Toy.toyEK` + toy API, lifted
  from `Scratch/R1gammaWork.lean`), imported by `Toy/Trivial.lean`, `Toy/ShaTrivial.lean`
  and the root module. `Toy/{Katz,ShaKatz}.lean` lost the three retired fields;
  `Toy/{Trivial,ShaTrivial}.lean` lost `deltaE`/`deltaE_tie` and gained `ek`,
  `notAnomalous`. `Toy.Setup.ap_ne_one` (new, `Toy/Analytic.lean`) discharges
  `notAnomalous` in BOTH toys — no toy `ap` changed. `AxiomAudit` +3 names.
- **GREEN 2026-08-29:** `lake build` 8740 jobs, `./scripts/audit.sh` = AUDIT: PASS,
  80 audited declarations, allowlist still empty.
- Remaining: sweep stale prose references to the retired fields; verify epistemic split
  by grep.

## R2a COMPLETE — 2026-08-29

`lake build` 8740 jobs green. `./scripts/audit.sh` = `AUDIT: PASS`, 80 audited
declarations (77 + `Toy.toyEK`, `Toy.Setup.ap_ne_one`,
`ClassicalInputs.isPUnit_one_sub_alphaInv`). Allowlist empty, no sorry/admit/native_decide.
`ToyTrivial` and `ToySha` both still elaborate as `ClassicalInputs`;
`toySha_conclusions_fail`, `interface_does_not_force_sha_trivial`,
`toySha_fails_c2_5_certificate` all still prove.

Loose ends left for R2c:
- `blueprint/src/content.tex:78` still says `\lean{FinShaRank2.HorizontalVanishing}`; the
  declaration is now `HorizontalControl`. Not touched (blueprint is out of scope for R2a).
- The `linter.style.haveILetI` warnings are unchanged in number and location.
- `Kernel/Normalization.lean` and `Main/Consequence.lean` still carry `rmk:normalisation`
  references that R2c will retarget.
