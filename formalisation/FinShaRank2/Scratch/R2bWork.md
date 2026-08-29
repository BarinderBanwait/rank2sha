# R2b — Theorem A (cor_horizontal), ConjEK, thm_reduction_of_conjEK

**COMPLETE 2026-08-29.** `lake build` exit 0 (8741 jobs); `./scripts/audit.sh`
`AUDIT: PASS`, **82** audited declarations; allowlist still empty. Not committed
(PM commits). No branch created.

## Files touched
- `FinShaRank2/Statements.lean`      — added `ConjEK`; module docstring amended
- `FinShaRank2/Main/Horizontal.lean` — NEW; `cor_horizontal`
- `FinShaRank2/Main/Reduction.lean`  — added `thm_reduction_of_conjEK`; firewall ¶ amended
- `FinShaRank2.lean`                 — `import FinShaRank2.Main.Horizontal` (after Consequence)
- `FinShaRank2/AxiomAudit.lean`      — `-- R2b` block, two names; "Amended (R2b)" ¶

## Final signatures
```
def ConjEK (H : ClassicalInputs) : Prop :=
  ∀ c : Fin 6 → H.ek.K, c ≠ 0 → H.ek.deltaE c ≠ 0

theorem cor_horizontal (H : ClassicalInputs) (hweak : ConjWeak H) :
    HorizontalControl {p | p.Prime ∧ p % 4 = 1}
      (fun p ↦ ∀ (hp : p.Prime) (hsplit : p % 4 = 1) (hpS : p ∉ H.S),
        have : Fact p.Prime := ⟨hp⟩
        Subsingleton (H.dataAt p hp hsplit hpS).selmer.ShaDual)

theorem thm_reduction_of_conjEK (H : ClassicalInputs) (c : Fin 6 → H.ek.K) (hc : c ≠ 0)
    (hconj : ConjEK H) (hsin : …as thm_reduction…) : …as thm_reduction… :=
  thm_reduction H c (hconj c hc) hsin
```

## One change to the sketch
The sketch statement of `cor_horizontal` does **not** elaborate as given:
`failed to synthesize Fact (Nat.Prime p)` at the `.selmer` projection. `PrimeData`
takes `[Fact p.Prime]`, so its projections carry it instance-implicitly and Lean
synthesises rather than unifies; inside the predicate `p` is a bound variable with no
instance in scope. Fixed by `have : Fact p.Prime := ⟨hp⟩` inside the predicate — the
same device `ConjWeak`/`ConjStrong` use, spelled `have` rather than `letI` so the
`linter.style.haveILetI` warning count does not grow. Nothing else changed.

## Epistemic split — verified by grep
`ConjEK` as a code term occurs exactly twice: `Statements.lean:160` (the def) and
`Main/Reduction.lean:235` (`hconj : ConjEK H`). Every other hit is docstring prose.
`cor_horizontal`'s elaborated statement mentions `ConjWeak` and nothing else
conjectural — no `ConjEK`, no `ConjStrong`, no `SinnottHyp`.
`#print axioms` on both new theorems: `[propext, Classical.choice, Quot.sound]`.

## Not done (out of scope, flagged to PM)
`project_management/TASK_BOARD_RESYNC.md` was not edited: R2b's row still reads ☐
and "Resume here" still points at R2b.
