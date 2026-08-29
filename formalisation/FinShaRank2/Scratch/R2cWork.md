# R2c / R2d work log

Opened 2026-08-29. Resilience record: append after each file.

## Sub-tasks

1. Paper title: old "Horizontal rigidity for second jets of Katz p-adic L-functions,
   with applications to the Tate--Shafarevich group in rank two" ->
   "Second derivatives of $p$-adic $L$-functions and the Shafarevich--Tate group of
   rank-two CM elliptic curves". ("Katz" dropped deliberately.)
2. `Tate--Shafarevich` -> `Shafarevich--Tate`.
3. `rmk:normalisation` -> `prop:normalisation` (normalisation statement) or
   `rmk:integrality` (integrality, formerly (iii)). Route each site individually.
4. Retired labels: `cor:sha5`, `cor:sha13`, `eq:match5`, `eq:pred13`, `sec:anchor`,
   `ssec:pred13`, `Certificates`. Rewrite the sentence.
5. Stale internal file references (`Kernel/Normalization` for `eq_five_or_thirteen_le`,
   `Interface/Certificates`, `Main/Corollaries`).
6. `linter.style.haveILetI` warnings.
7. R2d: delete stale `Scratch/` files T14Check, T15Chain, T26Check, T34Work,
   PMVerifyW5, PMVerifyT41.

## Progress

- Title (8 sites) DONE: Defs, Statements, Interface/{Analytic,Global,Heights,Katz,Iwasawa},
  Kernel/{Normalization,Decoupling}.
- Shafarevich--Tate: done in the same files + Kernel/ShaEndgame.lean:55.
- rmk:normalisation -> prop:normalisation: Defs (x3), Kernel/Normalization (x9),
  Kernel/Anomalous (x2).
- Kernel/Normalization retired-material paragraph rewritten (CLS subsumption named).
- BUILD GREEN after batch 1.
- haveILetI sites, fresh: LambdaModule 151,153,155,174,175,177; Toy/Iwasawa 102,128;
  Toy/ShaIwasawa 286,323; Toy/ShaTrivial 133,182; Main/Reduction 139,166,210. (15, not 13.)
- Batch 2 DONE, build green: Interface/Analytic (rmk:normalisation(iii) -> rmk:integrality,
  x3), Main/Consequence (x7 incl. the cor:sha5 sentence and the stale v1 block quote of
  prop:consequence, now Theorem B's v2 statement), Main/Dictionary (x2),
  Main/Reduction (x1), Toy/ShaTrivial (eq:match5 x3), AxiomAudit (x2).
- Acceptance grep clean outside Scratch/.
- NEXT: haveILetI sites, then R2d.
- haveILetI: all 15 flagged sites changed to `have`; build green, ZERO warnings.
  No site needed to keep letI. In-statement letI (Reduction 123/128/136/238/243,
  ShaTrivial 129/156/183) untouched -- frozen statements, not flagged.
- Kernel/ShaEndgame.lean:44 rewritten (cited Scratch/T15Chain.lean, now deleted).
- R2d: deleted T14Check, T15Chain, T26Check, T34Work, PMVerifyW5, PMVerifyT41.
  NameCheck.lean compiles at v4.33.1 (lake build FinShaRank2.Scratch.NameCheck);
  its stale pin (v4.32.0) and stale `cd formal` path fixed.
- Systematic label cross-check against paper/v2 \label{} set: found and fixed
  sec:testbed -> ssec:testbed (5 sites), app:anchor (2 sites, Heights.lean;
  appendix dropped in v2), rmk:normalisation in Scratch/T31Work.lean.
  Every paper label in the Lean tree now resolves in v2.
- Scratch/T31Work.lean:27 pointer to the deleted T15Chain rewritten.
- FINAL: lake build green (8741 jobs), 0 warnings; AUDIT: PASS, 82 decls;
  acceptance greps empty. R2c + R2d complete.
