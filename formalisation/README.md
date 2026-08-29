# FinShaRank2

Companion code for a paper on p-adic L-functions of CM elliptic curves and
the Tate–Shafarevich group: a Lean 4 formalization of the paper's main
statements, together with the PARI/GP computations behind its numerical
results.

This repository holds **all the code and data**; the manuscript itself lives
elsewhere and is deliberately not part of this repo.

The manuscript's own discussion of this formalization (v1 §1.9 and Appendix B)
was removed in the paper's v2 rewrite of 2026-08-25; `FORMALIZATION.md` here is
now the canonical account of what is machine-checked, what is assumed, and how
to audit it — see the dated note at its head for what changed and why.

## Contents

| Path | What it is |
|---|---|
| `FinShaRank2/` | Lean 4 sources: interface, kernel lemmas, main theorems |
| `blueprint/` | Lean blueprint (builds locally, see below) |
| `scripts/` | `audit.sh`, the audit gate for the Lean project |
| `computations/` | PARI/GP scripts for the scan, the anchors, and δ_E |
| `data/` | Their outputs, including the 508-prime scan and the δ_E results |

The GP scripts read and write via paths relative to their own directory
(`../data/...`), so run them from inside `computations/`.

## Build

```sh
lake exe cache get   # fetch prebuilt mathlib oleans (mathlib v4.32.0, see lean-toolchain)
lake build
```

## Audit gate

```sh
scripts/audit.sh
```

Checks (from a clean `lake build`): no `sorry`/`admit` outside
`FinShaRank2/Scratch/` (modulo `scripts/sorry-allowlist.txt`, **currently
empty** — so no incomplete proof is tolerated anywhere in the imported tree),
and a clean axiom trace (`propext`, `Classical.choice`, `Quot.sound` only — no
`native_decide`) via `FinShaRank2/AxiomAudit.lean`.

## Blueprint

Built locally via `blueprint/bp pdf` (→ `blueprint/print/print.pdf`) and
`blueprint/bp web` (→ `blueprint/web/`); see `blueprint/README.md`. Not
published (no GitHub Pages on this private repo).

## Docs

**`FORMALIZATION.md` is the referee-facing guide to this formalization** and
the right place to start: what is proved, what is assumed on citation, what is
certified numerically, what is descoped and why, and how to re-run every check
in this repo yourself. Its §6 reproduces the build and audit transcripts, and
§6.6 gives a short metaprogram that mechanically confirms the epistemic split
— that the two anchor corollaries' proofs never touch the conjectural surface.

The task roadmap (`TASK_BOARD.md`) is maintained outside this repo.
