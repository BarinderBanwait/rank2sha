# FinShaRank2 — the Lean formalisation

A Lean 4 formalisation of the main statements of *Second derivatives of
$p$-adic $L$-functions and the Shafarevich–Tate group of rank-two CM elliptic
curves*, together with a blueprint linking the informal argument to the Lean
declarations.

This directory holds the Lean project and nothing else. The computer algebra —
the PARI/GP and SageMath scripts behind Part 2 of the paper, and the output of
every run — is in `../code`; see `../code/README.md`. It moved there on
2026-08-29, having previously sat under `computations/` and `data/` here.

The manuscript itself is not part of this repository.

## Requirements

The toolchain is pinned in `lean-toolchain`; `elan` will install it on demand.
If you do not have `elan`:

```sh
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

Nothing else is needed. mathlib is fetched as a prebuilt binary cache, so a
first build takes minutes rather than hours.

## Build

```sh
lake exe cache get   # prebuilt mathlib oleans (mathlib v4.32.0, per lean-toolchain)
lake build
```

## Audit gate

```sh
scripts/audit.sh
```

From a clean `lake build` this checks two things:

- no `sorry` or `admit` outside `FinShaRank2/Scratch/`, modulo
  `scripts/sorry-allowlist.txt`, which is **currently empty** — so no incomplete
  proof is tolerated anywhere in the imported tree;
- a clean axiom trace via `FinShaRank2/AxiomAudit.lean`: `propext`,
  `Classical.choice` and `Quot.sound` only, and in particular no
  `native_decide`.

## Layout

| Path | What it is |
|---|---|
| `FinShaRank2/` | Lean 4 sources: interface, kernel lemmas, main theorems |
| `FinShaRank2/Scratch/` | working files, excluded from the audit gate |
| `blueprint/` | the Lean blueprint |
| `scripts/` | `audit.sh` and the (empty) sorry allowlist |

## Blueprint

Built locally: `blueprint/bp pdf` writes `blueprint/print/print.pdf`, and
`blueprint/bp web` writes `blueprint/web/`. See `blueprint/README.md`. It is not
published, there being no GitHub Pages on this repository.

## Documentation

`FORMALIZATION.md` is the referee-facing guide and the right place to start: what
is proved, what is assumed on citation, what is certified numerically, what is
descoped and why, and how to re-run every check here. Its §6 reproduces the build
and audit transcripts, and §6.6 gives a short metaprogram confirming that the two
anchor corollaries' proofs never touch the conjectural surface.

The paper's own discussion of this formalisation (v1 §1.9 and Appendix B) was
removed in the v2 rewrite of 2026-08-25; `FORMALIZATION.md` is now the canonical
account. See the dated note at its head for what changed and why.
