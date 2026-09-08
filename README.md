# Second derivatives of $p$-adic $L$-functions and the Shafarevich–Tate group of rank-two CM elliptic curves

Supporting material for the paper of that name, by Barinder S. Banwait.

There are two directories.

## `code`

The computations reported in Part 2 of the paper: the regulator scan of §7.4,
the control on the normalisation of §7.5, the unit condition by modular symbols
of §7.8, and the Eisenstein–Kronecker brackets of §8. PARI/GP and SageMath
scripts, and the raw output of every run.

Every number quoted in Part 2 traces to a script and to an output file, both
committed here. `code/README.md` gives the map from number to script to file, and
`code/build.sh` checks a machine for the required software and runs a smoke test.

## `formalisation`

A Lean 4 formalisation of the paper's main statements, together with a blueprint
linking the informal argument to the Lean declarations. `formalisation/README.md`
is the guide: what is proved, what is assumed on citation, how to build it and
re-run the audit, and a worked example of checking one assumed field against the
literature it cites. The derivation of the main theorem from the assumed
classical inputs has also been checked with Lean's `comparator`; §2 of that
README records the run. The blueprint is published at
<https://barinderbanwait.github.io/rank2sha/blueprint/>.

---

A link to the paper will be added here on release.
