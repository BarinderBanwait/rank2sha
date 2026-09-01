# Second derivatives of $p$-adic $L$-functions and the Shafarevich–Tate group of rank-two CM elliptic curves

Supporting material for the paper of that name, by Barinder S. Banwait.

There are two directories.

## `code`

The computations reported in Part 2 of the paper: the horizontal regulator scan
of §4.3, the $p = 5, 13$ control on the normalisation, and the
Eisenstein–Kronecker computation of §6. PARI/GP and SageMath scripts, and the
raw output of every run.

Every number quoted in Part 2 traces to a script and to an output file, both
committed here. `code/README.md` gives the map from number to script to file, and
`code/build.sh` checks a machine for the required software and runs a smoke test.

## `formalisation`

A Lean 4 formalisation of the paper's main statements, together with a blueprint
linking the informal argument to the Lean declarations. `formalisation/README.md`
is the guide: what is proved, what is assumed on citation, how to build it and
re-run the audit, and a worked example of checking one assumed field against the
literature it cites.

---

A link to the paper will be added here on release.
