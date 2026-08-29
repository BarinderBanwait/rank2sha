import Mathlib

/-!
# R1β checkpoint — landed 2026-08-29

All three deliverables of task R1β are in their final files; nothing is left here.

* `FinShaRank2/Kernel/Resultant.lean` — `Resultant.forall_eq_one_of_prod_eq_one`,
  `Resultant.prod_ne_zero_of_prod_eq_one`.
* `FinShaRank2/Kernel/Orbit.lean` — `Orbit.prod_mem_range_algebraMap`,
  `Orbit.forall_eq_zero_of_exists_eq_zero`.
* `FinShaRank2/Kernel/Anomalous.lean` — `anomalous_iff_five`, plus
  `eq_five_or_thirteen_le` moved in from `FinShaRank2/Kernel/Normalization.lean`
  (unchanged name and docstring).

All five new declarations are registered in `FinShaRank2.lean` and in
`auditedDecls` of `FinShaRank2/AxiomAudit.lean`; the audited count is 73.
-/
