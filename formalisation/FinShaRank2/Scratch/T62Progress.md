# T62 golf pass — progress log (agent W8-A)

Scope: `FinShaRank2/Kernel/LambdaModule.lean`, `FinShaRank2/Kernel/Normalization.lean` only.
Baseline: `lake build` green (8687 jobs) at start. LambdaModule 282 lines, Normalization 250 lines.
Lean MCP tools unavailable in this run -> verification is `lake env lean <file>` + `lake build`.

| # | declaration | file | before | after | note |
|---|---|---|---|---|---|
| 1 | `isPUnit_one_sub_alphaInv_of_split` | Normalization.lean | 5 | 3 | `by refine ... ; rcases ... ; two Or branches` -> term mode `Or.symm.imp_right`. `lake build` green. |
| 2 | `isPUnit_c2tilde_iff` | Normalization.lean | 8 | 5 | dropped the intermediate `hnorm` have; `subst` hoisted to top and the `simp only` now closes the `show`n iff directly. `lake build` green. |
| 3 | `isUnit_of_toZModPow_cert` | Normalization.lean | 10 | 8 | inlined single-use `hlt`; dropped `rw [map_mul, map_natCast] at hcert` (already subsumed by the closing `simp only`). `lake build` green. |
| 4 | `eq_five_or_thirteen_le` | Normalization.lean | 5 | 4 | dropped `have h2 := hp.two_le`: `interval_cases` finds the `0` lower bound itself and `omega` kills `p = 0`. `lake build` green. |
| 5 | `pow_X_dvd_le` | LambdaModule.lean | 12 | 1 | hand-rolled cancellation argument replaced by mathlib `pow_dvd_pow_iff X_prime.ne_zero X_prime.not_unit` (same cancellation-only route, no UFD). File elaboration 14s -> 6.6s. `lake build` green. |
| - | `rank_lower_bound` | LambdaModule.lean | 3 | 3 | ATTEMPTED + REVERTED: term-mode `finrank_fin_fun.symm.trans_le ...` typechecks but needs explicit `(R := ℤ_[p]) (n := 2)` and is still 3 lines. Original `have`/`rwa` kept. |
| 6a | `selmer_dual_structure` (tail) | LambdaModule.lean | 10 | 7 | dropped the `hTXbot` / `Submodule.restrictScalars_injective` round-trip: work directly in `TXℤ` and bridge membership with `Submodule.restrictScalars_mem`. Also removes a naked `;`. NOTE: the fully-defeq version (`hmem : ... ∈ TXℤ := Submodule.smul_mem_smul ...`) times out at `whnf` — the explicit `rw [hTXℤ, Submodule.restrictScalars_mem]` bridge is required. `lake build` green. |
| 6b | `selmer_dual_structure` (hinj', hrank') | LambdaModule.lean | 2 | 2 | `by rw [hφ', LinearMap.coe_restrictScalars]; exact hinj` -> `hinj` (defeq); `by rw [← hconv]; exact hrank` -> `hconv ▸ hrank`. Directness wins, two naked `;` removed. `lake build` green. |
| 6c | `selmer_dual_structure` (instance no-ops) | LambdaModule.lean | 4 | 0 | deleted four `haveI ... := inferInstance` lines (`Module.Free`/`NoZeroSMulDivisors`/`Module.Finite`/`IsNoetherian` on the product `C`); typeclass inference finds all four at the use sites. Measured elaboration unchanged (6.67s vs 6.71s). `lake build` green. |
| 6d | `selmer_dual_structure` (hCfin2, nz_i) | LambdaModule.lean | 11 | 8 | `hCfin2`: `rw [finrank_pi_fintype, <- hsum]` + a term-mode `Finset.sum_congr` (was a nested `rw [show ... from ...]`). `nz_i` / `NoZeroSMulDivisors X_mod`: eta-reduced `(fun c x => map_smul _ c x)` to `map_smul _`. NB `Module.finrank_fin_fun` takes `R` EXPLICITLY in this mathlib rev. `lake build` green. |
| 7 | `rank_lower_bound` | LambdaModule.lean | 3 | 2 | now lands: term mode `(Module.finrank_fin_fun ℤ_[p]).symm.trans_le (LinearMap.finrank_le_finrank_of_surjective hπ)` (earlier revert was caused by the explicit `R` argument, not by the idea). `lake build` green. |
| 8 | `quotXpow_linEquiv` (hker) | LambdaModule.lean | 12 | 9 | hoisted the shared `rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]` above `constructor` (it was duplicated, once forwards and once `at hg`), then the forward branch is a single `intro hg m hm` + `simpa`. `lake build` green. |
| 9 | `quotient_collapse` | LambdaModule.lean | 6 | 5 | folded the `intro r hr m _` into the `Submodule.smul_le.mpr` lambda. `lake build` green. |
