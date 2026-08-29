# R0b — mathlib bump v4.32.0 → v4.33.1 (working note)

Target pin:

- `lean-toolchain` = `leanprover/lean4:v4.33.1`
- `lakefile.toml` `rev = "v4.33.1"`, mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`

Starting point: `lean-toolchain` = `leanprover/lean4:v4.32.0`, `rev = "v4.32.0"`,
mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997`. Last green commit `abcab66`.

Out of scope: `formalisation/README.md`, `blueprint/`, `formalisation/legacy/`,
`FinShaRank2/Scratch/`, `scripts/audit.sh`.

## Status

- [x] pin edited
- [x] `lake update mathlib`
- [x] `lake exe cache get` (post-update hook already primed; 8690 files, nothing downloaded)
- [x] `lake build` green, 8736 jobs
- [x] `./scripts/audit.sh` PASS, 68 audited declarations
- [x] §4 API re-verification — all pass, see below
- [x] `NOTES/MathlibAudit.md` updated (header re-verification note; §3 items 9–11)
- [x] `FORMALIZATION.md` pin updated (§1.2, §6.1, and the §6.2–§6.4 transcript counts)

R0b is complete. Not committed — the PM commits.

Build was green before any source edit. The only fallout was two deprecation
warnings; there were no errors.

## Files repaired

- `FinShaRank2/Kernel/LambdaModule.lean:72` — `Prime.not_unit` deprecated in v4.33
  (`@[deprecated (since := "2026-08-02")] alias not_unit := not_isUnit`). Replaced
  `X_prime.not_unit` with `X_prime.not_isUnit`.
- `FinShaRank2/Kernel/TsqUnit.lean:130` and `FinShaRank2/Toy/ShaTrivial.lean:94` —
  `Set.mem_setOf_eq` deprecated in v4.33 (`setOf` renamed to `Set.ofPred`;
  `@[deprecated (since := "2026-07-09")] alias mem_setOf_eq := mem_ofPred_eq` in
  `Mathlib/Data/Set/Operations.lean:82`). Replaced with `Set.mem_ofPred_eq`, which has
  the identical statement `(x ∈ {y | p y}) = p x`.

## Semantic changes observed

- New mathlib linter `linter.style.haveILetI` (`Mathlib/Tactic/Linter/HaveILetI.lean`,
  added in mathlib #41657, absent at v4.32.0, `defValue := true`). It flags `haveI`/`letI`
  in a proof of a `Prop`. Thirteen sites in the tree emit it: `Kernel/LambdaModule.lean`
  (151, 153, 155, 174, 175, 177), `Main/Reduction.lean` (122, 147, 191),
  `Toy/Iwasawa.lean` (102, 128), `Toy/ShaIwasawa.lean` (286, 323),
  `Toy/ShaTrivial.lean` (130, 179). Warnings only, not errors. Left alone: those files
  are on the R2a/R2b rewrite list and churning them now would collide with peer sessions.
- No simp-set regression, no defeq loss, no instance resolving differently. Both §2
  workarounds of `NOTES/MathlibAudit.md` still compile verbatim, including the `simp`
  call `simp [RingHom.mem_ker, Ideal.mem_span_singleton, X_dvd_iff]`.
  `FinShaRank2/Scratch/NameCheck.lean` compiles with 0 errors against the new pin.
- `lake update mathlib` moved the transitive pins as well. One to note:
  `lean4-cli` `inputRev` is now `v4.33.0`, not `v4.33.1` — that is mathlib v4.33.1's own
  choice, recorded in `lake-manifest.json`, not ours.

## §4 API re-verification (all against `.lake/packages/mathlib` at v4.33.1)

Signatures below are `#check` output.

1. `Finset.prod_eq_one_iff_of_le_one'` — present, `Mathlib/Algebra/Order/BigOperators/`
   `Group/Finset.lean:213`, shape unchanged:
   `[CommMonoid N] [PartialOrder N] {f : ι → N} {s : Finset ι} [MulLeftMono N] :`
   `(∀ i ∈ s, f i ≤ 1) → (∏ i ∈ s, f i = 1 ↔ ∀ i ∈ s, f i = 1)`.
2. Root `map_prod` — present, `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:366`,
   `[CommMonoid M] [CommMonoid N] {G} [FunLike G M N] [MonoidHomClass G M N] (g : G)`
   `(f : ι → M) (s : Finset ι) : g (∏ x ∈ s, f x) = ∏ x ∈ s, g (f x)`. Still `@[simp]`.
3. `Valuation` — still `structure Valuation extends R →*₀ Γ₀`
   (`Mathlib/RingTheory/Valuation/Basic.lean:80`), and
   `instance : ValuationClass (Valuation R Γ₀) R Γ₀` (line 126) with
   `class ValuationClass … extends MonoidWithZeroHomClass F R Γ₀` (line 87).
   `map_prod v f s : v (∏ i ∈ s, f i) = ∏ i ∈ s, v (f i)` elaborates.
4. `AddValuation` — still **no** product/sum lemma. `AddValuation.map_prod` and
   `AddValuation.map_sum` are unknown constants; no `prod`/`∏` occurs anywhere in the
   `AddValuation` namespace. What exists is `map_le_sum`/`map_lt_sum`/`map_lt_sum'`,
   bounds on `v (∑ i ∈ s, f i)` — the additive analogue of `map_add`, not of `map_prod`.
   All three were already present at v4.32.0. The design decision stands.
5. `InfiniteGalois.mem_range_algebraMap_iff_fixed` — present,
   `Mathlib/FieldTheory/Galois/Infinite.lean:114`,
   `[IsGalois k K] (x : K) : x ∈ Set.range (algebraMap k K) ↔ ∀ f : Gal(K/k), f x = x`.
   `IsGalois.mem_range_algebraMap_iff_fixed` — present, `Galois/Basic.lean:340`, same
   conclusion with the extra `[FiniteDimensional F E]`.
6. `MulAction.exists_smul_eq (M) (x y : α) : ∃ m : M, m • x = y`
   (`Mathlib/Algebra/Group/Action/Pretransitive.lean:74`, `M` explicit);
   `class MulAction.IsPretransitive (M α) [SMul M α] : Prop` (same file, line 60);
   `MulAction.toPerm [Group α] [MulAction α β] (a : α) : Equiv.Perm β`
   (`Mathlib/Algebra/Group/Action/Basic.lean:34`);
   `Equiv.prod_comp (e : ι ≃ κ) (g : κ → M) : ∏ i, g (e i) = ∏ i, g i`
   (`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:750`, `[Fintype ι] [Fintype κ]`);
   `Finset.prod_ne_zero_iff : ∏ x ∈ s, f x ≠ 0 ↔ ∀ a ∈ s, f a ≠ 0`
   (`Mathlib/Algebra/BigOperators/GroupWithZero/Finset.lean:60`,
   `[CommMonoidWithZero M₀] [Nontrivial M₀] [NoZeroDivisors M₀]`).
7. `Finset.prod_eq_one_iff_of_one_le'` (line 193) and its `to_additive` sibling
   `Finset.sum_eq_zero_iff_of_nonneg` both present, shapes unchanged. The `to_additive`
   sibling of `prod_eq_one_iff_of_le_one'` is `Finset.sum_eq_zero_iff_of_nonpos`.
