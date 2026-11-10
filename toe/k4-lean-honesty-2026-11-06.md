# K4 Lean honesty (2026-11-06)

Carried onto live Cookies `[local path redacted]/toe` branch `toe-unification` as commit `73d313a7248acf8b5d40d864853fa0dce981be59` (not pushed). Parent was `47477c7`. Subject: Record K4 Lean honesty: geometric English is not kernel-checked. The uncommitted L7 file `results/proof_bounds.json` and the L7 logs were left unstaged.

## What changed

- `CORE.md` K4 stays [P]. The evidence cell no longer says the geometric English is a finite predicate kernel-checked in Lean; it now says Lean certifies only encoded finite predicates and that this geometric English is not a kernel-checked theorem statement.
- Ledger notes appended, labels unchanged, on CH-VII-001 [P], CH7b-P1-forced-curvature [P], and CH-VII-029 [C]. Claim count remains 1329 (P373 C244 X118 E356 F191 A47).
- `SCORECARD.md` gained a section "K4 Lean honesty (2026-11-06)".

## What was checked

The file `[local path redacted]/-/certificates/Phase7Counting.lean` was read (sha256 `38453c1d7aeb34ce02c072f374924b9631f835db5f2624be36b8b51acd82076c`). That hash matches the `sha256_prefix_of_repo_file` `38453c1d7aeb34ce` in `toe/inventory/lean_recheck.json`. The file is not in the toe tree (`toe/certificates/Phase7Counting.lean` does not exist).

The kernel-checked theorems used for the K4 count are encoded predicates on an encoded `trivial` test:

- `octant_bound`: `countTriv pc pv s ≤ bound s` for every encoded centre permutation, octant permutation, and admissible octant sign vector
- `total_bound`: the listed bound values sum to 9 (`(octantSigns.map bound).foldl (· + ·) 0 = 9`)
- `bound_attained`: there is a centre permutation such that each octant sign separately attains its bound for some octant permutation

The geometric English of K4 (every geometry-compatible frame field has ≥ 12 of the 21 centre-octant two-cycles non-trivial in every level-1 supertile) and the docstring step from those bounds to "≥ 12 of 21" are not themselves Lean theorem statements.

## What was not done

No label changes. No Kato cite and no author-list ruling. `main.tex` was not edited. CH-VI-008 (the proper-frame nine-forced count) was left as written; its notes already point at CH-VII-001.
