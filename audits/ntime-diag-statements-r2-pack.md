# External audit pack — C1-E's statements, round 2: the guessed-budget middle rung (PR #121)

Campaign: the Arora-Barak chapters 3-4 plan, C1 (the nondeterministic time hierarchy, [AB09, Theorem
3.2] [Coo72]). Round 1 of this statement gate (`audits/ntime-diag-statements-findings.md`, verbatim)
returned **FAIL 0/1/2/1**. It found the stages, the stage query and both contracts' statements true
and sufficient. Its major was in `exists_diagonalizer`'s proof sketch. The resolutions are in
`audits/ntime-diag-statements-resolutions.md`.

- **The user's rulings** (2026-10-17):
  - finding 1: **the guessed budget**, the alternative named in C1's design §3.6;
  - **R's prefix clause stays** in `exists_ndInterpreterCore`'s statement. After the repair it has
    no consumer.
- **The head:** `lean/ntime-diag` at `0a5878ed`, two commits on round 1's `13f52659`:
  - `2738e9da` merges the campaign tip, which has #119 and #120. It brings no Lean change to the
    two files of this PR.
  - `0a5878ed` applies the maintainer review's patch unchanged
    (`audits/evidence/c1/c1e/pr/r2/r2-ntimediag.patch`). It touches only
    `Diagonalization/NTimeDiagonalizer.lean`: `exists_diagonalizer`'s docstring sketch, and two
    new lemmas.

| Round-1 finding | Repair in round 2 |
|---|---|
| 1 (major): the sketch used R's prefix clause in an old form; the gated clause's `|x|` term carries a per-code constant that a uniform `K` cannot absorb | The middle rung guesses a nominal budget `b`, with the width of `bits (g n)`. It rejects unless `b ≤ g n`, normalizes `b` to `bits b`, and runs R on `⟨⟨bits b, α⟩, 1^{n + 1}⟩` with the stream `s`, `|s| = g n`. Completeness takes `b = t'` and uses R's **total-time clause** `T ≤ C_R·(b + 1)`. Soundness uses `AcceptsWithin.mono` from `b` to `g n`. |
| 2 (minor): `K` was both the body allowance and the physical coefficient | The "**Time.**" paragraph separates them: the body allowance is `g n`; the clock costs at most `7·(g n + 1)` physically; setup is `P·(g n + 1)`, dispatch `P'`; `K = P + 7 + P'` |
| 3 (minor): `stage` for `n ≤ 2` and `query` off its guard had no published equation | `stage_of_le_two`, `query_of_not_guard` (proved, standard axioms), listed in Main results |
| 4 (note): no PR body, no `TimeHierarchy/Diagonal.lean` | Both are in this bundle. `Diagonal.lean` is blob `e8087e57` at both heads. |

**No statement changes.** `query`, `exists_queryTM` and `exists_diagonalizer` keep their round-1
statements, and so does every other declaration.

- **Evidence:** `audits/evidence/c1/c1e/`:
  - round 1's `pr/`;
  - round 2's `pr/r2/` (the patch, the elaboration, the freeze, the lint, the screen, the replay
    script, log and static check, the PR body);
  - round 1's PR body, `pr/pr-body.md`;
  - the design note, corrected for round 2.
- **C1's design** (`audits/evidence/c1/C1-design.md`) is corrected in §3.6 and in D6 and D9.

## Brief for the auditor

1. **Finding 1's repair is sound.** Check the middle rung as now sketched.
   - **Soundness:** an accept implies coded acceptance of `1^{n + 1}` within `g n`. Consider in
     particular a guess `b` below every acceptance time, and the test `b ≤ g n` as what gives R's
     hypothesis `t ≤ |s|`.
   - **Completeness:** `C·(t' + 1) ≤ g n` gives an accept, with `C ≥ C_R` per code. Check that only
     R's total-time clause is used, and that it has no `|x|` term (`NDCodeSimulator.lean`,
     `exists_ndInterpreterCore`).
   - **The rewrite's cost:** the guess, the test, the normalization to canonical `bits b` and the
     re-pairing must fit in `O(g n + 1)` for a uniform constant, using `n ≤ g n` as
     `exists_queryTM` does. Is the normalization needed, given R's input
     `pairEncode (pairEncode (Nat.bits t) α) x`?
   - **The top rung** is unchanged. Does it still fit the same allowance?
2. **Finding 2's ledger.**
   - Is `K = P + 7 + P'` a uniform bound on every branch? Here `P` is the code-independent setup,
     including the budget's phases; the clock's cost is at most `5d + 2|bits d| + 2 ≤ 7(d + 1)` at
     `d = g n` (`Build/StepClock`, `exists_stepClockTMVia`); and `P'` is the dispatch.
   - Are the body allowance and `K` now distinct quantities?
3. **Finding 3's lemmas.**
   - Are `stage_of_le_two` and `query_of_not_guard` correct?
   - Together with `stage_spec`/`stage_eq` and `query_eq`, do they cover every input?
4. **The statements are unchanged** (`pr/r2/freeze.txt`). The freeze tool's "UNAUTHORIZED BODY
   CHANGE: exists_diagonalizer" is the docstring; check that the declaration's code is identical.
5. **The prefix-clause ruling.** R keeps a clause with no consumer. Is that acceptable for a frozen,
   gated statement? Or does an unused clause in a contract mislead its fill? Recommend, without
   reopening R's gate.
6. **Records:** do the resolutions, the corrected design notes, this pack and the PR body agree with
   the evidence? The PR body as of round 2's head is `pr/r2/pr-body.md` (round 1's:
   `pr/pr-body.md`).

## Repository-side attestations (verify or challenge)

- **Elaboration** (against `oleans-lndiag`, round 1's replay): 0 errors. 2 warnings, the two
  contracts' `sorry`s. The two new lemmas use `propext`, `Classical.choice` and `Quot.sound`
  (`pr/r2/logs/`).
- **Freeze:** 20 → 22 publics, the two added; no statement changed.
- **Lint:** `Diagonalization/` 0 FAIL, 1 WARN (`EXPCOM`, unrelated), unchanged.
- **Screen** (the 7-file population, which includes `TimeHierarchy/Diagonal.lean`): 48 → 49
  declarations, 6 → 6 pairs, 1,814 characters, no new pair (`pr/r2/screen-head.txt`; the base is
  round 1's `pr/screen-head.txt`).
- **Replay:** `replay-lndiag2.sh`, 2 modules, chained from `oleans-lndnf` (the tip's snapshot).
  **Passed (user, 2026-10-17):** 2 of 2 at `0a5878ed`, 0 failed (`pr/r2/replay-lndiag2.log`); the
  sorry counts equal a static count (0 mismatches, 2; `pr/r2/replay-lndiag2-static.txt`). The
  snapshot `oleans-lndiag2` is the tip plus #121's round 2.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/ntime-diag-statements-r2-findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named
`ntime-diag-statements-r2-findings.md`** (the findings table and the verdict line, no other
wrapping), and also paste its content in your reply.
