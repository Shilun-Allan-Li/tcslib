# External audit pack — C1-E continuation 1: the exhaustive replay (PR #136, a fill gate)

Campaign: the Arora-Barak chapters 3-4 plan, C1 (the nondeterministic time hierarchy, [AB09,
Theorem 3.2]). The fill brief E cont1 (`campaign/fills/c1/briefs/c1-fill-exhaustive-cont1.md`)
targets **`Turing.FinNDTM.exists_exhaustiveDecider`** (`TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean`):
one deterministic machine `E` that decides a fixed NDTM's acceptance within `C·2^{C·(T + 1)}`
steps wherever every branch halts within `T` ([AB09, §3.2, proof of Theorem 3.2]), with `C`
depending only on the machine and no `|z|` term. Through the proved
`Turing.ndAcceptsWithin_decider_of_universal` (`BF := E(UN)`), the exponential decider
`Turing.exists_ndAcceptsWithin_decider` then has exactly one open dependency, the universal NDTM.

**A complete fill (1/1).** The worker's report is `campaign/fills/c1/reports/exhaustive-2-REPORT.md`;
the maintainer's review is `campaign/fills/c1/reviews/exhaustive-cont1/REVIEW.md` ("complete; land,
with three small maintainer edits").

**The head:** `lean/c1-exhaustive-fill` at `75b2e94c`: the review's head `b5629b91` (on the campaign
branch at `3638965b`) with the campaign branch merged in after #132 (`e9e97970`; no conflict, the
PR's own files byte-unchanged):
- the worker's 16 commits `1eabca5e..041c82ab`, cherry-picked from its verified bundle; the first
  adds the three authorized imports alone. They add 183 private `xr_` declarations and no public
  one;
- `b5629b91`, the maintainer's (the review's F1 and F2): `xr_branch_inputPos_le` closes by
  `simpa [NDTM.initCfg_eq]` instead of simp's unfolding of `NDTM.initCfg` (rule 10); the private
  section's header in public-facing terms; the module's main results; `ClassNP`'s contents line and
  `exists_ndAcceptsWithin_decider`'s docstring no longer call the replay pending.

**The user's rulings (2026-10-18):**
- **The route's one deviation is accepted** (the review's F4). The brief's obligation 4 returned
  the heads to `0` between replays; the proof leaves them in place and uses translation invariance
  (`xr_runWith_shift`), clearing radius `2L` around each displaced head. It is sound because the
  replay lemma holds from any configuration; the worker disclosed it.
- **Proof sketches follow up** (the review's F3): 24 private proofs over 20 lines have no "Proof
  sketch" (policy §3). The six main ones (`xr_passTM_run`, `xr_testTM_run`, `xr_clearTape_host`,
  `xr_cycle_host`, `xr_depth_host`, `xr_run_host`) are written on `lean/c1-exhaustive-sketches`
  (docstrings only, 0 errors), whose PR opens after this one merges.
- **File size:** 3,245 lines; file size alone is not a driver.

## Brief for the auditor

1. **Faithfulness.** Does the proof establish the frozen statement (`evidence/freeze.txt`: 2 → 2
   public, 0 → 183 private, the only body change the target's): for every input and every `T`
   with every branch halting within `T`, `E` answers acceptance within `C·2^{C·(T + 1)}` with
   `C = 18·N.k + 41`? Is the answer the one at the first all-halting depth `L*`, and does that
   agree with acceptance at every promised bound `T ≥ L*` (`xr_accepts_iff_of_halts`)?
2. **The ledger** (`xr_ledger`, `xr_run_host`): a cycle costs at most `(18 N.k + 19)(L + 1)`, a
   depth `2^L` cycles plus the deepening's `6L + 11`; the sum over the depths up to `L*`. Is the
   constant right, independent of `|z|`, and is the input's length truly absent from every phase's
   cost?
3. **The deviation (accepted).** With the heads left in place, is the radius-`2L` clear around the
   displaced heads (six ruler passes, `xr_clearTape_host`) enough for every later replay, and is
   translation invariance (`xr_runWith_shift`, `xr_stepWith_shift`) proved for the steps the replay
   takes?
4. **Rule 10.** The review's 31-definition seal with controls at both ends of the private section,
   the F1 fix, and the inspection of the proofs' `rw`/`simp` arguments. Does any step still close
   only because another file's definition reduces?
5. **Duplication.** The screen: 297 → 428 declarations, 106 → 228 pairs, the 122 new pairs all
   inside the file, none touching the brief's hazards. The review's dedup notes (its decision 4:
   `xr_val` against `counterValue`, `xr_bufferTape_neg` against `FinTM.bufferTape_of_neg`, the
   replay exits' prelude) are for the user's dedup window. The private `xr_rewindTM` is a rewind
   over the file's own state type; the public rewind row (PR #138) came later and would need a
   state embedding to replace it. Is anything here copied material needing acknowledgment?
6. **The text:** the module's main results, the private section's header, `ClassNP`'s line and
   `exists_ndAcceptsWithin_decider`'s docstring, against the proof; no campaign labels in new text.
   The frozen target docstring's sketch says "clear the work tapes within radius `L`", where the
   proof clears radius `2L` around the displaced heads: is that misleading enough to fix now?

## Repository-side attestations (verify or challenge)

- **Elaboration** (maintainer, against `oleans-lc6m`): `ClassNP/ExhaustiveReplay` 0 errors,
  0 warnings; the target and `ndAcceptsWithin_decider_of_universal` depend on `[propext,
  Classical.choice, Quot.sound]` (`evidence/elab-ExhaustiveReplay-axioms.out`).
  `Diagonalization/NTimeHierarchy` (docstring edit) 0 errors, its two remaining sorries; `ClassNP`
  0 errors.
- **The review:** integrity (47/47 sums, the bundle, 16 linear commits, patch = bundle = file);
  scope; elaboration at the base and the tips; the seal; rule 11; the brief's 64-check and the
  worker's 260-check probes (0 errors); the screen; lint; the worker's 77-module sweep (sorry
  warnings 19 → 18).
- **Lint:** `ClassNP` 0 FAIL, 16 WARN over 21 files (the module's size warning); `Diagonalization`
  0 FAIL, 1 WARN over 5 files (`evidence/lint-*.txt`).
- **Replay:** `replay-l136.sh`: the changed modules' downstream closure on the merged tree (4 modules: `ClassNP/ExhaustiveReplay`, `ClassNP`, `Diagonalization/NTimeHierarchy`, `Diagonalization`), chained from `oleans-l132b` (#132's replay at its merged state). **Passed (user, 2026-10-21):** 4 of 4, 0 failed, static-equal (2) (`evidence/replay-l136.*`, `evidence/down-l136.txt`).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/53-c1-exhaustive-cont1-fill/findings.md`. The gate closes when it has zero
blockers and zero majors.

**Deliver your findings as a downloadable Markdown file named
`c1-exhaustive-cont1-fill-findings.md`** (the findings table and the verdict line, no other
wrapping), and also paste its content in your reply.
