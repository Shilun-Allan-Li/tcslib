# External audit pack — the space measure as a sum, and a head-radius space bound (PR #149, an API gate)

Campaign: the Arora-Barak chapters 3-4 plan, B6 (the space hierarchy's windowed runner with the
configuration-count clock, [AB09, §4.1.3, Theorem 4.8]). The user's "Everything" rule
(2026-10-16, `policy.md` §1): every definition a brief's route reads gets a published equation
before the brief is dispatched.
- **Why:** the pre-ship of the configuration-count runner's continuation 2 (B6-F3,
  `Turing.exists_configWindowRunnerTM`;
  `campaign/fills/b6/drafts/b6-fill-configclock-cont2/preship-0416ffea/README.md`) found that the
  target's space clause, `R.spaceUsed d t ≤ (K + 1) * (2 * C * (L + 1) + 1)`, has no published
  route under the no-unfolding rule. `MultiTapeTM.spaceUsed` is defined (in the vendored
  `Deterministic.lean`) as the sum of the per-tape visited counts, with no equation; the per-tape
  bound `MultiTapeTM.spaceUsedByTape_le_card_Icc` is public; the windowed runner's own radius
  bound `wr_space` (`Build/WindowRun`) is private and reads the definition. The pre-ship's
  control shows the sum step closes with nothing sealed and fails with `spaceUsed` sealed
  (`evidence/F3C2RouteProbe.*`, its last two theorems). **The user ruled (2026-10-22): an API PR
  first, with the equation and a radius lemma**; F3's continuation 2 issues after it lands.
- **The head:** `lean/spaceused-api` at `097f3e04`: one commit `e172b914` on the campaign branch at
  `0416ffea`, then a merge of the campaign branch after #145, #146 and #148 (`097f3e04`; no
  conflict, the two files unchanged). Its merge-base with the campaign branch is `144201de`; its
  Lean diff from there is exactly the two files below (`evidence/spaceused-merged.patch`, equal to
  the original commit's diff `evidence/spaceused.patch`). This bundle's records are from a later
  records commit (stated in the bundle's README).

| File | Change |
|---|---|
| `TuringMachine/Deterministic` (vendored) | **`Turing.MultiTapeTM.spaceUsed_eq_sum`**: `tm.spaceUsed cfg t = ∑ i, tm.spaceUsedByTape cfg t i`, by `rfl`, beside the definition; the vendored header's list of local modifications and the "Main definitions" section name it |
| `TuringMachine/Finite` | **`Turing.MultiTapeTM.spaceUsed_le_of_abs_le`**: if every work head stays within `r` cells of its start up to time `t`, then `tm.spaceUsed d t ≤ k * (2 * r + 1)`; beside `spaceUsedByTape_le_card_Icc`, proved from the equation and that per-tape bound only; the module's "Main results" list names it |

- **Evidence:** `evidence/`:
  - `spaceused.patch`, `spaceused-merged.patch`; `pr-body.md`;
  - before the replay, against `oleans-lsk2` (the tree of `0416ffea`): `DetAx.lean.txt`/`.out`
    (`Deterministic` at the head with `#print axioms`); `SpaceRadiusSeal.lean.txt`/`.out` (the
    radius proof verbatim, primed, citing a stand-in for the equation, with `spaceUsed`,
    `spaceUsedByTape`, `visitedByTapeHead` and `runFrom` sealed) and
    `SpaceRadiusSealControl.lean.txt`/`.out` (four `rfl` controls, closing unsealed and failing
    sealed);
  - after the replay, against `oleans-lspapi` (this PR's own snapshot): `SpAx.lean.txt`,
    `axioms-lspapi.out` (both lemmas' axioms and statements); `SpaceRadiusSealPub.lean.txt`/`.out`
    (the same sealed proof citing the published equation); `SpaceConsumerProbe.lean.txt`/`.out`
    (the F3 target's space clause, in its exact form, from its envelope clause);
  - `lint-tm-base.txt`, `lint-tm-head.txt`; `screen.txt`, `screen-population.txt`,
    `screen.status` (the copy-text screen v3);
  - the replay's script, list, log and static check.
- **The bundle** also contains both modules at the head, `Build/WindowRun` (with the private
  `wr_space`), `SpaceComplexity/WindowClock` (the consumer, its target's statement) and F3
  continuation 2's draft brief and pre-ship record.

## Brief for the auditor

1. **Faithfulness.** Is `spaceUsed_eq_sum` exactly the definition's content, and is
   `spaceUsed_le_of_abs_le` true and stated with the right quantifiers: for every machine, start
   configuration, `t` and `r`, with the hypothesis at every `u ≤ t` and every tape (the closed
   window, which the visited set `Finset.range (t + 1)` needs), and the bound `k * (2 * r + 1)`,
   including `k = 0`, `t = 0` and `r = 0`? Are the docstrings exact readings?
2. **Sufficiency.** Does the radius lemma give the F3 target's space clause from its envelope
   clause, as stated there, without reading `spaceUsed` (`SpaceConsumerProbe`)? Would a consumer
   need a different form (an asymmetric interval, a per-tape radius)?
3. **Rule 10 in the API proofs.** `spaceUsed_eq_sum` is proved by `rfl` in the definition's own
   file. The radius proof reads `spaceUsed` only through the new equation and the visited counts
   only through `spaceUsedByTape_le_card_Icc`: does the seal (four definitions locally
   irreducible) cover every other-file definition it could reach, and do the controls show the
   seal is effective? Inspect the proof's `rw` and `simp` arguments.
4. **The vendored file.** `Deterministic.lean` is vendored from cslib; the repository's rule is
   that the specification API's equations sit beside their definitions there and are listed in
   its header (`Finite.lean`'s header says so). Is the addition in that form, with the header's
   list of local modifications updated, and the upstream code otherwise unchanged?
5. **Duplication.** The screen (five files: the two modules, `Build/WindowRun`,
   `SpaceComplexity/WindowClock`, `Build/Contract/Basic`; 136 declarations, 30 pairs) pairs
   neither lemma with anything, `wr_space` included. Re-pointing `wr_space` to the radius lemma is
   recorded as optional cleanup: should it be ledgered now?
6. **No collateral change:** two lemmas, the header and contents lines; no `@[simp]`; no existing
   declaration changed (40 → 41 and 25 → 26 public declarations, at source).

## Repository-side attestations (verify or challenge)

- **Elaboration and axioms:** `Deterministic` at the head (against `oleans-lsk2`) 0 diagnostics.
  Against `oleans-lspapi`: both lemmas on `[propext, Classical.choice, Quot.sound]`
  (`evidence/axioms-lspapi.out`; `spaceUsed_eq_sum`'s axioms come from the definitions in its
  statement).
- **Seal:** before the replay, the proof with a stand-in: 0 diagnostics, with the four controls'
  expected errors (`SpaceRadiusSealControl.out`: exactly the four sealed goals); after it, the
  proof citing the published equation: 0 errors (`SpaceRadiusSealPub.out`).
- **Lint:** `TuringMachine` 0 FAIL, 64 WARN over 82 files at `0416ffea` and at `e172b914` (the
  commit itself adds none); at the merged head `097f3e04`, 0 FAIL and 66 WARN over 82 files, the
  same warnings as the campaign tip's (the two new ones come from the merged #145 and #146)
  (`evidence/lint-tm-*.txt`). No line over 100 characters.
- **Screen (v3):** `evidence/screen.txt`.
- **Replay:** `replay-lspapi.sh`: the downstream closure, on the merged tree `097f3e04`, of every
  file changed since #144's merge (324 modules: everything downstream of `Deterministic`, which
  contains the merged #145, #146 and #148), chained from `oleans-lsk2`. **Passed (user,
  2026-10-22):** 324 of 324, 0 failed, static-equal (87) (`evidence/replay-lspapi.*`,
  `evidence/down-lspapi.txt`).
- **Merge order:** #147 (U2-S) replays a closure contained in this one's: this PR merges first,
  and #147 then re-replays its six modules.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/62-spaceused-api/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `spaceused-api-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
