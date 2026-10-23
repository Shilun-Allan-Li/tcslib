# The space measure as a sum, and a head-radius space bound (PR #149, an API gate): resolutions (round 1; FAIL, fixed; round 2 pending)

**Gate:** the API gate of PR #149 (`lean/spaceused-api` at `097f3e04`: `e172b914` and a merge of
the campaign branch after #145, #146 and #148). Pack `pack.md`; bundle SHA-256
`2dca34f9ca5d75e387133062f7f08786db44a11b0d2ab3784899520ab2a3a155` (56 sections; folder
`62-spaceused-api-gate/`). Replay `replay-lspapi.sh` passed (user, 2026-10-22): 324 of 324 at
`097f3e04`, static-equal (87).

**Round 1** (`findings.md`, verbatim; received 2026-10-22, SHA-256
`df84f5425e317387192ec8350a0599ae696542a09cc044002915bf7070e9adb3`): **FAIL, 0 blockers, 1 major,
1 minor, 8 notes.** The maintainer checked both actionable findings directly (the review
sub-agents were all occupied): both true.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | `Build/WindowRun`'s private `wr_space` duplicates the new public radius lemma; "optional cleanup" does not satisfy the debt rule. | **True.** `wr_space` has exactly `spaceUsed_le_of_abs_le`'s statement at `Γ P : Type`, with its own 11-line proof. **Ruled (user, 2026-10-22): fix it in #149.** Commit `3d0f80b5`: `wr_space`'s body is `MultiTapeTM.spaceUsed_le_of_abs_le R d t radius henv`; its statement and its two uses are unchanged (`evidence/round1-fix/wr_space-repoint.patch`). Checks against `oleans-lspapi`: `WindowRun` elaborates with no diagnostic, and `exists_windowRunnerTM` and `exists_windowLoopTM` are on `[propext, Classical.choice, Quot.sound]` (`evidence/round1-fix/elab-WindowRun-repoint.out`); the freeze is 10 → 10 public and 25 → 25 private, only `wr_space` changed (`freeze-WindowRun.txt`); lint `TuringMachine/Build` 0 FAIL, 33 WARN over 39 files, no line over 100 characters. No ledger entry: the duplicate is gone. The re-point's replay (`replay-lspapi2.sh`, `WindowRun`'s downstream: 4 modules, from `oleans-lspapi`) and the five-file re-screen are pending; then round 2. |
| 2 | minor | F3 continuation 2's draft promises both new lemmas in its probe but adds only the radius lemma (101 checks). | **True; records.** The draft now adds both (`spaceUsed_eq_sum`, `spaceUsed_le_of_abs_le`): 102 checks, re-run at the issue commit. |
| 10 | note | Refresh the PR's replay status; keep the merge order (#149, then #147's six-module re-replay). | **Done:** #149's description records the passed replay, the fix and round 2. The order stands. |
| 3–9 | notes | Integrity and placement; the equation; the radius lemma and its edge cases (`k = 0`, `t = 0`, `r = 0`, the closed window); sufficiency for F3; rule 10; the axiom records; lint and screen. | No action. |

**Round 2** (`pack-r2.md`, after the replay): a narrow re-audit of `3d0f80b5`.

**Round 2, first dispatch: void** (`findings-r2-void.md`, verbatim; received 2026-10-23, SHA-256
`b39057d57eeffd0ecb4c5f9b5b84bdcb749a614b036ecf10ee551e070239c334`). The auditor was attached
round 1's bundle (`2dca34f9…`, 56 sections) instead of round 2's
(`f753f518057b49e5711b00cacfc5d7be69ca53a1c9aaefdc972a9ad4d88d6995`, 69 sections), and reported
exactly that: FAIL, 0 blockers, 1 major (the wrong bundle), 0 minors, 1 note (no substantive
review). **True; no repository action.** The round-2 bundle in the outbox is unchanged and checks
against its `SHA256SUMS`. It is re-dispatched with the same prompt, and the closed gates' outbox
folders (59–63) are moved to `exchange/archive/gates/` so that only undispatched bundles remain in
the outbox. Round 2's findings go to `findings-r2.md`.
