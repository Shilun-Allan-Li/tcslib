# B6, F5 continuation 1: the ruler device's call rows and host (PR #146, a fill gate): resolutions (round 1; gate CLOSED)

**Gate:** the fill gate of PR #146 (`lean/b6-f5-cont1` at `8114e482`): the worker's commits
cherry-picked (`b6c9e0c5`, `b26d53c9`) and the maintainer's docstring commit `8114e482`. Both
targets, `Turing.exists_rulerDeviceTM` and `Turing.exists_rulerHostTM`, are proved, with no
admission. Pack `pack.md`; bundle SHA-256
`9e427835ccf0359d7a59a350107057e5b8d5850936f783a560394bd38e83c75c` (106 sections; folder
`60-b6-f5-cont1-fill-gate/`). Replay `replay-lf5c1.sh` passed (user, 2026-10-22): 16 of 16 at
`8114e482`, static-equal (8).

**Round 1** (`findings.md`, verbatim; received 2026-10-22, SHA-256
`70cf3a08a6c996ccdc2028a86074a94e4db67d36bb613d7dde0abf6cfc778e5a`): **PASS, 0 blockers, 0 majors,
0 minors, 16 notes. The gate is closed.** No `.lean` change. The maintainer's review sub-agent
verified every finding (with gates 59 and 61): all 16 true
(`campaign/gates/59-c1-seamlayout-fill/evidence/round1-review/REVIEW.md` and its `out/`).

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | note | Integrity, identity, ownership and the freeze pass; the pack's `43d22595` is a later records snapshot, and the PR's merge-base is `34af2e0f`. | **True; pack erratum.** `git merge-base` of `8114e482` and the tip is `34af2e0f3bc984f336d08da42f55d448feb78a7b`, the parent of `b6c9e0c5`. `43d22595f0e3aaa35eccda39dff031804ee351cc` is a records-only child of `34af2e0f`, made after `8114e482`, and is not an ancestor of #146; the TCSlib tree is the same at both (`2babcaec`), so every elaboration and replay claim stands (`out/60-F1-merge-base.txt`, `out/60-F1-identity.txt`). **Pack erratum:** `pack.md:13–14`, "**The head:** `lean/b6-f5-cont1` at `8114e482`, on the campaign branch at `43d22595` (TCSlib = `b7447492`'s, after #139 and #143):", reads **"The head: `lean/b6-f5-cont1` at `8114e482`, on the campaign branch at `34af2e0f` (its merge-base; TCSlib = `b7447492`'s, after #139 and #143). `43d22595`, the records commit that recorded this landing, is a child of `34af2e0f` with the same TCSlib tree; it is not an ancestor of #146:"**. Gate 61's pack, which also names `43d22595`, is right: that commit is #148's parent and merge-base. **Process:** packs give the head's merge-base (`git merge-base <head> <campaign tip>`) and the bundle's records revision separately. |
| 13 | note | Two read exits are return points: from the blank and `false` reads the machine keeps moving after `2ℓ + 5`. Put a "consume at the first exit" note in the F6/U2-E briefs. | **True, from the source, and more than stated:** the exit *state* persists after the return time with displaced heads (at `ℓ = 1`, `z = [true]`, a virtual-zero read with the ruler head at 5: heads (1, 5) at step 7, and still `readExit none` at step 8 with heads (2, 4); `out/60-F13-read-exits.txt`). `readExit (some true)` and `moveExit` are stationary, but the statement does not say so. **Carried** to the F6 (`Complexity.space_universal`) and U2-E (`Turing.universalK`) briefs, whose drafts do not exist yet, as the text below. The frozen statement is not changed. An optional docstring sentence (below) goes into the deferred public-facing pass or the first consumer's PR, not into #146. |
| 16 | note | The environment account is consistent; 967 of the 1,002 cache archives were already in the store, of unestablished origin; log the store in the next addendum. | **True; records** ("967 archives already in the cache tool's store; origin not established"). **Carried** to addendum v2.5: log the store before the first fetch and report the count. Whether v2.5 allows a pre-populated store or requires an empty one is put to the user. |
| 11 | note | The implementation paragraphs are accurate; "R1" shorthand and 11 privates without docstrings are for the deferred pass. | **No action; already in the backlog** (the deferred public-facing pass). |
| 12 | note | No new cross-file copying; the in-file 79% pair `exists_rulerTestTM`/`rd_test_return` can wait for an authorized refactor. | **True; backlog** (the dedup window, the user's call since the proof is frozen): target 1's last step can cite `rd_test_return`, which removes the pair. With it, the review's promotion candidates (the `Lockstep` frames corollary, `rd_shift_move`, the "step plus bounded pause" block once U2-E fixes its shape). |
| 14 | note | The elaboration, axiom, sweep and replay records are consistent; replay again if an overlapping landing changes the tree. | **No action.** #146's closure is `{InputDevice, UniversalK, SelfUniversal, the facade}`: it meets #145's and #148's only at the facade and #144's not at all. It meets #147's (U2-S) beyond the facade (`UniversalK`, `SelfUniversal`): **whichever of #146 and #147 merges second replays on the merged tree.** |
| 2–10, 15 | notes | The frozen definitions; the inherited test; the call controller; the call rows' time and space; the host controller; the host's frames and ledgers (the ruler clause an upper bound, `inj` a state map); the edge cases; rule 10; rule 11; sizes and lint. | **No action.** Spot-checked in the source (`rd_answer`, `rd_family`/`rd_redirect`, `rd_hostCost`, the ruler clause `⊆ Finset.Icc (rp − 1) (rp + ℓ)`, `inj : S → Bool → Q`); 15 public and 41 private declarations; lint 32 WARN over 39 files, the new one InputDevice's size. Finding 7's two readings go into the consumers' carry below. |

**The carry into the F6 and U2-E briefs (C60-1).**

> **The ruler device's exits are return points, not stationary anchors.**
> - `Turing.exists_rulerDeviceTM` describes the device only up to its return time `t` (`2ℓ + 5`
>   in the proof): no exit before `t`, the stated endpoint at `t`, and the ruler-head bound for
>   `u ≤ t`. It says nothing after `t`.
> - After `t` the machine keeps running. From `readExit none` and `readExit (some false)` it runs
>   the boundary test's return leg: the next step moves the input head right and the ruler head
>   left, or the ruler head right. The exit state can persist with displaced heads: at `ℓ = 1`,
>   `z = [true]`, a read at virtual position 0 with the ruler head at 5 has heads (1, 5) at step 7
>   and is still in `readExit none` at step 8, with heads (2, 4).
> - `readExit (some true)` and `moveExit` happen to be stationary; the statement does not promise
>   it.
> - **Consume each exit at its first occurrence**: compose the device through a seam
>   (`seamCompTM`, `Contract.seq`) or a phase-host redirect that leaves at the exit state. Never
>   cite the device's configuration after `t`, never treat an exit as a stationary anchor, and
>   never detect an exit by its state at a later time.
> - If your route needs a stationary exit, escalate (the remedy is a change of the final phase,
>   by a separate authorized PR); do not restate the frozen statement.
>
> In `Turing.exists_rulerHostTM`, the ruler's space clause is an upper bound (the visited set lies
> in `[rp − 1, rp + ℓ]`), and `inj` is a state map, not an injection.

**Optional docstring sentence for `exists_rulerDeviceTM` (C60-2; the deferred public-facing pass
or the first consumer's PR):** "The exits are return points: nothing is stated after the return
time, and from the blank and `false` read exits the machine keeps moving, so a caller leaves the
device at its first exit, as a seam or a phase-host redirect does."

**Reviewer additions (records):** this gate's bundle list kept only the first 60 entries of the
review's `out/` folder (98), leaving out about 29 outputs its REVIEW.md cites (among them
`41-elab-tip-lg4c2.out`, `43-merged-replay.txt`, `48-ax-vs-worker.txt` and `49-publics-*.out`).
The auditor recorded the claims resting on them as attestations, so no finding changes. All are
in the repository (`campaign/fills/b6/reviews/rulerdevice-cont1/out/`). The lesson is in gate
59's resolutions.

**Merge state.** #146 is on the campaign branch (not stacked). **Clear to merge.** Its facade
overlap with #145 and #148 is covered by the standing rule; with #147, whichever merges second
replays.
