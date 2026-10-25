# Megafill C: B5a's uniform simulator and U2's universal machines

<!-- DRAFT (drafting agent), 2026-10-24. Drafting base: the campaign tip
`77f1eb4fb74deb7a1ac7bae7bc4e98d5d0f9a532`. The drafting report
(`megafill-C-DRAFTING-REPORT.md`, beside this file) records the pre-ships, the open questions and
the recommendations. Issue-time items: @ANCESTOR@, the SHA-256 column, the ⟨Q-M2⟩ ruling, each
draft moved to `briefs/` without its comment with its inputs staged, and every item's banner
(number, this file's name, budget). Re-run every item's pre-ship at the shared base if any Lean
change lands first.
**Revised for issue (maintainer, 2026-10-25).** Two of the four drafted items left the queue
because their targets were proved in their own fills: C1's replay canonizer
(`Turing.exists_replayCanonizer`, PR #160) and §13d G4 continuation 4 (both zone rows, PR #165).
Both prerequisites are in: Q-B1 was ruled A (2026-10-24), and its startup kit merged as #162
(`5a258cc2`, gate 74); Q-U1's field-equation API merged as #161 (`5bbef333`, gate 73). The queue
is B5a, then U2. The two pre-ships were re-run at `a524c36f`, whose Lean equals #162's merge
(`campaign/fills/b5a/drafts/b5a-fill-unisim/preship-a524c36f/`,
`campaign/fills/u2s/drafts/u2s-fill-universal/preship-a524c36f/`). The cover review's F8–F10
(`campaign/fills/megafill/reviews/megafill-c-drafts/c1-cover/`) are applied. -->

**One session, one host, a queue of two fill briefs**, worked one after another under Part 3 of
the fill-agent environment addendum (`campaign/standards/fill-environment-addendum.md`, **v2.5**).
Each item is its own fill: its brief binds it, and it has its own branch, checks, screens,
`REPORT.md` and zip, exactly as if it had been dispatched alone. Only the environment is shared.
**The order is binding**; never return to an earlier item. **The agent is Codex.**

## Repository and the shared base

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it fails, **stop**.
  That commit, **the shared base of every item**, contains:
  - this cover brief and the two item briefs:
    - `campaign/fills/b5a/briefs/b5a-fill-unisim.md`;
    - `campaign/fills/u2s/briefs/u2s-fill-universal.md`;
  - their inputs, order lists, base sorry sets, screen bases and pre-ship logs;
  - **the prerequisites of both items**: B5a's, the startup kit `Build/InterpreterStartup` (PR #162)
    and the harvested startup assembly (the user's ruling A+, 2026-10-25; ⟨PR⟩); U2's, the field
    equations of `Turing.StepBlock.forwardLoopCfg` and `Turing.rulerHostCfg` (PR #161);
  - the addendum v2.5.
- Every attached brief must match its repository copy at that commit except for its
  `@ANCESTOR@` placeholders. This cover's SHA-256 must be the one the dispatch message gives, and
  each item brief's the one below:

  | Brief | SHA-256 (dispatch copy) |
  |---|---|
  | `b5a-fill-unisim.md` | ⟨…⟩ |
  | `u2s-fill-universal.md` | ⟨…⟩ |

## Once, at the start

1. **Part 1 of the addendum:** the preflight (item 1, with its floors: 12 GiB free on the clone's
   filesystem, 4 GiB of memory headroom as the addendum computes it), the toolchain, one clone.
   If Lean cannot start, Part 2 applies. **If Lean never runs, deliver the environment report
   only: do not draft proofs blind.**
2. **One cache for the queue** (Part 3, item 2): log the cache tool's archive store first, then
   fetch for the union of the two order lists' Mathlib roots: **41 roots** at the base
   (**120 modules** in the union, which is B5a's list; U2's 97 are a subset of it). Never the
   unfiltered `lake exe cache get`, never `lake build`. At the drafting base on a fresh host this
   fetched 1,023 archives (none in the store before), with no failed download; the manifest check
   found 11 packages present and matching, 4 absent (the documentation toolchain).
3. **Keep the shared logs** under `evidence/logs/` at the clone's root (preflight, cache store,
   roots, cache fetch, manifest and cache checks), and **copy them into every item's zip**.

## The queue

| # | Item | Brief | Branch | Zip | Budget |
|---|---|---|---|---|---|
| 1 | B5a, H1: the uniform simulator `Turing.MachineFormat.exists_uniformSimulator` (`CodeSimulator`) | `b5a/b5a-fill-unisim.md` | `fill/b5a-unisim` | `fill-b5a-unisim.zip` | 5 hours |
| 2 | U2: U2-U `Turing.exists_selfUniversalK` and U2-E `Turing.universalK` (`UniversalK`) | `u2s/u2s-fill-universal.md` | `fill/u2s-universal` | `fill-u2s-universal.zip` | the rest |

Each budget is wall-clock from the item's branch creation (Part 3, item 3.4). Time an item does not
use passes to the later one; the last item has the rest of the session. **B5a's screen is long** (57
files; 53 minutes a run at the base on the maintainer's host, peak memory 7.8 GB, against U2's 6
minutes and 3.5 GB). **B5a's budget counts up to the start of its after run** (the user's ruling,
2026-10-25). Write its last checkpoint zip first; start the after run at the latest when the
budget ends, with no Lean process beside it, and write `REPORT.md` while it runs; create the next
item's branch only after the run has ended and B5a's zip is written. Never switch branches while a
screen runs.

**Why this order.**
- **B5a first:** the more valuable (the canonizer's module's last admission, behind six `EXPCOM`
  and two-tape targets and Baker–Gill–Solovay) and the larger (a twelve-phase startup on the
  interpreter core's pattern, through the published startup kit): it gets the fixed budget while
  the session is young.
- **U2 second:** two targets in two phases, each checkpointed; a partial (U2-U alone) is useful,
  and as the last item it uses all the time that remains.

## Per item, in the queue's order (Part 3, item 3)

1. Start from a clean tree (the previous item's work committed on its own branch and zipped).
   `git checkout -b <the item's branch> <the shared base>`.
2. **Its first edit:** B5a, its overlay (six imports); U2, its overlay (one import).
3. **Re-bootstrap the item's whole order list**, even the modules the earlier item built: a branch
   switch changes the sources the earlier oleans came from (U2's file is downstream of B5a's).
   Log each module's start and end time and **its maximum memory**, and the whole as the item's
   bootstrap. The lists: B5a `campaign/fills/b5a/orders/b5a-fill-unisim.txt` (120 modules, in the
   overlay's order), U2 `campaign/fills/u2s/orders/u2s-fill-universal.txt` (97). At the drafting
   base the 119-module list took 879 s of Lean time; the peak was 2,993,964 KiB
   (`Build/CfgRecord`).
4. Do the item as its brief says, through its delivery zip, and **deliver that zip at once**,
   with its checkpoint zips as they are written. The session may end at any time; finished items
   must survive it.
5. **Budget** (Part 3, item 3.4): when it runs out, finish the step in progress, commit, write the
   item's partial zip with its `REPORT.md` (the checkpoints reached; every open declaration with
   its literal "Proof sketch"; the axiom walk), and start the next item.
6. **Escalations stay per item** (each brief's ground rules). An item with nothing left that its
   escalations allow ends early, with its zip.

## How the items relate

- **The owned files are disjoint:** `CodeSimulator` (1), `UniversalK` (2). `CodeSimulator` is
  upstream of `UniversalK` (through `Codes2Tape`).
- **Each item branches from the shared base and sees only the base.** Neither item cites the
  other's target or new declarations: U2 cites nothing of `CodeSimulator`. **No item is proved
  modulo another's target.** Never carry code between the items' branches.
- **Their landings serialize later** (the maintainer's concern): B5a's six imports change
  `CodeSimulator`'s closure, so U2's landing replays after B5a's if B5a lands first.

## Environment rules for the whole queue (addendum v2.5, with megafill A's lessons)

- **Part 1 applies on this host** and **Part 3** governs the queue: one preflight, one cache for the
  union of the roots, a re-bootstrap per item, `df -B1` of the clone recorded before each item
  after the first (stop the queue with E-RES below 3 GiB free; the items already zipped stand).
- **One Lean process at a time** across the whole queue, and **one screen at a time**, under
  `nice -n 10`. Every check through `scripts/lean_check_tree.sh`.
- **The shared environment logs go in every item zip**, and **memory is logged per module** (in
  the bootstrap, the final sweep and every probe).
- **A seal not run is a checklist failure**, and so is a seal without `rfl` controls that fail
  sealed and close unsealed (each brief's ground rule 10). Ship the raw outputs.
- **An item that writes an input rewind** has `Simulation` and `Build/InputRewind` in its screen
  population, or cites `Turing.inputRewindTM` instead. Neither item writes one: B5a cites
  `Turing.inputRewindTM` (both modules in its population); U2 has `Simulation` in its population.

## Delivery

- Each item's zip (and its checkpoint zips) **as soon as it is written**, named as its brief says.
- At the end, or when the session must stop, `megafill-c-REPORT.md` (Part 3, item 6): the queue;
  each item's outcome (complete; partial, with its checkpoints; or not started) with its branch's
  start and end times and its zip's SHA-256; the shared preflight and cache numbers. An item never
  started is listed as such; it is not a failure.
