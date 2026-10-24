# Megafill C: C1's replay canonizer, B5a's uniform simulator, U2's universal machines and §13d G4 cont4

<!-- DRAFT (drafting agent), 2026-10-24. Drafting base: the campaign tip
`77f1eb4fb74deb7a1ac7bae7bc4e98d5d0f9a532`. The drafting report
(`megafill-C-DRAFTING-REPORT.md`, beside this file) records the pre-ships, the open questions and
the recommendations. Issue-time items: @ANCESTOR@, the dispatch table's SHA-256 column, the
prerequisites' merge state (Q-B1 and Q-U1 below), and each item's budget if the queue changes. -->

**One session, one host, a queue of four fill briefs**, worked one after another under Part 3 of
the fill-agent environment addendum (`campaign/standards/fill-environment-addendum.md`, **v2.5**).
Each item is its own fill: its brief binds it, and it has its own branch, checks, screens,
`REPORT.md` and zip, exactly as if it had been dispatched alone. Only the environment is shared.
**The order is binding**; never return to an earlier item. **The agent is Codex.**

## Repository and the shared base

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it fails, **stop**.
  That commit, **the shared base of every item**, contains:
  - this cover brief and the four item briefs:
    - `campaign/fills/c1/briefs/c1-fill-replaycanon.md`;
    - `campaign/fills/b5a/briefs/b5a-fill-unisim.md`;
    - `campaign/fills/u2s/briefs/u2s-fill-universal.md`;
    - `campaign/fills/s13d/briefs/s13d-fill-g4-cont4.md`;
  - their inputs, order lists, base sorry sets, screen bases and pre-ship logs;
  - **the prerequisites of items 2 and 3**: ⟨Q-B1: the user's ruling on B5a's startup kit, and,
    if it is published first, its PR⟩; ⟨Q-U1: the field-equation API PR for
    `Turing.StepBlock.forwardLoopCfg` and `Turing.rulerHostCfg`⟩. **An item whose prerequisite is
    not in the shared base is removed from the queue at issue**, and the queue renumbered;
  - the addendum v2.5.
- Every attached brief must match its repository copy at that commit except for its
  `@ANCESTOR@` placeholders, and its SHA-256 must be the one below:

  | Brief | SHA-256 (dispatch copy) |
  |---|---|
  | this cover | ⟨…⟩ |
  | `c1-fill-replaycanon.md` | ⟨…⟩ |
  | `b5a-fill-unisim.md` | ⟨…⟩ |
  | `u2s-fill-universal.md` | ⟨…⟩ |
  | `s13d-fill-g4-cont4.md` | ⟨…⟩ |

## Once, at the start

1. **Part 1 of the addendum:** the preflight (item 1, with its floors: 12 GiB free on the clone's
   filesystem, 4 GiB of memory headroom as the addendum computes it), the toolchain, one clone.
   If Lean cannot start, Part 2 applies. **If Lean never runs, deliver the environment report
   only: do not draft proofs blind.**
2. **One cache for the queue** (Part 3, item 2): log the cache tool's archive store first, then
   fetch for the union of the four order lists' Mathlib roots: **41 roots** at the drafting base
   (**119 modules** in the union; every item's list is a subset of C1's or B5a's 119). Never the
   unfiltered `lake exe cache get`, never `lake build`. At the drafting base on a fresh host this
   fetched 1,023 archives (none in the store before), with no failed download; the manifest check
   found 11 packages present and matching, 4 absent (the documentation toolchain).
3. **Keep the shared logs** under `evidence/logs/` at the clone's root (preflight, cache store,
   roots, cache fetch, manifest and cache checks), and **copy them into every item's zip**.

## The queue

| # | Item | Brief | Branch | Zip | Budget |
|---|---|---|---|---|---|
| 1 | C1, the replay canonizer `Turing.exists_replayCanonizer` (`NDCodeSimulator`) | `c1/c1-fill-replaycanon.md` | `fill/c1-replaycanon` | `fill-c1-replaycanon.zip` | 3 hours |
| 2 | B5a, H1: the uniform simulator `Turing.MachineFormat.exists_uniformSimulator` (`CodeSimulator`) | `b5a/b5a-fill-unisim.md` | `fill/b5a-unisim` | `fill-b5a-unisim.zip` | 5 hours |
| 3 | U2: U2-U `Turing.exists_selfUniversalK` and U2-E `Turing.universalK` (`UniversalK`) | `u2s/u2s-fill-universal.md` | `fill/u2s-universal` | `fill-u2s-universal.zip` | 4 hours |
| 4 | §13d G4, continuation 4: `Turing.exists_zoneExtendTM`, `Turing.exists_zoneRebalanceTM` (`Build/ZoneRebalance`), from the return home | `s13d/s13d-fill-g4-cont4.md` | `fill/s13d-g4-cont4` | `fill-s13d-g4-cont4.zip` | the rest |

Each budget is wall-clock from the item's branch creation (Part 3, item 3.4). Time an item does not
use passes to the later ones; the last item has the rest of the session. **B5a's screen is long**
(54 files; 87 minutes a run on the drafting host, against C1's 13 and U2's 10): ⟨Q-M2: whether
B5a's budget ends when its after run starts⟩. Never switch branches while a screen runs.

**Why this order.**
- **C1 first:** the smallest item (one primitive recursive list function and a composition), with
  every step of its route probed sealed at the drafting base; complete, it is admission-free and
  removes the last admission of two landed targets (the interpreter core and the universal
  NDTM). It should finish inside its budget, so a session that ends early still delivers it.
- **B5a second:** the most valuable (the canonizer's module's last admission, behind six
  `EXPCOM` and two-tape targets and Baker–Gill–Solovay) and the largest (a twelve-phase startup
  on the interpreter core's pattern): it gets the longest fixed budget while the session is
  young.
- **U2 third:** two targets in two phases, each checkpointed; a partial (U2-U alone) is useful.
- **G4 last:** its route is a long chain of checkpoints (the return home, the left pass, the
  `ℓ = 0` branch, the cleanup, the assembly, then the rebalance row), and its four earlier rounds
  each ended partial; as the last item it uses all the time that remains.

## Per item, in the queue's order (Part 3, item 3)

1. Start from a clean tree (the previous item's work committed on its own branch and zipped).
   `git checkout -b <the item's branch> <the shared base>`.
2. **Its first edit:** C1, none; B5a, its overlay (five imports); U2, its overlay (one import);
   G4, none.
3. **Re-bootstrap the item's whole order list**, even the modules an earlier item built: a branch
   switch changes the sources the earlier oleans came from (C1's and U2's files are downstream of
   B5a's). Log each module's start and end time and **its maximum memory**, and the whole as the
   item's bootstrap. The lists: C1 `campaign/fills/c1/orders/c1-fill-replaycanon.txt` (119
   modules), B5a `campaign/fills/b5a/orders/b5a-fill-unisim.txt` (119, in the overlay's order),
   U2 `campaign/fills/u2s/orders/u2s-fill-universal.txt` (96), G4
   `campaign/fills/s13d/orders/s13d-fill-g4-cont4.txt` (96). At the drafting base the 119-module
   list took 879 s of Lean time; the peak was 2,993,964 KiB (`Build/CfgRecord`).
4. Do the item as its brief says, through its delivery zip, and **deliver that zip at once**,
   with its checkpoint zips as they are written. The session may end at any time; finished items
   must survive it.
5. **Budget** (Part 3, item 3.4): when it runs out, finish the step in progress, commit, write the
   item's partial zip with its `REPORT.md` (the checkpoints reached; every open declaration with
   its literal "Proof sketch"; the axiom walk), and start the next item.
6. **Escalations stay per item** (each brief's ground rules). An item with nothing left that its
   escalations allow ends early, with its zip.

## How the items relate

- **The owned files are disjoint:** `NDCodeSimulator` (1), `CodeSimulator` (2), `UniversalK` (3),
  `Build/ZoneRebalance` (4). `CodeSimulator` is upstream of `NDCodeSimulator` and of `UniversalK`
  (through `Codes2Tape`); `Build/ZoneRebalance` is related to none of them.
- **Each item branches from the shared base and sees only the base.** No item cites another
  item's target or new declarations: C1 cites only `CodeSimulator`'s unchanged `serializeK` and
  `serializeK_eq`; U2 cites nothing of `CodeSimulator`. **No item is proved modulo another's
  target.** Never carry code between the items' branches.
- **Their landings serialize later** (the maintainer's concern): B5a's five imports change
  `CodeSimulator`'s closure, so C1's and U2's landings replay after B5a's if B5a lands first.

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
  population, or cites `Turing.inputRewindTM` instead. None of the four writes one: B5a cites
  `Turing.inputRewindTM` (both modules in its population); U2 and G4 have `Simulation` in theirs;
  C1 needs no rewind.

## Delivery

- Each item's zip (and its checkpoint zips) **as soon as it is written**, named as its brief says.
- At the end, or when the session must stop, `megafill-c-REPORT.md` (Part 3, item 6): the queue;
  each item's outcome (complete; partial, with its checkpoints; or not started) with its branch's
  start and end times and its zip's SHA-256; the shared preflight and cache numbers. An item never
  started is listed as such; it is not a failure.
