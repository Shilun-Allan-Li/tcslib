# Megafill C: U2's universal machines

**One session, one host, a queue of one fill brief**, worked under Part 3 of the fill-agent
environment addendum (`campaign/standards/fill-environment-addendum.md`, **v2.5**). The item is its
own fill: its brief binds it, and it has its own branch, checks, screens, `REPORT.md` and zip,
exactly as if it had been dispatched alone. **The agent is Codex.**

## Repository and the shared base

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it fails, **stop**.
  That commit, **the shared base**, contains:
  - this cover brief and the item brief `campaign/fills/u2s/briefs/u2s-fill-universal.md`;
  - its inputs, order list, base sorry set, screen base and pre-ship log;
  - **its prerequisite**: the field equations of `Turing.StepBlock.forwardLoopCfg` and
    `Turing.rulerHostCfg` (PR #161);
  - the addendum v2.5.
- Every attached brief must match its repository copy at that commit except for its
  `@ANCESTOR@` placeholders, and its SHA-256 must be the one the dispatch message gives.

## Once, at the start

1. **Part 1 of the addendum:** the preflight (item 1, with its floors: 12 GiB free on the clone's
   filesystem, 4 GiB of memory headroom as the addendum computes it), the toolchain, one clone.
   If Lean cannot start, Part 2 applies. **If Lean never runs, deliver the environment report
   only: do not draft proofs blind.**
2. **The cache** (Part 3, item 2): log the cache tool's archive store first, then fetch for the
   item's order list's Mathlib roots: **40 roots** (97 modules). Never the unfiltered
   `lake exe cache get`, never `lake build`.
3. **Keep the shared logs** under `evidence/logs/` at the clone's root (preflight, cache store,
   roots, cache fetch, manifest and cache checks), and **copy them into the item's zip**.

## The queue

| # | Item | Brief | Branch | Zip | Budget |
|---|---|---|---|---|---|
| 1 | U2: U2-U `Turing.exists_selfUniversalK` and U2-E `Turing.universalK` (`UniversalK`) | `u2s/u2s-fill-universal.md` | `fill/u2s-universal` | `fill-u2s-universal.zip` | the session |

The budget is wall-clock from the branch's creation (Part 3, item 3.4). The screen takes about 6
minutes a run at the base on the maintainer's host (peak memory 3.5 GB). Never switch branches
while a screen runs.

## The item (Part 3, item 3)

1. Start from a clean tree: `git checkout -b fill/u2s-universal <the shared base>`.
2. **Its first edit:** its overlay (one import).
3. **Re-bootstrap its whole order list** (`campaign/fills/u2s/orders/u2s-fill-universal.txt`, 97
   modules), logging each module's start and end time and **its maximum memory**, and the whole
   as the item's bootstrap.
4. Do the item as its brief says, through its delivery zip, and **deliver that zip at once**,
   with its checkpoint zips as they are written. The session may end at any time; a finished
   checkpoint must survive it.
5. **Budget** (Part 3, item 3.4): when the session must end, finish the step in progress, commit,
   and write the item's partial zip with its `REPORT.md` (the checkpoints reached; every open
   declaration with its literal "Proof sketch"; the axiom walk).
6. **Escalations** follow the brief's ground rules. If nothing is left that its escalations allow,
   the item ends early, with its zip.

## Environment rules for the session (addendum v2.5, with megafill A's lessons)

- **Part 1 applies on this host** and **Part 3** governs the session: one preflight, one cache,
  `df -B1` of the clone recorded before the item (E-RES below 3 GiB free stops the session).
- **One Lean process at a time** and **one screen at a time**, under `nice -n 10`. Every check
  through `scripts/lean_check_tree.sh`.
- **The shared environment logs go in the item's zip**, and **memory is logged per module** (in
  the bootstrap, the final sweep and every probe).
- **A seal not run is a checklist failure**, and so is a seal without `rfl` controls that fail
  sealed and close unsealed (the brief's ground rule 10). Ship the raw outputs.
- **An item that writes an input rewind** has `Simulation` and `Build/InputRewind` in its screen
  population, or cites `Turing.inputRewindTM` instead. U2 writes none, and has `Simulation` in its
  population.

## Delivery

- The item's zip (and its checkpoint zips) **as soon as it is written**, named as its brief says.
- At the end, or when the session must stop, `megafill-c-REPORT.md` (Part 3, item 6): the item's
  outcome (complete; partial, with its checkpoints; or not started) with its branch's start and
  end times and its zip's SHA-256; the preflight and cache numbers.
