# Megafill B: U2-S cont1, F5 cont1 and §13d G4 cont3

**One session, one host, a queue of three fill briefs**, worked one after another under Part 3 of
the fill-agent environment addendum (`campaign/standards/fill-environment-addendum.md`, **v2.4**).
Each item is its own fill: its brief binds it, and it has its own branch, checks, screens,
`REPORT.md` and zip, exactly as if it had been dispatched alone. Only the environment is shared.
**The order is binding**; never return to an earlier item.

## Repository and the shared base

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it fails, **stop**.
  That commit, **the shared base of every item**, contains:
  - this cover brief and the three item briefs:
    - `campaign/fills/u2s/briefs/u2s-fill-startup-cont1.md`;
    - `campaign/fills/b6/briefs/b6-fill-rulerdevice-cont1.md`;
    - `campaign/fills/s13d/briefs/s13d-fill-g4-cont3.md`;
  - their inputs, order lists, base sorry sets, screen bases and pre-ship logs;
  - the addendum v2.4.
- Every attached brief must match its repository copy at that commit except for its
  `@ANCESTOR@` placeholders, and its SHA-256 must be the one the dispatch message gives.

## Once, at the start

1. **Part 1 of the addendum:** the preflight (item 1, with its floors), the toolchain, one clone.
   If Lean cannot start, Part 2 applies.
2. **One cache for the queue** (Part 3, item 2): the union of the three order lists' Mathlib roots,
   **40 roots** at the shared base (95 modules in the union). Never the unfiltered
   `lake exe cache get`, never `lake build`.

## The queue

| # | Item | Brief | Branch | Zip | Budget |
|---|---|---|---|---|---|
| 1 | U2-S, continuation 1: the `k`-generic startup `Turing.exists_selfStartupTMK` (`UniversalK`) | `u2s/u2s-fill-startup-cont1.md` | `fill/u2s-startup-cont1` | `fill-u2s-startup-cont1.zip` | 4 hours |
| 2 | B6, F5 continuation 1: the ruler device's call rows and host (`Build/InputDevice`) | `b6/b6-fill-rulerdevice-cont1.md` | `fill/b6-rulerdevice-cont1` | `fill-b6-rulerdevice-cont1.zip` | 3 hours |
| 3 | §13d G4, continuation 3: the zone extension and rebalance rows (`Build/ZoneRebalance`), from the landed right pass | `s13d/s13d-fill-g4-cont3.md` | `fill/s13d-g4-cont3` | `fill-s13d-g4-cont3.zip` | the rest |

Each budget is wall-clock from the item's branch creation (Part 3, item 3.4). Time an item does not
use passes to the later ones; the last item has the rest of the session.

## How the items relate

- **The owned files are disjoint.** `Build/InputDevice` (item 2) is upstream of `UniversalK`
  (item 1); `Build/ZoneRebalance` (item 3) is related to neither.
- **Each item branches from the shared base and sees only the base.** Item 3 also applies PR #143's
  two commits by `git am`, as its brief says; items 1 and 2 do not. No item cites another item's
  new declarations. Never carry code between the items' branches.
- **Re-bootstrap at each item's start** (Part 3, item 3.2): a branch switch changes sources that
  the previous item's oleans were built from.

## Delivery

- Each item's zip (and its checkpoint zips) **as soon as it is written**, named as its brief says.
- At the end, or when the session must stop, `megafill-b-REPORT.md` (Part 3, item 6):
  the queue; each item's outcome (complete; partial, with its checkpoints; or not started) with its
  branch's start and end times and its zip's SHA-256; the shared preflight and cache numbers. An
  item never started is listed as such; it is not a failure.
