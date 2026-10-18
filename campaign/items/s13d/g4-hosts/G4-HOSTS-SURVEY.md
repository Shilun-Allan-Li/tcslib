# §13d G4: the hosts-first survey (obligation 3 of the G2–G4 statement gate)

**Obligation 3** (`audits/s13d-g24-statements-resolutions.md`): "Hosts first for G4's fill: before
its fill brief, identify the public host for the two-tape layout (scratch and ruler layout), or
gate a missing reusable host. A tape-adding counter loop cannot stand in for a two-tape witness."

This note surveys the campaign tip `64e8fe2b`, with PR #108 (the G2 fill) for the mapped rows. It
was made by reading the sources; no Lean was run. The result:
- **every host the two rows need is public;**
- one small **leaf** family is missing: a two-tape lockstep walk that stays where it ends.

Leaves are not hosts (`machine-library-design.md` §14, "keep the §4 rule of admission"). The
missing family has its two named customers, the two G4 rows. **One decision is for the user**
(§4 below).

## 1. What the rows need

Both rows are `MultiTapeTM 2 (ZoneSym k) S`: tape 0 is the zoned tape, tape 1 the scratch tape
(`Turing.zoneRowPre`). The tape count is fixed by the statement, so no component may add a tape:
`counterLoopTM` (`k + 1` tapes) is excluded, as the obligation says. The fill plans
(`Build/ZoneRebalance.lean`, the two rows' sketches; design note §4) need:

| Need | Where in the plan | Cost |
|---|---|---|
| (a) a loop over levels: the scan outward to `i₀`; the descending pairs `i₀, …, 1`; the home move; the ascending pairs `1, …, i₀` | rebalance | `O(2^i)` per level, `O(2^{i₀})` in all |
| (b) sequencing, branching and phase dispatch of Contracts | both | constant overhead |
| (c) moving one zone left or right on one side | both | `O(2^i)` |
| (d) copying track `t`'s column of a zone to scratch and back (`extract := zoneSlotOf t`, `merge := zoneSlotSet t`) | rebalance | `O(2^i)` |
| (e) reading one slot at a measured offset inside a zone (the guards: innermost, outermost, three-quarters) | rebalance | `O(2^i)` |
| (f) writing a column back at a measured offset (the re-pack) | rebalance | `O(2^i)` |
| (g) reaching level `i` on the mirror side (the other side of home) | both | `O(2^i)` |
| (h) measuring a zone, doubling a measure, clearing scratch | both | `O(2^i)` |

## 2. What is public (the hosts)

| Need | Public, proved | Module |
|---|---|---|
| (a) | **Round iteration without a counter:** `Turing.Round`, `Turing.Round.iterate` (index-free: a round-time function on configurations, so the level can vary per round), `Turing.roundOrbit`, and `Turing.RoundContract` with `orbit_anchor`/`orbit_round`/`orbit_start` (one index for all rounds) and `returning`/`escaping` | `Build/Contract/Basic` (§16a; "stated in the core so that round iteration needs no counter") |
| (a) | the round's release into a Contract: `Turing.RoundContract.release`, `Turing.ReturnContract.release` | `Build/Contract/Seam` |
| (b) | `Turing.Contract.seq`, `inPhase`, `branch`, `trans`, with `Traj.*`, `Frames.seq` and the `_positive` lemmas; the machine-level `phaseHostTM`, `seamCompTM` | `Build/Contract/Seam`, `Build/Contract/Basic`, `Build/Seam` |
| (c) | the one-tape seek family: `skipTM`, `skipBackTM`, `seekEndTM`, `seekStartTM` (framed `_run_ofCfg` rows). The zones are delimited nonblank words between blank separators (`Turing.zonedTape_right_word`, `_left_word`), so one skip crosses one zone | `Build/Catalog` (R8.3) |
| (d) | `Turing.copyMapTM_contract`, `transferMapTM_contract` and their `_frames`/`_traj` (proved by #108); `clearTM_contract` | `Build/Contract/Catalog` |
| (e), (f) | in place: `scanTM` (the two-pass transducer: `scanKeep`, `scanFold`, `scanMap`, `scanShift`, `scanCarry`) | `Build/Catalog` (R8.2) |
| (h) | measuring: `copyMapTM` with `extract := fun _ => true` writes `true^|zone|` on scratch and returns both heads. Clearing: `clearTM_contract` | as above |

**Two gaps in the packaging, not in the hosts.**
- The seek rows and `scanTM` have framed `_run_ofCfg` theorems but no `Contract` packaging in
  `Build/Contract/Catalog`.
- The rows are stated as Contracts, so the fill wraps each one, as `sweepContract` does for the
  sweeps.

That is mechanical (a constructor from the framed theorem and its trajectory clauses), and its
second customer is any later Contract consumer of the seeks. It can be done in the fill as
public additions to `Contract/Catalog`, or privately in `ZoneRebalance` (decision 2 below).

## 3. What is missing: a two-tape lockstep walk that stays

Needs (e), (f) and (g) move the head of tape 0 by a measured distance and **leave it there**.
- **Mirror crossing:** cross home and reach the mirror zone.
- **Guard offset:** stand on the slot three quarters into zone `i`.
- **Re-pack offset:** start the write-back `2^(i-1)` cells in.

The measure is a word on scratch, the ruler. No public row does this:
- the mapped copy and transfer move both heads in lockstep but **return** both, after `2|w| + 2`
  steps;
- the seeks and skips are one-tape;
- `scanTM` is one-tape;
- `Build/InputDevice`'s ruler (`Turing.RulerAt`, `exists_rulerTestTM`/`_DeviceTM`/`_HostTM`, H5;
  sorried) measures an **input-tape** offset for C1's suffix input. It is not a work-tape walk.

Without a ruler, the mirror crossing would need a count of the zones crossed. That count is not
bounded in finite control, and a counter tape is excluded.

**The missing family**, as a leaf in the catalog's idiom (TM1-style labelled control, framed
`_run_ofCfg` rows):
- **walk** `(src dst : Fin k) (hne : src ≠ dst) (dir : SignType)`: from the start of a delimited
  word `w` under `src`'s head, move both heads `|w|` cells in direction `dir` and stop there.
  `|w| + 1` steps; nothing is written; the other heads are fixed.
- **walk-back:** the same with `src`'s head returning to the start. This is the walk followed by a
  one-tape `skipBackTM`/`seekStartTM` on `src`, so it is a composition, not a new row.
- **doubling** (the extension row's ruler of twice zone `ℓ - 1`): the mapped copy appended to
  itself, or two walks. Also a composition.

So the new leaf is **one row** (the walk, in both directions) and its Contract. Its two named
customers are the rebalance row and the extension row (§4 rule of admission). It is the analogue,
for two work tapes, of the input device's restoring sweep.

**Layout of tape 1 during a pair step.** The ruler and the column buffer coexist on scratch, as
two delimited words separated by a blank:
- the ruler at `[q₀ - m - 1, q₀ - 1)`, left of the scratch head's start `q₀`;
- the buffer at `[q₀, q₀ + L)`.

The head travels between them in `O(m + L) = O(2^i)` steps. The row's endpoint clears both
(`clearTM_contract`) and returns the head (the row's tape-1 post is blank everywhere, its head
back). The envelope is the time-implied one (`Turing.zoneRowHi`, ruling 8).

## 4. Decisions for the user

1. **The walk row.** (a) *A public catalog leaf* (`Build/Catalog`, beside R8.3, with its Contract
   in `Contract/Catalog`), stated and gated first in a small statement unit: one row, both
   directions, its Contract, and the seek and scan Contract wrappers. Then the G4 fill brief cites
   it. Or (b) a private leaf in `Build/ZoneRebalance`, written in the fill with a promotion note.
   *Recommended: (a).* The row is generic and tiny, a gate on one leaf is cheap, and G5's
   assembly and the zoned two-tape universal will want the same walk. (b) is allowed by the leaf
   rule, but the next consumer would face a promotion PR and a gate anyway.
2. **The Contract wrappers for the seeks and `scanTM`.** Public in `Contract/Catalog` with the walk
   (with 1a), or private in the fill. *Recommended: public, in the same unit.*
3. **No new host.** Iteration is `Round.iterate` (or `RoundContract` where one index suffices), and
   sequencing is `Contract.seq`/`inPhase`/`branch`. *Recommended: the G4 brief binds these and
   forbids a private loop host.*
