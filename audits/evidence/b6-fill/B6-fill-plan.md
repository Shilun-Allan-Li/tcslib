# B6 fill plan: the space-hierarchy hosts (the ten contracts of PR #92)

Maintainer plan, 2026-10-14, written read-only against the campaign tip **`c52663f1`** (the
records commit after #94, the H1 harvest; its Lean content is `1b6b972c` plus #94). Line numbers
are at that tip. Figures are **MEASURED** unless marked ESTIMATE. The statement gate of the ten
contracts is closed (`audits/b6-hosts-statements-findings.md`: PASS, 0/0/5; resolutions
`…-resolutions.md`); its rulings bind every batch below.

**Fills are proved modulo the other sorried contracts** (the campaign's proved-modulo rule): a
batch cites another batch's contract by its frozen statement only. So every dependency in this
plan is a statement-level citation, and two batches with disjoint files can run in the same
round. The order below is the order in which their proofs are needed for the headline to become
sorry-free, and it fixes which briefs are written first.

## 1. The ten contracts and their homes

| # | Contract | File:line | Batch |
|---|---|---|---|
| 1 | `Turing.exists_stepClockTMVia` (H3's clock) | `TuringMachine/Build/StepClock.lean:115` | F1 |
| 2 | `Turing.exists_windowLoopTM` (H3's loop) | `TuringMachine/Build/WindowRun.lean:371` | F2 |
| 3 | `Turing.exists_windowRunnerTM` (H3) | `TuringMachine/Build/WindowRun.lean:428` | F2 |
| 4 | `Turing.exists_configWindowRunnerTM` (H3, configuration-count clock) | `SpaceComplexity/WindowClock.lean:187` | F3 |
| 5 | `Turing.exists_selfStartupTM` (`U₀`'s startup) | `TuringMachine/SelfUniversal.lean:89` | F4 |
| 6 | `Turing.exists_selfUniversal` (`U₀`) | `TuringMachine/SelfUniversal.lean:144` | F4 |
| 7 | `Turing.exists_rulerTestTM` (H5, the boundary test) | `TuringMachine/Build/InputDevice.lean:216` | F5 |
| 8 | `Turing.exists_rulerDeviceTM` (H5, the call rows) | `TuringMachine/Build/InputDevice.lean:249` | F5 |
| 9 | `Turing.exists_rulerHostTM` (H5, the ruler host) | `TuringMachine/Build/InputDevice.lean:313` | F5 |
| 10 | `Complexity.space_universal` (Exercise 4.1, `C · s`) | `SpaceComplexity/Hierarchy.lean:150` | F6 |

Not among the ten, and outside this plan's batches: the headline consumers in the same
`Hierarchy.lean`, `Complexity.space_hierarchy` (`:267`), `Complexity.LOGSPACE_ssubset_PSPACE`
(`:284`) and `Complexity.SPACE_linear_ne_NP` (`:314`), filled by a later batch **H** (§6).

## 2. The batches

| Batch | Owns (disjoint files) | Contracts | Cites, statement-level only | Critical path to the headline | Serves C1 | Size (ESTIMATE, lines landed) |
|---|---|---|---|---|---|---|
| **F1** | `Build/StepClock.lean`, and (brief v2) a listed promotion block in `Build/CounterLoop.lean` and `SymbolLift.lean` | 1 | none of the ten | **1st**: the head of the runner chain | **yes**: one step clock (C1 decision 4); C1's diagonalizer caps and `E`'s replays cite its `Bool` form `exists_stepClockTM`, proved from it in the file | +700 to +1,300 |
| **F2** | `Build/WindowRun.lean` | 2, 3 | 1 (the runner is the loop under the clock) | **2nd** | no | +1,000 to +1,800 |
| **F3** | `SpaceComplexity/WindowClock.lean` | 4 | 3 (Route A) | **3rd**; brief after F1 integrates (the gate's ruling: Route A once the shared clock is filled) | no | +500 to +1,000 (Route A); +700 to +1,200 (Route B) |
| **F4** | `SelfUniversal.lean` | 5, 6 | none of the ten; the emitting wrapper (a host to gate first, §5) | parallel branch: `U₀` is the headline's universal machine | no | +1,200 to +2,300 (with the wrapper host, +300 to +600, in its own gate) |
| **F5** | `Build/InputDevice.lean` | 7, 8, 9 | none of the ten | off the headline's path (only `space_universal` uses the ruler) | no (C1 decision 5 chose the window copy) | +800 to +1,550 |
| **F6** | `Hierarchy.lean`, `space_universal`'s region | 10 | 9, 7, 5 and the emitting wrapper | off the headline's path; last (no consumer) | no | +800 to +1,500 |
| H (later) | `Hierarchy.lean`, the headline region | — | 4, 6, row 18 | the headline | no | +1,500 to +3,000, and +600 to +1,500 for the two corollaries |

**Dependencies outside the ten.** Record-table row 18 (`Turing.exists_recordInitTM`, the initial
record, used only by H) is **proved** on PR #95 (branch `lean/rt5-row18`, open): it is not an
open dependency of any batch. Until #95 merges it is sorried at the tip, so an order list that
contains `Build/RecordTable` (F1's and F2's do) has it in its base sorry set, and #95 removes that
one sorry when it lands. The record rows `exists_recordTestTM` and `exists_recordStepTM`, the
counter loop and the R1, lift, seam and phase-host layers are proved. The H2 step block is public
(`Build/StepBlock`, #88) and its clocked loop H2-L too (`Build/StepBlockLoop`, #94).

**Critical path to `space_hierarchy`:** F1 → F2 → F3 → H, with F4 beside it (gated on the
emitting wrapper, §5). F5 and F6 serve `space_universal` alone, which no theorem consumes (the
gate's note 6): they can follow at any time.

## 3. Hosts and rows by batch (`policy.md` §1, hosts first; no new private host)

- **F1, the step clock.** The clock is itself the registered host (H3's clock). Its machine fuses
  the public one-tape decrement (`decrementTM_run_succ_ofCfg`, `_underflow_ofCfg`) lifted
  (`liftSymbols`, `liftSymbols_runFrom_over`) and embedded by R1 on the last tape
  (`embedEmitTM` along `lastEmb`), with one body transition by R1 along `Fin.castSuccEmb`;
  guarded state transport (`runFrom_mapState_of_agreeOn`); counter arithmetic
  (`counterOverhead_le_of_le`, `counterOverhead_le`); MIG-0b's segment layer for the round
  composition; the R1 reconstruction `embedEmitCfg_eq` for layouts. Not `counterLoopTMVia`,
  whose rounds return to one anchor (C1 design §3.3). The generic debit it needs is the
  requested shared lemma that retires `CounterLoop`'s private `counter_debit` (12.2c window).
- **F2, the windowed runner.** One phase host (`phaseHostTM`, `phaseHostTM_run`) over the two
  proved record rows (`exists_recordTestTM` by R1 on the record tape, `exists_recordStepTM` on
  the bank) for the loop; the step clock (F1's statement) plus a one-step timeout dispatch for
  the runner; the in-file specification lemmas of `windowRun`.
- **F3, the configuration-count runner.** Route A: `exists_windowRunnerTM` (F2) on an all-`true`
  clock word of width `c_M · L`, written by catalog rows (`copyTM`, `skipTM`, `scanTM`, their
  framed `_ofCfg` contracts) and cleared by `clearTM_run_ofCfg`, composed by R2 seams or the
  phase host; the proved bound `FinTM.configBound_le_two_pow`. Route B (fallback):
  `counterLoopTMVia` with the window round as body (`_run_escape`, `_run_done`) and one more
  record test after an escape.
- **F4, `U₀`.** The startup from `UniversalStartup` (`universalCanonTM`, `universalCaptureTM`,
  `universalCanon_complete`), catalog rows to redistribute the serialization, `FinTM.timed_rewind`;
  `U₀` from H2's step block (`StepBlock.Rep`, `roundTM_effect`, `roundTM_visited`,
  `roundTM_iterate`) with the native device (`NativeAt`) and **the emitting wrapper** (§5), a host
  that H2-L does not provide (H2-L is clocked and silent).
- **F5, the ruler device.** The boundary test is a leaf (a small finite controller moving the
  input and ruler heads in lockstep; no catalog row moves the input head with a work head), its
  docstring saying so; the call rows by R2 seams; **the ruler host as MIG-0b's macro-step
  lockstep** (`Turing.Lockstep` with `runFrom`, `cut`, `locate`: its encoding is
  `rulerHostCfg` with the boundary tag, a function of the source configuration, and its cost is
  one step or one step plus the restoring test), with the Z1 pattern of `vhostEmitTM` for the
  visited sets. `InputDevice`'s closure has neither `Build/Contract/Basic` nor `Build/Seam`
  (MEASURED: 14 modules), so F5 needs two import additions (§5).
- **F6, `space_universal`.** The ruler host (F5) around the shared emitting wrapper (§5), a
  header scan writing the ruler (catalog `scanTM`/`skipTM` over the doubled header, or the pair
  parser), the startup phases of F4 reading the code from the second pair, and the ledger facts
  already proved (`CodeTM.one_le_spaceUsed`, `pairEncode_pairEncode_length`, `_drop`,
  `length_bits_le_self`).
- **H.** `exists_configWindowRunnerTM` (F3) at `U₀` (F4) with `summaryTag`, row 18, the record
  test for the verdict, `inputFoldTM`, `g`'s witness, the radius phase, and the proved bridges
  (`exists_codeTM_spaceUsed`, `ComputesInSpace.computesFunInTime_and_forall_spaceUsed_le`,
  `windowRun_summary_of_halts`, `decidesInSpace_of_alphabetReduction`).

## 4. C1

F1 serves C1: C1's consumers (the diagonalizer `D`'s caps in `Diagonalization/NTimeHierarchy`,
the exhaustive decider `E` in `ClassNP/ExhaustiveReplay`) cite the clock, in its `Bool` form
`Turing.exists_stepClockTM`, which `StepClock.lean` proves from F1's target and F1 keeps
byte-identical. No C1 brief needs to wait for F1 (proved modulo). The C1-A assembly gate (round
2) adds `Turing.embedSilentCfg_cap` to `Build/Embed` (in F1's and F2's closures); neither batch
uses it.

## 5. Decisions needed before some briefs

1. **F3's route timing.** The gate's ruling is "Route A if the shared clock is filled first,
   else Route B". Recommendation: brief F3 after F1's delivery integrates (Route A, one clock);
   briefing it now would follow Route B by the ruling's letter.
2. **The emitting wrapper (consumer obligation CO-RF).** `StepBlock.roundTM_iterate` is the silent
   block; the wrapper that forwards each round's emission before the next round (H2-S finding 4)
   is an interpreter host, and the gate asked that it be **shared between `U₀` and `SU`, not
   recreated privately in each proof**. Recommendation: a small statement gate of one public
   contract (the emitting iterate from a `StepBlock.Rep` seam with the output erased, in
   `Build/StepBlockLoop` or a new `Build/StepBlockEmit`), before F4's brief; F4 and F6 cite it.
3. **F5's imports.** `Build/InputDevice` imports `Build/VirtualInput` and `UniversalStartup`
   only. The lockstep host and the seams need `Build/Contract/Basic` and `Build/Seam` (no cycle:
   only the facade and `InputDevice` itself are downstream of it, MEASURED). Recommendation:
   authorize both imports in F5's brief.
4. **`Hierarchy.lean`'s imports and its two batches.** F6 and H own disjoint regions of one file
   and both need new imports (`Build/InputDevice` and `SelfUniversal` for F6; `WindowClock`,
   `Build/RecordTable`, `SelfUniversal` for H); the gate's P5 said to add imports when a fill uses
   them. Recommendation: run H after F6 integrates, or let one maintainer PR add the union of the
   imports before both briefs.
5. **`SelfUniversal`'s import follow-up** (backlog: switch `CodeSimulator` to `Build.StepBlock`
   and re-point one citation): land it before F4's brief, so that F4's base and closure are
   final (31 modules today, MEASURED, including `Build/StepBlockLoop` since #94).

## 6. Outlines of the later briefs

**F3, `exists_configWindowRunnerTM` (`SpaceComplexity/WindowClock.lean`).** Owns line 187's body,
a home before its docstring (after `FinTM.configBound_le_two_pow`) and a Fill appendix. Route A,
the docstring's: write an all-`true` clock word of width `W = c_M · L` on a scratch tape by
copying the record's layout `c_M` times and mapping every cell to `digit true` (`copyTM`,
`skipTM`, `scanTM`), run `exists_windowRunnerTM` on it (its last tape is the clock; the
config runner's other tapes are the runner's), and on `halted`/`left` clear the clock
(`clearTM_run_ofCfg`) and rewind it, so that every other tape is blank again. The ledger is the
docstring's and the gate's: `configBound ≤ 2^(|Q| + posWidth n + 3k(2s + 1))`
(`configBound_le_two_pow`), `L + n + 1 ≤ 2^(L + 1)`, `C₀ · 2^(|Q| + 4L + 2)` against `2^W - 1`,
and the `+ 1` surplus round (`N ≤ configBound + 1`), with `windowRun_stop_unique` to move the
certification from the runner's `N` to the statement's. The consumer probe to ship with the
brief: row 18's endpoint meets this contract's precondition after the radius tape is cleared
(the record-table cont5 brief's consumer probe already shows the record part). Hazards: S1b's
dead private radius helpers in `ConfigGraph`; the counter loop (Route B only). Order list 174
modules (MEASURED at `c52663f1`), downstream: the `SpaceComplexity` facade only.

**F4, `U₀` (`TuringMachine/SelfUniversal.lean`).** Owns both bodies, a home between them and before
the first, and two Fill appendices. After decisions 2 and 5. Startup: `universalCanonTM` with the
capture of `universalCaptureTM` (`universalCanon_complete` gives the time `3|α| + 4 +
canonizerTime |α|` and the input head at `2|α| + 3`), then split the captured `serializeK`
(`Turing.oneTapeMachineFormat.serialize_eq`, or its re-pointed name after decision 5) into the
unary initial state on tape 2 at offset 2 and the table on tape 1, clear scratch, rewind the input
to position 1 (`FinTM.timed_rewind`); `T` and `B` depend on `α` only. `U₀`: the startup seamed to
the emitting wrapper (decision 2) at one coded work tape, the halting round's emission forwarded
before the physical halt, and the space ledger `B_α + s + 2(2B + 1) ≤ C_α (s + 1)` from
`roundTM_visited`. `U₀` is named by `Classical.choose` at its consumer (ruling Q6). Sanity: the
startup's empty output and input position `1` on an empty payload; a two-state coded machine
that emits and halts. Hazards: `CodeSimulator`'s H1 assembly (moved to `StepBlockLoop` by #94),
`UniversalBlock`/`UniversalInterpreter` (the chapter-1 interpreter, Finding B: never reuse its
unary input marker), `Inclusions`' private capture shape.

**F5, the ruler device (`TuringMachine/Build/InputDevice.lean`).** Owns the three bodies, homes
before each, Fill appendices, and (decision 3) two imports. The boundary test first, as a leaf: `ℓ`
lockstep moves (input head left, ruler head right) until the ruler's right delimiter, one read
(`inputCell_sub_eq_none_iff` is the semantic fact, proved), `ℓ` moves back; time `C · (ℓ + 1)`;
empty payload and `p = |z| + 1` covered (the gate's adversarial table). The call rows by seams
over the test (read: blank on `yes`, the native symbol on `no`, `inputCell_of_drop`; move: right
native, left suppressed on `yes`). The host as a `Turing.Lockstep` instance: one host step per
source step, plus the test after a left move from a cleared tag; the five clauses from
`Lockstep.runFrom`, `.cut` and `.locate`, and the visited sets as `vhostEmitTM_visitedByTapeHead_bank`
does. The gate's finding 2 (state map, not injection) is already in the text. Sanity: `ℓ = 1`,
`z = [true]`, `y = []` at both positions; the clamped right move at `|y| + 1`.

**F6, `space_universal` (`SpaceComplexity/Hierarchy.lean`, lines 86–161 only).** Owns the body at
line 161, a home before the docstring, a Fill appendix and (decision 4) the imports. After F4's and
F5's statements (modulo) and decision 2's wrapper. `SU` = a header scan writing `true^ℓ` on the
ruler tape (`ℓ = 2|bits s| + 2|α| + 4`, `pairEncode_pairEncode_length`, `_drop`), the canonizer on
the code read from the second pair (F4's startup phases), then the ruler host (F5) around the
emitting wrapper on the virtual input `x`. Ledger: `ℓ ≤ (2|α| + 6) · s` from
`CodeTM.one_le_spaceUsed` and `length_bits_le_self`, `C := B_α + 2|α| + 9` (the gate's
calculation). The budget's value is never used as a cutoff (note N7's reading). Sanity: the gate's
weakening probe (the old `+ logSpace` form follows).

**H, the headline (later; not one of the ten).** `space_hierarchy` on the window route of its
docstring, then `LOGSPACE_ssubset_PSPACE` and `SPACE_linear_ne_NP`. It needs F3 and F4 (modulo)
and row 18 (proved on #95), and decisions 4 and P4 (point the sketch at the gated names). The
diagonalizer `D` is the theorem's own machine (its natural contract depends on its consumer), so
it is not a host; its phases are public rows.

## 7. Sizes (all ESTIMATE)

Basis: the design note's §9 estimates, adjusted for what the pre-ship blocks of F1 and F2 already
contain.

| Batch | Lines landed | Basis |
|---|---|---|
| F1 | +700 to +1,300 | the prescribed block lands about 300 lines with six proofs; the generic debit about 150–250 (after `counter_debit`'s 168, MEASURED); the rounds and the two clauses 300–700 |
| F2 | +1,000 to +1,800 | the two home blocks about 140; the round lemma 300–500; the every-`N` induction 200–400; the runner 300–700 |
| F3 | +500 to +1,000 | the clock writer and the ledger (Route A) |
| F4 | +1,200 to +2,300 | `UniversalStartup.lean` is 591 lines and mostly reused; the wrapper's gate adds 300–600 separately |
| F5 | +800 to +1,550 | `VirtualInput.lean`'s Z1 pair is 508 lines (MEASURED at #92) |
| F6 | +800 to +1,500 | a header scan, a startup variant, the host composition, the ledger |
| H | +2,100 to +4,500 | `D`'s phases, the contradiction, the packaging; the two corollaries |
| **all** | **+7,100 to +13,950** | about 1–1.3k of it (F1) shared with C1 |

## 8. The first two briefs

**Update (2026-10-14, late): F1 is re-briefed as `briefs/b6-fill-stepclock-v2.md`.** The first F1
delivery stopped on escalation E1 (the route needed `CounterLoop` privates and unfoldings that v1's
rule 10 forbade). v2 authorizes exactly 19 promotions in `Build/CounterLoop` and `SymbolLift` and
ships a route probe; see the brief's "Why there is a v2". F2's brief is unchanged.

F1 and F2 are written in full, with pre-ship checks at `c52663f1` against `oleans-lh1`:
`briefs/b6-fill-stepclock.md` and `briefs/b6-fill-windowrun.md`, with their inputs in
`audits/evidence/b6-fill-stepclock/`, `audits/evidence/b6-fill-windowrun/`, `briefs/orders/` and
`audits/logs/`. They can be dispatched in the same round (disjoint files; F2 cites F1's
statement).
