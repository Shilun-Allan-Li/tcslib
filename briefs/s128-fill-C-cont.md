# §12.8 fill — stream C, continuation: the record step (`Turing.exists_recordStepTM`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 8e9a9b7eef75941a83ce036a195795c784758763 HEAD` succeeds. That
  commit contains:
  - the §12.8 statement layer and its closed gate (PR #28);
  - the maintainer's pre-issue shared layer (`5afed90b`);
  - **every other §12.8 fill your step cites, now proved:**
    - stream A, Catalog Part 3 and `Build/Seam`, PR #42;
    - stream B, `Build/Scan`, PR #41;
    - **the first stream-C delivery**, 6/7, PR #41, whose report is
      `audits/s12-8-fill-agent-reports/C-REPORT.md`;
  - this brief's order list, `briefs/orders/s128-fill-C-cont.txt`.

  If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested `fill/s128-C-cont`). Record the
  base hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-s128-C-cont.zip`, containing
  `REPORT.md`, the full modified source, a `git format-patch` series against your base, a git
  bundle, the final sweep log, the axiom log, and `SHA256SUMS`.

## What this is

**A continuation** (`workflow.md` §4). The first stream-C agent proved six of the seven
targets of `briefs/s128-fill-C.md`, with no admitted helper and no escalation:
- `cfgRecord_inj`, `recordValid_iff`, `exists_inputSeekTM`;
- `FinTM.exists_inputCallTM`;
- `exists_recordTestTM`, `exists_recordEqTM`.

All six are now **admission-free**, because streams A and B have landed. Fill the seventh,
**`Turing.exists_recordStepTM`**, row R8.7: one simulated step of a coded configuration
record, with the head-radius clause `C·(L + 1)`.

**Read first, in order:**
1. The original brief, `briefs/s128-fill-C.md`. Its route R8 is restated below verbatim and
   still binds.
2. The first delivery's report: its "Continuation frontier" (six numbered steps) and
   "Construction and obligations" sections.
3. Its integration records: `audits/s12-8-fill-integration.md`, and
   `audits/s12-8-fill-A-integration.md`, which shows every row you cite is now proved.

The design is `machine-library-design.md` §12.8a §3 (the R8.7 table) and §4. The binding
parts of the round-1 and round-2 findings and of the resolutions are quoted below.

**The proved-modulo set is now empty.** The original brief let the step cite nine sorried
stream-A rows. All nine are proved, so a complete delivery has **no `sorryAx`**.

**Pre-ship check (maintainer, executed at this brief's ancestor):**
`audits/evidence/s12-8/S128FillCProbe.lean.txt`, re-run at the issue tree
(`audits/logs/s128-fill-C-cont-preship.log`). It gives 0 errors and 0 warnings, and **every
probe print is within `[propext, Classical.choice, Quot.sound]`**. That includes
`probeCopy_seam`, which carried `sorryAx` through stream B at the original issue. The probe
elaborates the route steps this brief prescribes for R8:
- the restriction of a rich host to a dedicated digit bank (`probeRestrict`, the form of your
  one private R1 lemma);
- the record-step save loop through `counterLoopTM_run_escape` (`probeSaveBody_orbit`/`_exit`);
- the `binDigits`, `posWidth` and complement arithmetic.

## Owned file and target (modify this and nothing else)

| # | File:line (at the issue commit) | Target | Route |
|---|---|---|---|
| 7 | `TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean:475` | `Turing.exists_recordStepTM` | R8, phase host |

- **Owned file:** `Build/CfgRecord.lean`, for this one target's body and new `private`
  declarations only.
- **Not yours:** `Build/InputCall.lean` is now fully proved and frozen. Its private helpers are
  file-local and cannot be cited from `CfgRecord`; cite its public `exists_inputSeekTM`. The
  facade is not yours.

### Proof route (binding; R8 of the original brief, verbatim)

**R8. `exists_recordStepTM`** (round-1 note 28, round-2 note 3). `K + 1 = 4` tapes: `0` the record;
`1` = B (copy of F1: the seek target, then the F1 move scratch); `2` = Cs (the seek's blank
scratch); `3` = D (fuel counter, then the saved native position). Tapes 1–3 are **dedicated
digit tapes**: they only ever hold `RecSym.digit b` or blank. Every `Bool` row runs on them
**lifted along `e := RecSym.digitEmb Q T`**. The seek and the save loop read the native input,
so they run **R1-embedded** (`embedEmitTM ι (R.liftSymbols e)`, transported by
`embedEmitTM_runFrom` + `MultiTapeTM.liftSymbols_runFrom`). Their start configuration comes from
**one single-use private lemma** derived from the public R1 API exactly as the probe's
`probeRestrict` (`embedEmitCfg_selected_tape`/`_pos`, `embedEmitTM_frame` at time `0`,
`decodeBool_apply`, `decodeBool_eq_some`): a rich host whose selected tapes hold only digits and
blanks is the R1 transport of its decoded `Bool` restriction. No general R1 reconstruction was
landed; **do not copy Primitives' private `emitterP2_frame`**. The input-oblivious,
never-blank-writing rows (`incrementTM`, `decrementTM`) may instead run lifted at the bank's own
tape count through the overlay transport `MultiTapeTM.liftSymbols_runFrom_over` (with
`Cfg.liftOver`, `Cfg.decodeSymbols`, `Cfg.liftOver_decodeSymbols`), whose hypotheses `hin`, `hnb`
they meet; use one of the two transports per row, consistently. On the digit tapes,
`FinTM.bufferTape_map` and `FinTM.bufferTape_map_decode` turn delimited `Bool` words into their
lifts and back. The record tape is **never written** by a lifted row: under R1 it is never
selected, and under the overlay only the row's own digit tape changes (round-2 note 31's
isolation is what both transports provide; never apply the plain `liftSymbols_runFrom` to the
whole bank). Rich rows run on the bank directly (`scanTM 4 i`, `skipTM 4 0`, `skipBackTM 4 0`,
`copyTM`, `clearTM`). Phases, data accumulating in the phase host's index:

| # | Phase | Rows | Data |
|---|---|---|---|
| R1 | fold F0, skip | `scanTM` + `scanResult_fold`; `skipTM` | `q : Option Q` |
| R2 | fold F1 (`A := Fin 3 × Bool`) | `scanTM` + `scanResult_fold` | `W = 1`?, `p = 0`? |
| R3 | copy F1 → B and F1 → D, skip | `copyTM_run_ofCfg` ×2; `skipTM` | |
| R4 | per tape field `i < k`: fold, skip | `scanTM` fold (content at the mark, mark on the first / last cell); `skipTM` | `σ i`, `edgeL i`, `edgeR i` |
| R5 | fold the tag | `scanTM` fold | `τ` |
| R6 | back to the record start | `skipBackTM` ×(k+2) | |
| I0 | halted (`q = none`): clear B, D → `yes`, record unchanged (`hupd`, `step_of_halt`, `outputSymbol_of_halt`). `W = 1` (`|x| = 0`): clear D, `ι := none`, go to A0 with **no native movement** | `clearTM_run_ofCfg` | |
| I1 | fuel: D := all `digit true` | `scanTM` + `scanResult_map` | |
| I2 | probe the native head | private `Probe` table | `normal`/`right` |
| I3 | save loop | lifted `counterLoopTM_run_escape` on `![3]`, private body `Save : MultiTapeTM 0 Bool Bool` ("blank → exit; else left") | head at `0`; D = `counterWord w (q₀ + 1)` |
| I4 | seek to the recorded position | lifted `exists_inputSeekTM` on `![1, 2]` | |
| I5 | read the input symbol | private one-step `Read` table, verdict `inp.bind (decodeBool e)` | `ι` |
| I6 | complement D | `scanTM` + `scanResult_map` | value `q₀ + 1` |
| I7 | `normal` only: decrement D | lifted `decrementTM_run_succ_ofCfg` on `![3]` | value `pos` |
| I8 | seek back | lifted `exists_inputSeekTM` on `![3, 2]` | input at `pos` |
| I9 | clear D | `clearTM_run_ofCfg` | |
| A0 | dispatch `a := M.tr q' ι σ`; out of window iff some tape has `edgeL ∧ move = −1` or `edgeR ∧ move = +1` | — | |
| N | out of window: clear B → `no`, **before anything is written** | `clearTM_run_ofCfg` | |
| A1 | F0 := `[st a.state]`, skip | `scanTM` + `scanResult_map` (constant); `skipTM` | |
| A2 | F1 := clamped move: no change if `move = −1 ∧ p = 0` or `move = +1 ∧ ι = none ∧ p ≠ 0`; else lifted `incrementTM`/`decrementTM` on B, `copyTM 4 1 0` back, `clearTM 4 1`; skip | `incrementTM_run_succ_ofCfg`, `decrementTM_run_succ_ofCfg`, `copyTM_run_ofCfg`, `clearTM_run_ofCfg`; `skipTM` | |
| A3 | per tape field: write at the mark, shift the mark, skip | `scanResult_map`; `scanResult_shiftRight` / `_shiftLeft` (`get` the mark, `set` re-marks, `b₀ = false`); `skipTM` | |
| A4 | tag := `upd τ a.output` | `scanTM` + `scanResult_map` | |
| A5 | back to the start → `yes` | `skipBackTM` ×(k+2) | |

The save (I2–I3, the binding obligation of round-2 note 3): with `|x| ≥ 1` and a blank under the
head, `pos ∈ {0, |x| + 1}`; one right move reads a symbol iff `pos = 0` (move back: `normal`),
else the clamp kept `|x| + 1` (move left to `|x|`: `right`). From `q₀ ≤ |x|` (`q₀ = pos`, or `|x|`
for `right`) the save body escapes at round `q₀` with the head on `0`
(`probeSaveBody_orbit`/`_exit` and the checked escape call). The fuel `2 ^ W − 1 > |x| ≥ q₀`
(`n + 1 < 2 ^ posWidth n`) keeps the escape below the counter's value. After I6 the value is
`q₀ + 1` (`counterWord_value`, `counterWord_length`, and complement: values add to `2 ^ |u| − 1`,
proved in the probe); `normal` decrements to `pos`, `right` seeks to `q₀ + 1 = |x| + 1 = pos`.
The F1 clamp (A2) is `moveInputPos`'s: `p = |x| + 1` iff `ι = none ∧ p ≠ 0`, given `p ≤ |x| + 1`.
Ledger: reads and applies `O(L)`; I1–I9 `O(W + pos + p + 1)` with `W ≤ L` and `pos, p ≤ |x| + 1`;
tape 0 stays in `[h − 1, h + L]`, tapes 1–3 within `[pos_j − 1, pos_j + W]` (the seek's radius
`C_seek · (W + 1)`); so time `≤ C (L + |x| + 1)` and radius `≤ C (L + 1)`. Private pure lemmas you
need: `incFixed (binDigits W p) = some (binDigits W (p + 1))` for `p + 1 < 2 ^ W` and the
`decFixed` mirror (or by `counterWord_value` and injectivity); the rewritten tape field is
`cfgRecord`'s field of `a.apply c`; the window equivalence. The field-layout facts are public in
Catalog Part 3: cite them, and write no private equivalent. The hand tables' steps are
`step_of_inputMoveAction` (and, for any one-tape table, `step_of_tapeAction_move`/`_write`).

### The frontier you inherit (first delivery; all proved; cite or reuse)

- **Shared record layer, private in `CfgRecord`:**
  - `record_pos_lt`;
  - `record_digits_value` and `record_digits_inj`: the **one** shared `binDigits`
    value/injectivity pair that rule 7 requires;
  - `RecordRun` with `recordRun_zero`, `recordRun_trans` and `recordRun_tagged`: endpoint,
    verdict-cut and common-radius bookkeeping, concatenating established runs with
    `runFrom_add` and packaging `phaseHostTM_run`'s prefix and dispatch;
  - `record_tag_ne`.

  Reuse them; never restate them.
- **The two landed phase-host instances** (`exists_recordTestTM`, `exists_recordEqTM`) are
  templates for the index and phase-family style: `RecordTestIndex`, `recordTestRows`,
  `recordTestNext`, and so on. Write a new index type for the step; do not copy theirs. The
  screen pairs the two existing index types at 55–57%.
- **The first report's six-step frontier** is binding as an outline. It covers:
  1. one phase host on the four-tape bank;
  2. the reads R1–R6;
  3. the Probe/Save/Read tables;
  4. the seek–read–restore cycle, through the landed `exists_inputSeekTM`;
  5. reject-before-rewrite, the clamp, the rewrites and the cleanup;
  6. the time, radius, restoration and verdict-cut ledger.

## Cited infrastructure (public at the issue commit; all proved)

**Proved:**

- R1 (`Build/Embed`): `embedEmitTM`, `embedEmitCfg`, `embedEmitTM_runFrom`, `embedEmitTM_frame`,
  `embedEmitTM_visitedByTapeHead(_frame)`, `embedEmitCfg_selected_tape`/`_pos`;
  `MultiTapeTM.runFrom_mapState_of_agreeOn`.
- R2/R3′ (`Build/Seam`): `seamCompTM`, `seamCompTM_run_ofCfg`, `seamCompTM_firstReturn_ofCfg`,
  `seamCompTM_visitedByTapeHead_ofCfg`, `seamCompTM_runFrom_left`, `seamReleaseTM`,
  `seamReleaseTM_firstReturn`, `seamReleaseTM_visitedByTapeHead`.
- R8.0 (`SymbolLift`): `decodeBool(_apply)`, `Action/Cfg/MultiTapeTM.liftSymbols`,
  `MultiTapeTM.liftSymbols_step`, `_runFrom`, `_spaceUsed`, `Cfg.liftSymbols_state`,
  `_workTapePos`, `_inputSymbol`.
- R3 framed (`Build/Catalog`): `copyTM_run_ofCfg`, `clearTM_run_ofCfg`, `transferTM_run_ofCfg`,
  `incrementTM_run_succ_ofCfg`, `incrementTM_run_overflow_ofCfg`.
- §12.7 (`Build/CounterLoop`): `decrementTM_run_succ_ofCfg`, `_run_underflow_ofCfg`,
  `counterWord_length`, `counterWord_value`, `counterOverhead_le_of_le`, `counterOverhead_le`,
  `counterLoopTM_run_done`, `counterLoopTM_run_escape`, `counterLoop_time_le`.
- `Build/Loop`: `FinTM.exists_installCallTM`, `stateWord`. `Build/Convention`: `Cfg.ofWords`,
  `incFixed`. `Simulation`: `FinTM.controlAction`, `controlAction_apply`, `moveInputPos_neg_val`,
  `rewind_scan`, `timed_rewind`, `FinTM.bufferTape` and its simp lemmas,
  `MultiTapeTM.runFrom_eq_of_agreeOn`. `Configuration`: `moveInputPos(_zero)`,
  `moveInputPos_neg_of_ne_left`, `moveInputPos_pos_of_ne_right`, `inputSymbolInner`.
  `Deterministic`: `step_of_halt`, `outputSymbol_of_halt`, `runFrom_comm_of_step`,
  `runFrom_succ_eq_step(')`, `runFrom_add`, `visitedByTapeHead`. `StateRenaming`:
  `Cfg.mapState(_apply)`. Mathlib: `Nat.size_eq_bits_len`, `Nat.lt_size_self`, `Nat.lt_size`,
  `Nat.size_one`, `Nat.testBit_add_one`, `Nat.ofDigits_cons`, `sigma_mk_injective`.
- The carrier (`Build/CfgRecord`, landed): `Cfg.InWindow`, `RecSym`, `recSymFintype`,
  `RecSym.digitEmb`, `binDigits`, `posWidth`, `cfgRecord`, `cfgRecord_length`, `RecordValid`,
  `RecordAt`; the field layout `joinFields`, `fieldsTape`, `fieldOffset` and the actions
  `tapeAction`, `inputMoveAction` (Catalog Part 3).

**Landed for you before issue** (pre-issue layer `5afed90b`; all proved; lines at that commit):

- `Build/Seam`: `phaseHostTM` (774), `phaseHostTM_run` (791). Seam now imports Embed.
- `Build/CounterLoop`: `counter_cfg_eq` (626), public, name unchanged: `counterLoopCfg q c ct cp`
  is the body bank followed by the counter tape (`Fin.lastCases`).
- `Build/Catalog` (namespace `Turing.FinTM`): `rewind_scan_heads` (10337), `rewind_heads`
  (10376), formerly the private `f2_rewind_scan_heads`, `f2_rewind_heads`.
- `Build/Catalog` Part 3, the field layout: `joinFields_cons_cons` (11444),
  `fieldsTape_cons_shift` (11454), `fieldOffset_succ` (11471), `fieldOffset_cons_succ` (11478),
  `length_joinFields_add_one` (11487), `fieldOffset_add_length_le` (11505, the span bound
  `fieldOffset fs j + |fs[j]| ≤ |joinFields fs|`).
- `Build/Catalog` Part 3, one-step lemmas for hand tables: `step_of_tapeAction_move` (11358),
  `step_of_tapeAction_write` (11384), `step_of_inputMoveAction` (11412).
- `SymbolLift` (now imports `Simulation`): `decodeBool_eq_some` (245), `FinTM.bufferTape_map`
  (252), `FinTM.bufferTape_map_decode` (259), and the overlay transport `Cfg.liftOver` (271),
  `MultiTapeTM.liftSymbols_step_over` (285), `MultiTapeTM.liftSymbols_runFrom_over` (348),
  `Cfg.decodeSymbols` (362), `Cfg.liftOver_decodeSymbols` (371).
- Imports: `InputCall` imports `Build/Seam`; `CfgRecord` imports `Build/InputCall`.

**Not landed:** a general R1 reconstruction (`emitterP2_frame` stays private in Primitives).
Derive the one restriction you need privately (R8).

**Proved modulo: none.** Every declaration listed above is proved at the issue commit:
- stream A's nine rows that the original brief let you cite while sorried (`fieldsTape_field`,
  `compareTM_run_ofCfg`, `skipTM_run_ofCfg`, `skipBackTM_run_ofCfg`, `scanTM_run_ofCfg`,
  `scanResult_fold`, `scanResult_map`, `scanResult_shiftRight`, `scanResult_shiftLeft`);
- `exists_inputSeekTM` and `FinTM.exists_inputCallTM`.

The maintainer's admission walk (`audits/logs/s12-8-fill-A-admissions.log`) confirms it.

**Do not cite** `scanResult_carry`, `seekEndTM_run_ofCfg`, `seekStartTM_run_ofCfg`,
`seamCompTM₂_run_ofCfg`, `writeConstTM_run_ofCfg`, `inputFoldTM_run_ofCfg`,
`expandTM_run_ofCfg`, anything of R8.0b (`counterLoopTMVia`, `lastEmb`; PR #38, which may land
during your work), or anything downstream (`ClassPSPACE`, `SpaceComplexity`). The route does
not need them.

**If PR #38 (stream D, R8.0b) has merged by your base:**
- `counterLoopCfg`, `counterLoopOrbit` and `counterLoop_time_le` are generic over the tape
  alphabet, types only, with byte-identical bodies;
- the `Bool` contracts `counterLoopTM_run_done`/`_escape` and `counter_cfg_eq` keep their
  statements.

Use them exactly as the route says. Record in `REPORT.md` whether your base includes #38.

## Inherited audit contracts (verbatim; binding on the fill)

The rows below are quoted verbatim from the two findings tables (columns joined: number and severity, declaration, claim, evidence, proposed fix). Round 1's finding 1 and minors 2–3 were repaired in the statements you fill; their text explains the clauses you must meet.

### Round 1 (`audits/s12-8-statements-findings.md`)

> **1 (major)** — Build/CfgRecord.lean · `exists_recordStepTM`; Build/InputCall.lean · `exists_inputSeekTM`. *Claim:* The contracts are too weak for their named space-bounded consumers. *Evidence:* They bound time and restore the final tapes, but impose no bound on visited work cells. Concrete admissible detour: when the native head reads a symbol, move it left to position 0, recording one unary scratch mark per move; retrace and erase the marks while restoring the input head and scratch head. At a blank input position, skip this detour. It costs O(pos + 1), restores everything, and visits pos + 1 scratch cells. Prepending it preserves both stated time bounds. For record stepping, take the identity source machine with k = 0 and identity tag update: the detour followed by `yes` already satisfies the whole functional contract, but at pos = n its space is Θ(n), while the record length L = `posWidth n + 4` is Θ(log n). Thus restoration and O(L + n) time do not yield the O(L) workspace required by the advertised Savitch route; the analogous seek contract does not yield logspace either. *Fix:* Strengthen the same existential witnesses with trajectory/visited-set bounds through the verdict: O(L + 1) for record stepping and O(w.length + 1) for input seeking, independent of native-head travel. Prefer fixed intervals about entry heads so repeated calls compose. Re-audit the strengthened statements before fill.

> **2 (minor)** — Build/InputCall.lean · `exists_inputSeekTM` proof sketch. *Claim:* The literal existence statement is true, but its cited rewind route is off by one. *Evidence:* The statement asks for input position p, restored work tapes/heads/output, and a first exit within C·(w.length + pos + p + 1). `Simulation.lean::timed_rewind` returns to position 1, with bound pos + 2; it does not stop at position 0. For x = [false], w = [], p = 0, the sketched rewind followed by zero right moves leaves position 1. After one extra left move, copy–rewind–countdown–clear gives the claimed statement: the costs are bounded by `6*w.length + pos + 5*p + 13` with four seam dispatches, so a fixed coefficient suffices. Boundary checks: empty input/empty counter, leading-zero counters, and p = n + 1 all work. *Fix:* Insert the left move after `timed_rewind`, correct its quoted bound, and retain the finite first-exit construction. Add the space guarantee in finding 1.

> **3 (minor)** — Build/InputCall.lean · `FinTM.exists_inputCallTM` proof sketch. *Claim:* The statement is true, but the proposed inherited first-return proof lacks the callee's time-zero cut. *Evidence:* The requested module copies x from the blank seam, computes f x, and installs it on genuine tape 0 within c·(T(n) + n + (f x).length + 1), with positive return time. The copy establishes the exact entry seam of `exists_installCallTM`. However, that theorem excludes exits only at `0 < t' < t`, whereas `seamCompTM_firstReturn_ofCfg` also needs t' = 0. A stationary identity callee with `entry = exit` and return time 1 satisfies the install-call interface, but the proposed composite visits its final exit immediately after dispatch, before the proposed total time. Split on `entry = exit`; in that branch, `seamReleaseTM_firstReturn` supplies a fresh entry before composition. Empty input/result, identity f, and a constant-output zero-work-tape source then present no obstruction; the returned module still has positive tape count. *Fix:* Add the entry/exit case split and release adapter to the sketch. Do not infer a time-zero cut from a first-positive-return contract.

> **28 (note)** — Build/CfgRecord.lean · `exists_recordStepTM` functional content. *Claim:* The functional/time statement is constructible; its missing space guarantee is separate. *Evidence:* Read the finite state/tag/scanned-cell/edge data before writing; the next configuration is outside the window exactly when a moved work head crosses an edge, so that branch can return `no` with the original record. Otherwise rewrite the scanned cells, marks, state, tag, and clamped input position; the layout length on both sides is `k*(2*s + 1) + posWidth n + k + 4`, so the in-place interval is sufficient. To satisfy arbitrary host input positions, explicitly save the original position in binary, perform the simulated read, and restore it; when n = 0, detected by the one-digit position width, the input is known blank and need not be moved. Fixed many scans and amortized counter operations give O(L + n + 1). Checks: halted c uses `outputSymbol = none` and hupd, s = 0 with an outward move takes `no`, and k = 0 only updates state/input position/tag. *Fix:* Add finding 1's bound and name the saved-input-position and clamping obligations in the construction sketch.

> **29 (note)** — Build/CfgRecord.lean · `exists_recordEqTM`. *Claim:* Empty fields do not make the equality statement false; the one-sided length bound is adequate. *Evidence:* The fixed field count k + 3 lets finite control compare exactly that many fields, counting consecutive delimiters individually rather than treating a double blank as table termination. Every successful field comparison is followed by skips; at the first failure both heads have already returned to that field's starts, and only the preceding equal fields need to be crossed back. Each failed comparison costs at most twice the current fs field length plus two, so an arbitrarily longer gs does not violate the bound. Checks: all fields empty, unequal first fields, and equal prefixes followed by a short fs field versus a very long gs field. *Fix:* Keep the stronger arbitrary-field-list contract; neither nonempty fields nor `RecordValid` is necessary.

> **30 (note)** — Build/CfgRecord.lean · `exists_recordTestTM`. *Claim:* The state/tag test needs neither a window hypothesis nor any relation between host input y and recorded input x. *Evidence:* The first and last fields contain exactly the state and tag; k + 2 forward skips, two folds, and inverse skips read them and restore the head and tape. Their total length is O(L), and finite Q/T make dispatch on P finite. Checks: k = 0, a nonwindowed c, and a completely different native input y. A constant predicate may validly use an immediate verdict; it is still a reached, correct verdict. *Fix:* No statement change.

> **32 (note)** — TuringMachine/SymbolLift.lean · complete R8.0 public surface. *Claim:* The transport statements are correctly restricted and preserve exact time and work space. *Evidence:* `decodeBool` is a partial inverse of the embedding; actions map writes and emissions, configurations map tapes/output/input while preserving state and head coordinates, and lifted transitions decode reads before applying the original table. Thus the step square commutes on lifted configurations, iteration gives `liftSymbols_runFrom`, and equal head trajectories give equal visited sets and `spaceUsed`; initialization and the computation-via-e corollary follow on encoded inputs. Checks: zero tapes, halted configurations, and arbitrary nonempty output prefixes remain covered. Mixed record tapes are not globally lifted configurations: use R1 to isolate dedicated digit tapes and put the other tapes/output prefix in its frame. Keep `liftSymbols_step` public as the useful local form. *Fix:* No transport statement change. Do not apply the run or space theorem directly to a configuration with foreign symbols on its selected tapes.

> **35 (note)** — Build/CfgRecord.lean and Build/InputCall.lean · existential quantifiers and exit clauses. *Claim:* The modules are not satisfiable by a nonterminating implementation on an admissible entry. *Evidence:* Each record contract supplies a finite t and an exact verdict configuration; for stepping, the window predicate and its negation exhaust the two implications. `yes ≠ no` makes the verdicts observable. For `inputSeek`, entry ≠ exit follows globally: choose x = [], w = [], p = 0 and an entry configuration with input position 1; the required movement forces t > 0, and then the u = 0 cut excludes equality. It does not follow from the cut alone when t = 0. Empty tag types give no admissible tagged records, but the named consumer uses inhabited `Fin 3`; constant tests or identity steps may legitimately return at time 0. The input-call row's positive tape count prevents an empty-domain fake installation. *Fix:* No extra termination hypothesis is needed. Describe the input-seek nonvacuity argument with the required witness.

### Round 2 (`audits/s12-8-statements-r2-findings.md`)

> **3 (note)** — `Build/CfgRecord.lean` · `exists_recordStepTM`. *Claim:* The strengthened step contract is true and repairs the missing workspace guarantee. *Evidence:* The record has length \(L=k(2s+1)+\operatorname{posWidth}(n)+k+4\). Initialize a scratch counter of the position-field width, save the native position by binary counting, seek to the recorded position, read, and restore; binary carry accounting gives total time linear in native travel plus the width, with workspace linear in the width. For nonempty input, a one-step right probe distinguishes the two blank boundaries; for empty input, the one-digit width identifies that case and no native movement is needed. Finite control collects the scanned work symbols and edge flags; reject an outward head move before modifying the record, otherwise rewrite the fixed-length record and clean scratch. Checks: zero source tapes, halted source, radius zero, both clamped input boundaries, and empty input. *Fix:* No statement change. Preserve the saved-position, clamping, cleanup, and trajectory obligations in the fill.

> **4 (note)** — `Build/InputCall.lean` · `exists_inputSeekTM`. *Claim:* The strengthened seek contract is true, including its native-travel-independent head bound. *Evidence:* Copy, rewind to position 1, move left once, count down while moving the native head right, then clear scratch. The stated component bounds and four dispatches give \(t\le6\,w.length+d.inputPos.val+5p+13\), while every work head stays between its entry position minus 1 and entry position plus `w.length`. Thus one fixed coefficient satisfies both bounds. Empty counters, leading-zero counters, empty input, and \(p=n+1\) all satisfy the construction. *Fix:* No statement change.

> **5 (note)** — `Build/CfgRecord.lean` · `exists_recordEqTM`. *Claim:* Equality remains true with empty fields and with a second record much longer than the first. *Evidence:* Compare corresponding fields; a mismatch is detected after at most the first field’s length, and only equal fields are skipped. Therefore both traversals are bounded by the first layout’s length; the crossed fields have equal lengths and can be traversed backward to restore both heads. The fixed field count prevents adjacent blanks from being mistaken for an early table end. Checks: all fields empty, first-field mismatch against an arbitrarily long field, and disagreement in the last field. *Fix:* No statement change.

> **6 (note)** — `Build/CfgRecord.lean` · `exists_recordTestTM`. *Claim:* The strengthened test contract is true without a window hypothesis or any relationship between native input `y` and source input `x`. *Evidence:* Read the state field, cross the intervening fields, read the tag, and reverse those crossings; all work occurs within the record and its delimiters. The finite predicate determines the verdict, and the native input is unused. Checks: constant predicates, a non-windowed source configuration, and unrelated or foreign-symbol native inputs. *Fix:* No statement change.

> **7 (note)** — Four repaired contracts; `S128R2SpaceProbe` · head-range lemma; `Build/Embed`, `Build/Seam`. *Claim:* The repaired bounds imply the required workspace bounds and compose at restored entry heads. *Evidence:* A head-radius bound \(R\) gives `visitedByTapeHead d t j ⊆ Icc (d.workTapePos j − R) (d.workTapePos j + R)`, hence at most \(2R+1\) visited cells per tape and total space at most \(k(2R+1)\). Repeated calls with restored entry heads and uniformly bounded sizes remain in the same intervals; stationary dispatches add no cells. R1 preserves selected-tape visited sets and leaves unselected heads fixed. Consequently records of length \(O(S+1)\) use \(O(S+1)\) workspace per frame, and logarithmic-width seeks use logarithmic workspace; movement between frames must still be charged to the host’s bounded layout. A common coefficient can be enlarged to cover both time and radius. *Fix:* No further clause required. Consumers must intercept the verdicts; these contracts do not bound an unconnected module after its verdict time.

> **8 (note)** — `Build/InputCall.lean` · `FinTM.exists_inputCallTM`. *Claim:* The statement and corrected first-return construction are sound; this remains a time-only interface. *Evidence:* Copying native input onto tape 0 establishes the install-call entry seam. If the callee’s entry equals its exit, `seamReleaseTM_firstReturn` supplies a fresh entry without changing the positive-time run; otherwise the time-zero cut follows from inequality. This covers empty input/result, identity functions, and constant functions computed with zero source tapes, while the callable witness retains positive tape count. No small-space conclusion follows: the sketched input copy alone visits linearly many work cells. *Fix:* No space clause is needed for its advertised time-only use. A future space-preserving call requires a separately specified interface.

> **28 (note)** — `Build/CfgRecord.lean` · `cfgRecord_inj`. *Claim:* The injectivity statement is true on configuration cores and tags. *Evidence:* Equal fields give equal states, input positions, window contents, unique marked head positions, and tags; both window hypotheses extend tape equality outside the window. Conversely, equality of those components gives identical records. Checks: zero tapes, different outputs with the same core, and differing exterior tape cells when a window hypothesis is removed—the latter shows why the hypothesis matters. *Fix:* No statement change.

> **29 (note)** — `Build/CfgRecord.lean` · `RecordValid`, `recordValid_iff`. *Claim:* Validity is exactly the stated shape condition. *Evidence:* Forward, decode the fields of a windowed configuration. Backward, choose `List.replicate n false`, use the supplied position value, put each head at `m − s`, install the supplied window contents, and make exterior cells blank; this constructs the required witness. Checks: radius-zero singleton fields, zero or multiple marks, and an out-of-range position value. The corrected documentation properly requires external width/bound information for a uniform validator. *Fix:* No statement change.

> **31 (note)** — `SymbolLift.lean` · R8.0 public surface. *Claim:* The transport definitions and exported run, time, and space statements have the correct domain and strength. *Evidence:* Decoding inverts the embedding on digits; action/configuration lifting maps symbols while retaining state and head positions. One-step commutation gives run commutation, and identical head trajectories give equal visited sets and space. Initialization and `ComputesFunInTimeVia` follow on encoded inputs. Checks: zero tapes, halted configurations, and nonempty output prefixes. Mixed rich tapes require R1 isolation of dedicated digit tapes, rather than direct application of the globally lifted-configuration theorem. *Fix:* Keep the public one-step lemma and the stated domain restriction.

> **32 (note)** — Design O6; `SymbolLift`, `inputFoldTM`, `alphabet_reduction_spaceUsed`. *Claim:* Mandatory validation remains a sufficient and necessary safeguard for the chosen reduction interface. *Evidence:* The exported reduction requires a bound on all rich inputs, whereas lift transport controls encoded inputs. For example, a binary machine can stop after seeing blank twice, but move a work head forever if a symbol follows its first blank; binary inputs cannot exhibit the latter pattern, while `[foreign, e false]` can after decoding. A native fold rejects foreign symbols with fixed work heads; accepted inputs are encoded binary inputs. Correct consumers must also connect the repaired modules’ verdicts and final halt so their workspace bounds hold at every time. *Fix:* Retain O6 and the dedicated-digit-tape discipline.


## Gate guidance (binding; `audits/s12-8-statements-resolutions.md`)

- **The record step's obligations** (round-2 note 3, round-1 note 28): save the native input
  position in binary and restore it; seek, read, restore; clamp the position field at `0` and
  `|x| + 1`; reject an outward work-head move **before writing**; rewrite the fixed-length record;
  clean every scratch tape; keep the head-radius clause `C·(L + 1)`. `|x| = 0` is detected from
  the one-digit width and needs no native movement.
- **Intercept every verdict** (round-2 note 7). The contracts bound nothing after a module's own
  verdict or exit. Inside the record step, redirect at each sub-module's exit time (the phase
  lemma's guard is "no exit before `T`" and it dispatches at `T`); never run a sub-module past its
  exit. Consumers of your three record rows inherit the same duty.
- **R1 isolation of dedicated digit tapes** (round-1 note 32, round-2 notes 31–32). Never apply
  `liftSymbols_runFrom` or `liftSymbols_spaceUsed` to a configuration with a foreign symbol on a
  selected tape. Select only tapes 1–3, and keep them digit-only; the overlay transport
  (`liftSymbols_runFrom_over`) is the landed alternative for input-oblivious rows.
- **The input call is time-only** (round-2 note 8): add no space clause; a space-preserving call
  would be a new row.
- **The input seek** (round-1 minor 2, round-2 note 4): `timed_rewind` stops at `1`; one left move
  follows. **The input call** (round-1 minor 3): split on `entry = exit`.
- **No termination hypothesis** (round-1 note 35): each contract supplies its finite `t`.

## Ground rules (binding)

1. **File ownership.** Only `Build/CfgRecord.lean`, and in it only `exists_recordStepTM`'s
   body plus new `private` declarations. List every new declaration with its role.
2. **Statement freeze** over all seven targets (six now proved: their bodies are frozen too),
   **every landed definition and result**, and the first delivery's privates.
   - The landed definitions and results: `Cfg.InWindow`, `RecSym`, `recSymFintype`,
     `RecSym.digitEmb`, `binDigits`, `posWidth`, `cfgRecord`, `cfgRecord_length`,
     `RecordValid`, `RecordAt`.
   - The first delivery's privates are cited and reused, never changed.
   - No renames, re-signatures, restatements or attribution edits.
   - Docstrings stay. A flagged sketch appendix is expected where your route refines R8's
     sketch: `phaseHostTM` for its "R2 seams … dispatch", and the save loop's fuel countdown
     and complement.
3. **Status text.** Only `CfgRecord`'s module "Status" paragraph and the step's
   `## Main results` tag may change, to "proved"; flag each.
4. **Escalation** on anything unprovable as stated: stop, record the obstruction, deliver.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports unchanged.**
   - A Mathlib import is allowed only if a needed lemma requires it; flag it.
   - No TCSlib import may be added.
7. **One proof per shared argument.**
   - The step is one instance of the landed `phaseHostTM`: no private host, and no re-proof of
     its lemma.
   - There is **one** single-use private restriction-to-digit-bank lemma (R8), and no copy of
     `emitterP2_frame`.
   - Write no private field-layout, `bufferTape_map`, rewind-heads or `counterLoopCfg`-layout
     lemma; all are landed.
   - Use the **existing** `binDigits` value/injectivity pair. Reuse `RecordRun` for segment
     bookkeeping.
8. **Size: waived.** Large files are acceptable: `CfgRecord.lean` is 1,289 lines at the
   issue and may grow substantially. File size alone is not a driver. Create no new file, and
   report the final size.
9. **Continuation budget.** If your budget runs out, deliver a partial zip whose `REPORT.md`
   states:
   - what is proved;
   - which `private` helpers remain `sorry` (each with a "Proof sketch");
   - whether the target is proved modulo them.
10. **Hand-built tables** are allowed only for the native-input-head steps no row provides: the
    record step's `Probe`, `Save` and `Read`.
    - Each is a few states over `inputMoveAction`, stepped by `step_of_inputMoveAction`.
    - Each has a docstring naming the missing row ("no public native-input-head primitive").
    - Every other phase is a library row. The first delivery's report requested a public
      native-input-head primitive. It is a 12.2c candidate, not available to you.

## Duplication governance (binding)

Run the text-level screen **before and after**. The base, at this brief's issue tree, is
`audits/logs/s128-fill-C-cont-screen-base.txt`: **768 declarations, 689 pairs, 251,492
characters**. With `Build/Primitives.lean` appended it is
`…-screen-base-prim.txt`: **988 declarations, 1363 pairs, 529,577 characters**.
`CfgRecord`'s only existing pair is the first delivery's `RecordEqIndex` ↔ `RecordTestIndex`,
at 55–57%.

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/TuringMachine/Build/{CfgRecord,InputCall,Embed,Seam,Catalog,Loop,CounterLoop}.lean \
  TCSlib/Complexity/TuringMachine/{SymbolLift,Simulation}.lean
# and the same command with TCSlib/Complexity/TuringMachine/Build/Primitives.lean appended
```

- **No new cross-file pair** with a `CfgRecord` declaration on one side. That includes pairs
  with `InputCall`'s private seek helpers: your Save/Read tables are different machines, so
  keep their proofs different, or justify the pair.
- **Known hazards:**
  - the private R1 restriction against Primitives' `emitterP2_frame` (hence the second run,
    with Primitives: show no pair);
  - chaining phases against `phaseHostTM_run` (cite it per phase);
  - every `scanTM`/`copyTM` instantiation against its contract (cite it; never re-walk it);
  - the step's index type against `RecordTestIndex`/`RecordEqIndex`;
  - the save-loop orbit against the probe's `probeSaveBody_*` shape, which is evidence and
    not library;
  - the `incFixed`/`decFixed` digit lemmas against `CounterLoop`'s arithmetic (cite
    `counterWord_value` where it applies).
- List every new or changed in-file pair with a one-line justification. At 90% or more it is
  a copy: factor it.
- Quote all four outputs in `REPORT.md`, which carries **"new copies: none"**.

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/s128-fill-C-cont.txt`. It has **92 modules**: the
  upstream closure of the two stream-C files and of every module downstream of them, at the
  issue tree.
  - That is 18 more than the first order list. `SpaceComplexity/Inclusions` (B2b) now imports
    `CounterLoop`, `VirtualInput`, `Seam`, `Machines/Clean` and the Meyer tableau, and the
    `ClassPSPACE` facade reaches it.

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/s128-fill-C-cont.txt )
  ```

  **Base sorry-warning set, 13** (`audits/logs/s128-fill-C-cont-base-sorries.txt`).
  - Yours: `CfgRecord` 1 (`exists_recordStepTM`).
  - Elsewhere: `CounterLoop` 1 (`expandTM_run_ofCfg`, which waits on #38),
    `SpaceComplexity/Constructible` 2, `SpaceComplexity/ConfigGraph` 3,
    `SpaceComplexity/Inclusions` 1 (the private `b2b_host_contract`), `ClassPSPACE/TQBF` 4,
    `TuringMachine/NDCodes` 1.

  Record the base list by name first.
- **Final checks:**
  1. `CfgRecord`: zero errors, zero sorry warnings.
  2. Every other module of the order list, including `ClassPSPACE/TQBF`, `ClassPSPACE/Games`
     and the `ClassPSPACE` and `TuringMachine` facades: zero errors, and sorry warnings exactly
     the base's minus yours (**12**).
  3. Re-run the pre-ship probe: 0 errors.
- **Axiom prints** for all seven targets: every one within
  `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` (the modulo set is empty).
- **Lint:** `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`,
  0 FAIL.

## Out-of-scope sorries you will see (leave every one untouched)

- **§12.8 stream D:** `expandTM_run_ofCfg`. It waits on PR #38; if #38 has merged by your
  base, it is proved.
- **Elsewhere in the order list:**
  - `spaceConstructible_logSpace`, `spaceConstructible_linear`;
  - `NSPACE_subset_exp_dtime`, `NL_subset_P`, `polyTimeReducible_of_mem_NL`;
  - B2b's private `b2b_host_contract`;
  - `exists_adjacency_codec_cnf`, `TQBF_mem_PSPACE`, `TQBF_PSPACEHard`,
    `TQBF_PSPACEComplete`;
  - `exists_effectiveNDMachineCode`.

If a proof seems to *need* one of these, that is an escalation, not a license.

## REPORT.md checklist

- [ ] 1/1, or the partial frontier (rule 9); the base hash, the ancestor check, and whether
      your base includes #38.
- [ ] Every new declaration with its role:
  - the step's `phaseHostTM` index and phase family;
  - the restriction lemma;
  - the Probe/Save/Read tables (rule 10), with their gap sentences;
  - the pure digit and window lemmas.
- [ ] Imports unchanged (any Mathlib addition flagged); requested shared rows; escalations,
      or "none"; appendices and status updates, each flagged.
- [ ] Duplication: both screens, before and after; every new pair justified; "new copies:
      none".
- [ ] `CfgRecord`'s size; the final sweep tail; the re-run probe; seven axiom prints, with no
      `sorryAx`; the lint line. The diff touches only `CfgRecord.lean`.

## Known pitfalls at this pin (hard-won; most hit while building the probe)

- `rw [show (1 : ℕ) = 0 + 1 from rfl]` also rewrites the tape count of `MultiTapeTM 1 …` and the
  motive fails. Step one round with `change (M.step o).state = _` (`runFrom c 1` is `M.step c`
  definitionally).
- `simp` unfolds a machine's definition inside `counterLoopOrbit M …` arguments too, so terms
  stop matching. `generalize counterLoopOrbit M τ c r = o at …` first.
- A structure update inside `runFrom` needs an ascription:
  `({c with state := some s, inputPos := 1} : Cfg k Bool S x)`.
- `∑ r ∈ Finset.range d, τ (orbit r) + counterOverhead w (d + 1)` parses as
  `(∑ …) + counterOverhead …` (big operators bind at 67).
- `(-1 : SignType)` is `.neg` only up to unfolding: `change (moveInputPos o.inputPos SignType.neg).val = _`
  before `FinTM.moveInputPos_neg_val`.
- `decide` cannot evaluate `Nat.bits`/`Nat.size`, hence `posWidth`: use `Nat.size_eq_bits_len`,
  `Nat.lt_size_self`, `Nat.lt_size`, `Nat.size_one`. `binDigits` at a literal width does decide.
- `scanTM`'s accumulator is `A : Type` and the phase types must be finite: `ScanPhase A` is
  `Fintype` from `[Fintype A]`; `phaseHostTM`'s states `Σ i, Ph i` (the family is named `Ph`,
  over `I : Type`, at `Γ : Type`) need `[Fintype I]` and `[∀ i, Fintype (Ph i)]`, and
  `DecidableEq` likewise. `FinTM` wants `State : Type`.
- `simp` rewrites `Fin.castSucc 0` to `0` and `Fin.last 1` to `1` before `Fin.lastCases_castSucc`
  (which takes `i` explicitly) can fire: after `rw [counter_cfg_eq]`, close the tape facts with
  `simp only [Fin.lastCases_castSucc, Fin.lastCases_last]`.
- `rewind_heads`/`rewind_scan_heads` are declared in `Build/Catalog.lean` but live in
  `Turing.FinTM` (beside the `f2_` family), like `timed_rewind` in `Simulation.lean`.
- The overlay transport needs a table that ignores its input (`hin`) and never writes a blank
  (`hnb`): it serves `incrementTM`/`decrementTM`, not the seek or the save loop, which read the
  input.
- `counterLoopTM M` has `k + 1` tapes with the counter at `Fin.last k`; at `k = 1` it unifies with
  the R3 rows' `2`, and `Fin.last 1 = 1` is `rfl`. At `k = 0` (the save loop) the counter is the
  only tape.
- `counterLoopCfg` ignores the body configuration's state (its state field is the host's), and
  `counterWord` freezes at zero while the machine wraps: stay at `r ≤ value + 1`.
- `embedEmitCfg`'s output is `pre ++ c.output`: start every lifted `Bool` configuration with output
  `[]` and `pre :=` the host's output, which may contain foreign symbols.
- `Cfg.inputPos : Fin (|input| + 2)`: `0` and `|input| + 1` are the clamped blanks
  (`moveInputPos`). The lifted configuration's position is `Fin.cast` of the original; compare by
  `.val`.
- A halted source has `M.step c = c` and `M.outputSymbol c = none` (`step_of_halt`,
  `outputSymbol_of_halt`).
- `seamCompTM_firstReturn_ofCfg` needs the callee's cut at `t = 0` as well; `exists_installCallTM`
  gives it only for `0 < t`.
- `RecordAt` constrains only `[-1, |joinFields fs|]` from the head; a field's own delimiters come
  from `fieldsTape_field` and the span bound, never from cells beyond the layout.
- No `nlinarith`/`linarith` needed: `omega` with powers of two as atoms (`Nat.one_le_two_pow`,
  `pow_succ`). The linter needs a literal "Proof sketch" before every `sorry` (partial delivery
  only).
