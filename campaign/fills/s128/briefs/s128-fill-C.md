# §12.8 fill — stream C: configuration records and native-input modules (`Build/CfgRecord.lean`, `Build/InputCall.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 182e6f44c5135f07cb4965a42fc6865da720d553 HEAD` succeeds. That
  commit contains the §12.8 statement layer (PR #28, its gate closed in round 2:
  `audits/s12-8-statements-{findings,r2-findings,resolutions}.md`), the maintainer's pre-issue
  shared layer (`5afed90b`, "§12.8 fill pre-issue 2": the phase host, the promoted layout,
  rewind and lift lemmas, the field-layout facts, and both import edges this stream needs), and
  the order list `briefs/orders/s128-fill-C.txt`. If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested `fill/s128-C`). Record the base
  hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-s128-C.zip`, containing
  `REPORT.md`, the full modified sources, a `git format-patch` series against your base, a git
  bundle, the final sweep log, the axiom log, and `SHA256SUMS`.

## What this is

Fill the **seven audited-true statements** of the §12.8 rich-alphabet design that live in two
files (design `machine-library-design.md` §12.8a §3, rows R8.5b, R8.5e and R8.7):

| Row | Contract | File |
|---|---|---|
| R8.5b | `Turing.exists_inputSeekTM`: move the native input head to the binary value on a work tape, every work tape and head restored, head radius `C·(|w| + 1)` | `Build/InputCall.lean` |
| R8.5e | `Turing.FinTM.exists_inputCallTM`: a function-level machine on the native input at a clean seam (time-only) | `Build/InputCall.lean` |
| R8.7 pure | `Turing.cfgRecord_inj`, `Turing.recordValid_iff` | `Build/CfgRecord.lean` |
| R8.7 rows | `Turing.exists_recordStepTM` (one simulated step), `Turing.exists_recordEqTM`, `Turing.exists_recordTestTM` | `Build/CfgRecord.lean` |

Three other batches fill, **in parallel**, the rows you build on: stream A (Catalog Part 3 and
`Build/Seam`: the field layout, framed compare, skip family, `scanTM` and its identities,
`seamCompTM₂`), stream B (`Build/Scan`: the writers, `inputCopyTM`, `inputFoldTM`), stream D
(`Build/CounterLoop`: R8.0b and `expandTM`). Their statements are audited and frozen, so you
**cite them while they are still sorried**: your proofs are "proved modulo" them, and your axiom
prints show `sorryAx` exactly through them (the modulo set, below). Nothing of yours waits for
them.

Read in full: design §12.6, §12.7, §12.8 and §12.8a (especially §3's R8.7 table and §4); the
round-1 findings (finding 1, minors 2–3, notes 28–30, 32, 35), the round-2 findings (notes 3–8,
28, 29, 31, 32) and the resolutions — the binding parts are quoted below; `policy.md` §1
(construction reuse, hand-built machines, duplication); `workflow.md` §4.

**Pre-ship check (maintainer, executed):** `audits/evidence/s12-8/S128FillCProbe.lean.txt`
(output `.out`), run at the issue tree against the landed shared layer: 0 errors, 0 warnings, no
`sorry` of its own. It `#check`s
the 7 targets and 133 cited names, and elaborates the route steps this brief prescribes: the
lifted seek on a rich bank through R1; the restriction of a rich host to a dedicated digit bank
(`probeRestrict`, the form of your one private R1 lemma); the seek's round body, its
`counterLoopTM_run_done` countdown landing at `p`, its `timed_rewind` table and the extra left
move, and the four-phase seek machine (`probeSeekTM`, finite states); both branches of the input
call; the phase host and its phase lemma (now landed as `phaseHostTM`, `phaseHostTM_run`, the
probe's statement); the record-step save loop through `counterLoopTM_run_escape`; the
`binDigits`, `posWidth` and complement arithmetic; the field-0 compare of `recordEqTM`. Every
probe lemma prints within `[propext, Classical.choice, Quot.sound]`, except `probeCopy_seam`
(`sorryAx` through stream B's `inputCopyTM_run_ofCfg`). It uses the landed `phaseHostTM_run`, `counter_cfg_eq`,
`FinTM.bufferTape_map` and `FinTM.rewind_heads` in place of the probe's local copies and
`#check`s the 22 landed names: 0 errors, 0 warnings, same axiom prints.

## Owned files and targets (modify these and nothing else)

Lines are at the issue commit.

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `Build/CfgRecord.lean:175` | `Turing.cfgRecord_inj` | R3, pure | — |
| 2 | `Build/CfgRecord.lean:206` | `Turing.recordValid_iff` | R4, pure | — |
| 3 | `Build/InputCall.lean:103` | `Turing.exists_inputSeekTM` | R1, four R2 seams | — |
| 4 | `Build/InputCall.lean:63` | `Turing.FinTM.exists_inputCallTM` | R2, copy + install call | — |
| 5 | `Build/CfgRecord.lean:331` | `Turing.exists_recordTestTM` | R6, phase host | — |
| 6 | `Build/CfgRecord.lean:303` | `Turing.exists_recordEqTM` | R7, phase host | — |
| 7 | `Build/CfgRecord.lean:261` | `Turing.exists_recordStepTM` | R8, phase host | 3 |

Fill in the table's order; 7 is the long pole (more than half the stream) and stays in this
batch, under the continuation provision (ground rule 9) if your budget runs out. The paths are
under `TCSlib/Complexity/TuringMachine/`. The facade is not yours.

### Proof routes (binding; the docstring sketches, amplified by the gates)

**R1. `exists_inputSeekTM`** (round-1 minor 2, round-2 note 4). Two tapes: `w` on tape `0`, tape
`1` the scratch and the counter. The machine is four phases glued by `seamCompTM`, exactly the
probe's `probeSeekTM`:

```lean
seamCompTM (seamCompTM (seamCompTM (copyTM 2 0 1) .done Rw .start) (Sum.inr .done)
  (counterLoopTM Step () none) (.dec .run)) (Sum.inr CounterLoopState.done) (clearTM 2 1) .sweep
```

- **Copy** `w` to tape `1`: `copyTM_run_ofCfg 0 1` (`2|w| + 2`; tape 1 is blank, so `w` is
  delimited there).
- **Rewind**: a private table `Rw` (`start`, `scan`, `left`, `done`) in `FinTM.timed_rewind`'s
  shape, then one left move to the end marker `0` (`probeRewindTM`); time `≤ pos + 3`. Cite
  `Turing.FinTM.rewind_heads` (Catalog:10376; it is `timed_rewind` plus "every work head fixed at
  every prefix", with `FinTM.rewind_scan_heads` beneath it) for the run and the heads, and
  `controlAction_apply` for the extra step. The exit `done` is a stationary self-loop, and the
  state at the rewind's time is `left`; that gives the no-earlier-exit cut (one private
  five-line lemma).
- **Countdown**: `counterLoopTM_run_done` with the private one-state body `Step` ("input head
  right", `inputMoveAction 1`), `τ := 1`, `p` rounds from position `0` to `p`
  (`probeSeekBody_orbit_input`, `probeSeekBody_hround`; `p ≤ |x| + 1` prevents clamping). The
  host configuration after the rewind is a `counterLoopCfg`: cite `Turing.counter_cfg_eq`
  (CounterLoop:626, public since the pre-issue layer). Cost `p + counterOverhead w (p + 1) ≤ 5p + 2|w| + 2`
  (`counterOverhead_le`). The counter ends all `true` with its head back.
- **Clear** tape `1`: `clearTM_run_ofCfg 1` on `List.replicate |w| true`.

Glue by `seamCompTM_run_ofCfg`; cuts by `seamCompTM_firstReturn_ofCfg` at each level (each
callee's own no-earlier-exit clause, including time `0`). Total `≤ 6|w| + pos + 5p + 12`, so
`C := 13` serves time and radius. Head clause: `seamCompTM_visitedByTapeHead_ofCfg` with each
phase's trajectory clause, every head within `[pos − 1, pos + |w|]`. Finish: tape `1` blank again,
tape `0` untouched, heads restored, output unchanged (no phase emits). Check `w = []` (`p = 0`)
and `p = |x| + 1`. This target cites **no** sorried statement: its print must be clean.

**R2. `FinTM.exists_inputCallTM`** (round-1 minor 3, round-2 note 8). Obtain
`⟨C₀, entry, exit, c, hk, hC⟩ := FinTM.exists_installCallTM M f T hM`, then
`by_cases h : entry = exit`:

- `entry ≠ exit`: the module is `⟨C₀.k, SweepPhase ⊕ C₀.State, seamCompTM (inputCopyTM C₀.k
  ⟨0, hk⟩) .done C₀.tm entry⟩` with entry `inl .sweep`, exit `inr exit`, coefficient `c + 3`,
  tape count `hk`. Copy from the blank seam ends at `Cfg.ofWords .done (stateWord C₀.k x)`
  (`probeCopy_seam`, from `inputCopyTM_run_ofCfg`); then `seamCompTM_run_ofCfg` with `hC x x`'s run.
  First return: `seamCompTM_firstReturn_ofCfg`, the callee's cut at `t = 0` from `h`.
- `entry = exit`: the callee is `seamReleaseTM C₀.tm exit` with entry `inl ()` and exit
  `inr exit`; `seamReleaseTM_firstReturn … rfl hpos hrun rfl hfirst` supplies the full cut.
  **Do not infer a time-zero cut from the positive-return contract** (round-1 minor 3).

Time `2|x| + 3 + t ≤ (c + 3)(T|x| + |x| + |f x| + 1)`. The interface is time-only: no space
clause is owed or to be added (round-2 note 8). This target is modulo `inputCopyTM_run_ofCfg`
(stream B) only.

**R3. `cfgRecord_inj`** (round-2 note 28). `→`: peel `cfgRecord` with `List.cons` injectivity.
States from F0. Input positions from F1: equal `binDigits W` words with values below
`2 ^ W` (`n + 1 < 2 ^ posWidth n` via `Nat.size_eq_bits_len`, `Nat.lt_size_self`) decode to equal
values (`Nat.ofDigits 2 ((binDigits w v).map Bool.toNat) = v` for `v < 2 ^ w`, induction on `w`
with `Nat.testBit_add_one`; both are proved in the probe), then `Fin.ext`. Tapes: `funext z`;
for `|z| ≤ s` use index `(z + s).toNat` of the field; otherwise both window hypotheses give
blanks. Heads: `c`'s mark sits at index `pos + s`, in range by the window, and forces `d`'s. Tags
from the last field. `←`: rewrite. Checks: `k = 0`, different outputs with equal cores.

**R4. `recordValid_iff`** (round-2 note 29). `→`: read the shape off `cfgRecord`, with
`v := c.inputPos.val ≤ |x| + 1` and the mark at index `(pos + s).toNat`. `←`: `choose` the
contents `cs i` and marks `m i`; take `x := List.replicate n false`, the state and tag from their
cells, the position `⟨v, _⟩`, head `m i − s`, cell `z` from `cs i (z + s).toNat` when `|z| ≤ s`
and blank otherwise; the configuration is windowed and `List.ext_getElem` with
`fs.length = k + 3` closes. Checks: `s = 0` singleton fields, zero or two marks, an
out-of-range position value.

**R5. The phase host** (used by 5, 6, 7; **landed, public, proved**: cite it, write no private
host). `seamCompTM` has one exit and `seamCompTM₂` two, while the record rows branch on data of
parametric size and repeat a row `k + 2` or `k + 3` times. The pre-issue layer provides
`Turing.phaseHostTM` (Seam:774) and its phase lemma `Turing.phaseHostTM_run` (Seam:791):

```lean
def phaseHostTM {k : ℕ} {Γ : Type} {I : Type} {Ph : I → Type}
    (M : (i : I) → MultiTapeTM k Γ (Ph i)) (q0 : Σ i, Ph i)
    (red : (i : I) → Ph i → Option (Σ i, Ph i)) : MultiTapeTM k Γ (Σ i, Ph i)
  -- red i s = some q': one stationary, silent dispatch step to q'; else (M i).tr s, tagged by i
theorem phaseHostTM_run … (i : I) (c c' : Cfg k Γ (Ph i) x) (T : ℕ)
    (h : (M i).runFrom c T = c') (s' : Ph i) (hs' : c'.state = some s')
    (q' : Σ i, Ph i) (hred : red i s' = some q')
    (hguard : ∀ u < T, ∀ s, ((M i).runFrom c u).state = some s → red i s = none) :
    (∀ u ≤ T, (phaseHostTM M q0 red).runFrom (c.mapState (Sigma.mk i)) u =
        ((M i).runFrom c u).mapState (Sigma.mk i)) ∧
      (phaseHostTM M q0 red).runFrom (c.mapState (Sigma.mk i)) (T + 1) =
        c'.mapState (fun _ => q')
```

Each record row is one `phaseHostTM` instance: the index `I` carries the stage, the field
counter and the data read so far; verdict anchors are dedicated indices, so "no verdict
earlier" is index inequality along the tagged runs. Chain phases by applying `phaseHostTM_run`
once per phase (a private induction over the field counter is fine; a re-proof of the phase
lemma is not). Library rows enter as phases unchanged, at the host's tape count; `Bool` rows
enter lifted (R8).

**R6. `exists_recordTestTM`** (round-1 note 30, round-2 note 6). One tape. Phases: fold F0
(`scanTM 1 0 (scanFold δ) scanKeep none`, `A := Option (Option Q)`) → `skipTM` over fields
`0, …, k + 1` → fold the tag with `δ` computing `P q ·` from the `q` in the index
(`A := Option Bool`) → `skipBackTM` over the same `k + 2` fields → `yes`/`no`. Field framing:
`RecordAt` with `fieldsTape_field` and Catalog's public layout facts (`fieldOffset_succ`,
`fieldOffset_add_length_le`, …; see "Cited infrastructure"). Folds write nothing:
`scanResult_fold` returns the word itself, so the scan's rewrite is the identity on the
`RecordAt` cells. No window hypothesis and no relation between `y` and `x` are used. A constant
`P` may still run all phases.

**R7. `exists_recordEqTM`** (round-1 note 29, round-2 note 5). Two tapes, no scratch, so no
counter: the count `k + 3` lives in the index. For field `j`: `compareTM 2 0 1` on the two
current fields (the probe's field-0 instance); `done false` → `skipBackTM` both tapes over the
`j` crossed fields → `no`; `done true` with `j < k + 2` → `skipTM 2 0`, `skipTM 2 1` → `j + 1`;
`done true` at `j = k + 2` → `skipBackTM` both over `k + 2` fields → `yes`. Crossed fields are
equal on both tapes, so tape 1 costs what tape 0 does; a failing compare costs at most
`2|fs[j]| + 2` however long `gs[j]` is. Empty fields are legal (compare `δ = 0`; skip `1`; skip
back `3`). Never treat a double blank as the end: cells past `gs`'s layout are arbitrary.

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

## Cited infrastructure (public at the issue commit)

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

**Proved modulo (audited, sorried at issue, filled in parallel; cite, never re-prove):**

- stream A: `fieldsTape_field`, `compareTM_run_ofCfg`, `skipTM_run_ofCfg`,
  `skipBackTM_run_ofCfg`, `scanTM_run_ofCfg`, `scanResult_fold`, `scanResult_map`,
  `scanResult_shiftRight`, `scanResult_shiftLeft`;
- stream B: `inputCopyTM_run_ofCfg`.

| Target | Expected print at your delivery | Its modulo set |
|---|---|---|
| `cfgRecord_inj`, `recordValid_iff`, `exists_inputSeekTM` | `[propext, Classical.choice, Quot.sound]` | none |
| `FinTM.exists_inputCallTM` | + `sorryAx` | `inputCopyTM_run_ofCfg` |
| `exists_recordTestTM` | + `sorryAx` | `fieldsTape_field`, `scanTM_run_ofCfg`, `scanResult_fold`, `skipTM_run_ofCfg`, `skipBackTM_run_ofCfg` |
| `exists_recordEqTM` | + `sorryAx` | `fieldsTape_field`, `compareTM_run_ofCfg`, `skipTM_run_ofCfg`, `skipBackTM_run_ofCfg` |
| `exists_recordStepTM` | + `sorryAx` | stream A's nine above |

**Do not cite** `scanResult_carry`, `seekEndTM_run_ofCfg`, `seekStartTM_run_ofCfg`,
`seamCompTM₂_run_ofCfg`, `writeConstTM_run_ofCfg`, `inputFoldTM_run_ofCfg`, `expandTM_run_ofCfg`,
or anything of R8.0b: the routes do not need them, and each would widen your modulo set. Do not
cite anything downstream (`ClassPSPACE`, `SpaceComplexity`).

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

1. **File ownership.** Only `Build/CfgRecord.lean` and `Build/InputCall.lean`; in each, only the
   targets' bodies plus new `private` declarations. List every new declaration with its role.
2. **Statement freeze** over the seven targets **and every landed definition and result**:
   `Cfg.InWindow`, `RecSym`, `recSymFintype`, `RecSym.digitEmb`, `binDigits`, `posWidth`,
   `cfgRecord`, `cfgRecord_length`, `RecordValid`, `RecordAt`. No renames, re-signatures,
   restatements or attribution edits. Docstrings stay; flagged sketch appendices are allowed and
   expected where your route refines a sketch (`phaseHostTM` for R8's "R2 seams … dispatch";
   the save loop's fuel countdown and complement). The pre-issue layer's declarations are landed
   results too: cite them, never edit them.
3. **Status text.** Only the module docstrings' "Status: statements" paragraphs and the
   "(statement)" tags of `## Main results` may change, to "proved" (or "proved modulo …");
   flag each.
4. **Escalation** on anything unprovable as stated: stop on that item, record the obstruction,
   continue with the rest.
5. **No touching other sorries.** Cite, never re-prove, proved or audited material.
6. **Imports unchanged.** The two edges this stream needs (`InputCall` → `Build/Seam`,
   `CfgRecord` → `Build/InputCall`) landed with the pre-issue layer. A Mathlib import only if a
   needed lemma requires it; flag it. No TCSlib import may be added.
7. **One proof per shared argument**: every record row is an instance of the landed
   `phaseHostTM` (no private host, no re-proof of its lemma); one single-use private
   restriction-to-digit-bank lemma (R8), no copy of `emitterP2_frame`; no private field-layout,
   `bufferTape_map`, rewind-heads or `counterLoopCfg`-layout lemma (all are landed); one
   `binDigits` value/injectivity pair, shared by R3, R4 and R8; one input-only "work heads fixed"
   argument per file.
8. **Size: waived.** Large files are acceptable for this fill (`CfgRecord.lean` may reach about
   2000 lines). Create no new file; report the final size of each owned file.
9. **Continuation budget.** If your budget runs out, deliver a partial zip whose `REPORT.md`
   states which targets are proved, which `private` helpers remain `sorry` (partial delivery
   only, each with a "Proof sketch"), and which proved targets are proved modulo them.
   Targets 1–6 first; 7 may be the continuation.
10. **Hand-built tables** are allowed only for the native-input-head steps no row provides —
    the seek's `Rw` and `Step`, the record step's `Probe`, `Save` and `Read` — each a few states
    over `FinTM.controlAction` (`Rw`, to meet `rewind_heads`' hypotheses) or `inputMoveAction`
    (the rest, stepped by `step_of_inputMoveAction`), each with a docstring naming the missing
    row ("no public native-input-head primitive"). Every other phase is a library row.

## Duplication governance (binding)

Run the text-level screen **before and after** (base at the pre-issue layer:
`audits/logs/s128-fill-C-screen-before.txt`, 714 declarations, 680 pairs, 248,080 characters;
with `Build/Primitives.lean` appended, `…-screen-before-prim.txt`, 934 declarations, 1354 pairs,
526,165 characters; **no pair involves an owned file** in either):

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/TuringMachine/Build/{CfgRecord,InputCall,Embed,Seam,Catalog,Loop,CounterLoop}.lean \
  TCSlib/Complexity/TuringMachine/{SymbolLift,Simulation}.lean
# and the same command with TCSlib/Complexity/TuringMachine/Build/Primitives.lean appended
```

- **No new cross-file pair** with an owned-file declaration on one side, including between the
  two owned files.
- **Known hazards:** the seek's rewind against `timed_rewind`, `f2_catalogRewind`,
  `loop_rewind_bounded`, `FinTM.rewind_heads` (cite `rewind_heads`; never restate a rewind); the
  `counterLoopCfg` layout (cite `counter_cfg_eq`); the private R1 restriction against
  Primitives' `emitterP2_frame` (hence the second run with Primitives: show no pair); any
  chaining of phases against `phaseHostTM_run` (cite it per phase); the seek body's orbit lemmas
  (InputCall) against the save body's (CfgRecord): different machines, keep their proofs
  different or justify the pair; every `copyTM`/`scanTM` instantiation against its contract
  (cite, never re-walk).
- List every new in-file pair with a one-line justification; at 90% or more it is a copy: factor
  it.
- Quote all four outputs (both runs, before and after) in `REPORT.md`, which carries **"new
  copies: none"**.

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/s128-fill-C.txt` (74 modules: the upstream closure of the
  two owned files and of every module downstream of them, with the landed edges, so `Seam`
  precedes `InputCall` and `InputCall` precedes `CfgRecord`):

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/s128-fill-C.txt )
  ```

  Base sorry-warning set, **37**: yours `CfgRecord` 5, `InputCall` 2; elsewhere `Build/Seam` 1,
  `Build/Catalog` 12, `Build/Scan` 4, `Build/CounterLoop` 1, `SpaceComplexity/Constructible` 2,
  `SpaceComplexity/ConfigGraph` 3, `SpaceComplexity/Inclusions` 2, `ClassPSPACE/TQBF` 4,
  `TuringMachine/NDCodes` 1.
- **Final checks:** (1) owned modules: zero errors, zero sorry warnings; (2) every later module of
  the order list (`ClassPSPACE/TQBF`, `ClassPSPACE/Games`, the `ClassPSPACE` and `TuringMachine`
  facades) and every earlier one: zero errors, sorry warnings exactly the base's minus your seven
  (**30**); (3) re-run the pre-ship probe: 0 errors.
- **Axiom prints** for the seven targets, matching the table in "Cited infrastructure": standard
  three for 1–3; `sorryAx` for 4–7, **only** through their listed modulo sets (list, per target,
  every sorried declaration your proof cites). The maintainer re-prints after A and B integrate,
  when all seven must be within `[propext, Classical.choice, Quot.sound]`.
- **Lint:** `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`, 0 FAIL.
- **After delivery:** stream D generalizes `counterLoopCfg` and `counterLoopOrbit` in place
  (types only). The maintainer re-runs your sweep after D integrates; nothing is asked of you.

## Out-of-scope sorries you will see (leave every one untouched)

- **Streams A, B, D (parallel):** Catalog Part 3's twelve (`fieldsTape_field`,
  `compareTM_run_ofCfg`, `skipTM_run_ofCfg`, `skipBackTM_run_ofCfg`, `seekEndTM_run_ofCfg`,
  `seekStartTM_run_ofCfg`, `scanTM_run_ofCfg`, `scanResult_fold`, `_map`, `_shiftRight`,
  `_shiftLeft`, `_carry`); `seamCompTM₂_run_ofCfg`; Scan's four (`writeConstTM_run_ofCfg`,
  `writeAdvTM_run_ofCfg`, `inputCopyTM_run_ofCfg`, `inputFoldTM_run_ofCfg`); `expandTM_run_ofCfg`.
- **Elsewhere in the order list:** `spaceConstructible_logSpace`, `spaceConstructible_linear`;
  `NSPACE_subset_exp_dtime`, `NL_subset_P`, `polyTimeReducible_of_mem_NL`; `NP_subset_PSPACE`,
  `SAT3_mem_PSPACE`; `exists_adjacency_codec_cnf`, `TQBF_mem_PSPACE`, `TQBF_PSPACEHard`,
  `TQBF_PSPACEComplete`; `exists_effectiveNDMachineCode`.

If a proof seems to *need* one of these beyond the modulo sets above, that is an escalation, not a
license.

## REPORT.md checklist

- [ ] 7/7, or the partial frontier (rule 9); the base hash and the ancestor check.
- [ ] Every new declaration with its role: each record row's `phaseHostTM` index and phase
      family; the restriction lemma; the hand tables (rule 10) with their gap sentences; the pure
      helpers.
- [ ] Imports unchanged (Mathlib additions, if any, flagged); requested shared rows (a
      native-input-head primitive row; a general R1 reconstruction, if you wanted one);
      escalations, or "none"; appendices and status updates, each flagged.
- [ ] Per target, the sorried declarations it cites (the modulo ledger).
- [ ] Duplication: both screens, every new pair justified, "new copies: none".
- [ ] Both owned files' sizes; the final sweep tail; the re-run probe; seven axiom prints; the
      lint line. The diff touches only the two owned files.

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
