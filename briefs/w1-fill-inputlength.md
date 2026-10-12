# Ch3–4 fill campaign — wave-1 fill: R8.5c, the input length (`Turing.exists_inputLengthTM`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 78116c5d5db075c9ce46ecec0b56735d1c600bef HEAD`
  succeeds. That commit contains:
  - the closed wave-1 statement gate (PR #43) and its records (`audits/wave1-statements-*`);
  - R8.0b (`counterLoopTMVia`, PR #38) and R8.6 (`expandTM_run_ofCfg`), both proved;
  - the §12.8 Catalog Part 3, Scan, InputCall and Seam rows, all proved;
  - this round's order lists, base sorry sets, screen bases and pre-ship logs.

  If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested `fill/w1-inputlength`). Record the base
  hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-w1-inputlength.zip`, containing
  `REPORT.md`, the full modified sources, a `git format-patch` series against your base, a git
  bundle, the final sweep log, the axiom log, and `SHA256SUMS`.

## Parallel batches this round (disjoint files; never edit another batch's file)

| Batch | Brief | Owns |
|---|---|---|
| R8.5c, the input length | `briefs/w1-fill-inputlength.md` | `TuringMachine/Build/InputLength.lean` |
| §12.8b record tables | `briefs/w1-fill-recordtable.md` | `TuringMachine/Build/RecordTable.lean` |
| §12.10 W2-S and W2-C | `briefs/w2-fill-oraclesim.md` | `TuringMachine/Build/OracleSim.lean` |
| §12.10 W2-V | `briefs/w2-fill-certshell.md` | `TuringMachine/Build/CertShell.lean` |
| B5a, the code simulator | `briefs/b5a-fill.md` | `TuringMachine/CodeSimulator.lean`, `TuringMachine/Codes2Tape.lean`, `Diagonalization/EXPCOM.lean` |
| The ND code scheme | `briefs/ndcodes-fill.md` | `TuringMachine/NDCodes.lean` |
| B4a, the TQBF codec | `briefs/b4a-fill-codec.md` | `ClassPSPACE/TQBF.lean` (one target) |

Also in flight: §12.8 C continuation 3 (`Build/CfgRecord.lean`), B7 continuation 3
(`Logspace/QueryReshape.lean`, `Logspace/Reductions.lean`) and the B7 multiplication batch
(`Logspace/Mult.lean`); and a maintainer PR filling `POracle_eq_P_of_mem_P`
(`ClassOracle/Classes.lean`) and `baker_gill_solovay` (`Diagonalization/Relativization.lean`).
A parallel batch's work is invisible to your base and your screen.

## What this is

The wave-1 statement layer landed three library extensions with audited-true sorried rows
(`machine-library-design.md` §§12.8b, 12.10, 12.11; gate closed at round 2,
`audits/wave1-statements-r2-findings.md`). This batch fills the smallest: **R8.5c**, a `Bool`
module that writes `Nat.bits |x|` on a work tape in time `C·(|x| + 1)` with logarithmic work
space. Its consumers are the record template (the parallel record-table batch cites it, proved
modulo) and the constructibility files.

**Read first:** the target's docstring (binding); design §12.8b ("Decisions", item 3); the
wave-1 findings rounds 1–2 and `audits/wave1-statements-resolutions.md` (note 44 binds you);
`policy.md`; `workflow.md` §4.

**Pre-ship check (maintainer, executed at this brief's ancestor):**
`audits/evidence/wave1-statements/S128bStatementsProbe.lean.txt`, re-run at the issue tree
(`audits/logs/w3-preship.log`): 0 errors, 0 warnings, output identical to round 2's.

## Owned files and targets (modify these and nothing else)

Lines are at the issue commit.

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `TuringMachine/Build/InputLength.lean:86` | `Turing.exists_inputLengthTM` | a framed in-place binary counter driven by one input pass | — |

- **Owned:** `TuringMachine/Build/InputLength.lean`, for this target's body and new `private` declarations.
- **Not yours:** every other file, including `Build/Catalog.lean` (whose private `f2_counterTM` is your template) and the facade.

### Proof route (binding; the docstring's sketch, amplified)

- **One pass over the input** drives an in-place binary counter on tape `0`. For each input
  symbol, move the input head right and increment: the carry turns the maximal `true` prefix to
  `false` and writes `true` on the next cell, which is the blank just after the word when the
  counter overflows. So the width grows by one cell exactly at the powers of two.
- **Return pass:** bring the counter head back to its first cell, guided by the blank delimiter
  on its left; at the input's right end marker, walk the input head back to position `1` (the
  `Turing.inputFoldTM_run_ofCfg` return) and exit.
- **Ledger:** the increments from `0` to `|x|` cost `Σ_v (2·p_v + 2)` for the true-prefix
  lengths `p_v`, which telescopes against twice the number of `true` cells, as in
  `Turing.counterOverhead_le_of_le` mirrored; the total is linear in `|x|`. The counter head stays
  in `[pos − 1, pos + |bits |x||]`.
- **The table.** No public input-driven loop host exists (`counterLoopTM` needs its round count
  on a tape, which is what is being computed), so this row is a **hand-built table**: the
  counting phase of Catalog's private `f2_counterTM`, without its emission, framed. You prove the
  framed round induction for this table directly. §12.8a's "increment with width extension" does
  not work here: `seekEndTM` stops one cell past the delimiter (design §12.8b decision 3).
- At `x = []` nothing is written, since `Nat.bits 0 = []`. The first-arrival clause ("not
  earlier") and the head clause hold at every `u ≤ t`.

## Gate guidance (binding)

- **Note 44.** Record in `REPORT.md` the future factoring against Catalog's private
  `f2_counterTM`: name the pair (table and round induction), measured. **No counter proof is
  copied now**: write the induction for your own table.
- **Note 46.** File size is not a driver.
- **Intercept every verdict** (§12.8 statement gate, round-2 note 7). The contracts bound
  nothing after a module's own verdict or exit. Redirect at each sub-module's exit time; never
  run a sub-module past its exit.
- **R1 isolation of dedicated digit tapes** (round-1 note 32, round-2 notes 31–32). Never apply
  `liftSymbols_runFrom` or `liftSymbols_spaceUsed` to a configuration with a foreign symbol on a
  selected tape; the overlay transport (`liftSymbols_runFrom_over`) is the alternative for
  input-oblivious rows.
- **No termination hypothesis** (round-1 note 35): each contract supplies its finite `t`.
- **The work-space clause** bounds every work head through the verdict to `C·(size + 1)` cells of
  its entry position (round-1 major 1); the exact finish restores every head, the input position,
  the scratch and the output.

## Cited infrastructure (public and proved at the issue commit)

- `Turing.inputFoldTM_run_ofCfg` (`Build/Scan`) for the input return; `Turing.counterOverhead_le_of_le`,
  `counterWord_value`, `counterWord_length` (`Build/CounterLoop`) for the arithmetic;
  `FinTM.bufferTape` and its simp lemmas, `MultiTapeTM.runFrom_add`, `runFrom_succ_eq_step(')`,
  `exists_first_halt`, `step_of_halt`, `visitedByTapeHead`; Catalog Part 3's one-step lemmas
  for hand tables (`step_of_tapeAction_move`/`_write`, `step_of_inputMoveAction`); `rewind_heads`,
  `rewind_scan_heads`.
- **Proved modulo: none.** Every cited row is proved.
- **Do not cite** anything of `RecordTable`, `CfgRecord`'s record-step row, or the
  `SpaceComplexity` constructibility files (they are consumers).

## Ground rules (binding)

1. **File ownership.** Only `Build/InputLength.lean`. Change only the target's body, and add new `private` helpers
   there. List every new declaration with its role. A lemma that genuinely belongs in a shared
   file is written privately, flagged in `REPORT.md` as a promotion candidate, and promoted by
   the maintainer at integration (`workflow.md` §4, rule 1).
2. **Statement freeze** over every target and every landed declaration: no renames,
   re-signatures, restatements or attribution edits. Docstrings stay; a flagged
   **"Fill appendix"** is expected wherever your proof refines or replaces a sketch's route.
3. **Status text.** Only your files' status text may change: the module's "Status" paragraph,
   its "Main results" tag, and your targets' "(statement)"/"(spec, fill pending …)" tags, each to
   "proved" (or to the new count, for a file you share with later targets); flag each. No new
   public declaration unless this brief names it.
4. **Escalation** on anything unprovable as stated, including a cited row that does not
   compose as the route says: stop on that item, record the obstruction, and continue with the
   rest.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Unchanged: the file imports only `Build/CounterLoop`. No TCSlib import may be added. A Mathlib import is allowed only if a needed lemma requires it; flag
   it.
7. **One proof per shared argument.** Cite the landed rows the route names; never re-walk a
   landed contract inside a target, and never write a second host, loop, trace or layout
   lemma for something already public.
8. **Size.** No cap; file size alone is not a driver (user, 2026-10-11). Report each owned
   file's final line count and its public and private declaration counts.
9. **Continuation budget.** If your budget runs out, deliver a partial zip whose `REPORT.md`
   states which targets are proved, which `private` helpers remain `sorry` (each with a literal
   "Proof sketch"), and which proved targets are proved modulo them. A partial is expected and
   fine; an unreported gap is not.
10. **Hand-built table:** exactly one, the counting table above, with a docstring naming the gap ("no public input-driven counter").

## Duplication governance (binding)

Run the text-level screen **before and after** (`audits/TEMPLATE.md` failure mode 5; `policy.md`,
**Duplication**). The base, at this brief's issue tree, is `audits/logs/w1-fill-screen-base.txt`:
**1,331 declarations, 1,717 pairs, 574,720 characters**.

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/TuringMachine/Build/InputLength.lean \
  TCSlib/Complexity/TuringMachine/Build/RecordTable.lean \
  TCSlib/Complexity/TuringMachine/Build/CertShell.lean \
  TCSlib/Complexity/TuringMachine/Build/OracleSim.lean \
  TCSlib/Complexity/TuringMachine/CodeSimulator.lean \
  TCSlib/Complexity/TuringMachine/ChoiceWords.lean \
  TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean \
  TCSlib/Complexity/TuringMachine/Build/Seam.lean \
  TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean \
  TCSlib/Complexity/TuringMachine/Build/Catalog.lean \
  TCSlib/Complexity/TuringMachine/Build/InputCall.lean \
  TCSlib/Complexity/TuringMachine/Build/OracleCall.lean \
  TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean \
  TCSlib/Complexity/TuringMachine/Oracle.lean \
  TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean \
  TCSlib/Complexity/ClassNP/Nondeterminism.lean \
  TCSlib/Complexity/TuringMachine/CodeFormat.lean \
  TCSlib/Complexity/TuringMachine/Codes2Tape.lean \
  TCSlib/Complexity/TuringMachine/Build/Primitives.lean \
  TCSlib/Complexity/ClassP/DTIME.lean \
  TCSlib/Complexity/TuringMachine/Universal.lean \
  TCSlib/Complexity/TuringMachine/UniversalBlock.lean \
  TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean \
  TCSlib/Complexity/TuringMachine/UniversalStartup.lean
```

- **No new cross-file pair** with an owned-file declaration on one side, except a pair this
  brief pre-discloses (measure it and report it).
- **Known hazards:**
  - **pre-disclosed:** your counting table against Catalog's private `f2_counterTM` (note 44). Measure and report it; a pair with its *proofs* is not allowed;
  - the round induction against `CounterLoop`'s `counter_rounds` and Catalog's increment traces;
  - `FinTM.computesFunInTime_lengthBits_spaceUsed` (Catalog): cite, never re-derive it here (12.2c may re-derive it from your row).
- List every new in-file pair with a one-line justification. At 90% or more it is a copy:
  factor it.
- Parallel batches are invisible to your screen. A cross-file pair between your private helpers
  and another batch's, found at integration, is the maintainer's to factor.
- Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each
  pre-disclosed pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/w1-fill.txt` (**55 modules**: the upstream closure of
  your owned files and of every module downstream of them, at the issue tree):

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/w1-fill.txt )
  ```

  **Base sorry-warning set, 28** (`audits/logs/w1-fill-base-sorries.txt`, one entry per declaration).
  Yours: `Build/InputLength` 1 (`exists_inputLengthTM`). Record the base list by name first. If anything else has landed by your base
  (a parallel batch, or the maintainer's corollary PR), report the difference.
- **Final checks:**
  1. Your owned modules: zero errors, zero sorry warnings (or exactly your partial's).
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours (**27** for a complete delivery).
  3. Re-run the pre-ship probe `audits/evidence/wave1-statements/S128bStatementsProbe.lean.txt`: 0 errors.
- **Axiom prints** for every target: within `[propext, Classical.choice, Quot.sound]`, with
  `sorryAx` only through a named proved-modulo citation.
- **Lint:** `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`, 0 FAIL.

## Out-of-scope sorries you will see (leave every one untouched)

- `TuringMachine/Build/CfgRecord`: exists_recordStepTM
- `TuringMachine/NDCodes`: exists_effectiveNDMachineCode
- `TuringMachine/Build/RecordTable`: joinFields_length, fieldOffset_length, joinFields_cfgRecord_length, cfgRecord_field_ne_nil, cfgRecord_init, recordValid_iff_exists_cfg, joinFields_recordTemplate_length, binDigits_posWidth_succ, TableWF.field_ne_nil, tableOffset_eq, tableOffset_length, TableAt.recordAt_take, tableRewindTM_run_ofCfg, exists_fieldsCopyTM, exists_tableFindTM, exists_tableAppendTM, exists_recordTemplateTM, exists_recordInitTM, exists_recordValidTM, exists_recordNextTM
- `TuringMachine/Build/CertShell`: FinTM.exists_certificateShell
- `TuringMachine/Build/OracleSim`: FinOracleTM.exists_plain_simulation, FinOracleNDTM.exists_choiceTM
- `TuringMachine/CodeSimulator`: exists_polyCanonizer, exists_uniformSimulator

If a proof seems to *need* one of these, that is an escalation, not a license.

## REPORT.md checklist

- [ ] 1/1, or the partial frontier (rule 9); the base hash and the ancestor check.
- [ ] Every new declaration with its role; every flagged appendix, status update and import.
- [ ] Requested shared lemmas and escalations, or "none".
- [ ] Duplication: both screens, every new pair justified, "new copies: none" (or the
      pre-disclosed pairs, measured).
- [ ] File sizes; the final sweep tail; the re-run probe; every target's axiom print; the lint
      line. The diff touches only your owned files.
- [ ] Note 44: the measured pair with `f2_counterTM`, for the 12.2c ledger.

## Known pitfalls at this pin (hard-won)

- `Cfg.inputPos : Fin (|input| + 2)` starts at `1`; `0` and `|input| + 1` are the clamped blanks
  (`moveInputPos`); compare lifted positions by `.val`.
- A halted source has `M.step c = c` and `M.outputSymbol c = none` (`step_of_halt`,
  `outputSymbol_of_halt`).
- `seamCompTM_firstReturn_ofCfg` needs the callee's cut at `t = 0` as well;
  `exists_installCallTM` gives it only for `0 < t`.
- A structure update inside `runFrom` needs an ascription:
  `({c with state := some s, inputPos := 1} : Cfg k Bool S x)`.
- `decide` cannot evaluate `Nat.bits`/`Nat.size`, hence `posWidth`: use `Nat.size_eq_bits_len`,
  `Nat.lt_size_self`, `Nat.lt_size`, `Nat.size_one`.
- `omega` with products and powers as atoms (`ring` first to expose them); `nlinarith` is
  rarely needed. The linter needs a literal "Proof sketch" before every `sorry` (partial only).
- `simp` unfolds a machine's definition inside `counterLoopOrbit M …` arguments too, so terms
  stop matching. `generalize counterLoopOrbit M τ c r = o at …` first.
- `∑ r ∈ Finset.range d, τ (orbit r) + counterOverhead w (d + 1)` parses as
  `(∑ …) + counterOverhead …` (big operators bind at 67).
- `scanTM`'s accumulator is `A : Type` and the phase types must be finite: `ScanPhase A` is
  `Fintype` from `[Fintype A]`; `phaseHostTM`'s states `Σ i, Ph i` need `[Fintype I]` and
  `[∀ i, Fintype (Ph i)]`, and `DecidableEq` likewise. `FinTM` wants `State : Type`.
- `rewind_heads`/`rewind_scan_heads` are declared in `Build/Catalog.lean` but live in
  `Turing.FinTM`, like `timed_rewind` in `Simulation.lean`.
- The overlay transport needs a table that ignores its input (`hin`) and never writes a blank
  (`hnb`): it serves `incrementTM`/`decrementTM`, not rows that read the input.
- Since R8.0b, `counterLoopCfg`, `counterLoopOrbit` and `counterLoop_time_le` take the tape
  alphabet as a parameter. Typed arguments fix it at `Bool`; a positional `@` application gains
  one argument.
- `counterLoopCfg` ignores the body configuration's state (its state field is the host's), and
  `counterWord` freezes at zero while the machine wraps: stay at `r ≤ value + 1`.
- `embedEmitCfg`'s output is `pre ++ c.output`: start every lifted `Bool` configuration with
  output `[]` and `pre :=` the host's output, which may contain foreign symbols.
- `RecordAt`/`TableAt` constrain only the stated interval around the origin; a field's own
  delimiters come from `fieldsTape_field` and the span bound, never from cells beyond the
  layout.
