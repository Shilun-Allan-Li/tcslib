# Ch3–4 fill campaign — wave-1 fill: §12.8b record tables and the deferred record rows (`Build/RecordTable.lean`, 20 targets)

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
- Create your working branch off the campaign branch (suggested `fill/w1-recordtable`). Record the base
  hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-w1-recordtable.zip`, containing
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

Fill the **§12.8b table layer and the deferred record rows** (`machine-library-design.md`
§12.8b; statements audited true at the wave-1 statement gate, round 2): the layout facts, the
end-to-start adapter, field-list copy, table find and append, and the record template, initial
record, validity and enumeration rows. Their consumers are S1b's breadth-first simulation of
`NSPACE` in exponential time and Savitch's midpoint recursion; both wait on you.

**Read first:** `Build/RecordTable.lean` in full (every docstring sketch is binding); design
§12.8b ("Layout", "Rows", "Decisions", "Degenerate cases", "Fill dependencies"); the wave-1
findings rounds 1–2 and `audits/wave1-statements-resolutions.md`; the §12.8 statement gate's
resolutions (`audits/s12-8-statements-resolutions.md`) for the row conventions; `policy.md`;
`workflow.md` §4.

**Proved modulo: `Turing.exists_inputLengthTM` only** (R8.5c, filled in parallel by
`briefs/w1-fill-inputlength.md`). The template row cites it; every other cited row is proved.
Design §12.8b lists R8.5c among the template's, init's and validity's dependencies, and next
reaches it through init. So a complete delivery prints `sorryAx` only for those record rows, and
only through R8.5c, until that batch lands; the layout facts, the adapter and the table rows are
admission-free.

**Pre-ship check (maintainer, executed at this brief's ancestor):**
`audits/evidence/wave1-statements/S128bStatementsProbe.lean.txt`, re-run at the issue tree
(`audits/logs/w3-preship.log`): 0 errors, 0 warnings, output identical to round 2's. It runs the
design's executed checks against the landed definitions, including the sanity cases for the last
matching table entry and the empty-field append.

## Owned files and targets (modify these and nothing else)

Lines are at the issue commit.

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `TuringMachine/Build/RecordTable.lean:115` | `Turing.joinFields_length` | induction on the field list | — |
| 2 | `…:127` | `Turing.fieldOffset_length` | **note 11:** `(length_joinFields_add_one fs hfs).symm` | — |
| 3 | `…:145` | `Turing.joinFields_cfgRecord_length` | from 1 and `cfgRecord_length` | 1 |
| 4 | `…:157` | `Turing.cfgRecord_field_ne_nil` | case on the field index | — |
| 5 | `…:170` | `Turing.cfgRecord_init` | unfold at `Cfg.init` | — |
| 6 | `…:199` | `Turing.recordValid_iff_exists_cfg` | the bridge Savitch needs; both directions | — |
| 7 | `…:221` | `Turing.joinFields_recordTemplate_length` | from 1 | 1 |
| 8 | `…:233` | `Turing.binDigits_posWidth_succ` | digit arithmetic | — |
| 9 | `…:271` | `Turing.TableWF.field_ne_nil` | from `TableWF` | — |
| 10 | `…:281` | `Turing.tableOffset_eq` | the closed form | 1 |
| 11 | `…:293` | `Turing.tableOffset_length` | from 10 | 10 |
| 12 | `…:307` | `Turing.TableAt.recordAt_take` | restriction of the layout | 10 |
| 13 | `…:342` | `Turing.tableRewindTM_run_ofCfg` | `skipBackTM` then `seekStartTM`, one seam | — |
| 14 | `…:383` | `Turing.exists_fieldsCopyTM` | `copyTM` + `skipTM` per field, R2 seams | — |
| 15 | `…:456` | `Turing.exists_tableFindTM` | fuel loop under `counterLoopTMVia` | 9–12 |
| 16 | `…:507` | `Turing.exists_tableAppendTM` | `seekEndTM`, then 14 | 10–12, 14 |
| 17 | `…:559` | `Turing.exists_recordTemplateTM` | R8.5c, digit rows lifted by R1 | R8.5c (modulo) |
| 18 | `…:610` | `Turing.exists_recordInitTM` | 17, then field writes | 5, 17 |
| 19 | `…:668` | `Turing.exists_recordValidTM` | field-by-field checks; lifted `counterLoopTM` for `v ≤ n + 1` | 6 |
| 20 | `…:729` | `Turing.exists_recordNextTM` | carry odometer, 19, `counterLoopTMVia` | 14, 18, 19 |

- **Owned:** `TuringMachine/Build/RecordTable.lean`, for the 20 targets' bodies and new `private` declarations.
- **Not yours:** `Build/InputLength.lean` (parallel batch), `Build/CfgRecord.lean` (C continuation 3), every Catalog, Seam, CounterLoop, Scan, InputCall file, and the facade.
- Fill in the table's order: the layout facts first, then the adapter and the table rows, then the record rows.

### Proof routes (binding; the docstrings' sketches, read each in full)

- **Layout facts (1–12).** Pure list arithmetic over `joinFields`, `fieldOffset`, `fieldsTape`,
  `cfgRecord`, `tableFields`, `tableOffset`. Cite Catalog Part 3's layout lemmas
  (`joinFields_cons_cons`, `fieldsTape_cons_shift`, `fieldOffset_succ`, `fieldOffset_cons_succ`,
  `length_joinFields_add_one`, `fieldOffset_add_length_le`, `fieldsTape_field`); write no second
  layout induction (note 11 for target 2). `recordValid_iff_exists_cfg` (6) is the bridge
  Savitch needs: valid records are exactly the records of windowed configurations on the
  actual input.
- **The adapter (13)** is the real machine `tableRewindTM`: `seamCompTM_run_ofCfg` with
  `skipBackTM_run_ofCfg`, the dispatch step, then `seekStartTM_run_ofCfg`; the first-return cut
  is `seamCompTM_firstReturn_ofCfg`. Its exact contract has time `D + 7`.
- **Field-list copy (14):** for each of the `m` fields, `copyTM_run_ofCfg` into the blank slot,
  then `skipTM_run_ofCfg` advances both heads; R2 seams; every phase linear.
- **Find (15)** takes fuel: a digit word whose value exceeds the number of entries, restored
  (design decision 2), under the one rich loop host `counterLoopTMVia` with `e : Bool ↪ Γ`. Per
  **minor 3**, acceptance escapes **before** skipping an accepted final field; the
  explicit-verdict-bit alternative is named in the sketch.
- **Append (16):** `seekEndTM_run_ofCfg` over the table's field list, the separator, then 14
  copies `e` from tape `1`, `skipTM` crosses the copied fields; the new layout extends the old.
- **Template, init, validity, next (17–20)** are existential modules in the §12.8 house style
  (fixed local layouts hosted by R1; every `Bool` row lifted along `RecSym.digitEmb` on
  dedicated digit tapes). The template cites R8.5c and, per **note 26**, its extra increment is
  `incrementTM` plus a one-cell overflow extension. Validity's time includes `n` (decision 4:
  the `Bool` `counterLoopTM`, lifted onto two digit tapes, checks `v ≤ n + 1`). Next uses the
  carry odometer (decision 1: the order is existential), tests by 19, and repeats under
  `counterLoopTMVia`; its exponential bound is honest (decision 8).
- **Input convention** (decision 7): rows that read the native input enter at position `1` and
  restore it.
- **Degenerate cases** (design list): find needs `0 < m`; validity needs `|fs| = k + 3`; the empty
  table; `T` empty (`first` answers `no` through `match`); `k = 0`, `s = 0`, `n = 0`.

## Gate guidance (binding)

- **Note 11:** fill `fieldOffset_length` by `(length_joinFields_add_one fs hfs).symm`.
- **Note 25 and round-2 note 15:** append with empty new fields need not preserve `TableWF`;
  consumers that seek again must append nonempty fields. State this in append's appendix.
- **Note 26:** the template's extra increment is `incrementTM` plus a one-cell overflow
  extension (its prerequisites, #38, have landed).
- **Note 46:** file size is not a driver; report `RecordTable`'s size.
- **Note 50:** permanent sanity case **at fill**: the empty-`T` enumeration for `recordNext`, as
  an executed example in your evidence (`decide` or `rfl`), with the two §12.8b probe cases kept.
- **Minor 3:** find escapes before skipping an accepted final field.
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

- **Catalog Part 3:** `copyTM`, `clearTM`, `skipTM`, `skipBackTM`, `seekStartTM`, `seekEndTM`,
  `compareTM`, `scanTM` with `scanResult_fold`/`_map`/`_shiftRight`/`_shiftLeft`, and their
  `_run_ofCfg` contracts; the layout lemmas above; the one-step lemmas for hand tables.
- **Seam:** `seamCompTM`, `seamCompTM_run_ofCfg`, `seamCompTM_firstReturn_ofCfg`,
  `seamReleaseTM`, `seamReleaseTM_firstReturn`, `phaseHostTM`, `phaseHostTM_run`.
- **CounterLoop:** `counterLoopTM`, `counterLoopTMVia`, `lastEmb`, their `_run_done`/`_run_escape`
  contracts, `decrementTM_run_succ_ofCfg`/`_underflow_ofCfg`, `counterWord_value`.
- **Scan:** `writeConstTM_run_ofCfg`, `inputCopyTM_run_ofCfg`, `inputFoldTM_run_ofCfg`.
- **CfgRecord (landed):** `RecSym`, `RecSym.digitEmb`, `binDigits`, `posWidth`, `cfgRecord`,
  `cfgRecord_length`, `cfgRecord_inj`, `RecordValid`, `recordValid_iff`, `RecordAt`,
  `Cfg.InWindow`, `exists_recordEqTM`, `exists_recordTestTM`.
- **R1/SymbolLift:** `embedEmitTM`, `embedEmitTM_runFrom`, `embedEmitCfg_selected_tape`/`_pos`,
  `MultiTapeTM.liftSymbols_runFrom`, the overlay transport, `FinTM.bufferTape_map(_decode)`.
- **Do not cite** `exists_recordStepTM` (C continuation 3; no route here needs it), or anything
  downstream (`SpaceComplexity`, `ClassPSPACE`).

## Ground rules (binding)

1. **File ownership.** Only `Build/RecordTable.lean`. Change only the 20 targets' bodies, and add new `private` helpers
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
6. **Imports.** Unchanged (`Build/CfgRecord`, `Build/Seam`, `Build/InputLength`). No TCSlib import may be added. A Mathlib import is allowed only if a needed lemma requires it; flag
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
  - any private field-layout, buffer-map, rewind-heads or `counterLoopCfg`-layout lemma: all are public, cite them;
  - the record rows against `CfgRecord`'s record-step helpers (private there: never copy them) and `InputCall`'s private seek helpers;
  - a second loop host or forward scanner (decision 2 forbids it): find runs under `counterLoopTMVia`;
  - the template's binary counter against R8.5c: cite `exists_inputLengthTM`, never rebuild it.
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
  Yours: `Build/RecordTable` 20. Record the base list by name first. If anything else has landed by your base
  (a parallel batch, or the maintainer's corollary PR), report the difference.
- **Final checks:**
  1. Your owned modules: zero errors, zero sorry warnings (or exactly your partial's).
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours (**8** for a complete delivery).
  3. Re-run the pre-ship probe `audits/evidence/wave1-statements/S128bStatementsProbe.lean.txt`: 0 errors.
- **Axiom prints** for every target: within `[propext, Classical.choice, Quot.sound]`, with
  `sorryAx` only through a named proved-modulo citation.
- **Lint:** `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`, 0 FAIL.

## Out-of-scope sorries you will see (leave every one untouched)

- `TuringMachine/Build/CfgRecord`: exists_recordStepTM
- `TuringMachine/NDCodes`: exists_effectiveNDMachineCode
- `TuringMachine/Build/InputLength`: exists_inputLengthTM
- `TuringMachine/Build/CertShell`: FinTM.exists_certificateShell
- `TuringMachine/Build/OracleSim`: FinOracleTM.exists_plain_simulation, FinOracleNDTM.exists_choiceTM
- `TuringMachine/CodeSimulator`: exists_polyCanonizer, exists_uniformSimulator

If a proof seems to *need* one of these, that is an escalation, not a license.

## REPORT.md checklist

- [ ] 20/20, or the partial frontier (rule 9); the base hash and the ancestor check.
- [ ] Every new declaration with its role; every flagged appendix, status update and import.
- [ ] Requested shared lemmas and escalations, or "none".
- [ ] Duplication: both screens, every new pair justified, "new copies: none" (or the
      pre-disclosed pairs, measured).
- [ ] File sizes; the final sweep tail; the re-run probe; every target's axiom print; the lint
      line. The diff touches only your owned files.
- [ ] Note 50: the empty-`T` enumeration example, executed.

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
