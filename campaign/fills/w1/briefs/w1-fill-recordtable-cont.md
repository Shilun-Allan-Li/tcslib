# Ch3–4 fill campaign — wave-1 fill, continuation: §12.8b record tables, rows 14–20 (`Build/RecordTable.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 820d23121a5847808d079f26bfe7efe0aee36ca3 HEAD`
  succeeds. That commit contains:
  - the closed wave-1 statement gate (PR #43) and every row its sketches cite, now proved, including R8.5c (`exists_inputLengthTM`), W2-V (`FinTM.exists_certificateShell`), the §12.8 record step (`exists_recordStepTM`) and R8.0b;
  - the first wave-1 and B5a fill deliveries and their reports (`audits/wave1-fill-agent-reports/`, `audits/b5a-fill-agent-reports/`), with the integration record `audits/fills-4-integration.md`;
  - this round's order list `briefs/orders/w1-fill-cont.txt`, base sorry set, screen base and pre-ship log.

  If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested `fill/w1-recordtable-cont`). Record the base
  hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-w1-recordtable-cont.zip`, containing
  `REPORT.md`, the full modified sources, a `git format-patch` series against your base, a git
  bundle, the final sweep log, the axiom log, and `SHA256SUMS`.

## Parallel batches this round (disjoint files; never edit another batch's file)

| Batch | Brief | Owns |
|---|---|---|
| §12.10 W2-S, continuation | `briefs/w2-fill-oraclesim-cont.md` | `TuringMachine/Build/OracleSim.lean` |
| §12.8b record tables, continuation | `briefs/w1-fill-recordtable-cont.md` | `TuringMachine/Build/RecordTable.lean` |
| B5a, continuation | `briefs/b5a-fill-cont.md` | `TuringMachine/CodeSimulator.lean` (and status text in `TuringMachine/Codes2Tape.lean`, `Diagonalization/EXPCOM.lean`) |

A parallel batch's work is invisible to your base and your screen.

## What this is

**A continuation** (`workflow.md` §4). The first record-table delivery proved 13 of the 20
targets: the twelve layout and table facts, and the end-to-start adapter. It also built the
field-list copier `rt_copyMachine`, with its zero- and one-field contracts. Fill the **seven
remaining rows**: field-list copy, table find and append, and the record template, initial
record, validity and enumeration rows. S1b and Savitch wait on them.

**R8.5c is now proved** (`exists_inputLengthTM`, landed with the first delivery), so **the
proved-modulo set is empty**: a complete delivery has no `sorryAx`.

**Read first:** the first delivery's report (`audits/wave1-fill-agent-reports/recordtable-1-REPORT.md`),
especially its "Continuation frontier", which is written for you; then the original brief
`briefs/w1-fill-recordtable.md` (its routes and gate guidance still bind), design §12.8b, and
`Build/RecordTable.lean`.

**Pre-ship check (maintainer, executed at this brief's ancestor):**
`audits/evidence/wave1-statements/S128bStatementsProbe.lean.txt`, re-run at the issue tree
(`audits/logs/w1-fill-cont-preship.log`): 0 errors, 0 warnings.

## Owned files and targets (modify these and nothing else)

Lines are at the issue commit.

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 14 | `TuringMachine/Build/RecordTable.lean:837` | `Turing.exists_fieldsCopyTM` | complete `rt_copyMachine` by induction on the fields | — |
| 15 | `…:910` | `Turing.exists_tableFindTM` | fuel loop under `counterLoopTMVia` | — |
| 16 | `…:965` | `Turing.exists_tableAppendTM` | `seekEndTM`, then 14 | 14 |
| 17 | `…:1017` | `Turing.exists_recordTemplateTM` | R8.5c (proved), digit rows lifted by R1 | — |
| 18 | `…:1068` | `Turing.exists_recordInitTM` | 17, then field writes | 17 |
| 19 | `…:1126` | `Turing.exists_recordValidTM` | field-by-field checks; lifted `counterLoopTM` for `v ≤ n + 1` | — |
| 20 | `…:1187` | `Turing.exists_recordNextTM` | carry odometer, 19, `counterLoopTMVia` | 14, 18, 19 |

- **Owned:** `TuringMachine/Build/RecordTable.lean`, for the seven rows' bodies and new `private`
  declarations.
- **Frozen in your file:** the 13 proved targets and the first delivery's nine privates
  (`rt_field_cover`, `rt_fields_slice`, `rt_copyState` and its two instances, `rt_copyEntry`,
  `rt_copyExit`, `rt_copyMachine`, `rt_copy_run_base`). Cite and reuse them; never change them.
  `rt_copyMachine` is the copier: do not build another.
- **Not yours:** every other file, including `Build/InputLength.lean` (now proved and frozen) and
  `Build/CfgRecord.lean`, and the facade.
- Fill in the table's order.

### Proof routes (binding; the original brief's, for rows 14–20)

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

### The frontier you inherit (the first delivery's; resume at row 14)

1. Prove the contract for `m + 2` fields, assuming the nonempty-tail contract for `m + 1`; the
   base cases are `rt_copy_run_base`.
2. Write the source fields as `u :: tail`, with `tail` nonempty. Use `joinFields_cons_cons`,
   `fieldsTape_field` and `rt_fields_slice [u] tail []` for the first-field and tail frames. The
   first copy leaves the separator and the future tail slot blank on the destination.
3. Apply, in order, `copyTM_run_ofCfg`, `skipTM_run_ofCfg` on tape 0, `skipTM_run_ofCfg` on
   tape 1, the induction hypothesis on the tail, and `skipBackTM_run_ofCfg` once on each tape.
   Compose the six runs and the five stationary dispatches with the public R2 theorems.
   Intercept every exit.
4. The composition's time is the tail time plus `6·|u| + 17`. Since the layout length is
   `|u| + 1 + |tail layout|`, raising the tail's linear constant by 20 covers the time and
   head-radius inequalities. Formalize the two destination write masks as the single final
   layout write, and discharge the cuts and the visited-set containment.
5. Package the state type, its two instances, the machine and its anchors to fill
   `exists_fieldsCopyTM`. Then find, append and the four record rows in order. For find, keep
   the escape before the final accepted field's skip, and use `counterLoopTMVia`. For the
   template, use R8.5c and the increment-plus-overflow-extension route (note 26).

The frozen `cfgRecord` definition elaborates its window indices through a list coercion from
naturals to integers. The first delivery normalized it with `Bind.bind`, `Pure.pure` and
`← List.map_eq_flatMap`; do not change the definition to avoid this.

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
- `exists_inputLengthTM` (R8.5c, proved); `exists_recordStepTM` (proved, but no route here needs
  it).
- **Do not cite** anything downstream (`SpaceComplexity`, `ClassPSPACE`).

## Ground rules (binding)

1. **File ownership.** Only `Build/RecordTable.lean`. Change only the seven rows' bodies, and add new `private` helpers
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
6. **Imports.** Unchanged (`Build/CfgRecord`, `Build/Seam`, `Build/InputLength`, and the first delivery's flagged `Mathlib.Data.Nat.Bitwise`). No TCSlib import may be added. A Mathlib import is allowed only if a needed lemma requires it; flag
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
**Duplication**). The base, at this brief's issue tree, is `audits/logs/w1-fill-cont-screen-base.txt`:
**1,416 declarations, 1,735 pairs, 580,484 characters**.

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
  - the first delivery's seven in-file pairs (55–73%, the copier's state-family dictionaries) are recorded; the copier's induction must cite `rt_copy_run_base`, never restate it;
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
- **Bootstrap once** from `briefs/orders/w1-fill-cont.txt` (**85 modules**: the upstream closure of
  your owned files and of every module downstream of them, at the issue tree):

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/w1-fill-cont.txt )
  ```

  **Base sorry-warning set, 17** (`audits/logs/w1-fill-cont-base-sorries.txt`, one entry per declaration).
  Yours: `Build/RecordTable` 7. Record the base list by name first. If anything else has landed by your base
  (a parallel batch, or the maintainer's corollary PR), report the difference.
- **Final checks:**
  1. Your owned modules: zero errors, zero sorry warnings (or exactly your partial's).
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours (**10** for a complete delivery).
  3. Re-run the pre-ship probe `audits/evidence/wave1-statements/S128bStatementsProbe.lean.txt`: 0 errors.
- **Axiom prints** for every target: within `[propext, Classical.choice, Quot.sound]`, with
  `sorryAx` only through a named proved-modulo citation.
- **Lint:** `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`, 0 FAIL.

## Out-of-scope sorries you will see (leave every one untouched)

- `TuringMachine/Build/OracleSim`: FinOracleTM.exists_plain_simulation
- `TuringMachine/CodeSimulator`: exists_polyCanonizer, exists_uniformSimulator
- `Diagonalization/EXPCOM`: NPOracle_EXPCOM_subset_EXP
- `Diagonalization/NTimeHierarchy`: exists_timed_universal_NDTM, exists_ndAcceptsWithin_decider, exists_codeNDTM_accepts_linear, ntime_hierarchy, ntime_hierarchy_of_pos, NTIME_linear_ssubset_square

If a proof seems to *need* one of these, that is an escalation, not a license.

## REPORT.md checklist

- [ ] 7/7, or the partial frontier (rule 9); the base hash and the ancestor check.
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
