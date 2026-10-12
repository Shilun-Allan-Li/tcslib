# Ch3–4 fill campaign — wave-1 fill, continuation 2: §12.8b record tables, rows 15–20 (`Build/RecordTable.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 13957bf73eb37763259be1fd01a5cca9bd03c21f HEAD`
  succeeds. That commit contains:
  - the previous continuations of this round's three batches and their reports (`audits/wave1-fill-agent-reports/{oraclesim,recordtable}-2-REPORT.md`, `audits/b5a-fill-agent-reports/cont-1-REPORT.md`), with the integration record `audits/fills-5-integration.md`;
  - the `exists_tableFindTM` universe fix (`Γ : Type`, user option (b), flagged in its docstring) and the 12.2c T2a export `Turing.embedEmitTM_tr`;
  - the B4 pre-issue promotion: twelve CNF-grammar publics in `Formulas/CNFEncoding.lean`, and `MultiTapeTM.spaceUsedByTape_le_card_Icc` moved from `Build/Zone.lean` to `Build/Catalog.lean` (same name and statement);
  - this round's order lists (`briefs/orders/{w1,b5a}-fill-cont2.txt`), base sorry sets, screen bases and pre-ship logs.

  If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested `fill/w1-recordtable-cont2`). Record the base
  hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-w1-recordtable-cont2.zip`, containing
  `REPORT.md`, the full modified sources, a `git format-patch` series against your base, a git
  bundle, the final sweep log, the axiom log, and `SHA256SUMS`.

## Parallel batches this round (disjoint files or declarations; never edit another batch's)

| Batch | Brief | Owns |
|---|---|---|
| B4, TQBF membership | `briefs/ch34-b4-mem.md` | `ClassPSPACE/TQBF.lean`: `TQBF_mem_PSPACE` only |
| §12.10 W2-S, continuation 2 | `briefs/w2-fill-oraclesim-cont2.md` | `TuringMachine/Build/OracleSim.lean` |
| §12.8b record tables, continuation 2 | `briefs/w1-fill-recordtable-cont2.md` | `TuringMachine/Build/RecordTable.lean` |
| B5a, the canonizer | `briefs/b5a-fill-canon.md` | `TuringMachine/CodeSimulator.lean`, by declaration: `MachineFormat.exists_polyCanonizer` and new privates in its gap |
| B5a, the uniform simulator H1 | `briefs/b5a-fill-h1.md` | `TuringMachine/CodeSimulator.lean`, by declaration: `MachineFormat.exists_uniformSimulator` and new privates in its gap |

Also in flight (wave 5): S1b (`SpaceComplexity/ConfigGraph.lean`), which cites five record-table
rows; B3a (`SpaceComplexity/Constructible.lean`); and B5b (`Diagonalization/EXPCOM.lean`, by
declaration), which cites W2-S and B5a's two rows. A parallel batch's work is invisible to your
base and your screen.

## What this is

**A second continuation** (`workflow.md` §4). The first continuation proved **row 14**,
`exists_fieldsCopyTM`, for all field counts and alphabet universes, and append's complete
seek-and-copy prefix (`rt_append_copy`). The file has **14 of 20** targets proved. Fill the
**six remaining rows**: table find and append, and the record template, initial record,
validity and enumeration rows. **S1b (in flight) cites five of them modulo**, and Savitch waits
on all of them. The proved-modulo set is empty: a complete delivery has no `sorryAx`.

**The escalation is resolved.** The first continuation stopped on row 15: `exists_tableFindTM`
was stated for `Γ : Type*`, but its mandated loop `counterLoopTMVia` (and `phaseHostTM`) take
their alphabet in `Type`. The user chose to restate the row at **`Γ : Type`** (a maintainer
statement fix with its own gate, flagged in the row's docstring; every consumer's alphabet,
`RecSym Q T`, is in `Type`). **Resume row 15 with the mandated loop.** Rows 17–20 are already
stated over `Q T : Type`. Rows 14 and 16 stay at `Type*`; append's route needs only
universe-polymorphic rows (`seekEndTM`, the copier, the skips, `seamCompTM`). If a phase there
seems to need `phaseHostTM`, use R2 seams instead or escalate.

**Read first:** the first continuation's report (`audits/wave1-fill-agent-reports/recordtable-2-REPORT.md`),
especially its "Continuation frontier", which is written for you; the earlier briefs
`briefs/w1-fill-recordtable-cont.md` and `briefs/w1-fill-recordtable.md` (routes and gate guidance
still bind); design §12.8b; `Build/RecordTable.lean`.

**Pre-ship check (maintainer, executed at this brief's ancestor):**
`audits/evidence/wave1-statements/S128bStatementsProbe.lean.txt`, re-run at the issue tree with the
restated row (`audits/logs/w1-fill-cont2-preship.log`): 0 errors, 0 warnings.

## Owned files and targets (modify these and nothing else)

Lines are at the issue commit.

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 15 | `TuringMachine/Build/RecordTable.lean:1277` | `Turing.exists_tableFindTM` | fuel loop under `counterLoopTMVia` (now at `Γ : Type`) | — |
| 16 | `…:1551` | `Turing.exists_tableAppendTM` | `rt_append_copy`, then the suffix and the old-table rewind | 14 |
| 17 | `…:1603` | `Turing.exists_recordTemplateTM` | R8.5c (proved), digit rows lifted by R1 | — |
| 18 | `…:1654` | `Turing.exists_recordInitTM` | 17, then field writes | 17 |
| 19 | `…:1712` | `Turing.exists_recordValidTM` | field-by-field checks; lifted `counterLoopTM` for `v ≤ n + 1` | — |
| 20 | `…:1773` | `Turing.exists_recordNextTM` | carry odometer, 19, `counterLoopTMVia` | 14, 18, 19 |

- **Owned:** `TuringMachine/Build/RecordTable.lean`, for the six rows' bodies and new `private`
  declarations.
- **Frozen in your file:** the 14 proved targets, including the restated `exists_tableFindTM`'s
  **statement**; the nine first-delivery privates; and the first continuation's four
  (`rt_copy_seam`, `rt_copy_run`, `rt_fieldsCopy_reverse`, `rt_append_copy`). Cite and reuse them;
  never change them. `rt_copyMachine` is the copier: do not build another.
- **Not yours:** every other file, including `Build/CounterLoop.lean` and `Build/Seam.lean` (the
  universe-zero hosts, unchanged; their generalization is the optional backlog item UNIV-1),
  `Build/InputLength.lean` and `Build/CfgRecord.lean`, and the facade.
- Fill in the table's order.

### Proof routes (binding; the original brief's, for rows 15–20)

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

### The frontier you inherit (the first continuation's; resume at row 15)

1. **Row 15:** with the statement at `Γ : Type`, apply `counterLoopTMVia` directly. Keep the
   accepted-final-field escape **before** its skip (minor 3), and the fuel on its own digit tape,
   restored (design decision 2).
2. **Row 16:** consume `rt_append_copy`. Its destination head is exactly at the old second
   trailing blank, with the source layout copied there. The source tape and head, the native
   input position and the output are restored, and every other cell is unchanged.
3. For an **empty** fixed suffix, attach the public old-table rewind directly: its frame stops
   strictly before the current head, so the newly copied cell may be nonblank. For a
   **nonempty** suffix, cross the known number of copied fields with catalog skips, write the
   suffix with the public constant writers and skips, return over the new fields, and invoke the
   same rewind. Intercept every exit.
4. Prove that the final mask equals the extended table layout, using the existing layout
   restrictions. Do not assume the new fields are nonempty: append's statement permits empty
   fields, and `TableWF` need not be preserved.
5. Then rows 17–20 in order, along the binding routes: the increment-plus-overflow-extension
   (note 26), digit-tape isolation, finite verdict witnesses and the empty-tag obligations.

The first continuation corrected an inherited constant (the copier's additive time constant is
`6·|u| + 15`, not `17`); no frozen statement or machine changed.

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

1. **File ownership.** Only `Build/RecordTable.lean`. Change only the six rows' bodies, and add new `private` helpers
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
**Duplication**). The base, at this brief's issue tree, is `audits/logs/w1-fill-cont2-screen-base.txt`:
**1,477 declarations, 1,747 pairs, 582,620 characters**.

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
  - the first continuation's four privates: cite them; `rt_copy_seam` and `rt_fieldsCopy_reverse` are recorded promotion candidates;
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
- **Bootstrap once** from `briefs/orders/w1-fill-cont2.txt` (**88 modules**: the upstream closure of
  your owned files and of every module downstream of them, at the issue tree):

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/w1-fill-cont2.txt )
  ```

  **Base sorry-warning set, 18** (`audits/logs/w1-fill-cont2-base-sorries.txt`, one entry per declaration).
  Yours: `Build/RecordTable` 6. Record the base list by name first. If anything else has landed by your base
  (a parallel batch, or the maintainer's corollary PR), report the difference.
- **Final checks:**
  1. Your owned modules: zero errors, zero sorry warnings (or exactly your partial's).
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours (**12** for a complete delivery).
  3. Re-run the pre-ship probe `audits/evidence/wave1-statements/S128bStatementsProbe.lean.txt`: 0 errors.
- **Axiom prints** for every target: within `[propext, Classical.choice, Quot.sound]`, with
  `sorryAx` only through a named proved-modulo citation.
- **Lint:** `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`, 0 FAIL.

## Out-of-scope sorries you will see (leave every one untouched)

- `TuringMachine/Build/OracleSim`: FinOracleTM.exists_plain_simulation
- `TuringMachine/CodeSimulator`: exists_polyCanonizer, exists_uniformSimulator
- `Diagonalization/EXPCOM`: NPOracle_EXPCOM_subset_EXP
- `Diagonalization/NTimeHierarchy`: exists_timed_universal_NDTM, exists_ndAcceptsWithin_decider, exists_codeNDTM_accepts_linear, ntime_hierarchy, ntime_hierarchy_of_pos, NTIME_linear_ssubset_square
- `TuringMachine/Build/Zone`: exists_zoneShiftInTM, exists_zoneShiftOutTM

If a proof seems to *need* one of these beyond a named citation, that is an escalation, not a license.

## REPORT.md checklist

- [ ] 6/6, or the partial frontier (rule 9); the base hash and the ancestor check.
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
