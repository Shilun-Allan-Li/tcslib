# Ch3–4 fill campaign — wave-1 fill, continuation 3: §12.8b record tables, rows 17–18 (`Build/RecordTable.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor c0eefa8be8c277777dfecd8d2510d8e57218ce4c HEAD`
  succeeds. That commit contains:
  - the fills-6 integration (`audits/fills-6-integration.md`), with the second continuation's report
    `audits/wave1-fill-agent-reports/recordtable-3-REPORT.md`;
  - this round's order lists (`briefs/orders/{w1,b5a}-fill-cont3.txt`), base sorry sets, screen
    bases, screen populations and pre-ship logs.

  If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested `fill/w1-recordtable-cont3`). Record the base
  hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-w1-recordtable-cont3.zip`, containing
  `REPORT.md`, the full modified sources, a `git format-patch` series against your base, a git
  bundle, the final sweep log, the axiom log, and `SHA256SUMS`.

## Parallel batches this round (disjoint files or declarations; never edit another batch's)

| Batch | Brief | Owns |
|---|---|---|
| §12.8b record tables, continuation 3 | `briefs/w1-fill-recordtable-cont3.md` | `TuringMachine/Build/RecordTable.lean`: rows 17–18 only |
| B5a, the canonizer, continuation | `briefs/b5a-fill-canon-cont.md` | `TuringMachine/CodeSimulator.lean`, by declaration: `MachineFormat.exists_polyCanonizer` and new privates in its gap |
| B5a, H1, continuation | `briefs/b5a-fill-h1-cont.md` | `TuringMachine/CodeSimulator.lean`, by declaration: `MachineFormat.exists_uniformSimulator` and new privates in its gap |

A parallel batch's work is invisible to your base and your screen.

## What this is

**A third continuation, narrowed** (user, 2026-10-12: "Narrow to rows 17–18"). The file has
**14 of 20** targets proved. The second continuation proved the table-find round and its clocked
interface (20 privates) but no new row. Since then, S1b stopped as a partial, and Savitch moved to
the programming layer (design §16). Rows 15, 16, 19 and 20 (find, append, validity, next) have
lost their consumers. They are **paused**, as retirement candidates (backlog MIG-23): **do not
work on them, and leave their bodies untouched.**

**This batch is rows 17 and 18 only:** the record template and the initial record. Their next
consumer is the space hierarchy's window route (B6; design §14, host H3), which writes an initial
record inside a space window. The proved-modulo set is empty: a complete delivery has no `sorryAx`
in either row.

**Read first:** the two rows' docstrings, whose proof sketches are binding; the second
continuation's report (`audits/wave1-fill-agent-reports/recordtable-3-REPORT.md`); the earlier
briefs `briefs/w1-fill-recordtable-cont2.md` and `briefs/w1-fill-recordtable.md`, whose gate guidance
still binds for these rows; design §12.8b; `Build/RecordTable.lean`.

**Pre-ship check (maintainer, executed at this brief's ancestor):**
`audits/evidence/wave1-statements/S128bStatementsProbe.lean.txt`, re-run at the issue tree
(`audits/logs/w1-fill-cont3-preship.log`): 0 errors, 0 warnings.

## Owned files and targets (modify these and nothing else)

Lines are at the issue commit.

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 17 | `TuringMachine/Build/RecordTable.lean:2250` | `Turing.exists_recordTemplateTM` | the docstring's sketch: R8.5c (`exists_inputLengthTM`), one more increment with a one-cell width extension, `expandTM`, `writeAdvTM`, a `scanTM` map; every `Bool` row lifted by R1 on dedicated digit tapes | — |
| 18 | `…:2301` | `Turing.exists_recordInitTM` | the docstring's sketch: row 17 onto a scratch tape, then the record field by field (`cfgRecord_init`) | 17 |

- **Owned:** `TuringMachine/Build/RecordTable.lean`, for the two rows' bodies, their docstrings'
  flagged appendices, and new `private` declarations.
- **Frozen in your file:** the 14 proved targets; the four paused rows (15, 16, 19, 20), whose
  bodies and docstrings stay byte-identical; and all **33 inherited privates** (the first
  delivery's nine, the first continuation's four, the second continuation's 20, among them
  `rt_copyMachine`, `rt_append_copy` and the find round `rt_findRound`, `rt_find_round_entry`,
  `rt_findClock`). Cite and reuse them; never change them.
- **Not yours:** every other file, including `Build/CfgRecord.lean`, `Build/InputLength.lean`,
  `Build/CounterLoop.lean`, `Build/Seam.lean` and the facade.
- Fill row 17 first; row 18 cites it.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **The outer host is the public phase host or a chain of R2 seams.** Compose each row's phases by
  `Turing.seamCompTM` (`seamCompTM_run_ofCfg`, `seamCompTM_firstReturn_ofCfg`) or by
  `Turing.phaseHostTM` (`phaseHostTM_run`). Do not write a hand controller for the pipeline.
- **Every `Bool` row runs lifted** along `RecSym.digitEmb` on dedicated digit tapes, through R1
  (`embedEmitTM_runFrom`, `MultiTapeTM.liftSymbols_runFrom`, or the overlay transport
  `MultiTapeTM.liftSymbols_runFrom_over` for input-oblivious rows).
- **Head displacement:** the statements' envelope clause is proved from the public one-step bounds
  `workTapePos_step_le` (`Deterministic.lean`) and `workTapePos_apply_le` (`Configuration.lean`),
  and from each cited row's own envelope. Catalog's `f2_head_steps` is private and is to be
  retired (MIG-1): do not copy it.
- If the template's pipeline seems to need a component that no public row provides, write it
  privately as a generic component with its own contract, list it as a promotion candidate, and
  continue.

### Proof routes (binding: the docstrings' sketches)

- **Template (17).** The bound field: `exists_inputLengthTM` gives `Nat.bits |x|` on a scratch
  tape; one more `incrementTM` with a one-cell overflow extension (**note 26**:
  `incrementTM_run_succ_ofCfg`, `incrementTM_run_overflow_ofCfg`) gives `Nat.bits (|x| + 1)`,
  which is the bound field by `binDigits_posWidth_succ`; copy it to tape `0` (`copyTM_run_ofCfg`)
  and clear the scratch (`clearTM_run_ofCfg`). The window field: copy `ws` to a scratch counter
  before each expansion (an expansion leaves its counter all `true`); `expandTM_run_ofCfg` with
  pattern `[false]` writes `s` digits, `writeAdvTM_run_ofCfg` one `true` digit, and `expandTM`
  again `s` digits; a `scanTM` map (`scanResult_map`) turns `digit b` into `cell none b`. Clear the
  counters and return the heads by `skipBackTM_run_ofCfg`. The expansions cost `O(s + |ws|)` by
  `counterOverhead_le`, and `2s + 1` is at most the template length.
- **Initial record (18).** Run row 17 onto a scratch tape. Write the record field by field by R2
  seams, following `cfgRecord_init`: `writeConstTM` writes `[st (some q₀)]`; the position field is
  the template's bound field copied, mapped to `digit false` by `scanTM`, with `digit true`
  written on its first cell (the digits of `1`); the `k` tape fields are copies of the template's
  window field; `writeConstTM` writes `[tag τ₀]`; `skipTM_run_ofCfg` crosses each written field
  (`fieldsTape_field` gives the delimiters). Clear the template field by field and return the
  heads by `skipBackTM_run_ofCfg`.
- **Input convention** (decision 7): the rows read the native input at position `1` and restore
  it.
- **Degenerate cases:** `x = []`, `s = 0` (`ws` may be `[]` or all `false`), and `k = 0` (row 18
  has no tape field, which is why the radius enters its space bound).

## Gate guidance (binding)

- **Note 26:** the template's extra increment is `incrementTM` plus a one-cell overflow
  extension.
- **Intercept every verdict** (§12.8 statement gate, round-2 note 7). The contracts bound
  nothing after a module's own verdict or exit. Redirect at each sub-module's exit time; never
  run a sub-module past its exit.
- **R1 isolation of dedicated digit tapes** (round-1 note 32, round-2 notes 31–32). Never apply
  `liftSymbols_runFrom` or `liftSymbols_spaceUsed` to a configuration with a foreign symbol on a
  selected tape; the overlay transport is the alternative for input-oblivious rows.
- **No termination hypothesis** (round-1 note 35): each contract supplies its finite `t`.
- **The work-space clause** bounds every work head through the exit, independently of `|x|`
  (round-1 major 1); the exact finish restores every head, the input position, the scratch and
  the output.
- **Note 46:** file size is not a driver; report `RecordTable`'s size.
- **Sanity cases at fill:** execute the template and the initial record on `x = []`, `s = 0`
  and on one small nonzero case (for example `|x| = 3`, `s = 2`, `k = 1`), as examples in your
  evidence (`decide`, `rfl` or a bounded run).

## Cited infrastructure (public and proved at the issue commit)

- **RecordTable (yours, proved):** `recordTemplate`, `recordLength`, `cfgRecord_init`,
  `binDigits_posWidth_succ`, the field-layout lemmas; `exists_fieldsCopyTM` (row 14), if a field
  copy is cleaner through it.
- **Catalog:** `copyTM`, `clearTM`, `skipTM`, `skipBackTM`, `incrementTM`, `scanTM`, with their
  `_run_ofCfg` contracts and `scanResult_map`; `fieldsTape_field`; the one-step lemmas
  `tapeAction`, `step_of_tapeAction_move`, `step_of_tapeAction_write`.
- **Scan:** `writeConstTM_run_ofCfg`, `writeAdvTM_run_ofCfg`.
- **CounterLoop:** `expandTM`, `expandTM_run_ofCfg`, `counterOverhead_le`.
- **InputLength:** `exists_inputLengthTM` (R8.5c).
- **Seam:** `seamCompTM`, `seamCompTM_run_ofCfg`, `seamCompTM_firstReturn_ofCfg`, `seamReleaseTM`,
  `seamReleaseTM_firstReturn`, `phaseHostTM`, `phaseHostTM_run`.
- **R1 and SymbolLift:** `embedEmitTM`, `embedEmitTM_runFrom`, `MultiTapeTM.liftSymbols_runFrom`,
  `MultiTapeTM.liftSymbols_runFrom_over`, `FinTM.bufferTape_map(_decode)`.
- **CfgRecord:** `RecSym`, `RecSym.digitEmb`, `binDigits`, `posWidth`, `cfgRecord`,
  `cfgRecord_length`.
- **Head bounds:** `workTapePos_step_le`, `workTapePos_apply_le`.
- **Do not cite** anything downstream (`SpaceComplexity`, `ClassPSPACE`).

## Ground rules (binding)

1. **File ownership.** Only `Build/RecordTable.lean`. Change only rows 17 and 18's bodies, append a
   flagged **Fill appendix** to their docstrings where your proof refines the sketch, and add new
   `private` helpers. List every new declaration with its role. A lemma that genuinely belongs in
   a shared file is written privately, flagged in `REPORT.md` as a promotion candidate, and
   promoted by the maintainer at integration (`workflow.md` §4, rule 1).
2. **Statement freeze** over every target and every landed declaration: no renames,
   re-signatures, restatements or attribution edits. Docstrings stay; a flagged
   **"Fill appendix"** is expected wherever your proof refines or replaces a sketch's route.
3. **Status text.** Only your file's status text may change: the module's "Status" paragraph,
   its "Main results" tag, and your two targets' tags, each to "proved"; flag each. No new public
   declaration.
4. **Escalation** on anything unprovable as stated, including a cited row that does not
   compose as the route says: stop on that item, record the obstruction, and continue with the
   rest.
5. **No touching other sorries.** The four paused rows stay exactly as they are. Cite proved
   material; never re-prove it.
6. **Imports.** Unchanged. No TCSlib import may be added. A Mathlib import is allowed only if a
   needed lemma requires it; flag it.
7. **One proof per shared argument.** Cite the landed rows the route names; never re-walk a
   landed contract inside a target, and never write a second host, loop, trace or layout
   lemma for something already public.
8. **Size.** No cap; file size alone is not a driver (user, 2026-10-11). Report the file's final
   line count and its public and private declaration counts.
9. **Continuation budget.** If your budget runs out, deliver a partial zip whose `REPORT.md`
   states which targets are proved, which `private` helpers remain `sorry` (each with a literal
   "Proof sketch"), and which proved targets are proved modulo them. A partial is expected and
   fine; an unreported gap is not.

## Duplication governance (binding)

Run the text-level screen **before and after** (`audits/TEMPLATE.md` failure mode 5; `policy.md`,
**Duplication**). The population is widened this round to the files your rows cite and to S1b's
record helpers (`audits/evidence/fills-6/w1-fill-cont3-screen-population.txt`, 31 files). The base,
at this brief's issue tree, is `audits/logs/w1-fill-cont3-screen-base.txt`:
**1,851 declarations, 2,237 pairs, 748,156 characters**.

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  $(cat audits/evidence/fills-6/w1-fill-cont3-screen-population.txt)
```

- **No new cross-file pair** with an owned-file declaration on one side.
- **Known hazards:**
  - `ConfigGraph.lean`'s private S1b record helpers (`s1b_record`, `s1b_recordEdge`, `s1b_record_eq_iff` and the rest): never copy them;
  - the second continuation's in-file pair (the find round's scan and skip phases, 60–68%) is recorded; add nothing to it;
  - `CfgRecord`'s private record-step helpers and `InputCall`'s private seek helpers: never copy them;
  - the template's binary counter against R8.5c: cite `exists_inputLengthTM`, never rebuild it;
  - `Catalog`'s `f2_` copies (for example `f2_head_steps`): they retire with MIG-1; cite the public rows.
- List every new in-file pair with a one-line justification. At 90% or more it is a copy:
  factor it.
- Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/w1-fill-cont3.txt` (**134 modules**: the upstream closure of
  your owned file and of every module downstream of it, at the issue tree; it now includes
  `SpaceComplexity`, since S1b imports `RecordTable`):

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/w1-fill-cont3.txt )
  ```

  **Base sorry-warning set, 26** (`audits/logs/w1-fill-cont3-base-sorries.txt`, one entry per
  declaration). Yours: `Build/RecordTable` 6. Record the base list by name first, and report any
  difference.
- **Final checks:**
  1. `Build/RecordTable`: zero errors, and exactly the four paused rows' sorry warnings (plus
     your own targets', for a partial).
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours (**24** in all for a complete delivery).
  3. Re-run the pre-ship probe `audits/evidence/wave1-statements/S128bStatementsProbe.lean.txt`: 0 errors.
- **Axiom prints** for both targets: exactly `[propext, Classical.choice, Quot.sound]` for a
  complete delivery.
- **Lint:** `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`, 0 FAIL.

## Out-of-scope sorries you will see (leave every one untouched)

- `TuringMachine/Build/RecordTable`: exists_tableFindTM, exists_tableAppendTM, exists_recordValidTM, exists_recordNextTM (paused)
- `TuringMachine/CodeSimulator`: exists_polyCanonizer, exists_uniformSimulator
- `SpaceComplexity/ConfigGraph`: NSPACE_subset_exp_dtime
- `ClassPSPACE/TQBF`: TQBF_mem_PSPACE, TQBF_PSPACEHard, TQBF_PSPACEComplete
- `SpaceComplexity/Savitch`: spaceConstructible_poly, savitch, PSPACE_eq_NPSPACE
- `SpaceComplexity/Hierarchy`: space_universal, space_hierarchy, LOGSPACE_ssubset_PSPACE, SPACE_linear_ne_NP
- `SpaceComplexity/Logspace/Path`: PATH_mem_NL, PATH_NLComplete
- `SpaceComplexity/Logspace/ImmermanSzelepcsenyi`: compl_PATH_mem_NL, NL_eq_coNL, NSPACE_compl_eq
- `TuringMachine/Build/Zone`: exists_zoneShiftInTM, exists_zoneShiftOutTM

If a proof seems to *need* one of these beyond a named citation, that is an escalation, not a license.

## REPORT.md checklist

- [ ] 2/2, or the partial frontier (rule 9); the base hash and the ancestor check.
- [ ] Every new declaration with its role; every flagged appendix, status update and import.
- [ ] Requested shared lemmas, promotion candidates and escalations, or "none".
- [ ] Duplication: both screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the re-run probe; both targets' axiom prints; the lint
      line. The diff touches only your owned file, and the paused rows are byte-identical.
- [ ] The sanity cases, executed.

## Known pitfalls at this pin (hard-won)

- `Cfg.inputPos : Fin (|input| + 2)` starts at `1`; `0` and `|input| + 1` are the clamped blanks
  (`moveInputPos`); compare lifted positions by `.val`.
- A halted source has `M.step c = c` and `M.outputSymbol c = none` (`step_of_halt`,
  `outputSymbol_of_halt`).
- `seamCompTM_firstReturn_ofCfg` needs the callee's cut at `t = 0` as well.
- A structure update inside `runFrom` needs an ascription:
  `({c with state := some s, inputPos := 1} : Cfg k Bool S x)`.
- `decide` cannot evaluate `Nat.bits`/`Nat.size`, hence `posWidth`: use `Nat.size_eq_bits_len`,
  `Nat.lt_size_self`, `Nat.lt_size`, `Nat.size_one`.
- `omega` with products and powers as atoms (`ring` first to expose them). The linter needs a
  literal "Proof sketch" before every `sorry` (partial only).
- `scanTM`'s accumulator is `A : Type` and the phase types must be finite; `phaseHostTM`'s
  states `Σ i, Ph i` need `[Fintype I]` and `[∀ i, Fintype (Ph i)]`, and `DecidableEq` likewise.
  `FinTM` wants `State : Type`.
- `rewind_heads`/`rewind_scan_heads` are declared in `Build/Catalog.lean` but live in
  `Turing.FinTM`.
- The overlay transport needs a table that ignores its input (`hin`) and never writes a blank
  (`hnb`): it serves `incrementTM`/`decrementTM`, not rows that read the input. Check its two hypotheses
  before using it for any other row.
- `embedEmitCfg`'s output is `pre ++ c.output`: start every lifted `Bool` configuration with
  output `[]` and `pre :=` the host's output.
- An expansion leaves its counter all `true`: copy `ws` to the scratch counter before each one.
