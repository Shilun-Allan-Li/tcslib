# Ch3–4 fill campaign — wave-1 fill, continuation 5: §12.8b record tables, row 18 (`Build/RecordTable.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD`
  succeeds. That commit contains:
  - the fills-8 integration (`audits/fills-8-integration.md`), with the fourth continuation's report
    `audits/wave1-fill-agent-reports/recordtable-5-REPORT.md` (row 17 proved);
  - MIG-0b (PR #90: the contract layer split into `Build/Contract/*`, Seam's release lemmas made
    public, the public R1 reconstruction lemma) and the B6 hosts (PR #92: the windowed runner, its
    clock, `Cfg.inWindow_init`, the summary tags), both merged;
  - this round's order list (`briefs/orders/w1-fill-recordtable-cont5.txt`), base sorry set, screen
    population and base, pre-ship log, and the pre-ship probes with their generators
    (`audits/evidence/w1-fill-recordtable-cont5/`).

  If the check fails, **stop**.
- **Branch at exactly that commit, not at the campaign tip** (maintainer decision; new this round):

  ```sh
  git checkout -b fill/w1-recordtable-cont5 @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  ```

  Record that hash as your base in `REPORT.md`. Never rebase, merge or cherry-pick later campaign
  commits. The campaign tip moved while this brief was drafted (PRs #90 to #93 merged). Those PRs
  changed `Seam`, `Embed`, `Catalog`, `CounterLoop`, `CfgRecord`, `StateRenaming` and `Finite`, all
  in your file's import closure. They brought `Build/Contract/Basic` into that closure and added two
  modules downstream of your file. More landings are queued.
  Pinning keeps your base, your base sorry set and your screen base exactly the ones this brief
  states. The maintainer re-checks your delivery at integration on the tip of that day. Ground rule 10
  says what the pinned base means for your citations.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-w1-recordtable-cont5.zip`,
  containing `REPORT.md`, the full modified source, a `git format-patch` series against
  `@ANCESTOR@`, a git bundle whose only prerequisite is `@ANCESTOR@`, the bootstrap and final sweep
  logs, the axiom log, the sanity evidence file and its log, both screen outputs, and `SHA256SUMS`.

## Parallel batches this round (disjoint files or declarations; never edit another batch's)

| Batch | Brief | Owns |
|---|---|---|
| §12.8b record tables, continuation 5 | `briefs/w1-fill-recordtable-cont5.md` | `TuringMachine/Build/RecordTable.lean`: row 18 and the home below only |

Other batches dispatched in the same round own other files (for example RD-2a and RD-2b own
`ClassPSPACE/TQBF.lean` and `FormulaKit/*`, which are downstream of yours). A parallel batch's work is
invisible to your base and your screen.

## What this is

**A fifth continuation, narrowed to row 18** (user, 2026-10-12: "Narrow to rows 17–18"; row 17 was
proved by the fourth continuation and integrated at fills-8). The file has **15 of 20** targets
proved. Rows 15, 16, 19 and 20 (find, append, validity, next) stay **paused** as retirement
candidates (backlog MIG-23): **do not work on them, and leave their bodies untouched.**

**This batch is row 18 only:** `Turing.exists_recordInitTM`, the initial record. Its consumer is the
space hierarchy's **window route** (design §16b item 3, backlog RD-3). There, `space_hierarchy`'s
diagonalizer writes `U₀`'s initial record at radius `r = a · g(n)`, tagged with the empty-output
summary, by `exists_recordInitTM`. It then runs the H3 windowed runner, landed with PR #92, on that
record (`SpaceComplexity/Hierarchy.lean`'s sketch, lines 206 and 259, names row 18). **The
proved-modulo set is empty:** a complete delivery has no `sorryAx` in row 18.

**What is proved:** row 17, `exists_recordTemplateTM`, with standard axioms only, by 28 privates. Your
previous report's frontier builds row 18 from it (steps 1–5 there; the route below makes them
concrete).

**Read first:** row 18's docstring, whose proof sketch is binding, and its two flagged appendices;
row 17's statement and its continuation-4 appendix; the previous report
(`audits/wave1-fill-agent-reports/recordtable-5-REPORT.md`); `audits/fills-8-integration.md`; the
earlier briefs `briefs/w1-fill-recordtable-cont4.md` and `briefs/w1-fill-recordtable-cont3.md`,
whose gate guidance still binds for this row; design §12.8b and §16b item 3; `Build/RecordTable.lean`;
the pre-ship overlay `audits/evidence/w1-fill-recordtable-cont5/RecordTableOverlay.lean.txt`.

**Pre-ship check (maintainer, executed at the issue tree `1b6b972c`, which `@ANCESTOR@` extends without
a Lean change; `audits/logs/w1-fill-recordtable-cont5-preship.log`):**
- `audits/evidence/w1-fill-recordtable-cont5/RT5ImportProbe.lean.txt` (86 `#check`s): every public
  declaration this brief cites, and every one its pitfalls and prohibitions name, resolves in your
  file's import context. 0 errors, 0 warnings. **Re-run it after your delivery.**
- `audits/evidence/w1-fill-recordtable-cont5/RT5ConsumerProbe.lean.txt`: row 18's frozen endpoint
  meets the windowed runner's record precondition at the diagonalizer's data (below,
  **Consumer interface**). 0 errors, 0 warnings.
- `audits/evidence/w1-fill-recordtable-cont5/RecordTableOverlay.lean.txt`, generated by
  `tools/mkoverlay.py` from `tools/home.lean.txt` and `tools/row18body.lean.txt`, every edit asserted.
  It is `RecordTable.lean` with the home block inserted at the home and row 18's body replaced by a
  skeleton. Elaborated in your file's import context: **0 errors, 0 non-sorry warnings, 6 sorry
  warnings** (the four paused rows, the suggested `rt_tail_run`, and the skeleton's one sorried
  obligation). It shows the following:
  - the three prescribed privates below are **proved** there, on standard axioms;
  - the suggested tail writer and the whole suggested machine elaborate, with their instances;
  - row 17 runs through R1 at row 18's start, its hypotheses discharged from row 18's own;
  - its time and head envelope fit row 18's bounds at the constant `2 · C + 64`, where `C` is row 17's;
  - the top-level R2 join is `rt_copy_seam`, and the endpoint closes against row 18's statement by
    `rfl`.

  What remains is one obligation, `rest` (the route, step 7). `tools/mkchecks.py` adds the axiom
  prints and the `#check`s of the 11 inherited privates this brief names: all resolve.

## Owned file and target (modify these and nothing else)

Lines are at the issue tree. `RecordTable.lean` itself did not change in PRs #90–#93.

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 18 | `TuringMachine/Build/RecordTable.lean:4610` | `Turing.exists_recordInitTM` | the docstring's sketch: row 17 onto a scratch tape, then the record field by field (`cfgRecord_init`); concretely, the route below | 17 (proved) |

- **Owned:** `TuringMachine/Build/RecordTable.lean`, for row 18's body, a flagged Fill appendix to its
  docstring, new `private` declarations **at the home**, and the status text of rule 3.
- **The home (binding):** the blank line **4574**, between the end of row 17's proof (line 4573,
  `  · rfl`) and row 18's docstring (line 4575). Every new private goes there, in dependency order,
  each immediately before its first consumer and after what it uses, never between a docstring and
  its declaration. Open a section comment there (`/-! ### Initial-record fill, continuation 5 -/`).
  Add no `section`, `open` or `variable` that leaks past it. The home is the only gap between row
  17, which your privates cite, and row 18, which consumes them.
- **Frozen in your file:** the 15 proved targets; the four paused rows (15, 16, 19, 20), whose bodies
  and docstrings stay byte-identical; and all **82 inherited privates**: the first delivery's 9, the
  first continuation's 4, the second's 20, the third's 21 and the fourth's 28. Cite and reuse them;
  never change them. No style clean-up is requested this round.
- **Not yours:** every other file, including `Build/CfgRecord.lean`, `Build/Seam.lean`,
  `Build/Embed.lean`, `Build/Catalog.lean`, `Build/Scan.lean`, `Build/InputLength.lean`,
  `Build/CounterLoop.lean`, `Build/Contract/*`, the consumers (`Build/WindowRun.lean`,
  `SpaceComplexity/WindowClock.lean`, `SpaceComplexity/Hierarchy.lean`) and the facade.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **The outer host is a chain of public R2 seams** (`Turing.seamCompTM`: `seamCompTM_run_ofCfg`,
  `seamCompTM_firstReturn_ofCfg`, `seamCompTM_visitedByTapeHead_ofCfg`, bundled by the inherited
  `rt_copy_seam`) **or the public phase host** (`Turing.phaseHostTM`, `phaseHostTM_run`). Do not
  write a hand controller or a new transition table.
- **Row 18 runs no `Bool` row of its own.** Row 17 already isolates its `Bool` phases. Every row-18
  phase is either a rich catalog row (`copyTM`, `clearTM`, `skipTM`, `skipBackTM`, `scanTM`,
  `writeConstTM`) or row 17 itself through R1 (`embedEmitTM`, by the prescribed
  `rt_exists_scratchTemplateTM`). Never apply `liftSymbols_runFrom` or `liftSymbols_spaceUsed` in row
  18. Row 17 permits foreign symbols outside its framed words; so do the rich rows.
- **The `k` window copies are a fixed finite chain.** `k` is a parameter of the statement, so a
  recursion on `k` unrolls into public seams, exactly like the frozen `rt_copyMachine` behind row 14.
  It is not a host (the user's ruling, 2026-10-14), and it has no runtime loop, counter or clock. The phase host over a finite index
  is the alternative.
- **Head displacement:** prove the envelope clause from each cited row's own envelope (the catalog
  rows' interval clauses, row 17's clause) composed by `rt_copy_seam`. Where a one-step or run-level
  bound is needed, use `workTapePos_step_le`, `workTapePos_apply_le`, or MIG-0b's
  `MultiTapeTM.workTapePos_runFrom_mem_Icc`. Never copy Catalog's private `f2_head_steps`.
- **Not the contract layer.** `Build/Contract/Basic` is now in your import closure (through
  `CounterLoop`), but `Build/Contract/{Seam,Embed,Catalog}` are not, and imports stay unchanged. Row
  18's statement and this file are in the existing style; compose with `rt_copy_seam`.
- If the pipeline seems to need a component that no public row provides, write it privately as a
  generic component with its own contract, list it as a promotion candidate, and continue.

### Prescribed home declarations (binding; proved in the overlay)

Take these three from `tools/home.lean.txt` verbatim. Replace their "(Prescribed, proved.)" tags by
ordinary docstrings. Their statements are binding as elaborated.

1. **`rt_exists_scratchTemplateTM`:** row 17 on an R1-selected bank `ι : Fin (K + 2) ↪ Fin k` of a
   larger rich host. Its destination is `ι 0` and its radius is `ι 1`; its other tapes `ι j`, for
   `2 ≤ j`, are blank. Row 17's time and envelope carry over, and the template is written at `ι 0`.
   The unselected host tapes, the host's prior output, the radius and every head are kept.
   - Its proof cites `exists_recordTemplateTM`, the **public** R1 reconstruction (`Cfg.select`,
     `embedEmitCfg_select`, `embedEmitCfg_eq`, since MIG-0b), `embedEmitTM_runFrom`, and the
     inherited `rt_embed_radius`.
   - It does not use the inherited `rt_embed_matches`, which the public lemma now covers.
2. **`rt_binDigits_one`:** `binDigits w 1 = true :: List.replicate (w - 1) false` for `0 < w`.
3. **`rt_initRecord_fields`:** the initial record in the words the route writes. It is
   `[st (some q₀)]`, then `digit true` followed by `|Nat.bits (|x| + 1)| - 1` copies of
   `digit false`, then `k` copies of row 17's window field
   `(replicate s false ++ true :: replicate s false).map (cell none)`, then `[tag τ₀]`. Its proof is
   `cfgRecord_init`, `rt_binDigits_one`, `rt_centeredWord`.

If a prescribed statement turns out unusable, that is an escalation (rule 4): record the obstruction
and continue.

### Suggested shape (not binding; elaborated in the overlay)

- **The tail writer**, in `tools/home.lean.txt`: `rt_tailState`, its two instances, `rt_tailEntry`,
  `rt_tailExit` and `rt_tailTM`. It writes `k` copies of the field under the head of `src`, each
  crossed on `dst`, then the one-cell field `[last]`, and returns the head of `dst`. These are catalog
  rows and R2 seams only, in `rt_copyMachine`'s shape. Its contract statement `rt_tail_run` is a
  sorried guard: the layout `fieldsTape (replicate k w ++ [[last]])`, time `(k + 1) · (4|w| + 12)`
  and envelope "layout length + 1". It is the maintainer's claim, checked by hand (the slot supplies
  every delimiter, and the source frame is never written), not a proof. Take it, adjust it or
  replace it; if you change the statement, say why in `REPORT.md`.
- **The machine** in the overlay's row-18 body: 14 phases, innermost last. The host has `K₁ + 3`
  tapes, where `K₁ + 2` is row 17's tape count, so row 18's `K` is `K₁ + 1`. The bank is
  `ι 0 = 2` (the scratch template), `ι 1 = 1` (the radius) and `ι j = j + 1` otherwise.

  | Phase | Row | Tape | Effect |
  |---|---|---|---|
  | 1 | `embedEmitTM ι R₁` (row 17) | 2 | the template `[wb, wc]` at the scratch head, with `wb = Nat.bits (|x| + 1)` as digits |
  | 2 | `writeConstTM 0 [st (some q₀)]` | 0 | the state field |
  | 3 | `skipTM 0` | 0 | crosses it |
  | 4 | `copyTM 2 0` | 2 → 0 | copies `wb` |
  | 5 | `scanTM 0 (scanMap (fun _ => digit false)) scanKeep ()` | 0 | zeroes it (`scanResult_map`) |
  | 6 | `writeConstTM 0 [digit true]` | 0 | the leading `true`: the digits of `1` |
  | 7, 8 | `skipTM 0`, `skipTM 2` | 0, 2 | cross the position field and the bound field |
  | 9 | `rt_tailTM 2 0 (tag τ₀) k` | 2 → 0 | `k` window fields and the tag |
  | 10, 11 | `skipBackTM 0` twice | 0 | back over the position and state fields |
  | 12–14 | `clearTM 2`, `skipBackTM 2`, `clearTM 2` | 2 | clear the window field and the bound field |

### The route (binding where it names a row)

1. **Scratch template.** Apply `rt_exists_scratchTemplateTM` at `ι` to the host start
   `d.mapState (fun _ => entry)`. Its three hypotheses follow from row 18's radius, slot and blank
   hypotheses (the overlay does this). `rt_template_fields` identifies the two words.
2. **State field:** phases 2–3. The slot supplies the blank after the cell.
3. **Position field:** phases 4–8. Phases 5–6 are the docstring's route ("mapped to `digit false`
   (`Turing.scanTM`), with `digit true` written on its first cell"). One permitted refinement uses one
   phase fewer: a single `scanTM` by
   `scanShift (fun _ => false) (fun _ b => RecSym.digit b)` from `true`, which writes `digit true`
   and then `digit false`s by `scanResult_shiftRight`. If you take it, say so in the Fill appendix.
   Every frame the copy and the scan need is either the template's (from row 17's endpoint and
   `fieldsTape_field`) or the slot's.
4. **Window fields and tag:** phase 9. The source frame is the template's window field, whose right
   delimiter is the blank beyond the template (tape 2 was blank everywhere at entry). The destination
   slot runs to `recordLength k |x| s`: `3 + |wb| + k · (2s + 2) + 1` is exactly the record length.
5. **Return and clean:** phases 10–14. After phase 14 tape 2 is blank again, and every head is at its
   entry position.
6. **`k = 0`:** the tail writes only the tag. The scratch template still has its `2s + 1`-cell window,
   and the radius term in row 18's bounds absorbs it (`absorb` in the overlay:
   `|joinFields template| ≤ recordLength + 2s`). This is why the constant is `2 · C + 64`, not
   `C + 64`.
7. **Package:** start from the overlay's skeleton (`tools/row18body.lean.txt`). It contains the
   scratch phase, the bound arithmetic, the join by `rt_copy_seam` and the final `rfl`. It leaves one
   obligation, `rest`: from the template's endpoint, the chain of phases 2–14 reaches its exit within
   `64 · (recordLength + |ws| + s + |x| + 1) − 1` steps, and not earlier. Its heads stay within
   `(2C + 64) · (recordLength + |ws| + s + 1)` of the entry. Its endpoint is the record on tape 0 at
   the head, with every other cell, head, the input position and the output as at row 18's entry.
   Prove `rest` by components with their own contracts; for example, the position field and the
   cleanup as privates, each joined by `rt_copy_seam`. Do not re-walk any catalog trace. If you
   change the chain, adapt the skeleton's `stateField`, `stExit`, constant and `rest` with it; the
   skeleton is a frame, not a statement.
- **Input convention** (decision 7): the native input stays at position `1`. Row 17 restores it, and
  the rich rows never move it.
- **Degenerate cases:** `x = []` (so `wb = [true]`), `s = 0` (`ws` may be `[]` or all `false`), and
  `k = 0`.

### Consumer interface (for orientation; it changes nothing in your statement or route)

PR #92 landed row 18's consumer. `Turing.exists_configWindowRunnerTM`
(`SpaceComplexity/WindowClock.lean:187`, sorried, gated) takes its input in this form:
- a configuration `c` with `c.InWindow s` (the window predicate, `Build/CfgRecord.lean:101`);
- `RecordAt d 0 (cfgRecord s c τ)`: the record at the head of tape `0`, delimited by blanks at `-1`
  and at the record length;
- every other tape blank;
- a tag update `upd` with `upd τ none = τ`.

The diagonalizer instantiates it at:
- `c = Cfg.init q₀ x`, whose window predicate is the new `Turing.Cfg.inWindow_init`
  (`CfgRecord.lean:5268`);
- `T = Fin 3`, `τ₀ = outSummaryCode (outSummary [])`, which is `0` by `outSummaryCode_nil`;
- `upd = summaryTag` (`SpaceComplexity/ConfigGraph.lean`).

Row 18's frozen endpoint gives the record precondition. The slot's blanks at `-1` and at the record
length survive as its delimiters (`RT5ConsumerProbe`, first example). The two rows also instantiate
at that data (second example). The radius tape is the consumer's to clear: row 18 keeps it, and the
runner wants the other tapes blank. None of #92's definitions (the window predicate, the summary
tags) enters row 18's statement, and your proof needs none of them. Do not cite `WindowRun` or
`WindowClock`: they are downstream of your file.

## Gate guidance (binding)

- **Intercept every verdict** (§12.8 statement gate, round-2 note 7). The contracts bound
  nothing after a module's own verdict or exit. Redirect at each sub-module's exit time; never
  run a sub-module past its exit.
- **No termination hypothesis** (round-1 note 35): each contract supplies its finite `t`.
- **The work-space clause** bounds every work head through the exit, independently of `|x|`
  (round-1 major 1). Row 17's envelope has no `|x|` term beyond its template length, and every
  rich row's envelope lies within its layout. The exact finish restores every head, the input
  position, the scratch and the output.
- **Note 46:** file size is not a driver; report `RecordTable`'s size.
- **Sanity cases at fill:** execute the initial record end to end, which the previous delivery could
  not (its report: "layout evaluations only"). Run it on `x = []`, `s = 0` with `k = 0` and with
  `k = 1`, and on `|x| = 3`, `s = 2`, `k = 1`. Put them as examples (`decide`, `rfl` or a bounded run)
  in an evidence file `RT5Sanity.lean.txt`, as your `W1Cont4Sanity.lean` did, and include it and its
  log in the zip.

## Cited infrastructure (public and proved at `@ANCESTOR@`; all in `RT5ImportProbe.lean.txt`)

- **RecordTable:** `exists_recordTemplateTM` (row 17), `recordTemplate`, `recordLength`,
  `cfgRecord_init`, `binDigits_posWidth_succ`, `joinFields_length`, `fieldOffset_length`,
  `joinFields_cfgRecord_length`, `joinFields_recordTemplate_length`, `cfgRecord_field_ne_nil`,
  `exists_fieldsCopyTM` (row 14).
- **RecordTable privates (yours to cite, never to change; checked in the overlay by
  `tools/mkchecks.py`):** `rt_copy_seam`, `rt_embed_radius`, `rt_moveWordTM`, `rt_moveWord_run`,
  `rt_bufferMask`, `rt_template_fields`, `rt_centeredWord`, and the pattern of `rt_copyState`,
  `rt_copyMachine` and `rt_copy_run`. (`rt_embed_matches` stays frozen; new code uses the public
  reconstruction instead.)
- **Catalog:** `copyTM`, `clearTM`, `skipTM`, `skipBackTM`, `scanTM` with their `_run_ofCfg`
  contracts; `scanResult_map`, `scanResult_shiftRight`, `scanMap`, `scanKeep`, `scanShift`;
  `ScanPhase`, `SweepPhase`, `SeekPhase`; `joinFields`, `fieldsTape`, `fieldOffset`, `fieldsTape_field`.
- **Scan:** `WritePhase`, `writeConstTM`, `writeConstTM_run_ofCfg`.
- **Seam:** `seamCompTM`, `seamCompTM_run_ofCfg`, `seamCompTM_firstReturn_ofCfg`,
  `seamCompTM_visitedByTapeHead_ofCfg`, `phaseHostTM`, `phaseHostTM_run`.
- **R1 (Embed):** `embedEmitTM`, `embedEmitCfg`, `embedEmitTM_runFrom`, `embedEmitTM_frame`,
  `embedEmitCfg_selected_tape`, `embedEmitCfg_selected_pos`; since MIG-0b, `Cfg.select`,
  `embedEmitCfg_select`, `embedEmitCfg_eq`, `embedEmitCfg_unselected`.
- **CfgRecord:** `RecSym` (`st`, `digit`, `cell`, `tag`), `RecSym.digitEmb`, `binDigits`, `posWidth`,
  `cfgRecord`, `cfgRecord_length`, `RecordAt`.
- **Configurations and runs:** `Cfg.init`, `Cfg.mapState`, `Cfg.ext`, `FinTM.bufferTape`,
  `MultiTapeTM.runFrom`, `MultiTapeTM.runFrom_succ_eq_step'`, `MultiTapeTM.workTapePos_step_le`,
  `workTapePos_apply_le`, `MultiTapeTM.workTapePos_runFrom_mem_Icc`.
- **Do not cite** anything downstream (`Build/WindowRun`, `SpaceComplexity`, `ClassPSPACE`) or
  outside your import closure (`Build/Contract/{Seam,Embed,Catalog}` are not imported).

## Ground rules (binding)

1. **File ownership.** Only `Build/RecordTable.lean`. You may change row 18's body, append a flagged
   **Fill appendix** to its docstring where your proof refines the sketch, and add new `private`
   helpers at the home. List every new declaration with its role. A lemma that genuinely belongs in a
   shared file is written privately, flagged in `REPORT.md` as a promotion candidate, and promoted by
   the maintainer at integration (`workflow.md` §4, rule 1).
2. **Statement freeze** over every target and every landed declaration: no renames,
   re-signatures, restatements or attribution edits. Docstrings stay; a flagged
   **"Fill appendix"** is expected wherever your proof refines or replaces a sketch's route.
3. **Status text.** Only your file's status text may change: the module's "Status" paragraph, its
   "Main results" tag for row 18, and row 18's own appendix, each to "proved"; flag each. No new
   public declaration.
4. **Escalation** on anything unprovable as stated, including a prescribed private or a cited row that
   does not compose as the route says: stop on that item, record the obstruction, and continue with
   the rest.
5. **No touching other sorries.** The four paused rows stay exactly as they are. Cite proved
   material; never re-prove it.
6. **Imports.** Unchanged. No TCSlib import may be added. A Mathlib import is allowed only if a
   needed lemma requires it; flag it.
7. **One proof per shared argument.** Cite the landed rows the route names; never re-walk a landed
   contract inside a target. Never write any of the following:
   - a second seam certificate (`rt_copy_seam` exists);
   - a second R1 identification (`embedEmitCfg_eq` and `embedEmitCfg_select` are public);
   - a second R1 envelope lemma (`rt_embed_radius`);
   - a second word move (`rt_moveWord_run`);
   - a second field-layout lemma.
8. **Size.** No cap; file size alone is not a driver (user, 2026-10-11). Report the file's final line
   count and its public and private declaration counts (base: 4,779 lines; 28 public / 82 private, by
   the lint's count).
9. **Continuation budget.** If your budget runs out, deliver a partial zip whose `REPORT.md` states
   whether the target is proved, which `private` helpers remain `sorry` (each with a literal "Proof
   sketch"), and what is proved modulo them. A partial is expected and fine; an unreported gap is not.
10. **The pinned base** (new, binding). Cite only declarations that are public at `@ANCESTOR@`, and
    your file's own privates.
    - Since MIG-0b, Seam's release lemmas are public (`seamReleaseTM_runFrom_pos` and the rest), and
      `counterLoopOrbit` is an `abbrev` of `roundOrbit`. Row 18 needs neither a release nor a counter
      loop.
    - Do not rely on unfolding the body of any definition in `Seam`, `Embed`, `CounterLoop` or
      `CfgRecord`. Use their public contracts only; `rt_copy_seam` already does.
    - Nothing that lands after your base is visible to you. If a lemma you want is "about to land",
      write it privately and flag it as a promotion candidate.
    - List every declaration you cite outside your file in `REPORT.md`. The import probe covers this
      brief's list. If you cite more, add them to a copy of the probe and run it.

## Duplication governance (binding)

Run the text-level screen **before and after** (`audits/TEMPLATE.md` failure mode 5; `policy.md`,
**Duplication**). The population is widened this round to **43 files**
(`audits/evidence/w1-fill-recordtable-cont5/screen-population.txt`):
- the previous rounds' 31 files;
- the cited files they lacked: `Configuration`, `Deterministic`, `StateRenaming`, `Simulation`,
  `Finite`;
- the row's consumers: `SpaceComplexity/Hierarchy`, `Build/WindowRun`, `SpaceComplexity/WindowClock`;
- the contract layer as a known overlap: `Build/Contract/Basic` (in your import closure) and
  `Build/Contract/{Seam,Embed,Catalog}`.

**The screen's known defect, and the workaround.** `copy-text-screen.py` labels every file by its
basename. Two same-named files therefore share a label. A pair between two declarations of the same
name in those files looks like a declaration paired with itself and is dropped, and the output
cannot say which file a pair is in. **Your
population has three such collisions**: `Build/Contract/{Seam,Catalog,Embed}.lean` beside
`Build/{Seam,Catalog,Embed}.lean`. The screen is therefore run, unchanged, on byte-identical copies
whose names encode the full path (`/` becomes `__`). The base was computed this way, and you must do
the same, before and after:

```sh
bash audits/evidence/w1-fill-recordtable-cont5/tools/flat-screen.sh . \
  audits/evidence/w1-fill-recordtable-cont5/screen-population.txt "$(mktemp -d)" > screen-before.txt
```

The base, at the issue tree, is `audits/logs/w1-fill-recordtable-cont5-screen-base.txt`:
**2,098 declarations, 2,428 pairs, 790,157 characters**. Your "before"
must reproduce it after its header line. Measured at the base, a control run with basename labels gives the same counts and the same pairs. No pair links two same-basename files, so the defect drops nothing there. Your file's basename is unique, so it cannot drop a pair that touches your file either. The flattened labels keep the before/after comparison exact by name.

- **No new cross-file pair** with an owned-file declaration on one side.
- **Known hazards:**
  - the frozen recursive copier `rt_copyMachine`/`rt_copy_run`: the suggested tail writer has its
    shape. Follow its pattern, but do not transcribe its proof. If your tail proof pairs with it,
    measure the pair and justify it;
  - **the home block itself, measured pre-ship.** The tip's file with only `tools/home.lean.txt`
    inserted was screened on the same population: 7 more declarations, 2 more pairs (2,105 / 2,430 / 790,285). Both new pairs are in-file, between the suggested tail state's two instances: `rt_tailState_decidableEq` reproduces `rt_tailState_fintype` at 65%, and the reverse at 60%. This is structural-recursion boilerplate, below 90%. There is no cross-file pair, and nothing pairs with the inherited `rt_copyState` family or with `Build/Embed`'s reconstruction lemmas. If you take the tail writer verbatim, report these two pairs as pre-disclosed;
  - the recorded in-file pairs touching your file (10 at the base): the `rt_copyState` instance
    family (55–73%), the find round's scan and skip phases (60–68%), `joinFields_cfgRecord_length`
    against `cfgRecord_init` (56%), and `rt_richWindow_run` against `rt_moveWord_run` (56%). Add
    nothing to them;
  - the R1 reconstruction family: `Build/Embed.lean`'s `embedEmitCfg_eq`/`embedEmitCfg_select`
    against the inherited `rt_embed_matches`. Cite the public lemmas; do not write a third member;
  - `Build/Contract/Seam.lean`'s sequencing and trajectory bookkeeping: cite `rt_copy_seam`;
  - `ConfigGraph.lean`'s private S1b record helpers (`s1b_record`, `s1b_recordEdge`,
    `s1b_record_eq_iff` and the rest), and the private helpers of `WindowRun` and `WindowClock`:
    never copy them;
  - `CfgRecord`'s private record-step helpers and `InputCall`'s private seek helpers: never copy them;
  - `Catalog`'s `f2_` copies (for example `f2_head_steps`): they retire with MIG-1; cite the public
    rows.
- List every new in-file pair with a one-line justification. At 90% or more it is a copy:
  factor it.
- Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/w1-fill-recordtable-cont5.txt` (**271 modules**: the upstream
  closure of your owned file and of every module downstream of it, at the issue tree, topologically
  ordered). Your file is module 157, its import closure has 23 modules, and 50 modules are downstream
  of it, `Build/WindowRun` and `SpaceComplexity/WindowClock` among them. The list grew from the
  previous round's 134 (137 modules added, none removed). Most of the growth is the ARM extensions
  downstream of `ConfigGraph` and the 38 circuit modules their closure brings in; the rest is the
  contract layer, RD-2's kit, C1's hosts and the B6 hosts.

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/w1-fill-recordtable-cont5.txt )
  ```

  **Base sorry-warning set, 69** (`audits/logs/w1-fill-recordtable-cont5-base-sorries.txt`, one entry
  per declaration, 16 modules). Yours: `Build/RecordTable` 5 (rows 15, 16, 18, 19, 20). Record the
  base list by name first, and report any difference.
- **Final checks:**
  1. `Build/RecordTable`: zero errors, exactly the four paused rows' sorry warnings (plus your
     helpers', for a partial), and no other warning in anything you added.
  2. Every module of the order list after your file (114 modules), re-checked against your final
     source, and every other module: zero errors, and sorry warnings exactly the base's minus yours
     (**68** in all for a complete delivery).
  3. Re-run `audits/evidence/w1-fill-recordtable-cont5/RT5ImportProbe.lean.txt` and
     `RT5ConsumerProbe.lean.txt`: 0 errors. Elaborate `RT5Sanity.lean.txt`: 0 errors.
- **Axiom prints** for row 18, row 17 and every new private: exactly `[propext, Classical.choice,
  Quot.sound]` (or a subset) for a complete delivery.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`, 0 FAIL
  (base: 0 FAIL, 11 WARN over 32 files; `RecordTable`'s size WARN is not a driver).

## Out-of-scope sorries you will see (leave every one untouched)

- `TuringMachine/Build/RecordTable`: exists_tableFindTM, exists_tableAppendTM, exists_recordValidTM, exists_recordNextTM (paused)
- `FormulaKit/Gate`: template_eval, template_numVars_le, template_length_le, template_widthAtMost, numVars_le_of_forall_lt, exactlyOne_eval, cost_flatMap_le, serialize_length_le, gate_cost_le, exactlyOne_cost_le
- `FormulaKit/Emit`: polyTimeComputable_fragment_iff_serialize, polyTimeComputable_flatMap_range, polyTimeComputable_fragment_relabel, polyTimeComputable_fragment_gate_select, polyTimeComputable_unary_sub, polyTimeComputable_unary_mul, polyTimeComputable_unary_le, polyTimeComputable_unary_div, polyTimeComputable_unary_mod, polyTimeComputable_serialize_relabel_add
- `ClassPSPACE/TQBF`: width_le, code_length, code_getD_inputVar, code_getD_headVar, code_getD_stateVar, code_getD_workVar, code_getD_summaryVar, code_input_eq, code_eq_iff, validity_eval_iff, adjacency_eval_iff, adjacency_eval_of_ne, acceptance_eval_iff, validity_numVars_le, acceptance_numVars_le, adjacency_numVars_le, exists_serialize_length_le, polyTimeComputable_serialize_validity, polyTimeComputable_serialize_adjacency, polyTimeComputable_serialize_acceptance, polyTimeComputable_code_initCfg
- `TuringMachine/CodeSimulator`: exists_polyCanonizer, exists_uniformSimulator
- `TuringMachine/Build/StepClock`: exists_stepClockTMVia
- `TuringMachine/Build/WindowRun`: exists_windowLoopTM, exists_windowRunnerTM
- `SpaceComplexity/WindowClock`: exists_configWindowRunnerTM
- `SpaceComplexity/Savitch`: spaceConstructible_poly, savitch
- `SpaceComplexity/Hierarchy`: space_universal, space_hierarchy, LOGSPACE_ssubset_PSPACE, SPACE_linear_ne_NP
- `TuringMachine/Build/NDHost`: ndWriterTM_run_block
- `TuringMachine/Build/Zone`: exists_zoneShiftInTM, exists_zoneShiftOutTM
- `TuringMachine/Build/InputWindow`: exists_inputWindowCopyTM
- `TuringMachine/Build/InputDevice`: exists_rulerTestTM, exists_rulerDeviceTM, exists_rulerHostTM
- `TuringMachine/SelfUniversal`: exists_selfStartupTM, exists_selfUniversal
- `TuringMachine/NDCodeSimulator`: exists_replayCanonizer, exists_ndInterpreterCore

If a proof seems to *need* one of these beyond a named citation, that is an escalation, not a license.

## REPORT.md checklist

- [ ] 1/1, or the partial frontier (rule 9); the base hash (`git rev-parse HEAD` at branch creation,
      equal to `@ANCESTOR@`) and the ancestor check.
- [ ] Every new declaration with its role. Whether the three prescribed privates were taken verbatim;
      the tail writer as suggested or your own, with any change to `rt_tail_run`'s statement and its
      reason; the position-field variant used. Every flagged appendix, status update and import.
- [ ] Requested shared lemmas, promotion candidates (the tail writer and the scratch-template
      transport are natural ones) and escalations, or "none".
- [ ] Rule 10: the list of declarations cited outside your file, and both probes re-run.
- [ ] Duplication: both flattened screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; both targets' axiom prints and the new privates'; the lint
      line. The diff touches only your owned file; the paused rows and the 82 inherited privates are
      byte-identical.
- [ ] The sanity cases, executed end to end.

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
- The overlay transport `liftSymbols_runFrom_over` needs a table that ignores its input and never
  writes a blank; row 18 has no `Bool` row, so it should not arise.
- `embedEmitCfg`'s output is `pre ++ c.output`. `Cfg.select` empties the source output, so the
  scratch-template guard runs row 17 on output `[]` with `pre :=` the host's output.
- An expansion leaves its counter all `true` (row 17's concern; row 18 runs no expansion).
- MIG-0b moved `MultiTapeTM.runFrom_mapState_of_agreeOn` to `StateRenaming` and
  `MultiTapeTM.spaceUsedByTape_le_card_Icc` to `Finite`; the names are unchanged.
- From the pre-ship probe. Each of the first five failed a run of the overlay:
  - a `let` machine needs its alphabet ascribed, `let M : MultiTapeTM (K + 3) (RecSym Q T) _ := …`;
    otherwise "don't know how to synthesize implicit argument `Symbol`";
  - a record-symbol list inside a type needs `[(RecSym.st (some q₀) : RecSym Q T)]`;
  - `writeConstTM`'s control is `WritePhase w₀.length`, entry `.wr 0`. A seam whose second machine is
    itself a seam enters at `.inl` of that machine's first entry (`.inl .run`, not `.run`);
  - `inferInstance` fails on the 14-summand control's `DecidableEq`: give the existential's as
    `Classical.typeDecidableEq _`, as row 17 does, and its `Fintype` by
    `set_option synthInstance.maxSize 1024 in infer_instance`;
  - after `rw [run]`, the endpoint `c.mapState Sum.inr = { … }` is left open: close it by `rfl`.

  And three that held at once:
  - `rt_embed_radius` states its conclusion under a `let`: apply it to `u hu j`, then `rw` the
    identification;
  - `(1 : Fin (K + 3))` and `⟨1, _⟩` are defeq. Prove the bank's values by `Fin.ext; simp [ι]`;
  - row 17's constant must be doubled: the template is at most `recordLength + 2s` long, not
    `recordLength` (`absorb`).
