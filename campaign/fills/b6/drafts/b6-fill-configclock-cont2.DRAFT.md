# Ch3–4 fill campaign — B6 fill, batch F3, continuation 2: the configuration-count runner (`Turing.exists_configWindowRunnerTM`, `SpaceComplexity/WindowClock.lean`)

<!-- DRAFT (maintainer), 2026-10-18. Issues after #134 (F3 cont1's landing) and #139
(`wordPatch_append`) merge; #132 merges before #134. Issue-time items: ⟨BASE⟩, ⟨IN-FLIGHT⟩,
⟨LINES⟩ (the file at the base: home, target, sorry, status paragraph; with gate 52's docstring
commit on #134: 458 lines, target 426, sorry 456, status 404–424; without it 452, 420, 450,
404–418), ⟨ORDER⟩, ⟨ROOTS⟩,
⟨SORRIES⟩ (28 expected), ⟨SCREEN⟩ (the review's out/30-screen-after.txt, re-screened at the
base), ⟨PROBE⟩ (cont1's 60 + the six cont1 helpers' citations + `wordPatch_append`), ⟨LINT⟩ and
the pre-ship log. -->

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **F3 continuation 1's partial, landed (PR #134):** your file with eleven private `cw_` lemmas:
    the first round's five (`cw_true_value`, `cw_round_cost`, `cw_budget`, `cw_time_bound`,
    `cw_head_bound`) and continuation 1's six (`cw_field_total`, `cw_record_clock`, the one-cell
    leaf `cw_leftTM` with `cw_left_run`, `cw_copy_constant`, `cw_clear_patch`), and the target's
    **Implementation status** paragraph;
  - **`Turing.wordPatch_append`** (PR #139, `Build/StepClock`; its API gate
    `campaign/gates/56-wordpatch-append/`): adjacent word patches join. It is **the user's ruling
    of 2026-10-18 on continuation 1's escalation E2** (option B);
  - continuation 1's report and the maintainer's review
    (`campaign/fills/b6/reports/configclock-cont1-REPORT.md`,
    `campaign/fills/b6/reviews/configclock-cont1/REVIEW.md`), whose "Continuation 2" list this
    brief follows;
  - the specification, core and brief-inventory APIs (PRs #112, #116, #118), B6's F1 and F2 (the
    step clock, the windowed loop and runner), row 18 and the B6 fill plan
    (`campaign/fills/b6/evidence/b6-fill/B6-fill-plan.md`; F3 is §3 and §6,
    Route A);
  - the fill-agent environment addendum `campaign/standards/fill-environment-addendum.md`
    (**v2.3**: Part 1, the resources and the cache, applies on every host; **the cache is fetched
    for your brief's Mathlib roots only**), and the copy-text screen v3
    `scripts/copy-text-screen-v3.py`;
  - **this round's inputs** (`campaign/fills/b6/inputs/b6-fill-configclock-cont2/`): the import
    probe, the consumer probe and the screen population; the order list
    `campaign/fills/b6/orders/b6-fill-configclock-cont2.txt`, the base sorry set, the screen base
    and the pre-ship log (`campaign/fills/b6/logs/b6-fill-configclock-cont2-*`).
- **Before anything else, run Part 1 of the addendum**: the preflight, with its stop rule
  (E-RES). Fetch the cache for your roots only; never run the unfiltered `lake exe cache get`. If
  Lean cannot start, follow Part 2 exactly. **If Lean never runs, do not draft proofs blind**:
  deliver the environment report only.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/b6-configclock-cont2 @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  ```

  Record that hash as your base in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-b6-configclock-cont2.zip`. It
  contains `REPORT.md` and the full modified source; a `git format-patch` series against your
  base and a git bundle whose only prerequisite is your base; the bootstrap and final sweep logs
  and the axiom log; both screen outputs; and `SHA256SUMS`.
- **Checkpoint zips.** After each checkpoint below, commit and write
  `fill-b6-configclock-cont2-cp<N>.zip` with the same contents as of that commit (the final
  sweep may be your module's check only). Each checkpoint is a landable partial.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign tip after #134 and #139** (⟨BASE⟩). Lines in this
  brief are that tree's. `WindowClock.lean` there is continuation 1's landing (⟨LINES: 452⟩
  lines; 4 public, 11 private). Every probe and measurement below was run there, against the
  olean snapshot of ⟨the replay at the base⟩.
- **F2's runner is proved and sorry-free.** Cite only its statement (ground rule 10).
- **In flight, merging after your base and invisible to it:** ⟨IN-FLIGHT⟩. Cite nothing they add.

## Parallel batches this round

None in `WindowClock.lean`. F5 (`Build/InputDevice`) may run in parallel. F6 and H follow.

## What this is

**B6's third batch, continued again, on the critical path to `Complexity.space_hierarchy`**
(F1 → F2 → F3 → H). One target, frozen: **`Turing.exists_configWindowRunnerTM`** (line
⟨420⟩), the windowed runner that builds its own clock, large enough for every configuration in
the window plus the extra halt-test round. Its statement passed the B6 hosts gate
(`campaign/gates/13-b6-hosts-statements/findings.md`, PASS 0/0/5). **The route is Route A**: write
an all-`true` clock word, run F2's runner on it, clear it.

**Where it stands.** The clock arithmetic is proved at the actual record (`cw_field_total`,
`cw_record_clock`: `c = C + |Q| + 8` passes, width at most `c · L`, value enough for every round
up to `configBound + 1`), and so are the writer's leaf and its two endpoint shapes:
- `cw_left_run`: the one-cell move onto the clock's delimiter, one silent step;
- `cw_copy_constant`: the constant mapped copy of one field, writing `e` on the destination
  interval, which needs delimiters only on the source and so also appends to a clock prefix;
- `cw_clear_patch`: the clear after the runner, leaving the clock tape blank.

**Open:** the clock writer (the per-field round, a pass, `c` passes, the rewinds), and the target
(the composition, the endpoint, the ledger). Continuation 1 stopped the writer on escalation E2;
**E2 is answered by `wordPatch_append`** (below).

**Read first:**
- the target's docstring: its Route A sketch and the **Implementation status** paragraph, whose
  "Proof sketch (remaining)" is the route below. The sketch's whole-layout writer
  (`W := c_M · L` by `copyTM`/`skipTM`/`scanTM`) is an alternative not in use: the record's
  fields are separated by blank cells and those rows read one blank-delimited word. This
  brief's field-by-field writer (`W = c · F ≤ c · L`) refines the sketch and binds;
- `exists_windowRunnerTM`'s statement and docstring (`Build/WindowRun.lean`);
- `wordPatch`, `wordPatch_of_mem`, `wordPatch_of_not_mem` and **`wordPatch_append`**
  (`Build/StepClock.lean`);
- continuation 1's review, F1 (E2) and its "Continuation 2" list.

**Pre-ship check** (maintainer, at the base; `campaign/fills/b6/logs/b6-fill-configclock-cont2-preship.log`):
- **Your file** elaborates with exactly the target's sorry warning.
- **The import probe** (`F3C2ImportProbe.lean.txt`, ⟨PROBE: N⟩ `#check`s: continuation 1's 60, the
  names its six helpers cite, and `wordPatch_append`): 0 errors, 0 warnings. Re-run it after your
  delivery.
- **Silence** (maintainer, at pre-ship): the framed rows' lemmas (`copyMapTM_run_ofCfg`,
  `skipTM_run_ofCfg`, `clearTM_run_ofCfg`) state the output only at their endpoints; confirm
  the published route to the round's and the writer's intermediate output clause, and name it
  here.
- **The consumer probe** (`F3ConsumerProbe.lean.txt`, unchanged): row 18's endpoint, after the
  radius word is cleared, is this contract's precondition. 0 errors.
- **The join** (`F3C2JoinProbe.lean.txt`): `cw_copy_constant`'s endpoint on the clock tape is
  `wordPatch ct p (List.replicate |f| e)`, and two such writes at `p` and `p + |f|` join by
  `wordPatch_append` into `wordPatch ct p (List.replicate (|f| + |g|) e)`; from public lemmas
  only, sealed. (Built 2026-10-18 against `oleans-lc6m` with `wordPatch_append` inlined, 0
  errors: `drafts/b6-fill-configclock-cont2/F3C2JoinProbe.lean.txt`; re-run at issue citing the
  published lemma.)

## Owned regions and targets (modify these and nothing else)

| # | File:line | Target | Route |
|---|---|---|---|
| 1 | `SpaceComplexity/WindowClock.lean:⟨420⟩` | `Turing.exists_configWindowRunnerTM` (frozen statement) | Route A |

Your regions:
- **(a) the home**, lines ⟨143–⟩…: after `/-! ### The runner -/` and up to the target's docstring.
  It holds the eleven `cw_` lemmas and your new `private` declarations. You may adjust the `cw_`
  lemmas' statements or remove them (private, and none is used by another file); report each
  change. `private` only, and no `section`, `open` or `variable` that leaks past it.
- **(b) the target's body**, the `sorry` on line ⟨450⟩.
- **(c) the target docstring's Implementation status paragraph** (lines ⟨404–418⟩): rewrite it
  for the final state. When the target is proved, keep a short note of the construction used
  (the clock over field cells, of width `c · F`, written field by field), since the frozen Route
  A sketch still describes the whole-layout alternative. It is public-facing library text:
  what is proved and what is open, in mathematical terms, with no campaign labels (brief, gate,
  finding, escalation or batch names), no dates and no session narrative. The same holds for your
  new docstrings; provenance goes in `REPORT.md`.

Everything else is frozen: the module header, the three proved bridges, the target's docstring
before (c), the statement, and every other file. The maintainer updates the module's status text
at integration.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **Compose by the public combinators:** R2 seams (`seamCompTM`, `seamCompTM_run_ofCfg`,
  `seamCompTM_firstReturn_ofCfg`, `seamReleaseTM`), the phase host (`phaseHostTM`,
  `phaseHostTM_run`), and R1 embedding (`embedEmitTM`, `embedEmitTM_runFrom`, `embedEmitTM_frame`,
  `embedEmitCfg_eq`). Never write a second seam, phase host, loop or embedding transport.
- **The rows:** the mapped copy `copyMapTM_run_ofCfg` (through `cw_copy_constant`); `skipTM_run_ofCfg`,
  `skipBackTM_run_ofCfg`, `clearTM_run_ofCfg` (through `cw_clear_patch`); F2's runner
  `exists_windowRunnerTM`; state transport `MultiTapeTM.runFrom_mapState_of_agreeOn`.
- **Leaves you may write:** `cw_leftTM` (landed) and a one-step exit dispatch if a phase host
  needs one. Nothing else.
- **The join (E2, ruled B):** adjacent constant writes on the clock tape join by
  **`Turing.wordPatch_append`**. Restate `cw_copy_constant`'s clock-tape endpoint as
  `wordPatch ct p (List.replicate |f| e)` (by `wordPatch_of_mem`/`_of_not_mem` and the
  `FinTM.bufferTape` equations), and join a pass's writes into one patch. **An interval case
  split on an `if` (as in such a restatement) is ordinary bookkeeping of your own endpoint, not
  "record bookkeeping" under ground rule 7**; it is allowed.
- **Promotion candidates** (notes only, in `REPORT.md`): the clock writer.

### The route (binding where it names a row): the writer in checkpoints

Each checkpoint may land alone. Write `fs` for the record's fields (`m = k + 3` of them, all
nonempty, `Turing.cfgRecord_field_ne_nil`) and `F = (fs.map List.length).sum`.

1. **The per-field round** (one private machine and its run lemma): `copyMapTM` (the constant
   copy, `cw_copy_constant`) → `skipTM` on the source → `skipTM` on the clock → `cw_leftTM` on
   the clock, by `seamCompTM`. Its run: write `e^{|f|}` at the clock head, advance the clock head
   by `|f|` (onto the next write position, the new delimiter), and move the source head to the
   next field's first cell; nothing else changes; exact time, no earlier exit, silence.
   - **The clock's blank suffix** is a hypothesis of the round, re-established at the new
     write position `p + |f|`: every clock cell from the write position on is blank (initially by
     the blank clock precondition; afterwards because the writes only append).
     `cw_copy_constant` does not supply it: outside its interval it keeps the old cells, so a
     nonblank cell at `p + |f|` stays nonblank, and `skipTM_run_ofCfg` on the clock needs the
     blank right delimiter there. Carry it through the pass and the passes explicitly.
   - **Cuts and envelopes.** `cw_copy_constant` (and `cw_clear_patch`) export only their row's
     endpoint. The seams need each phase's first-return cut (`seamCompTM_run_ofCfg`'s `hcut`)
     and its head envelope: take them from the second and third clauses of
     `copyMapTM_run_ofCfg` (`clearTM_run_ofCfg`) under the same `hw`, or extend the helper to
     export them (region (a) allows it).
2. **One pass** over the `m` fields, by induction on the fields, joining the writes by
   `wordPatch_append`: the clock tape becomes `wordPatch ct p (List.replicate F e)`.
3. **`c` passes**, with the source's rewind between passes by `skipBackTM` (back over the `m`
   fields to the record's first cell): the clock tape becomes
   `wordPatch ct p (List.replicate (c · F) e)`.
4. **The clock's rewind** to its start (back over the word to its first cell), so that the word
   is at F2's clock head.
5. **The writer's contract**: from the record at the head of tape `0` (`RecordAt d 0 fs`) and a
   blank clock tape, the all-`e` word of width `c · F` at the clock head, both heads returned,
   silently, within `C · ((joinFields fs).length + 1)` (continuation 1's recommended stub,
   `campaign/fills/b6/inputs/b6-fill-configclock/tools/home.lean.txt`, or your restatement).
6. **Then phase 2**, the target: R1-embed the writer on `{0, clock}`; seam to
   `exists_windowRunnerTM` at its entry; at `halted` and `left`, clear by `cw_clear_patch`; dispatch
   the three exits; instantiate `cw_time_bound`'s `A`/`D` and `cw_head_bound`; move the
   certification by `Turing.windowRun_stop_unique`. The clock tape is the runner's last tape; the
   ledger is continuation 1's brief's, item 4 (unchanged).
   - `cw_clear_patch`'s blank-exterior hypothesis at F2's `halted`/`left` endpoint comes from the
     writer's blank clock exterior and F2's `w'.length = w.length`; no second
     patch-normalization lemma is needed.
   - **One constant** `C` for the whole statement: it must dominate the time constant
     (`cw_time_bound`'s `A + 4c + D + 10`), the head constant (`cw_head_bound`'s `C_R · (c + 1)`)
     and the space clause at once (take their sum or maximum).
   - **Silence and space** are clauses of the target too (`∀ u ≤ t, output = d.output`, and the
     `spaceUsed` bound): prove them for the composite, through the seams and the embedding, not
     only at the endpoints.

### Phases (for a partial; ground rule 9)

The checkpoints 1–6 above. **A partial must reach at least checkpoint 1** if Lean runs. If the
join is still open, deliver checkpoint 1 with its run lemma.

## Gate guidance (binding)

- **The B6 hosts gate's minors** bind as fixed at landing
  (`campaign/gates/13-b6-hosts-statements/resolutions.md`); the bound `N ≤ configBound + 1`
  contains the extra halt-test round.
- **Route B** only on a recorded Route A obstruction (and it would need `counterLoopCfg`'s layout
  outside the `Bool` alphabet, which is private: escalate first).
- **`wordPatch_append`'s gate** (`campaign/gates/56-wordpatch-append/`): cite it as stated.

## Cited infrastructure (public and proved at the issue commit; all in `F3C2ImportProbe.lean.txt`)

Continuation 1's 60 names (the target, its runner and the window semantics; the configuration
count and the record layout; the framed rows; composition; Route B; the record facts and the
brief-inventory API), the names continuation 1's six helpers cite (`copyMapTM_run_ofCfg`,
`tapeAction`, `step_of_tapeAction_move`, `cfgRecord_length`, `joinFields_cfgRecord_length`,
`recordLength_eq`, `record_pos_lt`, `configBound_le_two_pow`, …), and `wordPatch_append`.

**Proved modulo, exactly:** none. A complete delivery has no `sorryAx` in your target.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(c) of `SpaceComplexity/WindowClock.lean`.
   List every new declaration with its role.
2. **Statement freeze** over the target and every landed public declaration.
3. **No new public declaration.** Your machines are private; list them as promotion candidates.
4. **Escalation, item by item:** on anything unprovable as stated, including a cited row that
   does not compose as the route says, stop **on that item only**, record the obstruction
   mathematically, and **continue with every item that does not depend on it**. Stopping one
   checkpoint does not stop the checkpoints before it.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Unchanged (`Build/WindowRun`, `SpaceComplexity/ConfigGraph`; `Build/StepClock`
   and its `wordPatch_append` are in the closure). No TCSlib import may be added.
7. **One proof per shared argument.** Never write a second seam, phase host, clock, R1
   reconstruction or record bookkeeping; never re-walk a row's trace or F2's proof. (Restating
   your own endpoint by an interval case split is not record bookkeeping; see Hosts.)
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public
   and private declaration counts (base: ⟨452⟩ lines; 4 public, 11 private).
9. **Continuation budget.** A partial zip states the checkpoint reached, the open declarations
   (each with a literal "Proof sketch"), and the target's axiom walk.
10. **The pinned base, and no unfolding (user, 2026-10-16).**
    - Cite only declarations public at your base, and your file's own privates.
    - **Never unfold a definition of another file**, and no definitional closure either. Read
      `wordPatch` only through `wordPatch_of_mem`, `_of_not_mem` and `wordPatch_append`, and
      `FinTM.bufferTape` only through its equations.
    - **The machine model's primitives** (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
      `Cfg.mapState`) are read through their lemmas. Unfold `step` and `Action.apply` only for a
      leaf defined in your own file. `phaseHostTM`'s table is read through `phaseHostTM_run`.
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate** (ground rule 4), naming the lemma you need.
    - **Self-check:** a seal test (a scratch copy of your module with `attribute [local
      irreducible]` on every other-file definition your proofs mention, which must still
      elaborate, with a control that fails under the seal) and an inspection of every
      `rw`/`simp`/`simpa`/`unfold` argument in your diff. Continuation 1's review lists its seal
      set (17 definitions); extend it. The frozen bridge `FinTM.configBound_le_two_pow` (before
      the home) unfolds `FinTM.configBound`; it predates rule 10, stays outside the seal and is
      not yours to change.
    - List every declaration you cite outside your file. If you cite more than the probe's list,
      add them to a copy of the probe and run it.
11. **MIG-1 compatibility.** Cite none of the six R3 canonical rows; use their framed `_ofCfg`
    forms. Cite no private declaration of another file. Keep your new privates under `cw_`.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**.
- **The population** is continuation 1's 21 files, unchanged
  (`campaign/fills/b6/inputs/b6-fill-configclock-cont2/screen-population.txt`).
- **The screen** is `scripts/copy-text-screen-v3.py`, on the repository paths.
- **The base** is `campaign/fills/b6/logs/b6-fill-configclock-cont2-screen-base.txt`: ⟨SCREEN:
  continuation 1's after-screen, 1,048 declarations and 510 pairs, plus `wordPatch_append`⟩
  (MEASURED at the base).
- **No new cross-file pair** with an owned-file declaration on one side. Nothing is
  pre-disclosed.
- **Known hazards:** `exists_fieldsCopyTM`'s route (`RecordTable`'s `rt_copyMachine`: copy,
  skip, recurse, skip back) and `rt_adjacentWrites`: your writer follows the same shape; cite the
  rows and `wordPatch_append`, do not transcribe `RecordTable`'s private proof. F2's `wr_*`/`wl_*`;
  the phase-host compositions elsewhere; the R1 reconstruction family (cite `embedEmitCfg_eq`).
- List every new in-file pair with a one-line justification. At 90% or more it is a copy: factor
  it. Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each
  pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; the cache **for your roots only** (addendum v2.3, items 2–4;
  ⟨ROOTS⟩ roots); **never `lake build`**, and never the unfiltered `lake exe cache get`. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `campaign/fills/b6/orders/b6-fill-configclock-cont2.txt` (⟨ORDER⟩
  modules: the upstream closure of your owned file and of every module downstream of it, without
  the root `TCSlib`).
- **The base sorry-warning set has ⟨SORRIES: 28⟩ entries**
  (`campaign/fills/b6/logs/b6-fill-configclock-cont2-base-sorries.txt`). Yours is the target.
- **Final checks:** `SpaceComplexity/WindowClock`: zero errors, no sorry warning (for a partial,
  exactly the open declarations'), and no other warning in anything you added; every other module
  of the order list: zero errors, sorry warnings exactly the base's minus yours; the import and
  consumer probes re-run, 0 errors.
- **Axiom prints** for the target and every new private: within
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx` for a complete delivery.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/SpaceComplexity`, 0 FAIL
  (⟨LINT⟩). No new line over 100 characters.

## Out-of-scope sorries you will see (leave every one untouched)

Everything in the base sorry set except your target (MIG-1 stage S's specs, `Build/RecordTable`'s
rows, `SpaceComplexity/Hierarchy`'s, `SpaceComplexity/Savitch`'s). If a proof seems to *need* one
of these beyond a named citation, that is an escalation, not a license.

## REPORT.md checklist

- [ ] The preflight's numbers, the roots' count and the cache fetch's (addendum v2.3).
- [ ] 1/1, or the checkpoint reached; the base hash and the ancestor check; the checkpoint zips.
- [ ] Every new declaration with its role; the writer's contract as recommended or restated; the
      status paragraph.
- [ ] The constant `c` and the ledger, step by step.
- [ ] Promotion candidates and escalations, or "none".
- [ ] Rule 10: the declarations cited outside your file, the probes re-run, the seal test with its
      control, and the inspection. Rule 11: a grep of your diff for the six R3 rows and for other
      files' private names.
- [ ] Duplication: both v3 screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints; the lint line.

## Known pitfalls at this pin (hard-won)

- `WindowExit` derives only `DecidableEq`: give a `Fintype` for a phase type containing it
  through `show Fintype WindowExit from ⟨…⟩`. `(Sigma.mk.inj h).2` is a `HEq`: use
  `eq_of_heq`. A dotted constructor of `WindowExit` in a redirect table needs its type.
- `phaseHostTM_run` gives the prefix up to `T` and the dispatch at `T + 1`; its `hguard` must hold
  strictly before `T`.
- **F2's runner takes the native input as digits** (`x.map (RecSym.digitEmb M.State T)`); its
  clock tape is `Fin.last (K + 1)` of `K + 2` tapes (`show` the goal if `K + 2` and `K + 1 + 1`
  clash).
- `RecordAt d 0 fs` includes the blank delimiters at `-1` and at `(joinFields fs).length`.
- **`cw_copy_constant`'s endpoint is an `if` on the interval, not a `wordPatch`**: restate it once
  (per field) before joining.
- **`skipTM` stops one cell past the delimiter**; `cw_leftTM` brings the clock head back onto it,
  where the next write continues the word.
- `Cfg.inputPos` starts at `1`; the writer and the clear never move the input head.
- `omega` with products and powers as atoms (`ring` first). The linter needs a literal "Proof
  sketch" before every `sorry` (partial only).
