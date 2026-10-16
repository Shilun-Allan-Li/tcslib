# Ch3–4 fill campaign — B5a, the canonizer, continuation 5: the grammar stage and the validator (`MachineFormat.exists_polyCanonizer`, by declaration in `TuringMachine/CodeSimulator.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If the check fails,
  **stop**. That commit contains:
  - **your predecessor's phase-2 delivery (PR #107, merged):**
    - the eight prescribed grammar bridges;
    - the bounded unary reader `exists_canonUnaryTM` (C1);
    - the generic record validator `exists_canonRecordTM` (C2);
    - 25 helpers, and the two open stubs `exists_canonGrammarStage` and `exists_canonDecider`;
    - its report `audits/b5a-fill-agent-reports/canon-5-REPORT.md`.
  - **MIG-1 stage S** (PR #98) and everything merged up to #107. Their names are the base's names.
  - the fill-agent environment addendum `briefs/fill-environment-addendum.md`, and the
    declaration-keyed copy-text screen v3 `audits/evidence/retrofit/copy-text-screen-v3.py`;
  - **this round's inputs** (`audits/evidence/b5a-canon-cont5/`):
    - the prescribed factoring patch `factor.patch`, with its generator;
    - the regions table;
    - the screen population;
    - the pre-ship walk probe.

    Also the order list `briefs/orders/b5a-fill-canon-cont5.txt`, the base sorry set, the screen
    base and overlay, and the pre-ship log (`audits/logs/b5a-fill-canon-cont5-*`).
- If Lean cannot start, follow `briefs/fill-environment-addendum.md` exactly.
- **Branch from exactly that commit**, not from the moving campaign tip:
  `git checkout -b fill/b5a-canon-cont5 @ANCESTOR@`. Record the base hash in `REPORT.md`. Never
  rebase, merge or cherry-pick anything into your branch.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-b5a-canon-cont5.zip`. It
  contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle;
  - the final sweep log and the axiom log;
  - the note-50 file and its log;
  - both screen outputs, and `SHA256SUMS`.

## Base, line numbers and what is in flight

- **Your base's Lean content is the campaign tip after #107** (`6354471a`): the canonizer
  continuation 4, merged. The inputs commit adds no Lean change. Every probe and measurement below
  was run there, against the olean snapshot of #107's replay.
- **Your first commit applies the prescribed factoring patch** (below). **Lines in this brief are
  those of the patched tree** unless marked "issue tree". The patch moves every line after
  `canonPatchWord` by +5.
- **In flight, merging after your base and invisible to it:**
  - **#108, the §13d G2 fill**: `Build/Catalog.lean` and `Build/Zone.lean`, proofs only. It
    makes no statement change, renames no public, and adds no public.
  - MIG-1's batches F-A to F-D. F-D retires the six R3 canonical rows and edits the one
    consumer in your file (ground rule 11).

  Cite nothing these add.

## Parallel batches this round

None in `CodeSimulator.lean`. H1's continuation (`exists_uniformSimulator`) is briefed later. A
parallel change is invisible to your base and your screen.

## What this is

**The canonizer's sixth continuation: phases 3–5 of the cont3 route, plus one prescribed
factoring edit.**
- Your target is `MachineFormat.exists_polyCanonizer`, a polynomial-time machine computing
  `F.serialize (F.decode α)`.
- **It is already proved modulo exactly two private stubs**, `exists_canonGrammarStage` and
  `exists_canonDecider`. The landed glue covers the rest, over the proved strip machine and the
  constant fallback.
- **The two components the stubs need are proved:** C1 (`exists_canonUnaryTM`) and C2
  (`exists_canonRecordTM`), with the contracts in `canon-5-REPORT.md` §"Construction and promotion
  contracts".
- When both stubs are proved the canonizer is complete. With H1, the two-tape code scheme, the
  `EXPCOM` cluster and Baker–Gill–Solovay then lose their last canonizer admission.

**The user's two rules from cont3 stay in force** (2026-10-14):
- the `computesFunInTime_cond` decomposition (validator, strip machine, constant fallback) is the
  route;
- a partial may leave named private stubs open, checked by an **axiom walk**: `sorryAx` reaches
  the headline only through the named open stubs.

**What you build:**
- the grammar stage, from C1, C2, the nested public counter loops and the suffix check;
- the validator that joins the frozen parse front end to it;
- then the prescribed note 50, which already elaborates and runs unchanged on the complete
  canonizer (phase 5).

**Read first:**
- the previous report (`canon-5-REPORT.md`), sections "Construction and promotion contracts" and
  "Open stubs and next continuation";
- the cont4 brief `briefs/b5a-fill-canon-cont4.md`. Its route C3–C5 and B, its gate guidance and
  its pitfalls bind where this brief does not replace them;
- `CodeSimulator.lean` lines 1–4637;
- `Build/CounterLoop.lean`: `counterLoopTM`, its `_run_done`/`_run_escape` contracts,
  `counterLoop_time_le`, `counterOverhead_le_of_le`, `counterValue`, `counterWord`.

**Pre-ship check** (maintainer, at the base, against `oleans-lcanon4`, #107's replay;
`audits/logs/b5a-fill-canon-cont5-preship.log`):
- **The factoring patch** (`audits/evidence/b5a-canon-cont5/factor.patch`; generator
  `tools/mkfactor.py`): the patched `CodeSimulator.lean` gives 0 errors, 0 non-sorry warnings,
  and exactly 3 sorry warnings (the two stubs and `exists_uniformSimulator`).
  `git apply --check` passes at the base.
- **The import probe** `audits/evidence/b5a-canon-cont4/CanonCont4ImportProbe.lean.txt`, whose
  130 `#check`s cover every public declaration this brief cites: 0 errors, 0 warnings at the base.
  This brief cites no public declaration that cont4 did not. **Re-run it after your delivery.**
- **Note 50** (`audits/evidence/b5a-canon-cont4/CanonNote50.lean.txt`, prescribed): 0 errors, 0
  warnings. `note50_cases` prints `sorryAx` today. The pre-ship walk
  (`audits/evidence/b5a-canon-cont5/CanonNote50Walk.lean.txt`: the note-50 file plus the read-only
  `#sorry_sources` walk of the S1210 probe) shows that both it and the headline reach `sorryAx`
  through `exists_canonDecider` and `exists_canonGrammarStage` only.
- **The inherited probes**, each with 0 errors:
  - `audits/evidence/b5a-canon-cont3/CanonCont3ImportProbe.lean.txt`;
  - `audits/evidence/wave1-statements/B5aStatementsProbe.lean.txt`, with its one probe-local
    admission;
  - `audits/evidence/b5a/B5aContPreShip.lean.txt`;
  - `audits/evidence/wave1-statements/S1210StatementsProbe.lean.txt`, with its one probe-local
    admission. Its census still detects its control `Complexity.EXP_subset_POracle_EXPCOM`.

## The prescribed factoring edit (do this first)

**User decision (2026-10-15):** factor continuation 4's one in-file pair in this continuation.
In that pair, the frozen strip machine `exists_canonStripTM` reproduces the boundary split of
`canonPatchWord` (134/229, 59%: a `0 ≤ z`, then `z < length`, case split on buffered words).
`factor.patch` does exactly three things:
1. It adds `canonPatchWord_le` before the strip machine's docstring: patching a buffered word by
   a word at least as long, over the longer word's interval, gives the longer word's buffer.
2. It re-points the strip machine's copy block at it, for the blank tape (`[]`).
3. It re-proves `canonPatchWord` as its equal-width instance.

Both statements are byte-identical. **Apply it as your first commit** (`git apply
audits/evidence/b5a-canon-cont5/factor.patch`), unchanged. Its three hunks are maintainer-owned:
do not edit them further. If it does not apply or does not elaborate at your base, that is an
escalation (ground rule 4). The pre-ship overlay screen shows the pair gone and no new pair.

## Owned region and targets (modify these and nothing else)

| # | File:line (patched tree) | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `CodeSimulator.lean:4448` | `exists_canonGrammarStage` (frozen statement) | C3–C5 | C1, C2, the bridges, the public counter loop |
| 2 | `CodeSimulator.lean:4475` | `exists_canonDecider` (frozen statement) | B | `exists_canonParseFront`, target 1, `canonGrammar_verdict` |
| 3 | `CodeSimulator.lean:4592` | `Turing.MachineFormat.exists_polyCanonizer` | the landed glue (frozen) | targets 1–2 |

**The two stub statements are frozen verbatim**, as landed by #96 and quoted in the cont4 brief.
The table `audits/evidence/b5a-canon-cont5/codesimulator-regions.tsv` (issue tree) lists the
file's 149 declarations with their regions:
- 13 in the frozen layout and formats;
- 74 inherited from the earlier rounds;
- 16 from #96, of them `exists_canonStripTM` frozen except the patch;
- 35 from #107, of them `canonPatchWord` frozen except the patch;
- the two stubs and the headline;
- four D4 clock declarations;
- four in H1.

Everything there is frozen except the parts of ground rule 1.

- **H1's region is off-limits:** `h1HostedVerdictTM`, `h1HostedVerdict_effect`,
  `h1HostedVerdict_accepts` and `exists_uniformSimulator` (lines 4694–4891).
- **Frozen, neither batch's:**
  - lines 1–189 (the module header, the layout, `MachineFormat`, the one-tape format);
  - the D4 section 4639–4693 (its section comment, `section StepBlockClients`/`open StepBlock`
    and the four clock declarations);
  - targets 3–8 in `Codes2Tape.lean` and `EXPCOM.lean`.
- **Not yours:** every other file.

### Home

All new declarations live in the **home**, the blank line 4435. It sits between the last line of
`exists_canonRecordTM` (4434) and `exists_canonGrammarStage`'s docstring (4436), inside
`namespace MachineFormat`. Each goes after what it uses and before its first consumer.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **Compose by the public combinators**, as in cont4:
  - R2 seams: `seamCompTM`, `seamReleaseTM`;
  - the phase host: `phaseHostTM`;
  - R1 embedding: `embedEmitTM`, `embedEmitCfg_eq`;
  - the counter loop: `counterLoopTM`, `counterLoopTM_run_done`, `counterLoopTM_run_escape`, or
    the contract-level `RoundContract.counterLoopDone_traj`/`counterLoopEscape_traj`;
  - the framed catalog rows: `copyTM_run_ofCfg`, `clearTM_run_ofCfg`, `writeConstTM_run_ofCfg`,
    `incrementTM_run_succ_ofCfg`.

  Do not write a hand controller for a phase that a public row provides. Never write a second
  loop, seam or embedding transport.
- **Cite C1 and C2**, which are proved and private in your file. Never re-walk their internals.
  Their inherited leaves and run lemmas are the models for any new leaf:
  - `canonCellTM`/`canonCell_step`, `canonPairsTM`/`canonPairs_run`, `canonTagTM`/`canonTag_step`;
  - #96's `canonTrimTM`/`canonTrim_run`;
  - the guard's `guardBlockTM` family.
- **Leaves you may write.** No public row provides these, and C1/C2's leaves do not fit:
  - the native all-`true` suffix scan;
  - a one-step emitting halt.

  Each is a small finite controller.
- **Promotion candidates** (list each with its contract in `REPORT.md`; notes only, not this
  round): any generic repetition loop you build, C1, C2 and the strip machine.

### The route (binding where it names a row)

**C3–C5. The grammar stage** (`exists_canonGrammarStage`). Tape `header` holds `bits`, every
other tape is blank, and the native head is at the remainder. Decide
`(canonGrammar F.k n rest).isSome`, where `n = codeBitsNat bits`. The route is cont4's, with C1
and C2 now proved:
1. **The initial state.** Run C1 against the header (bound `counterValue bits = n`, by
   `Turing.foldr_bit_eq_ofDigits`), embedded on `{header, scratch}`.
2. **The table** (`canonSkipTable_eq`) has `n + 1` states of `3^(k+1)` records each.
   - **The inner loop:** a public counter loop of `3^(k+1)` rounds with C2 as its body. Write its
     counter word with `writeConstTM_run_ofCfg` at the start of each state block.
   - **The outer loop:** a public counter loop over the states. A header copy as its counter gives
     `n` rounds, so either run one leading state block before the loop
     (`codeSkipRepeat f (n + 1) xs = (f xs).bind (codeSkipRepeat f n)` holds by `rfl`), or install
     `n + 1` with `incrementTM_run_succ_ofCfg` on a copy with a spare `false`.
   - A body failure is the loop's escape.
   - **Prove the generic link once:** a counter loop whose body decides a skipper `r` decides
     `codeSkipRepeat r (counterValue c)`, failing fast. `canonSkipRepeat_mul` and
     `canonSkipTable_eq` are the bridges.
   - Do not copy `MathlibBridge.codeSkipRepeat_iter`, the H1 loop proofs in
     `Build/StepBlockLoop.lean`, or C1's countdown (`canonUnaryLoop`, `canonTrueOrbit`). If C1's
     loop lemma fits a step of the link, cite it.
3. **The suffix.** Scan from the table's end to the right blank: all `true` accepts, any `false`
   rejects.
4. **The ledger, fail-fast included.**
   - Every successful record consumes at least `4k + 5` cells (`codeActionK_length`,
     `skipTable_consumes`, `canonSkipFields_cells`), and every record fails on a blank. So at most
     `|x| + 1` records run before a failure or the table's end.
   - Each record is charged `O(|x| + |bits|)` by C2's bound, and `|bits| ≤ |x|`
     (`length_pairEncode` at the decoded pair).
   - The counter loops add `counterOverhead`, at most `4r + 2|w|` per loop
     (`counterOverhead_le_of_le`).
   - The total is quadratic in `|x| + 1` and independent of the value `n`: this is the stage's
     `a * (x.length + 1) ^ a`.
   - The guard's hypotheses (canonicality, `canonGuardBlock F * (n + 1) ≤ |rest|`) are available
     if a bound needs them.

**B. The validator** (`exists_canonDecider`), as in cont4.
- Embed the frozen front end `exists_canonParseFront F` and the grammar stage in one bank:
  - the front end on its own `C.k` tapes;
  - the stage's `header` tape on the front end's tape `0`;
  - its other tapes on fresh tapes beyond `C.k`, blank by the front end's embedding frame
    (`canonBlankLift`, `canonEmbedEq` and the public `embedEmitCfg_eq`).
- Dispatch the front end's `exit true` to the stage's entry by a public seam.
- Send `exit false` and both stage exits to a one-step leaf that emits the bit and halts (one
  `phaseHostTM` dispatch).
- **The ready configuration is not a `Cfg.ofWords` configuration.** Its native head is at the
  remainder (`2|bits| + 3`) and its tape `1` holds the guard's residue; the stage's contract needs
  neither.
- **Laws and ledger:** the verdict laws are the front end's reject clause and
  `canonGrammar_verdict`. The ledger is the front end's linear bound, plus the stage's, plus the
  dispatches.
- Remove the stub's composition comment and placeholder `obtain`s when you prove it.

**Phase 5. Note 50** (prescribed; user decision 2026-10-14).
- Copy `audits/evidence/b5a-canon-cont4/CanonNote50.lean.txt` unchanged to your zip's
  `evidence/CanonNote50.lean.txt`.
- Elaborate it with `scripts/lean_check_tree.sh` (0 errors), and quote its last line. For a
  complete delivery, `#print axioms note50_cases` shows no `sorryAx`.
- A partial says "pending" and quotes the print.

### Phases (for a partial; ground rule 9)

The factoring patch is in every delivery. After it, stop, if you must, at the end of a phase, and
say which:
3. **The grammar stage** proved (`exists_canonGrammarStage` closed).
4. **The validator** proved (`exists_canonDecider` closed). The headline is then complete.
5. **Note 50** elaborated on the complete canonizer.

A partial may leave only the open frozen stubs. **Add no new admission:** any recommended
component you state for yourself goes in only once it is proved. The freeze check for a partial
is the **axiom walk**: `sorryAx` reaches the headline only through the open frozen stubs.

## Gate guidance (binding)

As in cont4:
- minor 5 (zero guard);
- note 47 (`tableBitsK` stays in the item-8 residual family);
- note 50 (phase 5; permanent; no `#eval`, `native_decide` or `IO`);
- round-2 note 17 (keep the S1210 probe's detecting control);
- the time-zero cut: `exists_canonHeaderCall` and `exists_installCallTM` give the positive-time
  cut only; `canonStrictInstall` and the release adapter cover coincident anchors;
- F7-1(c): your leaves and `StepBlock.recordTM` walk a record's fields; do not copy the step
  block's reader or its trace.

## Cited infrastructure (public and proved at the issue commit)

Exactly cont4's list ("Cited infrastructure" there), all of it resolving in
`CanonCont4ImportProbe.lean.txt` at your base. In your file you also cite:
- C1, C2 and their contracts;
- the eight bridges;
- the inherited front end (`exists_canonParseFront`, `canonBlankLift`, `canonEmbedEq`).

**Proved modulo, exactly:** none. A complete delivery has no `sorryAx` in your target.

## Ground rules (binding)

1. **File ownership, by declaration.** In `TuringMachine/CodeSimulator.lean`, and nowhere else,
   you own exactly these regions (lines at the patched tree):
   - **(a) the home**, the blank line 4435: your own `private` declarations. `private` only, and no
     `section`, `open` or `variable` that leaks past it.
   - **(b) `exists_canonGrammarStage`'s body**, the `sorry` on line 4463, and a flagged **"Fill
     appendix"** paragraph appended to its docstring (4436–4447). The statement (4448–4462) is
     frozen.
   - **(c) `exists_canonDecider`'s body**, lines 4480–4487, and a flagged appendix paragraph in
     its docstring (4465–4474). The statement (4475–4479) is frozen.
   - **(d) `exists_polyCanonizer`'s docstring**, lines 4489–4591: append a flagged **"Fill
     appendix (canonizer continuation 5)"** paragraph before the closing ` -/` (at the end of
     line 4591). The existing text does not change. The statement and the glue (4592–4637) are
     frozen.
   - **(e) the factoring patch**, applied unchanged (above).

   **Not yours:** every other line, including:
   - the module header and every section heading;
   - every existing declaration, #96's and #107's deliveries;
   - H1's region.

   The maintainer updates the module header and the status text in `Codes2Tape.lean`/`EXPCOM.lean`
   at integration; report any text that reads wrong. List every new declaration with its role.
2. **Statement freeze** over every landed declaration and both stub statements: no renames,
   re-signatures, restatements or attribution edits.
3. **Status text.** Only the headline's "(spec, fill pending — batch B5a)" tag may change, to
   "proved", and only for a complete delivery; flag it. No new public declaration.
4. **Escalation** on anything unprovable as stated, including a cited row that does not compose
   as the route says, or a factoring patch that does not apply: stop on that item, record the
   obstruction, and continue with the rest.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Unchanged. No TCSlib import may be added. A Mathlib import only if a needed lemma
   requires it; flag it.
7. **One proof per shared argument.** Never re-walk a landed contract. Never write a second host,
   loop, trace or layout lemma for something already public or already proved in your region,
   in particular C1, C2, their leaves and run lemmas, #96's leaf and `canonBlankLift`/
   `canonEmbedEq`.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public
   and private declaration counts. The patched base has 4,894 lines and 150 declarations, 11
   public and 139 private; the issue tree has 4,889 lines and 149 declarations.
9. **Continuation budget.** A partial zip states the phase reached, the open stubs (each with a
   literal "Proof sketch"), and the headline's axiom walk. A partial is expected and fine; an
   unreported gap is not.
10. **D4 is complete:** no further deletions or moves.
11. **MIG-1 compatibility.** Keep `canonPreserveInstall` byte-identical (line 1241; F-D rewrites
    its `copyTM_run` citation, line 1279, after you). Cite none of the six R3 rows anew
    (`copyTM_run`, `transferTM_run`, `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`,
    `incrementTM_run_overflow`); use their framed `_ofCfg` forms.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**
(`audits/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**).
- **The population** is cont4's 45 files
  (`audits/evidence/b5a-canon-cont5/b5a-canon-cont5-screen-population.txt`, the same list).
- **The screen** is the declaration-keyed `audits/evidence/retrofit/copy-text-screen-v3.py`, run
  on the repository paths.
- **The base**, at the issue tree, is `audits/logs/b5a-fill-canon-cont5-screen-base.txt`:
  **2,388 declarations, 2,648 pairs, 834,815 characters** (MEASURED with v3; about 28 minutes).
- **The patched tree** (the overlay) is `audits/logs/b5a-fill-canon-cont5-screen-overlay.txt`:
  **2,389 declarations, 2,647 pairs, 834,681 characters**. The patch removes the pair `exists_canonStripTM` ← `canonPatchWord` and adds
  none.
- Your "before" run is on the patched tree, after your first commit.

```sh
P=audits/evidence/b5a-canon-cont5
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/b5a-canon-cont5-screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/b5a-canon-cont5-screen-population.txt) > /tmp/screen-after.txt
```

- **No new cross-file pair** with an owned-file declaration on one side. Nothing is
  pre-disclosed.
- **Recorded, add nothing to them:**
  - `scan_grammar_guard`/`canonScan_all` (55%, cont3);
  - the frozen `canonOffset_spec` reproducing `Turing.length_bits_le_self` (100%; backlog);
  - the earlier canonizer in-file pairs;
  - the uniform-code mirror pair (75%, CH34-D3);
  - item 8's writer pairs.
- **Known hazards.** A proof that reproduces one of the following at 90% or more must be
  factored (parameterize, or cite):
  - C1's countdown and C2's leaf;
  - the inherited native leaves (`guardBlockTM` and its family, `canonCellTM`, `canonPairsTM`,
    `canonTagTM`, `canonTrimTM` and their run lemmas);
  - `MathlibBridge.codeSkipRepeat_iter` and the chapter-1 parser;
  - the H1 counter-loop proofs in `Build/StepBlockLoop.lean`;
  - the R1 reconstruction family (cite `canonEmbedEq`, `canonBlankLift`, `embedEmitCfg_eq`).

  **Your predecessor's lesson:** repeated one-step run unfolding created two cross-file pairs
  (against `MultiTapeTM.liftSymbols_runFrom` and `timedFrame_run`). The public
  `step_of_inputMoveAction` already supplies each one-step result.
- List every new in-file pair with a one-line justification. At 90% or more it is a copy: factor
  it. Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each
  pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/b5a-fill-canon-cont5.txt` (**100 modules**: the upstream
  closure of your owned file and of every module downstream of it). Since cont4 it adds
  `Build/StepBlockForward`, `Build/ZoneTape`, `Build/ZoneRebalance` and `UniversalK`:

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/b5a-fill-canon-cont5.txt )
  ```

  **The base sorry-warning set has 46 entries** (`audits/logs/b5a-fill-canon-cont5-base-sorries.txt`,
  one entry per declaration). Yours are `CodeSimulator`'s first two of three: the two stubs.
  Record the base list by name first, and report any difference.
- **Final checks:**
  1. `CodeSimulator`: zero errors, and exactly one sorry warning, `exists_uniformSimulator` (plus,
     for a partial, each open frozen stub).
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's.
     For a complete delivery that is **44** in all, counting `CodeSimulator`'s one.
  3. Re-run `CanonCont4ImportProbe.lean.txt`, `CanonCont3ImportProbe.lean.txt`,
     `B5aStatementsProbe.lean.txt` and `B5aContPreShip.lean.txt`: 0 errors.
  4. Re-run `S1210StatementsProbe.lean.txt`: 0 errors, its census still detecting its probe-local
     admission.
  5. Elaborate the note-50 file: 0 errors; its axiom print (phase 5).
- **Axiom prints**, within `[propext, Classical.choice, Quot.sound]`, for:
  - your target;
  - every new private and `canonPatchWord_le`, in an in-module probe, as the previous report did;
  - targets 3–8 (`Turing.exists_uniformMachineCode2`, `Turing.exists_uniformMachineCode`,
    `Complexity.EXP_subset_POracle_EXPCOM`, `Complexity.POracle_EXPCOM_eq_EXP`,
    `Complexity.NPOracle_EXPCOM_eq_EXP`, `Complexity.POracle_EXPCOM_eq_NPOracle_EXPCOM`) and
    `Complexity.baker_gill_solovay`.

  For a complete delivery your target has no `sorryAx`, and the others have it only through
  `exists_uniformSimulator`. For a partial, the headline's admission walk names exactly the open
  stubs.
- **Lint:** `python3 scripts/campaign_style_lint.py` over `TCSlib/Complexity/TuringMachine` and
  `TCSlib/Complexity/Diagonalization` (two runs), 0 FAIL. Add no line over 100 characters and no
  Lean linter warning in your region; the patched base file has none.

## Out-of-scope sorries you will see (leave every one untouched)

The base sorry set, apart from your two stubs:
- `TuringMachine/CodeSimulator`: `exists_uniformSimulator` (H1, a later brief);
- the 43 others listed in `audits/logs/b5a-fill-canon-cont5-base-sorries.txt`. These are:
  - MIG-1 stage S's sorried specs (`Simulation`, `Composition`, `Build/Wrappers`, `Build/Loop`,
    `Encoding`, `ClassP/TimeConstructible`, `Build/Primitives`);
  - `Build/RecordTable`, `Diagonalization/NTimeHierarchy`, `Build/NDHost`;
  - `Build/StepBlockForward`, `Build/InputWindow`, `Build/InputDevice`;
  - `NDCodeSimulator`, `UniversalK`;
  - the §13d G2–G4 statements (`Build/Catalog`'s two mapped framed rows, `Build/Zone`'s
    `zoneCascadeRight_home`, `Build/ZoneRebalance`'s two rows). #108 proves the first three
    after your base; that is invisible to you.

If a proof seems to *need* one of these beyond a named citation, that is an escalation, not a
license.

## REPORT.md checklist

- [ ] The phase reached (3–5), the base hash and the ancestor check.
- [ ] The factoring patch applied unchanged as the first commit (`git apply --check` and the
      commit hash).
- [ ] Every new declaration with its role; every flagged appendix and status update.
- [ ] The generic components' contracts (any repetition loop), as promotion candidates.
- [ ] Requested shared lemmas and escalations, or "none".
- [ ] Rule 11: `canonPreserveInstall` unchanged; no new citation of the six R3 rows (a grep of
      your diff).
- [ ] Duplication: both v3 screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the re-run probes; every axiom print; the headline's
      admission walk; the lint lines. The diff touches only your owned regions.
- [ ] Note 50: the file's elaboration and its axiom print (or "pending").

## Known pitfalls at this pin (hard-won)

All of cont4's ("Known pitfalls" there) still hold. In particular:
- `Cfg.inputPos` starts at `1`, so the suffix at position `p` is `x.drop (p - 1)`.
- The front end's ready configuration is not `Cfg.ofWords`.
- `counterLoopTM M` has `k + 1` tapes with the counter at `Fin.last k`. On `done` the counter
  interval is all `true`; on `escape` it holds `counterWord w r`, so clear or re-write it before
  reuse.
- `codeSkipRepeat r (n + 1) xs = (r xs).bind (codeSkipRepeat r n)` holds by `rfl`, but the nested
  `codeSkipTableK` does not (use `canonSkipTable_eq`).
- `seamCompTM_firstReturn_ofCfg` needs the callee's cut at `t = 0` as well.
- The inherited canonizer lemmas take `(F : MachineFormat)` explicitly.

**New from cont4:**
- C1 and C2 run on a two-tape bank with the bound at index `0`.
- C2's coefficient is `16 + 4k + 9`, linear in `|x| + |w| + 1`.
- Both restore every work tape and head and leave the native head at the accepted suffix, so a
  counter-loop body can be C2 itself, without a wrapper.
- The one-step unfolding lesson above: use `step_of_inputMoveAction`/`step_of_tapeAction_move`,
  not `runFrom_succ_eq_step` chains.
