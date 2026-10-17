# Ch3–4 fill campaign — B5a, the canonizer, continuation 6: the grammar stage (`exists_canonGrammarStage`, by declaration in `TuringMachine/CodeSimulator.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If the check fails,
  **stop**. That commit contains:
  - **your predecessor's delivery (PR #113, merged).** It holds:
    - the prescribed factoring (`canonPatchWord_le`);
    - **`exists_canonDecider` proved modulo your stub**;
    - the two permitted leaves: `canonSuffixTM`/`canonSuffix_run`, the native all-`true` suffix
      scan (unused so far; yours to use), and `canonHaltTM`/`canonHalt_run`;
    - the three-port emit adapter `canonEmitVerdict`.

    Its review is `audits/evidence/b5a-canon-cont5/delivery-review.md`.
  - **the API PRs** (the user's "Everything" rule, 2026-10-16: every definition your route reads
    has a published lemma): the specification API (PR #112), the core API (PR #116) and the
    brief-inventory API (PR #118). For this brief #118 gives `counterLoopBody`'s fields (the
    round-contract counter loop's trajectories), `stateWord_eq`, `decFixed`'s cases, and the
    contract layer's predicates as `_iff`s;
  - the fill-agent environment addendum `briefs/fill-environment-addendum.md`, and the
    declaration-keyed copy-text screen v3 `audits/evidence/retrofit/copy-text-screen-v3.py`;
  - **this round's inputs** (`audits/evidence/b5a-canon-cont6/`): the import probe and the screen
    population. Also the order list `briefs/orders/b5a-fill-canon-cont6.txt`, **which now includes
    `ClassNP/TMSAT`** (cont5's review found it missing: `B5aStatementsProbe` imports it), the base
    sorry set, the screen base and the pre-ship log (`audits/logs/b5a-fill-canon-cont6-*`).
- If Lean cannot start, follow `briefs/fill-environment-addendum.md` exactly.
- **Branch from exactly that commit**, not from the moving campaign tip:
  `git checkout -b fill/b5a-canon-cont6 @ANCESTOR@`. Record the base hash in `REPORT.md`. Never
  rebase, merge or cherry-pick anything into your branch.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-b5a-canon-cont6.zip`. It
  contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle;
  - the final sweep log and the axiom log;
  - the note-50 file and its log;
  - both screen outputs, and `SHA256SUMS`.

## Base, line numbers and what is in flight

- **Your base's Lean content is the campaign tip after #118** (⟨BASE-LEAN⟩). The inputs commit
  adds no Lean change. Lines in this brief are those of that tree. `CodeSimulator.lean` is #113's
  (5,271 lines; 12 public, 144 private). Every probe and measurement below was run there, against
  the olean snapshot of #118's replays (`oleans-lbapi2`).
- **In flight, merging after your base and invisible to it:**
  - U2-S (`UniversalK`), B6 F5 (`Build/InputDevice`), the B6 F3 continuation
    (`SpaceComplexity/WindowClock`), G4's continuation (`Build/ZoneRebalance`);
  - MIG-12 (`Build/CfgRecord`) if issued;
  - MIG-1's batches F-A to F-D. F-D retires the six R3 canonical rows and edits the one consumer
    in your file (ground rule 11).

  Cite nothing these add.

## Parallel batches this round

None in `CodeSimulator.lean`. H1's continuation (`exists_uniformSimulator`) is briefed later. A
parallel change is invisible to your base and your screen.

## What this is

**The canonizer's last open admission.** `MachineFormat.exists_polyCanonizer`, a polynomial-time
machine computing `F.serialize (F.decode α)`, is proved modulo exactly one private stub,
**`exists_canonGrammarStage`** (line 4646). Your target is that stub, and then note 50 on the
complete canonizer. With H1, the two-tape code scheme, the `EXPCOM` cluster and
Baker–Gill–Solovay then lose their last canonizer admission.

**User ruling on cont5's escalation E1 (2026-10-16): the adapter is authorized.**
- C2 (`exists_canonRecordTM`) cannot be a counter-loop body directly: it stops at a separate,
  stationary `exit true`, while `counterLoopTM` needs each round to start and end at one anchor.
  The cont5 brief's pitfall said otherwise; it is withdrawn.
- **Use a phase-host adapter with a fresh anchor:**
  - a fresh state `a` dispatches to C2's entry;
  - C2's `exit true` returns to `a`;
  - C2's `exit false` goes to a separate escape.

  It is a composition over the public `phaseHostTM` (two dispatch steps per record), **not a new
  host**.
- **State and prove its first-return contract once**, as a private lemma: from `a`, positive
  time, the interior avoids both `a` and the escape (the anchor is fresh, so C2's internal visits
  to its own entry do not count), the endpoint is `a` or the escape, and the record's ledger is
  C2's plus two.

**The user's two rules from cont3 stay in force** (2026-10-14):
- the `computesFunInTime_cond` decomposition (validator, strip machine, constant fallback) is the
  route, and it is landed;
- a partial may leave the named private stub open, checked by an **axiom walk**: `sorryAx`
  reaches the headline only through `exists_canonGrammarStage`.

**Read first:**
- cont5's review (`audits/evidence/b5a-canon-cont5/delivery-review.md`), in particular its E1
  assessment;
- the cont5 brief `briefs/b5a-fill-canon-cont5.md` and the cont4 brief
  `briefs/b5a-fill-canon-cont4.md`. Their route C3–C5, gate guidance and pitfalls bind where this
  brief does not replace them;
- the C1 and C2 contracts (`audits/b5a-fill-agent-reports/canon-5-REPORT.md`, "Construction and
  promotion contracts");
- `CodeSimulator.lean` lines 1–4661;
- `Build/CounterLoop.lean`: `counterLoopTM`, its `_run_done`/`_run_escape` contracts,
  `counterLoop_time_le`, `counterOverhead_le_of_le`, `counterValue`, `counterWord`,
  `RoundContract.counterLoopDone`/`counterLoopEscape` with their `_traj` theorems and their field
  equations (`_pre`, `_time`, `_post`, `_lo`, `_hi`; #118's round 2), and `counterLoopBody`'s
  field equations;
- `CodeParser.lean`: `codeSkipRepeat` with `codeSkipRepeat_zero` and `codeSkipRepeat_succ` (#118's
  round 2), the repetition's two cases;
- `Build/Seam.lean`: `phaseHostTM` and `phaseHostTM_run`, the adapter's host.

**Pre-ship check** (maintainer, at the base, against `oleans-lbapi2`;
`audits/logs/b5a-fill-canon-cont6-preship.log`):
- **`CodeSimulator.lean` at the base** elaborates with 0 errors and exactly 2 sorry warnings: your
  stub and `exists_uniformSimulator`.
- **The import probe** `audits/evidence/b5a-canon-cont6/CanonCont6ImportProbe.lean.txt`: cont4's
  130 `#check`s, #118's 14 and its round 2's 12, every public declaration this brief cites. 0 errors, 0 warnings.
  **Re-run it after your delivery.**
- **Note 50** (`audits/evidence/b5a-canon-cont4/CanonNote50.lean.txt`, prescribed): 0 errors,
  0 warnings. `note50_cases` prints `sorryAx` today. The pre-ship walk
  (`audits/evidence/b5a-canon-cont5/CanonNote50Walk.lean.txt`) shows that it reaches `sorryAx`
  through `exists_canonGrammarStage` only.
- **The inherited probes**, each with 0 errors:
  - `audits/evidence/b5a-canon-cont3/CanonCont3ImportProbe.lean.txt`;
  - `audits/evidence/wave1-statements/B5aStatementsProbe.lean.txt`, with its one probe-local
    admission;
  - `audits/evidence/b5a/B5aContPreShip.lean.txt`;
  - `audits/evidence/wave1-statements/S1210StatementsProbe.lean.txt`, with its one probe-local
    admission. Its census still detects its control `Complexity.EXP_subset_POracle_EXPCOM`.

## Owned region and target (modify these and nothing else)

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `CodeSimulator.lean:4646` | `exists_canonGrammarStage` (frozen statement) | C3–C5, with the adapter | C1, C2, the adapter, the bridges, the public counter loop, the suffix leaf |
| 2 | `CodeSimulator.lean:4969` | `Turing.MachineFormat.exists_polyCanonizer` | the landed glue (frozen) | target 1 |

**The stub's statement is frozen verbatim**, as landed by #96 and quoted in the cont4 brief.

### Home

All new declarations live in the **home**, the blank line 4626. It sits between the last line of
`canonEmitVerdict` (4625) and `exists_canonGrammarStage`'s docstring (4627), inside
`namespace MachineFormat`. Each goes after what it uses and before its first consumer.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **Compose by the public combinators**, as in cont4 and cont5:
  - R2 seams: `seamCompTM`, `seamReleaseTM`;
  - the phase host: `phaseHostTM`, `phaseHostTM_run` (the adapter's host);
  - R1 embedding: `embedEmitTM`, `embedEmitCfg_eq`;
  - the counter loop: `counterLoopTM`, `counterLoopTM_run_done`, `counterLoopTM_run_escape`, or
    the contract-level `RoundContract.counterLoopDone`/`counterLoopEscape`, read through their
    field equations and `_traj` theorems and `counterLoopBody`'s field equations (#118);
  - the framed catalog rows: `copyTM_run_ofCfg`, `clearTM_run_ofCfg`, `writeConstTM_run_ofCfg`,
    `incrementTM_run_succ_ofCfg`.

  Do not write a hand controller for a phase that a public row provides. Never write a second
  loop, seam or embedding transport.
- **Cite C1, C2 and #113's leaves**, which are proved and private in your file. Never re-walk
  their internals:
  - C1 `exists_canonUnaryTM`, C2 `exists_canonRecordTM`;
  - `canonSuffixTM`/`canonSuffix_run` (the suffix scan), `canonHaltTM`/`canonHalt_run`,
    `canonEmitVerdict`;
  - the inherited leaves as models for any new one (`canonCellTM`/`canonCell_step`,
    `canonPairsTM`/`canonPairs_run`, `canonTagTM`/`canonTag_step`, #96's
    `canonTrimTM`/`canonTrim_run`, the guard's `guardBlockTM` family).
- **Leaves you may write.** None is expected: the adapter is a `phaseHostTM` composition, and the
  suffix scan and the emitting halt are landed. A further leaf is an escalation.
- **Promotion candidates** (list each with its contract in `REPORT.md`; notes only, not this
  round): the adapter (a generic "body with a separate success exit, as a round" combinator), any
  repetition loop you build, C1, C2 and the strip machine.

### The route (binding where it names a row)

**C3–C5. The grammar stage** (`exists_canonGrammarStage`). Tape `header` holds `bits`, every
other tape is blank, and the native head is at the remainder. Decide
`(canonGrammar F.k n rest).isSome`, where `n = codeBitsNat bits`. The route is cont5's, with these
changes:
1. **The initial state.** Run C1 against the header (bound `counterValue bits = n`, by
   `Turing.foldr_bit_eq_ofDigits`), embedded on `{header, scratch}`.
2. **The table** (`canonSkipTable_eq`) has `n + 1` states of `3^(k+1)` records each.
   - **The adapter** around C2 (above), with its first-return contract proved once.
   - **The inner loop:** a public counter loop of `3^(k+1)` rounds with **the adapter** as its
     body. Write its counter word with `writeConstTM_run_ofCfg` at the start of each state block.
   - **The outer loop:** a public counter loop over the states. A header copy as its counter gives
     `n` rounds, so either run one leading state block before the loop
     (`codeSkipRepeat_succ`: `codeSkipRepeat f (n + 1) xs = (f xs).bind (codeSkipRepeat f n)`), or install
     `n + 1` with `incrementTM_run_succ_ofCfg` on a copy with a spare `false`.
   - A body failure is the loop's escape.
   - **Prove the generic link once, over the adapter's contract:** a counter loop whose body
     decides a skipper `r` decides `codeSkipRepeat r (counterValue c)`, failing fast. Its two
     cases are `codeSkipRepeat_zero` and `codeSkipRepeat_succ`; `canonSkipRepeat_mul` and
     `canonSkipTable_eq` are the bridges.
   - Do not copy `MathlibBridge.codeSkipRepeat_iter`, the H1 loop proofs in
     `Build/StepBlockLoop.lean`, or C1's countdown (`canonUnaryLoop`, `canonTrueOrbit`). If C1's
     loop lemma fits a step of the link, cite it.
3. **The suffix.** From the table's end to the right blank, by the landed `canonSuffixTM`
   (`canonSuffix_run`): all `true` accepts, any `false` rejects.
4. **The ledger, fail-fast included.**
   - Every successful record consumes at least `4k + 5` cells (`codeActionK_length`,
     `skipTable_consumes`, `canonSkipFields_cells`), and every record fails on a blank. So at most
     `|x| + 1` records run before a failure or the table's end.
   - Each record is charged `O(|x| + |bits|)` by C2's bound plus the adapter's two dispatches,
     and `|bits| ≤ |x|` (`length_pairEncode` at the decoded pair).
   - The counter loops add `counterOverhead`, at most `4r + 2|w|` per loop
     (`counterOverhead_le_of_le`).
   - The total is quadratic in `|x| + 1` and independent of the value `n`: this is the stage's
     `a * (x.length + 1) ^ a`.
   - The guard's hypotheses (canonicality, `canonGuardBlock F * (n + 1) ≤ |rest|`) are available
     if a bound needs them.

**Note 50** (prescribed; user decision 2026-10-14).
- Copy `audits/evidence/b5a-canon-cont4/CanonNote50.lean.txt` unchanged to your zip's
  `evidence/CanonNote50.lean.txt`.
- Elaborate it with `scripts/lean_check_tree.sh` (0 errors), and quote its last line. For a
  complete delivery, `#print axioms note50_cases` shows no `sorryAx`.
- A partial says "pending" and quotes the print.

### Phases (for a partial; ground rule 9)

1. **The adapter and its first-return contract** (a private lemma).
2. **The generic link**, over the adapter's contract.
3. **`exists_canonGrammarStage` proved:** the canonizer is complete.
4. **Note 50** elaborated on the complete canonizer.

A partial may leave only the frozen stub open. **Add no new admission:** any component you state
for yourself goes in only once it is proved. The freeze check for a partial is the **axiom
walk**: `sorryAx` reaches the headline only through the stub.

## Gate guidance (binding)

As in cont4 and cont5:
- minor 5 (zero guard);
- note 47 (`tableBitsK` stays in the item-8 residual family);
- note 50 (permanent; no `#eval`, `native_decide` or `IO`);
- round-2 note 17 (keep the S1210 probe's detecting control);
- the time-zero cut: `exists_canonHeaderCall` and `exists_installCallTM` give the positive-time
  cut only; `canonStrictInstall` and the release adapter cover coincident anchors;
- F7-1(c): your leaves and `StepBlock.recordTM` walk a record's fields; do not copy the step
  block's reader or its trace.

## Cited infrastructure (public and proved at the issue commit)

Exactly cont4's list ("Cited infrastructure" there) and #118's lemmas for this brief, all of it
resolving in `CanonCont6ImportProbe.lean.txt` at your base (156 names). In your file you also
cite:
- C1, C2 and their contracts;
- the eight bridges;
- the inherited front end (`exists_canonParseFront`, `canonBlankLift`, `canonEmbedEq`);
- #113's leaves and `canonEmitVerdict`.

**Proved modulo, exactly:** none. A complete delivery has no `sorryAx` in the headline.

## Ground rules (binding)

1. **File ownership, by declaration.** In `TuringMachine/CodeSimulator.lean`, and nowhere else,
   you own exactly these regions:
   - **(a) the home**, the blank line 4626: your own `private` declarations. `private` only, and no
     `section`, `open` or `variable` that leaks past it.
   - **(b) `exists_canonGrammarStage`'s body**, the `sorry` on line 4661, and its appendix
     paragraph (4640–4645): rewrite it as **"Fill appendix (canonizer continuation 6)"** for the
     final state, before the closing ` -/` (end of 4645). The statement (4646–4660) and the rest of
     the docstring (4627–4639) are frozen.
   - **(c) `exists_polyCanonizer`'s docstring**, lines 4860–4968: append a flagged **"Fill appendix
     (canonizer continuation 6)"** paragraph before the closing ` -/` (at the end of line 4968).
     The existing text does not change, except that the "(spec, fill pending — batch B5a)" tag on
     line 4860 becomes "proved", only for a complete delivery; flag it. The statement and the glue
     (from 4969) are frozen.

   **Not yours:** every other line, including:
   - the module header and every section heading;
   - every existing declaration: #96's, #107's and #113's deliveries, `exists_canonDecider`
     included;
   - the D4 section (5016–5067: its section comment, `section StepBlockClients`/`open StepBlock`
     and the four clock declarations). D4 is complete: no further deletions or moves;
   - H1's region (`h1HostedVerdictTM` … `exists_uniformSimulator`, 5068–5268).

   The maintainer updates the module header and the status text in `Codes2Tape.lean`/`EXPCOM.lean`
   at integration; report any text that reads wrong. List every new declaration with its role.
2. **Statement freeze** over every landed declaration and the stub's statement: no renames,
   re-signatures, restatements or attribution edits.
3. **Status text.** Only the headline's tag may change, as in rule 1(c). No new public declaration.
4. **Escalation** on anything unprovable as stated, including a cited row that does not compose as
   the route says: stop on that item, record the obstruction, and continue with the rest.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Unchanged. No TCSlib import may be added. A Mathlib import only if a needed lemma
   requires it; flag it.
7. **One proof per shared argument.** Never re-walk a landed contract. Never write a second host,
   loop, trace or layout lemma for something already public or already proved in your region, in
   particular C1, C2, #113's leaves, their run lemmas and `canonBlankLift`/`canonEmbedEq`.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public and
   private declaration counts (base: 5,271 lines; 12 public, 144 private).
9. **Continuation budget.** A partial zip states the phase reached, the open stub (with a literal
   "Proof sketch"), and the headline's axiom walk. A partial is expected and fine; an unreported
   gap is not.
10. **The pinned base, and no unfolding (user, 2026-10-16).**
    - Cite only declarations public at your base, and your file's own privates.
    - **Never unfold a definition of another file.** Read every definition through its published
      lemmas: the specification API (PR #112), the core API (PR #116), the brief-inventory API
      (PR #118), and the landed lemmas the probe lists.
    - **The machine model's primitives** (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
      `Cfg.mapState`) are read through their existing lemmas. Unfold `step` and `Action.apply`
      only for a leaf defined in your own file. `phaseHostTM`'s table is read through
      `phaseHostTM_run`.
    - Your own file's definitions may be unfolded.
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate** (ground rule 4), naming the lemma you need.
    - List every declaration you cite outside your file in `REPORT.md`. If you cite more than the
      probe's list, add them to a copy of the probe and run it.
11. **MIG-1 compatibility.** Keep `canonPreserveInstall` byte-identical (line 1255; F-D rewrites its
    `copyTM_run` citation, line 1293, after you). Cite none of the six R3 rows anew (`copyTM_run`,
    `transferTM_run`, `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`,
    `incrementTM_run_overflow`); use their framed `_ofCfg` forms.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**
(`audits/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**).
- **The population** is cont4's 45 files
  (`audits/evidence/b5a-canon-cont6/b5a-canon-cont6-screen-population.txt`, the same list).
- **The screen** is the declaration-keyed `audits/evidence/retrofit/copy-text-screen-v3.py`, run on
  the repository paths.
- **The base**, at the issue tree, is `audits/logs/b5a-fill-canon-cont6-screen-base.txt`:
  **2,410 declarations, 2,631 pairs, 824,047 characters** (MEASURED with v3 at #118's round-2 head;
  about 30 minutes).

```sh
P=audits/evidence/b5a-canon-cont6
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/b5a-canon-cont6-screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/b5a-canon-cont6-screen-population.txt) > /tmp/screen-after.txt
```

- **No new cross-file pair** with an owned-file declaration on one side. Nothing is
  pre-disclosed.
- **Recorded, add nothing to them:**
  - `scan_grammar_guard`/`canonScan_all` (55%, cont3);
  - the frozen `canonOffset_spec` reproducing `Turing.length_bits_le_self` (100%; backlog);
  - the earlier canonizer in-file pairs;
  - the uniform-code mirror pair (75%, CH34-D3);
  - item 8's writer pairs.
- **Known hazards.** A proof that reproduces one of the following at 90% or more must be factored
  (parameterize, or cite):
  - C1's countdown and C2's leaf;
  - the inherited native leaves and #113's (`guardBlockTM` and its family, `canonCellTM`,
    `canonPairsTM`, `canonTagTM`, `canonTrimTM`, `canonSuffixTM`, `canonHaltTM` and their run
    lemmas);
  - `canonEmitVerdict`'s phase-host composition: your adapter follows the pattern, it does not
    transcribe it;
  - `MathlibBridge.codeSkipRepeat_iter` and the chapter-1 parser;
  - the H1 counter-loop proofs in `Build/StepBlockLoop.lean`;
  - the R1 reconstruction family (cite `canonEmbedEq`, `canonBlankLift`, `embedEmitCfg_eq`).

  **The earlier lesson:** repeated one-step run unfolding created two cross-file pairs (against
  `MultiTapeTM.liftSymbols_runFrom` and `timedFrame_run`). The public `step_of_inputMoveAction`
  already supplies each one-step result.
- List every new in-file pair with a one-line justification. At 90% or more it is a copy: factor it.
  Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/b5a-fill-canon-cont6.txt` (**102 modules**: the upstream
  closure of your owned file and of every module downstream of it, plus `ClassNP/TMSAT`'s for the
  statements probe). Since cont5 it adds `ClassNP/TMSAT` and `Build/Contract/Counter`:

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/b5a-fill-canon-cont6.txt )
  ```

  **The base sorry-warning set has 41 entries in 16 modules**
  (`audits/logs/b5a-fill-canon-cont6-base-sorries.txt`, one entry per declaration). Yours is
  `CodeSimulator`'s first of two: the stub. Record the base list by name first, and report any
  difference.
- **Final checks:**
  1. `CodeSimulator`: zero errors, and exactly one sorry warning, `exists_uniformSimulator` (plus,
     for a partial, the stub).
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's. For
     a complete delivery that is **40** in all, counting `CodeSimulator`'s one.
  3. Re-run `CanonCont6ImportProbe.lean.txt`, `CanonCont3ImportProbe.lean.txt`,
     `B5aStatementsProbe.lean.txt` and `B5aContPreShip.lean.txt`: 0 errors.
  4. Re-run `S1210StatementsProbe.lean.txt`: 0 errors, its census still detecting its probe-local
     admission.
  5. Elaborate the note-50 file: 0 errors; its axiom print.
- **Axiom prints**, within `[propext, Classical.choice, Quot.sound]`, for:
  - the headline;
  - every new private, in an in-module probe, as the previous reports did;
  - targets 3–8 (`Turing.exists_uniformMachineCode2`, `Turing.exists_uniformMachineCode`,
    `Complexity.EXP_subset_POracle_EXPCOM`, `Complexity.POracle_EXPCOM_eq_EXP`,
    `Complexity.NPOracle_EXPCOM_eq_EXP`, `Complexity.POracle_EXPCOM_eq_NPOracle_EXPCOM`) and
    `Complexity.baker_gill_solovay`.

  For a complete delivery the headline has no `sorryAx`, and the others have it only through
  `exists_uniformSimulator`. For a partial, the headline's admission walk names exactly the stub.
- **Lint:** `python3 -I scripts/campaign_style_lint.py` over `TCSlib/Complexity/TuringMachine`
  (base: 0 FAIL, 67 WARN over 79 files) and `TCSlib/Complexity/Diagonalization` (base: 0 FAIL,
  1 WARN over 4 files), 0 FAIL. Add no line over 100 characters and no Lean linter warning in your
  region.

## Out-of-scope sorries you will see (leave every one untouched)

The base sorry set, apart from your stub:
- `TuringMachine/CodeSimulator`: `exists_uniformSimulator` (H1, a later brief);
- the 39 others listed in `audits/logs/b5a-fill-canon-cont6-base-sorries.txt`. These are:
  - MIG-1 stage S's sorried specs (`Simulation`, `Composition`, `Build/Wrappers`, `Build/Loop`,
    `Encoding`, `ClassP/TimeConstructible`, `Build/Primitives`);
  - `Build/RecordTable`, `Diagonalization/NTimeHierarchy`, `Build/NDHost`, `Build/InputWindow`,
    `Build/InputDevice`, `NDCodeSimulator`, `UniversalK`, `Build/ZoneRebalance`. `ClassNP/TMSAT`,
    added for the statements probe, has none.

If a proof seems to *need* one of these beyond a named citation, that is an escalation, not a
license.

## REPORT.md checklist

- [ ] The phase reached (1–4), the base hash and the ancestor check.
- [ ] The adapter: its statement, its first-return contract, and how the fresh anchor keeps C2's
      internal entry visits out of the cut.
- [ ] Every new declaration with its role; every flagged appendix and status update.
- [ ] The generic components' contracts (the adapter, any repetition loop), as promotion
      candidates.
- [ ] Requested shared lemmas and escalations, or "none".
- [ ] Rule 10: the declarations cited outside your file, and the probe re-run. Rule 11:
      `canonPreserveInstall` unchanged; no new citation of the six R3 rows (a grep of your diff).
- [ ] Duplication: both v3 screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the re-run probes; every axiom print; the headline's
      admission walk; the lint lines. The diff touches only your owned regions.
- [ ] Note 50: the file's elaboration and its axiom print (or "pending").

## Known pitfalls at this pin (hard-won)

All of cont4's and cont5's ("Known pitfalls" there) still hold, **except cont5's claim that C2
can be a counter-loop body without a wrapper, which is withdrawn** (E1). In particular:
- `Cfg.inputPos` starts at `1`, so the suffix at position `p` is `x.drop (p - 1)`.
- The front end's ready configuration is not `Cfg.ofWords`.
- `counterLoopTM M` has `k + 1` tapes with the counter at `Fin.last k`. On `done` the counter
  interval is all `true`; on `escape` it holds `counterWord w r`, so clear or re-write it before
  reuse.
- `codeSkipRepeat r (n + 1) xs = (r xs).bind (codeSkipRepeat r n)` is `codeSkipRepeat_succ` (cite
  it; do not rely on `rfl` through another file's definition), and the nested `codeSkipTableK`
  needs `canonSkipTable_eq`.
- `counterLoopOrbit` is an `abbrev` of `roundOrbit`, so `rw [roundOrbit_succ]` does not fire on
  it; `exact` and `simp only [roundOrbit_succ]` do (#118's gate review, N3).
- `seamCompTM_firstReturn_ofCfg` needs the callee's cut at `t = 0` as well.
- The inherited canonizer lemmas take `(F : MachineFormat)` explicitly.
- C1 and C2 run on a two-tape bank with the bound at index `0`. C2's coefficient is
  `16 + 4k + 9`, linear in `|x| + |w| + 1`. Both restore every work tape and head and leave the
  native head at the accepted suffix.

**New for cont6:**
- **C2's `exit true` is stationary and distinct from its entry** (cont5's review, check 23: the
  worker's diagnostics `cont5_record_entry_ne_true` and `cont5_record_true_stationary`, not in
  the repository). The counter loop's rounds must
  return to one anchor, hence the adapter.
- `phaseHostTM_run` gives the prefix up to `T` and the dispatch at `T + 1`; its `hguard` must hold
  strictly before `T`. A phase whose entry equals its verdict has `T = 0`.
- `canonEmitVerdict` is the landed model of a `phaseHostTM` composition in this file: follow its
  shape for the adapter.
- Use `step_of_inputMoveAction`/`step_of_tapeAction_move`, not `runFrom_succ_eq_step` chains.
