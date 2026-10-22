# Ch3–4 fill campaign — B5a, the canonizer, continuation 7: the grammar stage (`exists_canonGrammarStage`, by declaration in `TuringMachine/CodeSimulator.lean`)

> **Megafill A, item 3 of 3** (cover brief `megafill-A.md`; addendum v2.4, Part 3). The
> preflight, the toolchain, the clone and the cache are done once for the whole queue. For this
> item: create its branch from the shared base (below), **re-bootstrap your order list** (items 1
> and 2 changed `NDCodeSimulator` and `Diagonalization/NTimeHierarchy`, both downstream of your
> file, on their own branches), then follow this brief. **Budget:** the rest of the session.

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If the check fails,
  **stop**. That commit contains:
  - **your predecessors' deliveries:** PR #113 (continuation 5: the factoring,
    `exists_canonDecider` proved modulo your stub, the suffix scan
    `canonSuffixTM`/`canonSuffix_run`,
    the emitting halt, `canonEmitVerdict`) and **PR #131 (continuation 6, landed as a partial)**:
    - the fresh-anchor adapter `canonReturnAdapter` (a `phaseHostTM` composition, two dispatch
      steps, a positive first-return contract) and its C2 instance `exists_canonRecordRound`;
    - the generic counter-loop link `canonCounterRepeat`, with `canonRepeat_orbit` and
      `canonRepeat_last`;
    - its gate (`campaign/gates/49-b5a-canon-cont6-fill/`, PASS 0/0/2/11) and the maintainer's
      review (`campaign/fills/b5a/reviews/canon-cont6/REVIEW.md`), whose "Continuation 7 should"
      this brief carries;
  - **the API PRs** (the user's "Everything" rule, 2026-10-16): the specification API (PR #112),
    the core API (PR #116), the brief-inventory API (PR #118), and **#122's value equations
    `Turing.counterValue_eq` and `Turing.codeBitsNat_eq`** (cont6's review, F3);
  - the fill-agent environment addendum `campaign/standards/fill-environment-addendum.md`
    (**v2.4**: Part 1, the resources and the cache for the Mathlib roots only; **Part 3, the
    megafill**, under which this session runs), and the copy-text screen v3
    `scripts/copy-text-screen-v3.py`;
  - **this round's inputs** (`campaign/fills/b5a/inputs/b5a-fill-canon-cont7/`): the import probe
    and the screen population. Also the order list
    `campaign/fills/b5a/orders/b5a-fill-canon-cont7.txt`, the base sorry set, the screen base and
    the pre-ship log (`campaign/fills/b5a/logs/b5a-fill-canon-cont7-*`).
- **The environment was set up once, at the session's start** (the cover brief; Part 1 of
  `campaign/standards/fill-environment-addendum.md` and its Part 3): the preflight, the
  toolchain, the clone and the cache for the whole queue's Mathlib roots. If Lean cannot start,
  Part 2 applies. **If Lean never runs, do not draft proofs blind.**
- **Branch from exactly that commit**, not from the moving campaign tip:
  `git checkout -b fill/b5a-canon-cont7 @ANCESTOR@`, then `git rev-parse HEAD` must print
  `@ANCESTOR@`. Record the base hash in `REPORT.md`. Never rebase, merge or cherry-pick anything
  into your branch.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-b5a-canon-cont7.zip`. It
  contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle;
  - the final sweep log and the axiom log;
  - the note-50 file and its log;
  - both screen outputs, and `SHA256SUMS`.
- **Checkpoint zips.** Each checkpoint of phase 3 below may land alone. After each, commit and
  write `fill-b5a-canon-cont7-cp<N>.zip` with the same contents as of that commit (the final sweep
  may be `CodeSimulator`'s own check), so that a lost workspace loses at most one checkpoint.
  Deliver the latest if the session ends early.

## Base, line numbers and what is in flight

- **Your base's Lean content is the campaign tip after #137** (`2ff214c5`, #137's merge; #132,
  #140, #138, #133, #134 and #136 merged since #131, none of them upstream of your file). The
  inputs commit adds no Lean change. Lines in this brief are those of that tree.
  `CodeSimulator.lean`
  is #131's, unchanged (5,590 lines; 12 public, 149 private). Every probe and measurement below
  was run there, against the olean snapshot `oleans-lg4c2` (the tip's merged-tree replay).
- **In flight, merging after your base and invisible to it:** #139 (`Build/StepClock`), #143
  (`Build/ZoneRebalance`), the seam layout's landing (`Build/SeamLayout`), MIG-12's fill
  (`Build/CfgRecord`); earlier in this session, on their own branches, R (`NDCodeSimulator`) and
  UN (`Diagonalization/NTimeHierarchy`), both downstream of your file; on another host, U2-S
  (`UniversalK`, downstream of your file), F5 (`Build/InputDevice`) and G4
  (`Build/ZoneRebalance`). Cite nothing these add.

## Parallel batches this round

None in `CodeSimulator.lean`. H1's continuation (`exists_uniformSimulator`) is briefed later.

## What this is

**The canonizer's last open admission.** `MachineFormat.exists_polyCanonizer` is proved modulo
exactly one private stub, **`exists_canonGrammarStage`** (line 4965). Your target is that stub,
then note 50 on the complete canonizer. With H1, the two-tape code scheme, the `EXPCOM` cluster
and Baker–Gill–Solovay then lose their last canonizer admission.

**Where continuation 6 stopped** (its review): phases 1 and 2 are complete. The adapter is
exactly the authorized design, and the link is generic over a round specification. **Phase 3,
the stage itself, is not started**: no C1 embedding, no inner or outer loop machine, no counter
initialization, no suffix scan and no ledger. The review found that the assembly needs no further
generic kit: the inner counter loop (done/escape) is itself a source with an injective Boolean
exit, so the same `canonReturnAdapter` gives the outer round's first-return contract.

**The user's rules that stay in force:** the `computesFunInTime_cond` decomposition (cont3's
route, landed); a partial may leave the named private stub open, checked by an **axiom walk**
(`sorryAx` reaches the headline only through `exists_canonGrammarStage`); the adapter is
authorized (cont5's E1 ruling).

**Read first:**
- continuation 6's review, (c) and (g);
- the cont6 brief `campaign/fills/b5a/briefs/b5a-fill-canon-cont6.md`, and through it the cont5
  and cont4 briefs: their route C3–C5, gate guidance and pitfalls bind where this brief does not
  replace them;
- the C1 and C2 contracts (`campaign/fills/b5a/reports/canon-5-REPORT.md`, "Construction and
  promotion contracts");
- `CodeSimulator.lean` lines 4568–4980: `canonEmitVerdict`, `canonReturnAdapter`,
  `exists_canonRecordRound`, `canonRepeat_last`, `canonRepeat_orbit`, `canonCounterRepeat` and the
  stub;
- `Build/CounterLoop.lean`: `counterLoopTM`, `counterLoopTM_run_done`/`_run_escape`,
  `counterLoop_time_le`, `counterOverhead_le_of_le`, `counterValue` with `counterValue_eq`,
  `counterWord`;
- `CodeParser.lean`: `codeSkipRepeat` with `codeSkipRepeat_zero`/`_succ`, `codeBitsNat_eq`,
  `codeSkipActionK`, `codeEraseActionK`, `codeReadActionK_sound`.

**Pre-ship check** (maintainer, at the base;
`campaign/fills/b5a/logs/b5a-fill-canon-cont7-preship.log`):
- **`CodeSimulator.lean` at the base** elaborates with 0 errors and exactly 2 sorry warnings: your
  stub and `exists_uniformSimulator`.
- **The import probe** `CanonCont7ImportProbe.lean.txt` (224 `#check`s: continuation 6's 156, its
  worker's further 66 citations with `counterLoopOrbit`, and the value bridges): every public
  declaration this brief cites resolves. 0 errors, 0 warnings. **Re-run it after your delivery.**
- **Note 50** (`campaign/fills/b5a/evidence/b5a-canon-cont4/CanonNote50.lean.txt`, prescribed):
  0 errors; `note50_cases` prints `sorryAx`, reached through `exists_canonGrammarStage` only.
- **The value bridges** (continuation 6's review, probed at #122's head): `counterValue w =
  Nat.ofDigits 2 (w.map Bool.toNat)` is `rw [counterValue_eq]`; `counterValue w = codeBitsNat w` is
  `rw [counterValue_eq, ← foldr_bit_eq_ofDigits, codeBitsNat_eq]`; `Nat.ofDigits 2 (w.map
  Bool.toNat) = codeBitsNat w` is `rw [← foldr_bit_eq_ofDigits, codeBitsNat_eq]`.

## Owned region and target (modify these and nothing else)

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `CodeSimulator.lean:4965` | `exists_canonGrammarStage` (frozen statement) | C3–C5, phase 3 below | C1, C2, the adapter, the link, the public counter loop, the suffix leaf |
| 2 | `CodeSimulator.lean:5288` | `Turing.MachineFormat.exists_polyCanonizer` | the landed glue (frozen) | target 1 |

### Home and regions

- **(a) the home**, the blank line 4952, between `canonCounterRepeat`'s last line (4951) and the
  stub's docstring (4953), inside `namespace MachineFormat`: your own `private` declarations, each
  after what it uses and before its first consumer. `private` only, and no `section`, `open` or
  `variable` that leaks past it.
- **(b) the stub's body**, the `sorry` on line 4980, and **for a partial only** a paragraph headed
  `**Implementation status.**` at the end of the stub's docstring, before its closing ` -/` (end of
  line 4964). It is public-facing library text: what is proved and what is open, in mathematical
  terms, with no campaign labels (brief, gate, finding, continuation or escalation names), no
  dates and no session narrative. The same holds for the docstrings of your new declarations;
  provenance goes in `REPORT.md`.

**Not yours:** every other line, including the headline's docstring (5179–5287) and its tag: the
maintainer rewrites the canonizer's status text (the module header, the headline's docstring, and
`Codes2Tape`/`EXPCOM`'s) at integration. Report any text that reads wrong. Also not yours: every
existing declaration (`exists_canonDecider` and continuation 6's lemmas included; adjust none of
them, cite them), the D4 section (5335 on) and H1's region (`h1HostedVerdictTM` …
`exists_uniformSimulator`, 5390–5590).

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **Compose by the public combinators**: R2 seams (`seamCompTM`, `seamReleaseTM`); the phase host
  (`phaseHostTM`, `phaseHostTM_run`); R1 (`embedEmitTM`, `embedEmitCfg_eq`); the counter loop
  (`counterLoopTM`, `counterLoopTM_run_done`, `counterLoopTM_run_escape`); the framed catalog rows
  (`copyTM_run_ofCfg`, `clearTM_run_ofCfg`, `writeConstTM_run_ofCfg`,
  `incrementTM_run_succ_ofCfg`). Never write a second loop, seam or embedding transport.
- **Cite your file's proved privates**, never re-walk their internals: C1 `exists_canonUnaryTM`,
  C2 `exists_canonRecordTM`, continuation 6's `canonReturnAdapter`, `exists_canonRecordRound`,
  `canonCounterRepeat`, `canonRepeat_orbit`, `canonRepeat_last`, #113's leaves (`canonSuffixTM`,
  `canonSuffix_run`, `canonHaltTM`, `canonHalt_run`) and `canonEmitVerdict`.
- **Leaves you may write:** none is expected. A further leaf is an escalation.
- **Promotion candidates** (list each with its contract in `REPORT.md`; notes only): the adapter,
  the generic link, any repetition loop you build, C1, C2 and the strip machine.

### The route: phase 3, in order, each step a checkpoint that may land alone (binding where it names a row)

Tape `header` holds `bits`, every other tape is blank, and the native head is at the remainder.
Decide `(canonGrammar F.k n rest).isSome`, where `n = codeBitsNat bits`.
1. **The record round, instantiated.** Apply `canonCounterRepeat` at `exists_canonRecordRound`,
   with `r := codeSkipActionK k (counterValue bits)`, `valid` := C2's bank preconditions,
   `tail d := x.drop (d.inputPos.val − 1)` and `B := (a + 2)(|x| + |bits| + 1)`. The tail update on
   success comes from `codeEraseActionK` and `codeReadActionK_sound`.
2. **The inner block.** `writeConstTM_run_ofCfg` writes the inner counter for `3^(k+1)` rounds;
   then the inner loop through a seam; then `canonReturnAdapter` again (done ↦ the anchor, escape
   ↦ the escape) for the outer round's first-return contract.
3. **The outer loop** over a header copy, `n + 1` state blocks (`canonSkipTable_eq`): either one
   leading block before a loop of `n` (`codeSkipRepeat_succ`), or `incrementTM_run_succ_ofCfg` on a
   copy padded with a spare `false`. `canonSkipRepeat_mul` and `canonSkipTable_eq` give the
   grammar. The header copy's counter hypothesis is `Nat.ofDigits 2 (bits.map Bool.toNat) = n`, by
   the value bridges above; **never unfold `counterValue` or `codeBitsNat`**.
4. **C1 on `{header, scratch}`** (the initial state's range check, bound `counterValue bits = n`),
   then **`canonSuffix_run`** from the table's end to the right blank, with every failure forwarded
   to the rejecting port.
5. **The ledger.** At most `|x| + 1` records run (each successful record consumes at least
   `4k + 5` cells: `codeActionK_length`, `skipTable_consumes`, `canonSkipFields_cells`; each fails
   on a blank); each is charged `O(|x| + |bits|)` (C2's bound plus the adapter's two dispatches),
   with `|bits| ≤ |x|` (`length_pairEncode` at the decoded pair); each loop adds
   `counterOverhead_le_of_le`. The total is quadratic in `|x| + 1` and independent of `n`: the
   stage's `a * (x.length + 1) ^ a`. The guard's hypotheses are available if a bound needs them.
6. **The stub proved**, then **note 50**: copy
   `campaign/fills/b5a/evidence/b5a-canon-cont4/CanonNote50.lean.txt` unchanged to your zip's
   `evidence/CanonNote50.lean.txt`, elaborate it (0 errors) and quote its last line; for a complete
   delivery `#print axioms note50_cases` shows no `sorryAx`. A partial says "pending".

Do not copy `MathlibBridge.codeSkipRepeat_iter`, the H1 loop proofs in `Build/StepBlockLoop.lean`,
or C1's countdown; cite C1's loop lemma if it fits a step.

### Phases (for a partial; ground rule 9)

The checkpoints 1–6 above. A partial may leave only the frozen stub open. **Add no new
admission:** any component you state for yourself goes in only once it is proved. The freeze
check for a partial is the **axiom walk**: `sorryAx` reaches the headline only through the stub.

## Gate guidance (binding)

As in cont4–cont6: minor 5 (zero guard); note 47 (`tableBitsK` stays in the item-8 residual
family); note 50 (permanent; no `#eval`, `native_decide` or `IO`); round-2 note 17 (keep the S1210
probe's detecting control); the time-zero cut (`canonStrictInstall` and the release adapter cover
coincident anchors); F7-1(c) (do not copy the step block's reader or its trace). Gate 49 (cont6's
landing) adds: carry the corrected citation inventory (with `counterLoopOrbit`) into your report.

## Cited infrastructure (public and proved at the issue commit)

Exactly the probe's 224 names, resolving at your base. In your file you also cite C1, C2 and
their contracts; the eight bridges; the inherited front end (`exists_canonParseFront`,
`canonBlankLift`, `canonEmbedEq`); #113's leaves and `canonEmitVerdict`; continuation 6's five
lemmas.

**Proved modulo, exactly:** none. A complete delivery has no `sorryAx` in the headline.

## Ground rules (binding)

1. **File ownership, by declaration**: only regions (a) and (b) above, in
   `TuringMachine/CodeSimulator.lean`, and nowhere else. List every new declaration with its role.
2. **Statement freeze** over every landed declaration and the stub's statement: no renames,
   re-signatures, restatements or attribution edits.
3. **No new public declaration.** No status text outside (b).
4. **Escalation, item by item:** on anything unprovable as stated, including a cited row that does
   not compose as the route says, stop **on that item only**, record the obstruction
   mathematically, and continue with every item that does not depend on it. Two rounds have
   produced kit only; this round's measure of progress is the composed stage.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Unchanged. No TCSlib import may be added. A Mathlib import only if a needed lemma
   requires it; flag it.
7. **One proof per shared argument.** Never re-walk a landed contract. Never write a second host,
   loop, trace or layout lemma for something already public or already proved in your file.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public and
   private declaration counts (base: 5,590 lines; 12 public, 149 private).
9. **Continuation budget.** A partial zip states the checkpoints reached, the open stub (with a
   literal "Proof sketch"), and the headline's axiom walk.
10. **The pinned base, and no unfolding (user, 2026-10-16).**
    - Cite only declarations public at your base, and your file's own privates.
    - **Never unfold a definition of another file**, and **no definitional closure either**: a
      `rfl`, `exact`, `show`, `decide`, `simp` or `simpa` step that closes only because another
      file's definition reduces counts as unfolding. Continuation 6's F1 was one: `simpa only
      [c, Cfg.mapState_workTapes] using word` could not rewrite the partial application
      `(c).workTapes bound`, since `Cfg.mapState_workTapes` is stated fully applied, and the
      closing `exact` unfolded `Cfg.mapState`. Rewrite pointwise (`funext`, then the field lemma).
    - **The machine model's primitives** (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
      `Cfg.mapState`) are read through their lemmas. Unfold `step` and `Action.apply` only for a
      leaf defined in your own file. `phaseHostTM`'s table is read through `phaseHostTM_run`.
    - Your own file's definitions may be unfolded.
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate** (ground rule 4), naming the lemma you need.
    - **Self-check:** a seal test (a scratch copy of your module with `attribute [local
      irreducible]` on every other-file definition your new proofs mention, which must still
      elaborate) and an inspection of every `rw`/`simp`/`simpa`/`unfold` argument in your diff.
    - List every declaration you cite outside your file in `REPORT.md`. If you cite more than the
      probe's list, add them to a copy of the probe and run it.
11. **MIG-1 compatibility.** Keep `canonPreserveInstall` byte-identical (line 1255; MIG-1's F-D
    rewrites its `copyTM_run` citation, line 1293, after you). Cite none of the six R3 rows anew
    (`copyTM_run`, `transferTM_run`, `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`,
    `incrementTM_run_overflow`); use their framed `_ofCfg` forms.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**
(`campaign/standards/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**).
- **The population** is cont4's 45 files
  (`campaign/fills/b5a/inputs/b5a-fill-canon-cont7/screen-population.txt`, the same list).
- **The screen** is `scripts/copy-text-screen-v3.py`, on the repository paths.
- **The base**, at the issue tree, is
  `campaign/fills/b5a/logs/b5a-fill-canon-cont7-screen-base.txt`:
  **2,419 declarations, 2,633 pairs, 824,240 characters** (MEASURED; about 30 minutes).

```sh
P=campaign/fills/b5a/inputs/b5a-fill-canon-cont7
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-after.txt
```

- **No new cross-file pair** with an owned-file declaration on one side. Nothing is
  pre-disclosed.
- **Recorded, add nothing to them:** `scan_grammar_guard`/`canonScan_all` (55%); the frozen
  `canonOffset_spec` reproducing `Turing.length_bits_le_self` (100%; backlog); the earlier
  canonizer in-file pairs; the uniform-code mirror pair (75%); item 8's writer pairs.
- **Known hazards** (a proof reproducing one at 90% or more must be factored): C1's countdown and
  C2's leaf; the inherited native leaves and #113's; `canonEmitVerdict`'s and the adapter's
  phase-host compositions (your second adapter use cites the lemma, it does not re-prove it);
  `MathlibBridge.codeSkipRepeat_iter` and the chapter-1 parser; the H1 counter-loop proofs in
  `Build/StepBlockLoop.lean`; the R1 reconstruction family (cite `canonEmbedEq`, `canonBlankLift`,
  `embedEmitCfg_eq`). Use `step_of_inputMoveAction`/`step_of_tapeAction_move`, not
  `runFrom_succ_eq_step` chains (the earlier lesson: one-step unfolding created two cross-file
  pairs).
- List every new in-file pair with a one-line justification. Quote both outputs in `REPORT.md`,
  which carries **"new copies: none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; the cache **for the queue's Mathlib roots only** (addendum
  v2.4, fetched once at the session's start; your order list's modules import 41 roots directly);
  **never `lake build`**, and never the unfiltered `lake exe cache get`. Use
  `scripts/lean_check_tree.sh` for every check.
- **Re-bootstrap** (addendum Part 3, item 3.2) from
  `campaign/fills/b5a/orders/b5a-fill-canon-cont7.txt` (**118 modules**: the upstream closure of
  your owned file and of every module downstream of it, plus
  `ClassNP/TMSAT`'s for the statements probe).
  **The base sorry-warning set has 38 entries in 17 modules**
  (`campaign/fills/b5a/logs/b5a-fill-canon-cont7-base-sorries.txt`, one entry per declaration).
  Yours is `CodeSimulator`'s first of two: the stub. Record the base list by name first, and report
  any difference.
- **Final checks:**
  1. `CodeSimulator`: zero errors, and exactly one sorry warning, `exists_uniformSimulator` (plus,
     for a partial, the stub).
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's.
  3. Re-run `CanonCont7ImportProbe.lean.txt` and the inherited probes (cont3's import probe,
     `B5aStatementsProbe`, `B5aContPreShip`, `S1210StatementsProbe` with its census still detecting
     its probe-local admission): 0 errors.
  4. Elaborate the note-50 file: 0 errors; its axiom print.
- **Axiom prints**, within `[propext, Classical.choice, Quot.sound]`, for the headline, every new
  private (in an in-module probe), targets 3–8 (`Turing.exists_uniformMachineCode2`,
  `Turing.exists_uniformMachineCode`, `Complexity.EXP_subset_POracle_EXPCOM`,
  `Complexity.POracle_EXPCOM_eq_EXP`, `Complexity.NPOracle_EXPCOM_eq_EXP`,
  `Complexity.POracle_EXPCOM_eq_NPOracle_EXPCOM`) and `Complexity.baker_gill_solovay`. For a
  complete delivery the headline has no `sorryAx`, and the others have it only through
  `exists_uniformSimulator`.
- **Lint:** `python3 -I scripts/campaign_style_lint.py` over `TCSlib/Complexity/TuringMachine`
  (base: 0 FAIL, 63 WARN over 82 files) and `TCSlib/Complexity/Diagonalization` (base: 0 FAIL,
  1 WARN over 5 files), 0 FAIL. Add no
  line over 100 characters and no Lean linter warning in your region.

## REPORT.md checklist

- [ ] The session's shared preflight and cache numbers (quoted from its logs), and this item's
      bootstrap.
- [ ] The checkpoints reached (1–6), the base hash and the ancestor check; the checkpoint zips.
- [ ] Every new declaration with its role; the status paragraph, if a partial.
- [ ] The link's instantiation (`r`, `valid`, `tail`, `B`), the inner and outer blocks, the counter
      words, and the value bridges used.
- [ ] Requested shared lemmas and escalations (each stated mathematically), or "none".
- [ ] Rule 10: the declarations cited outside your file (with `counterLoopOrbit`), the probe
      re-run, the seal test and the inspection. Rule 11: `canonPreserveInstall` unchanged; no new
      citation of the six R3 rows (a grep of your diff).
- [ ] Duplication: both v3 screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the re-run probes; every axiom print; the headline's
      admission walk; the lint lines. The diff touches only your owned regions.
- [ ] Note 50: the file's elaboration and its axiom print (or "pending").

## Known pitfalls at this pin (hard-won)

All of cont4's to cont6's still hold. In particular:
- `Cfg.inputPos` starts at `1`, so the suffix at position `p` is `x.drop (p - 1)`.
- `counterLoopTM M` has `k + 1` tapes with the counter at `Fin.last k`. On `done` the counter
  interval is all `true`; on `escape` it holds `counterWord w r`, so clear or re-write it before
  reuse.
- `codeSkipRepeat r (n + 1) xs = (r xs).bind (codeSkipRepeat r n)` is `codeSkipRepeat_succ` (cite
  it), and the nested `codeSkipTableK` needs `canonSkipTable_eq`.
- `counterLoopOrbit` is an `abbrev` of `roundOrbit`, so `rw [roundOrbit_succ]` does not fire on
  it; `exact` and `simp only [roundOrbit_succ]` do.
- C2's `exit true` is stationary and distinct from its entry: hence the adapter.
- `phaseHostTM_run` gives the prefix up to `T` and the dispatch at `T + 1`; its `hguard` must hold
  strictly before `T`.
- **Field lemmas are stated fully applied** (`Cfg.mapState_workTapes`): a partial application
  `(c).workTapes j` needs `funext` first (continuation 6's F1).
- C1 and C2 run on a two-tape bank with the bound at index `0`. C2's coefficient is
  `16 + 4k + 9`, linear in `|x| + |w| + 1`. Both restore every work tape and head and leave the
  native head at the accepted suffix.
