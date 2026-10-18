# Ch3–4 fill campaign — B5a, the canonizer, continuation 4: the physical grammar and the validator (`MachineFormat.exists_polyCanonizer`, by declaration in `TuringMachine/CodeSimulator.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Confirm that `git merge-base --is-ancestor 46be11046b74b3ef0018c81afe272c9b411e5cfb HEAD` succeeds. That commit contains:
  - **your predecessor's phase-1 delivery (PR #96, merged):** the strip machine
    `exists_canonStripTM`, five helpers, the prescribed `computesFunInTime_cond` glue, and the two
    open stubs `exists_canonGrammarStage` and `exists_canonDecider`; its report
    `audits/b5a-fill-agent-reports/canon-4-REPORT.md`;
  - PRs #95 (`Build/RecordTable`, row 18 proved) and #97 (`Build/Embed`'s public
    `embedSilentCfg_cap`, `Build/NDHost`, `SpaceComplexity/Inclusions`), both merged;
  - the fill-agent environment addendum `briefs/fill-environment-addendum.md` and the
    declaration-keyed copy-text screen v3 `audits/evidence/retrofit/copy-text-screen-v3.py`;
  - the H1 harvest (PR #94): H1's counter-loop assembly moved from `CodeSimulator.lean` to the
    public `Build/StepBlockLoop.lean`, and the canonizer's former private `canonBits_value` is now
    the public **`Turing.foldr_bit_eq_ofDigits`** in `Build/CounterLoop` (beside
    `Turing.counterValue` and `Turing.counterValue_bits`);
  - this round's inputs: the order list `briefs/orders/b5a-fill-canon-cont4.txt`, the base sorry
    set, the screen population and base, the pre-ship log, and the pre-ship probes with their
    generator (`audits/evidence/b5a-canon-cont4/`).

  If the check fails, **stop**.
- If Lean cannot start, follow `briefs/fill-environment-addendum.md` exactly.
- **Branch from exactly that commit**, not from the moving campaign tip:
  `git checkout -b fill/b5a-canon-cont4 46be11046b74b3ef0018c81afe272c9b411e5cfb`. Record the base hash in `REPORT.md`. Never
  rebase, merge or cherry-pick anything into your branch.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-b5a-canon-cont4.zip`,
  containing `REPORT.md`, the full modified source, a `git format-patch` series against your
  base, a git bundle, the final sweep log, the axiom log, the note-50 file and its log, both screen
  outputs, and `SHA256SUMS`.

## Base, line numbers and what is in flight

- **Lines in this brief are those of the campaign tip `ff4cab18`**, whose Lean content is
  `c9cc485b` (#95, #96 and #97 merged, in that order). `CodeSimulator.lean` is byte-identical
  to #96's branch head, so no line in it moved. The inputs commit `46be11046b74b3ef0018c81afe272c9b411e5cfb` adds no Lean
  change. Every probe and measurement below was run at the tip, against the olean snapshot of the
  merged tip's catch-up replay.
- **Since #96, four modules changed, none of them yours:** `Build/Embed` (upstream of you; one
  added public theorem), `Build/RecordTable` and `Build/NDHost` (in your order list, not upstream
  of `CodeSimulator`), `SpaceComplexity/Inclusions` (outside your order list). Your order list is
  unchanged; the base sorry set lost `exists_recordInitTM` (#95).
- **Nothing merged after your base touches your files.** Merged after it, and so not in your
  base: **MIG-1 stage S** (PR #98, on eight files upstream of you: `Simulation`, `Composition`, `Build/Wrappers`, `Encoding`,
  `ClassP/TimeConstructible`, `Build/Loop`, `Build/Primitives`, `Build/Catalog`). It renames 37
  catalog names by `audits/evidence/mig1/gate/scripts/renames.json`; **cite none of them**
  (`audits/evidence/b5a-canon-cont4/mig1s-renamed-names.txt`: 35 are private elsewhere and
  unreachable; the two public ones are `rewind_scan_heads` and `rewind_heads`). It is invisible
  to your base; the maintainer rebases at integration. Keep the region's `canon` prefix for your
  new privates. Also after your base: #99 (`Build/WindowRun`), #100 (`TimeHierarchy/Diagonal`),
  #101 (the ARM dedup payback), #102 (U2: the new `Build/StepBlockForward` and `UniversalK`, with
  `Codes2Tape`, `SelfUniversal` and the `TuringMachine` facade edited) and B6 F1 (#103:
  promotions in `Build/CounterLoop` and `SymbolLift`, upstream of you). None edits
  `CodeSimulator`; cite nothing they add.
- **MIG-1's final batch F-D lands after you.** It retires the six R3 canonical rows
  (`copyTM_run`, `transferTM_run`, `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`,
  `incrementTM_run_overflow`) and edits the one consumer in your region,
  `canonPreserveInstall`'s use of `copyTM_run` (lines 1274–1275). See ground rule 11.

## Parallel batches this round

None in `CodeSimulator.lean`. H1's continuation (`exists_uniformSimulator`) is briefed later. A
parallel change is invisible to your base and your screen.

## What this is

**The canonizer's fifth continuation** (phases 2–5 of the cont3 route). Your target is
`MachineFormat.exists_polyCanonizer`, a polynomial-time machine computing
`F.serialize (F.decode α)`. **It is already proved modulo exactly two private stubs**,
`exists_canonGrammarStage` and `exists_canonDecider`, by the landed glue over the proved strip
machine and the constant fallback. When both stubs are proved the canonizer is complete, and
with H1 the two-tape code scheme, the `EXPCOM` cluster and Baker–Gill–Solovay lose their last
canonizer admission.

**The user's two rules from cont3 stay in force** (2026-10-14): the `computesFunInTime_cond`
decomposition (validator, strip machine, constant fallback) is the route; and a partial may leave
named private stubs open, checked by an **axiom walk**: `sorryAx` reaches the headline only
through the named open stubs.

**What you build.** The physical grammar stage (the bounded unary reader C1, the record
validator C2, the nested table loops and the suffix check) and the validator that joins the
frozen parse front end to it. **Note 50 is prescribed and already elaborates**: once both stubs
are proved, the evidence file runs on the complete canonizer unchanged (phase 5).

**Read first:** the previous report (`canon-4-REPORT.md`), sections "Construction and
promotion contracts", "Exact continuation frontier" and "Note 50"; the cont3 brief
`briefs/b5a-fill-canon-cont3.md` (its routes A–D, gate guidance and pitfalls bind where this
brief does not replace them); `CodeSimulator.lean` lines 1–3313; `Build/CounterLoop.lean`
(`counterLoopTM`, its `_run_done`/`_run_escape` contracts, `counterLoop_time_le`,
`counterOverhead_le_of_le`, `counterValue`); the pre-ship overlay below.

**Pre-ship check (maintainer, at `ff4cab18`, against `oleans-ltip3`, the merged tip's replay;
`audits/logs/b5a-fill-canon-cont4-preship.log`):**
- `audits/evidence/b5a-canon-cont4/CanonCont4ImportProbe.lean.txt`: every public declaration
  this brief cites (130 `#check`s) resolves from `CodeSimulator`'s import context: 0 errors, 0
  warnings. **Re-run it after your delivery.**
- `audits/evidence/b5a-canon-cont4/CanonCont4Overlay.lean.txt` (generator `tools/mkoverlay.py`,
  input `tools/home.lean.txt`): the full `CodeSimulator.lean` with the prescribed block of 10
  declarations inserted at its home. **0 errors, 0 non-sorry warnings, 5 sorry warnings**: the
  two recommended component stubs, the two frozen stubs, and `exists_uniformSimulator`. The eight
  other prescribed declarations (seven lemmas and one definition) print the standard axioms
  only. The generator pins the two stub
  statements and the headline byte for byte and undoes its edit to reproduce the input.
- `audits/evidence/b5a-canon-cont4/CanonNote50.lean.txt` (prescribed): 0 errors, 0 warnings;
  `note50_cases` prints `sorryAx` today, through the two stubs only.
- The inherited probes `audits/evidence/wave1-statements/B5aStatementsProbe.lean.txt`,
  `audits/evidence/b5a/B5aContPreShip.lean.txt` and
  `audits/evidence/wave1-statements/S1210StatementsProbe.lean.txt` and the cont3 import probe
  `audits/evidence/b5a-canon-cont3/CanonCont3ImportProbe.lean.txt`: 0 errors (one probe-local
  admission each in the first and third); the S1210 census detects its probe-local
  `Complexity.exists_EXPCOM_decider`.

## Owned region and targets (modify these and nothing else)

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `CodeSimulator.lean:3132` | `exists_canonGrammarStage` (frozen statement) | C1–C5 | the prescribed bridges, C1, C2, the counter loop |
| 2 | `CodeSimulator.lean:3159` | `exists_canonDecider` (frozen statement) | B | `exists_canonParseFront`, target 1, `canonGrammar_verdict` |
| 3 | `CodeSimulator.lean:3268` | `Turing.MachineFormat.exists_polyCanonizer` | the landed glue (frozen) | targets 1–2 |

**The two stub statements are frozen verbatim** (as landed by #96; the generator checks them):

```lean
private lemma exists_canonGrammarStage (F : MachineFormat) :
    ∃ (m : ℕ) (S : Type) (_ : Fintype S) (_ : DecidableEq S) (G : MultiTapeTM m Bool S)
      (entry : S) (exit : Bool → S) (a : ℕ) (header : Fin m), Function.Injective exit ∧
      ∀ (x bits rest : List Bool), pairDecode x = some (bits, rest) →
        bits = (codeBitsNat bits).bits →
        canonGuardBlock F * (codeBitsNat bits + 1) ≤ rest.length →
        ∀ d : Cfg m Bool S x, d.state = some entry → d.output = [] →
          d.inputPos.val = 2 * bits.length + 3 →
          d.workTapes header = FinTM.bufferTape bits → d.workTapePos header = 0 →
          (∀ j, j ≠ header → d.workTapes j = FinTM.bufferTape [] ∧ d.workTapePos j = 0) →
          ∃ t ≤ a * (x.length + 1) ^ a,
            (G.runFrom d t).state =
              some (exit (canonGrammar F.k (codeBitsNat bits) rest).isSome) ∧
            (G.runFrom d t).output = [] ∧
            ∀ u < t, ∀ v, (G.runFrom d u).state ≠ some (exit v)

private lemma exists_canonDecider (F : MachineFormat) :
    ∃ (D : FinTM Bool) (a : ℕ), ∀ α : List Bool, ∃ b : Bool,
      D.ComputesInTime α [b] (a * (α.length + 1) ^ a) ∧
        (b = false → F.decode α = F.fallback) ∧
        (b = true → ∃ tail, F.scan α = some tail)
```

- **The canonizer region** is lines 190–3313: 93 declarations, 92 private and the headline
  (table `audits/evidence/b5a-canon-cont4/codesimulator-regions.tsv`). In it you own exactly the
  parts of ground rule 1. Frozen there: the 74 inherited privates of the earlier rounds
  (`skipRepeat_consumes` … `exists_canonParseFront`; `canonBits_value` has left for
  `Build/CounterLoop` as `Turing.foldr_bit_eq_ofDigits`), the 16 proved declarations of #96
  (`canonGrammar`, `scan_eq_canonGrammar`, `canonGrammar_verdict`, `canonStrip`,
  `canonStrip_append`, `canonFlatMap_last`, `actionBitsK_last`, `serializeK_last`,
  `canonScan_all`, `canonStrip_of_scan`, `canonStrip_split`, `canonStrip_boundary`,
  `canonTrimTM`, `canonEraseLast`, `canonTrim_run`, `exists_canonStripTM`), the two stub
  statements, and the headline's statement and glue body (3268–3313).
- **H1's region is off-limits:** `h1HostedVerdictTM`, `h1HostedVerdict_effect`,
  `h1HostedVerdict_accepts` (lines 3367–3453) and `exists_uniformSimulator` (3456–3567). The rest
  of H1 now lives in `Build/StepBlockLoop.lean` (not yours).
- **Frozen, neither batch's:** lines 1–189 (the module header, the layout, `MachineFormat`, the
  one-tape format); the section comment 3315–3322, the `section StepBlockClients`/`open StepBlock`
  lines and the four D4 clock declarations at 3324–3365; targets 3–8 in `Codes2Tape.lean` and
  `EXPCOM.lean`.
- **Not yours:** every other file.

### Prescribed home and block (binding where marked; elaborated in `CanonCont4Overlay.lean.txt`)

All new declarations live in the **home**, the blank line 3119 between the last line of
`exists_canonStripTM` (3118) and `exists_canonGrammarStage`'s docstring (3120), inside
`namespace MachineFormat`. Insert the eight declarations before the stubs first, exactly as in
`tools/home.lean.txt`; insert each recommended stub only once you have proved it (as stated or
restated). Replace the "(Prescribed.)", "(Prescribed;
proved.)" and "(Recommended shape; you may restate it.)" tags by ordinary docstring prose. Your
own further privates go in the same home, each after what it uses and before its first
consumer.

| Declaration | Status | Role |
|---|---|---|
| `canonSkipFin_iff` | proved | `codeSkipFin (n + 1) ys = some rest ↔ ∃ i ≤ n, ys = 1^i ++ false :: rest` |
| `canonSkipFields` (def) | given | a record's `4k + 4` fixed bits: input move, `k` × (write, move), output |
| `canonSkipAction_eq` | proved | `codeSkipActionK k n xs = (canonSkipFields k xs).bind (codeSkipState (n + 1))` |
| `canonSkipPair_cells` | proved | a successful pair skip consumes exactly its two cells |
| `canonSkipFields_cells` | proved | successful fixed fields consume exactly `4k + 4` cells |
| `canonSkipRepeat_add` | proved | repetition counts add |
| `canonSkipRepeat_mul` | proved | a repetition of repetitions is one repetition of the product |
| `canonSkipTable_eq` | proved | `codeSkipTableK k n = codeSkipRepeat (codeSkipRepeat (codeSkipActionK k n) (3^(k+1))) (n + 1)` |
| `exists_canonUnaryTM` | **stub, recommended** | C1, the bounded unary reader (generic) |
| `exists_canonRecordTM` | **stub, recommended** | C2, the action-record validator (generic, any `k`) |

The two recommended contracts share one shape: on a bank whose tape `bound` holds a binary word
`w` (head at the origin), every other tape blank, the native head at position `≥ 1`, the
component decides its field of `x.drop (d.inputPos.val - 1)` against the bound
`counterValue w`, with distinct live exits and strict cuts, silently, within
`a * (x.length + w.length + 1)`, restoring every work tape and head, and on acceptance leaving
the native head at the field's suffix. C1 decides `codeSkipFin (counterValue w + 1)`; C2 decides
`codeSkipActionK k (counterValue w)`. **User decision (2026-10-14): C1 and C2 are recommended
contracts you may restate, not a gated interface.** If you restate either, keep it private,
generic and linear, give your statement in `REPORT.md`, and re-check its composition into the
grammar stage yourself. The proved declarations may be taken verbatim. A prescribed
statement that is false or unusable is an escalation (ground rule 4).

**Why the header is the bound.** At the ready port the header tape holds `bits` with
`bits = (codeBitsNat bits).bits`, and `counterValue bits = codeBitsNat bits`
(`Turing.foldr_bit_eq_ofDigits`, since `codeBitsNat` is the `Nat.bit` fold). So C1 against the
header decides exactly `codeSkipFin (n + 1)` of `canonGrammar`, and C2 exactly
`codeSkipActionK k n`, with no restoration of the guard's counter and no unary expansion.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **Compose by the public combinators:** R2 seams (`seamCompTM`, `seamReleaseTM`), the phase
  host (`phaseHostTM`), R1 embedding (`embedEmitTM`, `embedEmitCfg_eq`), the counter loop
  (`counterLoopTM`, `counterLoopTM_run_done`, `counterLoopTM_run_escape`, or the contract-level
  `RoundContract.counterLoopDone_traj`/`counterLoopEscape_traj`), and the framed catalog rows
  (`copyTM_run_ofCfg`, `clearTM_run_ofCfg`, `writeConstTM_run_ofCfg`). Do not write a hand
  controller for a phase that a public row provides; never a second loop, seam or embedding
  transport.
- **Leaves you may write** (no public row provides them; each a small finite controller, like
  the inherited `guardBlockTM`, `canonBoolPopTM` and #96's `canonTrimTM`): the one-cell unary
  body, the one-cell terminator and tag checks, the native fixed-field validator, the native
  all-`true` suffix scan, and a one-step emitting halt. `inputFoldTM`/`inputCopyTM` start at
  native position `1` and traverse the whole input; `StepBlock.recordTM`, `recordSkipTM` and
  `succFieldTM` read canonized records on a work tape and validate nothing.
- **Promotion candidates** (list each with its contract in `REPORT.md`; notes only, not this
  round): C1, C2, any generic repetition loop you build, and #96's strip machine.

### The route (binding where it names a row)

**C1. The bounded unary reader** (`exists_canonUnaryTM`). Copy the bound to a blank scratch tape
(`copyTM_run_ofCfg` writes the interval and changes no other cell) and run `counterLoopTM` on the
copy with a one-cell body: a `true` moves right and returns to the anchor; a `false` or a blank
takes the exit without moving. Both host exits (`done` after `counterValue w` rounds, `escape`
earlier) go to one check of the current cell: a `false` moves right and accepts, anything else
rejects. Clear the copy (`clearTM_run_ofCfg`: the loop leaves `counterWord w r`, or all `true`
on `done`, on the same interval). The rounds are at most `min n (i + 1)`; the cost is linear in
the field and the bound's width, never in its value (`counterLoop_time_le`,
`counterOverhead_le_of_le`). The semantic side is `canonSkipFin_iff`. **Never expand the
bound in unary.**

**C2. The record validator** (`exists_canonRecordTM`). By `canonSkipAction_eq` a record is
`canonSkipFields k` then `codeSkipState (n + 1)`. Validate the `2k + 2` fixed pairs by one native
leaf, in order (the input move and the output with `a || !b`; each work tape's write with any
pair and its move with `a || !b`), failing fast on a blank; `canonSkipFields_cells` fixes its
native advance at `4k + 4`. Then read the tag: `false` ends the record; `true` is followed by C1,
embedded on the bound and a scratch tape by a public seam. **F7-1(c):** your leaf and
`StepBlock.recordTM` both walk a record's fixed fields; do not copy the step block's reader or
its trace (a screen pair between them is disclosed and measured).

**C3–C5. The grammar stage** (`exists_canonGrammarStage`: tape `header` = `bits`, every other tape
blank, native head at the remainder, decide `(canonGrammar F.k n rest).isSome`).
1. **The initial state.** C1 against the header, embedded on `{header, scratch}`.
2. **The table** (`canonSkipTable_eq`): `n + 1` states of `3^(k+1)` records. An inner public
   counter loop of `3^(k+1)` rounds (its counter word written by `writeConstTM_run_ofCfg` at the
   start of each state block) with C2 as its body, inside an outer public counter loop over the
   states: the header copied to an outer counter gives `n` rounds, so run one leading state block
   before the loop (`codeSkipRepeat f (n + 1) xs = (f xs).bind (codeSkipRepeat f n)` holds by
   definition), or install `canonCount bits` (value `n + 1`) with
   `incrementTM_run_succ_ofCfg` on a copy with a spare `false`. A body failure is the loop's
   escape. Prove the generic link once ("a counter loop whose body decides a skipper `r`
   decides `codeSkipRepeat r (counterValue c)`, failing fast"); `canonSkipRepeat_mul` and
   `canonSkipTable_eq` are the bridges. Do not copy `MathlibBridge.codeSkipRepeat_iter` or the
   H1 loop proofs in `Build/StepBlockLoop.lean`.
3. **The suffix.** Scan from the table's end to the right blank: all `true` accepts, any `false`
   rejects (a one-cell leaf).
4. **The ledger, fail-fast included.** Every successful record consumes at least `4k + 5` cells
   (`codeActionK_length`, `skipTable_consumes`, `canonSkipFields_cells`), and every record fails
   on a blank, so at most `|x| + 1` records run before a failure or the table's end, each
   charged `O(|x| + |bits|)` by C2's bound, and `|bits| ≤ |x|` (from `length_pairEncode` at the
   decoded pair). The counter loops add `counterOverhead` (at most `4r + 2|w|` per loop, by
   `counterOverhead_le_of_le`). The total is quadratic in `|x| + 1`, independent of the value
   `n`, which is the stage's `a * (x.length + 1) ^ a`. The guard's hypotheses (canonicality,
   `canonGuardBlock F * (n + 1) ≤ |rest|`) are available if a bound needs them.

**B. The validator** (`exists_canonDecider`). Embed the frozen front end
`exists_canonParseFront F` and the grammar stage in one bank: the front end on its own `C.k`
tapes, the stage's `header` tape on the front end's tape `0`, its other tapes on fresh tapes
beyond `C.k` (blank by the front end's embedding frame; `canonBlankLift`, `canonEmbedEq` and the
public `embedEmitCfg_eq`). Dispatch the front end's `exit true` to the stage's entry by a public
seam; send `exit false` and both stage exits to a one-step leaf that emits the bit and halts (one
`phaseHostTM` dispatch, as `canonExitDispatch` does). **The ready configuration is not a
`Cfg.ofWords` configuration:** its native head is at the remainder (`2|bits| + 3`) and its tape
`1` is the guard's residue; the stage's contract needs neither. The verdict laws are the front
end's reject clause and `canonGrammar_verdict`; the ledger is the front end's linear bound, plus
the stage's, plus the dispatches. Remove the stub's composition comment and placeholder
`obtain`s when you prove it.

**Phase 5. Note 50.** **User decision (2026-10-14): note 50 is a prescribed file, so phase 5 is
elaborate and print.** `audits/evidence/b5a-canon-cont4/CanonNote50.lean.txt` proves the four
cases (the zero-guard `2^128` header with a one-bit remainder, an encoded empty
header, a malformed pair, every padded well-formed code) from the public headline for a
zero-guard variant of the one-tape format, with one machine and one degree for all four. Copy it
unchanged to your zip's `evidence/CanonNote50.lean.txt`, elaborate it with
`scripts/lean_check_tree.sh` (0 errors), and quote its last line: for a complete delivery
`#print axioms note50_cases` shows no `sorryAx`. A partial says "pending" and quotes the print.

### Phases (for a partial; ground rule 9)

Stop, if you must, at the end of a phase, and say which. Phases 2–5 continue cont3's numbering:
2. **C1 and C2** proved (the two recommended stubs closed, or restated and proved).
3. **The grammar stage** proved (`exists_canonGrammarStage` closed).
4. **The validator** proved (`exists_canonDecider` closed): the headline is complete.
5. **Note 50** elaborated on the complete canonizer.

A partial may leave only the two frozen stubs open. **Insert a recommended stub only once it is
proved**, so a partial never adds an open admission. The freeze check for a partial is the
**axiom walk**: `sorryAx` reaches the headline only through the open frozen stubs.

## Gate guidance (binding)

- **Minor 5** (zero guard): the front end's `canonGuardBlock` already enforces both necessary
  conditions before any state-indexed work.
- **Note 47:** the generic writer `tableBitsK` against the frozen serializers stays in the item-8
  residual family; it is not new debt.
- **Note 50:** phase 5 above; permanent; no `#eval`, `native_decide` or `IO`.
- **Round-2 note 17:** keep the S1210 probe's detecting control.
- **The time-zero cut:** `exists_canonHeaderCall` and `exists_installCallTM` give the
  positive-time cut only; `canonStrictInstall` and the release adapter cover coincident anchors.
- **F7-1(c):** above (C2).

## Cited infrastructure (public and proved at the issue commit)

All of it resolves in `CanonCont4ImportProbe.lean.txt` (the cont3 list and twelve more).
- **Format and grammar layer:** as in cont3 (`CodeFormat.scan`, `parseFull`, `decode`,
  `canonical_eq`, `scan_full`, `parseFull_sound`, `decode_of_parseFull_none`,
  `decode_serialize_pad`; `codeSkipActionK`, `codeSkipWork`, `codeSkipFin`, `codeSkipState`,
  `codeSkipRepeat`, `codeSkipPair`, `codeActionK_length`; `pairDecode`, `pairEncode`,
  `length_pairEncode`, `length_bits_le_self`; `serializeK`, `codeSkipTableK`), and
  **`codeReadUnary`, `codeReadUnary_sound`, `codeReadUnary_append`**.
- **Counter layer:** `counterLoopTM`, `counterLoopCfg`, `counterLoopOrbit`, `roundOrbit`,
  `counterLoopTM_run_done`, `_run_escape`, `counterLoop_time_le`, `counterOverhead_le_of_le`,
  **`counterValue`, `counterValue_bits`, `foldr_bit_eq_ofDigits`, `counterWord`,
  `RoundContract.counterLoopDone_traj`, `RoundContract.counterLoopEscape_traj`**, `decrementTM`.
- **Hosts and framed rows:** as in cont3 (`seamCompTM`, `seamCompTM_run_ofCfg`,
  `seamCompTM_firstReturn_ofCfg`, `seamReleaseTM(_firstReturn)`, `phaseHostTM(_run)`,
  `embedEmitTM`, `embedEmitTM_runFrom`, `embedEmitTM_frame`, `embedEmitCfg_eq`,
  `copyTM_run_ofCfg`, `clearTM_run_ofCfg`, `writeConstTM_run_ofCfg`, `incrementTM_run_succ_ofCfg`,
  `tapeAction`, `inputMoveAction`, `step_of_inputMoveAction`, `step_of_tapeAction_move`), and
  **`catalog_trace_run`** (the two-pass trace #96's leaf uses).
- **H1's loop, for reference and the hazard only:** `StepBlock.loopTM`, `StepBlock.loopTM_run`.
- **Proved modulo, exactly:** none. A complete delivery has no `sorryAx` in your target.

## Ground rules (binding)

1. **File ownership, by declaration.** In `TuringMachine/CodeSimulator.lean`, and nowhere else,
   you own exactly these regions (lines at the issue tree):
   - **(a) the home**, the blank line 3119: the prescribed block, then your own `private`
     declarations. `private` only, and no `section`, `open` or `variable` that leaks past it.
   - **(b) `exists_canonGrammarStage`'s body**, the `sorry` on line 3147, and a flagged **"Fill
     appendix"** paragraph appended to its docstring (3120–3131). The statement (3132–3146) is
     frozen.
   - **(c) `exists_canonDecider`'s body**, lines 3164–3171, and a flagged appendix paragraph in
     its docstring (3149–3158). The statement (3159–3163) is frozen.
   - **(d) `exists_polyCanonizer`'s docstring**, lines 3173–3267: append a flagged **"Fill
     appendix (canonizer continuation 4)"** paragraph before the closing ` -/` (at the end of line
     3267). The existing text does not change. The statement and the glue (3268–3313) are frozen.

   **Not yours:** every other line, including the module header, every section heading, every
   existing declaration, #96's delivery and H1's region. The maintainer updates the module
   header and the status text in `Codes2Tape.lean`/`EXPCOM.lean` at integration; report any text
   that reads wrong. List every new declaration with its role.
2. **Statement freeze** over every landed declaration and both stub statements: no renames,
   re-signatures, restatements or attribution edits.
3. **Status text.** Only the headline's "(spec, fill pending — batch B5a)" tag may change, to
   "proved", and only for a complete delivery; flag it. No new public declaration.
4. **Escalation** on anything unprovable as stated, including a prescribed statement or a cited
   row that does not compose as the route says: stop on that item, record the obstruction, and
   continue with the rest.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Unchanged. No TCSlib import may be added. A Mathlib import only if a needed lemma
   requires it; flag it.
7. **One proof per shared argument.** Never re-walk a landed contract; never write a second
   host, loop, trace or layout lemma for something already public or already proved in your
   region (in particular #96's leaf and run lemmas, and `canonBlankLift`/`canonEmbedEq`).
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public
   and private declaration counts (base: 3,570 lines; 114 declarations, 11 public and 103
   private).
9. **Continuation budget.** A partial zip states the phase reached, the open stubs (each with a
   literal "Proof sketch"), and the headline's axiom walk. A partial is expected and fine; an
   unreported gap is not.
10. **D4 is complete:** no further deletions or moves.
11. **MIG-1 compatibility.** Keep `canonPreserveInstall` byte-identical (F-D rewrites its
    `copyTM_run` citation, lines 1274–1275, after you). Cite none of the six R3 rows anew; use
    their framed `_ofCfg` forms. Cite none of the 37 names stage S renames
    (`mig1s-renamed-names.txt`).

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**
(`audits/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**). The population is cont3's 44
files plus `Build/StepBlockLoop.lean`, where H1's counter-loop assembly now lives
(`audits/evidence/b5a-canon-cont4/b5a-canon-cont4-screen-population.txt`, 45 files). Use the
**declaration-keyed screen `audits/evidence/retrofit/copy-text-screen-v3.py`** (the campaign's
standard since the Diagonal Part 1 gate) on the repository paths; no staging is needed (labels are
basenames, unique in this population, and a short name repeated within one file gets its
namespace-qualified name). The base, at `ff4cab18`, is
`audits/logs/b5a-fill-canon-cont4-screen-base.txt`: **2,326 declarations, 2,576 pairs, 818,556
characters** (MEASURED with v3; about 26 minutes). v3 differs from the earlier v2 measurement
(2,574 pairs) by exactly CfgRecord's recorded instance pair (`Fintype`/`DecidableEq`, 66/66, both
ways) and the relabel of `Contract/Basic`'s repeated `trans` as `Turing.Segment.trans`. Against
the measurement at #96's branch head, the only other new pairs are five inside
`Build/RecordTable.lean` (#95's row 18, not yours).

```sh
P=audits/evidence/b5a-canon-cont4
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/b5a-canon-cont4-screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/b5a-canon-cont4-screen-population.txt) > /tmp/screen-after.txt
```

- **No new cross-file pair** with an owned-file declaration on one side, except the
  pre-disclosed ones (measure each).
- **Measured on the pre-ship overlay** (`audits/logs/b5a-fill-canon-cont4-screen-overlay.txt`;
  2,334 declarations, 2,576 pairs, 818,556 characters, v3): **the prescribed block adds no pair.** Its
  first draft paired `canonSkipFields` with `CodeFormat.codeSkipActionK` (76%, cross-file) and
  C1's statement with C2's (87%, through a `let` the screen reads as a body); both were removed
  before shipping. Nothing is pre-disclosed beyond the recorded pairs below and F7-1(c).
- **Recorded, add nothing to them:** `scan_grammar_guard`/`canonScan_all` (55%, cont3); the
  frozen `canonOffset_spec` reproducing `Turing.length_bits_le_self` (65/65 = 100%; backlog);
  the earlier canonizer in-file pairs; the uniform-code mirror pair (75%, CH34-D3); item 8's
  writer pairs.
- **Known hazards:** the fixed-field walk (F7-1(c)); the inherited native leaves
  (`guardBlockTM` and its step, run and orbit lemmas) and #96's `canonTrimTM`/`canonTrim_run`
  are the models for your leaves: a proof that reproduces one of them at 90% or more must be
  factored (parameterize, or cite); `MathlibBridge.codeSkipRepeat_iter` and the chapter-1 parser;
  the H1 counter-loop proofs in `Build/StepBlockLoop.lean`; the R1 reconstruction family
  (cite `canonEmbedEq`, `canonBlankLift`, `embedEmitCfg_eq`).
- List every new in-file pair with a one-line justification; at 90% or more it is a copy: factor
  it. Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each
  pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/b5a-fill-canon-cont4.txt` (**96 modules**: the upstream
  closure of your owned file and of every module downstream of it; since #94 it includes
  `Build/StepBlockLoop`):

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/b5a-fill-canon-cont4.txt )
  ```

  **Base sorry-warning set, 27** (`audits/logs/b5a-fill-canon-cont4-base-sorries.txt`, one entry
  per declaration; checked by elaborating all 96 modules). Yours: `CodeSimulator` 2 of its 3 (the
  two stubs). Record the base list by name first, and report any difference.
- **Final checks:**
  1. `CodeSimulator`: zero errors, and exactly one sorry warning, `exists_uniformSimulator` (plus,
     for a partial, each open frozen stub).
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     (**25** in all, with `CodeSimulator`'s one, for a complete delivery).
  3. Re-run `CanonCont4ImportProbe.lean.txt`, `CanonCont3ImportProbe.lean.txt`,
     `B5aStatementsProbe.lean.txt` and `B5aContPreShip.lean.txt`: 0 errors.
  4. Re-run `S1210StatementsProbe.lean.txt`: 0 errors, its census still detecting its probe-local
     admission.
  5. Elaborate the note-50 file: 0 errors; its axiom print (phase 5).
- **Axiom prints** for your target, every new private (in an in-module probe, as the previous
  report did), and targets 3–8 (`Turing.exists_uniformMachineCode2`,
  `Turing.exists_uniformMachineCode`, `Complexity.EXP_subset_POracle_EXPCOM`,
  `Complexity.POracle_EXPCOM_eq_EXP`, `Complexity.NPOracle_EXPCOM_eq_EXP`,
  `Complexity.POracle_EXPCOM_eq_NPOracle_EXPCOM`) and `Complexity.baker_gill_solovay`: within
  `[propext, Classical.choice, Quot.sound]`; for a complete delivery your target has no `sorryAx`
  and the others have it only through `exists_uniformSimulator`. For a partial, the headline's
  admission walk names exactly the open stubs.
- **Lint:** `python3 scripts/campaign_style_lint.py` over `TCSlib/Complexity/TuringMachine` and
  `TCSlib/Complexity/Diagonalization` (two runs), 0 FAIL. No new line over 100 characters and no
  new Lean linter warning in your region (the base file has none; its one wide line, 1127, is
  inherited).

## Out-of-scope sorries you will see (leave every one untouched)

- `TuringMachine/CodeSimulator`: exists_uniformSimulator (H1, a later brief)
- `TuringMachine/Build/RecordTable`: exists_tableFindTM, exists_tableAppendTM, exists_recordValidTM, exists_recordNextTM
- `Diagonalization/NTimeHierarchy`: exists_timed_universal_NDTM, exists_ndAcceptsWithin_decider, exists_codeNDTM_accepts_linear, ntime_hierarchy, ntime_hierarchy_of_pos, NTIME_linear_ssubset_square
- `TuringMachine/Build/StepClock`: exists_stepClockTMVia
- `TuringMachine/Build/WindowRun`: exists_windowLoopTM, exists_windowRunnerTM
- `TuringMachine/Build/NDHost`: ndWriterTM_run_block
- `TuringMachine/Build/Zone`: exists_zoneShiftInTM, exists_zoneShiftOutTM
- `TuringMachine/Build/InputWindow`: exists_inputWindowCopyTM
- `TuringMachine/Build/InputDevice`: exists_rulerTestTM, exists_rulerDeviceTM, exists_rulerHostTM
- `TuringMachine/SelfUniversal`: exists_selfStartupTM, exists_selfUniversal
- `TuringMachine/NDCodeSimulator`: exists_replayCanonizer, exists_ndInterpreterCore

If a proof seems to *need* one of these beyond a named citation, that is an escalation, not a
license.

## REPORT.md checklist

- [ ] The phase reached (2–5), the base hash and the ancestor check.
- [ ] Every new declaration with its role; the prescribed block as taken; C1/C2 as stated or
      restated; every flagged appendix and status update.
- [ ] The generic components' contracts (C1, C2, any repetition loop), as promotion candidates.
- [ ] Requested shared lemmas and escalations, or "none".
- [ ] Rule 11: `canonPreserveInstall` unchanged; no new citation of the six R3 rows or of the
      37 stage-S names (a grep of your diff).
- [ ] Duplication: both v2 screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the re-run probes; every axiom print; the headline's
      admission walk; the lint lines. The diff touches only your owned regions.
- [ ] Note 50: the file's elaboration and its axiom print (or "pending").

## Known pitfalls at this pin (hard-won)

- `Cfg.inputPos : Fin (|input| + 2)` starts at `1`; `0` and `|input| + 1` are the clamped blanks;
  cell `i` (from `0`) is at position `i + 1`, so the remainder after the doubled header starts at
  `2|bits| + 3`, and the suffix at position `p` is `x.drop (p - 1)`.
- `Cfg.ofWords` puts the native head at `1`; the front end's ready configuration is not of that
  form, and neither are the configurations inside the grammar stage.
- `counterLoopTM M` has `k + 1` tapes with the counter at `Fin.last k`; `counterLoopOrbit` is an
  `abbrev` of `roundOrbit` (a `simp only [counterLoopOrbit]` must also unfold `roundOrbit`). On
  `done` the counter interval is all `true`, on `escape` it holds `counterWord w r`: clear or
  re-write it before reuse. The counter's value convention is `counterValue w =
  Nat.ofDigits 2 (w.map Bool.toNat)`; `foldr_bit_eq_ofDigits` links it to `codeBitsNat`.
- `codeSkipRepeat r (n + 1) xs = (r xs).bind (codeSkipRepeat r n)` holds by `rfl`; the nested
  form of `codeSkipTableK` is not `rfl` to a single repetition (use `canonSkipTable_eq`).
- `ComputesFunInTime f T` unfolds with beta-redexes; `dsimp only` before rewriting an output.
- A halted source has `M.step c = c` and `M.outputSymbol c = none`.
- `seamCompTM_firstReturn_ofCfg` needs the callee's cut at `t = 0` as well.
- A structure update inside `runFrom` needs an ascription.
- `decide` cannot evaluate `Nat.bits`/`Nat.size`; the note-50 file avoids evaluating
  `(2 ^ 128).bits` by proving its decoding law for every `n`.
- `omega` with products and powers as atoms (`ring` first). The linter needs a literal "Proof
  sketch" before every `sorry` (partial only).
- The inherited canonizer lemmas take `(F : MachineFormat)` explicitly; call them as
  `exists_canonParseFront F`.
