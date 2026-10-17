# Ch3–4 fill campaign — B5a, the canonizer, continuation 3: the grammar (`MachineFormat.exists_polyCanonizer`, by declaration in `TuringMachine/CodeSimulator.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Confirm that `git merge-base --is-ancestor c8163e9bda3f53a999f4a4ad9164c17aa3c15cc4 HEAD` succeeds. That commit contains:
  - the fills-8 integration (`audits/fills-8-integration.md`), with the canonizer's previous
    report `audits/b5a-fill-agent-reports/canon-3-REPORT.md`;
  - H2-M (PR #88): the step block is the public module `Build/StepBlock.lean`
    (`Turing.StepBlock`); `CodeSimulator.lean` keeps its 105 staying declarations, with H1's
    clients in `section StepBlockClients` (`open StepBlock`); and #91, its proof sketches;
  - MIG-0b (PR #90): the contract library `Build/Contract/{Basic,Seam,Embed,Catalog,Lift}`;
    `Turing.counterLoopOrbit` is now an `abbrev` of `Turing.roundOrbit`;
  - the B6 hosts (PR #92) and the ARM minor fixes (PR #93), both merged (`1b6b972c`);
  - this round's inputs: the order list `briefs/orders/b5a-fill-canon-cont3.txt`, the base sorry
    set, the screen population and base, the pre-ship log, and the pre-ship probes with their
    generator (`audits/evidence/b5a-canon-cont3/`).

  If the check fails, **stop**.
- **Branch from exactly that commit**, not from the moving campaign tip:
  `git checkout -b fill/b5a-canon-cont3 c8163e9bda3f53a999f4a4ad9164c17aa3c15cc4`. Record the base hash in `REPORT.md`. Never
  rebase, merge or cherry-pick anything into your branch.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-b5a-canon-cont3.zip`,
  containing `REPORT.md`, the full modified source, a `git format-patch` series against your
  base, a git bundle, the final sweep log, the axiom log, the note-50 evidence file (gate
  guidance), both screen outputs, and `SHA256SUMS`.

## Base, line numbers and what landed before you

- **Lines in this brief are those of campaign commit `9d441a4e`.** Its Lean content equals
  `1b6b972c`, the merge of PRs #92 and #93, and the inputs commit `c8163e9bda3f53a999f4a4ad9164c17aa3c15cc4` adds no Lean
  change. `CodeSimulator.lean` has not changed since `759471be` (byte-identical, checked), so
  no line number in it moved. Every probe and measurement below was run at `9d441a4e`, against
  the olean snapshot of #92's replay.
- **PR #92 (the B6 hosts) has merged; it is in your base.** It changed four modules of your
  order list, `TuringMachine/StateRenaming`, `TuringMachine/Encoding`,
  `TuringMachine/Build/CfgRecord` (upstream of you) and the facade `TuringMachine` (downstream),
  and added five modules, four of them in your order list: `Build/StepClock`,
  `Build/WindowRun`, `Build/InputDevice`, and `TuringMachine/SelfUniversal`, which imports
  `CodeSimulator`. `SelfUniversal` cites no `CodeSimulator` declaration in code (its docstring
  names `Turing.oneTapeMachineFormat.serialize_eq` and `serializeK`). Its two contracts and the
  new hosts' six are sorried; they are in your base sorry set. `Encoding` and `CfgRecord` are in
  your screen population, and so is `SelfUniversal`.
- **PR #93 (comments and imports in 33 ARM files) has merged.** It touches no module of your
  order list and no file of your screen population.
- **Nothing is open against your files.** The one change in preparation is **MIG-1's stage S**,
  being built at the tip now. It adds statements to modules upstream of you (`Simulation`,
  `Composition`, `Build/Wrappers`, `Encoding`, `ClassP/TimeConstructible`, `Build/Loop`,
  `Build/Primitives`, `Build/Catalog`) and makes several of today's private witnesses public
  under new names in `Turing.FinTM` and `Turing` (for example `idTM`, `constTM`, `condTM`,
  `timedCondTM`, `pairDiagTM`, `lengthBitsTM`, `loopHostTM`, `callTM`, `prependTM`,
  `incFixedTM`, `pairValidTM`, `appendBitTM`). It is invisible to your base; the maintainer
  rebases at integration. Keep the region's `canon` prefix (or the prescribed names) for your
  new privates, so no name of yours meets one of S's.
- **MIG-1's final batch F-D lands after you.** It retires the six R3 canonical rows
  (`copyTM_run`, `transferTM_run`, `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`,
  `incrementTM_run_overflow`) and edits the one consumer in your region,
  `canonPreserveInstall`'s use of `copyTM_run` (lines 1281–1282); that edit is rebased onto
  your result. See ground rule 11.

## Parallel batches this round

None in `CodeSimulator.lean`. H1's continuation (`exists_uniformSimulator`) is briefed later,
after a separate H1-harvest gate lands. The other work in flight (MIG-1's stage S, the §13d
design notes, the gates) owns no file of yours. A parallel change is invisible to your base and
your screen.

## What this is

**The canonizer's fourth continuation** (user, 2026-10-14: the canonizer goes now; F-D's
CodeSimulator site rebases onto it). Your target is `MachineFormat.exists_polyCanonizer`, a
polynomial-time machine computing `F.serialize (F.decode α)`. With H1 it closes the last two
admissions under the two-tape code scheme, the `EXPCOM` cluster and Baker–Gill–Solovay.

**What is proved, privately, in your file** (75 declarations, lines 187–2659): the format-free
grammar bounds, the physical binary-header loader, the fail-fast binary length guard, the
canonical-header check, the successor counter, the guard front end, and **the total two-port
parse front end** `exists_canonParseFront` (fills-8):

```lean
private lemma exists_canonParseFront (F : MachineFormat) :
    ∃ (C : FinTM Bool) (entry : C.State) (exit : Bool → C.State) (a : ℕ),
      4 ≤ C.k ∧ Function.Injective exit ∧ ∀ x : List Bool,
        ∃ t ≤ a * (x.length + 1), ∃ verdict : Bool,
          let start := Cfg.ofWords (input := x) entry (fun _ => [])
          let e := C.tm.runFrom start t
          e.state = some (exit verdict) ∧ e.output = [] ∧
          (∀ u < t, ∀ q, (C.tm.runFrom start u).state ≠ some (exit q)) ∧
          (verdict = false → F.decode x = F.fallback) ∧
          (verdict = true → ∃ bits rest,
            pairDecode x = some (bits, rest) ∧ bits = (codeBitsNat bits).bits ∧
            canonGuardBlock F * (codeBitsNat bits + 1) ≤ rest.length ∧
            e.inputPos.val = 2 * bits.length + 3 ∧
            ∀ j, j.val ≠ 1 →
              e.workTapes j = FinTM.bufferTape (canonReadyWords C.k bits j) ∧
                e.workTapePos j = 0)
```

At the ready port tape `0` holds the canonical header `bits` (binary `n = codeBitsNat bits`),
tape `2` the address `canonOffset bits`, every tape from `3` on is blank, all with heads at the
origin; tape `1` is the guard's residue, unspecified.

**What remains** is the previous report's frontier, steps 1–6: the grammar after the front end,
the generic record validator, the emission, the headline's ledger and note 50. This brief fixes
**the top-level decomposition** (prescribed below and elaborated): the headline is the public
timed branch `Turing.FinTM.computesFunInTime_cond` over a polynomial **validator** (one verdict
bit), a polynomial **strip machine** (the input with its all-`true` suffix removed) and the
constant fallback. On accepted inputs the strip is exactly the canonical serialization
(`canonStrip_of_scan`, proved). The emission therefore needs no saved prefix boundary.
**User decision (2026-10-14): this decomposition is accepted in place of the prefix-copy
emission** of the docstring sketch and the earlier briefs; your fill appendix records the
refinement.

**Read first:** the previous report (`canon-3-REPORT.md`), sections "Proved progress" and
"Exact continuation frontier"; the earlier canonizer briefs `briefs/b5a-fill-canon-cont2.md`,
`briefs/b5a-fill-canon-cont.md` and `briefs/b5a-fill-canon.md` (routes, gate guidance and
pitfalls still bind where this brief does not replace them); `CodeSimulator.lean` lines 1–2749;
`Build/StepBlock.lean` lines 170–1125 (the fixed-field reader, the successor-field leaf and the
whole-record skipper, for the hazard of F7-1(c)); the pre-ship overlay below.

**Pre-ship check (maintainer, at `9d441a4e`, against #92's replay snapshot;
`audits/logs/b5a-fill-canon-cont3-preship.log`):**
- `audits/evidence/b5a-canon-cont3/CanonCont3ImportProbe.lean.txt`: every public declaration
  this brief cites (118 `#check`s) resolves from `CodeSimulator`'s import context: 0 errors,
  0 warnings. **Re-run it after your delivery.**
- `audits/evidence/b5a-canon-cont3/CanonCont3Overlay.lean.txt` (generator
  `tools/mkoverlay.py`, inputs `tools/home.lean.txt` and `tools/headline.lean.txt`): the full
  `CodeSimulator.lean` with the prescribed block of 13 declarations inserted at its home and the
  headline's `sorry` replaced by the prescribed glue. **0 errors, 0 non-sorry warnings, 4 sorry
  warnings**: the three stubs and `exists_uniformSimulator`. The headline is proved there from
  the stubs. The ten proved prescribed declarations print the standard axioms only; the
  headline's `sorryAx` comes only through the stubs. The generator undoes its two anchored edits
  and checks that this reproduces the input byte for byte.
- The inherited probes `audits/evidence/wave1-statements/B5aStatementsProbe.lean.txt`,
  `audits/evidence/b5a/B5aContPreShip.lean.txt` and
  `audits/evidence/wave1-statements/S1210StatementsProbe.lean.txt`, re-run at the tip: 0 errors
  (one probe-local admission each in the first and third); the S1210 census detects its
  probe-local `Complexity.exists_EXPCOM_decider`.

## Owned region and targets (modify these and nothing else)

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `TuringMachine/CodeSimulator.lean:2746` | `Turing.MachineFormat.exists_polyCanonizer` | the prescribed glue (take it verbatim) | the two prescribed stubs |
| 1a | home (line 2660) | `exists_canonStripTM` (prescribed stub) | copy, trim, forward (route A) | public input copy, a trim leaf, the emit call |
| 1b | home (line 2660) | `exists_canonDecider` (prescribed stub) | the front end, the grammar stage, a verdict leaf (route B) | `exists_canonParseFront`, `canonGrammar_verdict` |
| 1c | home (line 2660) | `exists_canonGrammarStage` (recommended stub) | bounded unary checks and the record loop (route C) | counter loop, framed rows, seams |

- **The canonizer region** is lines 187–2749 of `CodeSimulator.lean`: 76 declarations, 75 private
  and the headline (table `audits/evidence/b5a-canon-cont3/codesimulator-regions.tsv`). In it you
  own exactly the three parts of ground rule 1; the 75 inherited privates are frozen:
  `skipRepeat_consumes`, `skipSymbols_consumes`, `skipTable_consumes`, `scan_grammar_guard`,
  `guardedScan`, `guardedScan_eq`, `decode_of_grammar_guard`, `grammar_guard_states`,
  `canonHeader`, `canonHeader_length`, `exists_canonHeaderCall`, `guardPhase`, `guardBlockTM`,
  `guardCfg`, `guardBlock_step`, `guardBlock_run`, `guardBlock_blank`, `guardBlock_short`,
  `guardTime`, `guardBlock_interior`, `binaryGuardTM`, `binaryGuardStart`, `guardBlock_orbit`,
  `guardBlock_segment`, `binaryGuard_done`, `binaryGuard_escape`, `canonBitsOK`,
  `canonBits_fold`, `canonBits_value`, `canonBits_of_last`, `canonBits_bits`,
  `canonBitsOK_iff`, `canonCount`, `canonCount_spec`, `canonBitsTM`, `canonBitsTM_run`,
  `exists_canonHeaderSeam`, `exists_canonCountTM`, `canonVerdictTM`, `canonVerdictTM_run`,
  `exists_canonHeaderBitsTM`, `canonHeaderOK`, `canonHeaderOK_iff`,
  `scan_eq_none_of_canonHeaderOK`, `exists_canonHeaderOKTM`, `canonGuardBlock`,
  `canonGuardBlock_pos`, `decode_of_canonGuard`, `canonGuard_run`, `canonStrictInstall`,
  `canonEmbedEq`, `canonEmbedWords`, `canonPreserveInstall`, `exists_canonHeaderCountSeam`,
  `canonOffset`, `canonOffset_spec`, `exists_canonOffsetTM`, `canonReadyWords`,
  `exists_canonReadySeam`, `exists_canonSeekOnBank`, `exists_canonGuardFront`,
  `canonBoolPopTM`, `canonBoolPop_run`, `exists_canonBoolBranch`, `exists_canonHeaderBranch`,
  `decode_of_canonHeader`, `canonSeam_avoids`, `canonCounterBank`, `canonGuard_onBank`,
  `exists_canonGuardReady`, `exists_canonGuardFrontStrict`, `canonBlankLift`,
  `exists_canonCheckedFront`, `canonExitDispatch`, `exists_canonParseFront`.
  Cite them; never change them.
- **H1's region is off-limits:** lines 2803–3184 (`h1ClockTM`, `h1HostedClockTM`,
  `h1RoundTime`, `h1RoundTime_spec`, `h1Clock_orbit`, `h1Clock_round`, `h1Clock_effect`,
  `h1HostedClock_effect`, `h1HostedVerdictTM`, `h1HostedVerdict_effect`,
  `h1HostedVerdict_accepts`) and lines 3187–3285 (`exists_uniformSimulator`, its docstring and
  body). They belong to a later brief. Do not read them as a model for your phases either: they
  build a clock, not a parser.
- **Frozen, neither batch's:** lines 1–186 (the module header, the layout, `MachineFormat`, the
  one-tape format), the section comment at 2751–2758, the `section StepBlockClients` and
  `open StepBlock` lines and the four D4 clock declarations at 2764–2801 (`summaryClock`,
  `summaryClock_correct`, `summaryClock_accepts`, `summaryClock_zero`); the six filled targets
  3–8 and their privates in `Codes2Tape.lean` and `EXPCOM.lean`.
- **Not yours:** every other file, including `Build/StepBlock.lean`, `CodeFormat.lean`,
  `CodeParser.lean`, `Universal*.lean`, `MathlibBridge.lean`, `Codes2Tape.lean`, `EXPCOM.lean`
  and the facades.

### Prescribed homes and privates (binding; elaborated in `CanonCont3Overlay.lean.txt`)

All new declarations live in the **home**, the blank line 2660 between the last line of
`exists_canonParseFront` (2659) and `exists_polyCanonizer`'s docstring (2661), inside
`namespace MachineFormat`. Insert the prescribed block there first, in this order, exactly as in
`tools/home.lean.txt`; replace the "(Prescribed.)", "(Prescribed; proved.)", "(Prescribed; to
be proved.)" and "(Recommended shape; you may restate it.)" tags by ordinary docstring prose and
remove the composition comment in `exists_canonDecider`'s body when you prove it. Your own
further privates go in the same home, each after what it uses and before its first consumer.

| Declaration | Status in the probe | Role |
|---|---|---|
| `canonGrammar` (def) | given | the fixed grammar on the remainder: `codeSkipFin (n + 1)`, `codeSkipTableK k n`, the all-`true` suffix |
| `scan_eq_canonGrammar` | proved | at the ready port, `F.scan α = canonGrammar F.k n rest` |
| `canonGrammar_verdict` | proved | the validator's verdict law at the ready port |
| `canonStrip` (def) | given | `(α.reverse.dropWhile id).reverse` |
| `canonStrip_append` | proved | `canonStrip (u ++ [false] ++ tail) = u ++ [false]` for an all-`true` tail |
| `canonFlatMap_last` | proved | a nonempty concatenation of words ending in `false` ends in `false` |
| `actionBitsK_last` | proved | every record ends in `false` (its successor field) |
| `serializeK_last` | proved | every fixed `k`-record serialization ends in `false` |
| `canonScan_all` | proved | a successful scan's suffix is all `true` |
| `canonStrip_of_scan` | proved | `F.scan α = some tail → canonStrip α = F.serialize (F.decode α)` |
| `exists_canonStripTM` | **stub, binding statement** | a polynomial machine computing `canonStrip` |
| `exists_canonGrammarStage` | **stub, recommended statement** | the physical grammar from the ready layout |
| `exists_canonDecider` | **stub, binding statement** | the polynomial validator |

The two binding statements, as elaborated:

```lean
private lemma exists_canonStripTM :
    ∃ (M : FinTM Bool) (a : ℕ),
      M.ComputesFunInTime canonStrip (fun n => a * (n + 1) ^ a)

private lemma exists_canonDecider (F : MachineFormat) :
    ∃ (D : FinTM Bool) (a : ℕ), ∀ α : List Bool, ∃ b : Bool,
      D.ComputesInTime α [b] (a * (α.length + 1) ^ a) ∧
        (b = false → F.decode α = F.fallback) ∧
        (b = true → ∃ tail, F.scan α = some tail)
```

**The headline's body is the prescribed glue** (`tools/headline.lean.txt`, proved in the probe;
take it verbatim): `choose` the verdict function from `exists_canonDecider`, take the strip
machine and `FinTM.computesFunInTime_const (F.serialize F.fallback)`, join them by
`FinTM.computesFunInTime_cond`, identify the branch's function with
`F.serialize (F.decode α)` (`canonStrip_of_scan`, or the decider's rejection law), and absorb
the ledger into `d = c·(a + b + e + 1) + a + b + 1`.

The proved prescribed declarations may be taken verbatim. If a prescribed statement turns out
false or unusable, that is an escalation (ground rule 4): record the obstruction and continue.
`exists_canonGrammarStage` is a recommendation: you may restate it (keep it private and keep
the properties below), but then say so and give your statement in `REPORT.md`.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **Compose by the public combinators:** the timed branch (`FinTM.computesFunInTime_cond`), R2
  seams (`seamCompTM`, `seamReleaseTM`), the phase host (`phaseHostTM`), R1 embedding
  (`embedEmitTM`, `embedEmitCfg_eq`), the counter loop (`counterLoopTM` with
  `counterLoopTM_run_done`/`_escape`), the framed catalog rows (`copyTM_run_ofCfg`,
  `clearTM_run_ofCfg`, `writeConstTM_run_ofCfg`, `seekEndTM_run_ofCfg`, `seekStartTM_run_ofCfg`,
  `inputCopyTM_run_ofCfg`) and the calls (`FinTM.exists_emitCallTM`, `exists_installCallTM`). Do
  not write a hand controller for a phase that a public row provides.
- **Leaves you may write** (no public row provides them; each is a small finite controller,
  like the inherited `guardBlockTM` and `canonBoolPopTM`): a native fixed-field validator, a
  one-cell unary body, one-cell tag and terminator checks, the native all-`true` suffix scan, a
  one-tape trailing-`true` eraser, and a one-step emitting halt. `inputFoldTM` and
  `inputCopyTM` start at native position `1` and traverse the whole input, so they cannot read
  from the remainder; `StepBlock.recordTM`, `recordSkipTM` and `succFieldTM` read already
  canonized records on a work tape and validate nothing.
- **The generic components are the reusable pieces** (promotion candidates; list each with its
  contract in `REPORT.md`): the bounded unary reader against a binary bound (route C1), the
  action-record validator (C2), and the strip machine (A). None of them mentions
  `MachineFormat`.

### The route (binding where it names a row)

**A. The strip machine** (`exists_canonStripTM`). From the initial configuration (native head at
`1`): copy the native input to a work tape (`inputCopyTM_run_ofCfg`); a one-tape leaf walks to
the word's right end, erases the trailing `true` cells moving left until a `false` or the left
delimiter, and returns to the origin; then forward the word to the output with
`FinTM.exists_emitCallTM` and the identity machine (`FinTM.computesFunInTime_id`), and halt.
The trimmed tape is `FinTM.bufferTape (canonStrip α)`; every phase is linear. Mind the word
without any `false` (everything is erased) and the call's `Cfg.ofWords` entry layout (tape `0`
the argument, every other tape blank, every head at the origin, native head at `1`). The
catalog's `seekEndTM`/`seekStartTM` are field-layout seeks (they stop on a double blank and
need nonempty fields); use them only if they fit.

**B. The validator** (`exists_canonDecider`). Embed the front end and the grammar stage in one
bank: the front end on its own `C.k` tapes, the grammar stage's `header` tape on the front end's
tape `0` and its other tapes on fresh tapes beyond `C.k` (blank by the front end's embedding
frame; `canonBlankLift` and `canonEmbedEq` are the inherited transports, `embedEmitCfg_eq` the
public one). Dispatch the front end's `exit true` to the grammar's entry by a public seam; send
the front end's `exit false` and both grammar exits to a one-step leaf that emits the bit and
halts (one `phaseHostTM` dispatch, as `canonExitDispatch` does). The verdict laws are the front
end's reject clause and `canonGrammar_verdict`. The ledger is the front end's linear bound plus
the grammar stage's polynomial bound plus the dispatches. Every configuration you start a seam
from is the front end's ready configuration, which is **not** a `Cfg.ofWords` configuration:
its native head is at the remainder and its tape `1` is unspecified.

**C. The grammar stage** (`exists_canonGrammarStage`: from tape `header` = `bits`, every other
tape blank, native head at the remainder, decide `(canonGrammar F.k n rest).isSome`).

1. **The bounded unary reader** (generic). `codeSkipFin (n + 1)` accepts `1^i 0` with `i ≤ n`.
   Use the header itself as the binary bound: its value is `n`
   (`Nat.ofDigits 2 (bits.map Bool.toNat) = codeBitsNat bits`, the inherited
   `canonBits_value`). Copy it to a blank scratch counter (`copyTM_run_ofCfg` writes the interval
   and changes no other cell) and run `counterLoopTM` with a one-cell body: on
   `true` move right and return to the anchor; on `false` or a blank take the exit without
   moving. Both host exits (`done` after `n` rounds, `escape` earlier) go to one check of the
   current cell: `false` moves right and succeeds; `true` or a blank fails. The rounds are at
   most `min n (i + 1)`, so the cost is linear in the field and the bound's width, never in `n`
   (`counterLoop_time_le`, `counterOverhead_le_of_le`). Alternatively install `canonCount bits`
   (value `n + 1`) on a copy with `incrementTM_run_succ_ofCfg` after appending a spare `false`;
   either is fine, but never expand `n` in unary.
2. **The action-record validator** (generic, parameterized by `k` and a tape-resident binary
   bound `n`). `codeSkipActionK k n` reads `4k + 4` fixed bits in pairs (the input move and the
   output with `a || !b`, each work tape's write with any pair and its move with `a || !b`),
   then `codeSkipState (n + 1)`: a tag `false` ends the record; a tag `true` is followed by the
   bounded unary reader. Validate the fixed fields by one native leaf (fail fast on a blank),
   then the tag, then the unary part. Its success contract consumes exactly the prefix
   `codeSkipActionK k n` consumes and leaves the native head at the returned suffix; it
   restores the bound tape and leaves every other tape as it found it (or as your loop's
   invariant needs); its two exits are distinct with strict cuts; its cost is linear in the
   record and the bound's width.
3. **The table.** `codeSkipTableK k n = codeSkipRepeat ((fun r => codeSkipRepeat r 3)^[k + 1]
   (codeSkipActionK k n)) (n + 1)`: `n + 1` states of `3^(k+1)` records. Run the record
   validator under public counter loops: an inner loop of `3^(k+1)` rounds (the counter word
   written by `writeConstTM_run_ofCfg` each time) inside an outer loop over the states (the
   header copy with one leading block, or `canonCount`), the validator's failure as each loop's
   escape. Prove the nesting identity you need by induction over `codeSkipRepeat`; do not copy
   `MathlibBridge.codeSkipRepeat_iter`'s proof.
4. **The suffix.** Scan the native input from the table's end to the right blank: all `true`
   accepts, any `false` rejects (a one-cell leaf).
5. **The ledger.** Every record consumes at least `4k + 5` cells (`codeActionK_length`,
   `skipTable_consumes`) and every round fails fast on input exhaustion, so at most `|x| + 1`
   records run, each charged `O(|x| + |bits|)`, and `|bits| ≤ |x|` (`canonHeader_length`): a
   quadratic total, independent of the value `n`. The inherited guard's hypotheses
   (canonicality, `canonGuardBlock F * (n + 1) ≤ |rest|`) are available if a bound needs them.

**D. The semantic bridges.** `scan_eq_canonGrammar` and `canonGrammar_verdict` (prescribed) are
the only scanner facts route B needs; `canonStrip_of_scan` is the only one the glue needs. Cite
`guardedScan_eq`, `decode_of_grammar_guard`, `skipTable_consumes`, `F.skipTable_eq` and
`codeSkipTableK` where your component contracts meet the grammar; do not re-derive them.

### Phases (for a partial; ground rule 9)

Stop, if you must, at the end of a phase, and say which. **User decision (2026-10-14): a partial
that lands the glue may move the headline's `sorry` into the named private stubs**
(`exists_canonDecider`, `exists_canonGrammarStage`, and `exists_canonStripTM` if it were still
open). For such a partial the integration's freeze check is an **axiom walk**: `sorryAx` reaches
the headline only through those stubs, and through nothing else.
1. **The strip machine** proved, with the prescribed block and the glue landed: the headline is
   then proved modulo `exists_canonDecider` (and `exists_canonGrammarStage`). Until this phase
   is complete, keep the headline's original `sorry` and do not insert the stubs.
2. **The generic components** C1 and C2, with their contracts proved.
3. **The grammar stage** (C3–C5).
4. **The validator** (B): the headline is complete.
5. **Note 50** on the complete canonizer (gate guidance).

## Gate guidance (binding)

- **Minor 5** (zero guard): the front end's `canonGuardBlock` already enforces both necessary
  conditions before any state-indexed work; early rejection yields exactly the fallback.
- **Note 47:** the generic writer `tableBitsK` against the frozen serializers stays in the item-8
  residual family, with its bridges; it is not new debt.
- **Note 50** (permanent sanity cases at fill, on the complete physical canonizer). In an
  evidence file `CanonNote50.lean.txt` that imports `TCSlib.Complexity.TuringMachine.CodeSimulator`
  (not in the module), prove as `example`s from the public headline, for a format with
  `guard = 0` (for example `oneTapeMachineFormat` with its guard set to `0`): (a) the header of
  `2^128` with a short remainder: the canonizer halts within `d·(|α| + 1)^d` with output
  `F.serialize F.fallback`; (b) an encoded empty header; (c) a malformed pair encoding; (d) one
  small well-formed code with `true` padding round-trips (`CodeFormat.decode_serialize_pad`).
  No `#eval`, `native_decide` or `IO`. Include the file and its elaboration log in the zip. A
  partial says "pending".
- **Round-2 note 17:** keep a detecting control: the S1210 probe's census must still detect its
  probe-local admission after you land.
- **The time-zero cut:** `exists_canonHeaderCall` and `exists_installCallTM` give the
  positive-time cut only; `canonStrictInstall` and the release adapter cover coincident anchors.
- **F7-1(c), the fixed-field walk:** your native validator and `StepBlock.recordTM` both walk a
  record's fixed fields (pre-disclosed). Do not copy the step block's reader or its trace; a
  screen pair between them is disclosed and measured, and the maintainer factors it.

## Cited infrastructure (public and proved at the issue commit)

All of it resolves in `CanonCont3ImportProbe.lean.txt`.
- **Format layer:** `CodeFormat.scan`, `parseFull`, `decode`, `canonical`, `canonical_eq`,
  `scan_full`, `parseFull_sound`, `decode_of_parseFull_none`, `decode_of_guard_lt`,
  `decode_serialize_pad`; `actionBitsK`, `codeSkipActionK`, `codeReadActionK(_sound)`,
  `codeEraseActionK`, `codeActionK_length`, `codeSkipWork`; `codeSkipFin`, `codeSkipState`,
  `codeSkipRepeat`, `codeSkipPair`, `codeReadFin(_sound)`, `codeEraseFin`, `codeEraseState`,
  `codeBitsNat(_bits)`; `pairDecode`, `pairEncode`, `eq_pairEncode_of_pairDecode`,
  `length_pairEncode`, `unaryFin`, `optStateBits`, `length_bits_le_self`; `serializeK`,
  `codeSkipTableK`, `MachineFormat.serialize_eq`, `MachineFormat.skipTable_eq`.
- **Step block (H2):** `workReadsK`, `tableBitsK`, `StepBlock.length_workReadsK`,
  `StepBlock.recordWidth` (the hazard rows `recordTM`, `recordSkipTM`, `succFieldTM`).
- **Machines and time:** `FinTM.ComputesInTime(.mono)`, `ComputesFunInTime`,
  `computesInTime_iff`, `FinTM.bufferTape`, `FinTM.computesFunInTime_const`, `_id`, `_comp`,
  `_cond`, `Cfg.ofWords`, `initCfg_ofWords`, `stateWord`, `MultiTapeTM.runFrom_add`,
  `runFrom_succ_eq_step'`, `step_of_halt`, `outputSymbol_of_halt`.
- **Hosts:** `seamCompTM`, `seamCompTM_run_ofCfg`, `seamCompTM_firstReturn_ofCfg`,
  `seamReleaseTM(_firstReturn)`, `phaseHostTM(_run)`, `embedEmitTM`, `embedEmitCfg`,
  `embedEmitTM_runFrom`, `embedEmitTM_frame`, `embedEmitCfg_eq`, `embedEmitCfg_selected_tape`,
  `_selected_pos`; `counterLoopTM`, `counterLoopCfg`, `counterLoopOrbit`, `roundOrbit`,
  `counterLoopTM_run_done`, `_run_escape`, `counterLoop_time_le`, `counterOverhead_le_of_le`,
  `decrementTM`; `FinTM.exists_installCallTM`, `exists_emitCallTM`, `exists_inputCallTM`,
  `exists_inputSeekTM`.
- **Framed rows** (they survive MIG-1): `copyTM_run_ofCfg`, `clearTM_run_ofCfg`,
  `transferTM_run_ofCfg`, `compareTM_run_ofCfg`, `incrementTM_run_succ_ofCfg`,
  `incrementTM_run_overflow_ofCfg`, `seekEndTM_run_ofCfg`, `seekStartTM_run_ofCfg`,
  `skipTM_run_ofCfg`, `scanTM_run_ofCfg`, `inputCopyTM_run_ofCfg`, `inputFoldTM_run_ofCfg`,
  `writeConstTM_run_ofCfg`, `writeAdvTM_run_ofCfg`, `tapeAction`, `inputMoveAction`,
  `step_of_inputMoveAction`, `step_of_tapeAction_move`.
- **Proved modulo, exactly:** none. A complete delivery has no `sorryAx` in your target.

## Ground rules (binding)

1. **File ownership, by declaration.** In `TuringMachine/CodeSimulator.lean`, and nowhere else,
   you own exactly these regions (lines at the issue tree):
   - **(a) the home**, the blank line 2660: the prescribed block, then your own `private`
     declarations. `private` only, and no `section`, `open` or `variable` that leaks past it.
   - **(b) `exists_polyCanonizer`'s docstring,** lines 2661–2745. The existing text, including
     the five earlier fill appendices, does not change. Append a flagged **"Fill appendix
     (canonizer continuation 3)"** as its own paragraph before the closing ` -/` (line 2745).
   - **(c) its body,** the `sorry` on line 2749. The signature, lines 2746–2748, is frozen.

   **Not yours:** every other line of the file, including the module header (its Status and
   "Main results"), every section heading, every existing declaration, and H1's region. The
   maintainer updates the module header and the status text in `Codes2Tape.lean`/`EXPCOM.lean`
   at integration; report any header text that reads wrong. List every new declaration with
   its role. A lemma that belongs in a shared file is written privately, flagged in `REPORT.md`
   as a promotion candidate, and promoted by the maintainer (`workflow.md` §4, rule 1).
2. **Statement freeze** over every target and every landed declaration: no renames,
   re-signatures, restatements or attribution edits. Docstrings stay; a flagged "Fill appendix"
   is expected wherever your proof refines or replaces a sketch's route.
3. **Status text.** Only your target's "(spec, fill pending — batch B5a)" tag, inside your
   docstring region, may change, to "proved", and only for a complete delivery; flag it. No new
   public declaration.
4. **Escalation** on anything unprovable as stated, including a prescribed statement or a cited
   row that does not compose as the route says: stop on that item, record the obstruction, and
   continue with the rest.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Unchanged. No TCSlib import may be added. A Mathlib import is allowed only if a
   needed lemma requires it; flag it.
7. **One proof per shared argument.** Cite the landed rows the route names; never re-walk a
   landed contract inside a target, and never write a second host, loop, trace or layout lemma
   for something already public or already proved in your region.
8. **Size.** No cap; file size alone is not a driver (user, 2026-10-11). Report the file's final
   line count and its public and private declaration counts (base: 3,290 lines, 105
   declarations, 11 public and 94 private).
9. **Continuation budget.** If your budget runs out, deliver a partial zip whose `REPORT.md`
   states the phase reached, which `private` helpers remain `sorry` (each with a literal "Proof
   sketch"), and which proved declarations are proved modulo them. A partial is expected and
   fine; an unreported gap is not.
10. **D4 is complete** (the first delivery's ledger): no further deletions or moves.
11. **MIG-1 compatibility.** Keep `canonPreserveInstall` byte-identical, statement and proof:
    F-D rewrites its `copyTM_run` citation (lines 1281–1282) after you. Add no new citation of
    the six R3 rows (`copyTM_run`, `transferTM_run`, `clearTM_run`, `compareTM_run`,
    `incrementTM_run_succ`, `incrementTM_run_overflow`); use their framed `_ofCfg` forms. No
    other public that MIG-1 changes is visible from your file: its 22 other touched publics in
    your import closure keep their names and statements
    (`audits/evidence/b5a-canon-cont3/mig1-retired-rows.txt`).

## Duplication governance (binding)

Run the text-level screen **before and after** (`audits/TEMPLATE.md` failure mode 5; `policy.md`,
**Duplication**). The population is widened this round to every file this brief cites: the 34
files of last round's population and ten more, among them `Build/StepBlock.lean` and the new
downstream importer `SelfUniversal.lean`
(`audits/evidence/b5a-canon-cont3/b5a-canon-cont3-screen-population.txt`, 44 files). **The
screen labels files by basename and treats two declarations with the same basename and name as
one, so it is run on byte-identical copies under flattened, path-encoded names** (the path below
`TCSlib/Complexity/` with `/` replaced by `.`; `tools/flatscreen.py` stages and checks them).
The base, at `9d441a4e`, is `audits/logs/b5a-fill-canon-cont3-screen-base.txt`:
**2,290 declarations, 2,568 pairs, 816,241 characters** (MEASURED; about 25 minutes).

```sh
P=audits/evidence/b5a-canon-cont3
python3 -I $P/tools/flatscreen.py . $P/b5a-canon-cont3-screen-population.txt /tmp/flat-before
python3 -I audits/evidence/retrofit/copy-text-screen.py /tmp/flat-before \
  $(cat /tmp/flat-before/NAMES.txt)
# after: stage your CodeSimulator.lean (it is the repository's file on your branch)
python3 -I $P/tools/flatscreen.py . $P/b5a-canon-cont3-screen-population.txt /tmp/flat-after
python3 -I audits/evidence/retrofit/copy-text-screen.py /tmp/flat-after \
  $(cat /tmp/flat-after/NAMES.txt)
```

- **No new cross-file pair** with an owned-file declaration on one side, except the
  pre-disclosed ones below (measure each).
- **Pre-disclosed, measured on the pre-ship overlay** (the same population with the overlay as
  `CodeSimulator.lean`: 2,301 declarations, 2,569 pairs, 816,393 characters;
  `audits/logs/b5a-fill-canon-cont3-screen-overlay.txt`): exactly one new pair,
  `scan_grammar_guard` reproduces the prescribed `canonScan_all` (152/278 = 55%, in-file). Both
  decompose the frozen scanner `CodeFormat.scan` along its binds; one bounds the remainder, the
  other reads the padding test. It is recorded; quote it, and add nothing to it. No prescribed
  declaration forms a cross-file pair.
- **Known hazards:**
  - **the fixed-field walk** (F7-1(c)): `StepBlock.recordTM`, `recordSkipTM` and `succFieldTM`;
    a pair between them and your validator is pre-disclosed (measure it); never copy their
    traces;
  - **the inherited leaves**: `guardBlockTM` and its step, run and orbit lemmas are the model for
    a native leaf; a new leaf proof that reproduces one of them at 90% or more must be factored
    (parameterize your leaf, or cite the inherited lemma);
  - the chapter-1 parser (`CodeParser`, `MathlibBridge`, `codeSkipRepeat_iter`): never copy its
    parse proofs; the frozen grammar laws are the bridge;
  - your earlier in-file pairs (`canonHeader_length`/`canonHeaderOK_iff` 56%;
    `exists_canonOffsetTM`/`exists_canonCountTM`, `canonStrictInstall`/`exists_canonHeaderSeam`
    57–68%; `exists_canonReadySeam` and `exists_canonHeaderCountSeam` against `canonBlankLift`
    68%) are recorded; add nothing to them;
  - **the R1 configuration-reconstruction family** (backlog F7-1(b)): cite `canonEmbedEq`,
    `canonEmbedWords`, `canonBlankLift` or the public `embedEmitCfg_eq`; never write another
    reconstruction proof;
  - the canonical-bit lemmas against `NotTimeConstructible`'s and `UHaltMachine`'s (F6-1(c)):
    cite the inherited `canonBits_*`;
  - the pre-disclosed mirror pair (`exists_uniformMachineCode2`/`exists_uniformMachineCode`,
    75%; backlog CH34-D3) and the forced writer pairs of item 8's residual family
    (`oneTapeFormat` 85%, `codeTable2Bits` 67%, `Code2TM.serialize` 56%): add nothing to them;
  - **a base pair newly visible with `Encoding` in the population:** the frozen
    `canonOffset_spec` reproduces `Turing.length_bits_le_self` (65/65 = 100%; recorded for the
    maintainer). Cite `length_bits_le_self` for any `|bits m| ≤ m` bound; never inline it again;
  - the downstream `NDCodeSimulator.exists_replayCanonizer` (a different canonizer, by
    composition): nothing to share.
- List every new in-file pair with a one-line justification. At 90% or more it is a copy:
  factor it.
- Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/b5a-fill-canon-cont3.txt` (**95 modules**: the upstream
  closure of your owned file and of every module downstream of it, at the issue tree; since #92
  it includes `SelfUniversal` and the facade's new hosts):

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/b5a-fill-canon-cont3.txt )
  ```

  **Base sorry-warning set, 27** (`audits/logs/b5a-fill-canon-cont3-base-sorries.txt`, one entry
  per declaration; checked by elaborating all 95 modules). Yours: `CodeSimulator` 1 of its 2
  (your target). Record the base list by name first, and report any difference.
- **Final checks:**
  1. `CodeSimulator`: zero errors, and exactly one sorry warning, `exists_uniformSimulator`
     (plus, for a partial, the headline's own or each prescribed stub still open).
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     (**26** in all, with `CodeSimulator`'s one, for a complete delivery).
  3. Re-run `CanonCont3ImportProbe.lean.txt` and the inherited probes
     `B5aStatementsProbe.lean.txt` and `B5aContPreShip.lean.txt`: 0 errors.
  4. Re-run `S1210StatementsProbe.lean.txt`: 0 errors, its census still detecting its
     probe-local admission.
  5. Elaborate `CanonNote50.lean.txt` (complete delivery): 0 errors.
- **Axiom prints** for your target, for every new private (in an in-module probe, as the
  previous report did), and for targets 3–8 (`Turing.exists_uniformMachineCode2`,
  `Turing.exists_uniformMachineCode`, `Complexity.EXP_subset_POracle_EXPCOM`,
  `Complexity.POracle_EXPCOM_eq_EXP`, `Complexity.NPOracle_EXPCOM_eq_EXP`,
  `Complexity.POracle_EXPCOM_eq_NPOracle_EXPCOM`) and `Complexity.baker_gill_solovay`: within
  `[propext, Classical.choice, Quot.sound]`; for a complete delivery your target has no
  `sorryAx` and the others have it only through `exists_uniformSimulator`. For a partial that
  landed the glue, print the headline's admission walk: `sorryAx` only through the open stubs.
- **Lint:** `python3 scripts/campaign_style_lint.py` over `TCSlib/Complexity/TuringMachine` and
  `TCSlib/Complexity/Diagonalization` (two runs), 0 FAIL. No new line over 100 characters and no
  new Lean linter warning in your region (the base file has none).

## Out-of-scope sorries you will see (leave every one untouched)

- `TuringMachine/CodeSimulator`: exists_uniformSimulator (H1, a later brief)
- `TuringMachine/Build/RecordTable`: exists_tableFindTM, exists_tableAppendTM, exists_recordInitTM, exists_recordValidTM, exists_recordNextTM
- `Diagonalization/NTimeHierarchy`: exists_timed_universal_NDTM, exists_ndAcceptsWithin_decider, exists_codeNDTM_accepts_linear, ntime_hierarchy, ntime_hierarchy_of_pos, NTIME_linear_ssubset_square
- `TuringMachine/Build/NDHost`: ndWriterTM_run_block
- `TuringMachine/Build/Zone`: exists_zoneShiftInTM, exists_zoneShiftOutTM
- `TuringMachine/Build/InputWindow`: exists_inputWindowCopyTM
- `TuringMachine/Build/StepClock`: exists_stepClockTMVia (#92)
- `TuringMachine/Build/WindowRun`: exists_windowLoopTM, exists_windowRunnerTM (#92)
- `TuringMachine/Build/InputDevice`: exists_rulerTestTM, exists_rulerDeviceTM, exists_rulerHostTM (#92)
- `TuringMachine/SelfUniversal`: exists_selfStartupTM, exists_selfUniversal (#92)
- `TuringMachine/NDCodeSimulator`: exists_replayCanonizer, exists_ndInterpreterCore

If a proof seems to *need* one of these beyond a named citation, that is an escalation, not a
license.

## REPORT.md checklist

- [ ] 1/1, or the phase reached (rule 9); the base hash and the ancestor check.
- [ ] Every new declaration with its role; the prescribed block as taken (any deviation, with
      its reason); `exists_canonGrammarStage` as stated or restated; every flagged appendix,
      status update and import.
- [ ] The generic components' contracts (C1, C2, A), as promotion candidates.
- [ ] Requested shared lemmas and escalations, or "none".
- [ ] Rule 11: `canonPreserveInstall` unchanged; no new citation of the six R3 rows (a grep of
      your diff).
- [ ] Duplication: both flattened screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the re-run probes; every axiom print; the lint lines. The
      diff touches only your owned regions.
- [ ] Note 50: the four cases, executed (or "pending" for a partial).
- [ ] For a partial that landed the glue: the headline's axiom walk, naming exactly the open
      stubs (user decision 2).

## Known pitfalls at this pin (hard-won)

- `Cfg.inputPos : Fin (|input| + 2)` starts at `1`; `0` and `|input| + 1` are the clamped blanks
  (`moveInputPos`); compare lifted positions by `.val`. Cell `i` (from `0`) of the input is at
  position `i + 1`, so the remainder after the doubled header starts at `2|bits| + 3`.
- `Cfg.ofWords` puts the native head at `1`. The front end's ready configuration is not of that
  form; a row that needs `Cfg.ofWords` (the calls, `inputCopyTM`, `inputFoldTM`) cannot start
  there without a seek.
- A halted source has `M.step c = c` and `M.outputSymbol c = none` (`step_of_halt`,
  `outputSymbol_of_halt`).
- `seamCompTM_firstReturn_ofCfg` needs the callee's cut at `t = 0` as well;
  `exists_installCallTM` gives it only for `0 < t`.
- A structure update inside `runFrom` needs an ascription:
  `({c with state := some s, inputPos := 1} : Cfg k Bool S x)`.
- `ComputesFunInTime f T` unfolds to `∀ x, ComputesInTime x (f x) (T x.length)` with
  beta-redexes; `dsimp only` before rewriting the output, and state the decider's `T₀`
  explicitly before `computesFunInTime_cond` (the glue does both).
- `counterLoopOrbit` is an `abbrev` of `roundOrbit` since MIG-0b: a `simp only [counterLoopOrbit]`
  must also unfold `roundOrbit`. `counterLoopTM M` has `k + 1` tapes with the counter at
  `Fin.last k`; `counterWord` freezes at zero while the machine wraps: stay at
  `r ≤ value + 1`. On `done` the counter interval is all `true`: re-copy or re-write it before
  reuse.
- The step block's names changed at H2-M (`h1RecordTM` is `StepBlock.recordTM`, and so on;
  `audits/evidence/h2/r2/H2-design-r2.md`, Appendix A); `CodeSimulator` reaches them through
  `Turing.StepBlock.…`, opened only inside `section StepBlockClients`.
- `decide` cannot evaluate `Nat.bits`/`Nat.size`: use `Nat.size_eq_bits_len`,
  `Nat.lt_size_self`, `Nat.lt_size`, `Nat.size_one`.
- `omega` with products and powers as atoms (`ring` first to expose them). The linter needs a
  literal "Proof sketch" before every `sorry` (partial only).
- `canonCount` appends a high zero before incrementing, so its width is `|header| + 1` and its
  value `n + 1`, also for the empty header. The header itself has value `n`.
- A failed `pairDecode` and an encoded empty header both yield `[]` as the first component; the
  front end already keeps the separate pair-validity test.
- The inherited canonizer lemmas take `(F : MachineFormat)` explicitly although the section has
  `variable (F : MachineFormat)`; call them as `exists_canonParseFront F`.
