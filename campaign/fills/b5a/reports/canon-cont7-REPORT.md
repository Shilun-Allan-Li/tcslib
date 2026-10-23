# B5a canon cont7 — checkpoint 5 (Megafill A, item 3 of 3; the stub proved, final checks running)

**Target:** `exists_canonGrammarStage` (`TuringMachine/CodeSimulator.lean:4965` at the base).
**Status: COMPLETE — all six checkpoints; the frozen stub is PROVED** (statement untouched,
no new admission; `CodeSimulator` now carries exactly one sorry, `exists_uniformSimulator`,
which is outside this fill). Note 50 passes with a clean axiom print; the final battery
(sweep, probes, seal, lint, axioms) is recorded below.
Base `6cfee54474e3d954e3395f9d9eab5d025452a8dd` (ancestor check passed at session start);
branch `fill/b5a-canon-cont7` created 2026-10-22T10:58:17Z; budget: the rest of the session.
No first edit was required (imports unchanged, no overlay).

## Checkpoint 1 — the record round, instantiated

New privates at home (a), each proved (no new admission):
- `canonStageSkip_suffix`: a successful `codeSkipActionK` skip returns a suffix of its input
  (via `codeEraseActionK` + `codeReadActionK_sound`, as the brief's route prescribes).
- `canonStageSuffix_drop`: dropping to a suffix's start recovers it.
- `canonStageRoundSpec`: **the `spec` argument of `canonCounterRepeat`, discharged at
  `exists_canonRecordRound`**: with `valid` := C2's bank preconditions plus empty output,
  `tail d := x.drop (d.inputPos.val − 1)`, `r := codeSkipActionK k (counterValue w)`, and the
  per-round budget `B·(|x| + |w| + 1)` (`B` the round's own constant, which already carries the
  adapter's `+2`), each round is positive, interior-cut, exits by the skip verdict, and on
  success preserves the bank and lands the native head at the skipped suffix (the tail update).
  `τ` is the classical choice of the round's time.

## Checkpoint 2 — the inner block (one outer round, adapter-wrapped)

New privates at home (a), each proved (no new admission):
- `canonStageBuffer_none`: the buffer tape is blank at and beyond its word's length.
- `canonStageInnerSpec`: **one outer round's body as a first-return block.** The machine is
  `canonReturnAdapter` around the seam `Rin := seamCompTM W L`, where `W` is
  `writeConstTM` writing `w₀ := (3^(k+1)).bits` on a fresh inner-counter tape (`Fin.last m`,
  `2|w₀| + 2` steps, `writeConstTM_run_ofCfg`), and `L := counterLoopTM N₀ anchor₀
  (some escape₀)` loops checkpoint 1's record round over that counter
  (`canonCounterRepeat` with `canonStageRoundSpec`'s `spec`; `counterValue w₀ = 3^(k+1)` by
  `counterValue_eq` + `counterValue_bits`). The seam's two legs are joined by
  `seamCompTM_runFrom_left/right` (both-port cut — no definite endpoint port is needed), the
  junction into the loop's layout by `counter_cfg_eq` with `Fin.lastCases`. Contract: from a
  C2 bank (bound word `w` on `bound.castSucc`, inner counter blank, output empty, head inside
  the input) at the adapter's entry anchor, the block runs a positive time
  `≤ (3^(k+1)·(B₀+4) + 6|w₀| + 12)·(|x| + |w| + 1)`, cuts both ports strictly inside, exits by
  the verdict `(codeSkipRepeat (codeSkipActionK k (counterValue w)) (3^(k+1)) ·).isSome` on
  the native suffix, and on success restores the bank (inner counter confined to its window,
  blank outside, head back at the origin) and lands the head at the skipped suffix.

## Checkpoint 3 — the table block (the outer loop, n-free)

New privates at home (a), each proved (no new admission):
- `canonStageBlock_consumes`: one successful inner block consumes at least one input cell
  (route step 5's per-record count: `codeActionK_length` through `skipRepeat_consumes`).
- `canonStageOuterSpec`: **the whole fixed table grammar as a first-return block.** The
  machine is `canonReturnAdapter` around `counterLoopTM N₂ anchor₂ (some escape₂)` (checkpoint
  2's block as the loop body), its counter a word `u` of value `counterValue w + 1` — the
  incremented header copy the assembly will supply (route step 3's `incrementTM` option).
  `canonRepeat_orbit` gives the per-round chain and the dichotomy; `counterLoopTM_run_done` /
  `_run_escape` close the two runs; `canonSkipTable_eq` reads the verdict as
  `codeSkipTableK k (counterValue w)` on the native suffix. **The budget is independent of the
  counter value**: every round that returns consumes an input cell, so at most `|x| + 1`
  rounds run (telescoped through the orbit), each charged checkpoint 2's linear budget, the
  overhead settled by `counterOverhead_le` / `counterOverhead_le_of_le`; the block's bound is
  `(B₂ + 20)·(|x| + |w| + |u| + 1)²`. On success: empty output, head inside the input, and the
  native head at the surviving suffix (no tape restoration is needed after the table).

## Checkpoint 4 — the stage front (counter preparation and the range check)

New privates at home (a), each proved (no new admission). The front is a nine-phase
`phaseHostTM`: seven framed catalog rows prepare the outer counter — copy the header
(`copyTM`), skip past the copy (`skipTM`), one step back (`walkTM`, the lockstep walk over
the empty word), write the spare `false` pad (`writeConstTM`), skip past the pad, skip back
over the padded word (`skipBackTM`), increment (`incrementTM_run_succ_ofCfg`; `incFixed` on
the padded copy never overflows, `incFixed_eq_none_iff_replicate`) — then C1 runs embedded by
the forwarding transformer (`embedEmitTM`, reconstructed at the junction by
`embedEmitCfg_select`), both ports dispatched to a parking phase.
- Definitions: `canonStageHaltTM` (the parking machine), `canonStagePh` (+ its `Fintype` and
  `DecidableEq` builders), `canonStageFamily`, `canonStageRed`, `canonStageFr` (the host),
  `canonStageBank` (the bank shape).
- Lemmas: `canonStageInc_value` and `canonStagePad_value` (the incremented padded copy has
  value `counterValue w + 1`), `canonStageBank_fields`, `canonStageCut_leg` (one leg of the
  strict cut, by the host tag), `canonStageLeg0` … `canonStageLeg6` (one lemma per row:
  the row's framed run, the host's replay, the dispatch, and the junction into the next
  bank), and **`canonStageFrontSpec`**: from the stub's entry bank the front runs within
  `(ua + 33)·(|x| + |w| + 1)`, exits by C1's `codeSkipFin` verdict with a strict cut, is
  silent, preserves the header, leaves every other tape blank, and delivers the incremented
  header copy on the outer counter — C1's contract is a hypothesis, discharged by the
  assembly at `exists_canonUnaryTM`.
- Engineering note: a first, monolithic proof of the front exhausted elaboration memory (the
  Lean process was killed by the OS twice); the landed version hoists the host's family,
  dispatch table and bank into shared definitions and proves one lemma per leg, elaborating
  the whole file in ~80 seconds.

## Amendment before checkpoint 5 (disclosed statement changes to own checkpoints)

The stub demands `(G.runFrom d t).output = []` on **every** exit path, but checkpoints 1–3
asserted silence only on the success (`∀ ys, … = some ys →`) branches. Before the assembly,
each of this fill's own checkpoint lemmas gained one unconditional clause (statement
amendments to this fill's own privates only; the frozen base statements and the stub are
untouched):
- `canonStageRoundSpec` now also asserts `(N.runFrom d (τ d)).output = []` (checkpoint 1);
  the round's existing endpoint-identity proof already carried it.
- `canonStageInnerSpec` now also asserts `(N.runFrom d (τ d)).output = []` (checkpoint 2).
  Its loop section was re-derived on `canonRepeat_orbit` (the in-file orbit lemma checkpoint
  3 already used) so the failed-round branch owns a per-round output chain; the write row and
  both seam cuts are unchanged.
- `canonStageOuterSpec` now also asserts `(P.runFrom d (τ d)).output = []` (checkpoint 3),
  threaded through the same orbit chain and the adapter transport.
All three re-verified together: `CodeSimulator`'s own check, 0 errors, the same 2 expected
sorry warnings (the stub, 7482, and `exists_uniformSimulator`, 8095); no new line exceeds
100 characters.

## Checkpoint 5 — the assembly (the stub proved)

New privates at home (a), each proved, and **the frozen stub `exists_canonGrammarStage`
discharged** (statement untouched; no new admission anywhere):
- `canonGramPh` (+ its `Fintype` and `DecidableEq` builders), `canonGramFamily`,
  `canonGramRed`, `canonGramG`: a four-phase `phaseHostTM` — the stage front (checkpoint 4's
  host, instantiated with `exists_canonUnaryTM`'s reader through a piecewise embedding into
  the shared tape space `(m₃ + 2) + mU`), the table block (checkpoint 3's machine, embedded by
  the forwarding transformer `embedEmitTM` along `Fin.castLEEmb` and wrapped in
  `seamReleaseTM`, whose fresh entry makes the coincident entry/return anchor a genuine
  positive-time port), the native suffix test `canonSuffixTM`, and the parking machine.
- `canonGramCut_leg` (one leg of the strict cut, by the host tag), `canonGramFin_suffix`
  (a successful `codeSkipFin` skip returns a suffix, via `codeEraseFin` +
  `codeReadFin_sound`), `canonGramMapComp` (double control relabelling composes),
  `canonGramLedger` (the three legs with their dispatch steps fit under the single exponent
  `2·AF + 9·A₃ + 8`).
- The stub's proof: the decoded pair gives the geometry (`eq_pairEncode_of_pairDecode`,
  `length_pairEncode`, so the native suffix at entry is `rest`); the value bridge
  `counterValue bits = codeBitsNat bits` (`counterValue_eq` + `foldr_bit_eq_ofDigits`); the
  front decides `codeSkipFin (n+1) rest` and delivers the incremented header copy `u`; on
  success the table decides `codeSkipTableK F.k n` on the surviving suffix
  (`seamReleaseTM_firstReturn` on the return path, `seamReleaseTM_runFrom_pos` on the escape
  path — the escape's silence is checkpoint 3's amended unconditional output clause); the
  suffix test decides `List.all id`; each verdict parks. `canonGrammar`'s three binds fold
  the three verdicts into the required exit bit on every path, and every pre-exit control
  state carries a non-parking tag (the strict cut).

**Axiom walk (`evidence/logs/item3-cp5-axioms.log`; earlier checkpoints' in
`item3-cp1-axioms.log` … `item3-cp4-axioms.log`):** every checkpoint-5 private, the proved
stub `exists_canonGrammarStage`, the validator composition `exists_canonDecider` and the
headline `exists_polyCanonizer` all report within `[propext, Classical.choice, Quot.sound]`
— **no `sorryAx` reaches the headline** (the brief's complete-delivery criterion).

**The final sweep** (`evidence/logs/item3-final-sweep.log`): the order list's remaining
modules 66–118, rebuilt on the delivered tree — **53/53 OK, 0 failures**; the sorry census
over the whole 118-module list (bootstrap modules 1–65 + this sweep) is exactly the base's
38-entry set (`campaign/fills/b5a/logs/b5a-fill-canon-cont7-base-sorries.txt`) minus the
proved stub: 37, with `CodeSimulator` down to `exists_uniformSimulator` alone.

**Verification at this checkpoint:** `CodeSimulator`'s own check: 0 errors, exactly **one**
sorry warning — `exists_uniformSimulator` (line 8672 at delivery), the file's other, out-of-scope
admission; the stub's warning is gone. No new line exceeds 100 characters (the file's one
102-character line, 1145, is the base's). The 118-module order list was bootstrapped
upstream-first: modules 1–65 (through `CodeSimulator`) built with 0 FAILs
(`evidence/logs/item3-bootstrap.log`); the remaining modules 66–118 are rebuilt by the final
sweep (`evidence/logs/item3-final-sweep.log`).

## Screens (duplication governance)

Both v3 screens on cont4's 45-file population, one at a time, `nice -n 10`.
- **Before** (`evidence/logs/item3-screen-before.log`, on a pristine worktree at the base
  commit): **2,419 declarations, 2,633 pairs, 824,240 characters** — exactly the base
  reference (`campaign/fills/b5a/logs/b5a-fill-canon-cont7-screen-base.txt`). The launch
  deviation is disclosed below.
- **After** (`evidence/logs/item3-screen-after.log`, on the delivered tree): **2,455 declarations, 2,692 pairs, 885,426 characters**; 59 new pairs, none gone,
  all `CodeSimulator.lean` ↔ `CodeSimulator.lean`.
- **No new cross-file pair with an owned-file declaration on one side.** The first after
  screen (at the seal-hardening commit) found one — `canonStageInc_value` reproducing
  `Convention.lean::incFixed_length` at 59% (its induction skeleton) — so the lemma was
  restructured as an equation-style recursion (the disclosed dedup commit) and the final
  screen shows the pair gone. Nothing was added to the recorded pairs.
- **New in-file pairs** (all `CodeSimulator.lean` ↔ `CodeSimulator.lean`; one-line
  justifications):
  - `canonStageLeg0`…`canonStageLeg6` pairwise (51–94%): the seven stage-front rows are one
    phase-host leg pattern instantiated at seven catalog rows — the hoisted per-leg shape is
    the engineering fix for the monolith's elaboration blow-up (checkpoint 4's note), and
    each leg differs in its row lemma, window word and head arithmetic.
  - `canonGramCut_leg` ↔ `canonStageCut_leg` (97%): the same one-leg cut argument at the two
    hosts' different phase families (`Fin 9` vs `Fin 4` with different fibers); a shared
    form would need a public abstraction over the family, which rule 9 (no new public
    declarations) forbids.
  - `canonStagePh_fintype` ↔ `canonStagePh_deceq`, `canonGramPh_fintype` ↔
    `canonGramPh_deceq`, and the cross pairs between the two families (54–86%): four
    instance builders that are each a `match` listing `inferInstanceAs` per phase — forced
    by the dependent `match` over `Fin n`, no content to share.
  - `canonStageLeg* / canonStage*Spec` ↔ `canonGramMapComp` (55–66%): the `Cfg.ext` +
    `mapState` field-equation block (the seal-safe junction idiom) recurs wherever a host
    junction is reconstructed; `canonGramMapComp` is precisely the shared lemma that
    collapses two renamings, and the legs' remaining echoes are its application pattern.
  - `canonStageBlock_consumes` ↔ `skipTable_consumes` (61%/50%): the new per-record
    consumption count follows the base's in-file table-consumption proof on the same
    parser laws — in-file, and the base lemma is cited (not re-proved) where it applies.
- **New copies: none** (no new pair reproduces a source at 90%+ outside the deliberately
  parallel in-file host legs listed above, and no hazard-list declaration is involved).

**Deviation on the before screen, disclosed:** the first launch (11:00Z, on the working tree
before any item-3 edit) looked dead at 11:45Z (empty log, no match in a narrow pgrep), so an
authoritative replacement was launched on a worktree pinned to the base commit at 11:46Z; the
original process then turned out to be alive, sharing the same log file, and was killed at
11:49Z (≈3 minutes of two screens at once, both `nice -n 10`; the survivor's log was opened
fresh by the replacement, so no interleaving reached it).

## File size and diff scope

`CodeSimulator.lean`: 8,696 lines (5,590 at the base; +3,106). The whole diff against the
base is **one file, 3,107 insertions, 1 deletion** — the deleted line is the stub's `sorry`;
every insertion is at home (a) between `canonCounterRepeat` and the stub's docstring, or the
stub's own proof body. The lint's two `CodeSimulator` WARNs (the >1000-line split note and
the three base publics without adjacent lemmas) are the base's own, unchanged in kind.

## Lint (`evidence/logs/item3-lint-tm.log`, `item3-lint-diag.log`)

`python3 -I scripts/campaign_style_lint.py` on the delivered tree:
`TCSlib/Complexity/TuringMachine` — **0 FAIL, 63 WARN over 82 files** (the base's exact
numbers); `TCSlib/Complexity/Diagonalization` — **0 FAIL, 1 WARN over 5 files** (the
base's). No new line over 100 characters (the file's one 102-character line, 1145, is the
base's) and no new Lean linter warning in the owned region (the own-check log is
warning-free but for the expected `exists_uniformSimulator` sorry).

## The final axiom battery (`evidence/logs/item3-final-axioms.log`)

On the delivered tree (all downstream modules rebuilt by the sweep first):

    'Turing.MachineFormat.exists_polyCanonizer' : [propext, Classical.choice, Quot.sound]
    'Turing.exists_uniformMachineCode2'         : [propext, sorryAx, Classical.choice, Quot.sound]
    'Turing.exists_uniformMachineCode'          : [propext, sorryAx, Classical.choice, Quot.sound]
    'Complexity.EXP_subset_POracle_EXPCOM'      : [propext, sorryAx, Classical.choice, Quot.sound]
    'Complexity.POracle_EXPCOM_eq_EXP'          : [propext, sorryAx, Classical.choice, Quot.sound]
    'Complexity.NPOracle_EXPCOM_eq_EXP'         : [propext, sorryAx, Classical.choice, Quot.sound]
    'Complexity.POracle_EXPCOM_eq_NPOracle_EXPCOM' : [propext, sorryAx, Classical.choice, Quot.sound]
    'Complexity.baker_gill_solovay'             : [propext, sorryAx, Classical.choice, Quot.sound]

The headline is `sorryAx`-free. For targets 3–8 and `baker_gill_solovay`, the sweep's census
shows the tree's only remaining admissions are the base's 37 (the stub removed), and the
canonizer cone's only direct admission is `exists_uniformSimulator` (the import probes'
closure census) — the brief's expectation for a complete delivery.

## Probe re-runs (`evidence/logs/item3-probes.log`)

All five on the delivered tree, 0 errors each: `CanonCont7ImportProbe` (the 224 `#check`s),
continuation 3's import probe, `B5aStatementsProbe`, `B5aContPreShip`, and
`S1210StatementsProbe` (its census still detecting its probe-local admission, line 182).
The import probes' `sorryAx` census now names `exists_uniformSimulator` as the **only**
direct admission in the canonizer's closure — the stub no longer appears.

## Note 50 (permanent sanity cases)

`campaign/fills/b5a/evidence/b5a-canon-cont4/CanonNote50.lean.txt` copied **unchanged** to
this zip's `evidence/CanonNote50.lean.txt` and elaborated against the delivered tree
(`evidence/logs/item3-note50.log`): 0 errors; its last line prints

    'note50_cases' depends on axioms: [propext, Classical.choice, Quot.sound]

— **no `sorryAx`** (`evidence/logs/item3-note50-axioms.log`), the complete-delivery
criterion for note 50. No `#eval`, `native_decide` or `IO` anywhere in the file.

## Rule 10 and rule 11 (the final self-checks)

**Declarations cited outside the owned file** (all base-public; the import probe's list
covers them, and `counterLoopOrbit` — the brief's N3 pitfall, an `abbrev` of `roundOrbit` —
is cited only through the published `roundOrbit_zero`/`roundOrbit_succ` pair):
- *Machine and configuration*: `Cfg.mapState` (+ its `simps` field equations),
  `Cfg.ext`, `MultiTapeTM.runFrom` (`runFrom_zero`, `runFrom_add`),
  `FinTM.bufferTape` (`bufferTape_eq`, `bufferTape_nil`, `bufferTape_nat`,
  `bufferTape_of_neg`), `Function.update` laws.
- *Hosts and transports*: `phaseHostTM` / `phaseHostTM_run`; `seamCompTM` /
  `seamCompTM_runFrom_left` / `_right`; `seamReleaseTM` / `seamReleaseTM_firstReturn` /
  `seamReleaseTM_runFrom_pos`; `embedEmitTM` / `embedEmitTM_runFrom`; `embedEmitCfg`
  (+ its field equations `embedEmitCfg_state`/`_inputPos`/`_output`,
  `embedEmitCfg_selected_tape`/`_selected_pos`, `embedEmitCfg_unselected`) and the
  reconstruction lemma `embedEmitCfg_eq`.
- *The counter loop*: `counterLoopTM`, `counterLoopCfg`, `counter_cfg_eq`,
  `counterLoopTM_run_done`, `counterLoopTM_run_escape`, `roundOrbit`
  (`roundOrbit_zero`, `roundOrbit_succ`), `counterValue` (`counterValue_eq`,
  `counterValue_bits`, `foldr_bit_eq_ofDigits`), `counterOverhead`
  (`counterOverhead_le`, `counterOverhead_le_of_le`), `counterWord`.
- *Catalog rows (framed forms only)*: `copyTM_run_ofCfg`, `skipTM_run_ofCfg`,
  `walkTM_run_ofCfg`, `writeConstTM_run_ofCfg`, `skipBackTM_run_ofCfg`,
  `incrementTM_run_succ_ofCfg`; `incFixed` (`incFixed_nil`, `incFixed_false_cons`,
  `incFixed_true_cons`, `incFixed_length`, `incFixed_eq_none_iff_replicate`).
- *Parsing and encoding*: `codeSkipActionK` (`codeEraseActionK`, `codeReadActionK_sound`),
  `codeSkipRepeat` (`codeSkipRepeat_zero`, `_succ`, `skipRepeat_consumes`,
  `skipTable_consumes` via the in-file `canonSkipTable_eq`), `codeSkipFin`
  (`codeEraseFin`, `codeReadFin_sound`), `codeBitsNat` (`codeBitsNat_eq`),
  `pairEncode`/`pairDecode` (`eq_pairEncode_of_pairDecode`, `length_pairEncode`,
  `pairEncode_eq_dbl`), `dbl`, `unaryFin`, `codeActionK_length`.
- *Mathlib*: `Fin.castLEEmb` and the `Fin`/`Option`/`List`/`Finset`/`Nat` lemma families
  visible in the diff's rewrite arguments.

**The seal test** (`.lake/axcheck/Cp7Seal.lean`, log `evidence/logs/item3-seal.log`): a
scratch copy of the module with `attribute [local irreducible]` on all 35 other-file
definitions the new proofs mention, wrapping the whole owned region (the new privates and
the stub's proof), elaborates with 0 errors. The control copy
(`.lake/axcheck/Cp7SealControl.lean`, log `item3-seal-control.log`) adds
`example : Turing.counterValue [true] = 1 := rfl` inside the sealed section and fails on
exactly that line, so the seal is live. Two seal passes surfaced 19 definitional
shortcuts (reads through `Cfg.select`, `Cfg.mapState`, `embedEmitCfg`, `MultiTapeTM.runFrom`
at time zero, and literal `FinTM.bufferTape` cells); each was replaced by its published
equation (`Cfg.select` is no longer used: both embedded banks are explicit literals
reconstructed by `embedEmitCfg_eq`), and the delivered file carries the lemma-based forms
(the proof-only hardening commit, disclosed).

**Inspection of rewrite arguments:** every `rw`/`simp`/`simpa` argument in the diff is a
published base lemma, a Mathlib lemma, one of this fill's own in-file privates, or a local
hypothesis/`let`; the diff contains no `unfold` and no `simp` unfolding of a foreign
definition (full inventory re-derivable by the one-line grep in the delivery notes).

**Rule 11:** `canonPreserveInstall` is byte-identical (it does not appear in the diff), and
a grep of the diff's added lines shows no new citation of the six R3 rows (`copyTM_run`,
`transferTM_run`, `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`,
`incrementTM_run_overflow`) — only their framed `_ofCfg` forms.

**Escalations and requested shared lemmas: none.** **New copies: see the screens section**
(the after screen's pair list against the base reference, each new pair justified).
