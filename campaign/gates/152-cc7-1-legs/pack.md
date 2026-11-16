# Gate 152 · Closeout CC7-1: CodeSimulator's stage-front legs through one private template (PR #345)

**Not yet clear to merge** · PR #345 is a draft. Seyoon dispatches and merges.

- Lean head: `1dcbbe3171dd685600525d4f7cf71548889ecceb`.
- Base: campaign Lean `fb6f2e31` (the #344 merge); records `c9c51a73`.
- This is the first audit.

## Scope

This is wave R3, family CC7-1, under the design note `campaign/closeout/CC7-1-DESIGN.md`. The ledger
entry is "CC7-1, the canonizer cont7's in-file families", and the R3 row of
`campaign/closeout/R3-R6-MEASUREMENT.md` records zero rule-10 exposure. All three files are
bundled. Seyoon approved the design on 2026-11-16 with a stop rule: at least 35 lines saved per
leg on the prototype legs. The legs went from 85, 81, 86, 104, 101, 93 and 103 lines to 52, 33,
52, 70, 48, 43 and 72; the four new helpers total 80 lines.

`TuringMachine/CodeSimulator` proves its stage front one phase at a time. Each of the seven private
legs `canonStageLeg0`–`6` did four things:

1. run a public row on the outer counter (`copyTM`, `skipTM`, `walkTM`, `writeConstTM`,
   `skipBackTM` or `incrementTM`, through their `_run_ofCfg` rows);
2. call `phaseHostTM_run` with a dispatch proof;
3. supply a guard proof;
4. prove the dispatched configuration equal to the next bank, field by field.

The changes, all private and all in `TuringMachine/CodeSimulator`:

- **`canonStageLeg_of` (new).** Given a row's run from a bank configuration, its dispatching
  state and redirect, a guard, and the endpoint's input head, output, tapes and heads as those of
  the next bank, it gives the leg's lockstep window and the next bank one step later. It calls
  `phaseHostTM_run` and does the `Cfg.ext` once.
- **`canonStage_guard` (new).** The host's guard, from a row's cut and the fact that the phase's
  redirect row is `none` off its dispatching state. Phases 0–5 use it; leg 6, which has two
  outcomes, keeps its own guard.
- **`canonStageBank_move` (new).** Moving only the outer counter's head turns one bank's heads
  into another's. Legs 1, 4 and 5 use it.
- **The seven legs.** Their statements are byte-identical, so the consumer `canonStage_run` is
  untouched.
  - Each leg keeps its row premise proof.
  - The write legs (0, 3 and 6) keep their window-write tape argument. The walk leg (2) keeps its
    head argument.
  - The dispatch is `simp only [canonStageRed]` followed by `if_pos trivial`; the guard's
    redirect rows use `if_neg`.
- **`phaseCut_leg` (new).** The strict-cut leg for any phase host. `canonStageCut_leg` and its
  97% twin `canonGramCut_leg` keep their statements and are now one-line citations of it.

There are no statement changes. `SOURCE.json` has no `header_changed` and no
`definitions_changed`. Net: **−212 Lean lines** (+218/−429). The file goes from 9,032 to 8,820 lines.

## Brief for the auditor

1. **Statements.** Confirm that the seven legs, both cut legs and every other declaration keep
   their statements byte-identical.
2. **Template.** Check that `canonStageLeg_of`'s hypotheses are what `phaseHostTM_run` needs, plus
   exactly the next bank's fields, and that it proves each leg's original conclusion. Do the same
   for `canonStage_guard`'s use (only phases whose redirect row has a single dispatching state)
   and for `canonStageBank_move`.
3. **Legs.** Check that each leg's row, phase index, dispatching state and next phase match the
   redirect table `canonStageRed`, including leg 6's two outcomes.
4. **Cut legs.** Check `phaseCut_leg`'s statement against both former proofs.
5. **Rule 10.** The changed proofs: seals, controls and both sweeps (counts below).
6. **Copy screen** (population: CodeSimulator): see `evidence/PAIR-DISPOSITIONS.json` and the
   note under Evidence.

## Evidence

- `evidence/REPLAY.json`: the merged-tree replay of CodeSimulator's downstream closure on
  `oleans-cfb6f2` (the #344 merge's snapshot), against records tip `c9c51a73`. 24 modules
  replayed: 24 passed, 0 failed, 0 inherited admissions. There are 874 objects in and 874 out.
- **Seals:** all 13 changed or added proofs pass with every other-file definition they reach made
  irreducible (16 heads).
- **Controls:** 25 definitions' 50 paired controls close natively and fail when sealed.
- **Proof-syntax sweep:** 13 roots, 0 explicit reads.
- **Lean-backed sweep:** 71 identifiers. The flagged constants are `rfl` and `Turing.FinTM.bufferTape`.
  - `rfl` appears as `if_pos rfl` and similar term arguments.
  - `FinTM.bufferTape` appears inside `show FinTM.bufferTape [false] 0 = some false by …`, which
    is a term argument in legs 3 and 4's unchanged row-premise proofs. It occurs 3 times at base
    and 3 times at head.
  - Neither is a rewrite rule, and the sealed check passes.
  - The sweep's first run failed to parse a keyword in its identifier list. Its extractor now
    quotes every name (`drivers/defsweep/extract.py`).
- **Citation homes** (G147-02 procedure, `defsweep/CITATION-HOMES.json`): no other-file lemma is
  newly cited. The one listed home, `Build/StepBlock` for `Turing.StepBlock.Ph`, is a false
  resolution: `Ph` is `phaseCut_leg`'s own implicit binder. The scope pass's namespace error
  (`StepBlock`) affects only one of its scope blocks.
- **Lint:** no change. These are the same 5 pre-existing findings, and the campaign lint has 0 FAIL.
- **Copy screen:** 69 → 42 directed pairs, 29 gone and 2 new. The reproduced text falls from
  62,792 to 16,086 characters.
  - **Gone:** every pair among the seven legs, the 97% cut-leg pair (both directions), and the
    seven legs' 60% matches with `us_start`.
  - **New:** `canonStageLeg_of` reproduces `us_start` at 54%; both call `phaseHostTM_run` and close
    with `Cfg.ext`. The unchanged `canonStageFrontSpec` reproduces the template's statement at 50%,
    at the threshold. Both are shape matches between different statements.
- `evidence/DATA-CARRIER.json` and its recovery map: decode each gzip+base64 blob, then check its
  SHA-256 and byte count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate152-cc7-1-legs-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
