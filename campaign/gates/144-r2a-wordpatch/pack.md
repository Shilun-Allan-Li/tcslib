# Gate 144 · Closeout R2a: one interval patch (PR #330)

**Not yet clear to merge** · PR #330 is a draft. Seyoon dispatches and merges.
The Lean head is `ae4157ddf37ea3520e5d953faef808649b8688d3`, against the campaign Lean
`720e2a9cab2e80924d208f997e89045f573a69f0` (after #328 and #329; records `e00f64e9`). This is the
first audit.

## Scope

Chapters 3–4 closeout, refactor wave R2 (`campaign/closeout/REFACTOR-PLAN.md`, bundled). It retires
the interval-patch family IW-1 and the restated law WA-1 (ledger, bundled), with the API Seyoon
approved on 2026-11-16:

- **`Build/Catalog`**: `Turing.wordPatch` and its lemmas `wordPatch_of_mem`, `wordPatch_of_not_mem`,
  `wordPatch_append` move here from `Build/StepClock`, with the same names and statements, and
  replace Catalog's private copy `catalogTape`. **New public lemmas** (all approved): the published
  equation `wordPatch_apply`; `wordPatch_self`, `wordPatch_twice`, `wordPatch_frame` (same-width
  patches, previously proved privately in both StepClock and CounterLoop); `wordPatch_replicate`
  (a constant word, previously proved in InputWindow and inline in CounterLoop).
- **`Build/CounterLoop`**: deletes the private copy `counterPatch`. **New public lemmas**:
  `decrementTM_shadow_pre`, `decrementTM_liftSymbols_runFrom` (moved from StepClock's private
  `sc_shadow_pre`, `sc_lift_run`; `counter_debit` re-proved the first).
- **`Build/InputWindow`**: deletes the private copy `iw_patch`.
- **`Build/RecordTable`**: `rt_adjacentWrites` keeps its statement; its proof cites
  `wordPatch_append`.
- **Private lemmas kept as one-line citations** (the gate 143 pattern, so their use sites stay
  unchanged): `sc_wordPatch_self/_twice/_frame` and `sc_lift_run` (StepClock),
  `counter_patch_twice/_frame` (CounterLoop), `iw_patch_true` (InputWindow). `sc_shadow_pre` is
  deleted (its one use was in a proof this PR already changes).

**Exposed legacy reads, repaired.** Renaming the copies changed proofs whose unchanged text read
other files' definitions. The first head (`980b506d`) failed the sealed check in five proofs
(`history/head1-980b506d/` in the carrier), and a later head's proof-syntax sweep listed 27 explicit
reads (`history/head4-95542906/`). All are now read through published equations: `embedEmitCfg_eq`;
the field equations of `Cfg.mapState`, `Cfg.liftOver`, `Cfg.liftSymbols`, `Cfg.decodeSymbols`,
`clockCfg`, `Cfg.workTapeSymbols`; `roundOrbit_zero`/`_succ`; `decrementTM_tr_input`;
`FinTM.bufferTape_nat`/`_left`/`_eq`. The repaired proofs are `counter_debit`, `counter_rounds`,
`counterLoopTMVia_run_done`, `counterLoopTMVia_run_escape` (CounterLoop), `sc_debit` (StepClock),
`exists_inputWindowCopyTM` (InputWindow), `scanTM_run_ofCfg`, `catalog_write_middle` (Catalog).
No statement changes.

## Brief for the auditor

1. **The move.** Check that `wordPatch` and its three original lemmas have the same statements in
   Catalog as they had in StepClock (`evidence/SOURCE.json` and the base/head sources), and that no
   other file named `catalogTape`, `counterPatch` or `iw_patch`.
2. **New API.** Check each new public lemma's statement, docstring and proof sketch, and that each
   retires a copy as claimed (the copies' bodies at base are in the carrier).
3. **Statements.** `header_changed` lists five private lemmas whose headers changed only by naming
   `wordPatch` instead of the deleted copy (definitionally the same function); `definitions_changed`
   lists three private definitions (`catalogIncF`, `catalogIncR`, `iw_prefix`) changed the same
   way. Confirm nothing else changed and that no public statement changed.
4. **Rule 10.** Seals (`seals/`): all 31 changed proofs pass with every other-file definition they
   reach irreducible (30 heads); 34 definitions' 68 paired controls close natively and fail
   sealed. The proof-syntax sweep finds 0 explicit reads (`qa/FOREIGN-ARGUMENTS.json`). Review the
   repairs for faithfulness to the original proofs.
5. **Copy screen** (population: the five owners): BASE and HEAD both 82 pairs, no new pair, none
   gone (the deleted copies were short definitions). The restated lemmas surfaced by earlier heads'
   screens are retired (`history/*/pairdiff.txt`).
6. **Records.** Check the refactor plan's R2 row, the ledger's IW-1 and WA-1 entries and this
   pack agree.

## Evidence

- `evidence/REPLAY.json`: the merged-tree replay of the downstream closure of the five changed
  modules (127 modules) on `oleans-c720e` (873 objects; prospective tree in the replay record).
  127 passed, 0 failed. The 18 inherited admissions are `main`'s (RAMSimulation `WordSize` 3,
  `Simulation` 2, `Classes` 9; `RecordTable` 4), unchanged.
- Metadata: standard axioms only for the changed proofs. Lint: no change.
- `evidence/DATA-CARRIER.json` and its recovery map (501 logical files, including the history of
  the earlier heads). Decode each gzip+base64 blob and check its SHA-256 and byte count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate144-r2a-wordpatch-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
