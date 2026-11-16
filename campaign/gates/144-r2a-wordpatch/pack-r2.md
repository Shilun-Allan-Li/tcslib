# Gate 144 round 2 · Closeout R2a: one interval patch (PR #330)

**Not yet clear to merge** · PR #330 is a draft. Seyoon dispatches and merges.
The Lean head is `a3c9c2102865e60c4eed295a4b613ef2b85a987c`, one commit on the round-1 head
`ae4157ddf37ea3520e5d953faef808649b8688d3`, against the campaign Lean `720e2a9c` (records `e00f64e9`).

## What round 1 found and what changed

Round 1 held the gate (`findings.md`, verbatim; `resolutions.md`):

- **G144-01 (major).** Two changed proofs passed Mathlib's `SignType.cast`, a definition, to
  simplification, and the zero-read sweep only considered TCSlib definitions. **Fixed in Lean**
  (`a3c9c210`, proofs only): `catalog_increment_trace` and `scanTM_run_ofCfg` use Mathlib's published
  cast equations (`SignType.pos_eq_one`, `neg_eq_neg_one`, `coe_one`, `coe_neg_one`, `coe_zero`).
  The extended sweep also found six `Action.apply.eq_1` arguments in `catalog_increment_trace`
  (another file's generated equation lemma, an unfolding in substance); its five steps now read the
  step field by field through the published `Action.apply_state`, `_inputPos`, `_workTapes`,
  `_workTapePos`, `_output` equations, with `Function.update_apply` where a write leaves the cell
  unchanged. **The sweep is extended** (`defsweep/` in the carrier): a Lean command
  (`defsweep/Kinds.lean`, `#kinds`) resolves each identifier passed to a simp/rw/unfold-style tactic
  in every changed declaration (`defsweep/extract.py`), in its file's namespace and opens, and
  reports its kind and defining module across TCSlib, Mathlib and Core (`defsweep/logs/`,
  `defsweep/SUMMARY.json`). A text check finds no generated equation lemma (`eq_N`, `eq_def`),
  `SignType.cast` or `delta` in the changed declarations.
- **G144-02 (minor).** The inventory truncated statements at a `let … :=` in the type. **Fixed in
  the generator** (`drivers/mksource.py`): a statement ends at the declaration's own `:=`. The
  regenerated `evidence-r2/SOURCE.json` lists all eight changed theorem statements
  (`catalog_write_middle`, `counter_patch_twice`, `counter_patch_frame`, `counter_debit`,
  `counter_rounds`, `iw_patch_append`, `iw_patch_true`, `iw_local`) and the definition header
  `iw_prefix`, each changed only by the patch substitution. **Erratum to round 1's pack, brief
  item 3:** "five private lemmas" should read eight.

## Brief for the auditor

1. **G144-01.** Check the diff `ae4157dd..a3c9c210` (`patch/round1-to-round2.patch` in the carrier and the bundled
   Catalog): proofs only, in `catalog_increment_trace` and `scanTM_run_ofCfg`; no statement change.
   Check that the changed declarations now pass no other module's definition and no generated
   equation lemma. `defsweep/SUMMARY.json`'s remaining non-own hits are not definition reads: in
   CounterLoop, `control` is a local hypothesis (`rw [control]` in `counter_rounds` and
   `counterLoopTMVia_run_done`) and `List.replicate` occurs inside a lemma argument
   (`rw [counter_patch_twice … ((List.replicate w.length true).map e) …]`); in InputWindow,
   `wordPatch` occurs inside `show wordPatch … = _ from funext (wordPatch_apply _ _ _)`; in StepClock,
   `decodeBool` occurs inside `show … = (ct p).bind (decodeBool e) from Cfg.decodeSymbols_workTapes …`
   and `control` is a local hypothesis; `rfl` and the simproc `reduceIte` are not definitions passed
   to unfold. Confirm or refute each.
2. **G144-02.** Check the regenerated inventory against the base and head sources.
3. **Everything else** is unchanged from round 1 (its notes G144-03 to G144-05): re-check the
   replay, seals and screen for the new head.

## Evidence (head `a3c9c210`)

- `evidence-r2/REPLAY.json`: the downstream closure (127 modules) on `oleans-c720e`; 127 passed, 0
  failed; the 18 inherited admissions are `main`'s (RAMSimulation 14, `RecordTable` 4).
- Seals: all 31 changed proofs pass with their 30 other-file heads irreducible; 34 definitions' 68
  paired controls close natively and fail sealed. The TCSlib proof-syntax sweep: 0 candidates.
  Lint: no change. Metadata: standard axioms only.
- Copy screen (the five owners): 81 pairs at head against 82 at base; no new pair, one gone
  (`catalog_increment_trace` → `catalog_clear_trace`, which diverged with the rewrite).
- `evidence-r2/DATA-CARRIER.json` and its recovery map (519 logical files): round 2's runs, the
  sweep, and round 1's results under `history/round1-ae4157dd/`. Decode each blob and check its
  SHA-256 and byte count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate144-r2a-wordpatch-findings-r2.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
