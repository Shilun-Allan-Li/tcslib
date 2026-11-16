# Gate 144 resolutions (round 1 → round 2)

Round 1 HOLD: 0 blockers, 1 major, 1 minor, 3 notes (`findings.md`, verbatim).

- **G144-01 (major), fixed in Lean** at `a3c9c2102865e60c4eed295a4b613ef2b85a987c`. The seven
  `SignType.cast` arguments (`catalog_increment_trace` 5, `scanTM_run_ofCfg` 2) are replaced by
  Mathlib's published cast equations (`SignType.pos_eq_one`, `neg_eq_neg_one`, `coe_one`,
  `coe_neg_one`, `coe_zero`). The same sweep also found six `Action.apply.eq_1` arguments in
  `catalog_increment_trace` (the generated equation lemma of another file's definition, an
  unfolding in substance); its five steps now read the step field by field through the published
  `Action.apply_state/_inputPos/_workTapes/_workTapePos/_output` equations, with
  `Function.update_apply` where a write leaves the cell unchanged. **The sweep is extended**: a
  Lean-backed check (`defsweep/` in the round-2 carrier) resolves every identifier passed to a
  simp/rw/unfold-style tactic in each changed declaration and reports its kind and defining module,
  across TCSlib, Mathlib and Core; at the new head the changed declarations pass no other module's
  definition (the remaining hits are term arguments, local hypotheses and simprocs, listed), and
  no generated equation lemma (`eq_N`, `eq_def`), `SignType.cast` or `delta`.
- **G144-02 (minor), fixed in the generator and records.** `mksource.py` now ends a statement at
  the declaration's own `:=` (bracket depth 0, followed by `by` or a line break), so `let x := e`
  inside a type no longer truncates it. The regenerated inventory lists all eight changed theorem
  statements (`catalog_write_middle`, `counter_patch_twice`, `counter_patch_frame`,
  `counter_debit`, `counter_rounds`, `iw_patch_append`, `iw_patch_true`, `iw_local`) and the
  definition header `iw_prefix`; each change is the patch substitution only. **Pack erratum:**
  round 1's brief item 3 ("five private lemmas") should read eight.
