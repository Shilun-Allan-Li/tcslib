# Diagnostic whole-file seals

`make_seals.py` and `make_controls.py` are adapted from the sc-garble delivery at
exchange commit `a73072f1`, `evidence/tools/`; byte-for-byte reference copies are
preserved here. The adaptations change only the issue base and evidence paths.
The inherited preamble scans the complete imported TCSlib constant environment,
including matchers. It excludes reducible abbreviations. `A` treats PolyExpr.eval
as notation; `B` seals it. `coe` excludes projection coercions; `strict` seals them.
All SEALED/EXCLUDED rows and counts are preserved in every raw log.

`check_seal.sh` is adapted from this issue base's `scripts/lean_check_tree.sh`;
its reference is retained. It uses the current worktree root, runs Lean with
`-DmaxErrors=0`, and recognizes both `error:` and `error(...)` diagnostics.
Each invocation is held inside the host-wide lean-slot.sh wrapper, with tag
sc-yao-c and the isolated .lake/sc-yao-oleans tree.

These are diagnostic subagent checks. The lead must rerun final merged checks.
