# Rule 10 evidence (brief check 6), gsw-6b-statements, sub-agent `seal`

Heads: base `3e51b5f28900db6190f1eb2e6d207d27ee15d541`; O2 head `dd84941f747bca798c2a5a792616f5ead21cfa0b`;
final head `a855e111f3dd31e1d4664117618813dff544cb6d`. The `cp1/` run was made at the old checkpoint-1 head
`292ed48380fde2cf367f40dbb2ec0de6f7c6ba70`, before the rebase. The rebased checkpoint-1 head
`57815173072bf8c145a4bb774797989061fe96f4` differs from it only by a docstring rewrap in `GSW/Branching.lean`.
The final-head runs (`final-bitenc/`, `final/`) supersede `cp1/`, which is kept as history.

## Layout

The directories `o2/`, `cp1/`, `final-bitenc/` and `final/` are each one `run_checkpoint.sh` output directory.
(`cp1/` was made by calling the same component tools one by one, before `run_checkpoint.sh` existed. It has no
`source-identity.tsv`, and its unfold outputs and notation check are at the same paths.)

| Path | Content |
|---|---|
| `<run>/modules.txt` | owners (dotted module names) |
| `<run>/controls-spec.json` | control spec: owner, definition, statement, body read (`neg`), reader (`pos`) |
| `<run>/source-identity.tsv` | per file: sha256 at the rev (git show) and of the worktree file; must be `identical` (the probes elaborate against the olean tree, built from the worktree) |
| `<run>/seal-summary.tsv` | **summary**: owner, variant (A, B, coe-A, coe-B), requests, verified (install/EOF sums), rc, errors, counts_ok, verdict, failing declarations, first error line, source sha256, max RSS, seconds, sorry warnings |
| `<run>/seal/seal-{A,B,coeA,coeB}.tsv` | sealsum.py per probe (same data, probe labels) |
| `<run>/seal/seals-<V>/` | seal sources (`<label>.lean.txt`, the exact probe bytes) and records (`<label>.json`: requests, term rows, exclusions, line map; `manifest.json`) |
| `<run>/seal/run-<V>/` | raw logs (`mods/*.log`) and `results.jsonl` (rc, errors, sorry, max RSS, sha256 of source and log) |
| `<run>/seal/collect*.{lean,log}` | the collector (CAT/ROOT/CLOSURE rows) and its log |
| `<run>/seal/touched.{json,tsv}` | declaration spans (used to attribute errors to declarations) |
| `<run>/notation-check.tsv` | the notation side: each named abbreviation, `PolyExpr.eval` and the FinDist coercion, with requested or not per probe and variant; requested instances; requested reducible constants (must be none) |
| `<run>/unfold/explicit-unfold-scan.txt` | scan_unfold.py: `FOREIGN-UNFOLD`/`notation`/`OWN` lines; `RESULT foreign_unfolds=…` |
| `<run>/unfold/scan-resolve.{tsv,log}`, `Resolve_*.lean`, `run-resolve/` | the Lean-resolved supplement: every simp/rw/unfold argument resolved in the file's own name context and classified (THEOREM, LOCAL, OWN-DEF, NOTATION, FOREIGN-UNFOLD, CORE-DEF, …) |
| `<run>/controls/summary.tsv` | **controls**: per control file: harness (none / strict(A) / coe(coe-A)), rc, errors, expected, error inside the example, install/EOF records, verdict, error line |
| `<run>/controls/src/`, `records/`, `run-unsealed/`, `run-sealed/` | control sources, records, raw logs |
| `cp1/misc-instkind/` | probe showing that `Parameters.neZero_columns` and `fheView_fst`/`_snd` are theorems |

Variants:
- **A** (strict) seals every eligible TCSlib definition of the full import closure. Eligible means kind `def`
  and (matcher, or not reducible), minus `PolyExpr.eval`.
- **B** is A with `PolyExpr.eval` also sealed.
- **coe-A** (canonical) and **coe-B** are A and B with `FinDist.instCoeFunForallReal` also excluded as notation.
- Reducible definitions are never requested: abbreviations, instances declared by `instance`, and structure
  projections. `-DmaxErrors=0`, no `-o`.

## Commands

Each run is one command, with `/home/user/sub/seal` checked out at `<rev>` and `/home/user/oleans/seal` built
from it:

```
bash /home/user/ev/tools/seal/run_checkpoint.sh /home/user/sub/seal <rev> 3e51b5f28900db6190f1eb2e6d207d27ee15d541 \
     /home/user/ev/rule10/<run> /home/user/ev/rule10/<run>/modules.txt /home/user/ev/rule10/<run>/controls-spec.json "<title>"
```

- `o2/`: `<rev>` = `dd84941f…`. The worktree was at `292ed483`, and BitEncoding's bytes are identical
  (`source-identity.tsv`).
- `final-bitenc/`: `<rev>` = `a855e111…`.
- `final/`: `<rev>` = `a855e111…`, with
  `NOTATION="<GSW>.LevelCoins <GSW>.LeveledSeeds <GSW>.LeveledView" JOBS=3`.
- `cp1/`: `seal_pipeline.sh /home/user/sub/seal 292ed483… cp1/seal cp1/modules.txt "…" 3e51b5f2…`, then
  `xr/controls_full.py cp1/seal/collect-lines.log /home/user/sub/seal cp1/controls-spec.json cp1/controls`, then
  `scan_unfold.py`, `scan_resolve.py`, `xr/notation_check.py` and `xr/summarize.py` with the arguments that
  `run_checkpoint.sh` uses.

Environment knobs:
- `SEAL_CHUNK=1000` splits a request set into harness commands of at most 1,000 rows. Use it only if a probe
  overflows; no run here needed it.
- `VARIANTS`, `JOBS` (probes submitted at once; the pool caps the real parallelism at 3), `SKIP_COLLECT=1`.

Every Lean process ran through `/home/user/ev/tools/lead/poollib.py` (`xr/runner_pool.py`). Tools and their change
headers are in `/home/user/ev/tools/seal/`.

## Results

See `RESULTS.md` in this directory.
