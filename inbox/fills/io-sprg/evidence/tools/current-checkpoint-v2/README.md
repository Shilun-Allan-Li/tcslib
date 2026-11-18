# Checkpoint/final audit adapters V2 — staged, not run

All runtime candidates except `freeze_global.py` are **UNRUN**. Every `.py` was
parsed with Python `ast.parse` only. No Lean, Lake, cache, Git command, candidate
module, gate, or implementation mutation was executed by this preparing agent.
Root independently ran the byte-bound `freeze_global.py` successfully; that
specific result is recorded in `syntax-status.json`. The archived staging producer
was executed only to write candidate copies/diffs. It is not a runtime tool.

These are tool candidates for root review, not new gate passes. Preserve the M0,
M1 and M2 artifacts. Install the entire directory together under a new evidence
path so its adjacent `checkpoint_inventory.py` and `io-sprg-rule10/` remain together.
Old canonical seal generators, request payload adapters, reader elaborator and
`runner_full.py` remain at their original reviewed paths under `evidence/tools/`.
No candidate changes a conservative closure or invokes a whole Mathlib cache get.

## Inventory and required coverage

`checkpoint_inventory.py` derives owners from the **complete pinned-base→resolved
committed HEAD diff**, with exact area/export boundaries. It rejects source bytes
that differ from HEAD and untracked owner Lean files. Every new module (Basic,
Claim42 splits, later LPN splits) is discovered; no owner count is hardcoded.
`load()` independently reloads and rederives the complete inventory at every gate.
The root export is the exact approved single import. Direct Mathlib cache roots
are every direct Mathlib import in the full TCSlib source closure, not only newly
missing oleans or the Mathlib transitive closure. New roots require root's narrowed
cache evidence even when their oleans were already available transitively.

The original Rule10 guards are retained: four exact variants, complete catalogue
closures, current collector source/log/environment binding, full request rows/chunks, runtime Name/home/components/masks/status,
INSTALL/EOF identity and request totals, paired reader controls, independent
per-declaration diagnostics, exact source/log/import-environment bindings, and
canonical passes. Counts are established **after** independent set equality:
exactly `owners × {strict-A, strict-B, coe-A, coe-B}` seals and every eligible
reader's positive/negative pair in both sealed/unsealed modes for every variant.
No stale list or observed-result cardinality defines the expected scope.

## Root invocation order

All paths below should be absolute. `$V` is the installed V2 tool directory;
`$ROOT` is the managed worktree; `$I` is a fresh checkpoint evidence directory;
`$TREE` is its existing job-owned olean tree. Choose a new `RUN` label. Commands
shown here were **not executed by this agent**. Root retains all host preflight,
pinned slot/tag, resource, one-tactic-block and serial-execution requirements.

1. Finish and commit the intended Lean source; run the exact-owner source build
   under the existing bootstrap runner. Prepare current and historical inventories:

   ```sh
   python3 -I "$V/checkpoint_inventory.py" --root "$ROOT" --out "$I/inventory"
   python3 -I "$V/checkpoint_inventory.py" --root "$ROOT" --historical \
     --head d10a560b34d58919bc1a5206ce66a444613f94c7 --out "$I/M0-inventory"
   ```

   Build order is `inventory/owner-paths.txt`. Imported source hashes and all owned
   object hashes are checked again by `static_refresh_checkpoint.py`. Additional
   direct cache roots are the exact set difference in the two inventories; never
   request a broader cache set. Any refresh ledger must contain current `head`,
   `inventory_sha256`, exact `added_direct_roots`, and `commands` with `k=3`,
   pinned `wrapper_sha256`, `rc=0`, `roots`, `log`, `log_sha256`.

2. Run unchanged-byte `freeze_global.py` with the explicit move ledger and fresh
   output. Its source snapshot may be precommit, but the later static/report gates
   require every source hash to equal the committed inventory. It globally
   preserves all 670 M0 FQNs/kinds/normalized headers/statement-prose prefixes and
   retains/reconciles original per-file decls2 removals/additions as a move log.
   Later moves must be explicitly appended to the ledger; no removal is waived.

   ```sh
   python3 -I "$V/freeze_global.py" --root "$ROOT" --moves "$MOVES" --out "$I/freeze"
   python3 -I "$V/static_refresh_checkpoint.py" --inventory "$I/inventory/inventory.json" \
     --build "$BUILD_LOGS" --freeze-check "$I/freeze/summary.json" \
     --environment-tree "$TREE" --out "$I/static"
   python3 -I "$V/source_inventory.py" --inventory "$I/inventory/inventory.json" \
     --out "$I/statements"
   ```

   Add `--require-complete` to **both** latter commands for the final checkpoint.
   The zero-hole obligations TSV retains its fixed four-column schema. New helper
   sorrys, anonymous owned examples and non-theorem holes are rejected. Partial
   holes must remain a subset of the frozen obligations.

3. Prepare/run Rule10, each phase with the same `--inventory`, `--root`, `--tree`,
   and fresh `--run RUN`. Phase order is `collect`, `generate`, `seals`, `controls`,
   `summarize`, `scan-prepare`, `scan-run`. The `seals` and `controls` phases delegate
   to the existing environment-bound resumable queues. The control queue runs all
   unsealed groups before any sealed group. Raw `pretest` is optional diagnostic
   output and does not replace the bound final queue. Then:

   ```sh
   python3 -I "$V/io-sprg-rule10/dynamic_counts.py" "$ARCHIVED_GATE10_TOOLS" \
     "$ROOT/evidence/rule10/$RUN" "$ROOT/evidence/rule10/$RUN/current-runtime.json" \
     --inventory "$I/inventory/inventory.json" --environment-tree "$TREE" \
     --require-complete --require-canonical-pass
   ```

4. Prepare the complete exact-owner graph, run it with the new thin bound wrapper,
   summarize it against the **current** Rule10 collector binding, prepare prints
   from that complete census, run prints the same way, and compare:

   ```sh
   python3 -I "$V/census_tools.py" graph --inventory "$I/inventory/inventory.json" \
     --output "$ROOT/evidence/probes/$RUN/Graph.lean"
   python3 -I "$V/run_bound_probe.py" --inventory "$I/inventory/inventory.json" \
     --prepared-binding "$ROOT/evidence/probes/$RUN/Graph.binding.json" \
     --environment-tree "$TREE" --out "$I/graph-run"
   python3 -I "$V/axiom_graph_summary.py" "$I/graph-run/mods/$GRAPH_LOG_NAME.log" "$I/axioms" \
     --inventory "$I/inventory/inventory.json" \
     --collector-binding "$ROOT/evidence/rule10/$RUN/request-counts-binding.json" \
     --probe-binding "$I/graph-run/current-probe-binding.json"
   python3 -I "$V/census_tools.py" prints --inventory "$I/inventory/inventory.json" \
     --census "$I/axioms/stored-census.json" --output "$ROOT/evidence/probes/$RUN/Prints.lean"
   python3 -I "$V/run_bound_probe.py" --inventory "$I/inventory/inventory.json" \
     --prepared-binding "$ROOT/evidence/probes/$RUN/Prints.binding.json" \
     --environment-tree "$TREE" --out "$I/prints-run"
   python3 -I "$V/verify_axiom_prints.py" "$I/axioms/stored-census.json" \
     "$I/prints-run/mods/$PRINTS_LOG_NAME.log" "$I/axiom-prints.json" \
     --inventory "$I/inventory/inventory.json" \
     --probe-binding "$I/prints-run/current-probe-binding.json"
   python3 -I "$V/frozen_kernel_types.py" --inventory "$I/inventory/inventory.json" \
     --frozen "$ROOT/evidence/axioms/m0-sp-w3/StmtDump.jsonl" \
     --current "$I/axioms/StmtDump.jsonl" --output "$I/kernel-freeze.json"
   ```

   Log name is the full probe module path with `/` replaced by `_`; bindings also
   provide the exact path. The wrapper uses original `runner_full.py` and checks
   the pinned slot-wrapper hash; it verifies the whole owned olean environment is
   unchanged before/after, source/log hashes, return code, and both error forms.
   It does not construct algorithms/samplers or write oleans.

5. After **all** Lean/cache work in the checkpoint, root reruns the existing
   `slot_history_v2.py` into a fresh path with `--require-closed`. Its exact known
   93883/93983 overlap stays disclosed: historical seriality is false, maximum
   tagged wrappers is two, and post-correction seriality is checked separately.
   No tool claims a global host process cap or complete child-process history.

6. `checkpoint_report.py` requires explicit current paths for static summary,
   source inventory binding, runtime check, graph summary, print comparison,
   kernel freeze, source freeze, slot summary, and `explicit-current-binding.json`;
   use `--baseline-inventory` for M0 and `--environment-tree "$TREE"`. Partial
   checkpoints require `--completed-names` (explicit unique theorem FQNs) and
   prove those plus **all new helpers** standard-only. Final use additionally
   requires `--final`: zero source tokens/holes, zero direct/transitive sorryAx,
   every stored constant standard-only. Full current environment/source bindings
   must agree. New helper name/shape + exact/apply overlap admission remains an
   independent required record; this tool does not manufacture that review.
   `--historical-report` accepts only the exact canonical M0 report bytes.

7. Only after the report passes, root may call `package_checkpoint.py` with its
   original source/dest/report/head/zip arguments plus `--inventory` and
   `--report-binding`. The branch head, full changed path set, copied source bytes
   and report hash must match. Every commit's PDF exclusion, exact hash replay,
   bundle verification, symlink rejection and both exact manifests remain intact.
   Packaging overwrites the authorized delivery payload destination exactly as
   the original tool did; this preparing agent has not run it.

## Explicit limits

- The wrappers are untested adaptations. AST syntax parsing is not a runtime pass.
- Global source freeze is not proof completion, kernel-type comparison, overlap
  admission, or an axiom check; those remain separate mandatory inputs.
- Historical M0 tables/88 seals/96 controls/146 holes stay historical. No such count
  is used as a current owner/coverage authority. The fixed 670 is only frozen M0
  declaration coverage; new helpers are reported and separately checked.
- Static source inventories are lexical. Full stored-root graphs and exact public
  axiom prints, including private/internal dependencies, establish proof evidence.
- Partial checkpoints allow only declared frozen sorryAx dependencies; final mode
  allows only propext, Classical.choice and Quot.sound throughout owned roots.
- Phase B efficiency targets remain hypotheses. No finalizer proves them.
