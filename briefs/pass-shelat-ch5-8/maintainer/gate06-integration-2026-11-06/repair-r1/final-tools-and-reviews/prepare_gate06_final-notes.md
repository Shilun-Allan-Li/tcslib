# Fresh Gate06 final collector / seal-control preparation proposals

Two preparation-only tools, not executed by this invocation:

- `prepare_gate06_final_collector.py`: SHA256 `a402e458b32f65edb272276dfb8b6dd9ed59b992024b586b42ccfebe737470f4`; 147 lines.
- `prepare_gate06_final.py`: SHA256 `130f92d412ed7d60f3496c3928b06621f1ebde81363ecb5fbb7ff0fc91ccdb54`; 89 lines.

Both are under ignored Gate06 repairs. Python AST parsing passed. No imported tool code, Git command, Lean/cache/native process, collector, seal/control builder, or generated probe was run here. No library, Git, or actual evidence was changed.

## Root sequence after review and final source freeze

1. Reconcile current native source/object prerequisites and freeze the final committed repair source. Invoke the collector preparer with explicit full lowercase 40-character BASE and HEAD SHAs. It checks exact commit resolution, actual HEAD, base ancestry, complete library paths/bytes against Git archive, and the pinned TCSlib tree using the stable builder's `library_snapshot`.
2. The preparer derives all changed Lean paths from that exact base→HEAD pair. Math targets are independently derived with the verified declaration lexer; every complementary excluded file must contain only imports/options. Unsupported/deleted/nonlibrary paths fail closed. Import closures use the verified header parser. Touched names are recomputed with the pinned original helper against the clean final source. N is derived and revalidated, never set to 51 or 54.
3. Root runs the emitted collector argv separately, in the integration checkout, serially in the Gate06 olean tree. Collector native label remains `collect1` inside the fresh evidence root.
4. After completed successful collection, root invokes `prepare_gate06_final.py` (optionally `--control-module <fresh audited module>`). It rederives scope and revalidates every source/tool/input hash before using the stable builders to prepare **all N seals and all eleven controls**. It does not run their native commands. By default it prefers the original control module if its fresh full closure remains eligible, otherwise a sorted eligible fresh module; exact unchanged required target/reader conditions are enforced.

Commands (placeholders must be replaced by reviewed actual full SHAs):

```sh
python3 -I /Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4/.lake/ps-maintainer/gate06/repairs/prepare_gate06_final_collector.py BASE_SHA HEAD_SHA
python3 -I /Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4/.lake/ps-maintainer/gate06/repairs/prepare_gate06_final.py
```

The second command belongs **after** the separate collector check, not immediately after the first.

## Fixed fresh paths and preservation

Scratch: `/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4/.lake/ps-maintainer/gate06/rule10-final-r1`.

Evidence: `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-final-r1`.

The first tool refuses either existing root and exclusively creates its outputs. It saves `Collect.lean` only under fresh scratch, with exact `Collect.source.txt`, source metadata, pins, tool-input copies, preparer source, and `final-preparation.json` in evidence. The collector module is `.lake/ps-maintainer/gate06/rule10-final-r1/Collect`; its result/log/source copies are expected directly in the new evidence root. Original R1/R2 scratch/evidence remains untouched.

The adapter refuses existing seal/control/adapter manifests. Stable builders retain their own exclusive output and source preservation checks. Seals are standard `seals/G06Seal_<ordinal>_<fullmodule>.lean` under fresh scratch; controls are standard `controls/G06Control_<case>_<mode>.lean`. Exact probe `.source.txt` copies/line maps and standard manifests go into the corresponding fresh evidence subdirectories. Any partial failure is preserved; the tools do not overwrite it or silently resume.

## Reused verified logic and hard checks

No 571-line seal builder or 341-line controls builder is copied/reimplemented. Original sources are loaded at reviewed hashes, configured with `EXPECTED_MODULES = N` and the fresh `SCRATCH_REL`. Controls receive the same configured builder instance. The only V3 entry used is `configure_builders`, not its frozen e9/ordinal-19–51 retry main. Constant-AST request payloads apply to every seal and every control/catalog. Proof budgets and coverage exclusions are unchanged.

The collector reuses the hash-pinned initial all-stored wildcard/AXIOMSID adaptation and exact closure-supplement literal, obtained as data from the pinned preparer AST. Anchored transformations must each match exactly once. Every final module gets all three commands (`#collect`, `#axs`, `#sealclosure`); the adapter regenerates the exact collector body from reviewed source data before using its results, and the completion validator checks exact imports/commands, all-stored summaries, AXIOMSID counts, and fresh term-name inclusion/metadata against the complete closure. No old row set or diagnostic result is accepted as final coverage.

Archive validation, explicit import/option-only complement, source SHA matching, source preservation, actual `Lean.Name` resolution/unique home, installation/EOF checks, full closure, matcher retention, notation policy, all eleven control expectations, and failure preservation remain in the stable builder contracts. The preparer intentionally rejects a new math file consisting only of unsupported command forms rather than silently excluding it. Root must resolve such a case explicitly if encountered.

## Manifest contract for the separate final runner

Standard `seal-manifest.json` and `controls-manifest.json` are left untouched. `final-adapter.json` binds their exact hashes and discloses runtime configuration. Its keys are:

- `status = PREPARED_NOT_RUN`, `root`, `evidence_directory`, `base`, `head`, `expected_math_modules`, sorted `modules`, `scratch_relative`, `controls_module`;
- `source_sha256` of saved **adapter** `prepare_gate06_final.py`, `preparer_source_sha256` of separate saved `prepare_gate06_final_collector.py`, `final_preparation_sha256`, `seal_manifest_sha256`, `controls_manifest_sha256`, `collector_result_sha256`;
- `tool_input_sha256` exactly `build_seals.py`, `build_controls.py`, `request_payload_adapter.py` (their exact source copies are in `tool-inputs/`);
- `request_encoding = constant-AST newline/tab String parsed at runtime`, `proof_budgets_changed = false`, `coverage_exclusions_added = false`, `library_verification`, `runtime_verified = false`.

`final-preparation.json` separately binds source/pin/closure/touched/collector-copy input hashes, all preparer tool hashes and `tool_saved_names` (the Lean body archive uses `.source.txt`), its own source hash, N/module set, full library snapshot, collector module and label. The two Python source hashes are different and must not be equated. The native runner should pin the reviewed final-adapter JSON hash, capture both tool sources, regenerate all probes/control bodies, and check every runtime result. No new native runner is supplied by this task.

## Limits

The tools are unrun proposals. Their AST syntax alone has been checked; no claim is made about actual final scope, collector completion, applicability of the adapter, object freshness, seal/control outcomes, or merge clearance. Source/object prerequisite reconciliation and exact toolchain/package setup binding remain root/runner work before relying on native collection/results. An old-row diagnostic run cannot replace any final collection or probe. No new approval gate or mathematical requirement is introduced.

**Ready to run**
