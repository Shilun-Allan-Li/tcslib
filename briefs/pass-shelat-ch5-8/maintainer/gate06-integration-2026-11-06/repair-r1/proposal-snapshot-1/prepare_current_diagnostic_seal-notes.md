# Current-source diagnostic seal preparer

Helper: `prepare_current_diagnostic_seal.py`, SHA256 `39659352a439bbb1f1511ade405704aab7aa51951f9c8c9e40d8cbcd472ec6f7`; 102 lines. Preparation only. This invocation wrote the helper and these notes, parsed its Python AST, and did not execute its main function, builders, Git call, checker, or Lean. No actual probe/evidence directory was created here.

Root usage after review:

```sh
python3 -I /Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4/.lake/ps-maintainer/gate06/repairs/prepare_current_diagnostic_seal.py TCSlib.Cryptography.SecureComputation.Yao RepairR1_Yao
```

The effective label is automatically prefixed `OLD_COLLECTOR_DIAGNOSTIC_NOT_FINAL_COVERAGE_`. The module must match exactly one initial R2 entry; the suffix must be a fresh ASCII identifier of at most 80 characters. Existing scratch/evidence label directories are refused; files use exclusive creation. Preserve a partial attempt and choose a new label if preparation is interrupted.

The helper hash-pins the initial R2 `seal-manifest.json`, its pins, the reviewed original `build_seals.py`, the V3 constant-AST payload adapter, and generic `check_probe_v2.py`. It passes the entire initial `requested_names` list, unchanged, to `bs.instrument` with the **current module's raw bytes and header**. It adds no exclusions or name filtering. Current imports may differ and are recorded; the old row set does not grow to cover them. Both actual-name installation and EOF verifier commands remain in the generated source.

It records current Git HEAD using read-only `rev-parse` with optional locks disabled, plus the complete current library Lean path/hash list and its aggregate fingerprint. It deliberately does not assert that the working tree equals HEAD or the initial collector head `e9d64158461bfe24ddc88ab885bc4017899b4c16`. A second snapshot rejects source changes during preparation. This fingerprints dirty source bytes; it does not validate upstream object freshness or freeze the tree for a later run.

On root invocation, exact original source, generated probe text, helper source, and metadata (source/probe hashes, full old name list, insertions, and source-to-probe line map) are saved under both the ignored Gate06 `rule10/diagnostics/<effective-label>/` and main R2 `diagnostic-evidence/<effective-label>/`. The only actual `.lean` probe is under ignored scratch. Initial manifests, probes, logs, and library sources are not overwritten.

The helper prints an argv list and required cwd for root's separate serial native check. It never starts that command. Use its exact emitted `native_command` from the Gate06 integration root, with root coordinating one process per olean tree. A native attempt writes to a fresh `native/` subdirectory of that diagnostic evidence label.

After the checker returns, root must verify source SHA/unchanged bytes, all actual-name rows and installed irreducibility, the installation counts (active + already irreducible = requested = verified), the exact EOF marker, and every located source/harness diagnostic. Generic exit 0 or object existence alone is insufficient. Initial active/already counts are not asserted to describe the current environment; runtime counts must be inspected. Missing names, marker failures, body errors, and warnings remain explicit diagnostic outcomes, never exemptions.

This helper is an integration aid using **old collector rows**, not fresh elaborated-term or current import-closure coverage. New readers, terms, imports, generated names, or anonymous commands may be absent from the initial row list. A fresh collector and the complete intended final seal/control/scan workflow remain required for gate evidence. No final coverage, proof pass, or merge clearance is attested by preparation or a successful diagnostic run.

**Ready to run**
