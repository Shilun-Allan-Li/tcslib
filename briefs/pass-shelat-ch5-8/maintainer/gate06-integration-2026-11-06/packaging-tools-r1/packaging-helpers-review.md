# Gate 06 packaging helpers: bounded static review

**0 blockers / 0 majors / 0 minors for the current helpers and reviewed input pipeline.**
No helper/native/cache/build was run. No source, records, prepared inputs, exchange or Git
state was changed; this review file is the only output. Runtime archives/bundles do not yet
exist from these helpers, so no completed ZIP/split-back/output-hash result is claimed.

Reviewed complete sources:

- `build_gate06_common_archive.py` (45 lines), SHA256
  `c8b4cb75d05a3298e3b60e50c45450ddfadc985dbc21b148060231e548295a04`.
- `build_gate06_dispatch_inputs.py` (120 lines, current aligned filenames), SHA256
  `22c03d9e4d5fad9a5f7189dfa3056dc4d7a603b5cf3e8b5fcdb1197f273f3c4a`.

No corrective edit identified for the intended invocation with the common helper's own output:

- Full records-commit resolution is checked. Dispatch separately pins source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`
  and compares records library/root-export bytes to ancestor `eee107e92a7db11f1f8c98a5c2867304f57ddc54`.
  Source and records revisions have distinct roles and remain explicit in filelists/READMEs.
- Resolved fresh output paths stay under the worktree's ignored `.lake/ps-maintainer/gate06`
  (`.lake/` is ignored). The `outbox/gates` names are scratch subdirectories; neither helper
  contains an exchange write or a Git mutation. Git archive members must be ordinary files
  within the evidence prefix; traversal/unexpected members are rejected.
- The common ZIP preserves committed raw bytes, requires exact manifest/set equality and
  checks ZIP roundtrip hashes. It rejects PDF/olean/ilean inputs. Dispatch adds only the
  hash-pinned tracked PS10 PDF; Goldreich/PSV remain linked/version-qualified metadata.
- Current `issue-source-manifests-r1/06A–D-source-manifest.json` seven-field contents match
  the independently reviewed frozen preparation manifest: head/base, minimal roots, complete
  import edges, every raw file entry, source bundle filename and hash. The main preparation
  manifest copy is byte-identical to the reviewed ignored copy. The exchange filenames
  `gate06A-source-manifest.json` etc. now match the dispatch README and records-bundle paths.
- All common record paths are distinct. Each pack adds its own pack and raw JSON; D also adds
  Gate05 round-3 findings and resolutions. Actual records-section counts are **20 for A–C and
  22 for D**. Source section counts remain 125/129/171/185. No required D attachment is omitted.
- No hash self-cycle: the committed raw file manifest excludes itself from its entries; the
  ZIP metadata hashes the finished archive; per-folder `SHA256SUMS` excludes itself; source
  manifests hash source-only bundles and contain neither their own hash nor a self records
  commit. Builder hashes name fixed helper bytes, not their generated summaries.
- README text retains 37 passing/17 failing seals, three equation references and admissions;
  it does not call all source seals passing or close the external gates. Codex returns findings
  in chat, the user dispatches, audits may run in parallel, and prong fills wait for their gates.

This is static review of the exact helper bytes/current descriptor inputs, not an attestation
about an arbitrary supplied archive directory or a future changed records commit. Root still
runs the built-in Git/ZIP/split-back/SHA checks against the selected final records commit and
reviews the resulting inputs before staging; no new approval or audit gate is proposed.
README-only spacing polish does not change these algorithm conclusions; retain the final
helper source hash in generated provenance.

**Ready to run with the final records commit — static review only; no issuance, dispatch or merge clearance.**
