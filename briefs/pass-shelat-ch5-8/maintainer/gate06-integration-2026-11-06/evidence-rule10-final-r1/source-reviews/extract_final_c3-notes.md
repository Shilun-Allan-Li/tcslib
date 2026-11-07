# Frozen Gate06 C3 R2 extractor

**Prepared and not executed.** `extract_final_c3.py` is 339 lines, SHA256 `887c0760862fad6da7d0e42f53786c002c08f703614762755b625437e59c0aa8`. Only full-file Python AST parsing and source review were performed; it was not imported, tested by executing its functions, or launched. Root has reviewed this exact version. No further features or R2 source changes are included.

The tool accepts only the explicitly approved R2 source (`26f74568…`), manifest (`faa6852a…`), notes, native module and label. R1 remains an invalid retained parse-failure attempt; there is no fallback, version selection, retry or automatic hash refresh. Canonical Gate06 final `axioms-full.json`, pins, modules, full 1,108-source SHA list, checker/setup/toolchain and native kind table are hash-pinned. The ambiguously named manifest `module_list_sha256` is checked against the actual newline source-path file, as documented in the separate provenance note.

## Root interface

The native R2 attempt must already be completed. The output parent must exist, and the output directory must be absent, inside ignored Gate06 scratch and outside the native attempt:

```text
python3 -I /Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4/.lake/ps-maintainer/gate06/repairs/extract_final_c3.py /Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-final-r1/eqn-supplement-r2/native /Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4/.lake/ps-maintainer/gate06/repairs/final-c3-extracted-r2
```

No Lean/native process, Git command, helper import, source edit or evidence update is performed by the extractor. It reads current HEAD through Git metadata files only. Structural/native incompleteness fails before creating output; it never fabricates zero files for absent or partial input.

## Required evidence

Validation covers native rc0/no errors, fresh nonempty object SHA/mtime, captured/current/frozen source equality, checker hash, START/source-hash/END timestamps, the pruning guard and both metadata controls. It requires exactly 54 ordered module BEGIN/END pairs and exact per-module equality of every ROOT actual Name with all 2,881 canonical AXIOMSID identities, without private/generated/axiom/source-status filtering.

Every REF must follow its declared ROOT, fit its hit count, have a foreign TCSlib definition parent and a generated-equation suffix, and be unique by owner/reference. Root, module and global pair totals agree. Cache extraction totals also reflect all 2,881 owned values plus the two controls. Native kind/home checks allow the reference theorem to have a different home from its parent; for example the `coinLen.eq_1` reference is homed in EnsemblesLemmas while its parent is in PPT.

The complete fresh native kind table is streamed (378,176 rows); only needed identities are retained in memory. All raw native kinds are used, not the broadened legacy-scan table. A known kind/home contradiction fails validation. A missing kind-table identity never removes a pair: the complete dataset and all scanner files are emitted with unresolved metadata, a failing review status and exit1. Root reports three R2 pairs; all three must remain visible.

## Outputs and interpretation

- `eqn/` contains all **54** `{module}.eqn.txt` files, with tab-separated `[module, owner, parent, eqnref]` rows and zero-byte files only for completely verified zero-hit modules. This is the legacy scanner candidate directory.
- `all-refs.json` preserves every reference and both homes; `root-census.json` preserves every actual root and metric. No inherited, notation, root-equation or unknown-reference filter exists.
- `summary.json` reports collection counts and unresolved metadata; `manifest.json` records all raw input hashes, native result, tool hash and hashes of every other output. Completion metadata is written last. A missing/partial manifest or failed process is incomplete output, never passing evidence.

Exit0 means extraction/reconciliation completed with available kind metadata, even when the raw C3 pair count is nonzero. It is **not rule10 clearance**. Exit1 means invalid/incomplete inputs, output failure, or retained unresolved metadata; the diagnostic and summary distinguish them. Original attempts/evidence stay untouched. The standard bounds are 4MiB small inputs, 64MiB tables/objects, 128MiB native logs, 32,768 characters per log/table line and 1,000,000 REF pairs; exceeding a bound fails instead of truncating or reporting zero. The eleven seal controls, final source-failure reconciliation and any policy disposition remain separate.
