# Optional fresh final explicit-list scanner invocation

**Prepared, not run. Root review and serial native scheduling remain required.** The static new/touched review is complete separately; this optional route adds a fresh all-namespace kind table for the existing hardened textual scanner. It does not replay seals, add exclusions or clear failures.

Pins: base `eee107e92a7db11f1f8c98a5c2867304f57ddc54`, HEAD `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`, 54 math files. Source list: `final-explicit-files.txt` SHA256 `e027117c0810eabb2cf743e19517ab36ce57ca171a700a510547aaeb966d8d35`. Catalog source: `final-explicit-catalog.source.txt` SHA256 `fb79af50d9316974dfc19188bf5b07cf4337a12b7fe141ce8291d2ee6ccb6361`. Manifest SHA256 `1556043af36cb56ec5d5da2438b46b023a603bd4e78a868bf69ec92adb493602`. Full 1,108-source SHA list is bound in the manifest.

1. Read the 109-line catalog source and 113-line extractor in ignored repairs. The source copies the original Gate04-r5 kind classifier as data; actual imported Names and their native home/kind are enumerated without any reducibility change. Safe prop-valued projection fields retain their native theorem kind. No Core/Mathlib namespace is filtered out.
2. After other native work completes, place the exact catalog bytes in fresh ignored module `.lake/ps-maintainer/gate06/rule10-final-explicit/G06FinalExplicitCatalog.lean`. Refuse an existing directory/source; keep the actual source byte-identical to the reviewed `.source.txt`. Root runs its standard `check_probe_v2.py` serially in the pinned Gate06 olean tree, with a fresh attempt directory and label `G06FinalExplicitCatalog`.
3. Only after fresh rc0 completion, run the reviewed extractor. It launches no native process and refuses an existing/nonignored output directory. The root placeholder paths below must be replaced with that fresh attempt/output:

```text
python3 -I -B /Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4/.lake/ps-maintainer/gate06/repairs/extract_final_explicit_catalog.py FRESH_CATALOG_ATTEMPT FRESH_IGNORED_CATALOG_OUTPUT
```

It checks native rc/source/START/END/error/object/row completeness, fixed source/manifest/scanner hashes, current HEAD and every reviewed library source. `native-kinds.tsv` preserves all imported actual Name/native-kind/home rows. `constants.tsv` preserves the same name/home set while broadening def-private/def-aux/def-proj/def-irreducible to def so the existing scanner flags all ordinary data definitions and their equation-lemma parents. Reducible/instance definitions remain separately flagged; safe prop-valued projections remain theorem rows. No name is dropped; `catalog-validation.json` says only `NATIVE_KIND_CATALOG_VERIFIED_SCAN_NOT_RUN`.

4. Run the existing hardened scanner, without a touched-declaration filter and at the explicit frozen revision. `FRESH_SEAL_SOURCE_ERRORS` must contain all source-mapped final seal errors, including inherited ones, in the scanner's documented ` file.lean:line:...` form. It is not an exclusion file. `FRESH_EQN_CANDIDATE_DIRECTORY` belongs to a fresh proof-term collector if that independent stage is available:

```text
python3 -I -B /Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/gates/04-s2b/evidence-r5/tools/scan.py /Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4 /Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4/.lake/ps-maintainer/gate06/repairs/final-explicit-files.txt FRESH_IGNORED_CATALOG_OUTPUT/constants.tsv FRESH_EQN_CANDIDATE_DIRECTORY FRESH_SEAL_SOURCE_ERRORS FRESH_IGNORED_SCAN_LOG --rev 3f6db40e1688c4a0bb922c9575dd3bd2157a650b --srclemmas FRESH_IGNORED_SOURCE_LEMMA_DIRECTORY
```

Scanner SHA256: `5a8f30fe15d70e976e6a59e2aab42ae1bb6bec1b6d2f14587bb86f800d2a1ac6`; adjacent `declx.py`: `ffa3743f32fe22b19b4d18b5c233b916c23c7288ffe74e8aa8afb69f220af2c2`. Its raw C1 output is retained in full, including inherited reads and Core/Mathlib metadata hits. Local-variable/typed-receiver resolution and generated interfaces are reviewed using the final primary-source classification; do not delete apparent hits silently.

The legacy script appends C2 `show/change` and C3 proof-term equation counts. Missing corresponding inputs can make those historical sections print zero; **label them NOT_MEASURED unless fresh complete inputs were supplied**. They are not coverage or passing evidence for this C1 task. No old candidate table, old seal result, failure-filtered list or inherited waiver may replace the fresh data. The static item review found no compiler-equation head at all, but that does not claim a fresh whole-proof C3 census.

No command above was run. The proposed kind catalog, extractor, original scanner and any native checker require root's source review before execution; the extractor was AST-parsed only. Root's final collector/seals/controls, axiom comparison and failure reconciliation remain independent.
