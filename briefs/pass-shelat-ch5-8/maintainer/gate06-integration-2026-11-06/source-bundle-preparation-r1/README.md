# Gate06 source-bundle preparation

Source-only, unissued and unstaged. Frozen source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`; checked base `eee107e92a7db11f1f8c98a5c2867304f57ddc54`. The reviewed preparer verifies all 1,108 library source files against the Git archive, derives each primary facade import closure with the pinned header parser, and uses `mkbundle2.py` to assemble and split-back verify every source section against `git show`.

06A has 124 closure modules plus root-export context, 06B 128 plus root, 06C 170 plus root, and 06D 184 plus root. `TCSlib.lean` is context, not a closure root or an elaboration claim. Each manifest records every path, revision, raw byte count and SHA-256, complete TCSlib import edges, bundle hashes and the exact tool hashes. The source-only bundles currently remain ignored local artifacts; final record/evidence attachments and exchange paths are not supplied by this preparation.

These bundles do not issue the gate or certify final seals, controls, source-failure dispositions, generated-equation scans, or receiving-auditor access. No exchange content was changed. No native Lean/cache process was launched by the bundler.

**Not yet clear to merge — final common evidence and the four external audits remain.**
