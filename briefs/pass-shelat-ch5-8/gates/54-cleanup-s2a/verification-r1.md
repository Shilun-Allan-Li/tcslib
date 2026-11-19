# Gate 54 · merged-tree verification of PR #390 (S2-A) against the records tip · r1

**Result:** the merge of PR #390 with the records tip is clean, and its replay is clean.
- **Replay:** 28 modules rebuilt, all rc 0 with 0 errors; 1,428 reused.
- **Roots:** root `TCSlib` was rebuilt. The two `audits/*/Checks` roots were reused by the plan and then re-checked
  explicitly (rc 0, byte-identical oleans).
- **State check:** OK over all 1,456 modules.
- **Admissions:** S2-A's 192 in 44 modules, plus the records side's 15 in 6 modules, makes **207 in 50**.
- **Seals:** coe-A gives 0 on S2-A's 10 owners. `FromPermutation` keeps job J3's residue (2) unchanged.
- **Lint:** the delta against the records tip is exactly S2-A's own delta.

In-house, by a maintainer sub-agent, 2026-11-19. Static checks used git and `python3 -I`; Lean ran only through
`scripts/lean_check_tree.sh` and the archived seal runner, one process at a time, slot-gated (at most 3 Lean processes
on the host). No `lake build`, no `lake exe cache get`. Evidence is in `verification-r1.zip`; its SHA-256 is in
`verification-SHA256SUMS`, and its inner `SHA256SUMS` lists every file but itself. Read `PROVENANCE.txt` first. Paths
below are inside the ZIP.

| Pin | Value |
|---|---|
| PR #390 head | `9f7f409c2e09749428db75b9ddd324f92695e4af` (`TCSlib` tree `ae345736160511e6d3e7d8b47ad76c430c424500`) |
| S2-A base = merge base | `61a5f0fb640622c15fdd33df56efa470b2bf26c8` (`TCSlib` tree `849ee9454cff17b1fb15a22183526d7e071a9669`) |
| Records tip replayed | `8836292693d7c611ee375d162f34766841635337` (`TCSlib` tree `745bf4b494b6581a5666ef9ca0a6e735a68ddcef`) |
| Records tip at the verification | `a25338e0f78290dff74a754ba89a2988655ac046`: records-only on top of `88362926` (0 Lean, toolchain, manifest or lakefile paths changed). The tip at staging, `25c6a28ac31cd07c299afcb89fe030f4ada45b00`, is records-only on top of that (`source-head-r1.json`) |
| Merge tree | `git merge-tree --write-tree 88362926 9f7f409c` = `84c0205e003688519b1bd13156066d09d0ebe6b4`, clean; `TCSlib` tree **`73af3ec6968e023e87ce00af649db0e2e02f4353`** |
| Scratch commit | `62c2794272bd5cbe4fe3f031d4186924e4e1a222` = commit-tree of that tree, parents `88362926`, `9f7f409c` (`merge/scratch-commit-62c27942.txt`). **On no ref, never pushed** |
| Same Lean at later tips | `merge-tree(a25338e0, 9f7f409c)` = `3feb7cf2…` (`merge/staging-tip.txt`) and `merge-tree(25c6a28a, 9f7f409c)` = `59529934…`: both `TCSlib` tree `73af3ec6` |

## 1. The merge

- **Records side:** since the S2-A base, the records branch changed 12 Lean paths: the GSW 6b statements (#376/#377)
  and U12/U13 (#392). They are 8 new `GSW/*` modules, the `GSW` and `LWE` facades, the changed `LWE/BitEncoding` and
  the new `LWE/Ratio`.
- **S2-A side:** S2-A changes 63 paths. The two sets do not overlap (`merge/mergecheck.txt`).
- **Composition of the merge:**
  - its `TCSlib` differs from the head's exactly in the 12 records-side paths, each blob-equal to the tip's;
  - it differs from the tip's exactly in S2-A's 63 paths, each blob-equal to the head's;
  - against the base it changes their union, 75 paths, and nothing else.
- **Unchanged everywhere:** `TCSlib.lean`, `audits/`, `lean-toolchain`, `lake-manifest.json` and `lakefile.lean` are
  identical at the base, the head, the tip and the merge (`merge/trees.txt`).

## 2. The start tree

**Choice.** The replay starts from S2-A D4's replay output, `$SP/olean-replay-s2a-d4` (base + S2-A, state at
`9f7f409c`). The alternative was snapshot #11.
- **From D4's tree:** only the records side and its downstream are rebuilt, **28 modules**. None of them is an S2-A
  module, and none is upstream of one.
- **From snapshot #11:** S2-A's side would need about 290 modules, plus U12/U13.

**State check of the start tree, before the copy** (`replay/startcheck.*`):
- `stateplan check` over the head's full order (1,447 modules, byte-equal to D4's `full-order.txt`), with D4's checked
  state (`state-checked.json`, SHA-256 in `replay/state-start.sha`): **RESULT OK, bad 0**.
- D4's output map, rehashed: 1,478 entries, SHA-256 `1abe4bed…`, byte-identical to D4's recorded map
  (`replay/rehash-d4-before.txt`).

**The copy.** `cp -al` into `$SP/g54/olean-replay-g54`. The Mathlib overlay (`NthRootLemmas`) is identical in the two
trees. D4's tree was never written to:
- its map is byte-identical after the replay and at the end (`replay/rehash-d4-after.txt`, `-final.txt`);
- `lean_check_tree.sh` unlinks before it writes, so rebuilt modules break their hard links.

## 3. The replay

**Plan** (`replay/plan.out`, `plan/`). `fullorder` at the scratch commit gives **1,456 modules**: the head's 1,447 plus
the 9 new modules. `stateplan plan` uses import-closure keys (`stateplan.py`, unmodified) and gives:
- **28 to build:**
  - `LWE/BitEncoding`, `LWE/Ratio` and `LWE`;
  - the 9 `Encryption/*/Regev*` and `Encryption*` modules downstream of `BitEncoding`;
  - the 12 GSW modules (`Scheme`, `Eval`, `Security`, `Symmetric`, `Branching`, `DecryptFormula`, `Bootstrap`,
    `Circular`, `Leveled`, `LeveledSecurity`, `PolyRatio`, `Asymptotic`) and the `GSW`, `Homomorphic` and
    `AdvancedEncryption` facades;
  - root `TCSlib`.
- **1,428 reused.**

**Runs.**
- **Attempt 1** (`replay/build-attempt1-no-toolchain/`) failed at once, in 0.03 s, on its first module: elan found no
  toolchain. The scratch worktree had been made in non-cone sparse mode, without the root files. No Lean ran. It was
  fixed with `git sparse-checkout set --cone`, and the attempt was set aside (`log/notes.txt`).
- **Attempt 2** (`replay/build/`; `tools/g54/run-replay.sh`) used the recipe's `runner.py`, unmodified, one module per
  call, with `TCSLIB_OLEANS` set to the copy. Before each module it checked the slot gate (wait while 3 or more Lean
  processes run; the readings were 1–2) and the disk guard (stop below 2,000 MB).

| Check | Result |
|---|---|
| `permod` (`replay/permod.*`) | 28 modules; rc≠0 **0**; `error:` 0; `error(` 0; log/record mismatches none; 61 s in all |
| `sorry` warnings | 15, all in the records side's admitted GSW 6b targets: `Bootstrap` 5, `PolyRatio` 3, `Leveled` 2, `LeveledSecurity` 2, `Asymptotic` 2, `Circular` 1. This equals §4's records-side census module by module |
| `stateplan update` | 28 taken, none refused |
| `stateplan check` over the 1,456-module order | **RESULT OK, bad 0** (`replay/statecheck.*`) |
| Link counts (`replay/links.txt`) | 28 rebuilt at link count 1; 1,428 reused, all hard links |
| Roots | root `TCSlib` was rebuilt (rc 0). `audits/garg-ch1-3/Checks` and `audits/pass-shelat/Checks` were reused, since their closure keys are unchanged |
| Re-check of both `Checks` roots (`replay/build-roots/`, `tools/g54/run-roots.sh`) | rc 0, 0 errors, no `sorry` warning; oleans **byte-identical** to the reused ones (`roots-before.txt`), now at link count 1. The state check after it is again OK over 1,456 (`statecheck-final.*`) |
| Output map (`replay/output-map.tsv`, `mapnoml.py`, no Mathlib) | 1,487 entries, SHA-256 `5d0f72c825db125194fcd359989366ccfa25b7ec4120a2c5a01e874ab2e1ce54`; unchanged after the roots re-check |
| Map vs D4's map | 1,474 equal; 4 changed (`LWE`, `LWE/BitEncoding`, the `GSW` and `Homomorphic` facades); 9 added (the 8 new GSW modules and `LWE/Ratio`); none removed |

**`audits/pass-shelat/Checks` axiom prints.** One `sorryAx` line, on
`Complexity.NUPPT.decides_of_decidesWithAdviceInTime`, an admitted declaration counted in §4. The log is
byte-identical to D4's log of the same module.

**Independent cross-checks** (builds are deterministic):
- **Against snapshot #11** (B6 `bff0567b`, map `olean-snapshot.map-bff0567b.tsv`, SHA-256 in
  `replay/snapshot11-map.sha256`):
  - 26 of the 28 rebuilt oleans are byte-equal to snapshot #11's. The other two are `Branching` and `DecryptFormula`,
    which #392 filled after B6 (`replay/rebuilt-vs-snapshot11.txt`).
  - Over the whole order, every module whose import-closure key is equal at the scratch commit and at B6 (647) has a
    byte-equal olean; no exception (`replay/keycmp-snapshot11.txt`, `tools/g54/keycmp.py`).
- **Against the U12/U13 review:** `Branching.olean` (`aa01dfa1…`) and `DecryptFormula.olean` (`8f73be82…`) equal the
  objects recorded by the U12/U13 review replay (Gate 53's evidence, stack `51d46089`).

## 4. Admissions (`admissions/`, `sorryscan.py` over each full order)

| Tree | Census |
|---|---|
| S2-A base `61a5f0fb` (1,447) | `TOTAL 192 in 44 modules; native_decide 0; axiom 0` |
| PR head `9f7f409c` (1,447) | **192 in 44**, byte-identical to the base's and to D4's `lib-head.txt` |
| Records tip `88362926` (1,456) | **207 in 50**: the base's 192/44 plus 15 in 6 GSW modules (`Bootstrap` 5, `Circular` 1, `Leveled` 2, `LeveledSecurity` 2, `PolyRatio` 3, `Asymptotic` 2) |
| Merge `62c27942` (1,456) | **207 in 50**, byte-identical to the records tip's census |

**Total:** S2-A's 192/44 + the records side's 15/6 = **207 in 50**. S2-A adds and removes no admission; the merge adds
none.

## 5. Lint delta against the records tip (`lint/`)

**`campaign_style_lint --check8b`**, merge vs records tip. The scripts tree is identical at both.

| Subtree | Records tip | Merge |
|---|---|---|
| `TCSlib/Complexity` | 25 FAIL / 390 WARN | 25 / **389** |
| `TCSlib/Cryptography` | 92 / 103 | 92 / **104** |
| `TCSlib/InformationTheory` | 5 / 2 | 5 / 2 |

- **Complexity:** the one changed line is the removed check-8b `toFinTM` WARN.
- **Cryptography:** 23 changed lines:
  - the new size WARN for `OneWay.lean` (1,094 lines; Stage 3, Q-D2-3);
  - line-count updates for `Collections`, `Factoring`, `RSA` and `Rabin`;
  - check-8 lists that shrink in `Ensembles`, `EnsemblesLemmas`, `HardCoreLoops`, `OneWay`, `OneWayYao`, `InnerProduct`
    and `GeneratorFromPermutation`.
- **The delta is S2-A's own.** The FAIL/WARN line delta tip → merge is byte-identical to the delta base → head
  (D1's base outputs vs D4's head outputs; `lint/delta-*`).

**`style_lint`** on the 75 files the merge changes against the base: 9 findings at the merge, 8 at the tip
(`style-merged-75.txt`, `style-tip-75.txt`).
- **The only new finding:** `OneWay.lean` 1,095 lines (> 1,000), ruled for Stage 3.
- **Already there, sizes changed:** `Collections` 1,124 → 1,177, `Factoring` 1,814 → 1,924, `RSA` 2,433 → 2,435,
  `Rabin` 3,558 → 3,563.
- **Unchanged:** the `Enumeration`, `BitLists` and `LeftoverHash` findings, and the `DyadicUniform` parse artifact
  (moved line).

## 6. Seals on the merged tree (`seal/`)

Canonical **coe-A** for D4's 11 owners: the 10 S2-A owners and the downstream `FromPermutation`.
- **Tools:** D4's `finalseal.sh` re-pointed to the merged worktree and tree (`tools/g54/sealg54.sh`); the collector;
  `mkseals_coe.py` with the archived Gate 06/10 instrumenter, unmodified; the gated runner (`lean -DmaxErrors=0`, no
  `-o`).
- **Collector:** rc 0. Its log is byte-identical to D4's collector log.
- **Seal sources:** the 11 generated sources are byte-identical to D4's coe-A sources once the probe-package name is
  normalized (`seal-source-vs-d4.txt`).

| Owner | coe-A, merged tree | D4 |
|---|---|---|
| `Asymptotic/Collections`, `EnsemblesLemmas`, `HardCoreLemmas`, `HardCore/Functions`, `HardCorePermutation/GoldreichLevin`, `OneWayYao`, `SamplingFinDist`; `Candidates/Factoring`; `Hashing/SIS/CollisionOutput`; `InformationTheory/Extractors` | **0** each | 0 |
| `Pseudorandom/Generators/Asymptotic/FromPermutation` | **2** (rc 1) | 2 |

- **Same results as D4:** every seal log is byte-identical to D4's once the package name is normalized, so the error
  lines are too (`compare-d4.txt`).
- **The `FromPermutation` residue** is job J3's (`exists_owpPredictorSnoc`, l.374 and l.380 of the seal source).
- **No seal B here.** S2-A's owners have the same import closures in the merge as at the head, so D4's coe-B results
  stand.

## 7. Staging checks (`checks/`; git objects and `python3 -I` only)

| File | What it shows |
|---|---|
| `decls2-base-vs-head.tsv` | D4's decls2, base vs head: 41 ADDED, 15 CHANGED, 4 REMOVED |
| `decls2-to-items.tsv` | every decls2 row mapped to its `s2a-items.tsv` row(s) or D-ruling: **0 unmapped** |
| `added-proofs.tsv` | the proof term of each ADDED declaration: 19 `rfl`, 4 `Iff.rfl`, 18 others |
| `private-*.txt` | private declarations base vs head: + `invProbAt_glPad_eq`, + `oddParam_eval`, − `fac_ofFn_halves` |
| `simp-*.txt` | the `@[simp]`/`@[simps]` attributes in the 63 files: unchanged, except the removed `@[simps! …]` (Q-D2-5) |
| `added-scan.txt` | added lines: 0 `sorry`, `admit`, `native_decide`, `axiom`, `set_option`, `attribute`. 1 import (S2-RP-031). The 5 `unfold`s are of same-file definitions. Width: 6 added lines over 100 code points (pack S-2) |
| `items-owner-files.txt`, `diff-files.txt` | the 63 changed files = the 61 `TCSlib` owner files of `s2a-items.tsv` + `Games/BitCodec` + `InformationTheory/Extractors` |
| `shortname-hits.txt` | other declarations with the same short name as each new or changed one, at the merge (pack question G, S-1) |
| `commits.txt` | the 43 commits: 1 parent each, all with an SSH signature header |
| `batch-manifests.txt` | the four batch manifests re-verified at staging, 0 failures: D1 `dfab3215…` (24 rows), D2 `7d0ecfda…` (1,650), D3 `35e6dcf7…` (408), D4 `51d39684…` (544) |

**`batches/d1` … `d4`** carry the pieces of the batch evidence that a reading audit needs:
- each batch's manifest, commit list, decls2, admissions, replay summaries and lint findings;
- the seal run tables, orders and `errdecl` maps;
- the Q-A2 probes and controls (`d2/qa2`, `d3/qa2`) and D4's `SimpsEq` probe (`d4/q5`);
- the output-map hashes.

Large logs and seal sources stay in `$SP/s2a-d*/`, under the manifests.

## 8. Clean-up

- **Kept for adoption:** the merged replay tree `$SP/g54/olean-replay-g54`. It is the candidate olean snapshot for the
  #390 merge while the records tip's Lean stays at `745bf4b4`. It is a hard-link copy of D4's tree: 30 files (5.6 MB)
  are its own, the 28 rebuilt oleans and the 2 re-checked `Checks` oleans.
- **Removed:** the scratch worktree `$SP/g54/mwt` (with `git worktree prune`). Commit `62c27942` remains as an
  unreferenced object, never pushed.
- **Untouched:** D4's tree and `$SP/olean-snapshot*`.
