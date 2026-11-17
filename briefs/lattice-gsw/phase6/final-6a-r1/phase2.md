# gsw-6a-statements · maintainer delivery review (r1), phase 2: merged-tree Lean replays

**Verdict.**
- **`land/gsw-6a-o1`** (`a57dcf77a06455145181a26f9163abc5944157b4`, PR O1): **PASS**. It is ready for its draft PR
  against `cryptography/pass-shelat-ch2-4`.
- **`land/gsw-6a-statements`** (`66036926bcbffa9caf44f9e9469ca63bc555c374`, the statement PR with **LE-ren**): **PASS**.
  It is ready for its draft PR, stacked on PR O1 (base `land/gsw-6a-o1` until O1 merges).
- Phase 2 found 0 blockers, 0 majors, 0 minors and 2 new infos (G6A-F14, G6A-F15). G6A-F01 is closed by LE-ren, and
  G6A-F05 is confirmed pre-existing: the two `TreeNCAC` seal failures are byte-identical at the tip.
- Every check of the phase-1 checklist (P2-0 to P2-7) holds:

  | Check | O1 head (R1) | Statement head with LE-ren (R2) |
  |---|---|---|
  | Range-diff against the delivered series | 1/1 `=` | 5/5 `=`, plus LE-ren |
  | Tree, Lean paths | equal to phase 1's `fd9a242f` | `~1` equal to `31a37a04`; LE-ren byte-identical to the proposed diff |
  | Rebuilt modules | 9 | 20 |
  | Every rebuilt module | rc 0, 0 `error:`/`error(` | the same |
  | State check (snapshot closure + new) | 1424/1424 OK | 1435/1435 OK |
  | Admissions against the tip | +0 | **+98**, exactly the 98 targets |
  | Axioms | 141 constants, standard only | 544 constants; `sorryAx` in exactly the 98 targets + 5 N2/N12–N13 dependents |
  | Seals (strict A/B, coe A/B) | as expected; `TreeNCAC` 2, pre-existing | as expected; `TreeNCAC` 2, pre-existing; root coe-A 13,991, 0 errors |
  | Controls | ALL_OK (strict and coe) | ALL_OK (strict and coe); the delivery's 30 paired controls 30/30 |
  | Explicit-unfold scan | 0 foreign outside `TreeNCAC`'s 4 pre-existing | 0 foreign in the 13 new files |
  | Lint | no new FAIL/WARN | no new FAIL/WARN; `style_lint` 0 in the new files |

- **Cross-merge** with #340 (`916afc25`) and #346 (`89a18a82`): both merge cleanly with each head. Neither shares a path
  with the series, and the only module in two downstreams is the import-only root `TCSlib`, so no cross-build is needed
  (§ X).
- Snapshot #4 rehashed 0/0/0 before the replays, after R1, after R2 and at the end.

Run on 2026-11-17, 05:31–07:45 UTC. `$SP` is `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.
- **Evidence:** `gsw-6a-final-r1-phase2-evidence.zip`, under `gsw-6a-final-r1-phase2/`. It has `PROVENANCE.txt` and
  `SHA256SUMS`, and its own SHA-256 is in `evidence-SHA256SUMS`.
- **Not done:** nothing was pushed or committed to the records branch, no PR was opened, and the two landing branches
  stay local. The records files (this file, the zip, `evidence-SHA256SUMS`, `review.md`) are left uncommitted.
- **Builds:** no `lake build` and no cache get. Every module and probe ran through `scripts/lean_check_tree.sh`
  (`runner.py`) or `lean -DmaxErrors=0` without `-o` (`runner_full.py`), with `python3 -I`.
- **Lean slots:** at most 2 of this job's Lean processes at once, always on different olean trees (R1, R2, the base
  copy, and a read-only `cp -al` copy of R2 for the root seal and the axiom probe); another agent's job (`g44r2`) held
  the third slot for part of the run, and the machine never exceeded 3.
- **Other directories:** the snapshot, `olean-replay-g44`, `olean-replay-346c` and other agents' directories were not
  written; only this job's PIDs were ever signalled (none was).

## P2-0 Tip and snapshot
- `git fetch` gave the records tip **`84d144b565bd7a983a05d5b8dda87442bdaec1a4`** ("Records: phase 6a rulings Q1-Q4
  (LE-ren; DL-54)").
  - It is records-only since phase 1's `b9860ca8`: the 9 paths that changed are Markdown, zips and SHA256SUMS
    (`landing/trees.txt`).
  - `git diff 463f2244 84d144b5 -- '*.lean' lean-toolchain lake-manifest.json lakefile.lean scripts audits` is empty,
    so the tip is Lean-equal to snapshot #4's T, and phase 1's merge-trees need not be redone. They were recomputed
    anyway (P2-1, § X) and agree.
- **Snapshot #4** (`$SP/olean-snapshot`): `snapmap.py verify` against `olean-snapshot.map-463f2244.tsv`
  (SHA-256 `6607620d…41e7`) gives **1453 files, 0 extra / 0 changed / 0 missing**, no symlinks, no empty directories, at
  the start, after R1, after R2 and at the end (`snapshot/`). It was read only as the source of `cp -al`.
- **Disk:** 5377 MB free at the start (P2-0 asks for ≥ 1 GB), 4174 MB at the lowest point, 4352 MB at the end.

## P2-1 Landing branches (sparse worktree; `landing/`)
- **Worktree:** `git worktree add --no-checkout` at the tip, then a non-cone sparse checkout of the 18 series paths only
  (108 files, 2.3 MB); the main worktree's sparse state was not changed. It was removed after the commits.
- **`land/gsw-6a-o1`** = **`a57dcf77a06455145181a26f9163abc5944157b4`**: `git cherry-pick -S 413e9aa4` onto the tip. Tree
  `ba964762…` = `merge-tree 84d144b5 × 413e9aa4`; 0 Lean/lake/scripts/audits paths differ from phase 1's `fd9a242f`
  (the 9 paths that differ are the records files the tip gained since `b9860ca8`). Its diff is O1's four files.
- **`land/gsw-6a-statements`** = **`66036926bcbffa9caf44f9e9469ca63bc555c374`**, on `land/gsw-6a-o1`:
  - five signed picks `5127c5cd`, `2f8e03ef`, `76531c8f`, `5233fe4b`, `675371dc` of `ad8e170f..ec36703b`; `~1` has
    tree `140f5db9…` = `merge-tree 84d144b5 × ec36703b`, and 0 Lean/lake/`machine-library-design.md` paths differ from
    phase 1's `31a37a04`;
  - then **LE-ren** `66036926`, one signed commit with this session's `Co-Authored-By`/`Claude-Session` trailers.
- **Range-diffs** (`range-diff.txt`): `f6f295a6..413e9aa4` against `84d144b5..land/gsw-6a-o1` gives **1/1 `=`**;
  `413e9aa4..ec36703b` against `land/gsw-6a-o1..land/gsw-6a-statements` gives **5/5 `=`** and `> 6: 66036926` (LE-ren).
  The picks keep the worker's messages and trailers verbatim, as for #346 and #352.
- **LE-ren** (`LE-ren-commit.diff`, `LE-ren-hunkcmp.txt`): the per-file hunks are **byte-identical** to
  `landing/LE-ren-proposed.diff` of the phase-1 evidence (3 files, 6 hunks; only the hunk-header context text and the
  file order differ, which `hunkcmp.py` ignores). It is −35/+5 in `Combinators.lean` (659 → **629** lines), ±1 in the
  `FormulaArith.lean` facade contents and ±1 in the registry row of `machine-library-design.md`.
- **No `rename` reference remains** (`rename-scan.txt`): at the head, `git grep` for `TreeCircuit.rename`,
  `rename_eval`, `depth_rename` and `rename_eq` over `TCSlib`, `TCSlib.lean`, `audits`, `blueprint` and
  `machine-library-design.md` finds nothing, and no Lean file contains `.rename`. The only word hits in the 18 series
  paths are two unrelated pre-existing sentences of `machine-library-design.md` (lines 245 and 2721). The R2 probe
  confirms that none of the four constants, and no `TreeCircuit*rename*` constant, exists in the closure, while
  `reidx`, `reidx_eval` and `reidx_depth` are present with the expected statements and standard axioms (§ R2-4).
- **Export checks** (`export-check.txt`, `exportcheck-*.txt`): `src-o1/` equals the O1 head byte for byte (4/4);
  `src/` equals `land/gsw-6a-statements~1` in 17 of 18 files, the 18th being `TCSlib.lean`, which is the tip's plus the
  one line `import TCSlib.Complexity.BranchingPrograms` (the tip has #331's Cryptography block); the LE-ren head
  differs from `src/` in exactly those plus LE-ren's 3 files. The three `git archive` exports (tip, O1 head, statement
  head) are blob-exact (1574, 1576, 1587 files; 0/0/0).
- **decls2** (phase 1's unmodified `decls2.py`, tip against the LE-ren head; `statements/`): **267 ADDED, 0 CHANGED,
  0 REMOVED**, empty `.err`. That is phase 1's 271 rows minus exactly `TreeCircuit.rename`, `rename_eq`, `rename_eval`
  and `depth_rename`; every other row is identical in kind and normalized statement.
- **Signatures** (`signatures.txt`): all 7 landing commits carry an SSHSIG with key
  `SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc`, the key of the records tip `84d144b5`; `413e9aa4` and
  `ec36703b` are unsigned. Key identity only (BS-F12): `ssh-keygen` is not installed.

## R1 Replay of the O1 head (`r1/`)
- **Recipe** (`snapshots.md`): `cp -al $SP/olean-snapshot $SP/olean-replay-6a-o1`; `mloverlay.sh` (3346 symlinks);
  `mathlibextra.sh` NthRootLemmas, olean **`c0a9cff0…`**; `stateplan init` at `463f2244` (1422 modules); `downorder.py`
  (changed 4, down 9); `fullorder.py` (1424, roots `TCSlib` and both `audits/*/Checks`); `stateplan plan`: **9 to
  build, 1415 reused**, and the queue equals `down.txt` as a set.
- The 9 are exactly the review's: `Combinators`, `TreeNCAC`, `NCAC`, `FormulaArith`, `Parity`, `Hierarchy`,
  `CircuitComplexity`, `ComputationalModels`, `TCSlib`.
- **Build** (`runner.py` through `lean_check_tree.sh`, `TCSLIB_OLEANS=$SP/olean-replay-6a-o1`, 05:42:03–05:43:14,
  71 s, max RSS 4.4 GB): **9/9 rc 0**; `error:` 0, `error(` 0, substring "error" 0; 0 warnings; no log/record mismatch
  (`permod.py`).
- **Accept:** `stateplan update` took 9; `check` over the full order gives **1424/1424 OK, RESULT OK** (again after R2:
  R1 was never written to); **all 9 rebuilt oleans have link count 1** with object hash equal to the record.
- **Warnings** (`warncmp.py`): 5 SAME as the snapshot's own build logs of the same source (`NCAC`, `Parity`,
  `Hierarchy`, `ComputationalModels`, root); the 4 changed modules are NEWSRC with 0 warnings.
- **Admissions** (`admissions/r1-delta.txt`): **+0**. Every rebuilt module has 0 `sorry` warnings, and every one that
  exists at the tip has 0 `sorry`/`admit` tokens there. The source census is 827 tokens in 88 files at both the tip
  and the O1 head.
- **Axioms** (`probes/o1/`; the delivery's `AxiomProbe.lean` body restricted to O1's three modules): **141 constants**
  (`Combinators` 63, `TreeNCAC` 78; the facade defines none), axiom sets `[]` 62, `[propext]` 3,
  `[propext, Quot.sound]` 3, `[propext, Classical.choice, Quot.sound]` 73: **standard only**, no `sorryAx`.
- **Rule 10** (`rule10/o1/`; owners `Combinators`, the `FormulaArith` facade, `TreeNCAC` and the `CircuitComplexity`
  facade, i.e. all four of O1's files; `touched.json` against the tip):

  | Owner | Requests (strict A / B / coe A / B) | Errors |
  |---|---|---|
  | `Combinators` | 174/174/174/174 | 0 |
  | `FormulaArith` | 194/194/194/194 | 0 |
  | `TreeNCAC` | 194/194/194/194 | 2 per variant, `maxDepth_map_le` and `maxFaninL_map_le` (G6A-F05) |
  | `CircuitComplexity` (facade, chunked) | 3659 in all four | 0 |

  - Every probe has install and EOF records. Strict and coe request sets are equal (no `FinDist` in these closures).
  - **Controls** (`mkctl_g6a.py`, the covering subset; 8 probes per harness): 10 sealed negatives per harness
    (`balanced` 2, `sumSize` 4, `maxFaninL` 4), each failing exactly once; 0 positives fail; the unsealed probes give 0
    errors: **ALL_OK in strict and in coe**. The `sumSize`/`maxFaninL` rows exercise O1's two extra repairs (G6A-F02):
    `sumSize_nil`/`maxFaninL_nil` pass under the seal and the `rfl` unfoldings fail.
  - **Explicit-unfold scan** of the four files: 127 items (84 THEOREM, 31 OWNED_DEFINITION, 8 LOCAL_OR_UNRESOLVED);
    **4 foreign**, all `TreeNCAC` (`:188` `eval_node_map`, `:228`, `:250`, `:268` `toBinary_*`), which are the 4
    pre-existing unfolds of G6A-F05. At the tip the same file has 7: these 4 (then at `:366`, `:406`, `:428`, `:446`)
    and the 3 at `:195`, `:199`, `:261` that O1's brief-named repairs remove. `Combinators`, `FormulaArith` and the
    facade have 0.
- **Base seals at the tip** (`rule10/base/`; tip export, a `cp -al` copy of the snapshot with the overlay, read only by
  the probes and deleted afterwards): `TreeNCAC` has 94 requests in all four variants and fails **4 times** per variant:
  `maxDepth_map_le`, `maxFaninL_map_le`, and `sumSize_pairUp`, `maxFaninL_pairUp` (the nil cases that O1 moves to
  `Combinators` and repairs).
- **G6A-F05 confirmed pre-existing** (`rule10/f05-base-vs-o1.txt`, `f05-base-vs-stmt.txt`, `f05cmp.py`): in each of the
  four variants, at both heads, the two remaining failures are in `maxDepth_map_le` and `maxFaninL_map_le`, whose
  declaration text is byte-identical to the tip's and whose error messages (`Type mismatch … Nat.zero_le …`) are
  identical to the tip's. No failure is new.

## R2 Replay of the statement head with LE-ren (`r2/`)
- **Recipe:** `cp -al $SP/olean-replay-6a-o1 $SP/olean-replay-6a-stmt` (the overlay and NthRootLemmas `c0a9cff0…` came
  with it); R1's checked state; `downorder.py` against the O1 head (changed 16, down 20); `fullorder.py` (1435);
  `stateplan plan`: **20 to build, 1415 reused** (the queue equals `down.txt`).
- The 20 are the review's: the 11 new modules, the changed `Combinators`, `FormulaArith`, `CircuitComplexity`,
  `ComputationalModels` and `TCSlib`, and the downstream `TreeNCAC`, `NCAC`, `Parity` and `Hierarchy`. They are
  phase 1's `landing/downstream-merged-final.txt` (17 modules) plus `Defs`, `Combinators` and `NANDForm`.
- **Build** (05:45:18–05:46:48, 90 s, max RSS 4.4 GB): **20/20 rc 0**; `error:` 0, `error(` 0, substring "error" 0; 98
  warnings, all `declaration uses 'sorry'`; no log/record mismatch.
- **Accept:** `stateplan update` took 20; `check` gives **1435/1435 OK, RESULT OK**; **all 20 rebuilt oleans have link
  count 1**. R1 was not written: its state check still gives 1424/1424 OK.
- **Warnings:** 4 SAME (`NCAC`, `Parity`, `Hierarchy` against the snapshot build; `TreeNCAC` against R1); 16 NEWSRC,
  whose only warnings are the 98 `sorry` lines.

### R2-3 Admissions (`admissions/r2-delta.txt`, `admcheck.py`)
- **Against the tip: +98**, per module Defs 11, Eval 5, Barrington 11, BarringtonConverse 11, NC1 5, NANDForm 6,
  NANDLayering 7, Combinators **24**, CarrySave 7, Compare 7, ModSum 4; every other rebuilt module 0 (absent at the tip
  or 0 tokens there).
- **Exactly the targets:** each `sorry` warning was mapped to its declaration (touched spans) and matched against the
  delivered `rowmap.txt` targets minus `rename_eval` and `depth_rename`: **98 targets, 98 admitted, 98 matched, 0 not a
  target, 0 twice, 0 missing: EXACT**.
- Source census: 827 tokens (88 files) at the tip, 932 (99) at `~1`, 930 (99) at the head; the 5 other new tokens
  are prose in docstrings.

### R2-4 Axioms and the `sorryAx` trace (`probes/root/`, on the read-only copy of R2)
- The delivery's `AxiomProbe.lean` body unchanged (census and trace of the 13 new modules and `TreeNCAC`), plus the
  LE-ren absence check and the `reidx` family.
- **544 constants** (DECL 382, AUX 162): **delivered 548 minus exactly the 4 LE-ren constants**; every other DECL, AUX
  and TRACE line is byte-identical to the delivered `AxiomProbe.log` (`axioms-vs-delivery.txt`).
- **No non-standard axiom other than `sorryAx`.** `sorryAx` is in **103** constants: the **98 targets** and the 5
  dependents `toNANDForm` and `toNANDForm_eq` (through N2 `nandGadget_correct` only) and `layerNAND`, `layerNAND_gates`
  and `layerNAND_output` (through N12 `layerGates_acyclic` and N13 `layerOutput_lt` only). No AUX constant has
  `sorryAx`.
- **Traces:** 89 targets reach only themselves. The 9 targets whose statements name `toNANDForm` (`toNANDForm_eval`,
  `_isNANDForm`, `_size_le`, `_depth_le`) or `layerNAND` (`layerNAND_eval`, `_isNANDForm`, `_isLayered`, `_depth`,
  `_size_le`) reach themselves plus N2, or plus N12–N13, through those definitions, as in the delivery's own log
  (G6A-F14).
- `reidx : TreeCircuit m → (Fin m → Fin m') → TreeCircuit m'`, `reidx_eval : (c.reidx f).eval g = c.eval (g ∘ f)` and
  `reidx_depth : (c.reidx f).depth = c.depth` (`BooleanAnalysis/LMN/CircuitReindex`) use `[propext, Classical.choice,
  Quot.sound]`.

### R2-5 Rule 10 (`rule10/stmt/`, `rule10/root/`)
- **Seals of the 16 new or changed files** (`SEAL_CHUNK=1000`; strict A / B and coe A / B):

  | Owner | Requests (A/B/coe A/coe B) | Errors |
  |---|---|---|
  | `BranchingPrograms/Defs` | 0/0/0/0 | 0 |
  | `BranchingPrograms/Eval` | 25/25/25/25 | 0 |
  | `BranchingPrograms/Barrington` | 119/119/119/119 | 0 |
  | `BranchingPrograms/BarringtonConverse` | 243/243/243/243 | 0 |
  | `BranchingPrograms/NC1` | 333/333/333/333 | 0 |
  | `BranchingPrograms` (facade) | 335/335/335/335 | 0 |
  | `FormulaArith/Combinators` | 174/174/174/174 | 0 |
  | `FormulaArith/CarrySave` | 253/253/253/253 | 0 |
  | `FormulaArith/Compare` | 269/269/269/269 | 0 |
  | `FormulaArith/ModSum` | 273/273/273/273 | 0 |
  | `FormulaArith` (facade) | 276/276/276/276 | 0 |
  | `NANDForm` | 180/180/180/180 | 0 |
  | `NANDLayering` | 187/187/187/187 | 0 |
  | `TreeNCAC` | 218/218/218/218 | 2 per variant, pre-existing (G6A-F05) |
  | `CircuitComplexity` (facade, 4 chunks) | 3726/3726/3726/3726 | 0 |
  | `ComputationalModels` (2 chunks) | 1106/1107/1106/1107 | 0 |

  - Every probe has install and EOF records.
  - **Against the delivery's seal records** (`stmt-requests-vs-delivery.txt`): in all 64 owner-variant pairs the
    request set is the delivered one minus at most the single name `BoolCircuit.TreeCircuit.rename` (absent in the 5
    owners that do not import `Combinators`, and in `Combinators` itself), and contains no other name. The counts are
    the delivered ones minus 1 where `rename` was in the closure (e.g. the facade 3727 → 3726, root below).
- **Root coe-A** (the canonical variant; `rule10/root/`, one owner `TCSlib`, chunked into 14 commands): **13,991 requests, 0 errors**; 14 install and 14 EOF
  records, each `requested = verified` (sums 13,991), 4,360 s, 5.0 GB (`root-chunks.txt`). Against the delivery's root
  record (13,761 at the issue base) the set loses exactly `TreeCircuit.rename` and gains 231 names, all from modules
  the tip added since `f6f295a6` (`Yao` 160, `IdentityBased` 47, `Pairing`/`Joux` 24; `root-vs-delivery.txt`).
- **Controls** (`mkctl_g6a.py`; 40 probes per harness, the covering subset of 20 sealed records): **92 sealed negatives
  per harness** over all 12 rows (`yield` 8, `evalWith` 2, `sigma1` 4, `topDepth` 4, `balanced` 14, `sumSize` 18,
  `maxFaninL` 18, `IsNAND` 4, `litInput` 2, `val` 8, `bitAt` 6, `modSumDepth` 4), each failing exactly once; 0 of the
  92 positives fail; the 184 unsealed controls give 0 errors: **ALL_OK in strict and in coe**.
- **The delivery's own 30 paired controls** (`evidence/rule10/controls/Control_*.lean`, unchanged, on R2;
  `rule10/delivered-controls/`): **30/30 OK** (10 owners × unsealed negative 0, sealed negative 1, sealed positive 0).
- **Explicit-unfold scan** of the 16 files: 167 items (112 THEOREM, 43 OWNED_DEFINITION, 8 LOCAL_OR_UNRESOLVED);
  **0 foreign in the 13 new files** and the facades; the only foreign items are `TreeNCAC`'s 4 pre-existing ones (R1).

### R2-6 Lint, sizes and clashes (`lint/`, `clash/`)
- **`campaign_style_lint.py TCSlib/Complexity --check8b`**, each from its own export: tip 25 FAIL / 390 WARN over 500
  files; O1 head 25/390 over 502; statement head 25/390 over 513. **The FAIL and WARN line sets are identical** to the
  tip's (0 diff lines); only INFO size lines change.
- **`style_lint.py`:** **0 findings in the 13 new files** (and in O1's 2 new files at R1). Over all 17 changed Lean
  files, the 11 findings (`TCSlib.lean` 6, `ComputationalModels.lean` 5) are identical at the tip.
- **`sk15`** (the stricter ≥ 15-line measure): 3 proved helpers without a sketch, all ≤ 20 lines by `style_lint`'s
  measure: `combineFuel_maxFanin` (O1's moved private proof, byte-identical), `csaLevelsAux_fuel` (private, 18) and
  `modSumInterval_eq` (an `rfl` reader whose statement is long). No action.
- **Sizes** (`sizes.tsv`): every new file is under 600 lines except `Combinators` at **629** (659 before LE-ren;
  G6A-F06); every new file is at most 100 characters wide. Lines over 100 characters exist only in `TreeNCAC` (2; 5 at
  the tip), `CircuitComplexity` (1; 1) and `ComputationalModels` (1; 1), all pre-existing.
- **Clash scan at the tip** (phase 1's `names.py`): 31,175 names at the tip, 31,440 at the head; **281 new names**
  (18 private) in the changed files, which is phase 1's 285 minus the 4 LE-ren names. 11 share a full name with a tip
  declaration in another file, all O1's private moves from `TreeNCAC` (whose tip copies O1 removes); **0 other
  clashes**; no new name is declared twice at the head.

## X Cross-merge with #340 and #346 (`cross/`)
- Both PRs are open drafts with the given heads (`pr-state.txt`).
- `git merge-tree --write-tree` is clean (rc 0) for the tip, the O1 head and the statement head against each:
  #340 → `2226d6f0`, `fd3b64f1`, **`5fdb4737`**; #346 → `96bf2df4`, `d42f80a8`, **`d10e98af`**. Phase 1's merges
  (`f4e92964`, `292f1b60`) were with `ec36703b`, before LE-ren.
- **No file overlap:** #340 changes `Pairing/Assumptions.lean`, #346 changes 8 `IdentityBased` files; none is among the
  18 series paths, and each merged tree differs from the statement head in exactly the PR's files.
- **No closure overlap** (`closure-overlap.txt`, `downorder.py` on each merged tree): neither PR's changed modules lie in
  the non-root closure of the 6a downstream, and no 6a module lies in the non-root closure of either PR's downstream.
  The only module in both downstreams is the root `TCSlib`, an import-only file that every PR rebuilds. So the replay
  outputs are independent, and **no cross-build is needed**: whichever merges first, the other's prospective tree
  changes only in files outside its closure, and its re-replay on the new snapshot rebuilds the same modules.

## P2-8 Merge order and adoption (for the maintainer; nothing merged here)
1. **PR O1 first** (base `cryptography/pass-shelat-ch2-4`, head `a57dcf77`). On merge, run
   `git diff --name-only <merge> ba964762a9967f5e03011f44102bb2dab8510ecf -- '*.lean' lean-toolchain lake-manifest.json`.
   If it is empty, adopt **`$SP/olean-replay-6a-o1`** (recipe step 6) as snapshot #5.
2. **Then the statement PR**, retargeted to the records branch. If it merges right after O1 with the tip otherwise
   unchanged, run the step-3 diff against `34e41f159539c28713771186047a3f46c67c426a`; if empty, adopt
   **`$SP/olean-replay-6a-stmt`** (it already contains R1 and was built on it). Otherwise re-replay its 20 modules on the
   new snapshot.
3. If #340 or #346 merges first, neither replay output is adoptable as is (the step-3 diff names that PR's files);
   re-replay on the new snapshot: 9 modules for O1 and 20 for the statements, as above.
4. Either way, delete the output that is not adopted once its evidence is recorded.

## Findings (phase 2)
| # | Severity | Finding | Disposition |
|---|---|---|---|
| G6A-F01 | major, **closed** | LE-ren (`66036926`) drops `rename`, `rename_eq`, `rename_eval`, `depth_rename`, byte-identical to the proposed diff. Admissions 100 → 98, constants 548 → 544, `Combinators` 659 → 629; no reference remains. | Dedup entry DL-54 (move `reidx` into `Combinators`) stays open. |
| G6A-F02 | minor, ruled (Q2 A) | O1's five repairs are on the branch unchanged. The new controls exercise the two extra ones (`sumSize_nil`, `maxFaninL_nil`), and the base seal shows the two nil cases fail without them. | None. |
| G6A-F05 | info, **pre-existing (confirmed)** | `TreeNCAC` fails its seal twice at both heads, at `maxDepth_map_le` and `maxFaninL_map_le`, with declaration text and error messages identical to the tip's, in all four variants. The tip fails 4 times (also O1's two nil cases). The 4 explicit foreign unfolds are the tip's. | Clean-up part 2, as recorded. |
| G6A-F14 | info, record correction | Phase 1's "each target's trace reaches only itself" holds for 89 of the 98 targets. The 9 that name `toNANDForm` or `layerNAND` also reach N2 or N12–N13 through those definitions; the delivery's own trace shows the same. Expected: the definitions carry those admissions. | None; the traces clear when N2, N12 and N13 are filled. |
| G6A-F15 | info, my process | The Rule 10 driver `rule10_g6a.sh` was edited twice while the statement series was running (a base-scan line, a tree path for the root series). Bash had parsed the running loop, so every phase used the original text; after the last phase it printed a syntax error at the shifted offset (`rule10-stmt-driver.out`). All outputs are complete and checked. | None. |

## Replay outputs (kept)
- **`$SP/olean-replay-6a-o1`** (R1, REV `a57dcf77`, tree `ba964762`): 1455 files (1453 snapshot oleans with 9 rebuilt,
  link count 1, plus `Combinators` and `FormulaArith` new) and NthRootLemmas, plus 3346 Mathlib overlay symlinks. State
  check 1424/1424 OK. Adoptable on the O1 merge (P2-8.1). Remove `Mathlib/` at adoption.
- **`$SP/olean-replay-6a-stmt`** (R2, REV `66036926`, tree `34e41f15`): 1466 files and the overlay; 20 rebuilt oleans
  with link count 1. State check 1435/1435 OK. Adoptable on the statement merge if it follows O1 directly (P2-8.2).
- Deleted: the export worktrees, the base copy `olean-base-tip`, the read-only R2 copy `olean-r2-probe` and the
  sparse landing worktree.

**Phase 2 done: both landing branches pass. PR O1 is ready for its draft PR; the statement PR follows, stacked on it.**

## Re-replay on snapshot #5 (2026-11-17)
**Verdict: both heads PASS again; nothing changes against snapshot #4 except what #340 and #346 add to the root.**
#340 and #346 merged after phase 2, so neither replay output above could be adopted (P2-8.3). Both landing branches were
re-cut onto the new records tip and replayed on olean snapshot #5, and the checks that the new base can affect were re-run.

| | O1 | Statements with LE-ren |
|---|---|---|
| New head | **`a616adcac0760ab56b1b0a2a4869f4763843f9ab`** | **`73aedcdaaaffef7e69ab012d9b9195f150bae68d`** |
| Old head (phase 2, on `84d144b5`) | `a57dcf77` | `66036926` |
| Tree = `merge-tree e1d39836 × old head` | `a461632b`, equal | `2c243bb1`, equal |
| Range-diff | 1/1 `=` | 6/6 `=` (5 picks and LE-ren) |
| Rebuilt modules (rc 0, 0 `error:`/`error(`) | 9/9 | 20/20 |
| State check | 1429/1429 OK | 1440/1440 OK |
| Admissions | +0 | +98, EXACT (the 98 targets) |
| Axioms probe | 141 constants, standard only; log byte-identical to #4 | 544 constants, `sorryAx` in the 98 targets + 5; log byte-identical to #4 |
| coe-A seals of the new/changed owners | 4 owners, all SAME as #4 | 16 owners, all SAME as #4 |
| Root coe-A | n/a | 14,074 requests, 15 chunks, 0 errors (#4: 13,991; the 83 added names are all homed in #340/#346 files) |
| Lint | identical to #4 | identical to #4 |

Run 07:41–09:45 UTC. `$SP` as above. Evidence: **`gsw-6a-final-r1-rereplay5-evidence.zip`** (`985cdc5c…0f1b`), under
`gsw-6a-final-r1-rereplay5/`, with `PROVENANCE.txt` and `SHA256SUMS`; its own SHA-256 is in `evidence-SHA256SUMS`. The
phase-2 zip is unchanged.
- **Not done:** nothing was committed to the records branch, and these records files are left uncommitted. The two
  landing branches were pushed and their draft PRs opened afterwards (PR numbers in the report, not here).
- **Builds:** no `lake build` and no cache get. Modules ran through `scripts/lean_check_tree.sh` (`runner.py`); probes and
  seals ran through `lean -DmaxErrors=0` without `-o` (`runner_full.py`). Python ran as `python3 -I`.
- **Lean slots:** exactly one Lean process of this job at any time. Other agents held the other slots (up to 2), and the
  machine never exceeded 3.
- **Other directories:** the snapshot and the other agents' directories were not written. The old replays
  `olean-replay-6a-o1` and `olean-replay-6a-stmt` (built on #4, root overlapping #340/#346) were deleted at the start.

### S5-0 Tip and snapshot (`snapshot/`)
- `git fetch`: the records tip is **`e1d39836ed4a69a34914c35f4c73c71de853dcc6`** ("Records: #340/#346 merged; olean
  snapshot #5; GSW 6a phase 2 accept"). `git diff 3f540c22 e1d39836 -- '*.lean' lean-toolchain lake-manifest.json
  lakefile.lean scripts audits` is empty, so the tip is Lean-equal to snapshot #5's T. At the end of the run the tip had
  advanced to `3ef91b408b2a9303fa36c8ac696da532e4170ed0` with 4 records-only commits (bb1-sim fill phase 2, Gate 48, the
  overnight ruling): 0 Lean/lake/scripts/audits paths and no series path changed, so the re-cut heads stay Lean-equal to
  the merge with the current tip and were not re-cut again.
- **Snapshot #5:** `snapmap.py verify` against `olean-snapshot.map-3f540c22.tsv` (SHA-256 `fca1b6a3…1ef9`, as
  registered) gives **1458 files, 0 extra / 0 changed / 0 missing**, no symlinks and no empty directories, at the start,
  after R1, after R2 and at the end. It was read only as the source of `cp -al`.
- **Disk:** 4442 MB free at the start (4506 MB after deleting the #4 replays), 2994 MB at the lowest observed point (other jobs were writing too), 3618 MB at the end; never under 1.5 GB.

### S5-1 Re-cut (`landing/`)
- A sparse worktree at the tip (the 18 series paths) received `git cherry-pick -S` of `a57dcf77`, then the five picks
  `5127c5cd..675371dc`, then LE-ren `66036926`, with the messages kept. The branches were then moved with
  `git branch -f`, and the worktree was removed.
  - `land/gsw-6a-o1` moved from `a57dcf77` to **`a616adca`**.
  - `land/gsw-6a-statements` moved from `66036926` to **`73aedcda`** (picks `453fb1ab`, `c4870dd3`, `d8d0cf95`,
    `06b7734a`, `d7a72780`; LE-ren `73aedcda`).
- **Range-diff** (`range-diff.txt`): `84d144b5..a57dcf77` against `e1d39836..a616adca` gives 1/1 `=`;
  `a57dcf77..66036926` against `a616adca..73aedcda` gives 6/6 `=`.
- **Trees** (`trees.txt`):
  - Each of the 7 new commits has the tree of `git merge-tree --write-tree e1d39836 <old commit>`. The O1 head has
    `a461632b`, which also equals `merge-tree` with the worker's `413e9aa4`. `~1` has `541eb26b`, which equals
    `merge-tree` with `ec36703b`. The head has `2c243bb1`.
  - The full diffs against the base are patch-id-equal to the old ones: O1's 4 files and the statements' 18 paths.
  - The 18 series paths and the 53 paths the tip changed since `84d144b5` are disjoint.
- **Signatures** (`signatures.txt`): all 7 new commits carry an SSHSIG with key `SHA256:32dP45eS…2wc`, the same key as
  the tip and the old heads. Authorship is kept.

### S5-2 R1 (`r1/`)
- `cp -al $SP/olean-snapshot $SP/olean-replay-6a-o1`; `mloverlay.sh` made 3346 symlinks; NthRootLemmas compiled to
  **`c0a9cff0…`**.
- `stateplan init` at `3f540c22` gives 1427 modules. `downorder.py` gives changed 4 and down 9. `fullorder.py` gives
  1429. `plan` gives **9 to build and 1420 reused**, and the queue equals `down.txt`: the same 9 modules as on #4.
- **Build** (07:44:55–07:46:06): **9/9 rc 0**, with `error:` 0, `error(` 0 and substring "error" 0. There are 0 warnings
  and no log/record mismatch (`permod.tsv`).
- **Accept:** `update` took 9. `check` gives **1429/1429 RESULT OK**, and again after R2. All 9 rebuilt oleans have
  **link count 1** and object hash equal to the record.

### S5-3 R2 (`r2/`)
- `cp -al` of R1's output into `$SP/olean-replay-6a-stmt`, which carries the overlay and `c0a9cff0…`. It starts from
  R1's checked state.
- `downorder.py` against the O1 head gives changed 16 and down 20. `fullorder.py` gives 1440. `plan` gives **20 to
  build and 1420 reused**, with queue = `down.txt`: the same 20 modules as on #4.
- **Build** (07:46:57–07:48:34): **20/20 rc 0**, with 0/0 errors. There are 98 warnings, all `declaration uses
  'sorry'`.
- **Accept:** `update` took 20. `check` gives **1440/1440 RESULT OK**, and all 20 rebuilt oleans have link count 1.

### S5-4 Re-checks
- **Admissions** (`admissions/`; `admcheck.py` against `e1d39836`, with `touched.json` regenerated; its `files`
  section is identical to phase 2's):
  - R1 gives **+0**. R2 gives **+98, EXACT**: 98 targets, 98 admitted, 98 matched, 0 extra, 0 twice and 0 missing,
    against the delivered `rowmap.txt` (SHA-256 `b3ac759e…`, equal to exchange `d7a9adb5`) minus `rename_eval` and
    `depth_rename`.
  - Both delta files are **identical to phase 2's** below their header line.
  - The source token census, by a recorded tokenizer that is not phase 2's, has the same deltas: O1 +0, `~1` +105
    tokens / +11 files, head +103.
- **Axioms** (`probes/`; phase 2's `AxiomsO1.lean` on R1 and `AxiomsStmt.lean` on R2, unchanged):
  - Both logs are **byte-identical** to the #4 runs, and so are both `axtrace.txt` summaries.
  - O1 has 141 constants, standard only.
  - The statements have 544 constants. `sorryAx` is in exactly the 98 targets and the 5 N2/N12–N13 dependents, and
    there is no other non-standard axiom.
- **Closure identity** (`carry/ownerkeys-*.tsv`; stateplan's closure key at the old and the new head):
  - The keys are equal for **all 4 non-root O1 owners and all 16 non-root statement owners**, so each owner's local
    source closure is byte-identical to the one phase 2 sealed.
  - Only the root `TCSlib` differs, because its closure gained the 5 modules of #340/#346.
- **Canonical coe-A seals, re-run** (`rule10/o1`, `rule10/stmt`; `SEAL_CHUNK=1000`; `carry/sealcmp-*.txt`):
  - In all 20 owner records, the requested count, request name set, probe SHA-256, source SHA-256, closure-module count
    and seal outcome are **SAME** as in phase 2's coe-A records.
  - O1 gives `Combinators` 174, `FormulaArith` 194 and the facade 3659, with 0 errors. `TreeNCAC` (194) has 2 errors.
  - The statements give the 16 owners of the R2-5 table with the same counts and 0 errors, except `TreeNCAC` (218),
    which has 2 errors.
  - The two `TreeNCAC` failures (`maxDepth_map_le`, `maxFaninL_map_le`; G6A-F05, pre-existing) have seal logs
    byte-identical to #4, apart from the probe directory name (`carry/f05-*.txt`).
- **Root coe-A, re-run** (`rule10/root`; one owner `TCSlib`, chunked): **14,074 requests, 0 errors**, in 15 chunk commands: 15 install and 15 EOF records, each `requested = verified` (sums 14,074), 5,210 s, 5.1 GB (`root-chunks.txt`). Against the #4 run (13,991; `carry/root-requests-vs-4.txt`): 0 names removed, the 13,991 common rows identical, and **83 names added, every one homed in a file #340/#346 changed** (`BonehBoyenMachine.Handler` 34, `.Words` 33, `.Draws` 12, `.Oracles` 1, `.Reduction` 1, `Pairing.Assumptions` 2). The root closure grew from 1432 to 1437 modules.
- **Carried forward from #4, not re-run:**
  - which checks: strict A/B and coe-B seals of the 20 owners, the paired controls (strict and coe), the delivery's
    30 controls, and the explicit-unfold scans;
  - justification: each of these is a function of the owner's source closure, the fixed Mathlib and toolchain, and the
    unchanged tools (`tools/TOOLS.txt`: every reused tool is byte-equal to its copy in the phase-2 zip);
  - the closure keys show that the source closures are byte-identical, and the coe-A re-run reproduces phase 2's
    request sets, probes and outcomes exactly;
  - the strict and coe-B request sets are derived from the same collector output, and the controls from those records,
    so they are identical too;
  - the only owner whose closure changed is the root, and root coe-A was re-run.
- **Lint** (`lint/`):
  - `campaign_style_lint TCSlib/Complexity --check8b` at the tip, O1 and the statement head gives 25 FAIL / 390 WARN
    over 500, 502 and 513 files. All three outputs are byte-identical to phase 2's, and the FAIL/WARN line sets of
    both heads equal the tip's.
  - `style_lint` gives 0 findings in O1's 2 and the statements' 13 new files. The 11 findings over the 17 changed
    files are identical at the tip. All four outputs are byte-identical to phase 2's.
  - Sizes are unchanged, because the series blobs are identical.
- **Clashes** (`clash/`; phase 1's `names.py` at `e1d39836` and the head):
  - There are 281 new names, 18 of them private. 11 share a full name with a tip declaration in another file, all
    O1's moves out of `TreeNCAC`, whose tip copies the head removes. There are **0 other clashes** and no new name is
    declared twice.
  - Against phase 2's name lists, only the names in #340/#346's 9 files differ.

### S5-5 Replay outputs (kept)
- **`$SP/olean-replay-6a-o1`** (R1; REV `a616adca`, tree `a461632b`):
  - contents: snapshot #5's 1458 oleans, with 7 replaced and 2 added (9 with link count 1), plus NthRootLemmas and 3346
    overlay symlinks;
  - state check: 1429/1429 OK;
  - adoptable on the O1 merge if the merge's Lean paths equal tree `a461632b` (P2-8.1, with the new tree).
- **`$SP/olean-replay-6a-stmt`** (R2; REV `73aedcda`, tree `2c243bb1`):
  - contents: 20 rebuilt oleans with link count 1;
  - state check: 1440/1440 OK;
  - adoptable on the statement merge if it follows O1 directly and the merge's Lean paths equal `2c243bb1` (P2-8.2).
- Deleted: the sparse landing worktree and this job's scratch worktrees.

**Re-replay done: both heads pass on snapshot #5, and the draft PRs can be opened (O1 first, the statement PR stacked
on it). Gate 45 (Codex) audits both.**

## Re-replay on snapshot #6 (2026-11-17)
**Verdict: both merge trees PASS on snapshot #6. Every GSW olean is byte-identical to its snapshot-#5 / LE-g45b
counterpart, and the only differences are what #357 adds to the root closure.**
**Not adoptable as they stand:** #347 and #355 merged while this ran (tip `2be7eb20`), and their Lean changes reach
`CircuitComplexity`, `ComputationalModels` and the root, so both PRs re-replay on snapshot #7 before merge (S6-6).
#357 merged after the snapshot-#5 re-replay and LE-g45/LE-g45b, so neither earlier output can be adopted. This run
replays the merge-condition trees on olean snapshot #6 (`8060f6b7`). No branch was re-cut (S6-1).

| | R1' = tip × #358 (O1) | R2' = tip × #358 × #359 (statements, LE-g45b head) |
|---|---|---|
| PR head | `a616adcac0760ab56b1b0a2a4869f4763843f9ab` | `d154c8830fc8ffc52671b41992e7dbef61e30959` |
| Merge tree (replay target) | **`f7247ea3edff8d96fb53ff1912cabd792f780743`** | **`901bf528f11571286883c52f2515f83c281dcc82`** |
| Rebuilt modules (rc 0, 0 `error:`/`error(`) | 9/9 (the same 9 as on #5) | 20/20 (the same 20) |
| `sorry` warnings | 0 | 97 (exactly the 97 targets) |
| State check | 1434/1434 OK | 1445/1445 OK |
| Rebuilt oleans | link count 1; all 9 byte-identical to #5's R1 | link count 1; all 20 byte-identical to LE-g45b's |
| Admissions against the tip | +0 | +97, EXACT against LE-g45's target list |
| Axiom probes | `AxiomsO1` log byte-identical to #5 | `AxiomsStmt`, `AxiomsG45` logs byte-identical to LE-g45b |
| coe-A seals | 4 owners, all SAME as #5 | 16 owners: 14 SAME as #5, 2 (`Barrington`, `Combinators`) SAME as LE-g45b |
| Root coe-A | n/a | 14,082 requests, 15 chunks, 0 errors (#5: 14,074; the 8 added names are all homed in #357 files) |
| Lint | identical to #5 | identical to #5 / LE-g45b |
| Output map (`mapnoml.py`, no `Mathlib/`) | 1465 entries, `76bd72cbe9845619091540273cd6ab68d8d0d8e33fd2be093511fbd469f4a261` | 1476 entries, `3d0a4bb299ea7aedaa8f9895616f91975f9ca6167fb4001a2cb4bb3ee20cb7db` |

Run 16:24–18:06 UTC. `$SP` as above. Evidence: **`gsw-6a-final-r1-rereplay6-evidence.zip`** (`81c11830…8f1a`), under
`gsw-6a-final-r1-rereplay6/`, with `PROVENANCE.txt` and `SHA256SUMS`; its own SHA-256 is in `evidence-SHA256SUMS`. The
earlier zips are unchanged.
- **Not done:** nothing was committed or pushed, and no branch or PR was changed. These records files are left
  uncommitted.
- **Builds:** no `lake build` and no cache get. Modules ran through `scripts/lean_check_tree.sh` (`runner.py`); probes and
  seals ran through `lean -DmaxErrors=0` without `-o` (`runner_full.py`). Python ran as `python3 -I`.
- **Lean slots:** one Lean process of this job at a time, each started only after `pgrep -c -x lean` read under 3
  (59 readings before the 59 Lean processes: 0 running 8 times, 1 running 39 times, 2 running 12 times; no wait was needed). Only this job's PIDs were ever signalled (S6-5).
- **Other directories:** the snapshot and the kept replays (`-6a-stmt-g45b`, `-6a-readers`, `-6a-fill12`, `-6a-fill86`)
  were not written. At the start, after checking that no process had a file or working directory in them and that their
  evidence is committed (the #5 zip in `8c5875fa`, LE-g45's zip in `659542ec`), `olean-replay-6a-o1`, `-6a-stmt` and
  `-6a-stmt-g45` were deleted (52 MB of their own; the rest was hard links).

### S6-0 Tip and snapshot (`landing/`, `snapshot/`)
- `git fetch`: the records tip is **`6f13855029e918d4a0c19d17efbc35eedbb902f8`**, 11 records-only commits after
  snapshot #6's T `8060f6b7`. `git diff 8060f6b7 6f138550 -- '*.lean' lean-toolchain lake-manifest.json lakefile.lean
  scripts audits` is empty, so the tip is Lean-equal to T.
- **Snapshot #6:** `snapmap.py verify` against `olean-snapshot.map-8060f6b7.tsv` (`0858dccb…7caf`, as registered) gives
  **1463 files, 0 extra / 0 changed / 0 missing**, no symlinks and no empty directories, at the start, after R1', after
  R2' and at the end. It was read only as the source of `cp -al`.
- **Disk:** 2471 MB free at the start (2522 MB after deleting the three old replays), 8450 MB at the end. Another job's export took it to 43 MB at 16:47 (S6-5), and to 1598 MB at 17:37; this job's own files stayed under 0.33 GB.

### S6-1 Merge trees, no re-cut (`landing/trees.txt`)
- Both PR branches are still on `e1d39836`: merge-base(tip, #358) = merge-base(tip, #359) = `e1d39836`, and #359 is
  #358 plus 8 commits.
- Since `e1d39836` the tip changed 115 paths, 9 of them Lean (#357's: `BonehBoyen`, `BonehBoyenSecurity` and its 5 new
  children `Chain`, `Coupling`, `Lazy`, `Random`, `Real`, `IdentityBased/Defs`, `Games/Relational`). None of them is
  one of the 19 series paths, and #357 does not touch `TCSlib.lean`.
- **R1'** = `git merge-tree --write-tree 6f138550 a616adca`: rc 0, tree **`f7247ea3`**. Against the tip it differs in
  exactly O1's 4 files; against the #358 head it differs in exactly #357's 9 Lean files; the 19 series paths are
  blob-equal to the #358 head.
- **R2'** = `git merge-tree --write-tree M1 d154c883`, where M1 is an unreferenced, unsigned `commit-tree` commit
  (`c09a12ea`, tree `f7247ea3`, parents tip and #358) standing for the #358 merge commit: rc 0, tree **`901bf528`**.
  The direct `git merge-tree --write-tree 6f138550 d154c883` gives the same tree. Against the tip it differs in exactly
  the 19 series paths; against the #359 head in exactly #357's 9 Lean files.
- **No re-cut:** both merges are clean and GitHub merges with merge commits, so the replay targets are these two trees.
  `land/gsw-6a-o1` and `land/gsw-6a-statements` were not moved.
- Exports (`git archive` of `TCSlib TCSlib.lean audits scripts lakefile.lean lake-manifest.json lean-toolchain`, as in
  LE-g45/LE-g45b, `.lake/packages` symlinked): R1' 1586 files, R2' 1597, tip 1584, each 0 extra / 0 missing / 0
  changed (`exportcheck.py`).

### S6-2 R1' (`r1/`)
- `cp -al $SP/olean-snapshot $SP/olean-replay-6a-o1-s6`; `mloverlay.sh` made 3346 symlinks; NthRootLemmas compiled to
  **`c0a9cff0…`**.
- `stateplan init` at `8060f6b7` gives 1432 modules. `downorder.py` (`8060f6b7` → `f7247ea3`) gives changed 4 and down
  9. `fullorder.py` gives 1434. `plan` gives **9 to build and 1425 reused**, and the queue equals `down.txt`: the same 9
  modules as on #4 and #5.
- **Build** (16:33:03–16:35:05): **9/9 rc 0**, with `error:` 0, `error(` 0 and substring "error" 0. There are 0
  warnings, so no `sorry`, and no log/record mismatch (`permod.tsv`). `warncmp`: 9/9 SAME as #5's R1 logs.
- **Accept:** `update` took 9. `check` gives **1434/1434 RESULT OK**, again after R2' and at the end. All 9 rebuilt
  oleans have **link count 1** and object hash equal to the record.
- **The 9 oleans are byte-identical to #5's R1** (`linkcheck.txt` against the #5 zip). Against snapshot #6 the output
  map has 1461 equal, 2 changed (`CircuitComplexity`, `TreeNCAC`) and 2 added (`FormulaArith`, `Combinators`); the
  other 5 rebuilt modules came out byte-identical to the snapshot's.

### S6-3 R2' (`r2/`)
- `cp -al` of R1' into `$SP/olean-replay-6a-stmt-s6`, which carries the overlay and `c0a9cff0…`; R1''s checked state.
- `downorder.py` (`f7247ea3` → `901bf528`) gives changed 17 and down 20. `fullorder.py` gives 1445. `plan` gives **20 to
  build and 1425 reused**, with queue = `down.txt`: the same 20 modules as on #5 and in LE-g45.
- **Build** (16:35:57–16:37:08): **20/20 rc 0**, with 0/0 errors and substring "error" 0. There are **97 warnings, all
  `declaration uses 'sorry'`** (Defs 11, Eval 5, Barrington 11, BarringtonConverse 11, NC1 5, NANDForm 6, NANDLayering
  7, Combinators 23, CarrySave 7, Compare 7, ModSum 4). `warncmp`: 20/20 SAME as LE-g45b/LE-g45's logs.
- **Accept:** `update` took 20. `check` gives **1445/1445 RESULT OK**, and all 20 rebuilt oleans have link count 1.
- **The 20 oleans are byte-identical to LE-g45b's** (`olean-replay-6a-stmt-g45b`). The output map against LE-g45b's
  map (`fa206774…`): 1467 equal, 4 changed and 5 added, all of them #357's modules (snapshot #6's oleans); nothing else.

### S6-4 Checks
- **Admissions** (`admcheck.py` against the tip `6f138550`; `touched.json` regenerated against the tip, its `files`
  section identical to #5's for O1 and the root and to LE-g45b's for the 17 statement files):
  - R1' gives **+0**; the delta file is identical to #5's below the header line.
  - R2' gives **+97, EXACT**: the delivered `rowmap.txt` (`b3ac759e…`) minus `rename_eval`, `depth_rename` and
    `const_eval` (LE-g45's list) gives 97 targets, 97 admitted, 97 matched, 0 extra, 0 twice and 0 missing. The delta
    file is identical to LE-g45b's below the header line.
- **Axioms** (`probes/`; phase 2's `AxiomsO1.lean` on R1'; LE-g45's `AxiomsStmt.lean` and `AxiomsG45.lean` on R2', all
  unchanged):
  - All three logs are **byte-identical** to the references (#5's R1 for O1, LE-g45b's head for the other two), and so
    are both `axtrace.txt` summaries. Nothing differs, not even a closure size: the probes print constants and axioms
    of the GSW modules only, whose oleans are byte-identical.
  - O1: 141 constants, standard only.
  - Statements: 545 constants; `sorryAx` in exactly the 97 targets and the 5 N2/N12–N13 dependents; no other
    non-standard axiom; `eval_node_nil` and `const_eval` `[propext, Classical.choice, Quot.sound]`.
- **Closure keys** (`carry/ownerkeys-*.tsv`): the 4 O1 owners have equal keys at `a616adca` and `f7247ea3`. All 17
  non-root statement owners (the 16 plus `Hierarchy`) have equal keys at `d154c883` and `901bf528`; against #5's
  `73aedcda`, 13 of the 17 differ (all but `Defs`, `Eval`, `NANDForm`, `NANDLayering`), all through LE-g45/LE-g45b's
  edits to `Combinators`, `Barrington` and `Hierarchy`. Only the
  root differs from both, through #357's 5 new modules (closure 1427 → 1432 for O1, 1438 → 1443 for the statements).
- **Canonical coe-A seals** (`tools/rule10_g6a6.sh`, collector and `mkseals_coe.py` as on #5; `SEAL_CHUNK=1000`;
  `carry/sealcmp-*.txt`):
  - **O1** (R1'): `Combinators` 174, `FormulaArith` 194, the facade 3659, all 0 errors; `TreeNCAC` 194 with the 2
    pre-existing G6A-F05 errors (`maxDepth_map_le`, `maxFaninL_map_le`). All 4 records are **SAME** as #5's (requests,
    names, probe and source SHA-256, closure modules, outcome), and all 4 seal logs are byte-identical to #5's.
  - **Statements** (R2', the same 16 owners): the same counts as on #5 (`Defs` 0 … the facade 3726,
    `ComputationalModels` 1106), 0 errors except `TreeNCAC` (218, the same 2 F05 errors). 14 records are **SAME** as #5's
    and 14 seal logs byte-identical. `Barrington` (119) and `Combinators` (174) have equal requests, names, closure
    modules and outcome, but a different probe and source SHA-256: their sources changed in LE-g45/LE-g45b. Against
    LE-g45b's head records both are **SAME** in every field, and their logs are identical apart from the probe
    directory name (`G6aSeal` / `G45Seal`).
  - **`Hierarchy`** (extra owner, since LE-g45 changed it): 355 requests, 2 errors in `Language.InTreeSize.inSIZE`,
    **SAME** as LE-g45's head record, log identical apart from the probe prefix. LE-g45 recorded these 2 errors at its
    base and head alike (pre-existing).
  - The request sets are equal to the #5 records for all 20 owners. No root addition from #357 reaches a non-root
    owner, since no owner's closure contains a #357 module.
- **Root coe-A** (`rule10/root`; owner `TCSlib`, chunked): **14,082 requests, 0 errors**, in 15 chunk commands: 15 install and 15 EOF records, each `requested = verified` (sums 14,082), 3,823 s, max RSS 5.2 GB (`root-chunks.txt`). Against the #5 run (14,074; `carry/root-requests-vs-5.txt`): 0 names removed, the 14,074 common rows identical, and **8 names added, every one homed in a #357 file** (`BonehBoyenSecurity.Real` 3, `.Lazy` 3, `.Coupling` 2). The root closure grew from 1437 to 1442 modules (#357's 5 new modules).
- **Lint** (`lint/`; scripts blob-identical at tip, R1' and R2'):
  - `campaign_style_lint TCSlib/Complexity --check8b` gives 25 FAIL / 390 WARN over 500 (tip), 502 (R1') and 513 (R2')
    files. The tip and R1' outputs are byte-identical to #5's, and R2''s to LE-g45b's; the FAIL/WARN line sets of both
    trees equal the tip's.
  - `style_lint`: 0 findings in O1's 2 and the statements' 13 new files; the 11 findings over the 17 changed files are
    identical at the tip. All four outputs are byte-identical to #5's. With `Hierarchy` added (18 files), the 13
    findings are the same set at the tip and R2' (the 2 extra are the pre-existing `Hierarchy:17` false positives).
- **Clashes:** not re-run with `names.py`. The root `TCSlib`, which imports every module of both #357 and the series,
  compiled with 0 errors in R2', so no declaration name is declared twice across them.

### S6-5 Disk incident (`log/aborted-1/`)
- At 16:45–16:47 another job's unscoped export (`$SP/6b-stage`, 2.3 GB) took free disk from 2.3 GB to **43 MB** while
  this
  job's statement seals ran (the first, the `BranchingPrograms` facade, had finished at 16:45:33; the second was
  stopped). This job's processes held under 0.3 GB.
- This job stopped its own seal chain (its driver, `gated_full.sh`, `runner_full.py` and its one `lean` process) and
  moved the partial statement series aside. Nothing had been written to a replay tree since R2''s accept at 16:37
  (seals and probes never use `-o`).
- Free disk was back at 2.3 GB once the other job removed its export. The statement, `Hierarchy` and root series were
  then rerun from scratch through `gated_full_s6.sh`, which adds a disk guard (wait while free disk is under 1536 MB).
  The O1 seals (finished 16:45:08 with 756 MB free) and every earlier step were kept; their outputs are complete and
  match the references byte for byte.
- At the end, both replay trees rehash against their output maps (`replayverify.py`), and both state checks pass.

### S6-6 Replay outputs (kept) and adoption
- **`$SP/olean-replay-6a-o1-s6`** (R1', tree `f7247ea3`):
  - contents: snapshot #6's 1463 oleans, with 2 replaced and 2 added (9 rebuilt with link count 1), plus NthRootLemmas
    and 3346 overlay symlinks;
  - output map (no `Mathlib/`): 1465 entries, SHA-256 **`76bd72cbe9845619091540273cd6ab68d8d0d8e33fd2be093511fbd469f4a261`**;
  - state check 1434/1434 OK;
  - **adoptable on the #358 merge** if `git diff --name-only <merge> f7247ea3 -- '*.lean' lean-toolchain
    lake-manifest.json lakefile.lean` is empty (the recipe's step-3 diff), with the recipe's step-6 checks.
- **`$SP/olean-replay-6a-stmt-s6`** (R2', tree `901bf528`):
  - contents: R1' plus the 20 rebuilt oleans (link count 1);
  - output map: 1476 entries, SHA-256 **`3d0a4bb299ea7aedaa8f9895616f91975f9ca6167fb4001a2cb4bb3ee20cb7db`**;
  - state check 1445/1445 OK;
  - **adoptable on the #359 merge** if it follows the #358 merge with nothing else Lean in between and the step-3 diff
    against `901bf528` is empty.
- **Superseded at the end of the run.** A re-fetch at 18:03 found the records tip at
  **`2be7eb209ae89c9dfe5ba7b63b115ae486ff9ffd`**: #347 and #355 merged during the run ("snapshot #7 adoption pending"),
  changing 23 Lean paths (21 M, 2 A; `landing/tip-advance-lean.txt`). None is a series path, and both PRs still merge
  cleanly (`merge-tree` gives `36740243` and `2dedb4c9`), but the merge trees' Lean paths now differ from `f7247ea3` and
  `901bf528` in those 23 paths, so **neither output can be adopted on a merge made from the current tip**.
  - In R2''s rebuild set, 17 modules have none of the 23 in their closure (`landing/tip-advance-closure.txt`);
    `CircuitComplexity` reaches `TuringMachine/Build/ModuleHost`, `ComputationalModels` reaches `Randomized/PPT`, and
    the root reaches 21 of them.
  - So #358 and #359 must re-replay on snapshot #7 once it is adopted. The 17 GSW modules outside the advance keep their
    closure keys and their oleans are expected to be reused byte-identically; `CircuitComplexity`, `ComputationalModels`
    and the root rebuild, and their coe-A seals (and the root's) re-run.
- `olean-replay-6a-stmt-g45b` is no longer adoptable (built on #5 without #357); it is kept, as instructed.
- Deleted: the three exports (`wtx-tip` and `wtx-r1` at 17:40 when free disk read 1637 MB, `wtx-r2` at the end) and this
  job's scratch copies (the extracted #5 zip, `tmp/`).

**Re-replay done: #358 and #359 pass on snapshot #6, with every GSW olean, probe log, admission and seal record equal to
the snapshot-#5/LE-g45b references. Because #347 and #355 merged during the run, merge-time adoption needs a further
re-replay on snapshot #7.**
