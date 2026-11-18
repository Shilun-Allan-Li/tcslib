# gsw-6b-statements · final r1 · phase 2: landing and merged-tree Lean replays on snapshot #10

**Verdict: PASS for both landing branches. Both are pushed, with draft PRs open.**

- **PR O2** [#376](https://github.com/Shilun-Allan-Li/tcslib/pull/376), branch `land/gsw-6b-o2`, head
  `04ba2446f541c39dd02aefaa97a9eb31dbbda748`. Base: `cryptography/pass-shelat-ch2-4`.
- **Statement PR** [#377](https://github.com/Shilun-Allan-Li/tcslib/pull/377), branch `land/gsw-6b-statements`, head
  `680be9fa45a9cf5deeb7a59820e8e86aaaa4f068`. Base: `land/gsw-6b-o2`.
- Phase 2 found no blocker, major or minor. It adds three infos (G6B-F10 to F12, below).
- The ruled landing edits LE-6b1, LE-6b2 and LE-6b3 are applied in one signed commit. **LE-6b3 compiles and is kept.**

| Check | R1 = tip × O2 | R2 = R1 × statements (with LE-6b1..3) |
|---|---|---|
| Range-diff against the delivered series | 1/1 `=` | 5/5 `=`, plus the landing-edit commit |
| Tree | `8b615e06` = merge-tree(tip, `5bd5ada5`) | `~1` `22349e8e` = merge-tree(tip, `8f92fe7d`); head `956fc086` |
| Rebuilt / reused | 19 / 1428 | 14 / 1442 |
| Every rebuilt module | rc 0, 0 `error:`/`error(`, 0 `sorry` | rc 0, 0 `error:`/`error(`; `sorry` warnings exactly the 24 targets |
| State check | 1447/1447 OK | 1456/1456 OK |
| Link count of rebuilt oleans | 1 (19/19) | 1 (14/14) |
| Admissions | 192 (tip 192, +0) | **216** (+24, EXACT against the targets) |
| decls2 against the tip | 5 ADDED / 0 / 0 | 136 ADDED / 0 / 0; landing-edit commit 0/0/0 |
| Axioms | 24 BitEncoding constants, standard | 175 constants; `sorryAx` in exactly the 24 targets; `fheEvalCircuit`/`leveledEvalCircuit` and `_eq` standard |
| Seals (strict A/B, coe A/B) | BitEncoding 9/9/9/9, 0 errors | 12 owners, 48 probes, 0 errors |
| Controls | the delivery's 5 BitEncoding controls: ALL_OK | `mkctl_g6b` ALL_OK in strict and coe (70 + 70 sealed negatives); the delivery's 50: 34 unchanged + 16 after pruning stale names, all OK |
| Explicit-unfold scan | 54 items, 0 foreign | 101 items, 0 foreign |
| Lint | FAIL/WARN = tip (92/103) | FAIL/WARN = tip (92/103); `style_lint` 0 |
| Snapshot #10 rehash | 0/0/0 | 0/0/0 (before, after R1, after R2, end) |

Run on 2026-11-18, 04:20–06:45 UTC. `$SP` is `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.
The evidence is `gsw-6b-final-r1-phase2-evidence.zip`, under `gsw-6b-final-r1-phase2/`. Its SHA-256 is in
`evidence-SHA256SUMS`.

**Builds**
- No `lake build` and no cache get.
- Modules ran through the recipe's `runner.py` (`scripts/lean_check_tree.sh`). Probes ran through `runner_full.py`, which
  is `lean -DmaxErrors=0` without `-o`, so it writes nothing to a tree.
- Each call went through a slot gate, `pgrep -c -x lean`, which waits while 3 or more `lean` processes run.
- This job ran one Lean process at a time. Another job's single `lean` was running for part of the time, so the
  machine had at most 2.
- No process was signalled.

**Disk:** 7747 MB free at the start and 5976 MB at the end. The 1.5 GB guard never fired.

## P2-0 Tip and snapshot
- The records tip is `38123ccbebef878cd25dd2d2761de1b40ba7e421`.
- `git diff --name-only cf6a2266 38123ccb -- '*.lean' lean-toolchain lake-manifest.json lakefile.lean scripts audits` is
  empty, so the tip is Lean-equal to snapshot #10's T.
- #366 and #368 are merged into the tip, and every 6a target is proved.
- **Snapshot #10** (`$SP/olean-snapshot`) was verified with `snapmap.py verify` against `olean-snapshot.map-cf6a2266.tsv`
  (`84d88738…`). It gave **1478 files, 0 extra / 0 changed / 0 missing** at the start, after R1, after R2 and at the
  end. It was read only as the source of `cp -al`.

## P2-1 Reproduction and landing branches
- **Reproduction:**
  - delivery: `git archive 3b340824 inbox/fills/gsw-6b-statements`, with the top `SHA256SUMS` OK;
  - worktree: sparse, detached at the issued base `3e51b5f2`;
  - `git am` per patch, with the `COMMITS.tsv` committer data and `commit.gpgsign=false`;
  - result: all six hashes reproduce, `5bd5ada5`, `7a814546`, `dd9f00f4`, `1378740f`, `5c8f81cd` and `8f92fe7d`
    (`landing/reproduction.txt`).
- **`land/gsw-6b-o2`** = `04ba2446`:
  - built as `git cherry-pick -S 5bd5ada5` onto the tip;
  - tree `8b615e06` = `git merge-tree --write-tree 38123ccb 5bd5ada5`;
  - diff: `LWE/BitEncoding.lean` only, +58/−0;
  - range-diff `3e51b5f2..5bd5ada5` against `38123ccb..land/gsw-6b-o2`: **1/1 `=`**.
- **`land/gsw-6b-statements`**, stacked on O2:
  - five `-S` picks, `47aae69d`, `c10e0d3e`, `80366e7f`, `52f52dc7` and `75c683b2`;
  - range-diff `5bd5ada5..8f92fe7d` against `land/gsw-6b-o2..~1`: **5/5 `=`**;
  - the tree of `~1` is `22349e8e` = merge-tree(tip, `8f92fe7d`);
  - the picks keep the worker's messages and trailers.
- **Landing-edit commit `680be9fa`** (signed, with this session's two trailers, explicit paths):
  - It applies LE-6b1, LE-6b2 and LE-6b3 from `landing-edits-proposed.diff`, split per edit and applied in order with
    `git apply`.
  - Each of the 5 files is byte-equal to the proposal applied to `8f92fe7d` (`landing/le-vs-proposal.txt`).
  - Diff +17/−21. Line widths stay ≤ 99.
- **Signatures:** all 7 landing commits carry an SSHSIG with key `SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc`,
  the records tip's key. The worker's `5bd5ada5` and `8f92fe7d` are unsigned. This checks key identity only.
- **Exports:** `git archive` of each head (`TCSlib`, `TCSlib.lean`, `audits`, manifests, `lakefile.lean`, `scripts`)
  matches blob for blob: 1599 files (R1) and 1608 files (R2), 0/0/0.

### Prose that called the prerequisites missing or admitted (task item: "list each")
At this base #368 provides `decrypt_eq_decode_dotProduct` and `hybridPlant_eq`, and #366 proves N2, N12 and N13. The
landing-edit commit corrects every such passage in the series:
1. `GSW/DecryptFormula.lean`, G6 `decryptFormula_eval` sketch. The text "It is **MISSING** at the base (the step exists
   only inside the private `decrypt_eq_decode_errorSum`), listed in the reader census, and lands owner-side before this
   fill" becomes "in `GSW/Scheme.lean` (owner-side, ruling Q-C1)" (LE-6b1).
2. `GSW/Bootstrap.lean`, `fheEvalCircuit` docstring. "While 6a's N2 (`nandGadget_correct`) is admitted, `sorryAx` reaches
   this definition through `toNANDForm` only" is removed (LE-6b1).
3. `GSW/Leveled.lean`, `leveledEvalCircuit` docstring. "While 6a's N2, N12 and N13 are admitted, `sorryAx` reaches this
   definition through `toNANDForm` and `layerNAND` only" is removed (LE-6b1).
4. `GSW/LeveledSecurity.lean`, L4 `distAdv_levelHybrid_le` sketch. "`hybridPlant`'s planted position" becomes
   "`hybridPlant_eq` (the planted position)" (LE-6b1).

A scan of the 12 series files after the commit found no other passage that calls either prerequisite missing, calls a
6a declaration admitted, or names `hybridPlant_apply` (`landing/stale-prose-scan.txt`). The remaining "admitted" phrases
refer to 6b's own targets, and "will be cited once ingested" is the P6-Q19 B disclosure.

Outside the series, `GSW/Scheme.lean` and `EnsembleSecurity.lean` already carry LE-g50e's corrections. The census itself
(`issued-6b-r1/census.txt`, the delivery's `census/reader-census.md`) is evidence and is left unchanged, as G6B-F09 rules.
Its rows for `decrypt_eq_decode_dotProduct` and the `hybridPlant` reader (landed as `hybridPlant_eq`) are now satisfied
at the tip.

### Comment-strip identity (`commentstrip/`)
- `commentstrip50.py` (LE-g50d's tool, unchanged), `75c683b2` against `680be9fa`:
  - Bootstrap, Leveled, LeveledSecurity and PolyRatio give **RESULT EQUAL**;
  - every M1, M2 and M3 mutation is caught;
  - every N1 docstring control stays EQUAL;
  - overall **RESULT OK**, with 16 controls.
- DecryptFormula's comment-stripped diff (`stripdiff.py`) is exactly the `neZero_columns` proof: 5 lines out, 2 in.

## R1: the O2 head (`r1/`)
- **Recipe:**
  - copy: `cp -al $SP/olean-snapshot $SP/olean-replay-6b-o2`;
  - overlay: `mloverlay.sh` (3346 symlinks) and `mathlibextra.sh` NthRootLemmas `c0a9cff0…` (lean rc 0);
  - state: `stateplan init` at `cf6a2266` (1447 modules);
  - `downorder.py`: changed 1, down 19;
  - `fullorder.py`: 1447;
  - `stateplan plan`: **19 to build, 1428 reused**. The queue equals `down.txt`.
- **Build** (04:26:38–04:27:13, maximum RSS 4.4 GB): **19/19 rc 0**, `error:` 0, `error(` 0, substring "error" 0,
  `sorry` 0, and no log/record mismatch (`permod.py`).
  - The 3 warnings (Regev `simps` ×2, one unused section variable) are pre-existing.
  - All 18 modules with a reference log are SAME as the delivery's `sweep-o2-r2` logs; the root has no reference.
- **Accept:**
  - `stateplan update` took 19 modules;
  - `check` gives **1447/1447 RESULT OK**, and again at the end;
  - the rebuilt oleans have link count 1 (19/19), and the 1428 reused ones are snapshot #10's inodes;
  - there are no `.ilean` files and no stray symlinks.
- **Output map** (Mathlib excluded): `olean-replay-6b-o2.map-04ba2446.noMathlib.tsv`, 1478 entries, `e1d210bf…`.
  Against #10 only `LWE/BitEncoding` differs; the 18 rebuilt downstream oleans are byte-equal to the snapshot's.
- **Admissions:** `sorryscan.py` over the full order gives **192 in 44 modules** at the tip and at R1, byte-equal per
  module.
- **decls2** (pinned `fa81981a…`, tip against the O2 head): **5 ADDED**, 0 CHANGED, 0 REMOVED, empty `.err`.
- **Axioms** (the delivery's `AxiomProbe.lean` restricted to `BitEncoding` and the `LWE` facade): 24 constants, 17 DECL
  and 7 AUX, **all standard**.
  - `decodeLo`, `decodeHi`, `decodeLo_eq` and `decodeHi_eq` use none.
  - `decode_iff_mem_Ico` uses `propext`, `Classical.choice` and `Quot.sound`.
  - No `sorryAx`.
- **Rule 10** (`rule10/o2/`; owner `LWE.BitEncoding`; `touched.json` against the tip):
  - seals: strict A/B and coe A/B, **9/9/9/9 requests, 0 errors**, install and EOF records;
  - the maintainer harness's covering controls have no BitEncoding row at R1, since no downstream owner is sealed;
  - the delivery's 5 BitEncoding controls (`r2/o2/controls/src`, unchanged) give **5/5 OK**. The unsealed body read has
    0 errors. Sealed strict and coe, the negative has exactly 1 error, in the example, and the reader 0. Install and EOF
    records are present, with 14 requests;
  - explicit-unfold scan: 54 items (52 THEOREM, 2 LOCAL), **0 foreign**.

## R2: the statement head with LE-6b1..3 (`r2/`)
- **Recipe:**
  - copy: `cp -al $SP/olean-replay-6b-o2 $SP/olean-replay-6b-stmt`, with the overlay carried along;
  - state: R1's checked state;
  - `downorder.py` against the O2 head: changed 11, down 14;
  - `fullorder.py`: 1456;
  - `stateplan plan`: **14 to build, 1442 reused**. The queue equals `down.txt`.
- **The 14 rebuilt modules:** `LWE/Ratio`, `LWE`, the 8 new `GSW/*` modules, `GSW`, `Homomorphic`,
  `AdvancedEncryption` and `TCSlib`.
- **Build** (04:28:41–04:29:07, maximum RSS 4.4 GB): **14/14 rc 0**, `error:` 0, `error(` 0. There are 24 warnings, all
  `declaration uses 'sorry'`, and no log/record mismatch.
  - The warnings are SAME as the delivery's `sweep-final-r2` in 10 modules. They are SAME-TEXT, with only line numbers
    shifted, in the 4 files whose line count the landing edits change: DecryptFormula, Bootstrap, Leveled and PolyRatio.
  - **LE-6b3 compiles**: DecryptFormula has rc 0 and 0 errors.
- **Accept:**
  - `stateplan update` took 14 modules;
  - `check` gives **1456/1456 RESULT OK**, and again at the end;
  - the rebuilt oleans have link count 1 (14/14);
  - R1 stayed consistent: its check is still 1447/1447 OK at the end, and its output map is unchanged. Its 5 oleans that
    R2 did not rebuild are shared with R2 by `cp -al`.
- **Output map** (Mathlib excluded): `olean-replay-6b-stmt.map-680be9fa.noMathlib.tsv`, 1487 entries, `52ed7825…`.
  - Against R1: 9 modules added; `LWE`, `GSW` and `Homomorphic` changed; `AdvancedEncryption` and the root are
    byte-equal.
  - Recomputed at the end, the map is equal.

### Admissions (`admissions/`)
- `sorryscan.py` over the full order: **216 in 52 modules** at R2, against 192 in 44 at the tip.
- The diff is exactly 8 new module lines:
  - Branching 3, DecryptFormula 6, Bootstrap 5, Circular 1, Leveled 2, LeveledSecurity 2, PolyRatio 3 and
    Asymptotic 2;
  - no other module changes.
- `admmap6b.py` maps each `declaration uses 'sorry'` warning of the R2 logs to its enclosing declaration in the export:
  - 24 targets, 24 admitted, 24 matched;
  - none outside the targets, none twice, none missing: **EXACT**.
- The 24 are the 23 `target` rows of `issued-6b-r1/targets.txt`, plus `decrypt_leveledEval_of_ratio`, which is G17's
  split. `targets.txt` provides for it ("24 if G17 is split").
- Per the ruling Q-6B-F2, `decDepth_le` is among them.

### decls2 (`decls2/`)
- **Tip against the head:** **136 ADDED, 0 CHANGED, 0 REMOVED**, empty `.err`. Ignoring line numbers, it is identical
  row for row to phase 1's `decls2-final.tsv`. 50 rows carry shifted line numbers, all in the files the landing edits
  change.
- **`~1` against the head** (the landing-edit commit): **0/0/0**. LE-6b3 does not change the instance header.

### Axioms (`axioms/`)
- **Probe:** the delivery's `AxiomProbe.lean` (`evidence/stmt/probe/`), unchanged, on R2. It reports 175 constants: 153
  DECL and 22 AUX.
- **Non-standard axioms other than `sorryAx`:** none.
- **`sorryAx`** is in **exactly the 24 targets**. Each TRACE names only the target itself.
- **`fheEvalCircuit`, `fheEvalCircuit_eq`, `leveledEvalCircuit` and `leveledEvalCircuit_eq` are standard**
  (`propext`, `Classical.choice`, `Quot.sound`). This confirms that with 6a fully proved, the four N2/N12/N13
  dependents of the delivery's log no longer reach `sorryAx`.
- **Against the delivery's `AxiomProbe-r2.log`:** 192 lines are equal, 7 appear only here and 12 only there.
  - The 4 dependents above lose `sorryAx`, and their 4 TRACE lines go.
  - **LE-6b3** changes three things:
    - `Parameters.neZero_columns` goes from `[Quot.sound, propext]` to `[propext]`;
    - its auxiliary `neZero_columns._proof_1` disappears, which leaves 22 AUX instead of 23;
    - `levelMsgs._proof_1` and `levelAssemble._proof_1`, which use `NeZero.ne P.columns`, go from
      `[Quot.sound, propext]` to `[propext]`.

  There is no other difference (G6B-F10).
- **O2's five declarations:** standard, as at R1.

### Rule 10 (`rule10/stmt/`, `scan/stmt/`)
- **Driver:** `rule10_g6b.sh`, which is `rule10_g6a.sh` re-pointed.
  - Owners: the 9 new modules, the facades `GSW` and `LWE`, and `BitEncoding`.
  - `touched.json` is taken against the tip.
  - `SEAL_CHUNK=1000`.
  - Every probe goes through the slot gate.
- **Seals:** 48 probes, **all rc 0 with 0 errors**. Each has one install and one EOF record, with
  `requested = verified`.

  | Owner | A | B | coe-A | coe-B |
  |---|---|---|---|---|
  | `LWE/BitEncoding` | 9 | 9 | 9 | 9 |
  | `LWE/Ratio` | 947 | 948 | 946 | 947 |
  | `GSW/Branching` | 200 | 200 | 200 | 200 |
  | `GSW/DecryptFormula` | 381 | 381 | 380 | 380 |
  | `GSW/Bootstrap` | 445 | 445 | 444 | 444 |
  | `GSW/Circular` | 465 | 465 | 464 | 464 |
  | `GSW/Leveled` | 480 | 480 | 479 | 479 |
  | `GSW/LeveledSecurity` | 1,562 | 1,563 | 1,561 | 1,562 |
  | `GSW/PolyRatio` | 1,395 | 1,396 | 1,394 | 1,395 |
  | `GSW/Asymptotic` | 1,654 | 1,655 | 1,653 | 1,654 |
  | `GSW.lean` (facade) | 1,663 | 1,664 | 1,662 | 1,663 |
  | `LWE.lean` (facade) | 966 | 967 | 965 | 966 |

- **Against the delivery's strict seal records** (`rule10/stmt-requests-vs-delivery.txt`): the sets differ only by
  closure drift since the issued base.
  - **17 names are added**, all from modules the tip changed since `3e51b5f2`: 6a's fills in `CarrySave` (6),
    `NANDLayering` (5), `Compare` (1) and `Barrington` (1), plus `BitLists` (3) and `IterateFind` (1).
  - **4 names are gone:** `IterateFind`'s `polyTimeComputable_find.match_1`, `match_1_1` and their two private
    `splitter`s, which no longer exist at the tip.
  - BitEncoding is identical.
- **Paired controls** (`mkctl_g6b.py`: `mkctl_g6a.py` with the harness unchanged, and rows B replaced by the delivery's
  10 rows):
  - The rows are `RatioBounded`, `select`, `decDepth`, `bootNoise`, `WeakCircularSecure`, `levelKey`,
    `challengeDist`, `pBoot`, `encodeCiphertext` and `decodeLo`. Their statements are verbatim, stated inside the
    delivery's namespace with its opens.
  - Covering subset: 14 seal records, giving 28 probes per harness.
  - **Strict and coe each:**
    - 70 sealed negatives, each failing exactly once: `decodeLo` 14, `select` 10, `decDepth` 10, `RatioBounded` 8,
      `bootNoise` 8, `levelKey` 6, `WeakCircularSecure` 4, `challengeDist` 4, `pBoot` 4, `encodeCiphertext` 2;
    - 70 positives with 0 failures, and 140 unsealed controls with 0 errors;
    - **ALL_OK** (`ctlcheck2.py`).
  - Every row is exercised.
- **The delivery's own control files** (`evidence/rule10/r2/{final,final-bitenc}/controls/src`, 50 files, run
  byte-unchanged; `rule10/delivered-stmt/`):
  - **34/50 OK.**
  - The 16 sealed files of `Ratio`, `PolyRatio`, `LeveledSecurity` and `Asymptotic` (strict and coe, negative and
    positive) stop at harness install. The reason is `absent/ambiguous imported name
    Complexity.IterateFind.polyTimeComputable_find.match_1`, followed by the EOF consequence. Their request sets were
    baked at the issued base and name the 4 names that are now gone.
  - `dctlprune.py` removes exactly those 4 entries from each `payload` and `componentPayload` literal, and lowers
    `expectedRequests` by 4. Nothing else changes, as the file diff confirms. The pruned files give **16/16 OK**:
    - each negative fails exactly once, in the example;
    - each positive gives 0 errors;
    - install and EOF records are present (Ratio 944/943, PolyRatio 1380/1379, LeveledSecurity 1553/1552,
      Asymptotic 1644/1643) (`rule10/delivered-stmt-pruned/`; G6B-F11).
- **Explicit-unfold scan** (the 12 changed files): 101 items, **0 foreign**.
  - THEOREM 91.
  - OWNED_DEFINITION 5: the file's own `unfold bootGate` ×3 and `unfold levelGate` ×2, in their case readers.
  - LOCAL_OR_UNRESOLVED 5.
- **Root coe-A was not re-run.** The root file is unchanged by both PRs and owns no declaration. Both changed facades
  were sealed in all four variants (G6B-F12).

### Lint and sizes (`lint/`)
- **`campaign_style_lint.py TCSlib/Cryptography --check8b`**, each run from its own export:
  - tip: 92 FAIL / 103 WARN over 531 files;
  - R1: 92/103 over 531;
  - R2: 92/103 over 540.
  - The FAIL and WARN line sets are **identical** to the tip's (0 diff lines). Phase 1's 104 WARN at the base dropped to
    103 at the tip, because #368 gave `hybridPlant` its reader.
- **`style_lint.py`:** 0 findings in the 12 changed files at R2.
- **Sizes:** at most 351 lines (LeveledSecurity) and at most 99 characters wide (`landing/sizes.tsv`).

## Infos added by phase 2
| # | Severity | Finding | Disposition |
|---|---|---|---|
| G6B-F10 | info | LE-6b3 removes `neZero_columns._proof_1` and drops `Quot.sound` from `neZero_columns`, `levelMsgs._proof_1` and `levelAssemble._proof_1`. It is the only axiom-log difference besides the four N2/N12/N13 dependents, which are now standard. | Record; expected from LE-6b3. |
| G6B-F11 | info (tooling) | The delivery's 16 sealed controls for the IterateFind-dependent owners bake request sets from the issued base, and 4 of their names no longer exist at the tip, so they fail at install. Pruning only those entries makes all 16 pass. The maintainer harness, built with the current request sets and the same 10 rows, is ALL_OK. | Record. Not a module finding. |
| G6B-F12 | info (scope) | The root coe-A was not re-run: the root is unchanged and declares nothing. | Record. Gate 46 may ask for it. |

## Merge and adoption (for the maintainer; nothing is merged here)
1. **#376 (O2) first.** On merge, run `git diff --name-only <merge> 8b615e060f72d72749f67abd39f820d117e0a806 -- '*.lean'
   lean-toolchain lake-manifest.json lakefile.lean`. If it is empty, adopt `$SP/olean-replay-6b-o2` (map `e1d210bf…`,
   after removing `Mathlib/`) as snapshot #11.
2. **Then #377**, retargeted to `cryptography/pass-shelat-ch2-4`. If the tip is otherwise unchanged, run the step-3 diff
   against `956fc086044551e8f04298ab70dd5aa451069c16`. If it is empty, adopt `$SP/olean-replay-6b-stmt`, which already
   contains R1. Otherwise re-replay its 14 modules.
3. Gate 46 (Codex) audits both PRs before merge.

## Not done or left
- The records files are uncommitted: this file, the zip, `evidence-SHA256SUMS` and the `review.md` append.
- The two replay trees are kept for adoption. They have 0 `.ilean` files, and their `Mathlib/` overlay is still in place.
- The landing worktree `$SP/g6b-p2/land` and the reproduction worktree `$SP/g6b-p2/repro` stay registered and were not
  pruned.
