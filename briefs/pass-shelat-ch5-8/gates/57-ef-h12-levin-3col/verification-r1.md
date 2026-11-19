# Gate 57 · in-house verification of PR #398 (EF-H12) against the records tip · r1

**Result:** the merge of the PR head with the records tip is clean, and the landing re-check's replay of that merge
binds to it unchanged. **Nothing was re-run for this gate; the evidence is the landing re-check's, re-derived and
packaged.**
- **Why it binds:** the records tip at staging, `56df3925`, has the same `TCSlib` tree as the tip the landing merged,
  `fb57a36c` (`745bf4b4…`), and the same `TCSlib.lean`, `audits/`, `scripts/`, toolchain, manifest and lakefile. So
  both merges have the same `TCSlib` tree, **`05b0eecd…`**, which is the tree the landing replayed (§1).
- **Replay:** 27 modules rebuilt, all rc 0 with 0 errors. The 12 `LevinHardness` modules, the two facades, root
  `TCSlib` and `audits/pass-shelat/Checks` have **0 `sorry` and 0 warnings**. The only warnings are 15
  `declaration uses 'sorry'` in six records-side GSW modules. 1,442 modules reused.
- **State check:** OK over all 1,469 modules, keyed by the tree and again by the commit.
- **Axioms:** 488 stored constants, all standard. The headline and both corollaries are
  `[propext, Classical.choice, Quot.sound]`; the `sorry` control reports `sorryAx`.
- **Seals:** canonical coe-A and seal B give **0 on all 11 non-bridge owners**. `Bridge.lean`, the recorded
  exception, has **43 errors on 20 lines, one line per definitional reader**. Strict seals 11/11 pass, the bridge's
  minimal unseal passes.
- **Paired controls:** 50 pairs, ALL_OK. **Explicit-unfold scan:** 7 hits, all in `Bridge.lean`.
- **N4 kernel probe (LE-h12-strip):** the landing proof passes with the matcher axiomatized; the delivered proof
  fails; with the private outer matcher also axiomatized, the landing proof fails too (the known residual).
- **decls2:** 242 ADDED / 0 / 0 against the base; per landing edit 3 REMOVED (arith), then 0, 0, 0. Re-run for this
  gate with the same results.
- **Lint:** FAIL and WARN line sets identical (92/103); `style_lint` 0 findings on the 14 files.

Staged 2026-11-19, 07:25–07:45 UTC, by a maintainer sub-agent.
- **Static checks** used `git` and `python3 -I` only.
- **Lean:** none for this gate. The landing re-check (2026-11-19, 05:25–07:20 UTC) ran Lean only through the
  recipe's `runner.py`/`runner_full.py` under `runq.sh` (fewer than 3 Lean processes on the host, at least 2,048 MB
  free before each start), one queue at a time on one olean tree.
- **Never run:** `lake build`, `lake exe cache get`.
- **PR data:** read with the GitHub MCP tool `pull_request_read` (read-only REST): `get` and `get_files`.

Evidence is in `verification-r1.zip`; its SHA-256 is in `verification-SHA256SUMS`, and its inner `SHA256SUMS` lists
every file but itself. Read `PROVENANCE.txt` first. Paths below are inside the ZIP.

| Pin | Value |
|---|---|
| PR #398 `land/ef-h12-levin-3col` | **`11f33ef370efe39dc62c958b99836df0d874b18f`**, draft; 23 commits on the base; 14 files, +4,068/−0 |
| PR base (= merge base with the tip) | `bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d` (`TCSlib` tree `949dfd63…`) |
| Worker series (commits 1–19) | head `393c5cc1f1690114bb52cae031c3d71a24c6bf9c`, tree `efdd41d867a0d057d7fce00b915aedcc743138f3` (phase 2's check-head tree) |
| Landing edits | `4230f872` LE-h12-arith, `76676c14` LE-h12-strip, `ad07b07c` LE-h12-bridge, `11f33ef3` LE-h12-doc |
| Delivery | `exchange/pass-shelat-ch5-8` at `36d9ac03c329544d33b1f3f9a73e6ce32152dde2`, `inbox/fills/ef-h12-levin-3col/` (tree `4d55bc05…`) |
| Records tip at staging | `56df3925884cfba6ec043f0aa3abe0ed64e466ca`, `TCSlib` tree `745bf4b494b6581a5666ef9ca0a6e735a68ddcef` |
| Records tip of the landing re-check | `fb57a36cd2e317e977efc51e8bd11544d8c11ad2`, `TCSlib` tree `745bf4b4…` (the same) |
| Merge tree | `git merge-tree --write-tree 56df3925 11f33ef3` = **`7a7e92293aee9287ac51bd4d6f6bba897876c8b3`**: clean, one line. `TCSlib` tree **`05b0eecda079cda320090f0581b623ef38e898b8`** |
| Landing's merge | `git merge-tree --write-tree fb57a36c 11f33ef3` = `d55035ca9af63b9c22c938bd1f4da9666c099c10`, the tree of the scratch check head `a3617cde18766131a63c5f0b766a073d4863f832` (parents `11f33ef3`, `fb57a36c`; **on no ref, never pushed**); `TCSlib` tree `05b0eecd…` |
| Phase 2 evidence (records) | `briefs/efficiency-gaps/wave1/EF-H12/final-r1/ef-h12-final-r1-evidence.zip`, SHA-256 `461b7af7…` (`evidence-SHA256SUMS`) |

## 1. The merge and why the landing evidence binds (`merge/mergecheck.txt`)

- **Records commits since `fb57a36c`:** `69fe27c5`, `8130c8dd`, `d1149e8b`, `56df3925`. They change six records
  paths (the decision log, `landing.md`, `COMMON.md`, `rulings.md`, the EF-D4 brief and prompt) and **no Lean path**.
- **Unchanged at the base, `fb57a36c`, the tip and the head:** `TCSlib.lean`, `audits/`, `scripts/`, `lean-toolchain`,
  `lake-manifest.json`, `lakefile.lean` (ids in `mergecheck.txt` and `source-head-r1.json` → `unchanged`).
- **The two sides are disjoint.** Against the tip, the merge differs in exactly the 14 PR paths. Against the head, its
  Lean differs in exactly the records side's two paths since the base: `GSW/Branching` and `GSW/DecryptFormula`
  (U12/U13, #392).
- **Consequence.** `merge-tree` with `56df3925`, with `8130c8dd` and with `fb57a36c` all give `TCSlib` tree
  `05b0eecd…`. The landing's replay, seals, controls, probes and lint ran on a worktree of `a3617cde`, whose `TCSlib`
  tree is that one. **Re-running would replay identical sources; the evidence is reused.** If the records side's Lean
  moves before the pin, the merged-tree check must be re-run first.

## 2. The PR (`checks/`; commands in `tools/g57/checks.sh.txt`)

- **Commits** (`commits.tsv`): 23, each with **one SSH signature**, one `Co-Authored-By` line and one
  `Claude-Session` line. Commits 1–3 are authored "Claude (EF-H12 fill)", 4–19 "Claude-EF-H12" (the worker's
  session), 20–23 "Claude" (the landing session).
- **Patch identity** (`patch-id.tsv`): the stable patch-ids of the 19 delivered patches equal those of commits 1–19,
  **19/19**. The 14 files at `393c5cc1` are blob-equal to the delivery's `src/`.
- **Landing edits, code vs text** (`landing-edits-codeonly.txt`, comments and docstrings stripped):
  - LE-h12-arith changes code in `UnaryArith` and `ColoringGraph` (+32/−45);
  - LE-h12-strip changes code in `Verifier` only (+25/−2);
  - **LE-h12-bridge (3 files, +45/−28) and LE-h12-doc (9 files, +65/−24) are docstring-only.**
- **PR #398 at staging** (`pr/`): open, **draft**, base `cryptography/pass-shelat-ch2-4` (GitHub's base SHA
  `fb57a36c`), head `11f33ef3`, 23 commits, 14 files, +4,068.
  - The REST patches equal `git diff bff0567b 11f33ef3` for 13 files byte for byte; for the facade
    `ZeroKnowledge.lean` the +/− lines are equal and only the hunk grouping differs (`files-vs-git.txt`).
  - The body equals the draft in `landing.md` except the closing footer line (`body-vs-landing-draft.diff`).
- **Source PDFs** (`source-pdfs.txt`): the local copies' SHA-256 equal the ingest reports' values (see the dispatch).

## 3. The replay (`replay/`)

**Start tree:** phase 2's `$SP/olean-replay-efh12` (state-checked 1,469/1,469 RESULT OK at `63d619e8` before the copy,
`statecheck-pre.txt`, and again at the end, `statecheck-efh12-end.log`), copied with `cp -al` to `$SP/land-efh12/replay` (1,501 files, all hard
links). Snapshot #11 was verified 0/0/0 before and at the end (`snapverify-*.log`).

| Check | Result |
|---|---|
| Plan (`plan/`) | `fullorder` 1,469 modules; **27 to build, 1,442 reused**: the 12 `LevinHardness` modules, the two facades, U12/U13 and their 9 GSW downstream modules, root `TCSlib`, `audits/pass-shelat/Checks` |
| Build (`build/results.jsonl`, `permod.log`) | **27/27 rc 0**; `error:` 0, `error(` 0; no log/record mismatch. Warnings: 15, all `declaration uses 'sorry'`, in `Bootstrap` 5, `PolyRatio` 3, `Asymptotic`, `Leveled`, `LeveledSecurity` 2 each, `Circular` 1 (records side). The 14 EF-H12 modules, root and `Checks`: 0 warnings, 0 `sorry` |
| Accept | `stateplan update` took 27, none refused; **check 1,469/1,469 RESULT OK** |
| Key labelling (pack S-4) | Plan, build and update were keyed with the check head's **tree** id `d55035ca`. Re-run keyed by the commit `a3617cde` (`plan-commit/`): `fullorder` identical, **0 to build**, check 1,469/1,469 OK (`stateplan-check-commit.log`) |
| Dev checks (`dev/`) | Pre-commit checks of the edited modules (`UnaryArith`, `ColoringGraph`, `ColoringWitness`, `Verifier`) |

## 4. Axioms (`axioms/`)

`AxiomsLand` (phase 2's census probe, unchanged) ran rc 0; its one warning is the control's.
- **488 stored constants** of the 12 modules and the facade (256 `DECL` + 232 `AUX` rows): 189
  `{Classical.choice, Quot.sound, propext}`, 134 `{Quot.sound, propext}`, 96 `{propext}`, 69 `{}`. **0 non-standard.**
- **Headline rows:** `levinNPHard_L3COL`, `zk_proof_of_witnessRelation_of_owp_unconditional`,
  `zk_proof_of_mem_NP_of_owp_unconditional`: each `[propext, Classical.choice, Quot.sound]`.
- **Control:** `CONTROL efh12SorryControl [sorryAx]`.
- **Against phase 2's 483:** 3 gone (`unaryDiv_poly`, `unaryMod_poly`, `unaryPow_poly`), 8 auxiliaries new (two `_simp`
  lemmas of `polyTimeComputable_gadgetAdj`; in `Verifier`, the private generated `eq_1`/`eq_2`/`splitter` of the two
  catalog matchers), no shared constant's axiom set changed (the landing's comparison).

## 5. Seals on the merged tree (`seal/`, `strict/`, `probes/`)

**Method.** Canonical coe-A over the 12 owners: the collector `Collect` (recipe template; rc 0), `mkseals_coe.py`
(A variant, unmodified, `SEAL_CHUNK=1000`), the gated `runner_full.py`. Seal B adds `PolyExpr.eval`. Every seal part
has its install and end records (`seal/*/logs/`). Source hashes of every run: `probes/probe-sources.sha256`.

| Owner | Requests (A / B) | coe-A errors | Seal-B errors |
|---|---:|---:|---:|
| `Relations` | 191 / 191 | **0** | **0** |
| `Verifier` | 2,150 / 2,151 | **0** (phase 2: 1, F08) | **0** (phase 2: 1) |
| `CircuitWitness` | 4,805 / 4,806 | **0** | **0** |
| `Gadget` | 1,052 / 1,053 | **0** | **0** |
| `UnaryArith` | 1,059 / 1,060 | **0** | **0** |
| `ColoringGraph` | 1,942 / 1,943 | **0** | **0** |
| `ColoringParse` | 2,550 / 2,551 | **0** | **0** |
| `ColoringWitness` | 1,854 / 1,855 | **0** | **0** |
| `Soundness` | 2,550 / 2,551 | **0** | **0** |
| `Padding` | 1,847 / 1,848 | **0** | **0** |
| `Hardness` | 4,865 / 4,866 | **0** | **0** |
| **`Bridge`** (the recorded exception) | 2,478 / 2,479 | **43 on 20 lines** | **43 on the same 20 lines** |

- **`Bridge`, attributed** (`seal/bridge-error-map.tsv`, re-derived for this gate from the raw logs and the head
  source): each of the 20 error lines is one reader: the 17 `rfl`/`Iff.rfl` readers with 1 error each,
  `syntaxStep_eq` 12, `edgeRelation_gadget_literal` 12, `edgeRelation_literal_gadget` 2. 17 + 12 + 12 + 2 = 43. The
  seven `simp [EdgeRelation]` readers pass sealed (they read `EdgeRelation` through its equation lemmas).
- **Requests:** equal to phase 2's except `Hardness` (+2, new matcher definitions in its closure). Seal B adds one
  request to every owner except `Relations`, whose closure does not contain `PolyExpr.eval` (pack S-9).
- **Strict seals** (`strict/`): the worker's 11 whole-file seals, moved onto the landing sources by `git merge-file`:
  **11/11 rc 0, 0 errors**. `strict-vs-head.txt` (this gate): each strict source is the head source plus exactly one
  line (`Gadget`: a comment, no candidates).
- **Bridge minimal unseal** (`BridgeMin`, phase 2's file moved the same way): rc 0, 0 errors.

## 6. Paired controls and the explicit-unfold scan (`ctl/`, `scan/`)

- **Controls:** phase 2's `mkctl.py` and `ctl-pairs.tsv`, **50 pairs**, one per new public definition (none was
  removed). `Ctl_sealed` rc 1 with **exactly 50 errors, one at each NEG line** (all "Type mismatch"), none at a POS
  line; `Ctl_open` rc 0 with 0 errors. **ALL_OK** (`ctl/check.txt`, recounted for this gate).
- **Scan** (gate-04 `scan.py` with the `G04Collect` tables; `scan/unfold-scan-pre.txt`):
  - (c1) **7 hits**, exactly the seven `simp [EdgeRelation]` lines of `Bridge.lean` (182, 187, 192, 199, 209, 231, 238);
  - **0 hits outside `Bridge.lean`**; (c2) 0 of 7 `show`/`change` occurrences on a failing line; (c3) 0 proof terms
    referring to a generated equation lemma of a foreign TCSlib **definition**.
  - LE-h12-strip's `…stripLastTM_computes.match_1.eq_1`/`eq_2` are equation lemmas of a compiler-generated
    **matcher**, named in `refine` terms; the scan's rules do not cover them (pack S-2). N4 checks them (§7).

## 7. The N4 kernel probe for LE-h12-strip (`n4/`)

`N4Strip` replaces the matcher by an **axiom** of the same type and rebuilds every TCSlib constant of the closure that
mentions it over the axiom (foreign theorems and the matcher's `eq_N`/`splitter` become axioms with the replaced
statement; definitions are re-added; the module's own theorems are re-checked by the kernel). Run on the check head
(rc 0):

| Case | Result |
|---|---|
| Landing proof of `polyTimeComputable_stripCert`, `stripLastTM_computes.match_1` axiomatized | **RESULT OK**: kernel accepts. Re-checked: `polyTimeComputable_stripCert`; axiomatized statements: `computesFunInTime_stripLast` and the matcher's `eq_1`/`eq_2` |
| The delivered (F08) proof, compiled as control `EFH12N4.oldStrip` | **RESULT FAIL**: kernel "application type mismatch" |
| Landing proof with **both** matchers axiomatized (`stripLastTM_computes.match_1` and the private `Turing.FinTM.extract_run.match_1` of `Build/Primitives.lean`) | **RESULT FAIL** (information: the residual of pack S-3; the delivered proof had it as well) |

The development runs (`n4/dev/`: `StripTry`, `MatchInfo`, the first `N4Strip` run) are kept for the record.

## 8. decls2 (`decls2/`)

Pinned `decls2.py` (SHA-256 `fa81981a…`). The landing's tables are in `landing/`; this gate re-ran each from git
objects (`rerun-*.tsv`, by the commands in `tools/g57/decls2-rerun.sh.txt`):

| Comparison | Result | Re-run equal to the landing's |
|---|---|---|
| head `11f33ef3` vs base `bff0567b`, 14 files | **242 ADDED, 0 CHANGED, 0 REMOVED** | yes, byte-identical |
| worker series `393c5cc1` vs base | 245 ADDED | yes, byte-identical (and to phase 1's `my-decls2.txt`) |
| LE-h12-arith `4230f872` vs `393c5cc1` | 3 REMOVED: `unaryDiv_poly`, `unaryMod_poly`, `unaryPow_poly` | yes |
| LE-h12-strip, LE-h12-bridge, LE-h12-doc (each vs its parent) | empty | yes |

## 9. Lint and sizes (`lint/`)

- **`campaign_style_lint --check8b`** on `TCSlib/Cryptography`, at the landing tip `fb57a36c` (540 files) and the check
  head `a3617cde` (553 files): **92 FAIL / 103 WARN** for both; the FAIL/WARN line sets are identical, raw
  (`delta.txt`). Both bind: the tip's `TCSlib/` and `scripts/` are unchanged since `fb57a36c`.
- **`style_lint.py`** on the 14 files: **0 findings**.
- **Sizes:** 59 to 720 lines (`ColoringParse` 720, `ColoringGraph` 675, `ColoringWitness` 400), at most 100 characters
  wide.

## 10. What is not here

- No new Lean run. Phase 2's bridge demonstrations (necessity: 46 reader uses fail without the readers; owner form:
  the 27 readers compile verbatim in their 5 owner files) are in the phase 2 ZIP (records, `461b7af7…`) and were not
  repeated at the landing head; LE-h12-bridge changed only docstrings (§2), so the readers' statements and proofs are
  those phase 2 checked.
- The worktrees and trees the landing kept (`$SP/land-efh12/{replay,mergewt,wt,dwt,lint}`) were only read.
