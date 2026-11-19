# GSW 6b U14+U16, U15+U17, U18+U19 · landing record

Landed 2026-11-19 by the maintainer, per the 6b fill rulings (Seyoon, 2026-11-19, decision log row "6b fill rulings
(Seyoon)"): one PR with the three units' worker commits, routes as delivered, docs fixed on both (LE-u1517-doc,
LE-u1819-doc), duplicates accepted as ledger DL-71, the helper `Parameters.ofFamily_columns_le` in its `Nat` form. The PR
is opened by the user; its Codex fills gate is **Gate 55** (`briefs/lattice-gsw/gates/55-gsw-6b-u14-u19-fills/`, staged,
not committed).

## Branch

- **`land/gsw-6b-u14-u19`**, pushed to `origin` (new branch, no force), head
  **`dd6d274eba9b55b5a2c7c97730245a4f1bea1e90`** (tree `c33c231aaaea24f45b62b0c848cb4d3af59ef536`, `TCSlib` tree
  `004dfaefe57ac8d72d539c55151ccf0fce0b6b65`).
- **Base:** cut from `origin/cryptography/pass-shelat-ch2-4` = `53e430b68cbe22416312a4f80bbc3426c71cf86d` ("Records:
  6b fill landing rulings; ledger DL-71"). Its `TCSlib` tree is `745bf4b494b6581a5666ef9ca0a6e735a68ddcef`, as required:
  #392's merge, B6 + U12/U13.
- **PR to open:** base `cryptography/pass-shelat-ch2-4`, head `land/gsw-6b-u14-u19`, draft, body below (also
  `gates/55-gsw-6b-u14-u19-fills/pr-description.md`, byte for byte). 9 commits, 6 files, +883/−90. No other open PR
  touches the six files (the 12 open PRs' file lists, read through REST).

## Commits

Applied with `git am -3 -S --committer-date-is-author-date` in a separate sparse worktree, committer name, email and
date from each delivery's `COMMITS.tsv` (equal to the author's), in the order U14+U16, U15+U17, U18+U19.

| # | Commit | Subject | Delivered patch | Worker commit | Stable patch-id |
|---|---|---|---|---|---|
| 1 | `7fc78336261434830042072fc360b9d804ebbeea` | fill gsw-6b-u14-u16: G9-G13 Bootstrap | `0001-…-G9-G13-Bootstrap.patch` | `e09ce698` | `0742b03d` = |
| 2 | `96e22a6dbfa127c6730fabe7691c1f6b76ac87c7` | fill gsw-6b-u14-u16: L2-L3 Leveled | `0002-…-L2-L3-Leveled.patch` | `9852429e` | `bc2fb6e5` = |
| 3 | `a8f241819b8f32778ffc214ef9034634acd90b36` | fill gsw-6b-u15-u17: G15 Circular | `0001-…-G15-Circular.patch` | `f4219a24` | `cc672029` = |
| 4 | `f400635c569a6b4595bc8e2b4f67bf1f4f6bfa1b` | fill gsw-6b-u15-u17: L4 LeveledSecurity | `0002-…-L4-LeveledSecurity.patch` | `56fe8e9a` | `27ad07bd` = |
| 5 | `1664c477eee920490863d65e1667612feb4f4f98` | fill gsw-6b-u15-u17: L5 LeveledSecurity | `0003-…-L5-LeveledSecurity.patch` | `619d2029` | `b02e93cc` = |
| 6 | `f66fb1bb5d20c03dd0a37a3af651a5fe4929d6e1` | fill gsw-6b-u18-u19: G16, G17 (pure, leveled) and Parameters.ofFamily_columns_le, PolyRatio | `0001-…-G16-G17-pure-leveled-and-Paramet.patch` | `479f6a88` | `f0c74141` = |
| 7 | `103a8bde9aa19e933633fa70eee94e75a308806b` | fill gsw-6b-u18-u19: A1, A3, Asymptotic | `0002-…-A1-A3-Asymptotic.patch` | `4672ed30` | `07b0ce9c` = |
| 8 | `64ccd270825a2f41f99bfbd3d95a6509c1f55b96` | LE-u1517-doc: LeveledSecurity helper docstrings and step comments (docs only) | maintainer | — | — |
| 9 | `dd6d274eba9b55b5a2c7c97730245a4f1bea1e90` | LE-u1819-doc: Asymptotic A1/A3 proof sketches name ofFamily_columns_le (docs only) | maintainer | — | — |

- **Deliveries** read from `exchange/pass-shelat-ch5-8` at `8f15c31d38b834505dc3ecd64200dc524eeacccc`; each folder's
  tree there equals its final's (`90b4c3a1`, `f501b669`, `c414248e`), and the delivered `SHA256SUMS` verify for
  `patches/` and `src/`.
- **Authorship kept:** commits 1–7 are authored and committed by the workers (Claude, the delivered dates); all nine
  carry SSH signatures (the account's shared key; not verified, no allowed-signers file).
- **Blob identity:** the six owned files at commit 7 (the fills head) are blob-identical to the delivered `src/`
  (`55286401`, `1d8b4c8c`, `783e5817`, `6759bacd`, `dc193a7a`, `178936f4`) and to the reviews' `frozen/*.head.lean`.
- **The fills head's `TCSlib` tree is `37ae0f3223db419f636bb2d39484191f698de994`**, the full 6b stack the U15-U17/U18-U19
  review replayed (`6e363a29`, P2-7).
- **Order note:** `README.md` §Landing order lists U15-U17 before U14-U16 for per-unit PRs; this branch uses the
  rulings' order. The files are disjoint, every worker commit still equals its patch, and the tree is the same.

## The docs edits and their check

- **LE-u1517-doc** (`64ccd270`, `LeveledSecurity.lean` +22/−6, 681 → 697 lines): the review's
  `proposed/LE-u1517-doc.diff` (evidence `ff76e899…`) applied as prepared; the file at the head is blob-identical to the
  evidence's `proposed/LeveledSecurity.LE-u1517-doc.lean` (`bf70162b`). "Glue." on the seven private helpers;
  Lean-order formulas on `levelPosHybrid_zero`, `levelPosHybrid_columns`, `acceptProb_sample_levelReduction`; step
  comments in `acceptProb_sample_levelReduction`, `abs_acceptProb_id_levelReduction_sub_le`,
  `acceptProb_levelHybrid_zero_realView`.
- **LE-u1819-doc** (`dd6d274e`, `Asymptotic.lean` +8/−8): A1's sketch now reads `hm` "through
  `Parameters.ofFamily_lwe`" (the proof does not use `ofFamily_width`) and bounds `N` by
  "`Parameters.ofFamily_columns_le`, `PolyExpr.eval`" (was `dimension_le`); A3's sketch: "`(d(κ) + 1)·ℓ(κ)` bounds `N`
  by `Parameters.ofFamily_columns_le`". Only lines below `**Proof sketch.**` changed; maximum width 99. As ruled, it
  names the helper only; A3's sketch still does not list `Negligible.const_mul` or the `Finset` counting lemmas
  (U1819-F02's other remarks).
- **Code unchanged.** With comments and docstrings stripped (nested `/- -/`, `--`, string literals respected) and blank
  lines dropped, each edited file is identical before and after its edit, and all six files are identical at the fills
  head and at the head (stripped SHA-256: LeveledSecurity `d5c5767e…`, Asymptotic `3a2a3843…`). Negative control (a fill
  commit on `Asymptotic.lean`): DIFFERENT. Removed lines of the edits: six private-helper docstring lines and eight
  sketch lines of A1/A3; the 15 targets' headers and prose before `**Proof sketch.**` are unchanged.

## Re-check on the landing head

One replay of `dd6d274e` on a `cp -al` copy of `$SP/olean-snapshot` (snapshot #11, verified 0/0/0 before, mid-run, at
the end and after deleting the tree), with the records tip's U12/U13 files built in the same plan. Evidence:
`gates/55-gsw-6b-u14-u19-fills/landing-u14-u19-recheck-evidence.zip` (SHA-256
`315668d7be753bdf76197234bfa962550cc2148bbe90ba59ad7e12ce0cfcc485`; inner `SHA256SUMS` 155 rows; `PROVENANCE.txt`).

| Check | Result |
|---|---|
| **Build** | Plan against B6: changed 8, down 12, build 12, reuse 1,444. **12/12 rc 0** (Branching, DecryptFormula, the six owners, the facades GSW, Homomorphic, AdvancedEncryption, **root `TCSlib`**); 0 errors, 0 warnings, **0 `sorry`**; 2–10 s per module, peak 4.55 GB (root). |
| **State** | `stateplan update` 12 taken; `check` **1,456 RESULT OK**, again at the end with the rebuilt oleans unchanged. Ten rebuilt oleans are byte-identical to the review's full-stack replay; `LeveledSecurity` and `Asymptotic` differ (docstrings). |
| **`sorry` in the six owned files** | 0 (build warnings; and 0 `sorry`/`admit`/`native_decide`/`axiom`/`opaque` tokens in the code). |
| **Admissions** | Records tip **33 in 14** → landing head **18 in 8**: all 15 targets gone; the remaining 18 are the 8 non-GSW modules of `base-sorries.txt`. |
| **Axioms** (`#print axioms` and the census) | All 15 targets and `encrypts_bootGate`: `[propext, Classical.choice, Quot.sound]`; `Parameters.ofFamily_columns_le`: `[propext, Quot.sound]`. Census of the six modules: 168 stored constants, **0 `sorryAx`**; the `sorry` control flagged. **No allowed admitted upstream remains** (the list is empty). |
| **coe-A seal** (canonical, A variant) | rc 0, **0 errors** on all six owners, requested = verified: Bootstrap 444, Leveled 479, Circular 464, LeveledSecurity 1,561, PolyRatio 1,394, Asymptotic 1,654 (one more than the U18+U19 review's B6 count: `LeveledSecurity`'s private `levelPosHybrid` is now in its closure). |
| **Paired controls (helpers)** | `encrypts_bootGate`: in `Leveled`'s sealed copy, the `bootGate` pair (NEG `rfl` at a fan-in-0 gate fails once, POS `bootGate_of_args_eq_nil` passes) and the sealed use (NEG `rfl` at a fan-in-1 gate fails once, POS a sealed application of `encrypts_bootGate` passes). `Parameters.ofFamily_columns_le`: in `Asymptotic`'s sealed copy, NEG `rfl` on `(ofFamily F κ).lwe` fails once, POS the helper passes. Open copies 0 errors. **ALL_OK**; `bootGate` and `Parameters.ofFamily` are among the sealed requests. |
| **decls2** vs the records tip | **ADDED exactly** `encrypts_bootGate` (`Bootstrap.lean:270`) and `Parameters.ofFamily_columns_le` (`PolyRatio.lean:106`); **0 CHANGED, 0 REMOVED**. |
| **Lint delta** | `campaign_style_lint --check8b`: 92 FAIL / 103 WARN over 540 files at the tip and at the head, **identical FAIL/WARN lines**; the INFO delta is the size lines and "LeveledSecurity.lean 697 lines > target 600" (U1517-F05). `style_lint` on the six files: 0 findings at both. **None.** |
| **Lean processes** | One at a time through `runq.sh` (at most 2 others on the machine at any start): 25 starts. Lowest free disk at a start 5,909 MB. |

Not re-run here (the reviews hold them, on the same code): seal B, the units' other liveness pairs, the unfold scans and
the duplication probes. Not done: `lake build`, `lake exe cache get`.

## Gate 55 (staged, not committed)

`briefs/lattice-gsw/gates/55-gsw-6b-u14-u19-fills/`: `pack-r1.md` (questions A–I; G53-01's lesson; the rulings with
DL-71 and the two docs edits), `dispatch-r1.md` (one cloud prompt; placeholder `<RECORDS-G55>`), `source-head-r1.json`,
`pr.diff.txt` with the per-unit and landing-edit diffs, `pr-description.md`, `landing-u14-u19-recheck-evidence.zip`,
`staging-checks-r1.txt` (§1–§10), `SHA256SUMS-r1` (10 files; not over the dispatch).

**To do before dispatch:**
1. Open the PR with the body below. Fill `#<PR>`/`<PR>` in `pack-r1.md`, `source-head-r1.json` (`pr.number`, `name`),
   `staging-checks-r1.txt` (§1) and `dispatch-r1.md`, then regenerate `SHA256SUMS-r1` (`sha256sum` over the 10 files it
   lists). If the opened body differs from `pr-description.md`, replace that file first.
2. Commit the gate directory and this file with explicit paths (the pin); replace `<RECORDS-G55>` in `dispatch-r1.md`
   with `git rev-parse` of that commit in a records-only follow-up; push the records.

## Scratch state

- Work directory `$SP/land-u1419/` (logs, tools, run records; 27 MB). **Deleted:** the replay tree
  `$SP/land-u1419/olean-replay-land` (not needed: the gate does not replay), the tip lint export, the evidence extracts
  and the landing worktree (`git worktree remove`; the branch stays, local and on `origin`).
- `/home/user/tcslib` was only read, apart from this file and the gate directory (both uncommitted), the new local
  branch ref and the worktree registration (removed).

## Draft PR body

````markdown
Proof fills for fifteen of the GSW phase-6b targets stated in #377 (Gate 46), and the two public glue lemmas that ruling Q-6BF-3 (A) allows. No statement, header, definition or reader changes: proofs, refreshed proof sketches, the module admission sentences, and the ruled insertions only.

## Contents
- **U14+U16**, `Homomorphic/GSW/Bootstrap.lean` and `Leveled.lean`: G9 `encrypts_bootNAND`, G10 `decrypt_fheEval`, G18 `decrypt_fheEvalCircuit`, G12 `decrypt_keygen_fheEvalCircuit`, G13 `bootNoise_le`; L2 `encrypts_leveledEval`, L3 `decrypt_keygen_leveledEvalCircuit`. Two commits. The allowed public helper `encrypts_bootGate` (the brief's statement, byte for byte) and one private helper.
- **U15+U17**, `Circular.lean` and `LeveledSecurity.lean`: G15 `distAdv_fheView_noEvk_le`; L4 `distAdv_levelHybrid_le`, L5 `distAdv_leveledView_le`. Three commits; seven private helpers, no public one. L4's route is accepted as delivered (Q-U1517-1 A).
- **U18+U19**, `PolyRatio.lean` and `Asymptotic.lean`: G16 `bootRatio_le_poly`, G17 `decrypt_fheEval_of_ratio` and `decrypt_leveledEval_of_ratio`; A1 `indCPA_of_dlweAssumption`, A3 `leveledINDCPA_of_dlweAssumption`, both proved from their frozen `heff` hypotheses, which stay (Q-6BF-1 A). Two commits. The allowed public helper `Parameters.ofFamily_columns_le`, kept in its `Nat` form (Q-U1819-1 A), and one private helper.
- The seven worker commits are applied with `git am -3`, keeping the workers' authorship, on the records tip `53e430b6` (its `TCSlib` tree `745bf4b4` is #392's merge). The six files are blob-identical to the delivered `src/`; the last worker commit's `TCSlib` tree, `37ae0f32`, is the full 6b stack the reviews replayed.
- Two maintainer landing edits, docs only (6b fill rulings, Seyoon: "fix both"):
  - **LE-u1517-doc** (U1517-F02): "Glue." notes, Lean-order formulas and step comments on the seven private helpers of `LeveledSecurity.lean`, as prepared in the review evidence.
  - **LE-u1819-doc** (U1819-F02): A1's and A3's proof sketches name `Parameters.ofFamily_columns_le` where the proofs use it, instead of `Parameters.ofFamily_width` and `dimension_le`.
  - With comments and docstrings stripped, the code is identical before and after each edit.
- 6 files, +883 / −90; 9 commits.

## Maintainer reviews (records: `briefs/lattice-gsw/phase6/issued-6b-fills-r1/U14-U16/final-r1/`, `.../U15-U17/final-r1/`, `.../U18-U19/final-r1/`)
- **Verdicts:** all three accept; 0 blockers, 0 majors.
- **Integrity:**
  - patches reproduce the workers' heads on B6;
  - headers and statement prose of the 15 targets byte-identical to B6;
  - no `sorry`, `admit`, `native_decide`, `axiom` or `opaque`;
  - no new attribute, `set_option` or import.
- **decls2** against the records tip: ADDED exactly `encrypts_bootGate` and `Parameters.ofFamily_columns_le`; 0 changed, 0 removed.
- **Duplication:** the inline copies of three small facts are accepted and recorded as ledger **DL-71** (publish `le_bootNoise`, `LWE.sample_eq` and `distAdv_nonneg` after the fills land, and re-point the copies).
- **Minors:** U1416-F01 (records side: the pre-dispatch sweep missed `m·B ≤ bootNoise P (m·B)`; DL-71) and U1517-F02 (fixed by LE-u1517-doc).

## Landing re-check (copy of olean snapshot #11, at this branch's head)
- 12/12 modules rc 0, including the root `TCSlib`; 0 errors, 0 `sorry` warnings; state check 1,456 OK.
- Admissions fall from 33 in 14 modules (records tip) to 18 in 8: all 15 targets are gone, and the six files hold none.
- **Axioms:** the 15 targets and both helpers are standard-only; 0 `sorryAx` over the 168 constants of the six modules.
- **Seals:** canonical coe-A, 0 errors on the six files (444 / 479 / 464 / 1,561 / 1,394 / 1,654 requests); paired controls for both helpers ALL_OK.
- **Lint:** no FAIL or WARN change.

Draft until the Codex fills gate (Gate 55) passes.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA
````
