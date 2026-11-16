# Gate 39 · Sequential repetition preserves zero knowledge and interactive proofs (`seq-zk`, [PS10, Theorem 175.1]) · round 2

The auditor is Codex. Round 1 was HOLD (0/1/0/0); its findings are `findings/gate39-seq-zk-findings.md` (SHA-256
`98be3c22…`). This round re-audits the fix of G39-01, checks the rebuild and seal evidence of that fix, and checks
that nothing regressed and nothing new is undisclosed. The round-1 pack (`pack.md`) still defines the scope; its
questions stand for anything round 1 left unverified.

- **PR:** draft [PR #327](https://github.com/Shilun-Allan-Li/tcslib/pull/327), now at
  `a94ba750b2f21ea5f2c3e58bc7959ad5ac9de871` (branch `land/pass-shelat-seq-zk`, tree
  `3efe62af6b414655aefa9506e3e63baedea33ae5`). Round 1 audited `bd19c433a4cf3d4027ffc891d7d3c06e927e9dfa`.
- **Base:** `05d26fe5b41fcb9426ec220d877d03264b9c8e8c`, as in round 1 (`git merge-base` with the current tip). **No
  rebase:** the head is the round-1 head plus one commit (`checks/rebase.txt`).
- **The tip** is now `364776f7ba77f0d6d210941eda663dafa06f0a0e`. Since round 1 it has merged **#326** (derand,
  `c27005d6`, merge commit `7e85f4c0`, 2026-11-16) and records. The LE-gate39 job built on the tip `0542dd92` ("Records:
  #326 merged"); from `0542dd92` to `364776f7` no path under `TCSlib/` or `audits/` changed (`checks/mergetrees.txt`).
- **New since round 1:** **LE-gate39** `a94ba750` on `bd19c433`, by the maintainer (author and committer Claude,
  SSH-signed): `SequentialZK/RealPrefixBounds.lean` only, +5/−5. It was fast-forward pushed; `refs/pull/327/head` is
  `a94ba750`.
- **Resolutions:** `resolutions-r1.md` (G39-01: "Fix by LE-gate39", the same practice as G36-01), and the
  decision-log rows of 2026-11-16 (in `verification-r2.zip`).
- **Pending merge condition** (not an audit item; § 5): the merge order. #327 merges before #324; #324 merges last.

Lean paths below are under `TCSlib/Cryptography/` unless they start with `TCSlib/`; `SQ/` is
`Composability/SequentialZK/`.

## What to check

### 1. G39-01: is `hsource` now the public `next_length_le`, with nothing else changed?

The diff is `le-gate39.diff.txt` (= `git diff bd19c433 a94ba750`, SHA-256 `184c7e2f…`; byte-identical to the evidence's
`landing/le-gate39.diff` and to the diff part of `landing/patch/0001-…patch`). The public lemma, unchanged since round
1 (`SQ/ProofTransfers.lean`, blob `f7f6b19f`), introduced by the worker commit `29b81e8b`:

```lean
-- SQ/ProofTransfers.lean:38
theorem next_length_le {π ρ : Protocol} {x : List Bool} {q p : ℕ}
    (d : PaddedProverSpec π ρ x q p) (y : List Bool) (B : ℕ)
    (hB : ∀ r hist, (π.P.next x y r hist).length ≤ B) :
    ∀ r hist, (ρ.P.next x y r hist).length ≤ B
```

The edit, with doc comments deleted (`checks/lecheck.txt` B; 7 code lines):

```lean
-- SQ/RealPrefixBounds.lean: one import added after the two existing imports
import TCSlib.Cryptography.Composability.SequentialZK.ProofTransfers
-- in PaddedProverSpec.realPrefix_bounds, :83-86 at round 1 (added by the worker commit 5fa0430c) ...
  have hsource (hist : List (List Bool)) : (ρ.P.next x y tape hist).length ≤ B := by
    rw [d.next y tape hist]
    dsimp only
    split_ifs <;> first | exact hbound _ _ | exact Nat.zero_le B
-- ... is now :85-86
  have hsource (hist : List (List Bool)) : (ρ.P.next x y tape hist).length ≤ B :=
    d.next_length_le y B hbound tape hist
```

This is your proposed replacement, character for character. `hbound` is bound in `realPrefix_bounds` as
`(hbound : ∀ r hist, (π.P.next x y r hist).length ≤ B)`, the type of `hB`; the lemma's conclusion at `r := tape` is the
type of `hsource`. The two later uses of `hsource` (`exec_snd_bounded`, `length_encodeMsgs_exec_snd_le`) are unchanged.

Re-checked from git objects (`checks/lecheck.txt`):
- **Headers.** The commit changes one file. Its one declaration, `realPrefix_bounds`, keeps its header byte for byte.
  In all 41 unit files the 264 declarations keep their names, order and headers (264/264), and the 42 definition
  blocks are identical. Only `RealPrefixBounds.lean`'s blob changed.
- **Docstring.** The only changed docstring is `realPrefix_bounds`'s proof sketch. It is a pure insertion of one
  contiguous chunk: after "…by the specification's public reply equation." it adds "This is the / public theorem
  `next_length_le`." (with a line break; the file stays 101 lines, maximum width 94). Removing the chunk gives the
  round-1 text. The statement prose is unchanged.
- **The import is acyclic and adds exactly one module.** The closure of `ProofTransfers` (136 modules, itself
  included) does not contain `RealPrefixBounds`, and it lies inside `RealPrefixBounds`' round-1 closure plus
  `ProofTransfers` itself. `RealPrefixBounds`' closure grows from 144 to 145 modules (itself included), by
  `ProofTransfers` alone. The union of the 41 unit closures is unchanged (185 modules; `ProofTransfers` is a unit
  module). `RealPrefixBounds`' downstream is unchanged: 6 modules (itself, `SQ/ComputationalTransfer`, the
  `SequentialZK` facade, `Composability`, `Composability/ThreeColoring`, root `TCSlib`).
- **decls2** against round 1 is empty (`checks/decls2-bd19c433-vs-a94ba750.tsv`). Against the base it is still
  **196 ADDED, 0 CHANGED, 0 REMOVED** (`checks/decls2-05d26fe5-vs-a94ba750.tsv`); it differs from round 1's table only
  in `realPrefix_bounds`' line number (54 → 56).
- **The frozen files** `Composability/SequentialZK.lean` and `ZeroKnowledge/Defs.lean` are unchanged since round 1, so
  the frozen check (0 differences) and S-01 stand.

**The overlap record.** G39-01 is fixed, not debt, so no ledger row is added (as for G36-01). The record of the
duplicate and its removal is `resolutions-r1.md`, the decision-log rows of 2026-11-16 (Gate 39 HOLD; LE-gate39
pushed), and the new sketch sentence in the code. The worker's REPORT is a delivery record and is not edited.

Is the re-derivation proof only, and does it use the published lemma as stated?

### 2. The rebuild and seal evidence (`landing-r1/`)

`gate39-le-evidence.zip`, SHA-256 `35e990e7cafba0222ee96e8618ccc52d70479b43d6e0fe4f399b19fa7643c85b`: 979 entries,
44 directories and 935 files, which are the 934 paths of its manifest `evidence-SHA256SUMS` plus `SHA256SUMS`
(byte-identical to the manifest). Its `PROVENANCE.txt` is beside it, byte-identical to the ZIP's. `checks/evidence.txt`
re-verifies the ZIP and reads back each entry cited below.

- **Statements and edit checks** (`statements/`, `checks/`): decls2 against the parent is empty; `touched` gives
  exactly 1 CHANGED, `realPrefix_bounds` (its proof). `checks/legate39-checks.txt`: the header is identical, the
  statement prose the same, the stripped code diff is the 7 lines of § 1, and the docstring change is a pure insertion.
- **Lint:** `scripts/campaign_style_lint.py TCSlib/Cryptography --check8b` at the head gives 92 FAIL / 101 WARN, with a
  FAIL/WARN line set identical to round 1's (the line diff is empty).
- **(a) #327 alone on the tip** (#326 merged): the build tree is `git merge-tree --write-tree 0542dd92 a94ba750` =
  `daac6140` (scratch commit `4cd422c7`). `checks/mergetrees.txt`: the current tip merged with the head has the same
  `TCSlib` and `audits` subtrees; the trees differ only in records.
  - **679/679 rc 0**, 0 errors in both forms (`error:` 0, `error(` 0; G26-N1), substring "error" 0, 420 warnings, 59
    sorry warnings (all in admitted non-PR modules; the tip's own admissions include `ComposeSecurity` 3 and `Yao` 2).
  - The build set is the downstream of `RealPrefixBounds` and both `audits/*/Checks` (8 modules) plus the 671
    base-delta modules the snapshot needed.
  - `RealPrefixBounds`: rc 0, 0 errors, 0 sorry, 0 warnings. The 8 downstream modules: rc 0, 0 errors, 0 sorry; the
    only warning is `SequentialZK`'s disclosed unused `hQ`.
  - 678 of 679 modules are byte-identical, in source and olean, to at least one reference build (the combined build,
    its solo builds and reference runs). The one without is `RealPrefixBounds`, whose source is new.
  - All 679 built sources equal their blobs in `daac6140` and in the current tip merged with the head
    (`checks/srcequality.txt`).
  - **Admissions:** 202 at the tip → **197**, −5: `SequentialZK` 5 → 0. Every new seq-zk module has 0.
    `RealPrefixBounds` has no `sorry` or `admit` token.
- **(b) The final combined tree** tip + #327 + #324 = `129810e4` (scratch commit `c51cf08d`); both merge orders give
  it. `checks/integration.txt`: merging the head and #324 onto the current tip, in both orders, gives the same `TCSlib`
  and `audits` subtrees. Against the earlier combined build of all open PRs (int-all-open, tree `3fb05ea0`, round 1's
  integration evidence), the only Lean path that differs is `RealPrefixBounds.lean`. As a control, the same merge chain
  with round 1's `bd19c433` gives exactly int-all-open's `TCSlib` and `audits` subtrees.
  - The rebuild set is 26 modules: the downstream of `RealPrefixBounds` and both `audits/*/Checks` (8), together with
    the downstream of #324's 16 files (19). Root `TCSlib` is shared. #324's downstream is included because tree (a)
    held the tip state for those modules.
  - Every other module of the set's import closure (1306) had the combined build's source and held the combined
    build's recorded olean: OK 1306, RESTORE 0, MISSING 0.
  - **26/26 rc 0**, 0 errors in both forms, substring 0, sorry 0, 1 warning (`SequentialZK`, the unused `hQ`).
    `build-b/verify.txt`: RESULT OK. `RealPrefixBounds` is byte-identical to (a); the other 25 are byte-identical to
    int-all-open's combined build.
  - **Admissions: 194**, identical module by module to int-all-open's combined census (the diff is empty).
  - Tree check (1332 modules at `c51cf08d`): every module rc 0 at its source, every olean = its record, none missing,
    no stray olean, no empty directory: RESULT OK.
- **Rule 10** (`rule10/`, at `c51cf08d`; owner `RealPrefixBounds.lean`; every probe run with `-DmaxErrors=0`):
  - The collector probe gives rc 0, 0 errors, 2508 CAT lines.
  - Seals strict A/B and coe A/B: all 4 probes rc 0, 0 errors, 0 failing declarations, install and EOF records present.
    Requests: strict 1875/1876, coe 1874/1875.
  - Paired controls (`PolyExpr.eval`, the `FinDist` CoeFun instance, `ZK`/`ZK_iff`, `StatZK`/`StatZK_iff`,
    `Composability.prefixProver`/`prefixProver_coins`):
    - **coe:** 4 probes. **7 sealed negatives** (A 3, B 4) each fail exactly once; the readers do not fail.
      `ALL_OK True`.
    - **strict:** 4 probes. **9 sealed negatives** (A 4, B 5) each fail exactly once. Separately, `ctlCoeReader`
      fails once in each sealed strict probe, **2** in all. That is the known harness effect: the reader elaborates to
      the sealed `FinDist` CoeFun instance itself, which the coe seal exempts. So `ALL_OK False`. The same was recorded
      in the seq-zk review, the sc-compose review and LE-gate37 (`rule10/controls-strict-attribution.txt`).
    - Unsealed controls all pass.
  - The other 40 unit files are byte-identical to round 1, so round 1's seals of them stand. Say if you disagree.
- **Axioms** (the combined tree, `axioms/`): the five targets, `PerfectZK.seqRep`, `PerfectZKAbort.seqRep`,
  `colSeq_efficientProverProof_zk`, `negligible_colSeqSound`, `StatZK_iff`, `zk_of_padded_spec` and
  `realPrefix_bounds` use `[propext, Classical.choice, Quot.sound]`; `next_length_le` uses `[propext]`.
- **Restore:** the olean tree was restored to `457ba704…` (SNAPSHOT EQUAL; `restore/`).

Is the evidence sufficient for a proof-only change of one module, and does it show no regression?

### 3. Duplication: is there any new undisclosed copy since round 1?

`checks/dupscan.txt`:
- **(A) Since round 1** the only code lines changed in the 41 unit files are LE-gate39's 7 (§ 1). The declaration list
  is identical (264 names).
- **(B) The G39-01 pattern.** At the head, the only proof lines in the unit that rewrite with a `PaddedProverSpec` reply
  equation and close by `split_ifs … | exact Nat.zero_le` are those of `next_length_le` itself (`SQ/ProofTransfers.lean`
  :43–45). `next_length_le` is used twice: by `PaddedProverSpec.complete` (`:72`) and by `hsource`.
- **(C) Statement scan** (binders and type after whitespace normalisation, name excluded). Each of the 175 theorems
  new at the head was compared against the files the tip changed since the base (58, including #326's) and against
  each open PR (#324, #331, #332, #333). There are **0 hits**. No new name of #327 is declared in a file any of them
  changed (`checks/namecheck.txt`).
- **(D) The same scan against the whole tree** (20686 theorems in 1278 files) has **0 hits**. As round 1 noted, a
  statement scan cannot see a local `have`; (B) is the targeted check for the G39-01 class.
- **Any further undisclosed duplicate of a public lemma is a major**, as in round 1.

### 4. Are the round-1 confirmations still valid at the new head?

Round 1 confirmed the five proofs, the uniformity of `SQ`, the bounds `Q·|ε|`, exactly `Q·δ` and `s^Q`, the boundary
cases, the freeze (196/0/0), S-01, LE-doc (docstrings only), Rule 10 (0 new failing declarations), the axioms, the
ownership and final-sweep records, and the 11 truncated formulas. Only `realPrefix_bounds`' proof of `hsource` and
its sketch changed (§ 1), and the theorem's statement is unchanged. Is any of these confirmations affected?

### 5. The merge interaction

`git merge-tree --write-tree a94ba750 <x>` is clean for each, and no path is shared (`checks/mergetrees.txt`,
`checks/downstream.txt`):

| `<x>` | head | merged tree | downstream of both | built? |
|---|---|---|---|---|
| the tip | `364776f7` | `c773e34d` | 52 (through #326's `DTIME`, `IterateFind` and #323's `DAGCircuit`, merged) | **yes**: (a); every Lean path = `daac6140` |
| #324 (sc-compose) | `4bd2d80b` | `e0ac5a25` | root `TCSlib` | **yes**: (b) is the final merged state |
| #331 (pairings) | `110c2f9d` | `8ca09ac9` | root `TCSlib` | no |
| #332 (DAGCircuit readers) | `94eae71b` | `4179ce90` | 41 (through `DAGCircuit`) | no |
| #333 (GSW) | `486f44f8` | `6fe5ff61` | 41 (through `DAGCircuit`) | no |
| #326 (merged) | `c27005d6` | `5a0816cc` | 52 | in the tip |

- **#331, #332 and #333** are draft statement PRs of the pairings and lattice campaigns, opened after round 1's
  combined build. They share no path with #327. Their integration with whichever PR is merged first is their own merge
  condition, run by the maintainer, as their Gates 40 and 41 recorded.
- **Merge order (not an audit item).** #327 merges next, on a tip that contains #326: that is state (a). #324 merges
  last: that is state (b). Both states are built. What you can raise: a concrete reason a merged tree cannot build, or a
  name or instance interaction.

## Known dispositions and slips (not findings)

- **`checks/doconly-sg.txt` prints "RESULT FAIL".** That tool asks whether the edit is docstring-only; it is not (the
  proof and the import change). The PROVENANCE says so ("code-identical False (expected)").
- **`%G?` prints N** for every commit of the series. That is only because this machine has no
  `gpg.ssh.allowedSignersFile`; each commit carries one `gpgsig` header (`checks/rebase.txt`).
- **Closure sizes.** The PROVENANCE gives 135 (`ProofTransfers`) and 143 (`RealPrefixBounds`) modules, without the
  module itself; § 1 counts the module itself (136; 144 → 145). They agree.
- **"nothing pushed"** in the PROVENANCE: true of the job. The maintainer then fast-forward pushed `a94ba750`.
- **The restore.** A classifier outage stopped the job's shell before its last two finish scripts. The maintainer read
  and ran them; the PROVENANCE's last section ("Restore (run by the maintainer, 2026-11-16T07:39:34Z)") records the
  result: 561 restored, 133 new oleans deleted, the Mathlib overlay removed, SNAPSHOT EQUAL.
- **The PR description is still round 1's.** It names `bd19c433` and does not mention LE-gate39. An update is drafted
  in the records (`gates/39-seq-zk/pr-description-r2.md`); the maintainer applies it before #327 is marked ready. It is
  not in this pack.
- **Job-local names.** The PROVENANCE refers to `$SP` paths; the records copies have the same bytes.

## Evidence files

- **`resolutions-r1.md`** and **`findings/`**: the round-1 dispositions and findings.
- **`le-gate39.diff.txt`**: `git diff bd19c433 a94ba750` (1 file, +5/−5).
- **`landing-r1/`**: `PROVENANCE.txt` (= the ZIP's), `gate39-le-evidence.zip` and its manifest. The patch is the ZIP's
  `landing/patch/`.
- **`integration/`**: round 1's combined build of all open PRs (int-all-open: `PROVENANCE.txt`,
  `int-all-open-evidence.zip`, `evidence-SHA256SUMS`), the reference for build (b).
- **`verification-r2.zip`**: `SHA256SUMS` lists every other entry, and `PROVENANCE.txt` gives each source.
  - Byte-identical originals at records `364776f7ba77f0d6d210941eda663dafa06f0a0e`: the decision log, the duplication
    ledger, the deferred-work register and the seq-zk review.
  - `checks/`, generated from git objects alone: the series, the edit, merge trees, downstream, names, the combined
    tree, source equality, the duplication scans, decls2 and the evidence read-back, with their scripts.
- **`pr.diff-r2.txt`**: `git diff origin/cryptography/pass-shelat-ch2-4...a94ba750`, which equals `05d26fe5..a94ba750`
  byte for byte (41 paths, 6652 insertions, 14 deletions, as in round 1).
- **`source-head-r2.json`**: hashes, line counts and over-width counts of the 41 changed files at `a94ba750`. It
  differs from `source-head.json` only in `RealPrefixBounds.lean`; no line is over 100 characters.
- **`sources-r2.zip`**: the source closure at `a94ba750` of every changed module, 185 files. It is round 1's set; only
  `RealPrefixBounds.lean` differs.
- **Round 1:** `outbox/gates/39-seq-zk-gate/` on the exchange at `da8f8f66e505a9e27034667ff68a3b104036e84e`, with
  records `d5a3e2d0c399b918d72e5a51732905625e500bd2`; `pack.md` here is its pack.

## Findings delivery

Return `gate39-seq-zk-r2-findings.md` as Markdown in this chat. If you have several evidence files, return a ZIP.
Use the same table and severities as round 1, and say for each round-1 finding whether it is closed. Report the audited
head and the counts by severity. The gate closes at zero blockers and zero majors.
