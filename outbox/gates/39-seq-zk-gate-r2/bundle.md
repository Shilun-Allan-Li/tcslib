## ===== briefs/pass-shelat-ch5-8/gates/39-seq-zk/pack-r2.md =====

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

## ===== briefs/pass-shelat-ch5-8/gates/39-seq-zk/resolutions-r1.md =====

# Gate 39 · resolutions, round 1 · HOLD → round 2 staged

Codex's verdict is **HOLD**: 0 blockers, 1 major, 0 minors, 0 notes.
- **Findings:** `findings/gate39-seq-zk-findings.md`, SHA-256 `98be3c2237cb36981087f4e941d0e7e429c9db28226db6fef272805cdfe8f618`.
- **Audited head:** `bd19c433a4cf3d4027ffc891d7d3c06e927e9dfa`, records `d5a3e2d0`, exchange `da8f8f66`.

Codex found no mathematical defect in the five target proofs. It confirmed:
- `SQ` is uniform.
- The ZK and statistical-ZK error bounds are `Q·|ε|` and exactly `Q·δ`.
- The adaptive soundness bound is `s^Q`.
- The boundary cases hold.
- The freeze holds at 196/0/0.
- S-01 is `Iff.rfl`.
- LE-doc changes docstrings only.
- Rule 10 adds 0 new failing declarations.
- The axioms are standard.
- The ownership and final-sweep records are consistent.

The 11 truncated formulas are acceptable: their prose states the omitted property.

| # | Severity | Disposition |
|---|---|---|
| G39-01 | major | **Fixed by LE-gate39** `a94ba750b2f21ea5f2c3e58bc7959ad5ac9de871` on `bd19c433` (proof only; the same practice as G36-01). The local `hsource` in `PaddedProverSpec.realPrefix_bounds` (`SequentialZK/RealPrefixBounds.lean:83`, now `:85`) re-proved the PR's own public `PaddedProverSpec.next_length_le` (`ProofTransfers.lean:38`). It is now `d.next_length_le y B hbound tape hist`, with an import of `SequentialZK.ProofTransfers` (acyclic; it adds only that module to the closure). The header is unchanged, and the sketch gains one sentence naming the public theorem. Evidence: `landing-r1/gate39-le-evidence.zip` (SHA-256 `35e990e7cafba0222ee96e8618ccc52d70479b43d6e0fe4f399b19fa7643c85b`, 934 manifest files) and its `PROVENANCE.txt`. It shows decls2 against `bd19c433` empty, #327 alone on the tip 679/679 rc 0 (admissions 202 → 197), the final combined tree 26/26 rc 0 (admissions 194), the seals of `RealPrefixBounds` passing, and standard axioms. The overlap record: the duplicate is removed, so no ledger row (as for G36-01); this table and the decision log record it. **Round 2 staged:** `pack-r2.md` and the round-2 files beside it; the Codex prompt is `dispatch-r2.md`. |

**Next:** Gate 39 round 2 (Codex) at `a94ba750`.

## ===== briefs/pass-shelat-ch5-8/gates/39-seq-zk/findings/gate39-seq-zk-findings.md =====

# Pass–shelat Gate 39 — seq-zk

**Verdict: HOLD. Counts: 0 blockers, 1 major, 0 minors, 0 notes.**

No mathematical defect was found in the five target proofs. An undisclosed inline
re-proof of an earlier public helper remains. The issued duplication rule makes this
major even though it does not invalidate the mathematics.

| Item | Audited revision |
|---|---|
| [Draft PR #327](https://github.com/Shilun-Allan-Li/tcslib/pull/327) | `bd19c433a4cf3d4027ffc891d7d3c06e927e9dfa` |
| Exchange | `da8f8f66e505a9e27034667ff68a3b104036e84e` |
| Campaign records | `d5a3e2d0c399b918d72e5a51732905625e500bd2` |
| PR base | `05d26fe5b41fcb9426ec220d877d03264b9c8e8c` |
| Issue base | `107f1e8c218733eac12d6b9bee6fece441271317` |

This is a source audit and an independent recheck of supplied native evidence, **not a
fresh Lean build**. The live PR metadata confirmed the requested head. No repository
source, PR, dispatch record, or merge was changed.

## Finding

Paths in this section are under `TCSlib/Cryptography/Composability/SequentialZK/`.

| ID | Severity | File · declaration | Claim and evidence | Proposed fix |
|---|---|---|---|---|
| G39-01 | **major** | `RealPrefixBounds.lean:83` · local `hsource` in `PaddedProverSpec.realPrefix_bounds` | Re-proves the public `PaddedProverSpec.next_length_le` from `ProofTransfers.lean:38`, specialized to `r := tape`. The public lemma arrived in landing commit `29b81e8ba`; the inline re-proof arrived later in `5fa0430ca`. The REPORT describes both helpers but does not disclose this overlap. Its account of `realPrefix_bounds` cites the specification reply readers and ExecutionBounds, omitting the exact existing public helper. | Import `SequentialZK.ProofTransfers` and derive `hsource` directly from `d.next_length_le y B hbound tape hist`. Preserve headers, correct the overlap record, and refresh affected checks. |

The existing public conclusion is:

```lean
(hB : ∀ r hist, (π.P.next x y r hist).length ≤ B) :
  ∀ r hist, (ρ.P.next x y r hist).length ≤ B
```

The later local proof is:

```lean
have hsource (hist : List (List Bool)) : (ρ.P.next x y tape hist).length ≤ B := by
  rw [d.next y tape hist]
  dsimp only
  split_ifs <;> first | exact hbound _ _ | exact Nat.zero_le B
```

This is the same bound and branch argument. The replacement uses the public lemma:

```lean
have hsource (hist : List (List Bool)) : (ρ.P.next x y tape hist).length ≤ B :=
  d.next_length_le y B hbound tape hist
```

The proposed import is acyclic: the existing `ProofTransfers` closure does not contain
`RealPrefixBounds`. This replacement is a proposed repair, not a newly compiled patch.
The complete final REPORT and the supplied checkpoint REPORTs do not identify this
particular re-proof; the reported overlap between `next_length_le` and the owned
`ProverBounded.seqRep` is a different relation. This finding concerns an earlier helper
within this PR, not a lemma predating the issue base. The brief explicitly includes
duplication inside parts of proofs. A scan of top-level statements cannot detect this
local `have`.

The evidence ZIP contains the compared fragments, their commit provenance, the relevant
REPORT passages, and the import-closure check. The gate remains HOLD until G39-01 is resolved.

## Proof assessment

The author-hosted [PS10 notes](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf),
Theorem 175.1, pp. 175–176, and
[Goldreich's chapter draft](https://www.wisdom.weizmann.ac.il/~oded/PSBookFrag/part4N.pdf),
§4.3.4, Lemma 4.3.9, support the wrapped-verifier and sequential-simulation route. The
fixed move budget, even padding, bounded honest-prover messages, and strict-PPT simulator
convention are explicit adaptations of the frozen interface.

1. **Normalization and simulator.** `PhaseView` validates the known common input,
   auxiliary input, empty wrapper tape, and canonical encoding. It normalizes to the
   prescribed bounded real-message slots and uses empty slots on malformed outputs.
   `normalizePhaseMsgs_viewV` proves the real-view fixed point. The simulator therefore
   needs no hypothesis about the shape of simulated outputs. `SimulatorMachine` realizes
   the recursion through the existing counted-loop host; its orbit-size bound is
   polynomial on every tape.

2. **Uniformity and quantifier order.** `exists_phaseSimulator` constructs `SQ` using
   `NUPPT.ofPolyTimeUniform` and explicitly proves `SQ.Uniform`. Its coin polynomial is
   `V.coins + Q*S.coins`: one verifier tape and independent simulator blocks. Both transfer
   theorems choose `S` and `SQ` before any auxiliary-input bound or distinguisher. The
   nonuniform metadata is used only in `exists_phaseReduction`, not in `SQ`.

3. **Computational ZK.** The encoded-prefix envelope is
   `Q(n)*π.rounds.eval n*(2*B(n)+2)`. `ComputationalPhaseBound` uses the larger polynomial
   `2*n + 2*Lz(n) + 2*V.coinLen n + 2*Q(n) + envelope + 8` for packed metadata and hence for
   the wrapped auxiliary input. Finite metadata covers all bounded prefixes. The selector
   maximizes witness-indexed suprema before the negligible bound is requested, so no
   witness-length bound or attained witness maximum is assumed. The reduction stores no
   witness and performs no reachability or witness-validity test. The continuation drift
   and endpoint readers give advantage at most `Q(n)*|ε(n)|`; the existing
   `Negligible.polyExpr_mul` proves negligibility. `ZK.seqRep` instantiates this result
   without changing its hypotheses.

4. **Statistical ZK.** A raw one-phase comparison is mapped through the same normalizer
   and padded-prefix update. Averaging, randomized postprocessing, and the triangle
   inequality give **exactly `Q(n)*δ(n)`**. The real and simulator endpoint equivalences
   add no error. Nonnegativity of `δ(n)` is obtained from the one-phase comparison on a
   witnessed input. `StatZK.seqRep` directly instantiates the padded-prover theorem.

5. **Interactive-proof cases.** Completeness transfers phase by phase, using exact coin
   slices and the all-phase verdict. `InteractiveProof.seqRep` preserves its original
   negligible rejection bound through phase zero. For explicit error, the fixed-prefix
   prover and verifier-prefix independence show that each fresh phase accepts with
   probability at most `s(n)`, after any earlier prefix. The adaptive product theorem
   gives **`s(n)^Q(n)`**, without assuming independence of the adaptive success events.
   `sound_nonneg` supplies the sign needed for multiplication. The efficient-prover case
   additionally supplies the repeated prover's uniform efficiency, message bound, and
   completeness for every valid witness. The unused `hQ` in the explicit-error theorem
   is already disclosed.

6. **Boundary cases.** The recursion and endpoint equations include zero phases for ZK
   and statistical ZK, with empty history and zero accumulated error. The explicit-error
   engine permits zero phases with bound one; the frozen proof-system statements retain
   their positive-phase hypothesis. Zero rounds, either first mover, and odd round counts
   are covered by the padded phase contracts. Honest prover fillers are empty; cheating
   verifier filler messages are not restricted. The delivered sketches describe this
   route. Only the statistical target's sketch changed from the issue base.

## Integrity, scope, and native evidence

| Check | Result |
|---|---|
| Pack integrity | All **24** outer manifest entries verify. Verification: **147** entries; nested review evidence: **1106**; LE-doc: **58**; integration: **1248**. Each extracted ZIP file set equals its manifest plus `SHA256SUMS`. The 25 pack files, including the manifest, match pinned exchange Git blobs. |
| Source provenance | All **185** source-closure files match the head's Git blobs. The complete **1319-file Lean tree** at the head was also checked against Git blobs for duplication searches. All 41 changed-file inventory hashes agree. The diff reproduces: **41 paths, +6652/−14**. |
| Frozen statements | Replayed declaration comparison gives **196 ADDED, 0 CHANGED, 0 REMOVED**. All **27 + 35** pre-existing declaration headers, their order, definition bodies, and statement prose are preserved. The frozen scanner returns **0 differences**. The two pre-existing files are also unchanged between the issue base and PR base. |
| S-01 | `StatZK_iff` is precisely the existing predicate's simulator property by `Iff.rfl`, with no attribute. The approved code matches apart from blank-line placement; LE-doc supplies its formula. No other pre-existing `Defs` declaration changes. |
| LE-doc | **23 files, 81 changed docstrings**; deleting doc comments leaves byte-identical code. All inserted formulas agree with their declarations/readers or the documented handwritten structure/recursion descriptions. No target docstring changes in LE-doc. |
| Build records | Independently checked hashes and recounted both diagnostic forms in **303 review build logs** and **715 integration records**, representing **694 effective modules**. All effective results have rc 0 and zero errors. All **694 effective source hashes** match the disjoint published PR changes over the pinned records commit; all **41 unit source hashes** equal the audited head. This comparison does not depend on fetching the maintainer's unpublished scratch tree. |
| Rule 10 | Rechecked **154 head probes and 8 base probes**: raw log hashes, executed probe hashes, removal of instrumentation back to the exact source revision, and install/EOF masks. The **10 omitted coe probes** are byte-identical to their executed strict counterparts, accounting for all **164 effective head cells**. |
| Rule-10 failures | Only `Defs` fails: **10 errors in each variant at both base and head**, in the same six unchanged declarations: `perfectZK_zeroRounds`, `AbortRetry.attempt_poly`, `AbortRetry.exists_retrySimulator`, `AbortRetry.statClose_retry`, `PerfectZKAbort.statZK`, and `negligible_inv_pow_sqrt_div`. **New failing declarations: 0.** `StatZK_iff` passes. |
| Controls and explicit reads | Recounted all **24** strict/coe control logs. The supplied paired-control interpretations and explicit-read attribution agree with the inspected readers and proof bodies. Coe-A remains canonical. No additional Rule-10 violation was found. |
| Axioms and admissions | Parsed all **414** stored-constant census rows: the axiom union is exactly `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`. The five targets and reported consumers print only standard axioms. The supplied admission census changes **23 → 18**, removing exactly the five targets. |
| Ownership and sweep | The ownership table assigns each of the **39 helpers** one owner: lead 5, a 10, b 9, c 15. The supplied lead-tagged, same-module slot records cover the **276** final-sweep checks; the recorded maximum is three slots. This establishes consistency of the provenance records, not independent authentication of who operated the host. |
| Style and API | Largest file: **992 lines**; maximum width: **100**. No new global simp attribute. The Prop-valued `Nonempty` instance is disclosed. Public definitions have readers; the long proofs have sketches. The supplied lint line-set comparison introduces no new failure. |

The combined integration build is accepted as evidence for the final merged state, as
dispatched. Merge order, **#324 last**, and any maintainer rebuild for the second merge
remain merge conditions and are not audit findings.

## Documentation and duplication disposition

The **11 truncated formulas** were assessed individually under G37-03. They are not
automatic failures: their own accompanying prose states the omitted property.

| File | Declarations | Assessment |
|---|---|---|
| `ComputationalHybrid` | `prefix_distAdv_joint_le`, `distAdv_view_endpoints` | The prose states the joint `Q(n)*ε` bound and the exact advantage identity between actual and typed endpoints. |
| `ComputationalReduction` | `reductionData_fields`, `exists_continuationSampler`, `exists_phaseReduction` | The prose supplies all five fields, the sampler's activation equation, and the continued distinguisher computation with its separate coin portions. |
| `ContinuationProbability` | `continuationProb`, `continuationProb_eq`, `continuationProb_real`, `phaseGap`, `phaseGap_eq` | The prose identifies acceptance of the remaining canonical suffix under the full typed table, its real-step expectation identity, and the raw real/simulator gap through the randomized continuation. These descriptions state properties rather than merely referring to a definition. |
| `EndpointSampling` | `simulate_eq_simPrefix` | The prose states the raw split-tape to typed-prefix output identity. |

The strict-PPT note is accurate and visible in the module's deviations and in
`PerfectZKAbort.seqRep`. PS10's sequential-composition sketch explicitly discusses expected
running time. Goldreich's Definition 4.3.1 uses a strict polynomial-time simulator with
abort and the exact conditional law. The code starts from that strict aborting premise
and uses bounded independent retries; it does not claim a general conversion from
expected-time perfect simulation preserving an exact conditional law.

The broader duplication search covered the hybrid arguments, statistical postprocessing,
coin-block readers, encodings, and history accesses. The code directly uses
`abs_sub_le_sum_hybrids`, the published `StatClose` laws, `FunFamily.blocks`, the existing
coin equivalences, `CommitmentLemmas.encodeMsgs_append`, and
`CommitmentLemmas.length_encodeMsgs_le`. The disclosed Yao encoding equality and repeated
block specializations are not reopened. A supplementary statement comparison, including
binder renaming, found no hits for the 175 new theorems against 20,640 other parsed
theorems. G39-01 was found by inspecting an inline proof, outside that scan's coverage.
No other undisclosed duplication was identified; these searches are not a decision
procedure for semantic equivalence.

**Notation (source notation):** `π`, `ρ`: original and repeated protocols; `R`: witness
relation; `n = |x|`; `Q`, `B`, `Lz`: phase, message, and auxiliary-input bound polynomials;
`S`, `SQ`: phase and repeated simulators; `δ`, `s`: statistical and soundness errors;
`ε`: negligible comparison bound.

## ===== briefs/pass-shelat-ch5-8/gates/39-seq-zk/landing-r1/PROVENANCE.txt =====

#327 (seq-zk) LE-gate39 (Gate 39 G39-01, major: inline re-proof of the PR's own public next_length_le), maintainer job, 2026-11-16 UTC
$SP = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad. Paths below are relative to this directory.
Rules: python3 -I; Lean 4.25.0 (PATH=$HOME/.elan/bin:$PATH); one Lean process of ours at a time, only on $SP/dl-oleans (another
  job's lean on dl-oleans-2 was seen running during the job and not touched); builds only through scripts/lean_check_tree.sh
  (worktree copy byte-equal to /home/user/tcslib/scripts/lean_check_tree.sh) via tools-used/review/runner.py (G26-N1, both
  error forms); probes via tools-used/runner_full.py (lean -DmaxErrors=0, no -o); no lake command; no cache get; nothing pushed;
  no rebase; no commit or branch in /home/user/tcslib (only `git fetch`, `git worktree` and unreferenced `git commit-tree
  --no-gpg-sign` scratch objects); the shared .lake/packages not modified.
Method and tools: records briefs/pass-shelat-ch5-8/maintainer/int-all-open-2026-11-16/int-all-open-evidence.zip (SHA-256
  4f8cb3746353c968be8d8b6d11407c03d5a96969b61029644a014db9577606fe), extracted into a fresh directory: 1248/1248 OK against
  evidence-SHA256SUMS, path set exact, SHA256SUMS = evidence-SHA256SUMS. tools-used/: unmodified copies of its tools-used/ (incl.
  review/{runner,downorder,snapshot,buildsum,sorrycensus,treecheck}.py, buildset, permod, refunion2, soloenv, soloverify,
  tipcensus, treecheck_ml, restoreplan, runner_full, and the Mathlib overlay method mloverlay.sh + mathlibextra.sh). Statement
  and Rule 10 tools, unmodified, from records gates/37-sc-compose/landing-r1/gate37-le-evidence.zip (382c09f4...; 202 files, OK
  against its evidence-SHA256SUMS): decls2.py, docaudit.py, doconly.py, doconly_sg.py, frozencheck_lib.py, touched.py,
  upclosure.py, rule10_b.sh, review/{mkcollect,mkseals_ab,mkseals_coe,sealsum,sealtable,ctlcheck2,touched}.py,
  NmCollect.template.lean, archived-gate10-tools/; and from records fills/seq-zk/final-r1/review-evidence.zip (f9c39479...,
  1106/1106 OK, SHA256SUMS = evidence-SHA256SUMS): mkctl_seqzk.py, mkcensus_seqzk.py (all byte-equal across the three sources
  where present). New: legate39_checks.py (header/strip/insertion check of the edited file), backupq.py (pre-build backup),
  restore_g39.sh (restore_derand.sh's steps with this job's paths + restoreplan.py --delete).

coordinator update during the job (before any build): #326 (derand, c27005d6) was merged; the job used the NEW tip.
  tip = origin/cryptography/pass-shelat-ch2-4 after `git fetch` = 0542dd9210ccdb844ad125cd95f8488c9f553153 ("Records: #326
  merged"; it contains #313, #318, #319, #323, #326; c27005d6 is an ancestor). The earlier tip b87d148b was NOT used for any build.
  PR heads by `git ls-remote` at the time: #324 4bd2d80bfb58fab5243c66c9f1a697a30b533756, #326 c27005d6, #327 bd19c433 (parent).

olean tree $SP/dl-oleans: pre tree/snapshot-pre.txt: 1230 files, 0 empty dirs, SHA-256
  457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f = the required value.

landing (landing/): land/pass-shelat-seq-zk in its worktree $SP/wt-land-seq-zk (sparse, briefs/ excluded, .lake/packages linked).
  parent bd19c433a4cf3d4027ffc891d7d3c06e927e9dfa (= refs/pull/327/head). NEW HEAD a94ba750b2f21ea5f2c3e58bc7959ad5ac9de871, tree
  3efe62af6b414655aefa9506e3e63baedea33ae5; author = committer = Claude <noreply@anthropic.com>, SSH-signed by the environment
  default (gpgsig present; `%G?` prints N only for lack of an allowedSignersFile); subject "seq-zk landing edit LE-gate39: hsource
  from the public next_length_le (G39-01)", message landing/commit-msg.txt (both trailers); patch landing/patch/, diff
  landing/le-gate39.diff (1 file, +5/-5), landing/commits.txt. Worktree clean at the new head.
edit (TCSlib/Cryptography/Composability/SequentialZK/RealPrefixBounds.lean):
  - import: `import TCSlib.Cryptography.Composability.SequentialZK.ProofTransfers` after the two existing imports. Acyclic:
    ProofTransfers' local closure (135 modules, from source) does not contain RealPrefixBounds; it is a subset of RealPrefixBounds'
    closure (143), so the import adds exactly one module (ProofTransfers) to it.
  - proof: in PaddedProverSpec.realPrefix_bounds the local
      have hsource (hist : List (List Bool)) : (ρ.P.next x y tape hist).length ≤ B := by
        rw [d.next y tape hist]; dsimp only; split_ifs <;> first | exact hbound _ _ | exact Nat.zero_le B
    is now
      have hsource (hist : List (List Bool)) : (ρ.P.next x y tape hist).length ≤ B :=
        d.next_length_le y B hbound tape hist
    (exactly the requested replacement; it compiled first time).
  - docstring: the proof sketch describes this step ("Each repeated-prover reply is either an original bounded message or an
    empty filler, by the specification's public reply equation."); one pure insertion right after it: " This is the\npublic
    theorem `next_length_le`." (the line break keeps widths <= 100; max width 94; file 101 lines before and after).
checks (statements/, checks/):
  - statements/decls2-vs-parent.tsv (decls2.py, parent bd19c433 vs head): EMPTY; decls2.err empty.
  - checks/legate39-checks.txt (legate39_checks.py): (1) frozencheck_lib.compare: 1 declaration, realPrefix_bounds header
    byte-identical, statement prose identical, no MISSING/ORDER; (2) doc/module comments stripped: 7 code lines changed, exactly
    the import line and the hsource proof (4 lines -> 2); (3) the one changed docstring is a pure insertion of one contiguous
    chunk (verified: removing it gives the parent text). checks/doconly-sg.txt: code-identical False (expected: the proof and
    import changed), docstring counts 2 -> 2, 1 changed.
  - statements/touched-vs-parent.tsv (touched.py): 1 CHANGED, realPrefix_bounds (lines 41-100); touched-after.json for sealsum.
lint (lint/): scripts/campaign_style_lint.py TCSlib/Cryptography --check8b at a94ba750: 92 FAIL / 101 WARN; FAIL/WARN line set
  identical to the LE-doc lint at bd19c433 (lint/linediff-Cryptography-bd19c433-vs-a94ba750.txt empty).

(a) #327 alone on the tip (merged second, after #326):
  scratch merge (landing/merge-tree-a-tip-x-327.txt): `git merge-tree --write-tree --messages` tip 0542dd92 x a94ba750: rc 0, no
    conflict message, tree daac61401cafe36fb036598e1bb33cdf6d5e743e; commit 4cd422c76c73cdcf4270b94a9c4ca9fcecd0fd9a (unsigned, no
    ref, fixed date). Tree = tip + #327's 41 files exactly (39 A, 2 M), every blob = a94ba750's (landing/solo-a-vs-tip-name-status.txt).
  worktree $SP/wt-g39 (sparse, non-cone /* !/briefs/, .lake/packages linked), detached at 4cd422c7.
  order-a/: downorder.py vs eff2dcd0 (the snapshot's base): changed 153, down 679, order 1317, 377 Mathlib roots. buildset.py,
    seeds RealPrefixBounds + audits/garg-ch1-3/Checks + audits/pass-shelat/Checks: down-seed 8 (RealPrefixBounds,
    ComputationalTransfer, SequentialZK facade, ThreeColoring, Composability, root TCSlib, both audits Checks), build set 679 =
    down-seed + 671 base-delta modules the tree needs (the snapshot predates #313/#318/#319/#323/#326/#327), excluded 0; queue
    imports-first (asserted per edge). (With RealPrefixBounds alone as seed, order-a/rpb-only/: down-seed 6, the audits Checks
    are not downstream of it; they were added as seeds as required.)
  Mathlib overlay (build-mathlib-extra/): mloverlay.sh: 3346 symlinks in dl-oleans/Mathlib; mathlibextra.sh compiled
    Mathlib/Analysis/SpecialFunctions/Pow/NthRootLemmas (pinned mathlib 029db123, source b371bf48...) with plain lean -o: rc 0,
    olean c0a9cff04c6707edac6980cf4d3c3cc8116ab8843e9ddfb82f6688aee8e0f54c = the derand review's / int-all-open's.
  backups: tools-used/backupq.py before each build: 561 snapshot oleans copied to $SP/dl-g39-backup (hash-verified,
    tree/backed-up.txt), 133 new modules listed (tree/new-oleans.txt; 118 for (a), 15 for (b)).
  build-a/ (runner.py, rc 0): 679/679 rc 0; errors 0 (`error:` 0, `error(` 0, per-module.tsv / permod.out, every log hash = its
    record); substring "error" 0; 59 sorry warnings (all in admitted non-PR modules, plus ComposeSecurity 3 and Yao 2, tip
    admissions); 420 warnings; 6167 s module time, 05:32-07:15 UTC. RealPrefixBounds: rc 0, 0 errors, 0 sorry, 0 warnings, 2.2 s.
    The 8 down-seed modules all rc 0, 0 errors both forms, 0 sorry; warnings only SequentialZK 1 (the disclosed unused hQ).
  refcmp (build-a/refunion.txt, refunion2.py vs int-all-open's combined records, its 4 solo builds and its 24 reference runs;
    build-a/refs-args.txt): 678 of 679 byte-identical (source and olean) to at least one reference; the one without is
    RealPrefixBounds (new source). SliceReduction: same-source different-olean vs int-313-323-324/sc-garble, SAME vs
    int-all-open/gate36 (the known LE-gate36 import-closure change).
  admissions (admissions/): tipcensus.py at the tip 0542dd92: 202; at 4cd422c7: 197 = 202 - 5 (SequentialZK 5 -> 0), every new
    seq-zk module 0; per-module identical to int-all-open's combined census 639d16d9 except ComposeSecurity (3 here: #324 is not
    in (a)) and #324's new modules (absent). RealPrefixBounds has no sorry/admit token.

(b) the final combined tree (tip, which now contains #326, + #327 a94ba750 + #324 4bd2d80b; merging #326 again is a no-op):
  landing/merge-tree-b-SA-x-324.txt: 4cd422c7 x 4bd2d80b: rc 0, no conflict, tree 129810e45fa842afa19219804e6cde7fe64cee7c;
    commit c51cf08dcf588ca6bbd79670462df5b8bb0ecb92 = THE NEW FINAL COMBINED TREE. Alternative order (tip x #324, then x
    a94ba750) gives the same tree 129810e4; merging c27005d6 into c51cf08d again gives 129810e4 (no-op). All clean.
  checks/combined-old-639d16d9-vs-new-c51cf08d-code.txt: outside briefs/, the new combined tree differs from int-all-open's
    final combined tree 639d16d9 only in RealPrefixBounds.lean (and the plan .md files changed on the records tip).
  rebuild set (order-b/; downorder at c51cf08d vs eff2dcd0: changed 169, down 694, order 1332): down(RealPrefixBounds +
    both audits Checks) 8 + down(#324's 16 files) 19 = 26 (shared: root TCSlib). #324's downstream is included because the (a)
    tree held the tip state for those modules.
  environment (build-b/env/, soloenv.py at c51cf08d with int-all-open's admissions/records-final.jsonl): every module of the
    rebuild set's import closure outside it (1306) has the combined build's source (asserted) and ALREADY held the combined
    build's recorded olean: OK 1306, RESTORE 0, MISSING 0 (the (a) build reproduced them byte for byte).
  build-b/build/ (runner.py at c51cf08d, queue build-b/env/queue.txt, rc 0): 26/26 rc 0, errors 0 (`error:` 0, `error(` 0),
    substring 0, sorry 0, warnings 1 (SequentialZK, unused hQ), 376 s, 07:16-07:22 UTC. build-b/verify.txt (soloverify.py):
    RESULT OK; RealPrefixBounds byte-identical to build-a; the other 25 byte-identical to int-all-open's combined build (and 9 of
    them also to build-a).
  admissions: admissions/census-b-c51cf08d.txt: 194, per module identical to int-all-open's merge-census-639d16d9
    (census-b-vs-int-all-open-639d16d9.diff empty): no admission added or removed beyond the targets already removed.
  tree check (tree/tree-check-combined.txt, treecheck_ml.py, order-b/order.txt 1332 modules, admissions/records-final-b.jsonl =
    int-all-open records-final + build-a + build-b): every module rc 0 at the c51cf08d source, every olean = its record, none
    missing, no stray olean, no empty dir: RESULT OK (4710 files = 1332 + 31 PFR + 3347 Mathlib overlay entries, attributed).

Rule 10 (rule10/; at c51cf08d in $SP/wt-g39; owner RealPrefixBounds.lean; probes under G39Probe/, removed afterwards,
  rule10/probe-files-in-worktree.txt; runner_full.py writes no olean, every run lean -DmaxErrors=0):
  - collector G39Probe/CollectHead (mkcollect.py; probe-runs/ rc 0, 0 errors; 2508 CAT lines).
  - seals (rule10_b.sh: mkseals_ab.py strict A, B with SEAL_EVAL=1; mkseals_coe.py coe A, B): seals-{A,B,coe-A,coe-B}.tsv: all 4
    probes rc 0, 0 errors, 0 failing declarations, install and EOF records present; requests strict A 1875 / B 1876, coe A 1874 /
    B 1875 (terms 12, stored 1).
  - paired controls (mkctl_seqzk.py: PolyExpr.eval, the FinDist CoeFun instance, ZK/ZK_iff, StatZK/StatZK_iff,
    Composability.prefixProver/prefixProver_coins; Protocol.seqRep not selected): coe 4 probes, 7 sealed negatives, each failing
    exactly once, readers 0, unsealed 0: ctlcheck-coe.log ALL_OK True. strict 4 probes, 9 sealed negatives each failing exactly
    once; ALL_OK False only because ctlCoeReader also fails once under the strict seal (harness effect, as in the seq-zk review,
    sc-compose review and LE-gate37; rule10/controls-strict-attribution.txt). Unsealed controls all pass.
axioms (axioms/; Axioms.lean.txt run as G39Probe/Axioms at c51cf08d with runner_full.py: rc 0, 0 errors, 0 warnings; source
  removed afterwards): the five targets ZK.seqRep, StatZK.seqRep, InteractiveProof.seqRep, InteractiveProofErr.seqRep,
  EfficientProverProofErr.seqRep, and PerfectZK.seqRep, PerfectZKAbort.seqRep, colSeq_efficientProverProof_zk,
  negligible_colSeqSound, StatZK_iff, zk_of_padded_spec, realPrefix_bounds: [propext, Classical.choice, Quot.sound];
  next_length_le: [propext] (axioms/probe-runs/mods/G39Probe_Axioms.log).

## Restore (run by the maintainer, 2026-11-16T07:39:34Z)
finish1.sh: backup hash failures 0; restored 561; deleted new oleans 133; Mathlib overlay removed (3346 symlinks, 1 file c0a9cff0); restoreplan: extra 0, changed 0, missing 0, 17 emptied dirs deleted; post snapshot sha256 457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f: SNAPSHOT EQUAL. Probe files hashed (14) and removed.

## ===== briefs/pass-shelat-ch5-8/maintainer/int-all-open-2026-11-16/PROVENANCE.txt =====

Combined integration build of every open PR (#318, #319, #323, #324, #326, #327) on the records tip, with each PR's solo coverage,
maintainer job, 2026-11-16 UTC
$SP = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad. Paths below are relative to this directory.
Rules: python3 -I throughout; Lean 4.25.0 (PATH=$HOME/.elan/bin:$PATH; `lean --version` 4.25.0 cdd38ac5); one Lean process at a time
  (ours: another job's lean on dl-oleans-2 was seen and not touched), only scripts/lean_check_tree.sh (worktree copy byte-equal to
  /home/user/tcslib/scripts/lean_check_tree.sh, checks/runner-equal.txt) through tools-used/review/runner.py (the G26-N1 runner,
  `^\S+\.lean:\d+:\d+: error[:(]`) with TCSLIB_OLEANS=$SP/dl-oleans; probes through tools-used/runner_full.py (lean
  -DmaxErrors=0, no -o); no lake command; nothing pushed; no commit or branch in /home/user/tcslib (only `git fetch`, `git worktree`
  and unreferenced `git commit-tree --no-gpg-sign` objects). The shared .lake/packages was not modified.
Method and tools: the int-313-323-324 evidence (records gates/37-sc-compose/integration/int-313-323-324-evidence.zip, SHA-256
  3917cc1e6136b8562a05e86f005c1505c5f2c2b943a0a9fdc1de3a8aac19df69), extracted into a fresh directory: 527/527 OK against
  evidence-SHA256SUMS, path set exact, SHA256SUMS = evidence-SHA256SUMS. tools-used/: unmodified copies of its tools-used/
  (review/{runner,downorder,snapshot,buildsum,sorrycensus,treecheck}.py; buildset, bothdown, bothdown3, bothdown317, refunion,
  refcmp, permod, restoreplan, tipcensus) and, from the derand review (fills/derand/final-r1/review-evidence.zip, ef0776d5...,
  1317/1317 OK), mloverlay.sh, mathlibextra.sh, restore_derand.sh, and runner_full.py (gate36-le / sc-compose copy). New:
  bothdownN.py (bothdown3.py for N seed sets), refunion2.py (refunion.py, every reference run kept separately, rc-0 records only,
  module x reference matrix), treecheck_ml.py (treecheck.py with the Mathlib overlay attributed and symlinks not followed),
  solocheck.py, soloenv.py, solorun.sh, soloverify.py (solo coverage, below).

trial merge (landing/):
  records tip b0ebd475eb0b4131449bce58462f168f27eee17b (= origin/cryptography/pass-shelat-ch2-4 after `git fetch`, unchanged
    during the job; its code equals 654323f2's: #313 merged).
  heads (refs/pull/N/head by `git ls-remote` at the start): #318 b0bad23ae611983e3323460bb8c564da90ad6e8c, #319
    47daa90792e96b93510384adbab9f6e492ccef3a, #323 8c3f3e3fe2912784f680c10f8c478d2eeeeb7f6a, #324 a6eaebd7 (then the LE-gate37
    head 4bd2d80bfb58fab5243c66c9f1a697a30b533756, see ../gate37-le/), #326 = the derand LE-doc head
    c27005d67298f79c785a4e8ac1648da0a67d3614, #327 = the seq-zk LE-doc head bd19c433a4cf3d4027ffc891d7d3c06e927e9dfa (both from
    ../ledoc-derand-seqzk/). Merge bases (checks/pr-bases.txt): #318/#319/#327 05d26fe5, #323 1321b9cb, #324/#326 6ce4658d; each
    base's code differs from the tip's only in #313's 5 Learning files.
  `git merge-tree --write-tree --messages`, each rc 0 with no conflict message (landing/merge-tree-*.txt, scratch-chain.txt):
    S1 tip x #318 bd129bfa -> d882e2c4; S2 x #319 66b34363 -> 6564ad82; S3 x #323 a7988cd9 -> d30ead70; S4 x #324(a6eaebd7)
    35e9289d -> 6cfe68ac; S5 x #326 0c1134e5 -> 0f43c1e8; S6 x #327 tree 225d0f05fa5f6d03356438e91d2daa8ac2414fca, commit
    e2e26b9e71747c03f71b26d684b99f943442d4d7 (the tree of the main build). Then, at the coordinator's request during the build,
    S7 = S6 x #324 LE-gate37 4bd2d80b: tree 3fb05ea062395caf069c09643a8caf751d3ad6da, commit
    639d16d943d4bb4777c77ae8614cd8c2ed91f1bd = THE FINAL COMBINED TREE (S7a with the superseded b4900559 kept in the chain
    file). Other orders (landing/merge-tree-alt.txt): two orders give 225d0f05 with the old #324 head, three orders give 3fb05ea0
    with the new one, all clean. All scratch commits: author = committer = Claude <noreply@anthropic.com>, date fixed
    2026-11-16T00:00:00Z, unsigned, no ref, never pushed (also the solo merges below).
  checks/: tip-vs-combined-name-status.txt (at 639d16d9) = the union of checks/pr*-name-status.txt: 97 .lean files (79 A, 18 M;
    +17309/-300), #318 7, #319 4, #323 14, #324 16, #326 15, #327 41; shared paths 0 (checks/shared-paths.txt); every blob at the
    combined tree equals its PR head's (checks/combined-blobs-vs-heads.txt: 7/7, 4/4, 14/14, 16/16, 15/15, 41/41).
worktree $SP/wt-int-all (sparse, non-cone /* !/briefs/, .lake/packages -> /home/user/tcslib/.lake/packages): at S6 for the build,
  S7 for the #324 rebuild, the axioms probe, Rule 10 of ../gate37-le/, tree check and lint, then at each solo merge. Clean at the
  end (checks/worktree-status.txt: only the ignored .lake/); removed (`git worktree remove --force`), pruned.

build set (order/ at S6; order-final/ at S7, identical sets and queue):
  downorder.py vs eff2dcd0 (the olean snapshot's base): changed 169 = 72 base-delta modules since eff2dcd0 (order/basedelta-
  modules.txt: int-313-323-324's 68 + #313's 5, minus SeedMajority, which #326 also changes) + the 97 PR modules; down 694; order
  1332 (imports-first); 377 Mathlib roots. buildset.py (seeds = the 97): down-seed 661 (incl. root TCSlib, audits/garg-ch1-3/Checks,
  audits/pass-shelat/Checks), build set 694 = down-seed + 33 base-delta modules they need, excluded 0; build-queue.txt 694 modules,
  imports-first (asserted per edge). (The expected "700 or more": 694.)
  downstream counts (order-final/bothdown.out, bothdownN.py at S7): #318 10, #319 68, #323 322, #324 19, #326 585, #327 65,
  union 661. Downstream of both, per pair: 318&319 1, 318&323 6, 318&324 3, 318&326 10, 318&327 1, 319&323 37, 319&324 1,
  319&326 57, 319&327 2, 323&324 16, 323&326 273, 323&327 41, 324&326 16, 324&327 1, 326&327 52; modules downstream of 1/2/3/4/6 PRs:
  353/214/90/3/1 (only root TCSlib is downstream of all six; order-final/merge-multi.tsv). With the old #324 head (order/
  bothdown.out) 323&324 was 3 and #323's downstream 309: G37-01's CommitmentLemmas import makes ComposeSecurity/Machines (hence
  the 16 #324 modules) downstream of #323's DAGCircuit.

Mathlib overlay (build-mathlib-extra/; the derand reviewer's method, derand-r1 PROVENANCE "environment"): the shared pinned Mathlib
  build lacks Mathlib/Analysis/SpecialFunctions/Pow/NthRootLemmas.olean, imported by Derandomization/RootSchedule (the only
  Mathlib module imported by the queue and missing). tools-used/mloverlay.sh put 3346 symlinks to the pinned Mathlib oleans in
  dl-oleans/Mathlib (our tree only; nothing under /home/user/tcslib written) and mathlibextra.sh compiled that one module from the
  pinned source (mathlib 029db123, source SHA-256 b371bf48...) with plain `lean -o`: rc 0, olean c0a9cff04c67... = the derand
  review's. Removed at restore.

olean tree $SP/dl-oleans:
  pre: tree/snapshot-pre.txt (snapshot.py): 1230 files, 0 empty dirs, SHA-256
    457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f = the required value (byte-equal to int-313-323-324's
    snapshot-post). Before the build the 561 base oleans the queue overwrites were copied aside ($SP/dl-intall-backup;
    tree/backed-up.txt with hashes = snapshot-pre; copies verified 561/561) and the 133 new ones listed (tree/new-oleans.txt).

build (build/; runner.py $SP/wt-int-all order/build-queue.txt $SP/dl-oleans build, at S6; runner rc 0):
  build/summary.txt: 694/694 rc 0; errors 0 (G26-N1); substring "error" 0; 56 sorry warnings; 417 warnings; 5650 s of module time,
  2026-11-16T01:42:54 - 03:17:06 UTC (1 h 34 min wall), max RSS 4.52 GB; slowest DetMod 1447 s, CookLevin/Hardness 329 s,
  NARMProb 214 s, audits/pass-shelat/Checks 136 s, SequentialZK 117 s. build/per-module.tsv (permod.py): per module rc,
  err_colon (`error:`), err_paren (`error(`), combined, error_substr, sorry, warnings: totals error: 0, error( 0; every log hash =
  its record. The 97 PR modules: rc 0, 0 errors both forms; sorry 0 except Yao 2 (yaoHybrid_polyTime, yaoHybrid_simulators:
  tip admissions, sc-yao); warnings 20 = IterateFind 12 (derand E1 copy of the base linter lines, disclosed), Classes 2 (lines
  586/1302, unchanged code), Universal 1 (unused hc, canonizer), SequentialZK 1 (unused hQ, disclosed), SliceParser 1 and
  NestedBounds 1 (SG-F06), Yao 2 (the sorries). Other sorry warnings only in admitted non-PR modules (TQBF 21, RAMSimulation/
  Classes 9, UniqueGames 8, Hierarchy 4, WordSize 3, MaxCutAlgorithm 2, Simulation 2, NTimeDiagonalizer 2, NonUniform 1,
  NDNormalForm 1, Savitch 1).
  build-324/ (after LE-gate37; worktree at S7; order-final/rebuild324-queue.txt = down(#324) at S7 + both audits Checks, 21
    modules, imports-first): 21/21 rc 0, 0 errors both forms, 0 sorry, 0 warnings, 204 s (03:24:21-03:27:44). build-324-attempt1/:
    the same queue at the superseded b4900559 merge: Runs.lean 5 errors (the splitCoins name clash, ../gate37-le/), stopped there.
  Records of the final tree: admissions/records-final.jsonl = int-317's base records (admissions/base-records-from-int-317.jsonl,
    = int-313-323-324's and gate36-le's copy) + build/ + build-324/; build/results-final.jsonl = build/ + build-324/.

admissions (admissions/):
  tip (tip-census-b0ebd475.txt, tipcensus.py over the base records, int-313-323-324, gate36-le build/rerun/trial, sc-garble and
    sc-compose builds; 1253 modules matched, 0 disagreeing; 34 modules outside root TCSlib's closure have no record, as at gate36):
    215 sorry warnings tree-wide (= gate36-le's 654323f2 census, per module identical).
  combined (merge-census-639d16d9.txt, tipcensus.py over records-final.jsonl at S7; 1332 modules matched): 194.
  tip-count.txt / tip-vs-merge-census.diff: 194 = 215 - 2 (sc-ot: ObliviousTransfer 2->0) - 1 (canonizer: Universal 1->0) - 7
    (sc-garble: SpecialEncryptionSecurity 3->0, Garbling 1->0, GarblingSecurity 1->0, SpecialEncryptionMulti 1->0, Yao 3->2) - 3
    (sc-compose: ComposeSecurity 3->0) - 3 (derand: SeedMajority 2->0, Derandomization 1->0) - 5 (seq-zk: SequentialZK 5->0);
    no other count changes; every new PR module 0.
  pr-modules-sorry.txt: the 97 PR modules have 0 sorry warnings and 0 `sorry`/`admit` tokens in code except Yao (2 warnings,
    2 code tokens = the two tip admissions; 3 with its docstring's mention). No PR module gained an admission.

axioms (axioms/; AxiomsAll.lean.txt run as IntProbe/AxiomsAll in the worktree at S7 with runner_full.py: rc 0, 0 errors,
  0 warnings, no olean written; source removed afterwards; probe-runs/, AxiomsAll.log, axioms-summary.txt): 67 #print axioms =
  each unit's census / integration list: sc-ot (gate34-le census: otProtocol_polyTime, otProtocol_simulators, otProtocol_hbcSecure
  and 8 OT helpers), canonizer (int-319 census: exists_canonizerExp, exists_polyCanonizer, ... 11), learning/sc-garble/sc-compose
  (int-313-323-324 probe: 2 + 8 + 4), derand (review census: the 3 targets, E1-E3, inBPP_iff, ... 18), seq-zk (review census: the
  5 targets, PerfectZK.seqRep, PerfectZKAbort.seqRep, ... 11), plus yaoHybrid_hbcSecure and yaoProtocol_hbcSecure. Result: 63
  [propext, Classical.choice, Quot.sound]; Turing.oneTapeFormat_serialize_decode [propext, Quot.sound] (as in int-319);
  OT.pairSndD_nil' no axioms; yaoHybrid_hbcSecure and yaoProtocol_hbcSecure [propext, sorryAx, Classical.choice, Quot.sound].
  Dependency trace (the sc-garble review's DepTrace logic, unchanged): the admitted declarations (direct sorryAx) in the closure of
  yaoProtocol_hbcSecure (18264 constants) are exactly yaoHybrid_polyTime and yaoHybrid_simulators (sc-yao); of
  yaoHybrid_hbcSecure (9418) the same two. otProtocol_polyTime / otProtocol_simulators and hbcSecure_compose are gone.

refcmp (build/; refunion2.py over build/results-final.jsonl):
  references: 24 build runs (rc-0 records), copied to build/refs/jsonl/ and each byte-equal to its entry in its evidence's
    SHA256SUMS (refs/refs-hash-check.txt 24/24); the zips (refs/refs-zip-check.txt) extracted into fresh directories and checked
    against their records evidence-SHA256SUMS, path sets exact: fills/sc-ot/final-r1/review-evidence.zip (aa3bcfc3..., 810/810;
    build, build-r2, build-r3, edit-build, lereuse-trial), fills/canonizer/final-r1 (2b52982f..., 838/838; build, build-r3),
    fills/sc-garble/final-r1 (5a121c02..., 1200/1200; build, edit-build, base-build), fills/sc-compose/final-r1 (c11ce8bb...,
    850/850; build, edit-build, base-build), fills/derand/final-r1 (ef0776d5..., 1317/1317; build, build-retry, base-build),
    fills/seq-zk/final-r1 (f9c39479..., 1106/1106; build), gates/34-sc-ot/landing-r1/gate34-le (145d5574..., 459/459; build),
    gates/35-canonizer/integration/int-319 (830395f8..., 299/299; build, build-combined), gates/36-sc-garble/landing-r1/gate36-le
    (f77628dd..., 628/628; build, build-rerun, trial/build), gates/37-sc-compose/integration/int-313-323-324 (3917cc1e..., 527/527;
    build). (Only the Rule 10 seal/control runs were deleted from the extracts after the check, to save disk.)
  build/refunion.txt, refunion-matrix.tsv, refunion-per-ref.txt: 660 of 694 modules byte-identical in source and olean to at least
    one reference.
  - NO reference with the same source: 34 modules = exactly the files edited in this job (build/edited-this-job.txt; each has
    references with a different source): derand LE-doc Classes; seq-zk LE-doc Defs + 22 SequentialZK files; LE-gate37's 10
    ComposeSecurity files. Their sources are new here (docstrings are stored in the olean). No module has no reference at all.
  - same source, different olean: 1, SpecialEncryptionMulti/SliceReduction vs int-313-323-324 and the sc-garble review; it is
    byte-identical to gate36-le build and build-rerun. Explained by gate36-le: LE-gate36 (#323's head 8c3f3e3f) edited SliceParser's
    imports (+BlockEncryptor, +FromPRG), changing SliceReduction's import closure; gate36's rerun showed the new olean deterministic.
  - build/both-modules-refmatch.txt: of the 308 modules downstream of two or more PRs, 278 are byte-identical to a reference; the
    other 30 are among the 34 edited files. Root TCSlib, both audits Checks, SecureComputation and Randomness match 11-18 references.
tree check (tree/tree-check-merge.txt; treecheck_ml.py, order-final/order.txt 1332 modules, records-final.jsonl, rev S7, run after
  the probes; tree/snapshot-merge.txt): every module rc 0 at the S7 source, every olean = its record, none missing, no stray olean,
  no empty dir: RESULT OK (4710 files = 1332 + 31 PFR + the 3347 Mathlib overlay entries, attributed).
lint (lint/; campaign_style_lint.py --check8b in the worktree at S7 and in a git-archive export of the tip, removed afterwards):
  Cryptography 92 FAIL / 101 WARN at the tip and at the merge; linediff-Cryptography-tip-vs-combined.txt: only ZeroKnowledge/Defs'
  check-8 list loses StatZK (#327's StatZK_iff). Complexity 25/391 at the tip, 25/390 at the merge; the line set changes only by
  the disclosed ones: DAGCircuit check-8 loses IsFaninTwo (#323), DTIME's check-8 WARN removed (#326 E3), Classes 1403 -> 1415
  lines and check-8 loses InBPP (#326 SR-01), CodeFormat check-8 loses oneTapeFormat and CodeSimulator 9126 -> 9133 lines and
  loses oneTapeMachineFormat (#319). No new FAIL. No PR file has a new FAIL.

solo coverage (solo/; summary.txt): each PR alone on the tip, scratch merges solo/solo-merges.txt (all rc 0, clean; tree = tip + the
  PR's files exactly): #318 bae29c92, #319 5e5a4f6c, #323 4ebf36f9, #324 bcf945e8 (old head), #326 af5c9d44, #327 e3d2c3e4.
  solocheck.py compares every module of the solo merge's build order (pr*/order/, downorder + buildset at the solo merge) with the
  full record set its own integration build left; differ.txt = source differs or no record; rebuild.txt = their downstream.
  - #319 (own build int-319 at 05d26fe5, records-B = base + job A + build/): differ = #313's 5 Learning modules; rebuild 7 =
    Learning x5, Randomness, root TCSlib (the expected "Randomness and TCSlib" plus #313's own 5).
  - #318 (own build gate34-le at 05d26fe5): the same 7.
  - #323 (own build gate36-le, LE-gate36 on 654323f2, = the current code): 0 differ, 0 to rebuild.
  - #326 (own build the derand review at d34fbf09 / 6ce4658d, logs/records-head.jsonl): differ Classes (LE-doc) + Learning x5;
    rebuild 89 (Classes' downstream and Learning's).
  - #327 (own build the seq-zk review at 05d26fe5): differ the 23 LE-doc files + Learning x5; rebuild 63.
  - #324: its own builds (int-313-323-324, gate36 trial) predate LE-gate37; not re-checked alone (see below).
  Separate tip+PR checks were run for all of #318, #319, #326, #327 (sets 7, 7, 89, 63), after the combined analysis, in the same
  tree (solorun.sh): soloenv.py takes, for every module of the import closure of the rebuild set outside it, the olean its own
  build recorded (same source and import-closure sources, so it is the expected one) and checks the tree: OK if present, RESTORE
  from the base-snapshot backup if that is it, MISSING otherwise (rebuilt first, must reproduce the recorded hash); then the queue
  (missing + set, imports-first) is built at the solo merge. soloverify.py, pr*/verify.txt:
    #319: env OK 1230 / RESTORE 13 / MISSING 2 (tip SeedMajority, tip SpecialEncryptionMulti: rebuilt, = recorded hashes); 9/9 rc 0,
      0 errors, 125 s; the 7 byte-identical to references (Learning to gate36-le/int-313-323-324/combined; Randomness, TCSlib to
      14-19 builds). RESULT OK.
    #318: OK 1246 / RESTORE 3 / MISSING 1 (ObliviousTransfer, = recorded); 8/8 rc 0, 127 s; RESULT OK.
    #327: OK 1227 / RESTORE 1; 63/63 rc 0, 0 errors, 0 sorry, 548 s; every module byte-identical to a reference (the 23 LE-doc
      modules to the combined build). RESULT OK.
    #326: OK 1170 / RESTORE 2 / MISSING 2 (DTIME, IterateFind, = recorded); 91/91 rc 0, 0 errors, 0 sorry, 871 s; every module
      byte-identical to a reference. RESULT OK.
  So each of #318, #319, #323, #326, #327 is covered merging first onto the tip, and the combined tree covers all six together.
  #324 at 4bd2d80b alone on the tip was not built: its rebuild set is small (down(#324) = 19 modules), but its environment needs
  tip-state oleans for the #323/#326-downstream modules those 19 import, and no record of such a state exists (the closest
  builds include #323 or the old #324), so it would mean a ~280-module solo build. The combined build covers it with all PRs; its
  old head was covered alone-with-#323 by gate36's trial.

restore (restore/): the 561 backups copied back, each hash checked (restore-log.txt: 561 restored, 0 failed); the Mathlib overlay
  deleted (3346 symlinks + the NthRootLemmas olean c0a9cff0..., logged); restoreplan.py --delete against tree/snapshot-pre.txt:
  133 extra files (= tree/new-oleans.txt; restore/extra-vs-new-oleans.txt empty) deleted with 17 emptied directories
  (deleted-dirs.txt); 0 changed, 0 missing. The solo checks' restores and rebuilds are covered by the same backups (changed 0).
  post: tree/snapshot-post.txt: 1230 files, 0 empty dirs, SHA-256 457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f,
  byte-identical to tree/snapshot-pre.txt. Backups removed afterwards.
cleanup: the worktree removed and pruned; the backup directory, the tip export and the reference extracts removed after zipping.
SHA256SUMS: every file here except itself (paths without "./"); ../int-all-open-evidence.zip holds exactly these paths plus SHA256SUMS.

## ===== briefs/pass-shelat-ch5-8/gates/39-seq-zk/pack.md =====

# Gate 39 · Sequential repetition preserves zero knowledge and interactive proofs (`seq-zk`, [PS10, Theorem 175.1])

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #327](https://github.com/Shilun-Allan-Li/tcslib/pull/327) at
  `bd19c433a4cf3d4027ffc891d7d3c06e927e9dfa` (branch `land/pass-shelat-seq-zk`, tree
  `cc520026f83524433328359af759084d23cabd0e`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `05d26fe5b41fcb9426ec220d877d03264b9c8e8c` (the merge base).
  - The fill was issued on `107f1e8c218733eac12d6b9bee6fece441271317`. The 41 PR paths are byte-identical at the
    issue base and at `05d26fe5` (`pack-checks/rebase.txt`). The Lean delta between them (29 files) is covered by the
    review's build.
  - The records tip is now `c2f6adeb3f3de2a21352a57e64c6a11a79cc220e`. Since `05d26fe5` it has merged #313
    (learning) and, on 2026-11-16, #318 (sc-ot), #319 (canonizer) and #323 (sc-garble).
  - `pr.diff.txt` is `git diff origin/cryptography/pass-shelat-ch2-4...bd19c433`, which equals `05d26fe5..bd19c433`
    byte for byte (41 paths, 6652 insertions, 14 deletions).
  - **Open PRs and the tip.** `git merge-tree --write-tree` of the head with the tip, #324 and #326 (and with the merged
    heads of #318, #319, #323) is clean in each case, and no path is shared. The combined build of all open PRs covers
    the merged state (question 9). **Pending merge condition** (not an audit item): the merge order, #324 last.
- **Commits:** 7 (`pack-checks/rebase.txt`), all committed by Claude and SSH-signed.
  - The Codex worker's 6 commits, made by a lead and three sub-agents on Seyoon's Mac. The author, Seyoon Ragavan,
    is kept. They were applied with `git am` with the delivered committer data; the 6 worker hashes reproduce
    unsigned.
  - They were rebased onto `05d26fe5`: `git range-diff 107f1e8c..d842dc8f 05d26fe5..e9b5ea47` is 6/6 `=`. At
    `e9b5ea47` the 41 files are byte-identical to the worker's `src/` (exchange `a6be22fa`).
  - Landing edit **LE-doc** `bd19c433a4cf3d4027ffc891d7d3c06e927e9dfa` (S-02): formula docstrings for 81 new public
    declarations, docstrings only. Author and committer Claude.
- **Scope:** a **proof audit** of five admitted, frozen statements in `Composability/SequentialZK.lean`
  ([PS10, §7.2.1, Theorem 175.1]; [Gol01, §4.3.4]):
  - `ZK.seqRep` (:866);
  - `StatZK.seqRep` (:884), with error `Q · δ`;
  - `InteractiveProof.seqRep` (:930);
  - `InteractiveProofErr.seqRep` (:958), with soundness error `s^Q`;
  - `EfficientProverProofErr.seqRep` (:976).

  They passed the prong C statement phase, Gate 03 (rulings G3-3, G3-4, G3-7d) and Gate 06, and are frozen. Their
  proved consumers `PerfectZK.seqRep`, `PerfectZKAbort.seqRep` and `Composability/ThreeColoring.lean` (Theorem 124.1)
  become standard with them.
- **Brief:** `fills/seq-zk/issued-r1/brief.md` on the records branch (SHA-256 `d8b9feec…`), in `verification.zip`.
  It sets four checkpoints (the IP case; the error and efficient-prover cases; StatZK; ZK) and the owned file plus
  `SequentialZK/`. It also sets the frozen-statement rule, the edge cases, Rule 10 (projection coercions and
  `PolyExpr.eval` as notation, coe seals canonical), the docstring and sketch rules, the G26-N1 error count and the
  evidence-completeness rule.

Lean paths below are under `TCSlib/Cryptography/`; `SQ/` is `Composability/SequentialZK/`.

## What changed

41 Lean files (`source-head.json`; every line at most 100 characters; the largest file is the owned one, 990 → 992
lines):
- the owned `Composability/SequentialZK.lean`: the five proofs; 12 new declarations (execution readers such as
  `exec_boundary_lengths` and `seqRep_outV_eq`, `seqRep_complete`, `seqRep_sound_first`, `seqProver_efficient`,
  `seqVerifier_efficient`, `ProverBounded.seqRep`, `seqRep_proverSpec`, `seqRep_verifierSpec`); the imports and the
  module docstring;
- **39 new helpers under `SQ/`** (60–370 lines each). They cover the phase structure, the repeated verifier and its
  soundness, the continuation probability and endpoint sampling, the prefix and suffix laws, the normalized simulator
  `S_Q` (`SQ/Normalization*`, `SQ/SuffixMachine`, `SQ/SimulatorMachine`), the statistical recursion and the
  computational hybrid with its non-uniform phase reduction (`SQ/Computational*`, `SQ/WrappedVerifier`);
- `ZeroKnowledge/Defs.lean`, **+11 lines**: the `Iff.rfl` reader `StatZK_iff` (S-01) with its formula docstring.

**The proof** (review § *content*; the worker's REPORT): each target is a short instantiation.
- `ZK.seqRep` is `SequentialZK.zk_of_padded_spec h hB Q (fun x => π.seqRep_proverSpec Q x)`. It uses the wrapped
  verifier `V*` and the normalized simulator `S_Q` (one verifier tape, `Q(|x|)` calls of `S` on fresh coin blocks,
  canonical normalization and fallback). It applies `ZK π R` at the enlarged auxiliary bound `Lz'`, with a non-uniform
  phase reduction that fixes a maximizing phase and bounded prefix as advice. The sum of the `Q(n)` gaps is
  `Q(n) · ε(n)`.
- `StatZK.seqRep` is `statZK_of_padded_spec`: the conditional hybrids and the triangle inequality give exactly
  `Q(|x|) · δ(|x|)`.
- `InteractiveProof.seqRep` uses `seqVerifier_efficient`, `PaddedProverSpec.complete` and soundness from phase 0
  (`seqRep_sound_first`).
- `InteractiveProofErr.seqRep` uses `(seqRep_verifierSpec Q x).sound`: soundness `s^Q` by conditioning on the prefix
  and induction on the phases. `hQ` is unused, which is disclosed.
- `EfficientProverProofErr.seqRep` adds `seqProver_efficient`, `ProverBounded.seqRep` and `seqRep_complete`.

**Statements** (`evidence/statements/`, re-checked in `pack-checks/headers.txt`, `shared.txt` and `decls2-*.tsv`):
- decls2 from the issue base and from `05d26fe5` to the head gives **196 ADDED, 0 CHANGED, 0 REMOVED**; 0 rows for
  LE-doc.
- The frozen check (`landing/frozen-check.txt`) takes `SequentialZK` from 27 to 39 declarations and `Defs` from 35 to
  36. It finds 0 header, prose or definition-body differences; the control (one header character of `ZK.seqRep`)
  gives exactly 1.
- `touched`: 5 CHANGED (the targets), 13 ADDED in existing files (12 owned, plus `StatZK_iff`), 190 in new files and
  57 UNCHANGED.
- Re-checked from git objects:
  - the 27 + 35 pre-existing headers and every definition block are identical, in order;
  - the five targets' headers are byte-identical and their bodies have no `sorry`;
  - **of the five target docstrings, only `StatZK.seqRep`'s differs from the issue base** (one sketch hunk). The other
    four are the statement-phase sketches, unchanged. LE-doc touched none of the five.

## Rulings and records in force

1. **S-01, confirmed by Seyoon (2026-11-16):** `StatZK_iff` (`Iff.rfl`) in the frozen `ZeroKnowledge/Defs.lean`, as
   approved in the worker's session (`worker/evidence/scope-request/`). Its added lines equal the approved patch apart
   from the position of one blank line (`pack-checks/shared.txt`); LE-doc adds its formula.
2. **The worker was Codex**, on Seyoon's Mac, as a lead with up to three sub-agents and a host-wide 3-slot Lean cap
   (Seyoon, 2026-11-15; `records/…/fills/codex-host-2026-11-15/`). The brief's header line "Worker Claude" is from
   issue.
3. **Rule 10 notation** (as the brief):
   - `PolyExpr.eval` (Q1, the user, 2026-11-07): seal A exempts it and is canonical;
   - reducible abbreviations;
   - projection coercions such as `FinDist`'s `⟨FinDist.prob⟩` (Seyoon, 2026-11-14). **coe-A is canonical**.
4. **The deviations in the owned file's module docstring** were fixed at the statement phase: filler moves;
   **strict-PPT simulators and bounded abort retries** (ruling G02-#4, D8); bounded prover messages (`ProverBounded`,
   G3-3); at least one phase for soundness.
5. **LE-doc (the maintainer's landing edit, S-02): docstrings only.**
   - For 81 of the review's 88 NO-FORMULA rows, it adds the declaration's own Lean conclusion (60 rows), or for a
     `def`/`abbrev` its `_eq` reader's (13), as a backticked formula at the end of the statement prose. 8 are written by
     hand (`statements/seq-zk-overrides.tsv` in `landing-ledoc/`).
   - The other 7 rows are the **5 frozen targets**, whose statement prose the brief freezes (left as is, as the
     sc-compose LE-doc did), and `ProverBounded.seqRep` and `zk_of_padded_spec`, which already state their conclusion.
   - **11 conclusions longer than 240 characters are cut at a space and end in " …"** (the sc-compose LE-doc rule;
     question 7).
6. **Uniformity (the uniformity audit of 2026-11-16, findings `7d398d16`, in `verification.zip`).** The convention is
   uniform simulators, with adversaries and distinguishers non-uniform.
   - #327's `exists_phaseSimulator` builds `SQ` with `SQ.Uniform` explicitly, by `NUPPT.ofPolyTimeUniform`
     (`SQ/SimulatorMachine.lean:310–344`). The audit grades it **OK**: lifted verifiers use auxiliary data, and the
     phase and repeated simulators are explicitly uniform; no new uniformity defect.
   - Its other findings (DW-1 to DW-3) concern HBC and non-malleability definitions and are deferred.
7. **The facade-completeness lint baseline (#305):** 92 FAIL / 101 WARN (Cryptography), 25 / 391 (Complexity).

## What is frozen

- **The five targets' statements and statement prose**, and every pre-existing declaration of `SequentialZK.lean` and
  `ZeroKnowledge/Defs.lean` (header bytes, order, whole definitions), in particular the construction (`seqProver`,
  `seqVerifier`, `seqRep`) and its readers, and `ZK`, `StatZK`, `PerfectZK`, `PerfectZKAbort` and `AbortRetry`.
- **Every other file**, in particular `ZeroKnowledge/Interaction.lean`, `InteractiveProofs.lean`,
  `Composability/ThreeColoring.lean`, `Asymptotic/*` and `Games/*`.
- **The landing edit:** LE-doc, 81 docstrings.

## Questions for the audit

**1. Correctness against [PS10, Theorem 175.1] and [Gol01, §4.3.4]**
- **`ZK.seqRep`:**
  - Is the normalized simulator `S_Q` a **uniform strict PPT**, with one verifier tape, `Q(|x|)` calls of `S` on
    fresh coin blocks, and canonical normalization and fallback?
  - Are the auxiliary-input bounds `Lz` and `Lz'` right?
  - Do the hybrids `H_i` (first `i` phases real) have the endpoints `H_Q` = real and `H_0` = `S_Q`?
  - Is the non-uniform phase reduction sound: advice of polynomial length, no witness, no trust in simulated
    metadata?
  - Is the total `Q(n) · ε(n)` negligible?
- **`StatZK.seqRep`:** is the error exactly `Q(|x|) · δ(|x|)`, by the triangle inequality over the `Q(|x|)` hybrids?
- **The proof-system cases:**
  - completeness from `seqRep_exec_phase`;
  - soundness from phase 0 (`InteractiveProof`), and `s^Q` by conditioning on the prefix and induction, with the
    prover that hard-wires the prefix (`InteractiveProofErr`);
  - the efficiency of `V_Q` and `P_Q` from the iterate hosts and `coinBlock` slices.
- **The brief's edge cases:** `k = 0` rounds; `Q(n) = 0` for the ZK statements (empty history; the proof-system
  statements assume `1 ≤ Q(n)`); odd `k`; `verifierFirst` true and false; a cheating verifier's filler replies;
  malformed or non-canonical simulator outputs; the honest prover's `[]` fillers.
- Do the sketches describe the delivered proof? Only `StatZK.seqRep`'s was rewritten; the other four are the
  statement-phase sketches.

**2. Frozen-statement integrity: 196 / 0 / 0**
- Are the five targets' headers, the 27 + 35 pre-existing declarations and their statement prose byte-identical
  (`landing/frozen-check.txt`, `pack-checks/headers.txt`)? Is decls2 **196 ADDED / 0 CHANGED / 0 REMOVED** from both
  bases?

**3. `StatZK_iff` (S-01)**
- `ZeroKnowledge/Defs.lean` gains exactly `StatZK_iff` (`:191`), +11/−0, lines inserted only (`pack-checks/shared.txt`).
  The other 35 declarations are unchanged.
- Is it exactly `StatZK`'s body by `Iff.rfl`, with a formula docstring and no attribute? The Rule-10 controls show the
  sealed `Iff.rfl` form of `StatZK` failing and `StatZK_iff` passing: the reader is needed and sufficient.

**4. The multi-agent provenance**
- `evidence/logs/ownership-check.txt`: the REPORT's table gives each of the 39 helpers exactly one owner: the lead 5,
  `seq-zk-a` 10, `seq-zk-b` 9, `seq-zk-c` 15. `SequentialZK.lean` and `Defs` are the lead's. The worker's
  `evidence/subagents/seq-zk-{a,b,c}` exist in the delivery on the exchange (`a6be22fa`, `inbox/fills/seq-zk/`; 221, 173
  and 222 files).
- `evidence/logs/final-sweep-attribution.txt`: all 276 final-sweep checks match a slot acquisition of the same module
  with the lead's tag. `evidence/logs/slots-check.txt`: never above 3 slots.
- The table is consistent with the delivered file set; it is not independently verifiable beyond the records. Is the
  provenance adequate?

**5. Rule 10: only the pre-existing `Defs` failures?**
- The seals cover the 41 files over the full closure, at the head and the base files at the base, in four variants,
  run with `-DmaxErrors=0`, with install and EOF records in every row (`pack-checks/rule10.txt`; 154 head probes, 10
  coe probes byte-identical to strict not re-run).
- **The only failing probe is `ZeroKnowledge/Defs`:** 10 errors in A and in B, strict and coe, at the head **and at
  the base**. They are the same 6 declarations, whose headers and docstrings are unchanged:
  - `perfectZK_zeroRounds` (:294);
  - `AbortRetry.attempt_poly` (:395), `AbortRetry.exists_retrySimulator` (:444) and `AbortRetry.statClose_retry` (:516);
  - `PerfectZKAbort.statZK` (:604);
  - `negligible_inv_pow_sqrt_div` (:682).

  `SequentialZK` and every helper give 0. **New failing declarations: 0**; `StatZK_iff` passes.
- **The controls** (`evidence/logs/ctlcheck.log` ALL_OK). Coe has 10 probes and 9 sealed negatives; strict has 14 and
  15, and `ctlCoeReader` fails in the 6 strict sealed probes (the harness effect). Rows: `PolyExpr.eval`, the
  `FinDist` CoeFun instance, `ZK`/`ZK_iff`, `StatZK`/`StatZK_iff` and `Composability.prefixProver`/`prefixProver_coins`.
- **The explicit-unfold scan:** 1245 items. The 13 "foreign" are local `let F`/`let g` bindings resolved by name to
  globals (`evidence/logs/scan-foreign-attribution.txt`): 0 real foreign definitions.
- Does any proof read a foreign definition other than through a published reader (`Interaction`'s `exec`, `viewV`,
  `withV`, `encodeMsgs`; `InteractiveProofs`; `Defs`; the `NUPPT` layer; one helper's definitions read from another)?

**6. Duplication (recent gates graded undisclosed re-proofs of public lemmas as majors)**
- Does any new declaration, or any part of a proof, duplicate a public TCSlib or Mathlib lemma, or copy a private
  one, beyond the worker's overlap disclosures (`worker-report.md`; the checkpoint REPORTs in `worker/`)? **Anything
  undisclosed is a major.** The review's spot checks (`evidence/logs/duplication-review.txt`) found nothing undisclosed.
- Search in particular:
  - the hybrid argument (`exists_hybrid_gap`, the multicopy lemmas, sc-compose's `abs_chain_le`) against the
    statistical and computational hybrids;
  - prefix and suffix laws against `Games/*`;
  - `StatClose`/`distAdv_le_of_statClose` uses;
  - coin blocks (`coinBlock`, `FunFamily.blocks`);
  - the history encoding: the PR uses the public `CommitmentLemmas.encodeMsgs_append` and `length_encodeMsgs_le`
    directly (`pack-checks/dupscan.txt` B);
  - `getD` readings (two `List.getD_eq_getElem?_getD` rewrites, no DL-47-class copy).
- Mechanical aids (`pack-checks/dupscan.txt`): a statement scan (binders and type, whitespace-normalised) of the 175
  new theorems has **0 hits**, both against the files the tip, #324 and #326 changed and against all 20686 theorems
  of the other 1278 TCSlib files. No new name is declared in a file another comparator changed
  (`pack-checks/namecheck.txt`).

**7. The docstrings: S-02 and the strict-PPT note**
- **LE-doc (ruling 5):** `e9b5ea47..bd19c433` changes 23 files, +222/−61. Every file is identical with doc comments
  deleted, 81 docstrings change, docstring counts are unchanged, and the max width is 100 (`pack-checks/lecheck.txt`;
  `landing-ledoc/`: `landing/seq-zk-le-doc.diff`, `seq-zk-le-doc-plan.tsv`, `checks/seq-zk-doconly.txt`).
  - Does each of the 81 formulas state what its declaration says, in Lean argument order?
  - The post-edit docaudit (`statements/seq-zk-post/docaudit.tsv` there) gives 190 OK and 2 LABEL. It has 1 NO-DOC,
    `prefixProver`, whose docstring precedes `@[simps]` (a tool artifact). Its 9 NO-FORMULA are the 5 frozen targets,
    the 2 already stated, and 2 Prop formulas without a relation symbol.
- **The 11 cut formulas.** Each ends in " …`", where the conclusion passed 240 characters. They are in
  `SQ/ComputationalHybrid` (125, 175), `SQ/ComputationalReduction` (62, 189, 253), `SQ/ContinuationProbability` (89,
  103, 171, 321, 337) and `SQ/EndpointSampling` (216), for:
  - `prefix_distAdv_joint_le`, `distAdv_view_endpoints`;
  - `reductionData_fields`, `exists_continuationSampler`, `exists_phaseReduction`;
  - `continuationProb`, `continuationProb_eq`, `continuationProb_real`, `phaseGap`, `phaseGap_eq`;
  - `simulate_eq_simPrefix`.

  Gate 37 round 1 graded this rule's label-and-prefix readers as incomplete (G37-03, minor). For #324 the maintainer
  completed all 20 in LE-gate37. Grade these by the same standard: a truncation is acceptable only where the
  docstring's own prose states the property.
- **The strict-PPT versus expected-PPT note.** The module docstring's *Deviations* states:
  - zero-knowledge is taken with **strict-PPT** simulators and bounded abort retries (G02-#4, D8);
  - `PerfectZKAbort`'s premise is [Gol01, Definition 4.3.1]'s strict-PPT aborting formulation;
  - [PS10]'s expected-polynomial-time wording "is a separate source convention".

  `PerfectZKAbort.seqRep`'s docstring repeats this as a *Source distinction*. Is the note accurate against [PS10,
  Theorem 175.1] and [Gol01, §4.3.4], and is it placed where a reader of the targets will see it?
- Does every proof of 15 lines or more carry a `**Proof sketch.**` (`evidence/statements/sketchaudit.txt`: 48 such
  proofs, all sketched)? A misstated formula or sketch is a minor.
- Does every new public `def` land with its `_eq` reader (lint check 8)? There is no `@[simp]` (only
  `@[simps (config := {isSimp := false})]`). The one instance is the Prop-valued `PhaseMetadata.instNonempty` (S-03).

**8. Simulator uniformity**
- Is `S_Q` uniform as constructed (`SQ.Uniform` by `NUPPT.ofPolyTimeUniform`, `SQ/SimulatorMachine.lean:310–344`), with
  its advice-free coins `CV + Q · S.coins`, and is the bad-prefix advice confined to the computational reduction, never
  to `S_Q` (ruling 6)?

**9. The merge interaction**
- `git merge-tree --write-tree bd19c433 <x>` is clean, and no path is shared (`pack-checks/mergetrees.txt`):

  | `<x>` | head | merged tree | downstream of both (`pack-checks/downstream.txt`) |
  |---|---|---|---|
  | the tip | `c2f6adeb` | `217fd194` | 41 (#323's `DAGCircuit` is in the unit closure) |
  | #324 (sc-compose) | `4bd2d80b` | `ae43ea76` | root `TCSlib` |
  | #326 (derand) | `c27005d6` | `029cdc65` | 52 (`ClassP/DTIME`, `Build/IterateFind` are in the unit closure) |
  | #318 (merged) | `b0bad23a` | `8ddcf527` | root `TCSlib` |
  | #319 (merged) | `47daa907` | `47f23ea6` | 2: root `TCSlib`, `audits/pass-shelat/Checks` |
  | #323 (merged) | `8c3f3e3f` | `295f67b2` | 41 |

  None of the 202 new short names is declared in a file another comparator changed.
- **The integration evidence** (`integration/`, `4f8cb374…`): the combined build of the records tip of that time
  `b0ebd475` plus all six PRs, with #327 at this head, as tree `3fb05ea0`. **694/694 rc 0**, 0 errors in both forms.
  - Re-checked (`pack-checks/integration.txt`): merging #324, #326 and #327 onto the current tip, in all six orders,
    gives `TCSlib` and `audits` trees equal to the built tree, and all 694 built sources equal their blobs there.
  - Its solo check of tip + #327 (on `b0ebd475`) rebuilt the 63 modules downstream of the 23 LE-doc files and #313's
    Learning files: 63/63 rc 0, 0 errors, 0 sorry, every module byte-identical to a reference.
  - **LE-doc's build is the combined build:** the review build ran at `e9b5ea47`, and 280 of its 303 built sources
    equal the head's; the 23 that differ are LE-doc's files (`pack-checks/srcequality.txt`).
- **Pending merge condition (not an audit item):** the merge order, **#324 last**. The intermediate states with the
  current tip are not built as such; any rebuild for whichever of #326 and #327 merges second is the maintainer's, if
  required.

## Known dispositions (not findings)

- **S-01** (minor, confirmed), **S-02** (fixed by LE-doc, with question 7's cut formulas open), **S-03** (info): the
  disclosed unused `hQ` warning (`SequentialZK` 1 warning); the Prop-valued instance `PhaseMetadata.instNonempty`;
  tool artifacts.
- **Admissions:** 23 → 18; only `SequentialZK` (5 → 0) differs; outside the order only `SeedMajority` (#312) and
  `SpecialEncryptionMulti` (#311), base delta (`evidence/logs/sorry-census.txt`).
- **The build:** 303/303 rc 0, 0 errors in both forms, 1670 s, through root `TCSlib` and both `audits/*/Checks`
  (`landing/root-checks.jsonl`). Whole-tree check: 1288 modules, OK. The olean tree was restored to `457ba704…`.
- **Axioms:** the five targets, `PerfectZK.seqRep`, `PerfectZKAbort.seqRep`, `Composability.colSeq_efficientProverProof_zk`,
  `negligible_colSeqSound`, `StatZK_iff` and `zk_of_padded_spec` print `[propext, Classical.choice, Quot.sound]`
  (`landing/census-head.log`). The census has 414 stored constants (= the worker's), the axiom union is standard, and
  there is no `sorryAx`. Against the base: 107 → 414, removed 0, type-changed 0, axioms-changed 7.
- **Lint:** 92/101 at the head and the tip; the only changed line is `Defs`' check-8 list losing `StatZK`
  (`StatZK_iff`). Complexity 25/391, identical.
- **The LE-doc PROVENANCE says +219/−61;** git and its own `landing/seq-zk-le-doc.stat` give **+222/−61**.
- **The PR description** predates LE-doc: it names the head `e9b5ea47` and announces "88 declarations"
  (`pr-description.md`, fetched on 2026-11-16). The maintainer updates it before #327 is marked ready.
- **The review's "target sketches rewritten"** is true of `StatZK.seqRep` only (question 1).

## Evidence

- **`review.md`:** the maintainer's delivery review, verdict ACCEPT (S-01–S-03).
- **`verification.zip`:** every file the review cites and the pack uses, as byte-identical originals. `SHA256SUMS` lists
  every other entry, and `PROVENANCE.txt` gives each source.
  - `review-evidence.zip` (`fills/seq-zk/final-r1/`, SHA-256 `f9c39479…`) and `review-evidence-SHA256SUMS`, its
    manifest: 1107 entries, exactly the 1106 manifest paths plus `SHA256SUMS`; every hash verifies;
  - `landing/PROVENANCE.txt`: the review's PROVENANCE (= the ZIP's);
  - `records/`: the issue package `fills/seq-zk/issued-r1/` and, at records
    `9760e69425babb1bc9ee8b085e227ae3faf6dac5` (local, unpushed: the tip `c2f6adeb` plus the Gate 37 round-2 and Gate 38 records), the duplication ledger, the decision log, the deferred-work register,
    the Codex host addendum and dispatch, and the uniformity audit's findings;
  - `evidence/`: byte copies of the review-evidence entries the pack cites;
  - `worker/`: byte copies from the exchange delivery `a6be22fa` (`inbox/fills/seq-zk/`): `COMMITS.tsv`, the
    scope request (`StatZK-iff.patch`, `request-and-answer.md`) and the five checkpoint REPORTs. The first three are
    each equal to the review's `logs/delivery-extracts/` copy;
  - `pack-checks/`: the re-checks for this pack, from git objects only (no Lean), with their scripts.
- **The worker's own evidence:** on the exchange at `a6be22fa`, under `inbox/fills/seq-zk/` (manifests 3073/3073 and
  3023/3023 in the review; 1.12 GB, verified there without extraction).
- **`landing/`:** byte copies of evidence-ZIP entries: `root-checks.jsonl` (= `build/results.jsonl`),
  `build-summary.txt` (= `logs/build-summary.txt`), `census-head.log` (= `probe-runs/mods/PlProbe_CensusHead.log`),
  `frozen-check.txt` (= `statements/frozen-check.txt`) and `tree-check-head.txt`.
- **`landing-ledoc/`:** LE-doc for derand (F-04) and seq-zk (S-02): `ledoc-derand-seqzk-evidence.zip` (`977bbe89…`),
  its manifest and PROVENANCE.
- **`integration/`:** the combined build of all open PRs (`4f8cb374…`), its manifest and PROVENANCE.
- **`worker-report.md`:** the worker's final `REPORT.md`, at exchange `a6be22fa`.
- **`pr-description.md`:** the PR #327 description as fetched from the GitHub REST API on 2026-11-16 (`.body`, raw).
- **`pr.diff.txt`:** `git diff` from the base to the head (41 paths, 6652 insertions, 14 deletions).
- **`source-head.json`:** the head hashes, line counts and over-width counts of the 41 changed files.
- **`sources.zip`:** the source closure at the head of every changed module, 185 files.
- **The bundle** adds, at the head, `Composability/SequentialZK.lean`, `ZeroKnowledge/Defs.lean` and
  `SQ/SimulatorMachine.lean`.

## Findings delivery

Return `gate39-seq-zk-findings.md` as a Markdown file in this chat. If you have several evidence files, return a ZIP.
The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish the frozen statement, or a scope
  violation.
- **major:** a changed frozen statement, a forbidden read in a touched declaration not covered by the rulings (the 10
  pre-existing `Defs` failures are not new), an undisclosed copied private lemma or undisclosed re-proof of a public
  one, or necessary evidence that cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring or proof sketch.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.

## ===== briefs/pass-shelat-ch5-8/duplication-ledger.md =====

# Duplication ledger: Pass–shelat ch. 5–8

Accepted debt, each entry acknowledged by the user, with its scheduled resolution.

| ID | New declaration (where) | Existing copy (where) | Status | Resolution |
|---|---|---|---|---|
| DL-1 | `TCSlib.InformationTheory.abs_probTrue_sub_le_statDist` (#183, `InformationTheory/Extractors.lean`, for `main`) | `TCSlib.Cryptography.abs_sum_sub_le_statDist` (`Foundations/Experiments.lean`, Garg's concrete layer, on `cryptography/pass-shelat-ch2-4` and `cryptography/garg-ch1-3`; not on `main`) | accepted 2026-11-04 (user) | No copy on `main` today. When the concrete layer lands on `main`, its lemma becomes a one-line corollary of #183's (a `Finset` test is the `Bool` test `(· ∈ T)`) or is removed. Gate 01 pack erratum E1. |

## Inherited with ch. 2–4 (found 2026-11-05; acknowledged 2026-11-05 by the user: clean up now)

This campaign owns ch. 2–4 since 2026-11-05 (plan, decision log). These duplicates predate it.

| ID | Copies (where) | Status | Proposed resolution |
|---|---|---|---|
| DL-2 | XOR of encodings is the encoding of the Boolean sum, `zipWith xor (ofFn a) (ofFn b) = ofFn (a + b)`, stated three times: `TCSlib.Cryptography.zipWith_xor_ofFn_add` (`Asymptotic/HardCoreLoops.lean`; it was `zipWith_xor_ofFn`, renamed by the base repair to end the name clash with `Encryption.lean`'s different lemma); `TCSlib.Cryptography.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessage.lean`); `TCSlib.Cryptography.MultiMsg.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessageLemmas.lean`) | accepted; scheduled now | Keep the most upstream copy (`HardCoreLoops`) and point the other two at it, in a ch. 2–4 cleanup PR. |
| DL-3 | `pairEncode a b ≠ []`, stated four times: `GGMRed.pairEncode_ne_nil` (`Asymptotic/GGMReduction.lean`), `GI.pairEncode_ne_nil` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean`), `ColMachines.pairEncode_ne_nil` (`ZeroKnowledge/ThreeColoring/Machines.lean`); and, on `main`, `Complexity.pairEncode_ne_nil` (`Complexity/SpaceComplexity/Logspace/InputAccess.lean`), the copy that made the merge's ambiguity | accepted; scheduled now | `main` is merged (#186). Remove the three local copies in favour of `Complexity.pairEncode_ne_nil`, in the same cleanup PR. |
| DL-4 | Not a copy (different carriers): the sampler-based `StatClose` (`Asymptotic/Sampling.lean`) and `main`'s `EpsClose` on `FinDist` (`InformationTheory/Extractors.lean`, #183) | accepted; scheduled now | A bridge lemma, in the same cleanup PR (user, 2026-11-05). |
| DL-5 | Not a copy (different carriers; found by the gate 02 round 2 review): `Games.guessAdv_eq_half_advantage` and `Games.accept_guessGame` (games) and the concrete layer's `predict_eq` (`Asymptotic/Ensembles.lean`, on `uprob` over seed spaces), both the identity behind [PS10, Lemma 73.8] | disclosed in the docstring (gate 02 closing commit) | Derive one from the other through bridge B2 when ch. 2–4 lands on `main`. |

## Found in the ch. 5–8 statement phase (2026-11-05)

| # | Statement | Copies | Status | Resolution |
|---|---|---|---|---|
| DL-6 | Coin-tape slices `(r.drop (j * c)).take c` in global/GI-shadow graph isomorphism, Lamport and sequential ZK, alongside the former BlockEncryptor home | historical duplicates found by the Lamport worker/maintainer | **Implemented at `e9d64158461bfe24ddc88ab885bc4017899b4c16`; final source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` is checked in draft PR #232. Native and layered Rule10 reconciliation identify zero new/touched reads; all older failures remain recorded. External gates and landing pending.** | One `TCSlib.Cryptography.coinBlock`, `coinBlock_eq` and `length_coinBlock` live in `Asymptotic/Adversary.lean`. The BlockEncryptor definition moved upstream; global/shadow `coinSlice` and sequential ZK's `phaseSlice`/unused length lemma are retired. Lamport already used the public BlockEncryptor `coinBlock`; its length lemma moved upstream. Consumers use the shared name and published reader. |
| DL-7 | Equal-length padding: Lamport's `ofFn_padFin_of_length`, and the inline step in `Composability.length_eval_of_length` (`CCA2Scheme.lean`) | General equation `Collection.ofFn_padFin_of_le` in **`Asymptotic/CollectionsHelpers.lean`**, not `Collections.lean` | **Implemented at `e9d64158461bfe24ddc88ab885bc4017899b4c16`; final source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` is checked in draft PR #232. Native and layered Rule10 reconciliation identify zero new/touched reads; all older failures remain recorded. External gates and landing pending.** | Lamport's duplicate theorem is deleted. Its uses and CCA2's two padding steps use the general equation, whose conclusion is `List.ofFn (padFin ℓ w) = w ++ List.replicate (ℓ - w.length) false`; at `w.length = ℓ`, simplify `Nat.sub_self`, `List.replicate_zero` and `List.append_nil`. |
| DL-8 | `SecureComputation.PRFOut ℓ₂` (prong B, `SpecialEncryptionSecurity.lean`): ch. 2–4's `PRF` with `ℓ₂(n)`-bit outputs; `PRF` is its case `ℓ₂ = n` | resolved 2026-11-05 | `prfOut_var_iff : PRFOut .var F ↔ PRF F` proved beside `PRFOut` (prong B). The ch. 2–4 layer is unchanged. |


## Found by gate 03 (2026-11-05; rulings G3-5 and R-03l-1: clean up in the gate 03 clean-up PR, after #195)

Most copies trace to helpers that are `private` in pack 03a's and 03l's files. The clean-up makes
one copy public in the most upstream file and re-points the rest.

| Id | Copies | Status | Payback |
|---|---|---|---|
| DL-9 | The coin-block bijection `blocks` (`Fin (m · c) → Bool ≃ Fin m → Fin c → Bool`) and its lemmas, copies and an inverse: `FunFamily.blocks`, `OneWayYao.blocksE`, `blocksEquiv`, `blocksEquivX`, `EnsembleLemmas.blocks`, `SoundnessRep.blocksEquiv`, and `Ensemble.blocks` (private, `Asymptotic/Ensembles.lean`, which calls itself a copy of `FunFamily.blocks`; added on gate 03a round 2, R2-4); with S2b's public duplicate `take_drop_ofFn_blocks` of `EnsembleLemmas.take_drop_ofFn_blocks` (gate 04 N4) | accepted; scheduled (G3-5) | One `FunFamily.blocks` in a low file; re-point 03h, 03i, 03k's statements, `Ensembles.lean` (03a) and S2b's copy. |
| DL-10 | `ptc_comp` (composition of polynomial-time functions in a convenient form), six private or public copies (`Closure`/`Repetition` helpers, `Universal*`, `ThreeColoring/Machines`, …) | accepted; scheduled (G3-5) | Public once in 03a's `Closure.lean`; delete the copies. |
| DL-11 | The state loop `stateFind` (private in `Repetition.lean`) and its copies `GI.stateFind`, `EncodingMachines.polyTimeComputable_stateFind`, `GGMRed.stateLoopFun`, and the variant `stateIterate` | accepted; **half done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`polyTimeComputable_stateFind` public, prose fixed); the copies are re-pointed in clean-up part 2 | `polyTimeComputable_stateFind` public in `Repetition.lean`; re-point; update the prose that calls it private (`StringLoops.lean:36–38`, `HardCoreLoops.lean:68`). |
| DL-12 | `abs_uexp_sub_le`, two copies (`PublicKeyLemmas` and a private one) | accepted; scheduled (G3-5) | One public copy. |
| DL-13 | `negligible_zero` (`Foundations/Negligible.lean` since G3-7a) and `negligible_const_zero` (`ZeroKnowledge/Defs.lean`) | accepted; scheduled (G3-5) | Delete `negligible_const_zero` (2 uses). |
| DL-14 | `forall_of_uprob_eq_one`, two copies | accepted; scheduled (G3-5) | One public copy. |
| DL-15 | `decodeFin_eq_some_iff`, a private copy in `Collections.lean` and a public one in `GGMReductionEval.lean` (`GGMRed.decodeFin_eq_some_iff`; making the `Collections.lean` copy public must avoid the namespace clash, gate 03b review #12c), and the new forward lemma `ofFn_of_decodeFin_eq_some` (`CollectionsHelpers.lean`, #198); S2b's private `eq_ofFn_of_decodeFin` | accepted; scheduled (G3-5) | One public `decodeFin_eq_some_iff` in `Asymptotic/Adversary.lean`; the forward lemma derived from it. |
| DL-16 | `IterateFindHost` (03l) copies 26 declarations of `main`'s private module layer in `Complexity/ClassNP/SAT.lean` (ten now public); the new host is missing from the policy's host registry (§14) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)**: one public host `Turing.ModuleHost` (`TuringMachine/Build/ModuleHost.lean`), consumed by `SAT.lean` and `IterateFindHost.lean`; registry row H14 | Make `SAT.lean`'s layer public on the ch. 2–4 branch and re-point `IterateFindHost`; register the host. |
| DL-17 | `StateLoop` (03l) restates five `main` lemmas, plus `tail_poly` and `xor_poly` (arrived with the `main` merge, #186) | accepted; scheduled (R-03l-1) | Use `main`'s lemmas. |
| DL-18 | `UnaryMul` (03l) privately copies `PairSplit`'s parser | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`Turing.PairParse` in `PairSplit.lean`) | Use `PairSplit`'s. |
| DL-19 | Not a copy yet: a latent name clash between `StateLoop.BlockLoop` and `main`'s `Complexity.BlockLoop` (nothing uses it) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (renamed `StateLoop.BlockMapLoop`) | Rename or merge in the same PR. |
| DL-20 | `main`'s `TuringMachine/Build/Loop.lean` keeps a private `loop_first_halt`, the same lemma as the new public `Turing.ModuleHost.first_halt` (found by #203's worker). `Loop.lean` is upstream of the host, so it cannot consume it | noted | Move `first_halt` and `live_prefix` down into `Loop.lean` (or the machine core) at the `main` landing, and have `Loop.lean` use them. |
| DL-21 | Elementary number theory that Mathlib already has (audit `mathlib-overlap-nt.md`, 2026-11-06, Mathlib pin `029db123`): 6 DUP (`QR` = `(powMonoidHom 2).range`, `crtUnits` (keep as alias, `rfl`), `coprime_of_ne` = `(Nat.coprime_primes hp hq).2`, `powOneSubgroup` = `(powMonoidHom m).ker`, `rsaPerm` ≈ `powCoprime` (optional), `IsGenerator` ≈ `∀ x, x ∈ zpowers g`) and 9 WRAP (shorter proofs from Mathlib: `units_val_mem`, `pow_mod_totient_modEq`, `units_pow_eq_one_iff`, `two_mul_card_le_of_ne_top`, `card_units_eq_mul_card_QR`, `card_QR_prime`, `sq_pow_div_four_succ`, `fmultNat_eq_mul_prime`; and the core of the sorried `elGamal_correct`) | accepted; scheduled (user direction 2026-11-06: Mathlib first) | Replace by Mathlib's (alias where a name is load-bearing), clean-up part 2 item M; rows in fill-owned files (`Candidates/*`) after those fills land, as landing edits. The fill briefs cite the report's Mathlib names. |
| DL-22 | TCSlib's Chebyshev lower bound (`NumberTheory/Chebyshev.lean`) and Korselt-type facts are in newer Mathlib (`Chebyshev.pi_ge`, `theta_ge`, `psi_ge`; `Nat.isCarmichael_iff_korselt`; master `94f43000`, Lean v4.36.0-rc2), not at our pin | noted | Replace at the next Mathlib bump (repository-wide, `main`'s pin). At the same bump, the hypothesis `BlumDensity` (`Rabin.lean`) can be discharged in its eventual form (`n ≥ n₀`): apply `WienerIkehara.tendsto_sum_range_div` (master only) to `vonMangoldt.residueClass 3` mod 4, with the continuation `vonMangoldt.continuousOn_LFunctionResidueClassAux` (already at our pin) and Chebyshev's `ψ(x) ≪ x` (master), to get `ψ(x; 4, 3) ~ x/2`; then `θ ≥ ψ − (ψ − θ)` (`Chebyshev.psi_sub_theta_le_mul_sqrt`) and `π(x; 4, 3) ≥ θ(x; 4, 3)/log x`. This changes the Rabin statements that take `BlumDensity` (they would take nothing, or `n ≥ n₀`); a statement gate then. |
| DL-23 | fac fill (`Candidates/Factoring.lean`, delivery review 2026-11-07): private near-copies of public lemmas: `fac_chunkEquiv` = `FunFamily.blocks`; `fac_arrowCongr` = `finCastEquiv`; `fac_ofFn_halves` repeats a private `OneWay` lemma (half is `ofFn_block_eq_take_drop`); `fac_listToNat_inj` repeats a private `Sampling` lemma; plus the REPORT's three near-duplicates and small numeral facts re-proved across the fac, rsa and dl-a fills | noted | Clean-up part 2: re-point to the public lemmas; publish the two private ones beside their files and share the numeral facts. |
| DL-24 | col-b fill (delivery review 2026-11-07): `ColZK.acceptProb_seed_to_coins` = `acceptProb_bind` reversed and `ColZK.findSome?_map_option` = core `List.map_findSome?` (removed by landing edits E3–E4); a third copy of `pushesUniform_restrict` across fill units (dl-a has one); `table_index_*` vs `finProdFinEquiv`; `polyTimeComputable_next` repeats `reply_poly`'s proof (review finding 6 has the full list) | E3–E4 at landing; rest noted | Clean-up part 2: publish one `pushesUniform_restrict`, re-point the rest. |
| DL-25 | dl-b fill (`DiscreteLogHardcore.lean`, delivery review 2026-11-07): `dlb_statClose_pi` copies the public `OneWay.statClose_pi` (removed by landing edit E1); `dlb_stateIterate_poly` (from `HardCoreLoops`), `dlb_count_ofFn` (from `HardCoreGL`; relative of `List.count_ofFn`), the `listToNat` fold lemmas, `two_pow_size_le` (dl-a and 3-col have inline `2^size m ≤ 2m` bounds), `pushesUniform_castLE` copies (review D1) | E1 at landing; rest noted | Clean-up part 2: publish one copy of each beside its source; missing equations `HardcoreBit.majority_eq` (`PairwiseIndependence.lean`) and `expSampler_coins` (`DiscreteLog.lean`) at the next shared-file window. |
| DL-26 | col-a fill (delivery review 2026-11-07): `colRep_xor_poly` = `StateLoop.xor_poly`, `eq_of_xor_eq_false` = core `bne_eq_false_iff_eq`, `pushesUniform_blockRead` rebuilds `FunFamily.blocks` (removed by landing edits E2–E4); `ColRep.exec_four_mul`'s step repeats `GI.exec_repViews`'s proof (promote `exec_four_mul`, request R-3); cross-unit near-copies with col-b's `ColZK.pushesUniform_offsetTable`, `ColZK.ofFn_drop_take` | E2–E4 at landing; rest noted | Clean-up part 2: promote `exec_four_mul`, share the col-a/col-b helpers; requests R-2 (`(decGraph x).1` equation), R-5 endorsed. Base reading for #210's next round: `R3COL_witnessRelation`'s `bounded` clause destructures `R3COL` instead of using `R3COL_iff`. |
| DL-27 | rsa fill (delivery review 2026-11-07): 151 lines copied verbatim from dl-a's private helpers (`dla_findSome?_ite`, `dla_find?_range_lt`, `dla_listToNat_append`, `dla_drop_natToList_zero_append`, `dla_ss*`); `rsa_appendEquiv` = Mathlib `Fin.appendEquiv` (landing edit E1); `rsa_comp`/`ptc_congr` copies of the private `ptc_comp` family; loop lemmas descend from Primality's private `spStep`; near-copies of `findSome?_eq_bind_find?`, `find?_range_eq_map_find?_finRange`; parallels with fac (`fac_natToList_mod`, `fac_pairDec`) | E1 at landing; shared-lemma PR planned | **Landing order:** (1) dl-a lands; (2) a shared-lemma PR publishes `PolyTimeComputable.comp'`/`.congr` (`PolyTime.lean`), `IterateFind.find?_range_and_lt` (`IterateFind.lean`), nine `listToNat`/`natToList` lemmas (`Arithmetic.lean`), `rejectBlocksL_eq_find?` (`Concrete.lean`), removing dl-a's copies; (3) rsa lands with E1–E3 and E4 (cites them; checked against stubs); (4) a statement-gated `polyTimeComputable_rejectBlocksL` retires the copied loops in dl-a, rsa, rabin (and dl-c, pending its review). |
| DL-28 | dl-c fill (delivery review 2026-11-07): near-verbatim copies of the trial loop and numeral helpers shared with dl-a and rsa (and dl-b's own modular-numeral layer); `dlc_abs_uexp_sub_le` duplicates `Sampling.lean`'s private lemma and its public copy in `PublicKeyLemmas.lean` (review D1) | noted | Folds into DL-27's shared-lemma PR. The review's D2 homes: generic `polyTimeComputable_rejectBlocksL` (`Concrete.lean`), `listToNat` lemmas, width lemmas (`Arithmetic.lean`), `find?_range` (`Repetition.lean`), `PolyTimeComputable.congr` (`PolyTime.lean`), `abs_uexp_sub_le` public in `Sampling.lean`, `finCastEquiv` to `CollectionsHelpers.lean`. Reconcile with DL-27's homes when that PR is drafted. |
| DL-29 | rabin fill (delivery review 2026-11-07): `rabin_appendEquiv` = Mathlib `Fin.appendEquiv` and `rabin_pushesUniform_prod` (re-proved from `PushesUniform.prodMap`) handled by landing edits E1–E2; undisclosed copies: `rabin_statClose_one` = dl-a's `dla_statClose_one`; `rabin_listToNat_mulStr`, `rabin_prime_poly` copy rsa helpers; `rabin_rS`/`_rQ`/`_rTest` ≈ rsa's `rsa_fS`/`_fQ`/`_fTest`; the block loop is a fourth copy (with dl-a, rsa, dl-c `dlc_ss*`); `rabin_drop_zeros_append`'s step = fac's `fac_natToList_mod` | E1–E2 at landing; rest noted | Folds into DL-27/DL-28's shared-lemma PR and the `polyTimeComputable_rejectBlocksL` host PR. Base reads `rabinCollection_index`, `rabinBlumTrapdoor_index` (through `show`; re-point via `Collection.index_eq`) go to clean-up part 2's (b) list. |
| DL-30 | padded-cpa fill (delivery review 2026-11-11): generic `ProbComp` facts published in a public-key helper as `Composability.ChallengeSim.expect_sample_equiv`, `expect_sample_comm`, `expect_sample_unique`, `expect_sub` (`PublicKey/OracleSecurity/ChallengeSim.lean`); `expect_sample_prod` repeated `Bridge.expect_sample_pair`'s proof. | `ChallengeSim.lean` only | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Landing edit re-proved `expect_sample_prod` from `Bridge.expect_sample_pair`. Promote the four lemmas to `ProbComp` in `Games/Probability.lean` and re-point their uses. |
| DL-31 | `ofFn_padFin_of_length` (`List.ofFn (padFin d w) = w` when `w.length = d`): `GGMRed.ofFn_padFin_of_length` (`GGM/Run.lean`), copy in `Asymptotic/HardCoreGLColl.lean`, private copy in `ElGamal.lean`; padded-cpa's `RecordHandler.lean` uses the GGM one through a transitive import. | 3 | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Promote one public lemma beside `padFin` in `Asymptotic/Adversary.lean`; re-point all uses and delete the copies. |
| DL-32 | `List.ofFn (cast h f) = List.ofFn f` for a width equality: public `Composability.AdaptiveCPA.ofFn_cast` (`PublicKey/AdaptiveCPA/Games.lean`) and private `cca2OfFn_cast` (`PrivateKey/OracleFromPRF.lean`, #289). adaptive-cpa review also lists for promotion: `expect_sample_update` (→ `Games/Probability.lean`, with DL-30), `simulate_eq_of_abs` and the `castImpl` family (→ `Games/Simulate.lean`), `padFin_ofFn_zeroBits`, `headD_ofFn_one`, `ofFn_splitHalf_fst/_snd`; reader request `indCodec_eq_bitCodec`; new uses of `GGMRed.ofFn_padFin_of_length` join DL-31. | 2 (+ candidates) | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Promote one generic `ofFn_cast` beside `padFin`/`BitCodec`; re-point both; promote the listed generic lemmas. |
| DL-33 | bitwise-cpa fill (delivery review 2026-11-11): `BitwiseSim.expect_sample_update` vs `AdaptiveCPA.expect_sample_update` (two forms, same name); generic `BitwiseSim.expect_simulate_eager` and public near-copy `BitwiseSim.expect_simulate_indImpl_cpa` of the private lemma in `PublicKey/OracleSecurity.lean`; `chRun_toCompOn_transport_list` generalizes `ChallengeSim.chRun_toCompOn_transport`; `BitwiseSim.headD_drop` = public `CommitmentLemmas.headD_drop` (and private `headD_drop_ofFn` in `Pseudorandom/NextBit.lean`); `flatten_ofFn_singleton` = private `flatten_ofFn_one` (`Yao.lean`); `decodeFin_nil_getD` (→ `Games/BitCodec`); `padded_enc_runAt/_coins` (→ beside the padded readers); `qDin/qDout` third copy of the two-oracle length vector (`recDin/recDout`, `acDin/acDout`); private `ofFn_half`, `bitwise_runAtL` re-prove published facts; reader request `HybridMachine.hybridPre_eq`. | several | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | One consolidation PR with DL-30–DL-32: promote to `Games/Probability`, `Games/Simulate`, `ChallengeSim`, `BitCodec`, a shared list module; re-point and delete copies. |
| DL-34 | pk-cpa-cca1 fill (delivery review 2026-11-12): `OracleFromPRF/Handler.lean` copies private AdaptiveCPA handler pieces (`ofFn_padFin_eq_padL`, round-input readers `rU`…`rCnt`, `impl_of_ret`, `replicate_one`); public `ofFn_pkTapes` re-proves `AdaptiveCPA.ofFn_acTapes` (a generic `⟦blocks q ℓ ω j⟧ = (⟦ω⟧.drop (j·ℓ)).take ℓ` belongs beside `FunFamily.blocks`, input-layout readers beside `InteractiveHandler.input`); private-key `indCodec_eq_bitCodec` (DL-32 reader request); `mem_keys_of_lookup_isSome` (core `List.lookup_isSome_iff`); promotion candidates `simulate_eq_of_abs_bounded` (generalizes `AdaptiveCPA.simulate_eq_of_abs`), `expect_simulate_congr` (→ `Games/Simulate`), `abs_expect_sub_le` (→ `Games/Probability`), `prob_bad_le`, `expect_sample_mem_le` (→ `Games/Hopping`), `padFin_nil`, `padFin_replicate_false`, `ofFn_arrowCongr_finCongr` (→ beside `padFin`), `zipWith_xor_cancel_left`, `xorPerm` (shared list/vector module); owned-file private overlaps with the `cca2*` helpers. | several | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Fold into the DL-30–DL-34 consolidation PR. |
| DL-35 | Found while staging the consolidation (2026-11-12): public `blocks` in `Asymptotic/EnsemblesLemmas.lean` and private `blocks` in `Asymptotic/Ensembles.lean`, both the equivalence `(Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool)` of `FunFamily.blocks` (`Asymptotic/Adversary.lean`). | 2 | Open (ch. 2–4 inherited) | Re-point to `FunFamily.blocks` in a later ch. 2–4 cleanup; out of scope for `dl-consolidation`. |
| DL-36 | nm-cca2 fill (delivery review 2026-11-12): `NMCCA2.logEmit` (`PublicKey/NonMalleability/Indistinguishability/Forward.lean`) generalizes `Games.EffFill.relabelN`/`relabel` (`Games/Efficiency/OracleBridge.lean`), and its log facts `logEmit_encodeLog`, `iterate_pairSndD_encodeLog`, `flatMap_range_drop`, `length_le_length_encodeLog`, `length_iterate_pairSndD_le`, `polyTimeComputable_logEmit` mirror `relabelN_encodeHist`, `length_le_length_encodeHist` and the orbit bound of `bridgePre_poly` (undisclosed); public `finU`, `finZ`, `finW`, `finA`, `finL`, `fields_finInput` are the DL-34 round-input readers (`rU`…`rL`) again; `ofFn_nthCt` (owned file) is DL-34's generic block fact (`ofFn_acTapes`, `ofFn_pkTapes`); the private readers `rState`…`rAns` (disclosed). Promotion requests: `fwdHandler`/`fwdHandler_impl`, `exists_withAdviceOn` (→ `Games/Efficiency`), `cntRead`/`ansRead` (→ `BitCodec`), `indImpl_eq_of_msgLen_eq_zero` (→ `PublicKey/OracleSecurity`, after that file is split: it is at 999 lines). | several | **Paid** ([#299](https://github.com/Shilun-Allan-Li/tcslib/pull/299), merge `eff2dcd0`, 2026-11-14; Gate 21) | After the DL-30–DL-34 consolidation lands: put `logEmit` beside `relabelN` with `relabel x = logEmit relabelEmit x`; re-point `dCnt`/`dCt`/`dIn`/`dFin`/`eBit`/`eMsg`/`eTape`/`eCt` to R6's readers and delete `finU`…`fields_finInput`; derive `ofFn_nthCt` from the generic block lemma; promote the accepted requests. |
| DL-37 | nm-sim fill (delivery review 2026-11-13; **undisclosed**, accepted as debt by Seyoon 2026-11-13): `NMSim.chunkAt`/`chunkAt_eq`/`length_chunkAt` (`PublicKey/NonMalleability/Simulation/Hybrid.lean`) and the block lemmas `ofFn_block`, `chunkAt_flatten_append`, `map_chunkAt_flatten`; private `padFin_replicate_false` (`Simulation/Challenge.lean`); `Rounds.impl_of_ret`, `rdU`…`rdLog`/`rdState`, `rdAns`, `Simulator.finSt` (`Simulation/Rounds.lean`, `Simulator.lean`); also generic neighbours `expect_eq_until_bad`, `NMSim.expect_simulate_eager`, `expect_congr_of_allOutputs`, `chunkMap`; disclosed: `flatMap_range_drop`, `ofFn_padFin_eq_padL`, `polyTimeComputable_guessBit`, `ofFn_eq_map_range` | `coinBlock`/`coinBlock_eq`/`length_coinBlock` (`Asymptotic/Adversary.lean`), `OneWayLemmas.ofFn_block_eq_take_drop`, `NMCCA2.ofFn_nthCt`, Lamport `coinBlock_flatten`; `PRFGame.padFin_replicate_false` (`OracleFromPRF/Transfer.lean`; → `Games.padFin_replicate_false` in the consolidation); DL-34 private `impl_of_ret` (`AdaptiveCPA/Handler.lean`, `PRFGame`) and readers `rU`…`rL`/`rS`; `Games.prob_eq_until_bad`, `BitwiseSim.expect_simulate_eager`, `ProbComp.expect_mono_of_allOutputs`, `relabelN`/`logEmit` (DL-36); ZK `ofFn_eq_map_range` ×2; A4 `EnsembleLemmas.ofFn_padFin_eq_padL`; `rFwd`/`rY`/Forward `rAns` | **Paid** ([#299](https://github.com/Shilun-Allan-Li/tcslib/pull/299), merge `eff2dcd0`, 2026-11-14; Gate 21) | Landing of the consolidation (after nm-sim): delete the private `padFin_replicate_false` and use `Games.padFin_replicate_false`; re-point the nm-sim files to the moved names. Post-consolidation fold window, with DL-36: fold `chunkAt` onto `coinBlock` (58 uses) and place the block lemmas beside it; re-point `rdU`…`rdLog`, `rdState`, `finSt` to `InteractiveHandler.rU`…`rS` and `impl_of_ret` to `InteractiveHandler.impl_of_ret`; derive `prob_eq_until_bad` and `ChallengeSim.expect_simulate_eager` from the general nm-sim forms; one iterate-and-emit definition for `relabelN`/`logEmit`/`chunkMap`; merge the three `ofFn_eq_map_range` into `Foundations/BitLists`; make `NMSim.ofFn_padFin_eq_padL` the A4 lemma; fold `rdAns` with the `rFwd`/`rY`/`rAns` readers; promote the accepted requests (review r1 table). |
| DL-38 | dl-folds fill (worker REPORT §0.6, disclosed; delivery review 2026-11-14): inline re-proofs of `impl_of_query` (`acHandler_impl_forward`) and of a returning finalization (`pkHandler_finish`, `acHandler_finish`); a local `have` equal to `polyTimeComputable_ansRead` (`OracleFromPRF.lean`); further block-window restatements (`Primality.ofFn_chunk`, `ColRep.drop_take_ofFn_blockRead`, `Factoring.fac_ofFn_halves`, already corollaries); other iterate-and-emit loops (`BlockEncryptor`, `EnsembleLemmas.CopiesLoop`, `StretchMachine`, `CommitmentLemmas.ComLoop`, ZK `EncodingMachines`); the ZK pair `GI.iterate_pairSndD_encodeMsgs` / `ColMachines.iterate_pairSndD_encodeMsgs`; and the B3 `blocks` aliases (`EnsembleLemmas.blocks` and its lemmas, private `Ensembles.blocks`), escalated. | `InteractiveHandler.impl_of_query`, `finish_of_ret`; `Games.polyTimeComputable_ansRead`; `FunFamily.ofFn_blocks`; `Games.iterEmit`; `FunFamily.blocks` | Open (deferred) | Opportunistic: fold each when its file is next touched. The B3 aliases need a gate-approved restatement of `exists_copiesRed`, `ofFn_blocks_symm`, `take_drop_ofFn_blocks`, `ComLoop.emit_init_of_lt` and of the bodies of `PRFGame.pkTapes`, `Ensemble.copies` (all definitionally equal). Complexity copies of `ofFn_eq_map_range` and `flatMap_range_drop` are another campaign's. |
| DL-39 | ext-nosrc fill (worker request and delivery review 2026-11-14, disclosed): `Randomness.Rejection.tupleEquiv` restates Mathlib's `(Fin.consEquiv _).symm`; generic `FinDist` facts local to `Randomness/Extraction/Rejection.lean` (`sum_map`, `expect_map`, `probTrue_map`, `probTrue_le_one`, `probTrue_nonneg`, `map_map`, `map_prod_snd`, `uniform_prod`, `map_uniform_equiv`, `mixture`, `mixture_isSource`, `uniform_probTrue`); no exact duplicate in TCSlib (nearest: `SamplingFinDist.uprob_comp_eq_probTrue_map`, `Experiments.uprob_comp_eq_sum_map`, `ProbComp.expect_map`). | Mathlib `Fin.consEquiv`; `InformationTheory/FinDist` (to be added) | Open (deferred) | Promote the `FinDist` facts to `InformationTheory/FinDist` and use `Fin.consEquiv` in a later job (`FinDist` was frozen for the fill). The authoritative full promotion list (also `map_apply_expect`, `branch_apply`, the uniform-machine family, `take_poly`) is the delivery's `evidence/promotion-requests.md`, `rejection-review.md`, `sampler-review.md` (exchange `a5da5cc3`, `inbox/fills/ext-nosrc/`; Gate 22 observation). |
| DL-40 | cca2-ett fill (delivery review 2026-11-14): undisclosed `ETTGame.eval_toOracleAdversary_len` (`EncryptThenTag/Machines.lean`) generalizes public `PRFGame.eval_toOracleAdversary_width` (`OracleFromPRF/Reduction.lean`, its `ℓ = n` case); disclosed `ETTGame.zipWith_xor_cancel` = four private `zipWith_xor_xor_self` copies (`FromPRF`, `FromPRG`, `SpecialEncryption`, owned `zipWith_xor_xor_self'`; public relative `zipWith_xor_cancel_left`, other orientation); Gate 23 (G23-01, Seyoon 2026-11-14: debt now, fold in cleanup): private `length_le_length_encodeLog` (`EncryptThenTag/Machines.lean`) = the private copy in `NonMalleability/Indistinguishability/Forward.lean:108`; `ETTGame.prfAdv_eq_expect` re-derives private `prfAdv_prfReduction` (public relative `prfAdv_eq`, uprob form); generic forms `ETTGame.tapeImpl`/`simulate_tapeImpl_congr`/`expect_simulate_tapeImpl` (AdaptiveCPA), `recBits` family and `ovr` (PRFGame), `expect_simulate_abs` (`Games.simulate_eq_of_abs_bounded`), private `abs_expect_sub_le_expect` (`ProbComp.abs_expect_sub_le`). | `Foundations/BitLists`, `Pseudorandom/Functions`, `Games/*`, the general ETT forms | Open (deferred) | Promote the general forms (worker requested most) and re-derive the specialised copies from them; fold the private XOR copies; publish `length_le_length_encodeLog` in `Games/Efficiency/Strings.lean` beside `length_encodeLog_le` and delete both private copies (cleanup job). |
| DL-41 | dl-crh fill (delivery review 2026-11-14): **undisclosed** `FromDiscreteLog.inputWord_split` restates `ofFn_eq_init_append` (`Asymptotic/ReductionSupport.lean`, up to `Fin.init`); `ofFn_splitBits_fst/_snd` restate `ofFn_splitCoins_fst/_snd` (`CollectionsHelpers.lean`; `Authentication.splitBits` = `splitCoins`); disclosed re-derivations from public readers of private `dlb_expo_val`, `fac_listToNat_inj`, `ofFn_splitCoins_symm_cast`, `dla_statClose_expDec`; near relatives `residueFinEquiv` (Mathlib `ZMod.finEquiv`), `boundedInputEquiv` (`Fin.snocEquiv`), `expect_sample_eq_uexp` (`Games.Bridge.prob_sample_eq_uprob`). | `ofFn_eq_init_append`, `ofFn_splitCoins_*`, a `splitBits = splitCoins` bridge; worker promotion list `evidence/PROMOTION.md` (exchange `9ad236d1`) | Open (deferred) | `inputWord_take` (Gate 24 G24-01) and `inputWord_split` re-pointed to `take_ofFn_castLE` / `ofFn_eq_init_append` by LE-reuse `d356381a` (#307); the rest: re-point and promote in a later job. |
| DL-42 | hash-sign fill (delivery review 2026-11-14): `HashSignForward.roundWord`/`handler` repeats the `Games/Forwarding` `fwdRun`/`fwdHandler` pattern with a hashed query and different widths (disclosed); `splitBits_pad_concat` is a corollary of `Games.padFin_append_split`; `expect_simulate_sample_once` near `Games.expect_simulate_eager`; `MachineCodec.ext_of_fields`, `forgerCodec_eq_bitCodec`, `eq_pure_of_cost_zero` overlap the parallel lamport delivery's `lamport_codec_ext`, `lamport_forgerCodec`, `exists_pure_of_cost_zero`. | `Games/Forwarding` (a query-map `fwdHandler`), `Games/BitCodec`, `Games/Hopping`, `Games/Machines` | Open (deferred) | Generalize `fwdHandler`; promote the codec/cost facts to `Games/Machines` (no attribute) and fold the lamport copies once both units have landed. |
| DL-43 | lamport fill (delivery review 2026-11-14): **undisclosed** `LamportFill.signatureBlock σ i` = `FunFamily.blocks n n σ i` (via `blocks_apply`; DL-9 class); near relatives `Blocks.flatten_ofFn_update` (`CommitmentLemmas.ofFn_update_eq`), `Averaging.expect_favourable_of_success` (`ProbComp` counterpart of `HardcoreBit.uprob_mul_le_uexp`). Overlaps with hash-sign are DL-42. Also the follow-up (Seyoon, 2026-11-14): restate the frozen `lamport_oneTimeSecure` hypothesis `f` over `Fin (var.eval n)` with a published reader, clearing its 16 seal-B failures. | `FunFamily.blocks`; `CommitmentLemmas`; `HardcoreBit` | Open (deferred) | Re-point `signatureBlock`; promote the averaging lemma; the frozen-statement restatement needs its own gate. |
| DL-44 | prf-mac fill (delivery review 2026-11-15): F-01 local `hadv` in `MAC/FromPRF/Bound.lean` re-proves public `ETTGame.prfAdv_eq_expect` (**ruling Seyoon 2026-11-15: promote now** to the PRF layer beside `prfAdv`, re-derive the ETT copy proof-only, re-point prf-mac); F-02 `decide_fnForge`'s `hw`/`htake`/`hdrop` restate list readings of `splitBits` (`take_ofFn_castLE`, `CollectionsHelpers.ofFn_drop_take`, `FromDiscreteLog.ofFn_splitBits_fst/_snd`); F-03 `PRFMAC.blocks`/`macState`/`hits_nil_iff` near `GGMRed.tblEnc`/`lookup` (cca2-ett `tblW`). The private `prfAdv_prfReduction` (`OracleFromPRF.lean`) is the same identity specialised (DL-40). | `TCSlib.Cryptography.prfAdv_eq_expect` (published in #314, merge `59c2c1fb`); the list readers above; `GGMRed.tblEnc` | Open (F-01 paid) | F-01 **paid**: promoted in #314 (ETT re-derived, LE-gate30), prf-mac re-pointed by LE-reuse `590d1a56` (#317, Gate 33). F-02/F-03 and the private `prfAdv_prfReduction` in the deferred cleanup. |
| DL-45 | learning fill (delivery review 2026-11-15): undisclosed `LearnPRF.uprob_eq_point` = `OneWay.uprob_eq_one_div_card` (reversed); inline re-proof of `MultiMsg.abs_uexp_sub_le_uprob` in `abs_gameProb_random_sub_half_le` (both re-pointed by maintainer LE-reuse `8befc589`, #313); private `length_blk` re-proves `MultiMsg.length_histBlock` for the disclosed private copy `blk` of `histBlock`; `flip0`/`flip0_flip0` = `flipBit`/`flipBit_flipBit` (BooleanAnalysis) and `flipAt` (DeterministicCC); `foldr_pairEncode_nil` reads `Strategy.encodeMsgs`; short-name clashes `relabel`/`relabel_eq` (DL-36 family) and `flipAt`. | `OneWay.uprob_eq_one_div_card`; `MultiMsg.abs_uexp_sub_le_uprob`, `length_histBlock`; `BooleanAnalysis.flipBit` | Open | Items 1–2 by LE-reuse at landing; the rest in the deferred cleanup. |
| DL-46 | prf-long fill (delivery review 2026-11-15, disclosed): `MultiMsg.encodeList_eq_flatMap` (`FromPRF/MultiMsgOut.lean`) is a third copy of public `encodeList_eq_flatMap` (`Asymptotic/BlockEncryptor.lean`) beside the frozen private copy in `FromPRF.lean` (now unused); reuse blocked by a private/public name clash. `histBlockLen` kept beside `histBlockLenOut` (different `PolyExpr` terms); `adviceBound` now unused. Near relatives: GGM `encodeHist_eq_histEnc`/`histEnc_append_single`/`length_histEnc`, `UniformTableauEmitter.encodeList_eq_flatMap`. | `encodeList_eq_flatMap` (to move to `EnsembleSecurity`, worker's promotion request) | Open (deferred) | Promote and delete the copies; remove the unused frozen items under a frozen-file exception in the cleanup. |
| DL-47 | Gate 32 staging (2026-11-15), pre-existing: copies of `((List.ofFn f).drop i).headD d = f i` and of its getD form `(List.ofFn f).getD i d = f i`, at the tip `e9998722`. Inline chain: `Pseudorandom/NextBit.lean:454` (`headD_drop, List.getD_eq_getElem?_getD, List.getElem?_ofFn`, the remnant of NextBit's private `headD_drop_ofFn` that dl-consolidation L1 deleted). Index-0 cases: `headD_ofFn_one` (`Foundations/BitLists.lean:75`), `GIZK.headD_ofFn_block` (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:280`), private `eq_const_headD` (`Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean:88`). getD forms: `GI.getD_ofFn_lt'` (`ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean:61`), `GI.getD_ofFn_lt` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean:818`), `GIZK.getD_ofFn_lt` (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:110`), `ColProofs.ofFn_getD_lt` (`ZeroKnowledge/ThreeColoring/ProtocolProofs.lean:391`), Yao's private `getD_ofFn'` (`SecureComputation/Yao.lean:611`). Inline getD chains (`List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos …`): `ZeroKnowledge/ThreeColoring/Simulator.lean:861`, `ZeroKnowledge/ThreeColoring/Language.lean:429` (in private `ofFn_getD_tape`), `ZeroKnowledge/Encoding.lean:359`; the same getD chain also inline outside the cryptography files, in `TCSlib/Complexity/ClassNP/SAT.lean:149`, `TCSlib/Complexity/ClassNP/Tautology.lean:142` and `TCSlib/Complexity/SpaceComplexity/Codec/Word.lean:135` (`getD_encChunk`). **Extended by Gate 32 G32-01 (ruling Seyoon 2026-11-15: extend DL-47 and close), at the #316 head `c18afbe6`:** exact copy of the promoted statement: GGM `Pseudorandom/Functions/Asymptotic/GGM/Run.lean:449–450` (`step_eq`, local `hbit`, replacement `TCSlib.Cryptography.headD_drop_ofFn x ⟨d.i, hi⟩ false`); headD chain `Asymptotic/HardCoreLoops.lean:278–280` (`orbit_eq`); getD/ofFn computations: `SecureComputation/Garbling.lean:193–198` (private `map_range_getD_ofFn`) and `:375–380` (`garbledValues_getD`), `SecureComputation/Yao.lean:626–627` (`yaoBobTables_yaoMsg`), `Encryption/PublicKey/BitwiseCPA.lean:107–113` (private `ofFn_half`), `Encryption/PublicKey/OracleSecurity/PaddedCPA.lean:72–78` (private `ofFn_splitHalf_bit`), `Complexity/CircuitComplexity/CircuitEvalNP.lean:68–69` (`dagCktSatLang_mem_NP`), `PSubsetPPolyGadget.lean:188–190` (`runWith_embedGates_getD`), `PSubsetPPolyProgram.lean:383–387` (`progGates_values`), `PSubsetPPolyTableau.lean:127–132` (`snapEncode_injective`), `UniformTableauCircuit.lean:427–431` (private `tabSrc_eval`), `Complexity/Randomized/RandomWalk.lean:256–259` (`decodeIdx_succ_append`), `Complexity/ClassPSPACE/TQBF.lean:857–859` (private `codecRow_realize`), optional-access form `Cryptography/Encoding/BooleanVector.lean:168–171` (`expandPoly_encode`) and `Hashing/SIS/CollisionOutput.lean:237–243` (`collisionOutputPoly_pairEncode`). **sc-garble SG-F04 (ruling Seyoon 2026-11-15, ledger):** new inline getD/`List.ofFn` chain in `SecureComputation/Garbling/CoinBlocks.lean:73–74` (`getD_eq_getElem`, `getElem_ofFn`), same as Yao's private `getD_ofFn'`. | `TCSlib.Cryptography.headD_drop_ofFn` (#316) | Open (deferred) | Ruling Seyoon 2026-11-15: pre-existing (merged before the promotion), recorded as debt and not re-pointed in #316. Re-point NextBit:454 and the index-0 cases onto `headD_drop_ofFn`, and the getD forms onto one shared getD reader, in the deferred cleanup. Yao's `getD_ofFn'` waits for sc-garble and sc-yao to land (`Yao.lean` is shared). **Cleanup plan (G32-01):** add one generic reader `(List.ofFn f).getD i d = f ⟨i, h⟩` (any type) derived from `headD_drop_ofFn` and `List.headD_drop`, then re-point every DL-47 copy onto it or onto `headD_drop_ofFn`, proof only, headers preserved, starting with the exact GGM copy; the `Garbling.lean`/`Yao.lean` copies wait for sc-garble and sc-yao to land. |
| DL-48 | sc-ot fill (delivery review 2026-11-15): F-02 `OT.splitLen` / `splitLen_symm_ofFn` (`SecureComputation/ObliviousTransfer/Simulators.lean`) restate public `coinsEquiv` (inverted) and `ofFn_coinsEquiv` (`Asymptotic/EnsemblesLemmas.lean:141,145`), body as private ElGamal `dlc_splitEquiv`; F-04 `OT.uprob_signedPredictor_false/_true` adapt `exists_pkPredictor` (`pkPredictor` has no public reader); F-07 near-relatives `GI.pairSndD_encodeMsgs` (for `getD_one_eq`), `predict_eq`, and promotion requests `negligible_finset_sum`, `statClose_prod_of_forall`, `exec_five`, `length_runAtL_le`. **Gate 34 G34-02 (ruling Seyoon 2026-11-15, ledger):** `OT.length_ofFn_coins` (`ObliviousTransfer/Simulators.lean:210–212`) is a verbatim copy of public `Composability.NMSim.length_ofFn_coins` (`Encryption/PublicKey/NonMalleability/Simulation/Rounds.lean:41–43`); direct reuse would add 69 NM modules to the OT closure. (G34-01, `OT.getD_zero_eq`/`OT.getD_one_eq'` re-proving `headD_drop`, is fixed by LE-gate34, not debt.) | `coinsEquiv`, `ofFn_coinsEquiv`; `exists_pkPredictor` | Open (deferred) | Ruling Seyoon 2026-11-15: ledger debt, disclosed (not fixed in the landing: reuse needs a new import and a definition change). Cleanup: replace `splitLen` by `(coinsEquiv h).symm`; publish `pkPredictor_apply` and re-derive the signed predictor from `exists_pkPredictor`; decide the promotion requests. G34-02 cleanup: promote `length_ofFn_coins` to the `NUPPT` layer (`Asymptotic/Adversary` or `Randomized/NonUniform`) and re-point both copies. |
| DL-49 | sc-compose fill (delivery review 2026-11-15, SC-F01; disclosed in the checkpoint REPORTs): helpers under `SecureComputation/ComposeSecurity/` restate public lemmas because the brief's two extra imports were read as exhaustive: a third `negligible_polyExpr_mul`; `appendCoins` (= `coinsEquiv`); `ofFn_blocks_symm` (= `FunFamily.ofFn_blocks_symm`); `polyTimeComputable_flatMap_range`, `flatMap_range_ite`, `iterSnd_poly`, `encodeMsgs_eq_flatMap`, `msgAt_encodeMsgs` and the `padTo` family (from `Composability/ZeroKnowledge/ThreeColoring/Machines.lean`). | `EnsembleLemmas.negligible_polyExpr_mul` (`Asymptotic/EnsemblesLemmas.lean:377`), `coinsEquiv`, `FunFamily.ofFn_blocks_symm`, the `ThreeColoring/Machines` helpers | Open (deferred) | Ruling Seyoon 2026-11-15: ledger debt. Cleanup: import the public lemmas (or promote the ThreeColoring helpers to a shared machine layer) and re-point the sc-compose copies proof-only. |

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).

## ===== TCSlib/Cryptography/Composability/SequentialZK/RealPrefixBounds.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.EndpointSampling
import TCSlib.Cryptography.Composability.SequentialZK.ExecutionBounds
import TCSlib.Cryptography.Composability.SequentialZK.ProofTransfers

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bounds for actual real phase prefixes

The endpoint reader identifies a typed real-prefix fold with an execution of the padded
prover. The construction specification then gives its exact message count, while the
original prover's uniform message bound also bounds every padded-prover reply. Existing
execution and word-encoding bounds finish the advice-size estimate. [PS10, Theorem 175.1].

## Main definitions

There are no new definitions.

## Main results

* `PaddedProverSpec.realPrefix_bounds`: exact count, bounded messages, and encoded-size bound.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.2.1, Theorem 175.1.
* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
  University Press, 2001, §4.3.4.
-/

namespace TCSlib.Cryptography.SequentialZK.PaddedProverSpec

open Complexity

/-- For `d : PaddedProverSpec π ρ x q p`, verifier `V`, inputs `y,z`, tape `rV`, index
`j≤q`, message cap `B`, uniform original-prover bound `hbound`, and independent phase coins
`coins`, put `pre = realPrefix π V x y z rV p j coins` and `k = π.rounds.eval |x|`. Then
`pre.length = j*k`, every `m ∈ pre` has `m.length ≤ B`, and
`(Strategy.encodeMsgs pre).length ≤ (j*k)*(2*B+2)`.
[PS10, Theorem 175.1; Gol01, §4.3.4, bounded real-prefix reduction advice].

**Proof sketch.** The public coin-table equivalence supplies a raw tape with exactly the
requested independent phase blocks. The real-prefix endpoint reader identifies the fold
with the repeated execution on that tape. Its boundary reader gives exactly `j*k` received
messages. Each repeated-prover reply is either an original bounded message or an empty
filler, by the specification's public reply equation. This is the
public theorem `next_length_le`. The public execution-message bound
therefore controls every received message. Finally reuse the execution encoding bound,
which already invokes the generic public encoded-word length theorem. -/
theorem realPrefix_bounds {π ρ : Protocol} {x : List Bool} {q p : ℕ}
    (d : PaddedProverSpec π ρ x q p) (V : Strategy) (y z rV : List Bool)
    (j : ℕ) (hj : j ≤ q) (B : ℕ)
    (hbound : ∀ r hist, (π.P.next x y r hist).length ≤ B)
    (coins : Fin j → π.P.Coins x.length) :
    (realPrefix π V x y z rV p j coins).length = j * π.rounds.eval x.length ∧
    (∀ m ∈ realPrefix π V x y z rV p j coins, m.length ≤ B) ∧
    (Strategy.encodeMsgs (realPrefix π V x y z rV p j coins)).length ≤
      (j * π.rounds.eval x.length) * (2 * B + 2) := by
  -- Reconstruct one raw tape whose blocks are the supplied typed phase coins.
  let e : (Fin (j * π.P.coinLen x.length) → Bool) ≃ (Fin j → π.P.Coins x.length) :=
    coinTableEquiv rfl
  let tape := List.ofFn (e.symm coins)
  have hblocks (i : Fin j) :
      coinBlock (π.P.coinLen x.length) i tape = List.ofFn (coins i) := by
    have hblock := coinTableEquiv_block (m := j * π.P.coinLen x.length)
      (q := j) (c := π.P.coinLen x.length) rfl (e.symm coins) i
    have hinverse := congrArg (fun table : Fin j → π.P.Coins x.length =>
      List.ofFn (table i)) (e.apply_symm_apply coins)
    exact hblock.trans hinverse
  have hend : realPrefix π V x y z rV p j coins =
      (exec ρ.P V π.verifierFirst x y z tape rV
        (2 * π.rounds.eval x.length * j)).2 :=
    d.realPrefix_eq_exec V y z tape rV j hj coins hblocks
  have hcount : (realPrefix π V x y z rV p j coins).length =
      j * π.rounds.eval x.length := by
    rw [hend]
    exact (d.boundary V y z tape rV j).2
  -- Empty fillers satisfy the same cap as the original real replies.
  have hsource (hist : List (List Bool)) : (ρ.P.next x y tape hist).length ≤ B :=
    d.next_length_le y B hbound tape hist
  have hmessages : ∀ m ∈ realPrefix π V x y z rV p j coins, m.length ≤ B := by
    rw [hend]
    exact exec_snd_bounded ρ.P V π.verifierFirst x y z tape rV B
      (2 * π.rounds.eval x.length * j) hsource
  -- Reuse the existing execution-specific encoded-history estimate.
  have hencoding : (Strategy.encodeMsgs (realPrefix π V x y z rV p j coins)).length ≤
      (j * π.rounds.eval x.length) * (2 * B + 2) := by
    rw [hend]
    have hencoded := length_encodeMsgs_exec_snd_le ρ.P V π.verifierFirst x y z tape rV B
      (2 * π.rounds.eval x.length * j) hsource
    rw [(d.boundary V y z tape rV j).2] at hencoded
    exact hencoded
  exact ⟨hcount, hmessages, hencoding⟩

end TCSlib.Cryptography.SequentialZK.PaddedProverSpec

## ===== TCSlib/Cryptography/Composability/SequentialZK/ProofTransfers.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.PaddedProverSpec
import TCSlib.Cryptography.ZeroKnowledge.InteractiveProofs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Completeness transfer through a padded-prover contract

## Main definitions

This module introduces no definitions.

## Main results

* `PaddedProverSpec.next_length_le`: repeated replies keep an original message-length bound.
* `PaddedProverSpec.complete`: pointwise acceptance transfer preserves the bounded
  completeness clause, using the published witness-completeness constructor.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.1 (sequential repetition of interactive proofs).
-/

namespace TCSlib.Cryptography.SequentialZK.PaddedProverSpec

open Complexity

/-- For `d : PaddedProverSpec π ρ x q p`, auxiliary input `y`, bound `B`, and an original
reply bound `∀ r hist, |π.P.next x y r hist| ≤ B`, every repeated reply has length at most
`B`: `∀ r hist, |ρ.P.next x y r hist| ≤ B`. [PS10, Theorem 175.1]. -/
theorem next_length_le {π ρ : Protocol} {x : List Bool} {q p : ℕ}
    (d : PaddedProverSpec π ρ x q p) (y : List Bool) (B : ℕ)
    (hB : ∀ r hist, (π.P.next x y r hist).length ≤ B) :
    ∀ r hist, (ρ.P.next x y r hist).length ≤ B := by
  intro r hist
  rw [d.next]
  dsimp only
  split_ifs <;> first | exact hB _ _ | exact Nat.zero_le _

/-- For pointwise construction contracts `d`, if acceptance on every `x,y,z` transfers
from `π` to `ρ`, then a bounded completeness witness for each `x ∈ L` in `π` is also one
in `ρ`, with the same polynomial bound. [PS10, Theorem 175.1].

**Proof sketch.** Use the original reply bound and perfect acceptance together as a witness
relation. The padded next-message reader preserves that bound. The published bounded-witness
completeness constructor then uses the transferred acceptance on every such witness. -/
theorem complete {π ρ : Protocol} {L : Language Bool} {q p : List Bool → ℕ}
    (d : ∀ x, PaddedProverSpec π ρ x (q x) (p x))
    (haccept : ∀ x y z, (uprob (fun r : π.ExecCoins π.P x =>
      π.outV π.P x y z r = [true]) = 1) →
        uprob (fun r : ρ.ExecCoins ρ.P x => ρ.outV ρ.P x y z r = [true]) = 1)
    (hc : ∃ B : PolyExpr, ∀ x ∈ L, ∃ y : List Bool,
      (∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length) ∧
        ∀ z, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1) :
    ∃ B : PolyExpr, ∀ x ∈ L, ∃ y : List Bool,
      (∀ r hist, (ρ.P.next x y r hist).length ≤ B.eval x.length) ∧
        ∀ z, uprob (fun r : ρ.ExecCoins ρ.P x => ρ.outV ρ.P x y z r = [true]) = 1 := by
  obtain ⟨B, hcomplete⟩ := hc
  let R : List Bool → List Bool → Prop := fun x y =>
    (∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length) ∧
      ∀ z, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
  have hbounded : ρ.ProverBounded R B := by
    rw [Protocol.proverBounded_iff]
    intro x y r hist hR
    exact (d x).next_length_le y (B.eval x.length) hR.1 r hist
  exact hbounded.exists_complete hcomplete (fun x y hR z => haccept x y z (hR.2 z))

end TCSlib.Cryptography.SequentialZK.PaddedProverSpec
