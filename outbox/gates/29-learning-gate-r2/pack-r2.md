# Gate 29 · PRF concepts are not efficiently predictable (`learning`, Theorem 179.1(b)) · round 2

The auditor is Codex. Round 1 was HOLD (0/2/0/0); its findings are `findings/gate29-learning-findings.md` (SHA-256
`4f304ba7…`). This round re-audits the two majors, the two resolution edits and the rebase. The round-1 pack
(`pack.md`) still defines the scope; its questions stand for anything round 1 left unverified.

- **PR:** draft [PR #313](https://github.com/Shilun-Allan-Li/tcslib/pull/313), now at
  `2b6c29816de4cb1cd0e6b74fa3ae848c9f0f1be9` (branch `land/pass-shelat-learning`, tree
  `34ebd47d02248455919f7eda5dfc17f0090e34f3`). Round 1 audited `8befc58966fd39f974a54250849736df194584b9`.
- **Base:** `6ce4658db08a1dc2a03a149987197660db078011`, the merge base with the records tip
  `540bac18ce13cb8ef37b7dc41d97de5d2deaf661` (records only since `6ce4658d`). Round 1's base was `4561c340`.
  The PR was **rebased** (§ 3).
- **New since round 1:** two resolution edits, both by the maintainer (author and committer Claude, SSH-signed), each
  touching only `Randomness/Learning/Random.lean`:
  - **LE-gate29a** `94b31964ee94b97bf3ed3b4b4338cacae8183194` on `8befc589`, rebased as
    `9b40c7cee73c98a95eae5ea47f96e5b4c163adf7` (G29-01; +2/−5);
  - **LE-gate29b** `2b6c2981` on `9b40c7ce` (G29-02; +4/−4), after #316 merged.
- **Pushed:** the maintainer force-pushed the rebased branch with lease, with Seyoon's approval (decision-log row
  "sc-garble and sc-compose reviewed", 2026-11-15). `refs/pull/313/head` is `2b6c2981`.
- **Resolutions:** `resolutions-r1.md`, and the decision-log rows of 2026-11-15 (in `verification-r2.zip`).
- **Pending merge condition** (not an audit item; § 5): whichever of #313 and another open PR with a shared
  downstream merges second needs an integration rebuild on the merged tip; the maintainer runs that build.

Lean paths below are under `TCSlib/Cryptography/` unless they start with `TCSlib/`; `L/` is `Randomness/Learning/`.

## What to check

### 1. G29-01: is LE-gate29a proof only, and does `hj` now use `OneWay.uexp_const`?

The diff is `landing-r1/0001-LE-gate29a.patch` (= `git format-patch -1 94b31964`). In
`abs_gameProb_random_sub_half_le`, local `hj`, after `intro j` and `rw [uprob_prod]`, the four lines

```lean
    simp only [uprob_eq_point, uexp_def, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (0 : ℝ) < Fintype.card ((Fin m → Fin n → Bool) × ρ) := by
      exact_mod_cast Fintype.card_pos
    field_simp
```

become your proposed shape `simp only [uprob_eq_point, OneWay.uexp_const]`. The docstring's sketch parenthesis
"(`uprob_prod`, `uprob_eq_point`)" gains ", `OneWay.uexp_const`" (a pure insertion). No import changes:
`OneWay.uexp_const` is already used in `hdev`, and the averaging type is nonempty by the theorem's `[Nonempty ρ]`.

Check that the header is unchanged, that only this body and that parenthesis changed, and that the new step uses
`OneWay.uexp_const` as published. Re-checked for this pack from git objects (`checks/lecheck.txt`): the commit touches
`L/Random.lean` only (+2/−5, two hunks), its 11 declarations keep their headers and imports, and only
`abs_gameProb_random_sub_half_le`'s docstring changes. The rebased commit `9b40c7ce` has the same patch.

**Evidence** (`landing-r1/`): `gate29-le-a-evidence.zip` (SHA-256
`b1ce1c5057d7b836d0546562a7f7dab503e4b5237fb28939bcf61ffc96fcffb2`; 289 entries: 34 directories, 255 files = the 254
paths of its manifest `evidence-SHA256SUMS` plus `SHA256SUMS`) and its `PROVENANCE.txt`. At `94b31964`, on the old
base: decls2 against the parent empty, 63 headers compared and 0 different; 66/66 rc 0; axioms standard;
seals strict A/B and coe A/B pass (requests 1732/1733/1731/1732, the
LE-reuse sets row for row); paired controls (`uprob`, `uexp`, `PAC.label`, and in B `PolyExpr.eval`) 4 probes and 7
sealed negatives per variant, ALL_OK; lint 92/101 unchanged. Its build is superseded at the head by § 2's
integration build.

### 2. G29-02: is `firstBit_of_pos` now the published `TCSlib.Cryptography.headD_drop_ofFn`?

The promotion ruled at G29-02 is merged: #316 (`1c09448c`, Gate 32 CLOSED by disposition) put
`TCSlib.Cryptography.headD_drop_ofFn {α} {n} (f : Fin n → α) (i : Fin n) (d : α) :
((List.ofFn f).drop i.val).headD d = f i` in `Foundations/BitLists.lean:61`, and re-derived
`LamportFill.headD_drop_ofFn` from it. LE-gate29b (`checks/le-gate29b.diff` in the round-2 evidence):

```lean
-- before (round 1)
theorem firstBit_of_pos (y : Fin n → Bool) : firstBit y = y ⟨0, hn⟩ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [firstBit_eq, List.ofFn_succ, List.headD_cons]
  rfl
-- after
theorem firstBit_of_pos (y : Fin n → Bool) : firstBit y = y ⟨0, hn⟩ := by
  rw [firstBit_eq]
  simpa only [List.drop_zero] using TCSlib.Cryptography.headD_drop_ofFn y ⟨0, hn⟩ false
```

and the docstring gains the line "This is the published `TCSlib.Cryptography.headD_drop_ofFn` at index `0`." No
import is added: `Foundations/BitLists` was already in `Random`'s closure (also at round 1), and its blob at the head
equals the tip's.

Check that the statement is unchanged and the proof is the published lemma at index `0` (your proposed shape, with
the shared reader instead of the Lamport one). Re-checked from git objects (`checks/lecheck.txt`): one file, +4/−4, two
hunks; 11 declarations, headers and imports identical; only `firstBit_of_pos`'s docstring changes.

**Evidence** (`landing-r2/`): `gate29-le-b-evidence.zip` (SHA-256
`66898704b4fb1734ebc64df691fcdb3ae6623d440ddb88ac45c6fbfb19b5b43a`; 499 entries: 37 directories, 462 files = the 461
paths of `evidence-SHA256SUMS` plus `SHA256SUMS`) and its `PROVENANCE.txt`. At `2b6c2981`:
- **Statements:** decls2 against `9b40c7ce` empty; `touched` 1 CHANGED (`firstBit_of_pos`), 60 UNCHANGED; the frozen
  check against the parent: every header and definition body identical, the one difference the instructed prose
  insertion.
- **Integration build** (`build/`): 268/268 rc 0, 0 errors in both forms (G26-N1), substring "error" 0. The 268
  modules are every module changed since `eff2dcd0` that the seeds need (#303, #305–#309, #311, #312, #314–#317) and
  their downstream, the 5 unit modules, `Randomness`, root `TCSlib` and both `audits/*/Checks`. The 5 Learning modules
  have 0 warnings and 0 sorries. This is **#313's integration build against #314–#317**. Whole-tree check (1253
  modules): RESULT OK. Every built source equals its blob at `2b6c2981` and in the tree merged with the tip
  (`checks/srcequality.txt`).
- **Axioms:** `predictAdv_prfConcept_negligible` (b) and `not_weakLearnsUnder_prfConcept` (c) use
  `[propext, Classical.choice, Quot.sound]`; `firstBit_of_pos`, `firstBit_flip0` and `headD_drop_ofFn` use
  `[propext]`.
- **Admissions:** 39 at the tip (after #317 discharged `MAC/FromPRF`) → 38; the only other difference is
  `Randomness/Learning` 1 → 0.
- **Rule 10** (`rule10/`): `L/Random.lean` sealed in strict A/B (1753/1754 requests) and coe A/B (1752/1753), all pass
  (rc 0, 0 errors, install and EOF records), run with `-DmaxErrors=0`. The collector stores 11 constants for `Random`
  (LE-a: 12; one fewer after the proof change, the 11 public declarations unchanged). Paired controls on the strict and
  coe records: 4 probes and 7 sealed negatives each, `ctlcheck-strict.log` and `ctlcheck-coe.log` ALL_OK.
- **Lint:** 92 FAIL / 101 WARN at the tip `6ce4658d`, the parent and the head, with identical line sets.
- **Restore:** `dl-oleans` back at `457ba704…`, tree check OK.

The other four unit files were not re-sealed: they are byte-identical at `8befc589` and `2b6c2981`, and their closures
gained only the base delta of § 3. Is carrying their round-1 seals forward sound?

### 3. The rebase: is the PR the round-1 PR plus the two edits?

- **Range-diff** (`checks/rebase.txt`): `git range-diff 4561c340..94b31964 6ce4658d..9b40c7ce` is 6/6 `=` (the 3
  worker commits, LE-doc, LE-reuse, LE-gate29a). The 5 unit files are byte-identical at `94b31964` and `9b40c7ce`, so
  `git diff 8befc589 2b6c2981` is exactly LE-gate29a plus LE-gate29b. All 7 commits from `6ce4658d` are authored and
  committed by Claude and carry one `gpgsig` each.
- **Headers since round 1** (`checks/lecheck.txt`): all 61 declarations of the 5 files (9, 27, 5, 9, 11) have
  byte-identical headers at `8befc589` and `2b6c2981`, in order; every definition block is identical; only the
  docstrings of `firstBit_of_pos` and `abs_gameProb_random_sub_half_le` change. decls2 `8befc589` → head is empty (56
  public declarations unchanged); against the new base it is 47 ADDED, 0 CHANGED, 0 REMOVED (as round 1).
- **The base delta** (`checks/basemove.txt`). From `4561c340` to `6ce4658d` six PRs merged: #311 and #312, which were
  already in round 1's records tip `f52a24be` and covered by round 1's pack, and **#314–#317**, new. The `.lean` delta
  since `f52a24be` is 16 files; four of them are in the unit's closure at the head: `Pseudorandom/Functions/Defs`
  (#314), `Encryption/PrivateKey/FromPRF/ReductionMachine` and `Pseudorandom/Functions/Asymptotic/Defs` (#315) and
  `Foundations/BitLists` (#316). The closure grows from 138 to 141 modules: `Games/Advantage`,
  `Games/Bridges/Experiments` and `Games/Probability`, through #314's `Functions/Defs`. § 2's build covers all of it.
- **`sources-r2.zip`** (141 files) is round 1's `sources.zip` (138) plus those three modules; it differs in five
  entries, the four delta modules and `L/Random.lean`.
- **`source-head-r2.json`** differs from `source-head.json` only in `L/Random.lean` (189 → 186 lines, SHA-256
  `a47fda9d…`, none over 100 characters).
- **`pr.diff-r2.txt`** is `git diff origin/cryptography/pass-shelat-ch2-4...2b6c2981`, which equals `6ce4658d..2b6c2981`
  byte for byte (5 paths, 856 insertions, 13 deletions).

Does the rebase, or the base delta, introduce anything that round 1 would have raised?

### 4. Duplication: is there any new undisclosed copy since round 1?

- **Since round 1** (`checks/dupscan.txt`): the only headD/getD-of-`List.ofFn` reading line in `git diff 8befc589
  2b6c2981` is the removed `rw [firstBit_eq, List.ofFn_succ, List.headD_cons]`; LE-gate29b adds a call of
  `headD_drop_ofFn` and nothing else of that class. LE-gate29a removes an inline sum and cancellation and adds a call of
  `OneWay.uexp_const`. No new declaration is added (the 61 names are those of round 1).
- **The pre-existing copies.** DL-47 (in `verification-r2.zip`) lists the pre-existing headD/getD copies across the
  library, the Gate 32 extension (G32-01, 16 more) and sc-garble's SG-F04. None is in a #313 file. **They are not
  findings** (Seyoon's rulings: "Ledger row, dispatch now" at Gate 32 staging; "extend DL-47 and close" at G32-01).
- **DL-45** (the learning overlaps of round 1) is unchanged: items 1–2 paid by LE-reuse, the rest deferred.
- **Any further undisclosed duplicate of a public lemma is a major**, as in round 1. The round-1 search list stands.

### 5. The merge interaction

`git merge-tree --write-tree 2b6c2981 <x>` is clean for each (`checks/mergetrees.txt`); no path is shared with any.

| `<x>` | head | merged tree | downstream of both (`checks/downstream.txt`) |
|---|---|---|---|
| the tip | `540bac18` | `aa6daa9b` | none (records only since the base) |
| #318 (sc-ot) | `f62a25b3` | `8ad47d31` | root `TCSlib` |
| #319 (canonizer) | `6421ac16` | `dfcec563` | `Randomness`, root `TCSlib` |
| #323 (sc-garble) | `cd9a4843` | `34984d25` | 7: the 5 unit modules, `Randomness`, root `TCSlib` |
| #324 (sc-compose) | `a6eaebd7` | `828d6685` | root `TCSlib` |

- **#323** changes `TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean` (the approved reader `isFaninTwo_iff`), which
  is in the unit's closure; so every unit module is downstream of both. No other open PR changes a module of the
  unit's closure.
- Of the 268 built modules, all have the tip-merged source; 267 have #318's, #319's and #324's merged source, and 264
  #323's (`checks/srcequality.txt`). None of the 52 new short names is declared in a file another PR changes
  (`checks/namecheck.txt`).
- **Pending merge condition (not an audit item).** The combined trees are **not** built. Whichever of #313 and #318,
  #319, #323 or #324 merges second needs an integration rebuild of the shared downstream on the merged tip before it
  merges (with #323: the unit modules, `Randomness` and root `TCSlib`); the maintainer runs that build. Treat it as a
  condition on the merge, not as something for this audit to establish. What you can raise: a concrete reason a
  merged tree cannot build, or a name or instance interaction.

## Known dispositions and slips (not findings)

- **"PUSH: NOT DONE" in `landing-r2/PROVENANCE.txt`** (and `landing/push.log` in the ZIP): written when the job's own
  push was refused. The maintainer then force-pushed `2b6c2981` with lease, with Seyoon's approval; the remote head is
  that commit.
- **The PR description is still round 1's.** It lists LE-doc and LE-reuse but not the rebase, LE-gate29a or LE-gate29b;
  the maintainer updates it before #313 is marked ready (it is not in this pack).
- **LE-a's build ran on the old base** (66/66 at `94b31964`). It is kept for the record of LE-gate29a; LE-b's
  integration build is the evidence for the head.
- **Job-local names.** `landing-r1/PROVENANCE.txt` and `landing-r2/PROVENANCE.txt` refer to `../gate29-le-a-evidence.zip`
  and `../gate29-le-b-evidence.zip` and to `$SP` paths; the records copies have the same bytes.
- **The decision log's G29-02 wording** says "promote `LamportFill.headD_drop_ofFn`"; the promoted name is
  `TCSlib.Cryptography.headD_drop_ofFn`, and the Lamport lemma remains as a re-derived reader (Gate 32).

## Evidence files

- **`resolutions-r1.md`:** the dispositions of G29-01 and G29-02.
- **`findings/`:** the round-1 findings (and their `SHA256SUMS`).
- **`landing-r1/`:** the LE-gate29a patch, `PROVENANCE.txt` (= the ZIP's), `gate29-le-a-evidence.zip` and its manifest.
- **`landing-r2/`:** `PROVENANCE.txt` (= the ZIP's), `gate29-le-b-evidence.zip` and its manifest (the LE-gate29b patch
  is the ZIP's `landing/0001-…patch`).
- **`verification-r2.zip`** (22 entries; `SHA256SUMS` lists every other entry, and `PROVENANCE.txt` gives each source):
  byte-identical originals at records `540bac18ce13cb8ef37b7dc41d97de5d2deaf661` of the decision log, the duplication
  ledger (DL-45, DL-47), the Gate 32 resolutions and the round-1 review; and `checks/`, generated from git objects
  alone (merge trees, downstream, source equality, names, the rebase, the edits, the base move, the duplication scan,
  decls2), with their scripts.
- **`pr.diff-r2.txt`:** `git diff` from the base to `2b6c2981`, 5 paths, 856/13.
- **`source-head-r2.json`:** hashes, line counts and over-width counts of the 5 changed files at `2b6c2981`.
- **`sources-r2.zip`:** the source closure at `2b6c2981` of every changed module, 141 files.
- **Round 1:** `outbox/gates/29-learning-gate/` on the exchange at `341f61def10e0481a7c29fa4787a80d6ece7d5df`, with
  records `7bd85992f8bd61df48f43092bc5c845d5fac1b27`; `pack.md` here is its pack.

## Findings delivery

Return `gate29-learning-r2-findings.md` as Markdown in this chat. If you have several evidence files, return a ZIP.
Use the same table and severities as round 1, and say for each round-1 finding whether it is closed. Report the audited
head and the counts by severity. The gate closes at zero blockers and zero majors.
