## ===== briefs/pass-shelat-ch5-8/gates/29-learning/pack-r2.md =====

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

## ===== briefs/pass-shelat-ch5-8/gates/29-learning/resolutions-r1.md =====

# Gate 29 · resolutions, round 1 · HOLD → round 2

Codex's verdict is **HOLD**: 0 blockers, 2 majors, 0 minors, 0 notes.
- **Findings:** `findings/gate29-learning-findings.md`.
- **Audited head:** `8befc58966fd39f974a54250849736df194584b9`.
- Codex found the proof correct, part (c) sorry-free and the frozen statements intact. The seals and controls pass.
  Both majors are re-proofs that the review missed and nobody disclosed.

| # | Severity | Disposition |
|---|---|---|
| G29-01 | major | **Fixed by LE-gate29a, proof only** (`94b31964ee94b97bf3ed3b4b4338cacae8183194`, tree `b283709e`). The four-line calculation in `hj` is now `simp only [uprob_eq_point, OneWay.uexp_const]`, no new import; the sketch names the lemma. `decls2` empty, headers 63/63 identical. Evidence `landing-r1/gate29-le-a-evidence.zip`, SHA-256 `b1ce1c5057d7b836d0546562a7f7dab503e4b5237fb28939bcf61ffc96fcffb2`. Pushed to #313. |
| G29-02 | major | **Ruling (Seyoon, 2026-11-15): promote it now.** The new `firstBit_of_pos` re-proves the zero-index case of the public `LamportFill.headD_drop_ofFn`. A small PR promotes `headD_drop_ofFn` to a shared list layer that is upstream of both consumers, and re-derives Lamport's copy proof-only. After that PR merges, #313 re-points `firstBit_of_pos` (LE-gate29b), and Gate 29 round 2 follows. |

## ===== briefs/pass-shelat-ch5-8/gates/29-learning/findings/gate29-learning-findings.md =====

# Pass–shelat Gate 29 — learning

**Verdict: HOLD.** The proof, frozen statements and supplied seal evidence pass inspection. Two further undisclosed re-proofs remain outside the worker’s overlap table and DL-45. Under the pack’s severity rule, both are majors.

| Blocker | Major | Minor | Note |
|---:|---:|---:|---:|
| 0 | 2 | 0 | 0 |

| Pin | Audited revision |
|---|---|
| PR | [Shilun-Allan-Li/tcslib #313](https://github.com/Shilun-Allan-Li/tcslib/pull/313), draft |
| Lean head | `8befc58966fd39f974a54250849736df194584b9` |
| PR base | `4561c3407f9f015da55255a6a4cbcfc5840fd1f3` |
| Campaign records | `7bd85992f8bd61df48f43092bc5c845d5fac1b27` |
| Exchange | `341f61def10e0481a7c29fa4787a80d6ece7d5df` |

## Findings

All source line numbers below refer to the audited head.

| ID | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G29-01 | major | `Randomness/Learning/Random.lean:172–179`, local `hj` in `abs_gameProb_random_sub_half_le` | The remaining collision calculation re-proves the public constant-average lemma inline. | After `uprob_prod` and `uprob_eq_point`, lines 176–179 expand `uexp_def`, sum the constant, prove positive cardinality and cancel the denominator. This is `OneWay.uexp_const`, `OneWayFunctions/Basic.lean:69–73`, already public at the PR base and already called at line 170. Neither the overlap table nor DL-45 discloses this additional re-proof. | Replace the constant-average calculation by `OneWay.uexp_const`; preserve the theorem header. |
| G29-02 | major | `Randomness/Learning/Random.lean:66–69`, `firstBit_of_pos` | This new public theorem independently re-proves the zero-index case of an existing public bit reader. | After `firstBit_eq`, its conclusion is `(List.ofFn y).headD false = y ⟨0, hn⟩`. Public `Authentication.LamportFill.headD_drop_ofFn`, `Authentication/Signatures/Lamport/MachineSpec.lean:195–199`, gives that equation at index `⟨0, hn⟩` after `List.drop_zero`. The reader is present and unchanged at the PR base. This overlap is absent from the worker’s table and DL-45. | Re-derive the theorem through an existing reader, or obtain an explicit disposition for this additional overlap. Importing the cited Lamport helper is acyclic; a shared reader can also avoid that additional import. |

### G29-01: exact remaining overlap

The unreused mathematical step is

```lean
uexp (fun _ : ((Fin m → Fin n → Bool) × ρ) => (1 : ℝ) / 2 ^ n)
  = (1 : ℝ) / 2 ^ n
```

The averaging type is finite and nonempty under the theorem’s existing hypotheses, exactly as required by `OneWay.uexp_const`. The surrounding Fubini step and point-mass specialization remain useful glue. The duplicated part is the subsequent sum-and-cancellation proof.

A replacement proof shape for `hj` is:

```lean
    intro j
    rw [uprob_prod]
    simp only [uprob_eq_point, OneWay.uexp_const]
```

This needs no new import. LE-reuse correctly repairs its two listed overlaps, but leaves this separate occurrence unchanged. DL-45’s coupling-bound disposition does not identify this constant-average re-proof.

### G29-02: exact specialization

The existing reader says

```lean
((List.ofFn y).drop i.val).headD false = y i
```

Specializing `i` to `⟨0, hn⟩` and rewriting `List.drop_zero` gives the new theorem’s entire conclusion after `firstBit_eq`. Its current proof instead splits the positive length and uses `List.ofFn_succ` and `List.headD_cons` to establish that conclusion again.

For example, after importing the cited helper, a replacement proof shape is:

```lean
  rw [firstBit_eq]
  simpa only [List.drop_zero] using
    (TCSlib.Cryptography.Authentication.LamportFill.headD_drop_ofFn y ⟨0, hn⟩)
```

The overlap table’s `firstBit` row explains its relationship to the owned `prfConcept`; it does not disclose this relationship to the existing bit reader. DL-45 records the flip operations and other named overlaps, but not `firstBit_of_pos`. The replacement snippets above were checked by statement matching, not by a new Lean run.

## Proof audit

The delivered proof establishes the frozen prediction statement on inspection, following the first-output-bit concept of [PS10, §8.1, Theorem 179.1, book p. 179](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf#page=191).

1. **Efficient distinguisher.** `exists_learnDist` calls the public `MultiMsg.exists_queryChain_nuppt` with zero message vectors and a polynomial-time learner/verdict machine. Its coin equivalence supplies exactly `m(n) + 1` uniform points and the learner’s coins. The public chain contract gives the stated verdict within budget `m(n) + 1`; it introduces no timeout discrepancy. The disclosed substitution for T1/T4 is valid.
2. **Real-game law.** `iid_uniform`, the product-uniform readers and `snocEquiv` identify the PAC experiment with the distinguisher’s acceptance probability. No conditioning excludes repeated points. Both sides interpret the learner’s prediction as `decide (output = [true])`, including all other output words.
3. **Random-function bound.** For positive `n`, `flipAt` is an involution of function tables. When the test point is absent from the examples, it preserves every example label and negates the test label. Uniform probability is preserved, so success equals its complement and is exactly `1/2`. The public coupling bound and the union bound then give

   \[
   |\operatorname{gameProb}-1/2|
   \le \Pr[\exists j,\ s_j=x]
   \le \sum_{j<m(n)}2^{-n}
   =m(n)/2^n.
   \]

4. **Negligibility.** The owned proof applies the triangle inequality to obtain

   \[
   \operatorname{predictAdv}
   \le \operatorname{prfAdv}+m(n)/2^n
   \qquad(n\ge1).
   \]

   `PRF.negligible_prfAdv` uses precisely the polynomial budget `m + 1`. Polynomial-times-exponential decay, addition and eventual domination finish the argument. The finite exception `n = 0` is handled by the cutoff `1`. With no examples, the empty union gives zero collision probability.

Part (c)’s complete source suffix, including its proof, is byte-identical to the PR base. It combines eventual prediction advantage at most `1/n` with `δ < γ` and the published PAC bridge. The final axiom prints for both (b) and (c) contain exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## Integrity and evidence checks

- **Pack:** all 17 `SHA256SUMS` entries verify. All 14 bundle sections match their pinned repository originals, allowing only the bundle’s framing newlines. Every one of the 138 source-closure files matches the Lean-head git blob.
- **Nested evidence:** `verification.zip` has exactly its 30 manifest paths plus `SHA256SUMS`. The review archive verifies all 488 manifest entries; the reuse archive verifies all 248. Their external and internal manifests agree, with no extra file entries.
- **Freeze:** exactly the five authorized Lean files differ from the PR base. All nine pre-existing declaration headers are byte-identical; there are 47 new public declarations. Part (c) is unchanged. The owned-file changes stay within the permitted imports, module prose, target sketch and target proof.
- **LE-doc:** only doc comments change in its four files. The 17 added formulas agree with their declarations and argument order; no documentation finding was found. The rewritten target sketch describes the delivered proof.
- **LE-reuse:** only `Random.lean` changes: the two disclosed proof bodies, one import and the two permitted docstring insertions. Both cited public lemmas instantiate correctly. `HybridLemmas` adds exactly one module to `Random`’s closure, from 123 to 124, with no cycle and no additional definition. Carrying forward the four unchanged files’ seals is justified.
- **Rule 10:** independently checked the request sets against the supplied catalogs and stored-term references, including matchers and private-name components; removed instrumentation to recover the exact pinned source bytes; and checked installation and EOF records. All 28 seal probes have zero errors: 20 at LE-doc, four for the base owned file, and four for final `Random`. The older base-seal revision `eff2dcd0` has the same 130 source files in the owned file’s closure as the PR base.
- **Controls:** recounted both diagnostic forms directly from raw logs. The canonical review controls have 16 probes and 46 sealed negatives; each negative fails once, reader positives pass, and unsealed controls pass. The strict review controls have 54 correct negative failures plus the disclosed 16 reader-positive failures, confined to `ctlUniformReader` and `ctlCoeReader` in eight sealed probes. Their type mismatches match the projection-coercion attribution. Final reuse controls pass in both variants, with seven sealed negatives per variant. No additional forbidden definition read was found.
- **Builds and axioms:** checked the raw 66-module final build records, their source hashes against the audited git head, their log hashes, and zero error/sorry counts. The supplied census covers 71 stored constants with the standard axiom union. The whole-tree check remains the supplied LE-doc check of 1245 modules; the pack’s separate combined-tree rebuild requirement for the PR merging second remains applicable.
- **Lint and size:** independently reran the final lint: 92 FAIL / 101 WARN, with exactly the same 193 FAIL/WARN lines as the supplied baseline. Files have 220, 275, 137, 174 and 189 lines; every line is at most 100 characters.

**Validation limit:** no Lean toolchain is installed in this audit environment. I independently checked source, manifests, import graphs, instrumentation and raw supplied execution evidence; I did not rerun Lean elaboration or the seals.

**Closure condition:** resolve G29-01 and G29-02 through reader-based proofs or explicit user dispositions, then supply validation for the revised head. No repository change, review submission, dispatch or merge was made by this audit.

**Notation:** `m(n)` means `m.eval n`; `ρ` is the learner’s coin type; `hn` proves `0 < n`; `i` is a bit index; `s_j` is example `j`; `x` is the fresh test point; `Pr` is uniform probability. Other names are the audited Lean declarations.

## ===== briefs/pass-shelat-ch5-8/gates/29-learning/landing-r1/0001-LE-gate29a.patch =====

From 94b31964ee94b97bf3ed3b4b4338cacae8183194 Mon Sep 17 00:00:00 2001
From: Claude <noreply@anthropic.com>
Date: Sun, 15 Nov 2026 07:09:59 +0000
Subject: [PATCH] learning resolution edit LE-gate29a: hj from
 OneWay.uexp_const (G29-01)
MIME-Version: 1.0
Content-Type: text/plain; charset=UTF-8
Content-Transfer-Encoding: 8bit

Gate 29 finding G29-01 (major): in abs_gameProb_random_sub_half_le (Randomness/Learning/
Random.lean), the local union-bound step hj re-proved the public constant-average lemma
OneWay.uexp_const inline (uexp_def, the sum of a constant, positive cardinality, field_simp).
After uprob_prod, hj now reads the point-mass probability with uprob_eq_point and averages the
constant 1/2^n with OneWay.uexp_const, already called in hdev; no new import.

Proof only: the theorem header and statement are unchanged. The proof sketch's lemma list for
Σ_j Pr[s_j = x] = m · 2^{-n} gains OneWay.uexp_const. G29-02 (firstBit_of_pos) waits for the
headD_drop_ofFn promotion and is not part of this edit.

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA
---
 TCSlib/Cryptography/Randomness/Learning/Random.lean | 7 ++-----
 1 file changed, 2 insertions(+), 5 deletions(-)

diff --git a/TCSlib/Cryptography/Randomness/Learning/Random.lean b/TCSlib/Cryptography/Randomness/Learning/Random.lean
index c2e90978d..910b1ef92 100644
--- a/TCSlib/Cryptography/Randomness/Learning/Random.lean
+++ b/TCSlib/Cryptography/Randomness/Learning/Random.lean
@@ -141,7 +141,7 @@ proof, step 2]: for `n ≥ 1`, every learner `ℓ` and `m` examples,
 (`uprob_flip_half`) and in `[0, 1]` otherwise, so `|p − ½| ≤ [x ∈ s]`. Averaging (the
 coupling bound `MultiMsg.abs_uexp_sub_le_uprob` against the constant `½`),
 `|gameProb − ½| ≤ Pr[∃ j, s_j = x]`, which the union bound (`uprob_exists_le`) bounds by
-`Σ_j Pr[s_j = x] = m · 2^{-n}` (`uprob_prod`, `uprob_eq_point`). -/
+`Σ_j Pr[s_j = x] = m · 2^{-n}` (`uprob_prod`, `uprob_eq_point`, `OneWay.uexp_const`). -/
 theorem abs_gameProb_random_sub_half_le {ρ : Type*} [Fintype ρ] [Nonempty ρ] (m : ℕ)
     (ℓ : (Fin m → (Fin n → Bool) × Bool) → ρ → (Fin n → Bool) → Bool) :
     |gameProb m (fun R : (Fin n → Bool) → (Fin n → Bool) => R) ℓ - 1 / 2| ≤ m / 2 ^ n := by
@@ -173,10 +173,7 @@ theorem abs_gameProb_random_sub_half_le {ρ : Type*} [Fintype ρ] [Nonempty ρ]
       t.1.1 j = t.2) = 1 / 2 ^ n := by
     intro j
     rw [uprob_prod]
-    simp only [uprob_eq_point, uexp_def, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
-    have : (0 : ℝ) < Fintype.card ((Fin m → Fin n → Bool) × ρ) := by
-      exact_mod_cast Fintype.card_pos
-    field_simp
+    simp only [uprob_eq_point, OneWay.uexp_const]
   have hunion := uprob_exists_le (Finset.univ : Finset (Fin m))
     (fun j (t : ((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool)) => t.1.1 j = t.2)
   simp only [hj, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hunion
-- 
2.43.0


## ===== briefs/pass-shelat-ch5-8/gates/29-learning/landing-r1/PROVENANCE.txt =====

#313 resolution edit LE-gate29a (Gate 29 G29-01, proof only), maintainer, 2026-11-15 UTC
$SP = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad. Paths below are relative to this directory.
Rules: python3 -I throughout; Lean 4.25.0, PATH=$HOME/.elan/bin:$PATH; one Lean process at a time (of this job), only
  scripts/lean_check_tree.sh through tools-used/review/runner.py (the G26-N1-fixed runner) with TCSLIB_OLEANS=$SP/dl-oleans-2
  (dl-oleans not touched); no lake command; nothing pushed; /home/user/tcslib working tree not edited (only `git fetch` there).
  Run after Job B (gate30-le), whose restore left the tree at the base snapshot.
Method and tools: as learning-r1-reuse (its zip from briefs/pass-shelat-ch5-8/fills/learning/final-r1/landing-reuse/, SHA-256
  5df65c56dce59c51558df1399e634f59708f4caaee6cd63027be270a8454fc52 = evidence-SHA256SUMS, extracted to a fresh directory and
  verified); tools-used/review/ and mkctl_reuse.py, sealrows.py = its copies, unmodified (review/ also equal to promote-prfadv's).
Finding: Gate 29 G29-01 (major): the local `hj` in abs_gameProb_random_sub_half_le (Random.lean:172-179 at 8befc589) re-proves
  the public OneWay.uexp_const (OneWayFunctions/Basic.lean) after uprob_prod / uprob_eq_point. G29-02 is not part of this job
  (it waits for the headD_drop_ofFn promotion, dl-review/promote-headd).

landing: branch land/pass-shelat-learning, worktree $SP/wt-land-learning (sparse, briefs/ excluded; .lake/packages link; from
  the review, clean at 8befc589 = origin/land/pass-shelat-learning after `git fetch`; removed at the end of this job, branch kept).
  parent LE-reuse     8befc58966fd39f974a54250849736df194584b9 (origin head, #313)
  head   LE-gate29a   94b31964ee94b97bf3ed3b4b4338cacae8183194, tree b283709ed6519a72ca5a3c0f72266481c754a728
  author = committer = Claude <noreply@anthropic.com>, SSH-signed by the environment default; message logs/commit-msg.txt
  ending with the two trailer lines (checks/commit.txt). Patch 0001-LE-gate29a.patch; diff checks/le-gate29a.diff (applied by
  tools-used/legate29a_edit.py, 2 exact replacements). checks/changed-paths.txt: one path, M .../Learning/Random.lean
  (189 -> 186 lines; max width 98 at both revisions, checks/widths.txt). Worktree clean at the head (checks/worktree-status.txt).

edit (Random.lean, abs_gameProb_random_sub_half_le):
  proof: in `hj`, after `intro j` and `rw [uprob_prod]`, the four lines
      simp only [uprob_eq_point, uexp_def, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have : (0 : ℝ) < Fintype.card ((Fin m → Fin n → Bool) × ρ) := by
        exact_mod_cast Fintype.card_pos
      field_simp
    are replaced by the finding's shape
      simp only [uprob_eq_point, OneWay.uexp_const]
    (OneWay.uexp_const is already used in hdev; no new import; the averaging type is nonempty by the theorem's [Nonempty ρ]).
  docstring: the sketch names the lemmas of the calculation Σ_j Pr[s_j = x] = m · 2^{-n}; its parenthesis
    "(`uprob_prod`, `uprob_eq_point`)" gains ", `OneWay.uexp_const`" (statements/docstring-delta.txt: pure insertion).
  Header and statement unchanged. The new proof compiled first time, with no warning.

statements (statements/; tools-used/review/ tools; unit-paths.txt = the 5 unit files):
  decls2-vs-parent.tsv and decls2.err (decls2.py over the 5 unit files): both empty.
  touched-parent-vs-head.tsv: 1 CHANGED (abs_gameProb_random_sub_half_le), 60 UNCHANGED.
  header-bytes-vs-parent.txt (headerbytes.py; touched-before.json = eff2dcd0 vs parent, touched-after.json = eff2dcd0 vs head;
    endpoints predictAdv_prfConcept_negligible (b), not_weakLearnsUnder_prfConcept (c)): 63 compared, 0 different or missing.
  docstring-header.txt (docheader.py): the theorem's keyword-to-`:=` header identical; the docstring differs by the insertion only
    (RESULT FAIL there is the docstring comparison, by design).

build (build/, order/C-build-queue.txt = learning-r1-reuse order/head-build-queue.txt, the same 66 modules in the same order;
  downorder.py head vs eff2dcd0; head-vs-parent/down.txt = Random, Learning, Randomness, root TCSlib): the tree starts at base, so
  the 66 modules are the #303/#306/#307/#308/#309 base delta and its downstream, the 5 unit modules (Sample, Distinguisher, Law,
  Random, Learning), Randomness, root TCSlib and audits/pass-shelat/Checks.
  66/66 rc 0, 0 errors (errors and errors_diag), 0 sorry; warnings all inherited (DDH 3, Lamport Blocks 2, InversionProbability 2,
  MachineSpec 2, Realization 1, Rejection 10, Extraction 2); Random 0 warnings (build/summary.txt).
  build/vs-reuse.txt (buildsum.py vs the learning-r1-reuse build): only Random differs (source and olean).
  build/refcmp.txt: 65 modules have a same-source reference with equal counts and byte-identical oleans (Learning, Randomness,
  TCSlib and Checks included); Random has none (edited).

axioms (axioms/; probe AxiomsHead.lean.txt run as LaProbe/AxiomsHead at 94b31964, rc 0):
  predictAdv_prfConcept_negligible (part (b)), not_weakLearnsUnder_prfConcept (part (c)), LearnPRF.abs_gameProb_random_sub_half_le
  (the target) and LearnPRF.uprob_eq_point: each [propext, Classical.choice, Quot.sound]. No sorryAx.

Rule 10 (rule10/), Random.lean at 94b31964 (tools-used/rule10.sh drives the review tools):
  collector probe-sources/CollectHead.lean.txt (mkcollect.py, owners rule10/order/head-owners.txt = Random), LaProbe/CollectHead
  rc 0, 2368 CAT lines (the reuse collector log has the same count), MODULE Random stored 12 (reuse: 12).
  seals: mkseals_ab.py strict -> seals/{A,B}; mkseals_coe.py coe -> seals-coe/{A,B}; B with SEAL_EVAL=1; mkseals-*.log.
    Requests strict A 1732, B 1733, coe A 1731, coe B 1732 = LE-reuse's. seal-rows-vs-reuse.txt (sealrows.py vs the reuse
    records): per variant 0 rows gone, 0 new, 0 changed; term readers and excluded terms equal.
    Runs seal-runs/ (order/seal-control-queue.txt, NOSTOP=1); sealsum.py with statements/touched-after.json: seals-A.tsv,
    seals-B.tsv, seals-coe-A.tsv, seals-coe-B.tsv: strict A pass, strict B pass, coe A pass, coe B pass (rc 0, 0 errors,
    install and EOF records present).
  paired controls (mkctl_reuse.py unmodified: rows uprob, uexp (rfl vs uexp_def), PAC.label, PolyExpr.eval (B)), on the strict
    records (seals-flat/ -> controls-strict/, LaProbe/KS) and the coe records (seals-coe-flat/ -> controls-coe/, LaProbe/K):
    4 probes each, 7 sealed negatives each (A: uprob, uexp, label; B: those and PolyExpr.eval). ctlcheck-strict.log,
    ctlcheck-coe.log (ctlcheck2.py): ALL_OK True (each sealed negative fails exactly once, readers and unsealed probes pass,
    no stray error).
  probe-copies-check.txt: the 14 worktree probe sources equal the copies here (LaProbe/ then removed).

lint (lint/): campaign_style_lint.py TCSlib/Cryptography --check8b: parent 8befc589 (git-archive export, removed) 92 FAIL /
  101 WARN over 347 files (byte-identical to learning-r1-reuse lint/lint-edit.log); head 92 / 101; FAIL and WARN lines identical
  (lint-parent-vs-head.diff empty); the full diff is Random.lean's INFO line (189 -> 186 lines). Lint unchanged.

olean tree $SP/dl-oleans-2:
  pre: tree/snapshot-pre.txt (1230 files) SHA-256 457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f (base).
  restore (restore/; restoreplan.py --delete vs snapshot-pre with order/base-topo-order.txt, the imports-first eff2dcd0 order):
    56 extra files deleted (46 oleans of modules new since eff2dcd0, 10 LaProbe oleans; the 4 sealed controls fail by design and
    leave none) with 11 emptied directories; 10 oleans differed; restore-list.txt = rebuild-order.txt (10 modules) rebuilt from
    the eff2dcd0 git-archive export (restore/base-export.txt; removed afterwards): 10/10 rc 0, every object hash equals the
    learning-r1 base record (buildsum.py: no difference).
  post: restore/tree-check-post.txt (treecheck.py, 1199 base modules, no stray olean, no empty dir, snapshot equals
    snapshot-pre): RESULT OK; tree/snapshot-post.txt byte-identical to snapshot-pre.txt, SHA-256
    457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f.

tools-used/: review/, mkctl_reuse.py, sealrows.py (learning-r1-reuse, unmodified); snap.py, restoreplan.py, docheader.py,
  docdelta.py, buildsum.py, refcmp.py (promote-prfadv, unmodified); new: legate29a_edit.py, widths.py, rule10.sh, probecopies.py.
SHA256SUMS: every file here except itself (paths without "./"); ../gate29-le-a-evidence.zip holds exactly these paths.

## ===== briefs/pass-shelat-ch5-8/gates/29-learning/landing-r2/PROVENANCE.txt =====

#313 (learning) LE-gate29b (Gate 29 G29-02, proof only) and #313's integration build against #314-#317, maintainer, 2026-11-15 UTC
$SP = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad. Paths below are relative to this directory.
Rules: python3 -I; Lean 4.25.0; one Lean process at a time, only on $SP/dl-oleans (dl-oleans-2 not touched); builds through
  scripts/lean_check_tree.sh via tools-used/review/runner.py (G26-N1); probes through tools-used/runner_full.py (lean -DmaxErrors=0,
  no -o); no lake command; the records checkout only read (git fetch, git worktree). Run after the sc-garble review, whose restore
  left the tree at the base snapshot. Method and tools: gate29-le-a (tools-used/ = its tools-used/ plus the sc-garble review's
  runner_full.py, frozencheck*.py, buildset.py, mancheck.py, snapshot.py, treecheck.py, restore.sh, sorrycensus.py); new:
  legate29b_edit.py, rule10_b.sh (rule10.sh with runner_full.py).

landing: branch land/pass-shelat-learning, worktree $SP/wt-land-learning (sparse, briefs/ excluded; .lake/packages link).
  - Rebase (landing/rebase.log): 94b31964 (= origin land/pass-shelat-learning = refs/pull/313/head) onto
    origin/cryptography/pass-shelat-ch2-4 6ce4658db08a1dc2a03a149987197660db078011 (1321b9cb + records-only commits; includes #314,
    #315 10b9be17, #316 1c09448c, #317 1d9b2ac3): rc 0, no conflict; range-diff 6/6 identical; the 5 unit files unchanged
    (landing/changed-paths-vs-origin.txt: 5 files +856/-13 incl. the edit). All commits SSH-signed by the environment default.
  - Edit commit 2b6c29816de4cb1cd0e6b74fa3ae848c9f0f1be9 "learning landing edit LE-gate29b: firstBit_of_pos from the published
    headD_drop_ofFn (G29-02)", tree 34ebd47d02248455919f7eda5dfc17f0090e34f3, parent 9b40c7ce (the rebased LE-gate29a), author =
    committer = Claude <noreply@anthropic.com>, message logs/commit-msg.txt with the two trailers; patch landing/0001-*.patch;
    commits landing/commits.txt. Worktree clean (checks/worktree-status.txt empty).
  - PUSH: NOT DONE. The authorised `git push --force-with-lease` was refused by the session's permission system; no workaround was
    tried (landing/push.log, with the exact command; the remote is still 94b31964).
edit (checks/le-gate29b.diff; tools-used/legate29b_edit.py, 2 exact replacements), Learning/Random.lean, firstBit_of_pos:
  proof `obtain ⟨k, rfl⟩ … ; rw [firstBit_eq, List.ofFn_succ, List.headD_cons]; rfl` replaced by
    rw [firstBit_eq]
    simpa only [List.drop_zero] using TCSlib.Cryptography.headD_drop_ofFn y ⟨0, hn⟩ false
  (compiled first time, no warning; no import added: Foundations/BitLists is already in Random's closure, build queue position 3).
  docstring: "This is the published `TCSlib.Cryptography.headD_drop_ofFn` at index `0`." inserted before `-/`
  (statements/docstring-delta.txt: removed '', inserted that line: pure insertion). Max width 98 -> 98, 0 lines over 100.
statements (statements/): decls2-vs-parent.tsv and decls2.err (decls2.py over the 5 unit files vs 9b40c7ce): both empty.
  touched-parent-vs-head.tsv: 1 CHANGED (firstBit_of_pos), 60 UNCHANGED. frozen-check-vs-parent.txt (frozencheck.py): every header
  and definition body identical; the single difference is the PROSE of firstBit_of_pos (the instructed docstring insertion; the
  docstring has no sketch). docstring-header.txt: header (keyword .. :=) identical True.
build (build/, order/buildset/build-queue.txt from tools-used/buildset.py: seeds = the 5 unit modules and both audits/*/Checks;
  base delta since eff2dcd0 = order/vs-eff2dcd0/changed.txt (74), excluded 0): 268 modules = every module changed since eff2dcd0
  that is needed (#303, #305-#309, #311, #312, #314-#317) and their downstream, the 5 unit modules, Randomness, root TCSlib,
  audits/pass-shelat/Checks and audits/garg-ch1-3/Checks. build/summary.txt: 268/268 rc 0, 0 errors (both forms), substring "error"
  0, 1605 s; the 5 Learning modules 0 warnings, 0 sorry; sorry warnings only in admitted modules. This is #313's integration build
  against #314-#317. tree/tree-check-head.txt (order/headfull-order.txt, 1253 modules; records admissions/records-head.jsonl =
  base records + build): RESULT OK.
axioms (axioms/AxiomsHead.lean.txt -> AxiomsHead.log, LaProbe/AxiomsHead rc 0): predictAdv_prfConcept_negligible and
  not_weakLearnsUnder_prfConcept [propext, Classical.choice, Quot.sound]; firstBit_of_pos, firstBit_flip0, headD_drop_ofFn [propext].
admissions (admissions/sorry-census.txt; sorrycensus.py over prf-long's issued base-sorries (= the integration builds' list, 40 in
  19 modules; issue base 7b307d62), records-head.jsonl): the tip count 39 (MAC/FromPRF discharged by #317) -> 38; the only further
  difference is Randomness/Learning 1 -> 0 (predictAdv_prfConcept_negligible, #313's target). 215 sorry warnings tree-wide (216 at
  int-317, minus this one).
Rule 10 (rule10/; tools-used/rule10_b.sh), Random.lean at 2b6c2981: collector LaProbe/CollectHead (= le-a's source; 2390 CAT
  lines; MODULE Random stored 11, le-a 12: one fewer stored constant after the proof change; the 11 public declarations are unchanged). Seals strict A 1753 / B 1754, coe A 1752 /
  B 1753 requests (B with SEAL_EVAL=1): seals-{A,B,coe-A,coe-B}.tsv all pass (rc 0, 0 errors, install and EOF records), runs with
  -DmaxErrors=0. Paired controls (mkctl_reuse.py unmodified: uprob, uexp, PAC.label, PolyExpr.eval in B) on the strict and coe
  records: 4 probes each, 7 sealed negatives each; ctlcheck-strict.log and ctlcheck-coe.log ALL_OK True.
lint (lint/): campaign_style_lint.py TCSlib/Cryptography --check8b: tip 6ce4658d 92 FAIL / 101 WARN (350 files), parent 9b40c7ce
  92/101 (354), head 92/101 (354); FAIL/WARN line sets identical (lint-tip-vs-head.diff, lint-parent-vs-head.diff empty). Exports
  removed.
trial merges (checks/trial-merges.txt): git merge-tree --write-tree of the head with #318 f62a25b3 clean (8ad47d31) and #319 6421ac16
  clean (dfcec563); no shared file; shared downstream #318: TCSlib; #319: Randomness, TCSlib.
olean tree $SP/dl-oleans: pre tree/snapshot-pre.txt 1230 files SHA-256 457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f;
  214 base oleans backed up (tree/backed-up.txt), 54 new listed (tree/new-oleans.txt); restore/restore-log.txt (tools-used/restore.sh):
  0 hash failures, 214 restored, 54 deleted, emptied dirs pruned (its snapshot call used a tools/ path absent here; the snapshot was
  taken with tools-used/snapshot.py); tree/snapshot-post.txt byte-identical to snapshot-pre.txt; restore/tree-check-post.txt: 1199
  base modules, snapshot equal: RESULT OK. Backups and LaProbe/ removed.
SHA256SUMS: every file here except itself (paths without "./"); ../gate29-le-b-evidence.zip holds exactly these paths plus SHA256SUMS.

## ===== briefs/pass-shelat-ch5-8/gates/29-learning/pack.md =====

# Gate 29 · PRF concepts are not efficiently predictable (`learning`, Theorem 179.1(b))

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #313](https://github.com/Shilun-Allan-Li/tcslib/pull/313) at
  `8befc58966fd39f974a54250849736df194584b9` (branch `land/pass-shelat-learning`, tree
  `5ad10b2805cd43d65c290e31b4140ca233ef1b9a`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `4561c3407f9f015da55255a6a4cbcfc5840fd1f3` (the merge base).
  - The fill was issued on `107f1e8c218733eac12d6b9bee6fece441271317`. Between the issue base and the PR base, the
    only merged PR that changes non-record files is #307 (dl-crh, merge `25fe1c05`). None of its 9 modules is in the
    unit's closure (review evidence `order/pr307-modules.txt`, `order/unit-closure.txt`).
  - From the PR base to the records tip `f52a24be7442013d00bef3608ce5336429dd4719` there are 22 commits. Their only
    non-record paths are #311's `SecureComputation.lean` and `SecureComputation/SpecialEncryptionMulti.lean`, #312's
    `Complexity/Randomized.lean` and `Complexity/Randomized/SeedMajority.lean`, and `machine-library-design.md`.
    Re-checked for this pack from git objects: no path is shared with the PR; none of those modules is in the import
    closure, at the head, of a changed module (138 files); the only tip module downstream of both a delta module
    and a PR module is root `TCSlib`. `git merge-tree --write-tree` of the tip with the head gives tree
    `0d41a4a2fd1a2c6fa9aceeb42878b3075a9c51ed` with no conflict.
  - `pr.diff.txt` is `git diff origin/cryptography/pass-shelat-ch2-4...8befc589`, which equals
    `4561c340..8befc589` byte for byte.
- **Commits:** 5.
  - The Claude worker's 3 commits (job `learning`), applied with `git am` with the delivered committer data (every
    worker hash reproduces) and rebased onto `4561c340` without conflict, author kept:
    `876145de248c691b5724a2d594ad3ab6b2744a17` (checkpoint 1: the distinguisher and the real game),
    `331c15f4d66e99537c59403b6bc77eb952a52e47` (checkpoint 2: the random function) and
    `b4caa53bb4a8f51e30789f282080ed0eb8d2827a` (Theorem 179.1(b) proved). At `b4caa53b` the 5 files are
    byte-identical to the worker's `src/` (worker head `f30d80f02aa3a79c8dd1bb6c674e1ba071b0f568`).
  - Landing edit **LE-doc** `7f5bdd510c15357ca8e4bc28ca74ec6bcdf211c1`: 17 formula docstrings; docstrings only.
  - Landing edit **LE-reuse** `8befc58966fd39f974a54250849736df194584b9` (the head): two proofs in `Random.lean`
    re-pointed to published lemmas, one import added, two docstrings extended; proof only.
- **Scope:** a **proof audit**. The job proves the admitted `Randomness.predictAdv_prfConcept_negligible` [PS10, §8.1,
  Theorem 179.1(b)]: if `F` is a PRF, every non-uniform PPT learner `A` with `m(n)` uniform labelled examples
  predicts the concept `prfConcept F n k` at a fresh uniform point with negligible advantage over `½`. Its statement
  passed the prong D statement phase (ruling D-5: the learning game is the PAC layer of `TCSlib/LearningTheory`) and
  Gate 06, and is frozen. Part (c), `not_weakLearnsUnder_prfConcept`, is proved from (b) at the base and is unchanged.
- **Brief:** `fills/learning/issued-r1/brief.md` on the records branch (SHA-256 `6f6c2648…`; exchange pack `2b9270ad`):
  three checkpoints following the docstring sketch (distinguisher and real game; random function; bound), the owned
  file plus the helper directory `Randomness/Learning/` only, `Games/Efficiency.lean` and every other file frozen,
  the binding duplication rule with an `## Overlap and reuse` section, Rule 10 with the projection-coercion ruling and
  seals with `PolyExpr.eval` both excluded and sealed, the G26-N1 error count, and the evidence-completeness rule.

## What changed

All paths are under `TCSlib/Cryptography/Randomness/`; `L/` is `Learning/`. The PR touches 5 Lean files: 1 modified
and 4 new (859 insertions, 13 deletions). Line counts are base → worker head `b4caa53b` → LE-doc `7f5bdd51` → PR head.

| File | Status | Lines |
|---|---|---:|
| `Learning.lean` | owned, modified | 149 → 220 → 220 → 220 |
| `L/Sample.lean` | helper, new | 259 → 275 → 275 |
| `L/Distinguisher.lean` | helper, new | 136 → 137 → 137 |
| `L/Law.lean` | helper, new | 173 → 174 → 174 |
| `L/Random.lean` | helper, new | 203 → 203 → 189 |

The facade `Randomness.lean` already imports `Learning`, which imports the four helpers; after #305 no facade edit is
needed, and none was made.

The proof follows [PS10, Theorem 179.1] and the frozen sketch (REPORT § 1, review § Content; the target's step list
was rewritten to describe the delivered proof):
1. **The distinguisher and the real game** (`Sample`, `Distinguisher`, `Law`): `LearnPRF.exists_learnDist` builds a
   next-query machine `B` whose coins are, by a bijection, `m(n) + 1` points and `A`'s coins. Its query tree with
   budget `m(n) + 1` evaluates to `decide (A(⟨S, ⟦ρ_m⟧⟩; c) = [true]) == firstBit (g ρ_m)`, where `S` is the sample of
   the first `m(n)` points labelled by `firstBit ∘ g`. `B` is the public query chain `MultiMsg.exists_queryChain_nuppt`
   with the zero message vector, applied to the machine that computes the learner's input and the last label from the
   encoded tuple, runs `A` and compares. `exists_learnDist_acceptProb` gives, for every keyed family `G`,
   `acceptProb G (oracleDist (B.toOracleAdversary n n n (m(n)+1))) = gameProb (m n) G (learnerFn A n (m n))`; the
   prediction game is the same uniform probability (`predictSuccess_eq_uprob`, through `iid_uniform`,
   `Rejection.uniform_prod`, `Rejection.uniform_probTrue`). In the owned file `learnerFn = learnerOf` and
   `firstBit ∘ F n k = prfConcept F n k`, through the owned readers.
2. **The random function** (`Random`, `abs_gameProb_random_sub_half_le`): for `n ≥ 1`,
   `|gameProb m (fun R => R) ℓ − ½| ≤ m/2^n`. For a fresh point `x`, flipping the first bit of `R x` (`flipAt`) is
   an involution that keeps the examples' labels and negates `x`'s, so the conditional success is exactly `½`
   (`uprob_flip_half`); otherwise it lies in `[0, 1]`. The coupling bound against the constant `½` and the union
   bound with `Pr[s_j = x] = 2^{-n}` (`uprob_eq_point`) give `m/2^n`.
3. **The bound** (owned file): for `n ≥ 1`,
   `predictAdv ≤ |acceptProb (F n) D − acceptProb R D| + |acceptProb R D − ½| ≤ prfAdv (F n) (D^{m(n)+1}) + m(n)/2^n`.
   This is negligible by `PRF.negligible_prfAdv` at budget `m + 1`, `EnsembleLemmas.negligible_polyExpr_mul` with
   `negligible_two_pow_neg`, and `Negligible.add`; `Negligible.mono` from `n = 1` makes `n = 0` a finite exception.

The edge cases are `n = 0` (steps 1 and 3 hold at every `n`; step 2 needs `n ≥ 1`), `m(n) = 0` (no examples, the
union bound is `0`), a fresh point equal to an example (no case split in step 1; the bad event of step 2), a learner
output other than `[true]` (`decide (… = [true])` throughout), and the query chain's timeout (exactly `m(n) + 1`
queries within the budget, so it is not reached).

**Statements:** decls2 from the issue base to the head gives 47 ADDED, 0 CHANGED, 0 REMOVED (review
`statements/decls2.tsv`, `head-le/decls2-vs-base.tsv`; LE-reuse `statements/decls2-vs-7f5bdd51.tsv`, empty). All 9
pre-existing declaration headers of `Learning.lean` are byte-identical, the target's and part (c)'s included. Only the
target's body and sketch changed, plus four imports, the module title, the Main-results line of part (b) and a new
`## Contents`. Re-checked for this pack from git objects with `maintainer/tools/decls2.py`'s parser: 47 ADDED and 9
unchanged against both the issue base and the PR base; 0 rows and 56 unchanged for `7f5bdd51..8befc589`.

## Rulings and records in force

1. **Rule 10: a `CoeFun`/`Coe` instance whose body is a structure projection is notation (Seyoon, 2026-11-14).** This
   is `FinDist`'s `⟨FinDist.prob⟩` (`FinDist.instCoeFunForallReal`). The coe-variant seals are canonical; the strict
   variant is still run and its differences attributed. **For this unit the seals agree in every row** (all five files
   pass A and B, strict and coe, at the head; the owned file also at the base; `logs/seal-table.txt`). The one
   strict-harness difference is in the controls: see the dispositions.
2. **`PolyExpr.eval` is notation (Q1, the user, 2026-11-07).** Seal A, which exempts it, is canonical; seal B is run
   and reported because the brief asks for both.
3. **The facade-completeness lint fix, #305 (Seyoon's ruling of 2026-11-14 to fix the bug by a PR on our branch).**
   The baseline at the issue base is **92 FAIL / 101 WARN** (the brief; #309 resolved one WARN of the 92/102 of
   #305's record). The records tip `4561c340`, the worker head `b4caa53b` and LE-doc `7f5bdd51` all give 92 / 101 with
   identical non-INFO line sets; LE-reuse (head) gives 92 / 101 with identical FAIL and WARN lines, the full diff being
   `Random.lean`'s INFO line (203 → 189 lines). Under the pre-#305 lint the four helpers would add 4 "facade does not
   import child module" FAILs (`lint/lint-old-diff.txt`), the class #305 fixed. No FAIL or WARN is new.
4. **LE-doc (the maintainer's landing edit): docstrings only.** 17 formulas for the new public declarations that the
   review's docaudit flagged NO-FORMULA (14 in `Sample`, 1 each in `Distinguisher`, `Law`, `Random`). With all doc
   comments blanked, the four files are byte-identical to the worker head (`landing/le-doc-doconly.txt` in
   `review-evidence.zip`; re-checked for this pack from git objects: `b4caa53b..7f5bdd51`, 4 files, 0 failing).
   Docaudit after: 47 OK; the one NO-FORMULA row is the frozen target's base prose. Sketches: every theorem with 15 or
   more proof lines has a `**Proof sketch.**` (4 theorems, `statements/sketchaudit-le.tsv`).
5. **LE-reuse (the maintainer's landing edit): proof only, done before the gate.** The review found two undisclosed
   restatements of public lemmas (findings 1 and 2). The brief makes undisclosed duplication a freeze violation, and
   the majors that held Gates 23 and 24 were of exactly this class (G23-01, a private copy of
   `length_le_length_encodeLog`; G24-01, `inputWord_take` re-proving `take_ofFn_castLE`, fixed by a maintainer
   LE-reuse on #307). So the maintainer re-pointed both before opening the PR rather than leave a known major for the
   gate (decision log 2026-11-15, "G24-01 precedent"). `Random.lean` only (`reuse-evidence.zip`:
   `0001-LE-reuse.patch`, `checks/le-reuse.diff`):
   - `LearnPRF.uprob_eq_point` is now proved from the public `OneWay.uprob_eq_one_div_card`
     (`OneWayFunctions/Basic.lean:144`, already in `Random`'s closure), reversing the equation and reading
     `|{0,1}^n| = 2^n`. Its docstring gains one `**Proof sketch.**` paragraph, a pure insertion.
   - In `abs_gameProb_random_sub_half_le`, the local `hpt`, `hcard` and the averaging proof of `hdev` (25 lines) are
     replaced by the public coupling bound `MultiMsg.abs_uexp_sub_le_uprob` (`FromPRF/HybridLemmas.lean:61`) with
     `a = p`, `b = fun _ => ½`, `E = bad`, plus `OneWay.uexp_const`. The three hypotheses are the old case split's
     branches. The sketch's "Averaging," gains a parenthesis naming the lemma, a pure insertion. The rest of the
     proof is unchanged.
   - One import, `TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas`. It was not in `Random`'s closure;
     it adds exactly that one module to the closures of `Random`, `Randomness.Learning` and `Randomness`, and none to
     root `TCSlib`. Its own closure (30 modules) is inside `Random`'s old closure and contains none of the 5 unit
     modules, so there is no cycle (`checks/imports.txt`). `HybridLemmas` defines nothing, so no seal request set
     changes.
   - Checks: decls2 against `7f5bdd51` empty; `touched` 2 CHANGED (the two theorems' bodies and docstrings), 59
     UNCHANGED; 63 header comparisons, 0 different (`statements/header-bytes-vs-7f5bdd51.txt`); both theorems'
     keyword-to-`:=` headers identical (`statements/docstring-header.txt`). The 66-module build is rc 0 with 0 errors
     and 0 sorry; every module has the same source and object SHA-256 as the review's `7f5bdd51` records except
     `Random` (`build/summary.txt`). Seals A and B, strict and coe, pass for `Random` with the review's request sets
     (`rule10/seal-rows-vs-review.txt`: 0 rows gone, new or changed); controls ALL_OK in both harnesses; axioms
     standard; lint unchanged.
   - **The promotion request for `uprob_eq_point` is withdrawn** (it is a reversed instance of a public lemma).
6. **DL-45 (duplication ledger, open).** Items 1 and 2 (`uprob_eq_point`, the inline coupling bound) are paid by
   LE-reuse. The rest is deferred to the cleanup (Seyoon's 2026-11-14 deferral of cleanup): the private `length_blk`
   re-proves `MultiMsg.length_histBlock` for the **disclosed** private copy `blk` of `histBlock` (no reader for
   `histBlock` exists; the worker's reader request stands); `flip0`/`flip0_flip0` duplicate `flipBit`/
   `flipBit_flipBit` (`BooleanAnalysis`) and `flipAt` (`DeterministicCC`), both outside the cryptography closure;
   `foldr_pairEncode_nil`'s left side is `Strategy.encodeMsgs`; and the short-name reuses `relabel`/`relabel_eq` (the
   DL-36 family, `Games.EffFill.relabel`) and `flipAt`.
7. **The disclosed route deviation: `MultiMsg.exists_queryChain_nuppt` is reused, not T1/T4.** The brief's step 1
   names T1 (non-adaptive queries) and T4. The worker instead calls the public `MultiMsg.exists_queryChain_nuppt` of
   the §3.9 reduction (`FromPRF/ReductionMachine.lean:461`), already a non-adaptive next-query machine with points
   from its coins and a final verdict of an arbitrary machine on the encoded tuple, at `ℓ₁ = ℓ₂ = n`; and it bridges
   probabilities in the `uprob` layer instead of the suggested `ProbComp`/`trialDist` bridge. No statement changes.
   It is called, not copied (review finding 8; `logs/duplication-grep.txt`). **Not a finding** by itself. What you
   can raise: a reason the reused chain does not give a legitimate PPT distinguisher with the budget used.
8. **The landing edits are the maintainer's** (the ext-nosrc, cca2-ett, dl-crh, hash-sign and lamport precedents):
   LE-doc docstrings only, LE-reuse proof only (with one acyclic import and two docstring insertions). Both were
   re-checked for this pack from git objects (rulings 4 and 5).

## What is frozen

- **The target's statement** (quoted in the brief), the 8 other pre-existing declarations of `Learning.lean` (part (c)
  and its proof included), the statement prose and the global simp attributes.
- **Every file outside** `Randomness/Learning.lean` and `Randomness/Learning/`. That includes the PAC layer
  (`LearningTheory/PAC/*`), `Games/Efficiency.lean`, `FromPRF/ReductionMachine.lean` and `FromPRF/HybridLemmas.lean`.
  The last two are owned by the running `prf-long` job (final delivered 2026-11-15, under review), whose binding
  frozen-statement rule keeps every existing header byte-identical; this unit uses `exists_queryChain_nuppt`,
  `histBlockLen`, `eval_histBlockLen`, `flatMap_range_blocks` and `abs_uexp_sub_le_uprob` from them.
- **The landing edits:** LE-doc docstrings only; LE-reuse two proofs, one import line and two docstring insertions.

## Questions for the audit

**1. Correctness against [PS10, Theorem 179.1(b)]**
- Does the proof establish the frozen statement for every PRF `F`, learner `A` and polynomial `m`, including `n = 0`,
  `m(n) = 0`, a fresh point equal to an example, and learner outputs other than `[true]`?
- Is `B` a legitimate distinguisher for `PRF.negligible_prfAdv`: a NUPPT next-query machine with budget `m + 1`, coins
  split correctly between the `m(n) + 1` points and `A`'s coins, and no timeout reached?
- Is `exists_learnDist_acceptProb` right: is the oracle game with `f_k` exactly the prediction game
  `predictSuccess (prfConcept F n) (m n) (learnerOf A n (m n))`, with the fresh point allowed to equal an example?
- Is the random-function bound `|gameProb − ½| ≤ m/2^n` right: is `flipAt` an involution that fixes the examples'
  labels and negates the fresh point's, and is the bad event exactly "the fresh point is an example"?
- Does the final calc with the negligible closure give `Negligible`, with `n = 0` handled by the eventual bound?
- **Part (c).** Is `not_weakLearnsUnder_prfConcept` now sorry-free with the standard axioms only
  (`landing/axioms-head.txt`; census in `review-evidence.zip`: `logs/census-summary.txt`,
  `logs/census-base-vs-head.txt`)?
- Does the rewritten target sketch describe the delivered proof?

**2. Frozen-statement integrity**
- Are the target's header and the other 8 pre-existing declarations byte-identical (`statements/head-le/header-bytes.txt`,
  `statements/head-le/decls2-vs-base.tsv` in `review-evidence.zip`; `statements/header-bytes-vs-7f5bdd51.txt` in
  `reuse-evidence.zip`), and are only the target's body and sketch, the imports, the title, the part (b) Main-results
  line and `## Contents` changed?

**3. LE-doc (ruling 4)**
- Does each of the 17 new formulas state what its declaration proves or defines, with arguments in the Lean order
  (`landing/le-doc.diff` and `statements/docaudit-le.tsv` in `review-evidence.zip`)? A formula that misstates its
  declaration is a minor. Is LE-doc docstrings only?

**4. LE-reuse (ruling 5)**
- Is it proof only (plus the import line and the two docstring insertions)? Are the two re-derivations correct
  instances of `OneWay.uprob_eq_one_div_card` and `MultiMsg.abs_uexp_sub_le_uprob`?
- Is the new import acyclic and justified, and is carrying the four untouched files' seals forward from `7f5bdd51`
  sound (their sources are unchanged; `HybridLemmas` adds no definition to any closure)?
- Do the re-run seals and controls for `Random.lean` bite (`rule10/` in `reuse-evidence.zip`)?

**5. Duplication**
- Does any new declaration duplicate a public TCSlib or Mathlib lemma, or copy a private one, beyond the worker's
  `## Overlap and reuse` table and DL-45 (ruling 6)? In particular, does any other part of a proof re-prove a public
  lemma inline, as `hpt`/`hdev` did before LE-reuse?
- Are the worker's disclosed overlaps (`learnerFn` vs the owned `learnerOf`, `firstBit` vs `prfConcept`, `sampleOf` vs
  `MultiMsg.blockMapFun`, `blk` vs `histBlock`, `tupleWord` vs `preFun_encodeHist`, `iid_uniform`,
  `predictSuccess_eq_uprob`, `snocEquiv`) accurate, and are its "why not reused" reasons valid?

**6. Rule 10**
- Do the seals, collected from the elaborated terms plus matchers, cover every touched declaration of the 5 files
  over the full closure, at the base and the head, in both variants (`logs/seal-table.txt`, `seals*/`,
  `base-seals*/`)? Do the coe controls (16 probes, 46 sealed negatives, ALL_OK; `logs/ctlcheck.log`) show that the
  seals bite? Explicit-unfold scan at `7f5bdd51`: 242 items, 0 foreign (`logs/scan2-head.log`).
- Is the strict-harness attribution of the two failing reader positives right (dispositions)?
- Does any proof read a foreign definition (the owned `prfConcept`, `encodeSample`, `learnerOf`; `PAC.label`;
  `MultiMsg.histBlock`, `blockMapFun`; `FinDist` internals) other than through a published reader?

## Known dispositions (not findings)

- **The strict-harness artifact on the FinDist reader controls** (review finding 7). In the strict control harness
  (`controls-strict/`, 16 probes, 54 sealed negatives; `logs/ctlcheck-strict.log`), every sealed negative fails
  exactly once, `ctlCoe` included, and every unsealed probe passes; but the reader positives `ctlUniformReader` and
  `ctlCoeReader` also fail, in all 8 sealed probes. With the `CoeFun` instance sealed, the control's own statement
  elaborates to `CoeFun.coe p a` instead of `p.prob a`, so a reader stated in the `.prob` form no longer matches
  (`seal-runs/mods/LnProbe_KS_ControlS_*.log`, "Type mismatch"). The canonical coe controls are ALL_OK, and the
  seals themselves agree in both variants (ruling 1). LE-reuse's controls drop the `FinDist` rows for this reason
  and are ALL_OK in both harnesses. The worker's own probe (`worker/evidence/logs/coe-probe.log`) reports that the
  strict seal cannot make a projection coercion fail; the review's strict `ctlCoe` negative does fail. The two
  controls are built differently; the canonical variant is coe either way. What you can raise: a reason the strict
  difference hides a real Rule-10 read.
- **Strict and coe seals agree** for this unit, at the base and the head (ruling 1); the worker's
  `seals-compare.log` reports the same.
- **The worker's promotion requests** (`iid_uniform` → `InformationTheory/Samples.lean`, `predictSuccess_eq_uprob` →
  `PAC/Prediction.lean`, `foldr_pairEncode_nil` → `PolyTimePairing.lean`) and **reader requests** (`MultiMsg.histBlock`,
  `MultiMsg.blockMapFun`) are recorded for the deferred cleanup; the `uprob_eq_point` promotion request is withdrawn
  (ruling 5).
- **The helper imports.** The brief names `Games/Efficiency`, `Games/Hopping`, `OracleFromPRF` and
  `Asymptotic/SamplingFinDist` as importable. The delivery imports `FromPRF/ReductionMachine` and
  `GGM/Reduction` (`Sample`), `Extraction/Rejection` and `LearningTheory.PAC` (`Law`), and after LE-reuse
  `FromPRF/HybridLemmas` (`Random`). None is downstream of a unit module, so there is no cycle (review
  `order/closure-*.txt`; LE-reuse `checks/imports.txt`). What you can raise: a cycle, or an import that changes what
  a frozen file's importers see.
- **The interaction with #314** (Gate 30, the `prfAdv_eq_expect` promotion). `Pseudorandom/Functions/Defs.lean`,
  which #314 changes, is in this unit's closure (through `HybridLemmas` and the PRF layer); #314's new import adds
  `Games.Probability`, `Games.Advantage` and `Games.Bridges.Experiments` to it. `git merge-tree --write-tree 8befc589
  5757bc06` gives tree `647c2e96fbb887ce32cd094d08536f7d1a57a8e8` with no conflict. The combined tree has not been
  built; whichever PR merges second is rebuilt on the merged tip.
- **No whole-tree check at the final head.** The review's whole-tree check (1245 modules plus PFR, RESULT OK;
  `landing/tree-check-7f5bdd51.txt`) is at LE-doc `7f5bdd51`. LE-reuse rebuilt the review's 66-module set at
  `8befc589` (`landing/root-checks.jsonl`), and `landing/build-summary.txt` shows that every module but `Random` has the
  same source and object hashes as the review's records; so the `7f5bdd51` tree check carries over except `Random`,
  which is rebuilt rc 0.
- **No explicit-unfold scan at the final head.** The review's scan is at `7f5bdd51`. LE-reuse's new proof text names
  only theorems (`OneWay.uprob_eq_one_div_card`, `Fintype.card_fun`, `Fintype.card_bool`, `Fintype.card_fin`,
  `Nat.cast_pow`, `Nat.cast_two`, `eq_comm`, `MultiMsg.abs_uexp_sub_le_uprob`, `uprob_nonneg`, `uprob_le_one`,
  `uprob_flip_half`, `OneWay.uexp_const`), and its seals pass.
- **#307 was built as base delta** in the review; none of its modules is in the unit's closure.
- **The worker's manifests list paths with a leading `./`** (review finding 9); the review's checker strips it, and
  both manifests verify (153/153, 142/142).

## Also check

**Axioms**
- At the head, `predictAdv_prfConcept_negligible`, `not_weakLearnsUnder_prfConcept`, `LearnPRF.uprob_eq_point` and
  `LearnPRF.abs_gameProb_random_sub_half_le` each print `[propext, Classical.choice, Quot.sound]`
  (`landing/axioms-head.txt`). At the base the target and part (c) also had `sorryAx`.
- Census at `7f5bdd51` (`review-evidence.zip`: `logs/census-summary.txt`, `logs/census-base-vs-head.txt`): 71 stored
  constants in the 5 files (12 internal or auxiliary, 7 private), axiom union `{propext, Classical.choice,
  Quot.sound}`, no `sorryAx`; base 11 → head 71, 60 added, none removed, type-changed, attribute-changed or moved; the
  only axiom changes are the target and part (c). LE-reuse changes two proofs and adds no constant.
- Nothing new is `@[simp]`, an instance or an abbreviation.

**Admissions:** 20 → 19 in the issued modules; only `predictAdv_prfConcept_negligible` is removed
(`logs/sorry-census.txt`).

**Sizes and widths:** every file is at most 275 lines and every line at most 100 characters (`source-head.json`).

**Build:** at `8befc589`, the 66 modules of the review's head set (the 51 base-delta modules of #303 and #306–#309 and
their downstream, the 5 unit modules, `Randomness`, root `TCSlib` and `audits/pass-shelat/Checks`) have rc 0, 0 errors
in both diagnostic forms and 0 sorry (`landing/root-checks.jsonl`, whose last line is the runner's `done` record;
each changed file's `source_sha256` matches `source-head.json`). The olean tree was restored to the base snapshot
afterwards (`restore/tree-check-post.txt` in `reuse-evidence.zip`).

## Evidence

- **`review.md`:** the maintainer's delivery review, verdict ACCEPT WITH LANDING EDITS. It was written before LE-reuse
  and says "LE-reuse is in progress"; LE-reuse's record is `fills/learning/final-r1/landing-reuse/` (the review record
  is not edited).
- **`verification.zip`** (31 entries): every file the review and the LE-reuse record cite, as byte-identical originals.
  Its `SHA256SUMS` lists every other entry, and `PROVENANCE.txt` gives each entry's source. It holds:
  - `review-evidence.zip` (`fills/learning/final-r1/`, SHA-256 `88ab5b78…`) and `review-evidence-SHA256SUMS`, its
    manifest. The ZIP has 489 entries, all files: under `learning-r1/`, exactly the 488 manifest paths plus that
    folder's `SHA256SUMS`, which is byte-identical to the manifest; all 488 hashes verify. It covers integrity, the
    landing and LE-doc, the build and the whole-tree check with the restore, decls2, header bytes, `touched`, the
    docstring and sketch audits, the census and axioms, the strict and coe seals at the base and the head, the
    paired controls in both harnesses, the scan, the old and new lint, sizes and the duplication grep;
  - `reuse-evidence.zip` (`fills/learning/final-r1/landing-reuse/learning-r1-reuse-evidence.zip`, SHA-256
    `5df65c56…`) and `reuse-evidence-SHA256SUMS`: 281 entries, 32 directory entries and 249 files, exactly the 248
    manifest paths plus `SHA256SUMS` (byte-identical to the manifest); and `landing-reuse/PROVENANCE.txt`, which
    equals the ZIP's `PROVENANCE.txt`. It covers LE-reuse's patch, the imports, statements, the 66-module build, axioms,
    seals and controls for `Random.lean`, lint and the restore;
  - `landing/`: the review's extracts `PROVENANCE.txt` and `duplication-grep.txt` (byte copies of ZIP entries);
  - `records/`: the issue package `fills/learning/issued-r1/`, the duplication ledger, the decision log, the #305
    record `maintainer/lint-facade-fix-2026-11-14/` (README and patch) and the issued prf-long brief, at records
    `f52a24be7442013d00bef3608ce5336429dd4719`;
  - `worker/`: byte copies from exchange `365d6639c0a3fbd2550e6ce792c2aee9b927010a` (`inbox/fills/learning/`):
    `patches/COMMITS.tsv` and `evidence/` files `seals/seals-compare.log`, `logs/coe-probe.log`, `probes/CoeProbe.lean`,
    `logs/final-searches.log`, `logs/final-census-vs-base.diff`, `logs/final-lint-vs-base.diff`, `logs/final-axioms.log`.
- **The worker's own evidence:** on the exchange at `365d6639c0a3fbd2550e6ce792c2aee9b927010a`, under
  `inbox/fills/learning/`. Its top `SHA256SUMS` lists 153 files and `evidence/SHA256SUMS` 142, all delivered.
- **`landing/`:** byte copies of evidence-ZIP entries.
  - `root-checks.jsonl` (= `reuse-evidence.zip`: `build/results.jsonl`): the 66 modules at `8befc589`, rc 0.
  - `build-summary.txt` (= `build/summary.txt`): the counts and the hash comparison with the review's records.
  - `axioms-head.txt` (= `axioms/AxiomsHead.log`): the four axiom prints at the head.
  - `tree-check-7f5bdd51.txt` (= `review-evidence.zip`: `learning-r1/tree/tree-check-head.txt`): the whole-tree
    check at LE-doc.
- **`worker-report.md`:** the worker's `REPORT.md`, at exchange `365d6639`.
- **`pr-description.md`:** the PR #313 description as fetched from the GitHub REST API on 2026-11-15 (`.body`, raw).
- **`pr.diff.txt`:** `git diff` from the base to the head (5 paths, 859 insertions, 13 deletions).
- **`source-head.json`:** the head hashes, line counts and over-width counts of the 5 changed files.
- **`sources.zip`:** the source closure at the head of every changed module, 138 files.
- **Evidence note.** `logs/duplication-grep.txt` (and its `landing/` copy) shows `grep: --include=*.lean: No such file
  or directory` once per search: the option was passed after the path, so each search covered every file under
  `TCSlib/`, not only `.lean` files. The matches shown are still the Lean declarations; the search was wider, not
  narrower.

## Findings delivery

Return `gate29-learning-findings.md` as a Markdown file in this chat. If you have several evidence files, return a ZIP.
The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish the frozen statement, or a scope
  violation.
- **major:** a changed frozen statement, a forbidden read in a touched declaration not covered by the rulings, an
  undisclosed copied private lemma or undisclosed re-proof of a public one outside DL-45, or necessary evidence that
  cannot be verified.
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

## ===== TCSlib/Cryptography/Randomness/Learning/Random.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Randomness.Learning.Law
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# With a random function, no learner predicts better than `½ ± m/2^n`

Step 2 of [PS10, Theorem 179.1, proof]: in the game with a uniform random function
`R : {0,1}^n → {0,1}^n` in place of the keyed family, every learner `ℓ` predicts the first bit of
`R x` with probability within `m/2^n` of `½`, for `n ≥ 1` (`abs_gameProb_random_sub_half_le`).

**Proof.** Fix the examples `s`, the coins `r` and the fresh point `x`. If `x` is none of the
examples, flipping the first bit of `R x` (`flipAt`, an involution of the random functions) keeps
the labelled examples and negates the label of `x`, so it exchanges the winning and the losing
functions: the probability over `R` is exactly `½` (`uprob_flip_half`). Otherwise the probability
is between `0` and `1`. So the game probability is within `Pr[x ∈ s]` of `½`, and
`Pr[x ∈ s] ≤ Σ_j Pr[x = s_j] = m · 2^{-n}` (`uprob_exists_le`, `uprob_eq_point`).

## Main definitions

* `LearnPRF.flip0`, `LearnPRF.flipAt`: flipping the first bit of a string, and of a function's
  value at a point.

## Main results

* `LearnPRF.firstBit_flip0`, `LearnPRF.flipAt_involutive`.
* `LearnPRF.uprob_flip_half`: at a fresh point, the prediction wins with probability `½`.
* `LearnPRF.uprob_eq_point`: a uniform point hits a given point with probability `2^{-n}`.
* `LearnPRF.abs_gameProb_random_sub_half_le`: the bound `|gameProb − ½| ≤ m/2^n`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.1, Theorem 179.1 (book p. 179).
-/

namespace TCSlib.Cryptography.Randomness.LearnPRF

open Complexity TCSlib.Cryptography TCSlib.LearningTheory.PAC Finset

section Random

variable {n : ℕ} (hn : 0 < n)

/-- **Flipping the first bit** of an `n`-bit string (`n ≥ 1`):
`flip0 hn y = update y 0 (!y 0)`. -/
def flip0 (y : Fin n → Bool) : Fin n → Bool := Function.update y ⟨0, hn⟩ (!y ⟨0, hn⟩)

/-- `flip0 hn y = Function.update y ⟨0, hn⟩ (!y ⟨0, hn⟩)`. -/
theorem flip0_eq (y : Fin n → Bool) : flip0 hn y = Function.update y ⟨0, hn⟩ (!y ⟨0, hn⟩) := rfl

/-- Flipping twice is the identity: `flip0 hn (flip0 hn y) = y`. -/
theorem flip0_flip0 (y : Fin n → Bool) : flip0 hn (flip0 hn y) = y := by
  rw [flip0_eq, flip0_eq, Function.update_self, Function.update_idem, Bool.not_not,
    Function.update_eq_self]

/-- The first bit of an `n`-bit string with `n ≥ 1` is its bit `0`:
`firstBit y = y ⟨0, hn⟩`.
This is the published `TCSlib.Cryptography.headD_drop_ofFn` at index `0`. -/
theorem firstBit_of_pos (y : Fin n → Bool) : firstBit y = y ⟨0, hn⟩ := by
  rw [firstBit_eq]
  simpa only [List.drop_zero] using TCSlib.Cryptography.headD_drop_ofFn y ⟨0, hn⟩ false

/-- Flipping the first bit negates it: `firstBit (flip0 hn y) = !firstBit y`. -/
theorem firstBit_flip0 (y : Fin n → Bool) : firstBit (flip0 hn y) = !firstBit y := by
  rw [firstBit_of_pos hn, firstBit_of_pos hn, flip0_eq, Function.update_self]

/-- **Flipping the first bit of a function's value at `x`:**
`flipAt hn x R = update R x (flip0 hn (R x))`. -/
def flipAt (x : Fin n → Bool) (R : (Fin n → Bool) → (Fin n → Bool)) :
    (Fin n → Bool) → (Fin n → Bool) :=
  Function.update R x (flip0 hn (R x))

/-- `flipAt hn x R = Function.update R x (flip0 hn (R x))`. -/
theorem flipAt_eq (x : Fin n → Bool) (R : (Fin n → Bool) → (Fin n → Bool)) :
    flipAt hn x R = Function.update R x (flip0 hn (R x)) := rfl

/-- `flipAt hn x` is an involution: `flipAt hn x (flipAt hn x R) = R`. -/
theorem flipAt_involutive (x : Fin n → Bool) : Function.Involutive (flipAt hn x) := by
  intro R
  rw [flipAt_eq, flipAt_eq, Function.update_self, flip0_flip0, Function.update_idem,
    Function.update_eq_self]

include hn in
/-- **At a fresh point the prediction wins with probability `½`:** if `x` is none of the
examples `s`, then for every learner `ℓ` and coins `r`, the uniform probability over `R` that
`ℓ (label (firstBit ∘ R) s) r x == firstBit (R x)` is `½`.

**Proof sketch.** `flipAt hn x` is a bijection of the functions (`flipAt_involutive`), so it
preserves the probability (`uprob_comp_equiv`). It keeps the labels of the examples
(`Function.update_of_ne`) and negates the label of `x` (`firstBit_flip0`), so it maps the event to
its complement; hence `p = 1 − p` (`uprob_not`). -/
theorem uprob_flip_half {m : ℕ} {ρ : Type*}
    (ℓ : (Fin m → (Fin n → Bool) × Bool) → ρ → (Fin n → Bool) → Bool) (s : Fin m → Fin n → Bool)
    (r : ρ) (x : Fin n → Bool) (hx : ∀ j, s j ≠ x) :
    uprob (fun R : (Fin n → Bool) → (Fin n → Bool) =>
      (ℓ (label (fun z => firstBit (R z)) s) r x == firstBit (R x)) = true) = 1 / 2 := by
  set σ := Function.Involutive.toPerm (flipAt hn x) (flipAt_involutive hn x) with hσ
  have h1 := uprob_comp_equiv σ (fun R =>
    (ℓ (label (fun z => firstBit (R z)) s) r x == firstBit (R x)) = true)
  have h2 : (fun R : (Fin n → Bool) → (Fin n → Bool) =>
      (ℓ (label (fun z => firstBit (σ R z)) s) r x ==
        firstBit (σ R x)) = true) =
      fun R => ¬ (ℓ (label (fun z => firstBit (R z)) s) r x == firstBit (R x)) = true := by
    funext R
    have hl : label (fun z => firstBit (σ R z)) s =
        label (fun z => firstBit (R z)) s := by
      funext j
      rw [label_apply, label_apply, hσ, Function.Involutive.coe_toPerm, flipAt_eq,
        Function.update_of_ne (hx j)]
    rw [hl, hσ, Function.Involutive.coe_toPerm, flipAt_eq, Function.update_self, firstBit_flip0]
    cases ℓ (label (fun z => firstBit (R z)) s) r x <;> cases firstBit (R x) <;> decide
  rw [h2, uprob_not] at h1
  linarith

/-- **A uniform point hits a given point with probability `2^{-n}`:**
`uprob (fun x : {0,1}^n => y = x) = 1 / 2^n`.

**Proof sketch.** This is `OneWay.uprob_eq_one_div_card` with the equation reversed and
`|{0,1}^n| = 2^n`. -/
theorem uprob_eq_point (y : Fin n → Bool) :
    uprob (fun x : Fin n → Bool => y = x) = 1 / 2 ^ n := by
  rw [show (fun x : Fin n → Bool => y = x) = (fun x => x = y) from
      funext fun _ => propext eq_comm, OneWay.uprob_eq_one_div_card, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_two]

include hn in
/-- **With a random function the prediction is within `m/2^n` of `½`** [PS10, Theorem 179.1,
proof, step 2]: for `n ≥ 1`, every learner `ℓ` and `m` examples,
`|gameProb m (fun R => R) ℓ − ½| ≤ m / 2^n`.

**Proof sketch.** Put the function last (`uprob_comp_equiv`) and average over it first
(`uprob_prod`): for fixed `((s, r), x)` the probability `p` is `½` when `x` is fresh
(`uprob_flip_half`) and in `[0, 1]` otherwise, so `|p − ½| ≤ [x ∈ s]`. Averaging (the
coupling bound `MultiMsg.abs_uexp_sub_le_uprob` against the constant `½`),
`|gameProb − ½| ≤ Pr[∃ j, s_j = x]`, which the union bound (`uprob_exists_le`) bounds by
`Σ_j Pr[s_j = x] = m · 2^{-n}` (`uprob_prod`, `uprob_eq_point`, `OneWay.uexp_const`). -/
theorem abs_gameProb_random_sub_half_le {ρ : Type*} [Fintype ρ] [Nonempty ρ] (m : ℕ)
    (ℓ : (Fin m → (Fin n → Bool) × Bool) → ρ → (Fin n → Bool) → Bool) :
    |gameProb m (fun R : (Fin n → Bool) → (Fin n → Bool) => R) ℓ - 1 / 2| ≤ m / 2 ^ n := by
  classical
  -- the random function last
  let e : (((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool)) × ((Fin n → Bool) → (Fin n → Bool)) ≃
      (((Fin n → Bool) → (Fin n → Bool)) × ((Fin m → Fin n → Bool) × ρ)) × (Fin n → Bool) :=
    { toFun := fun w => ((w.2, w.1.1), w.1.2)
      invFun := fun w => ((w.1.2, w.2), w.1.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  set p : ((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool) → ℝ := fun t =>
    uprob (fun R : (Fin n → Bool) → (Fin n → Bool) =>
      (ℓ (label (fun z => firstBit (R z)) t.1.1) t.1.2 t.2 == firstBit (R t.2)) = true) with hp
  have hgame : gameProb m (fun R : (Fin n → Bool) → (Fin n → Bool) => R) ℓ = uexp p := by
    rw [gameProb_eq, ← uprob_comp_equiv e, uprob_prod]
    rfl
  -- the bad event: the fresh point is an example
  set bad : ((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool) → Prop :=
    fun t => ∃ j ∈ (Finset.univ : Finset (Fin m)), t.1.1 j = t.2 with hbad
  -- the coupling bound against the constant `½`: off the bad event, `p = ½`
  have hdev : |uexp p - 1 / 2| ≤ uprob bad := by
    have h := MultiMsg.abs_uexp_sub_le_uprob p (fun _ => 1 / 2) bad
      (fun _ => ⟨uprob_nonneg _, uprob_le_one _⟩) (fun _ => ⟨by norm_num, by norm_num⟩)
      (fun t hb => uprob_flip_half hn ℓ t.1.1 t.1.2 t.2 fun j hj => hb ⟨j, Finset.mem_univ j, hj⟩)
    rwa [OneWay.uexp_const] at h
  -- the union bound
  have hj : ∀ j : Fin m, uprob (fun t : ((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool) =>
      t.1.1 j = t.2) = 1 / 2 ^ n := by
    intro j
    rw [uprob_prod]
    simp only [uprob_eq_point, OneWay.uexp_const]
  have hunion := uprob_exists_le (Finset.univ : Finset (Fin m))
    (fun j (t : ((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool)) => t.1.1 j = t.2)
  simp only [hj, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hunion
  rw [hgame]
  refine hdev.trans (hunion.trans (le_of_eq ?_))
  ring

end Random

end TCSlib.Cryptography.Randomness.LearnPRF

## ===== TCSlib/Cryptography/Foundations/BitLists.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bit lists and bit vectors

Generic facts about lists, lists of bits and bit vectors `Fin n → Bool`, shared by the
cryptographic developments: heads of suffixes, flattening singleton blocks, the bit of a one-bit
vector, cancellation of exclusive-or, exclusive-or with a fixed vector as a permutation, and keys of
an association list. They depend on Mathlib only.

## Main definitions

* `TCSlib.Cryptography.xorPerm v`: exclusive-or with the vector `v`, as a permutation.

## Main results

* `TCSlib.Cryptography.headD_drop`: the head of a suffix is an entry.
* `TCSlib.Cryptography.headD_drop_ofFn`: the head of a suffix of a tuple's list is the tuple's
  entry at that index.
* `TCSlib.Cryptography.flatten_ofFn_one`, `flatten_ofFn_singleton`: flattening one-element blocks.
* `TCSlib.Cryptography.headD_ofFn_one`: the bit of a one-bit vector is the head of its string.
* `TCSlib.Cryptography.zipWith_xor_cancel_left`: `(a ⊕ c) ⊕ a = c`.
* `TCSlib.Cryptography.xorPerm_apply`: `xorPerm v y = y ⊕ v`.
* `TCSlib.Cryptography.mem_keys_of_lookup_isSome`: a key with a value in an association list is
  one of its keys.
* `TCSlib.Cryptography.ofFn_eq_map_range`, `ofFn_natAdd_eq_drop`, `decide_map_ofFn`: lists of
  tuples as maps over ranges, tails of tuples, comparing optional tuples through their lists.
* `TCSlib.Cryptography.length_flatten_map_const`, `length_flatten_map_range`: the length of a
  concatenation of equal-length blocks.
* `TCSlib.Cryptography.flatMap_range_drop`: reading the successive suffixes of a list.

## References

Generic list facts; no textbook counterpart.
-/

namespace TCSlib.Cryptography

/-- The head of a dropped list is the element at the dropping index:
`(l.drop i).headD d = l.getD i d`. -/
theorem headD_drop {α : Type*} (l : List α) (i : ℕ) (d : α) : (l.drop i).headD d = l.getD i d := by
  rw [List.headD_eq_head?, List.head?_drop, List.getD_eq_getElem?_getD]

/-- The head of the suffix of a tuple's list at an index is the tuple's entry there: for
`f : Fin n → α`, `i : Fin n` and any default `d`, `((List.ofFn f).drop i.val).headD d = f i`
(for bit vectors, `d = false` reads the `i`-th bit of the string `List.ofFn f`).

**Proof sketch.** By `headD_drop` the left side is the entry `(List.ofFn f).getD i d`; since
`i < n` it is the in-range entry `f i` (`List.getElem?_ofFn`). -/
theorem headD_drop_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
    ((List.ofFn f).drop i.val).headD d = f i := by
  simp only [headD_drop, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos i.isLt,
    Option.getD_some]

/-- **Flattening one-element blocks:** concatenating the one-bit blocks `g j` gives their bits,
`(List.ofFn fun j => List.ofFn (g j)).flatten = List.ofFn fun j => g j 0` when the blocks have
length `l = 1`.

**Proof sketch.** Induction on the number `k` of blocks (`List.ofFn_succ`, `List.flatten_cons`). -/
theorem flatten_ofFn_one {k l : ℕ} (hl : l = 1) (g : Fin k → Fin l → Bool) :
    (List.ofFn fun j => List.ofFn (g j)).flatten = List.ofFn fun j => g j ⟨0, by omega⟩ := by
  subst hl
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.ofFn_succ, List.flatten_cons, ih (fun j => g j.succ), List.ofFn_succ (n := k)]
    simp

/-- Flattening singletons: `(List.ofFn fun i => List.ofFn fun _ : Fin p => f i).flatten =
List.ofFn f` when `p = 1` (`flatten_ofFn_one` with constant blocks). -/
theorem flatten_ofFn_singleton {p : ℕ} (hp : p = 1) :
    ∀ {k : ℕ} (f : Fin k → Bool),
      (List.ofFn fun i => List.ofFn fun _ : Fin p => f i).flatten = List.ofFn f :=
  fun f => flatten_ofFn_one hp fun i _ => f i

/-- The bit of a one-bit output is the head of its string: `⟦f⟧.headD false = f 0`. -/
theorem headD_ofFn_one (f : Fin 1 → Bool) : (List.ofFn f).headD false = f 0 := by
  rw [List.ofFn_succ, List.headD_cons]

/-- Exclusive-or with the same list twice cancels: `(a ⊕ c) ⊕ a = c` for `|a| = |c|`. -/
theorem zipWith_xor_cancel_left {a c : List Bool} (h : a.length = c.length) :
    List.zipWith xor (List.zipWith xor a c) a = c := by
  apply List.ext_getElem
  · simp [h]
  · intro i h₁ h₂
    simp only [List.getElem_zipWith]
    cases a[i] <;> cases c[i] <;> rfl

section XorPerm

variable {n : ℕ}

/-- Exclusive-or with a fixed vector `v`, as a permutation of `{0,1}ⁿ`: `xorPerm v y = y ⊕ v`. -/
def xorPerm (v : Fin n → Bool) : Equiv.Perm (Fin n → Bool) :=
  Function.Involutive.toPerm (fun y i => xor (y i) (v i)) fun y => funext fun i => by
    simp

/-- `xorPerm v y = y ⊕ v`. -/
theorem xorPerm_apply (v y : Fin n → Bool) : xorPerm v y = fun i => xor (y i) (v i) := rfl

end XorPerm

/-- A key with a value in an association list is one of its keys:
`(T.lookup x).isSome → x ∈ T.map Prod.fst`.

**Proof sketch.** Core's `List.lookup_isSome_iff` gives a pair `p ∈ T` with `x == p.1`, so `x`
is the first component of an element of `T` (`List.mem_map`). -/
theorem mem_keys_of_lookup_isSome {α β : Type} [DecidableEq α] (T : List (α × β)) (x : α)
    (h : (T.lookup x).isSome = true) : x ∈ T.map Prod.fst := by
  obtain ⟨p, hp, hx⟩ := List.lookup_isSome_iff.1 h
  exact List.mem_map.2 ⟨p, hp, (beq_iff_eq.1 hx).symm⟩

/-! ### Lists indexed by ranges, tails and blocks of lists -/

/-- A list of `r` values is a map over `List.range r`: if `f i = g i` for every `i : Fin r`, then
`List.ofFn f = (List.range r).map g` (both have `r` entries, entry `i` is `f i = g i`). -/
theorem ofFn_eq_map_range {α : Type*} {r : ℕ} (f : Fin r → α) (g : ℕ → α)
    (h : ∀ i : Fin r, f i = g i) : List.ofFn f = (List.range r).map g := by
  refine List.ext_getElem (by rw [List.length_ofFn, List.length_map, List.length_range])
    fun i h₁ h₂ => ?_
  rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  exact h _

/-- **The tail of a string:** `⟦j ↦ w (natAdd k j)⟧ = ⟦w⟧.drop k` (`List.ofFn_add`). -/
theorem ofFn_natAdd_eq_drop {k sl : ℕ} (w : Fin (k + sl) → Bool) :
    List.ofFn (fun j : Fin sl => w (Fin.natAdd k j)) = (List.ofFn w).drop k := by
  rw [List.ofFn_add, List.drop_left' List.length_ofFn]

/-- Comparing strings is comparing their lists:
`decide (o.map ofFn = some ⟦c⟧) = decide (o = some c)` (`List.ofFn_inj`). -/
theorem decide_map_ofFn {k : ℕ} (o : Option (Fin k → Bool)) (c : Fin k → Bool) :
    decide (o.map List.ofFn = some (List.ofFn c)) = decide (o = some c) := by
  cases o with
  | none => simp
  | some c' => simp [List.ofFn_inj]

/-- Blocks of `k` entries, one per element: `|(l.map g).flatten| = |l|·k` when every `g x` has
`k` entries (`List.length_flatten`, a sum of the constant `k`). -/
theorem length_flatten_map_const {α β : Type*} (l : List α) (g : α → List β) (k : ℕ)
    (hg : ∀ x, (g x).length = k) : (l.map g).flatten.length = l.length * k := by
  rw [List.length_flatten, List.map_map, show (List.length ∘ g) = fun _ => k from funext hg,
    List.map_const', List.sum_replicate_nat]

/-- `r` blocks of `k` entries have `r·k` entries: `|((range r).map g).flatten| = r·k` when
`g 0, …, g (r-1)` have `k` entries each (`List.length_flatten`, a sum of the constant `k`). -/
theorem length_flatten_map_range {β : Type*} (k r : ℕ) (g : ℕ → List β)
    (hg : ∀ i < r, (g i).length = k) : ((List.range r).map g).flatten.length = r * k := by
  rw [List.length_flatten, List.map_map,
    List.map_congr_left (f := List.length ∘ g) (g := fun _ => k)
      fun i hi => hg i (List.mem_range.1 hi),
    List.map_const', List.sum_replicate_nat, List.length_range]

/-- **Reading the suffixes of a list within at least its length many steps:** if `F [] = []`
and `F` reads only the first element of a nonempty suffix, `F (e :: t) = g e` for the members `e`
of `l`, then `(List.range m).flatMap (fun i => F (l.drop i)) = l.flatMap g` for every
`m ≥ |l|`.

**Proof sketch.** Induction on `l`: the first suffix is `l` itself, read as `g e`; the others are
the suffixes of the tail, within `m - 1` steps; the empty suffixes read `[]`. -/
theorem flatMap_range_drop {β γ : Type*} (F : List β → List γ) (g : β → List γ)
    (hnil : F [] = []) :
    ∀ (l : List β), (∀ e ∈ l, ∀ t, F (e :: t) = g e) → ∀ m : ℕ, l.length ≤ m →
      ((List.range m).flatMap fun i => F (l.drop i)) = l.flatMap g := by
  intro l
  induction l with
  | nil =>
    intro _ m _
    rw [List.flatMap_nil]
    refine List.flatMap_eq_nil_iff.2 fun i _ => ?_
    rw [List.drop_nil, hnil]
  | cons e t ih =>
    intro hcons m hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by rw [List.length_cons] at hm; omega⟩
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.drop_zero,
      hcons e List.mem_cons_self, List.flatMap_cons]
    congr 1
    simp only [List.drop_succ_cons]
    exact ih (fun e' he' => hcons e' (List.mem_cons_of_mem _ he')) m'
      (by rw [List.length_cons] at hm; omega)

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/OneWayFunctions/Basic.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Foundations.Experiments
import Mathlib.Data.Fintype.BigOperators

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Probability toolkit for one-way function reductions

The reductions of [Gar26, Chapter 2] manipulate uniform probabilities in a handful of
recurring ways: averaging a pointwise bound, conditioning on a bad set, splitting off a
uniform index, planting an input into a uniform tuple, and multiplying probabilities of
independent coordinates. This file proves these facts once, on top of the uniform
probability `uprob` and expectation `uexp` of `Foundations/Probability.lean`.

## Main definitions

None; this file only proves laws about `uprob` and `uexp`.

## Main results

* `uexp_mono`, `uexp_add`, `uexp_const`, `uexp_indicator`: laws of the uniform average.
* `uprob_and_le_mul`: conditioning on a set `S` on which every section has probability
  at most `θ` costs at most `θ · Pr[S]`.
* `sum_uprob_eq_card_mul`: a sum over a uniform index is `q` times a probability.
* `uprob_pi_forall`: independent coordinates multiply.
* `uprob_update`: planting a fresh uniform value into a uniform tuple leaves it uniform.
* `uprob_eq_one_div_card`: a uniform element hits a fixed point with probability
  `1 / |α|`.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Chapter 2 (the computations in §2.2.2 and §2.3).
-/

namespace TCSlib.Cryptography.OneWay

open Finset TCSlib.Cryptography

variable {α β ρ : Type*} [Fintype α] [Fintype β] [Fintype ρ]

/-- Two events that hold for the same elements have the same probability. -/
theorem uprob_congr {p q : α → Prop} (h : ∀ a, p a ↔ q a) : uprob p = uprob q := by
  rw [show p = q from funext fun a => propext (h a)]

/-- A pointwise smaller function has a smaller average. -/
theorem uexp_mono {f g : α → ℝ} (h : ∀ a, f a ≤ g a) : uexp f ≤ uexp g := by
  unfold uexp
  exact div_le_div_of_nonneg_right (sum_le_sum fun a _ => h a) (Nat.cast_nonneg _)

/-- The average of a sum is the sum of the averages. -/
theorem uexp_add (f g : α → ℝ) : uexp (fun a => f a + g a) = uexp f + uexp g := by
  unfold uexp
  rw [sum_add_distrib, add_div]

/-- The average of a constant times a function is the constant times the average. -/
theorem uexp_const_mul (c : ℝ) (f : α → ℝ) : uexp (fun a => c * f a) = c * uexp f := by
  unfold uexp
  rw [← mul_sum, mul_div_assoc]

/-- The average of a constant over a nonempty type is that constant. -/
theorem uexp_const [Nonempty α] (c : ℝ) : uexp (fun _ : α => c) = c := by
  unfold uexp
  have : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [sum_const, card_univ, nsmul_eq_mul]
  field_simp

/-- The average of `c` times the indicator of `p` is `c` times the probability of `p`. -/
theorem uexp_indicator (p : α → Prop) [DecidablePred p] (c : ℝ) :
    uexp (fun a => if p a then c else 0) = c * uprob p := by
  rw [uprob_eq_uexp, ← uexp_const_mul]
  congr 1
  funext a
  split_ifs <;> simp

/-- Conditioning on a bad set: if every `a` in `S` has a section of `p` of probability at
most `θ`, then `S a ∧ p (a, b)` has probability at most `θ · Pr[S]`. [Gar26, §2.3, proof
of Theorem 2.1, the step `Pr[x ∈ S ∧ E] ≤ Pr[x ∈ S] · Pr[E | x ∈ S]`].

**Proof sketch.** Average over `a` the section probabilities: the section of the event is
empty off `S` and has probability at most `θ` on `S`. -/
theorem uprob_and_le_mul (S : α → Prop) (p : α × β → Prop) {θ : ℝ}
    (h : ∀ a, S a → uprob (fun b => p (a, b)) ≤ θ) :
    uprob (fun z : α × β => S z.1 ∧ p z) ≤ θ * uprob S := by
  classical
  rw [uprob_prod, ← uexp_indicator]
  apply uexp_mono
  intro a
  by_cases ha : S a
  · simp only [ha, true_and, if_true]
    exact h a ha
  · simp only [ha, false_and, if_false]
    rw [uprob_false]

/-- Splitting off a uniform index: the sum over `i` of the probabilities of the events
`p i` is `|ι|` times the probability of `p i ω` for uniform `(i, ω)`. [Gar26, §2.3, proof
of Theorem 2.1, the step introducing the uniform index `i`]. -/
theorem sum_uprob_eq_card_mul (p : β → α → Prop) :
    ∑ i, uprob (p i) = Fintype.card β * uprob (fun z : β × α => p z.1 z.2) := by
  rw [uprob_prod]
  unfold uexp
  rcases Nat.eq_zero_or_pos (Fintype.card β) with h | h
  · rw [Fintype.card_eq_zero_iff] at h
    simp [Finset.univ_eq_empty]
  · have : (Fintype.card β : ℝ) ≠ 0 := by positivity
    field_simp

/-- Independent coordinates multiply: the probability that every coordinate of a uniform
tuple satisfies `p` is the `|ι|`-th power of the probability of `p`. [Gar26, §2.3, proof
of Theorem 2.1, `Pr[∀ i : xᵢ ∉ S] = (1 - Pr[S])^q`]. -/
theorem uprob_pi_forall {ι : Type*} [Fintype ι] [DecidableEq ι] (p : α → Prop) :
    uprob (fun xs : ι → α => ∀ i, p (xs i)) = uprob p ^ Fintype.card ι := by
  unfold uprob
  rw [Nat.card_congr (Equiv.subtypePiEquivPi (p := fun _ a => p a)), Nat.card_pi,
    prod_const, card_univ, Fintype.card_fun, Nat.cast_pow, Nat.cast_pow, div_pow]

/-- Planting a fresh uniform value `x` at position `i` of a uniform tuple `xs` (with
further independent coins `r`) yields a uniform tuple. [Gar26, §2.3, proof of
Theorem 2.1: "`x` is distributed as `xᵢ`"].

**Proof sketch.** The map `(x, (xs, r)) ↦ ((update xs i x, r), xs i)` is a bijection,
with inverse `((zs, r), a) ↦ (zs i, (update zs i a, r))`; the planted tuple is its first
component, and the forgotten coordinate `a` is irrelevant to the event. -/
theorem uprob_update {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty α] (i : ι)
    (P : (ι → α) → ρ → Prop) :
    uprob (fun z : α × ((ι → α) × ρ) => P (Function.update z.2.1 i z.1) z.2.2) =
      uprob (fun w : (ι → α) × ρ => P w.1 w.2) := by
  let e : α × ((ι → α) × ρ) ≃ ((ι → α) × ρ) × α :=
    { toFun := fun z => ((Function.update z.2.1 i z.1, z.2.2), z.2.1 i)
      invFun := fun w => (w.1.1 i, (Function.update w.1.1 i w.2, w.1.2))
      left_inv := fun z => by simp
      right_inv := fun w => by simp }
  rw [← uprob_fst (β := α) (fun w : (ι → α) × ρ => P w.1 w.2), ← uprob_comp_equiv e]
  rfl

/-- A uniform element of `α` equals a fixed point `a` with probability `1 / |α|`. -/
theorem uprob_eq_one_div_card (a : α) : uprob (fun x : α => x = a) = 1 / Fintype.card α := by
  unfold uprob
  simp

end TCSlib.Cryptography.OneWay
