## ===== briefs/pass-shelat-ch5-8/gates/24-dl-crh/pack-r2.md =====

# Gate 24 · The discrete-log hash is collision-resistant (`dl-crh`) · round 2

The auditor is Codex. Round 1 was HOLD (0/1/2/0); its findings are `findings/gate24-dl-crh-findings.md` (SHA-256
`f29e4cb9…`). This round re-audits the one fix, the two errata and the PR's combination with the merged tip. The
round-1 pack (`pack.md`) still defines the scope; its questions stand for anything round 1 left unverified.

- **PR:** draft [PR #307](https://github.com/Shilun-Allan-Li/tcslib/pull/307), now at
  `d356381aadc350860f9a0e97123e84d9aefa585b` (branch `land/pass-shelat-dl-crh`, tree
  `c7b77d28fa11c95a00789102e8d9410fc931bf63`).
- **Base:** `a757b6a18785377c158312ed051b1789cf45badf`, unchanged; the PR was not rebased.
- **New since round 1:** one commit, **LE-reuse** `d356381a`, on top of the round-1 head
  `649c4888f23fbb9df71d555e952d1149a0aaa00b`. It touches only `Hashing/FromDiscreteLog/Encoding.lean` (6 insertions,
  4 deletions).
- **The target branch moved.** Since round 1, #308 (merge `34dc8fb2`), #309 (`97ee2524`) and #306 (`7fdf3a9b`) were
  merged into `cryptography/pass-shelat-ch2-4`. Their 38 `.lean` files are disjoint from the PR's 9, so GitHub's
  three-dot diff against the current tip `47e6cf474ce4f7507eee9f945b973afbcbc40e96` equals `pr.diff-r2.txt` byte for
  byte. #303 (`d82e9a50`) was already in the base.
- **Resolutions:** `resolutions-r1.md`.

All Lean paths below are under `TCSlib/Cryptography/`.

## What to check

### 1. G24-01: is LE-reuse proof only, and does it reuse the published lemmas?

The diff is `landing-r1/0001-dl-crh-landing-edit-LE-reuse-inputWord_take-and-inpu.patch` (= `git format-patch -1
d356381a`, reproduced byte for byte).

- **`inputWord_take`** is now
  `(take_ofFn_castLE (Nat.le_succ n) x).trans (congrArg List.ofFn (funext fun _ => congrArg x (Fin.ext rfl)))`, a
  reader of `TCSlib.Cryptography.take_ofFn_castLE` (`Asymptotic/ReductionSupport.lean:288`, unchanged since the base).
  It no longer goes through `inputWord_split`.
- **`inputWord_split`** is now the term `ofFn_eq_init_append x` (`ReductionSupport.lean:58`). Its statement is the
  lemma's with `Fin.init x` unfolded, which the elaborator accepts by unfolding `Fin.init`, a Mathlib definition. This
  pays the DL-41 item that round 1 left as a known disposition.
- **The new import** `TCSlib.Cryptography.Asymptotic.ReductionSupport` is real: at `649c4888` it was not in
  `Encoding`'s closure (65 project modules). It adds 4 modules: `Asymptotic.ReductionSupport`,
  `Foundations.Negligible`, `Pseudorandom.Generators` and `Pseudorandom.Indistinguishability`. `ReductionSupport`'s own
  closure (35 modules) contains none of the 9 unit modules, so there is no cycle. `Authentication` and root `TCSlib`
  already imported it.

Check that:
- both statements and docstrings are byte for byte those of `649c4888`, and only the two bodies changed;
- both proofs use only the published lemmas plus `Fin.ext`, `congrArg`, `funext` and `Fin.init`'s unfolding;
- the import is acyclic and needed (it is the only route to the two lemmas);
- no other declaration of the 9 files changed.

**Evidence** (`landing-r1/`): `gate24-r1-evidence.zip` (SHA-256
`6c1802139817f3fc033a50ecec1e9a8ff6f953bccad5b82b02f4c9bddb94fa22`; 209 files, exactly the paths of its manifest
`evidence-SHA256SUMS`, with no inner `SHA256SUMS`) and its `PROVENANCE.txt`.
- **Statements** (`statements/`): decls2 against `649c4888` is empty. `header-bytes-vs-649c4888.txt`: 198 headers
  (all 197 declarations of the 8 Lean files that have declarations, plus the endpoint), 0 different.
  `touched-649c4888-vs-head.tsv`: 2 CHANGED (`inputWord_split`, `inputWord_take`), 195 UNCHANGED.
  `checks/docstring-header.txt` shows both bodies before and after.
- **Imports:** `checks/imports.txt` (the closures above, from `tools-used/impcheck.py` and `impdelta.py`).
- **Build** (`build/`): from the base snapshot, the round-1 22-module set, all rc 0 with 0 errors and 0 sorries,
  through root `TCSlib` and `audits/pass-shelat/Checks`. `build/vs-ledoc-build.txt`: against the `649c4888` build,
  every module's source, olean and log are the same except `Encoding`'s source and olean. So the new import changes no
  other olean, `Reduction` and `FromDiscreteLog` included, and adds no warning. The whole-tree check covers 1207
  modules: RESULT OK.
- **Rule 10, for `Encoding.lean`** (`rule10/`): seals A and B pass, strict and coe, each rc 0 with its install and EOF
  records. The request sets are 948/949 (strict A/B) and 947/948 (coe A/B), against 924/925/923/924 in the review.
  `seal-rows-vs-review.txt`: no review row is gone, every common row is identical, and the 24 new rows all come from
  the 4 newly imported modules. Paired controls (`padFin`, `splitBits`, and in B `PolyExpr.eval`, the tool's rows that
  fall in `Encoding`'s request sets): 8 probes, 10 sealed negatives, each failing exactly once; `ctlcheck.log`
  ALL_OK.
- **The other 8 files were not re-sealed.** Their sources and oleans are byte-identical to the `649c4888` build, so
  their round-1 seal results stand. Is that sound?
- **Axioms** (`axioms/`): `dlHash_crh` and `inputWord_take` depend on `[propext, Classical.choice, Quot.sound]`;
  `inputWord_split` on `[propext, Quot.sound]`.
- **Lint** (`logs/`): 92 FAIL / 102 WARN at `d356381a`, with the same FAIL and WARN lines as at `649c4888`. Only
  `Encoding.lean`'s INFO line count changes (199 → 201).
- **Restore:** `dl-oleans` is back at the base snapshot, SHA-256 `457ba704…`.

### 2. G24-02 and G24-03: are the errata correct?

- **G24-02** is an inline erratum in `fills/dl-crh/final-r1/review.md`, Content step 2. That file is in
  `verification-r2.zip` with the pinned round-1 copy `gates/24-dl-crh/review.md` (= the round-1 outbox's `review.md`).
  The two differ in exactly 3 hunks: the verdict line and the LE-doc docaudit line (both disclosed in round 1's
  "Slips in `review.md`") and step 2. Step 2 now says that a collision with *equal* selector bits is impossible, by
  cancellation and `expF_injective`, and that with different selector bits the reduction applies.
- **G24-03** is an erratum to the round-1 pack, ruling 3, recorded in `resolutions-r1.md` because the pack is pinned.
  The FAIL lines are identical at the head and the tip. Two `DiscreteLog` WARN lines change: `1192 → 1212` lines, and
  6 → 5 public definitions without a lemma (after `expSampleRaw_eq`). The counts stay at 92 FAIL / 102 WARN.
  `trial-307b-evidence.zip`'s `lint/lint-tip-vs-trial.diff` shows the same two changes against the current tip.

Check that each erratum now states what the Lean and the archived evidence show.

### 3. Do the trial merges show that #307 combines cleanly with the merged tip?

`trial-merge-r1/` holds two builds, each a ZIP with its manifest and `PROVENANCE`. Each ZIP's entries are its
manifest's paths plus an inner `SHA256SUMS` that is byte-identical to the manifest.

| | `trial-307-evidence.zip` | `trial-307b-evidence.zip` |
|---|---|---|
| SHA-256 | `a158a3d6ec689d912b7627589a613a6a91895403594a1ea49f166d35d10298c3` | `01e9e57a637755b854eb0c7ff820abee09ccf206cfd24e5fa814d67462645620` |
| Manifest, `PROVENANCE` | `evidence-SHA256SUMS` (142), `PROVENANCE.txt` | `evidence-b-SHA256SUMS` (152), `PROVENANCE-b.txt` |
| Tip merged onto | `996d7cc2` (after #308, #309) | `fb674b96` (after #306 as well) |
| `git merge-tree` tree | `c60af4c2`, no conflict | `84a1cbd8`, no conflict |
| Changed since `eff2dcd0` | 40 `.lean`: #303 4, #308 9, #309 17, facade, #307 9 | 51: the same plus #306 11 |
| Built | 48/48 rc 0 | 61/61 rc 0 |
| Whole-tree check | 1231 modules OK | 1241 modules OK |
| Constants of #307 vs the other units | 211 vs 430 | 211 vs 725 |

In both builds:
- **Integration:** each merge tree differs from its tip only in #307's 9 files, each with `d356381a`'s blob, and the
  tip's changes since `a757b6a1` touch none of them. Every module rebuilds downstream of the changes, through root
  `TCSlib` and `audits/pass-shelat/Checks`, with 0 errors and 0 sorries.
- **No new warning:** 22 warnings, all inherited (DDH 3, `Lamport/Blocks` 2, `InversionProbability` 2, `MachineSpec` 2,
  `Realization` 1, `Rejection` 10, `Extraction` 2). Every module's olean and log equal those of a per-PR build:
  #307's is `gate24-r1-evidence.zip`, and #308/#309's and #306's are the combined-308-309 record (in
  `verification-r2.zip`).
- **No name clash:** no log contains `ambiguous`, `already declared`, `already contains`, `import failed` or
  `overloaded`. The supplementary probe `axioms/NameOverlapTrial.lean` finds 0 fully-qualified collisions. The
  last-component overlaps (12, then 28) are all auto-generated `congr_simp` lemmas.
- **Axioms:** `dlHash_crh`, `hashAndSign_oneTimeSecure`, `lamport_oneTimeSecure`, `exists_oneTimeSecure_of_crh_owf`
  and, in the second build, `ccaScheme_cca2` each use only `[propext, Classical.choice, Quot.sound]`.
- **Lint:** 92 FAIL / 101 WARN at the tip and at the merge. The only difference is #307's two accepted `DiscreteLog`
  WARN changes (G24-03). The per-PR head has 102 WARN because one `Lamport.lean` WARN is resolved by #309.
- **Restore:** `dl-oleans-2` is back at `457ba704…`.

The current tip `47e6cf47` is records only after `fb674b96`. Its merge with `d356381a` (tree `b8b1308a`) differs from
`84a1cbd8` only in records, so the second build is #307 merged onto the current tip.

Do the trial merges show that #307 combines with #303, #306, #308 and #309 with no name clash, no new warning and only
the standard axioms?

### 4. Is anything new since round 1?

- `git diff 649c4888 d356381a` is the one LE-reuse hunk set in `Encoding.lean`; `pr.diff-r2.txt` is the round-1 diff
  plus that change (9 paths, 1523 insertions, 5 deletions).
- `source-head-r2.json` differs from `source-head.json` only in `Encoding.lean` (SHA-256 `0cea7598…`, 201 lines, none
  over 100 characters).
- `sources-r2.zip`, the source closure at `d356381a`, is the round-1 `sources.zip` plus `ReductionSupport.lean` and
  `Pseudorandom/Generators.lean` (128 files); every other entry is unchanged.

Does LE-reuse, or the merged tip, introduce anything that round 1 would have raised?

## Known dispositions and slips (not findings)

- **The rest of DL-41** (the `ofFn_splitBits_*` restatements and the disclosed overlaps) stays open and deferred, as in
  round 1. The ledger row (in `verification-r2.zip`) records what LE-reuse paid.
- **The G24-02 erratum's example omits the challenge.** It gives `p=3, m=2, g=2` and says `(0,false)` and `(0,true)`
  both hash to `1`. That holds only for `z = 0` (key `y = g^0 = 1`), as round 1's finding states. With `z = 1` they hash
  to `1` and `2`. The erratum's claim about the step is unaffected.
- **Names in `landing-r1/PROVENANCE.txt`.** It refers to the patch as `0001-LE-reuse.patch` and to the ZIP as
  `../dl-crh-r1-reuse-evidence.zip`, their job-local names. The records copies are
  `0001-dl-crh-landing-edit-LE-reuse-…patch` and `gate24-r1-evidence.zip`, with the same bytes; the patch is the
  ZIP's `0001-LE-reuse.patch`.
- **The tree in `resolutions-r1.md`.** Its "Next" paragraph gives the trial-merge tree `e0415be6`. That is the merge
  onto `b1c3cb6a`, the tip when it was written. It differs from the built `c60af4c2` only in records.
- **The `review.md` errata.** The round-1 pack called the review "a frozen record that is not edited". After the pin,
  inline errata were added to `fills/dl-crh/final-r1/review.md` (verdict line and docaudit line on 2026-11-14, and now
  G24-02). The pinned copy `gates/24-dl-crh/review.md` is unchanged.
- **Stale facade prose** (trial 2's observation): `Encryption/PrivateKey.lean:69` still calls `ccaScheme_cca2`
  pending. It is #306's file, not #307's, and is noted for the cleanup job.

## Evidence

- **`resolutions-r1.md`:** the dispositions and the LE-reuse summary.
- **`landing-r1/`:** the LE-reuse patch, `PROVENANCE.txt` (= the ZIP's), `gate24-r1-evidence.zip` and its manifest.
- **`trial-merge-r1/`:** the two ZIPs, their manifests and their `PROVENANCE` (each = its ZIP's).
- **`verification-r2.zip`** (10 entries; `SHA256SUMS` lists every other entry, and `PROVENANCE.txt` gives each source):
  byte-identical originals at records `47e6cf474ce4f7507eee9f945b973afbcbc40e96`:
  - the review with its errata and its pinned round-1 copy;
  - the decision log (Gate 24 rows of 2026-11-14) and the duplication ledger (DL-41);
  - the combined-308-309 record `maintainer/combined-308-309-2026-11-14/`: README, `PROVENANCE`, manifest and
    `combined-308-309-evidence.zip` (SHA-256 `2bf080d7…`, 128 manifest files plus `SHA256SUMS`).
- **`pr.diff-r2.txt`:** `git diff` from the base to `d356381a`, 9 paths.
- **`source-head-r2.json`:** hashes, line counts and over-width counts of the 9 changed files at `d356381a`.
- **`sources-r2.zip`:** the source closure at `d356381a` of every changed module, 128 files.
- **Round 1:** `outbox/gates/24-dl-crh-gate/` on the exchange at `e7b9e53e4a41ffa84b52deb17d34d144877d31f3`, with
  records `b01c150512fe6668ee6dddb1c6b429d1b9c822bf` (its `verification.zip` holds the review and LE-doc evidence).

## Findings delivery

Return `gate24-dl-crh-r2-findings.md` as Markdown in this chat. If you have several evidence files, return a ZIP. Use
the same table and severities as round 1, and say for each round-1 finding whether it is closed. Report the audited
head and the counts by severity. The gate closes at zero blockers and zero majors.

## ===== briefs/pass-shelat-ch5-8/gates/24-dl-crh/resolutions-r1.md =====

# Gate 24 · resolutions, round 1 · round 2 to follow

Codex's verdict is **HOLD**: 0 blockers, 1 major, 2 minors and 0 notes.
- **Findings:** `findings/gate24-dl-crh-findings.md`, SHA-256 `f29e4cb936dff2a470c58ccd405f6f37d755297eeefdc462e8bfd99494a4b689`.
- **Audited head:** `649c4888f23fbb9df71d555e952d1149a0aaa00b`.

| # | Severity | Disposition |
|---|---|---|
| G24-01 | major | **Fixed by LE-reuse** `d356381aadc350860f9a0e97123e84d9aefa585b` (tree `c7b77d28fa11c95a00789102e8d9410fc931bf63`), proof only. `inputWord_take` now reads `take_ofFn_castLE`, and `inputWord_split` is `ofFn_eq_init_append`, which also clears that DL-41 item. Re-audit in round 2. |
| G24-02 | minor | **Erratum** in `fills/dl-crh/final-r1/review.md`, Content step 2. A collision with *equal* selectors is impossible; the review had said *different*. The Lean proof and the target's sketch were already correct. |
| G24-03 | minor | **Erratum** to the pack, ruling 3. FAIL lines are identical at the head and the tip, but two `DiscreteLog` WARN lines change (`1192 → 1212` lines; missing readers `6 → 5`, after `expSampleRaw_eq`). The counts stay at 92 FAIL / 102 WARN. These two WARN changes are the accepted ones. The pack is pinned, so the correction is recorded here. |

## LE-reuse (`d356381a`)

**What changed.** Only `Hashing/FromDiscreteLog/Encoding.lean`, which grows from 199 to 201 lines:
- `inputWord_take := (take_ofFn_castLE (Nat.le_succ n) x).trans (congrArg List.ofFn (funext fun _ => congrArg x (Fin.ext rfl)))`.
- `inputWord_split := ofFn_eq_init_append x`.
- A new `import TCSlib.Cryptography.Asymptotic.ReductionSupport`. It is a real addition: it brings `ReductionSupport`,
  `Foundations.Negligible`, `Pseudorandom.Generators` and `Pseudorandom.Indistinguishability` into `Encoding`'s
  closure. `Authentication` and root `TCSlib` already import them, and none of them imports a unit module, so there
  is no cycle.
- The names, types and docstrings of both theorems are byte-identical.

**Statements.** decls2 against `649c4888` is empty, and all 198 headers are byte-identical.

**Build**
- On `dl-oleans`, the same 22 modules as the LE-doc build give rc 0, through root `TCSlib` and
  `audits/pass-shelat/Checks`.
- Only `Encoding`'s olean changed.
- The whole-tree check covers 1207 modules: OK.

**Rule 10**
- `Encoding.lean` passes seals A and B, strict and coe. Its request sets grow by the 24 rows that come from the newly
  imported modules; every earlier row is unchanged.
- Paired controls (`padFin`, `splitBits`, `PolyExpr.eval`): ALL_OK.

**Axioms.** `dlHash_crh` uses only the standard three.

**Lint.** 92 FAIL / 102 WARN, with the same FAIL and WARN lines as before.

**Restore.** `dl-oleans` is back at the base snapshot `457ba704…`.

**Evidence.** `landing-r1/gate24-r1-evidence.zip`, SHA-256
`6c1802139817f3fc033a50ecec1e9a8ff6f953bccad5b82b02f4c9bddb94fa22`. The patch is in `landing-r1/`.

**Next.** A trial-merge build onto the records tip (which now includes #308 and #309; the merge is conflict-free,
tree `e0415be6`) is running. After it, round 2 is staged for Codex.

## ===== briefs/pass-shelat-ch5-8/gates/24-dl-crh/findings/gate24-dl-crh-findings.md =====

# Pass–shelat Gate 24 — dl-crh findings

**Verdict: HOLD.** One major duplication finding remains outside the supplied dispositions. No mathematical, frozen-statement, or Rule-10 defect was found. Two additional findings concern audit-record prose.

| Blocker | Major | Minor | Note |
|---:|---:|---:|---:|
| 0 | 1 | 2 | 0 |

Audited [draft PR #307](https://github.com/Shilun-Allan-Li/tcslib/pull/307):

- Lean head: `649c4888f23fbb9df71d555e952d1149a0aaa00b`.
- PR base: `a757b6a18785377c158312ed051b1789cf45badf`.
- Records: `b01c150512fe6668ee6dddb1c6b429d1b9c822bf`.
- Exchange: `e7b9e53e4a41ffa84b52deb17d34d144877d31f3`, `outbox/gates/24-dl-crh-gate/`.

## Findings

Paths in this table are relative to the repository, except `pack.md` and `review.md`, which are relative to the gate pack.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G24-01 | **major** | `TCSlib/Cryptography/Hashing/FromDiscreteLog/Encoding.lean:73` · `inputWord_take` | An additional public result is re-proved without a disposition covering the overlap. | It specializes public `TCSlib.Cryptography.take_ofFn_castLE`, `Asymptotic/ReductionSupport.lean:288`; the finite-index embeddings agree pointwise. See comparison below. DL-41 enumerates other restatements and omits this one. | Reuse the existing public proof, directly or through a thin reader, and recheck the affected imports/seals; alternatively obtain an explicit disposition covering this overlap. |
| G24-02 | minor | `review.md:92` · Content, step 2 | The review reverses the selector argument: it says equal images under **different** selectors are impossible. | With `p=3`, `m=2`, `g=2`, `z=0`, the distinct inputs `(0,false)` and `(0,true)` both hash to `1`. The Lean lemma and frozen target sketch correctly rule out collisions with **equal** selectors. | Append an erratum to the gate record, preserving the frozen review. |
| G24-03 | minor | `pack.md:99–100` · ruling 3 | The claim that FAIL and WARN lines are identical, with an empty r3 diff, contradicts the archived evidence. | `ledoc-evidence.zip/logs/lint-crypto-tip-vs-head-r3.diff` is **674 bytes**. Two `DiscreteLog` WARN lines change: size `1192 → 1212`, and the missing-reader count `6 → 5` after adding `expSampleRaw_eq`. FAIL lines are identical; counts remain `92 FAIL / 102 WARN`. | Correct the description to distinguish unchanged FAIL lines from these two accepted WARN changes. |

### G24-01: exact overlap and its disposition

The existing public lemma states

```lean
theorem take_ofFn_castLE {ℓ m : ℕ} (h : m ≤ ℓ) (f : Fin ℓ → Bool) :
    (List.ofFn f).take m = List.ofFn fun i : Fin m => f (Fin.castLE h i)
```

Specialize its bounds to `n+1` and `n`, with proof `Nat.le_succ n`. For every `j : Fin n`,

\[
\bigl(\mathrm{Fin.castLE}\;(\mathrm{Nat.le\_succ}\;n)\;j\bigr).\mathrm{val}
=j.\mathrm{val}
=(j.\mathrm{castSucc}).\mathrm{val}.
\]

`Fin.ext` identifies the embeddings, so this specialization gives exactly

```lean
(List.ofFn x).take n = List.ofFn (fun j : Fin n => x j.castSucc)
```

The new reader instead derives this again from `inputWord_split` and `List.take_left'`. The existing result is present at the pinned head and is unchanged by this PR. Its file has Git blob `a314f02fe231ef4a64f02a7b68f53fd520760469` and SHA-256 `e79e05e05d01a6fff4e9d65970aa9e73ad457c9455b1ff987971c4eab7210934`.

The issued brief forbids copying public lemmas, and policy §1 requires explicit approval for duplicated proved material. The worker lists `inputWord_take` as a promotion candidate, but does not disclose this public overlap. Neither the pinned DL-41 row nor `evidence/PROMOTION.md` identifies `take_ofFn_castLE`. Listing a promotion destination does not record acceptance of this additional re-proof. The major concerns that missing disposition; the lemma itself is true.

## Proof and integrity checks

The proof matches [PS10, Protocol 142.2 and Theorem 142.3, pp. 142–143](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf), with the frozen, documented restriction on exponent inputs.

1. **Compression.** At generated indices above `G.n₀`, validity and well-formedness give `m>0`, exact output width `n`, and
   \[
   |D|=2m,\qquad |R|=p-1=m<2m.
   \]
   The evaluator writes a unit residue, so it lands in the specified range.
2. **Extraction.** Equal selectors permit cancellation; injectivity on bounded exponents then contradicts distinctness. For different selectors,
   \[
   z=\begin{cases}
   (x'+m-x)\bmod m,&b=1,\\
   (x+m-x')\bmod m,&b=0.
   \end{cases}
   \]
   The formal formulas use `x' + (m - x)` or `x + (m - x')`; the domain guards justify these subtractions. Equal exponent prefixes and the zero challenge are included.
3. **Reduction.** `collisionPost_split` covers arbitrary raw outputs using the collision game's padding/truncation. Exact hash-output lengths justify removing output padding. The polynomial-time reduction retains the finder's coins and advice and decodes the recovered exponent exactly.
4. **Probability.** Coin equivalences preserve independence. The published sampler law, including fallback zero and auxiliary finder coins, gives, for `n ≥ G.n₀`,
   \[
   \Pr[A\text{ collides}]\le G.\mathrm{dlProb}(B,n)+2^{-n}.
   \]
   Applying `hDL` to this concrete reduction and eventual domination proves negligible acceptance. Choosing actual acceptance as the negligible upper bound covers every parameter. Compression is eventual by its frozen definition; no arbitrary invalid-index claim is required.

| Check | Result |
|---|---|
| Pack integrity | **15/15** top-level SHA-256 entries verified. `verification.zip` has exactly its 44 manifested payloads plus its manifest. Nested review and LE-doc archives verify **478/478** and **128/128** entries, with exact member sets. |
| Pinned content | All **126** source-closure files match Git blobs in head tree `1d9f6d52d136f8bc8229bfaffe3c714aadb5eebd`. The six-patch series applies to independently retrieved base bytes and reproduces all **9** changed files exactly. |
| Freeze and exceptions | All **128** pre-existing declaration headers are byte-identical; pre-existing bodies other than the target are unchanged. The target docstring is unchanged. `DiscreteLog` gains exactly the two approved `rfl` readers and their documentation. The facade adds exactly six imports; its import graph is acyclic. |
| LE-doc | Removing doc comments leaves identical bytes in all **8** edited files. All **59** new formulas were compared with their declarations; no formula error found. The archived docaudit records **68/68 OK**. |
| Rule 10 | Independently reconstructed **48** head/base, strict/coercion, A/B and facade probe inputs. Requested sets equal the conservative closure inventories and cover elaborated-term references and matchers. Their source/log hashes and successful runs agree. All **12** controls match expectations: **21** sealed negatives fail once each, reader controls pass, and no stray errors occur. The archived explicit scan has 595 items and zero foreign-definition reads. |
| Axioms and admissions | Census **172 → 265**, with pre-existing types and attributes retained, no new simp attributes, instances or abbreviations, and only standard axioms. The target loses `sorryAx`; the issued-module admission census is **22 → 21**, solely the target. |
| Build evidence | All **22** final build rows have pinned source bytes, matching raw-log hashes, rc 0, zero errors and zero sorries. The archived **1207-module** object snapshot agrees with its latest successful run records. |
| Existing dispositions | DL-41's listed overlaps, the accepted `DiscreteLog` size/split follow-up, the projection-coercion ruling and the two disclosed review slips were not re-raised. |

**Verification limit:** no fresh Lean compilation was performed; this environment has no Lean executable. Compilation and seal execution conclusions use the authenticated archived runs, supplemented by independent source, patch, closure, census, control-log and hash checks. The archived object snapshot was checked for internal consistency; its oleans were not re-executed locally.

**Gate action:** hold for G24-01 until the public proof is reused or the additional overlap receives an explicit disposition. G24-02 and G24-03 are nonblocking record corrections. The user dispatches and merges; no repository changes or GitHub messages were made.

**Notation:** `n` is the security parameter; `i` a group index; `p=dlP i`, `m=dlM i=p−1`, and `g=dlG i`; `z` is the canonical challenge exponent; `x,x'` are bounded exponents and `b` the first selector; `D,R` are domain and range; `A` is the collision finder and `B=collisionReduction H A`; `G` is the instance generator and `H` the arithmetic bundle; `j` is a finite index. In the quoted existing lemma, `ℓ,m` are generic vector bounds, `h` their comparison proof, `f` a bit vector, and `i` its finite index.

## ===== briefs/pass-shelat-ch5-8/gates/24-dl-crh/landing-r1/0001-dl-crh-landing-edit-LE-reuse-inputWord_take-and-inpu.patch =====

From d356381aadc350860f9a0e97123e84d9aefa585b Mon Sep 17 00:00:00 2001
From: Claude <noreply@anthropic.com>
Date: Sat, 14 Nov 2026 21:37:24 +0000
Subject: [PATCH] dl-crh landing edit LE-reuse: inputWord_take (and
 inputWord_split) from the published ReductionSupport lemmas

Codex finding G24-01: Hashing/FromDiscreteLog/Encoding.lean re-proved
inputWord_take, a specialization of the public
TCSlib.Cryptography.take_ofFn_castLE (Asymptotic/ReductionSupport.lean).
It is now a thin reader of that lemma at m = n, l = n + 1 with
Nat.le_succ n; Fin.ext identifies Fin.castLE (Nat.le_succ n) j with
j.castSucc.

Review item DL-41: inputWord_split restated the public
ofFn_eq_init_append (same file) up to Fin.init; it is now that lemma,
read through the definitional unfolding of Fin.init.

Proof-only: both statements and docstrings are byte-identical (neither
docstring has a proof sketch to adjust). Encoding.lean now imports
TCSlib.Cryptography.Asymptotic.ReductionSupport directly. That module was
not in Encoding's transitive import closure before (it adds
ReductionSupport, Foundations.Negligible, Pseudorandom.Generators and
Pseudorandom.Indistinguishability to it); it does not import Encoding or
any module of this unit, so there is no cycle. Authentication and root
TCSlib already imported it.

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA
---
 .../Cryptography/Hashing/FromDiscreteLog/Encoding.lean | 10 ++++++----
 1 file changed, 6 insertions(+), 4 deletions(-)

diff --git a/TCSlib/Cryptography/Hashing/FromDiscreteLog/Encoding.lean b/TCSlib/Cryptography/Hashing/FromDiscreteLog/Encoding.lean
index cca76894e..fd751608a 100644
--- a/TCSlib/Cryptography/Hashing/FromDiscreteLog/Encoding.lean
+++ b/TCSlib/Cryptography/Hashing/FromDiscreteLog/Encoding.lean
@@ -6,6 +6,7 @@ import TCSlib.Cryptography.Candidates.Arithmetic
 import TCSlib.Cryptography.Asymptotic.Adversary
 import TCSlib.Cryptography.Authentication.Encoding
 import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
+import TCSlib.Cryptography.Asymptotic.ReductionSupport
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -65,14 +66,15 @@ theorem ofFn_splitBits_snd {a b : ℕ} (w : Fin (a + b) → Bool) :
 /-- The word of an `(n + 1)`-bit vector is its first `n` bits followed by its final bit:
 `List.ofFn x = List.ofFn (fun j : Fin n => x j.castSucc) ++ [x (Fin.last n)]`. -/
 theorem inputWord_split {n : ℕ} (x : Fin (n + 1) → Bool) :
-    List.ofFn x = List.ofFn (fun j : Fin n => x j.castSucc) ++ [x (Fin.last n)] := by
-  rw [List.ofFn_succ', List.concat_eq_append]
+    List.ofFn x = List.ofFn (fun j : Fin n => x j.castSucc) ++ [x (Fin.last n)] :=
+  ofFn_eq_init_append x
 
 /-- Taking the first `n` bits of an `(n + 1)`-bit word gives its restricted vector:
 `(List.ofFn x).take n = List.ofFn (fun j : Fin n => x j.castSucc)`. -/
 theorem inputWord_take {n : ℕ} (x : Fin (n + 1) → Bool) :
-    (List.ofFn x).take n = List.ofFn (fun j : Fin n => x j.castSucc) := by
-  rw [inputWord_split, List.take_left' (by simp)]
+    (List.ofFn x).take n = List.ofFn (fun j : Fin n => x j.castSucc) :=
+  (take_ofFn_castLE (Nat.le_succ n) x).trans
+    (congrArg List.ofFn (funext fun _ => congrArg x (Fin.ext rfl)))
 
 /-- Dropping the first `n` bits of an `(n + 1)`-bit word leaves its final bit:
 `(List.ofFn x).drop n = [x (Fin.last n)]`. -/
-- 
2.43.0


## ===== briefs/pass-shelat-ch5-8/gates/24-dl-crh/landing-r1/PROVENANCE.txt =====

dl-crh landing edit LE-reuse (Codex finding G24-01; review item DL-41), with build, Rule 10 seals, maintainer, 2026-11-14 UTC
$SP = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad. Paths below are relative to this directory.
Rules: python3 -I throughout; Lean 4.25.0 (cdd38ac5115b), PATH=$HOME/.elan/bin:$PATH; one Lean process at a time, only
  scripts/lean_check_tree.sh (worktree copy byte-equal to /home/user/tcslib/scripts/) through tools-used/review/runner.py with
  TCSLIB_OLEANS=$SP/dl-oleans (dl-oleans-2 not touched); no lake command; nothing pushed; /home/user/tcslib not edited (status clean).

landing: branch land/pass-shelat-dl-crh (PR #307), worktree $SP/wt-land-dl-crh. Not pushed: the branch is 1 commit ahead of
  origin/land/pass-shelat-dl-crh.
  parent LE-doc    649c4888f23fbb9df71d555e952d1149a0aaa00b (tree 1d9f6d52d136f8bc8229bfaffe3c714aadb5eebd)
  head   LE-reuse  d356381aadc350860f9a0e97123e84d9aefa585b (tree c7b77d28fa11c95a00789102e8d9410fc931bf63)
  author = committer = Claude <noreply@anthropic.com>; message logs/commit-msg.txt, ending with the two trailer lines
  (checks/commit.txt). Patch: 0001-LE-reuse.patch (git format-patch); diff checks/le-reuse.diff.
  checks/changed-paths.txt: one path, M TCSlib/Cryptography/Hashing/FromDiscreteLog/Encoding.lean
  (blob cca76894 -> fd751608; 199 -> 201 lines, max width 96, checks/widths.txt). The worktree is clean at the head.

edit (Encoding.lean; proof-only):
  (1) G24-01. inputWord_take now reads the public TCSlib.Cryptography.take_ofFn_castLE (Asymptotic/ReductionSupport.lean):
        (take_ofFn_castLE (Nat.le_succ n) x).trans
          (congrArg List.ofFn (funext fun _ => congrArg x (Fin.ext rfl)))
      Fin.ext rfl identifies Fin.castLE (Nat.le_succ n) j with j.castSucc. It no longer goes through inputWord_split.
  (2) DL-41. inputWord_split is now the term `ofFn_eq_init_append x` (same file of ReductionSupport); its statement is the lemma's
      with Fin.init x unfolded, which the elaborator accepts by unfolding Fin.init (a core/Mathlib definition, not sealed).
  (3) import TCSlib.Cryptography.Asymptotic.ReductionSupport added after the existing four imports.
  Statements and docstrings unchanged. Neither docstring had a `**Proof sketch.**` paragraph, so none was edited or added (the
  new proofs are one and two lines). An intermediate version used `fun j` and drew an unused-variable warning
  (logs/iteration/encoding-attempt1.log); the committed version compiles without a warning (attempt2.log, and the build below).

imports (checks/imports.txt; tools-used/impcheck.py, impdelta.py, source-level import graph):
  ReductionSupport was NOT in Encoding's transitive import closure at 649c4888 (65 project modules), so the import is not
  merely redundant. It adds 4 modules to Encoding's closure: Asymptotic.ReductionSupport, Foundations.Negligible,
  Pseudorandom.Generators, Pseudorandom.Indistinguishability. It also adds 3 modules to the closures of FromDiscreteLog/Reduction
  and Hashing.FromDiscreteLog, 2 to the closure of the Hashing facade, and 0 to Authentication and root TCSlib, which already had it.
  No cycle: ReductionSupport's closure (35 modules) contains none of the 9 unit modules. The build compiles it (rc 0).
  The effect on the build: Encoding's olean changes. Every other rebuilt olean, Reduction and FromDiscreteLog included, is
  byte-identical to the 649c4888 build (build/vs-ledoc-build.txt). No name clash, no new warning.

statements (statements/; tools-used/review/ = dl-crh review tools, below):
  unit-paths.txt = the 9 unit files (dl-crh-r1-ledoc landing/unit-paths.txt).
  decls2-vs-649c4888.tsv and .err: both empty (decls2g.py, 9 files): 0 ADDED/REMOVED/CHANGED/MOVED statements.
  decls2-vs-base.tsv (vs eff2dcd0): 67 ADDED. It equals the LE-doc record dl-crh-r1-ledoc statements/decls2-vs-base.tsv
    except for line numbers: decls2-vs-base-vs-ledoc.diff is empty, with `file:line` reduced to `file`.
  header-bytes-vs-649c4888.txt (headerbytes.py with touched-before.json = eff2dcd0 vs 649c4888 and touched-after.json = eff2dcd0 vs
    head, endpoint dlHash_crh): 198 compared (all 197 declarations of the 8 Lean files with declarations, private included, plus
    the endpoint), 0 different or missing. Hashing.lean has no declarations (imports only, unchanged).
  touched-649c4888-vs-head.tsv: 2 CHANGED (inputWord_split, inputWord_take), 195 UNCHANGED.
  checks/docstring-header.txt (tools-used/docheader.py): for both theorems, the docstring and the keyword-to-`:=` header are
    byte-identical; only the bodies differ (both shown).

build (build/, order/head-build.txt, logs/build-runner.out): the tree starts at base (below), so the full 22-module set of the
  LE-doc build was rebuilt (order/head-build.txt = dl-crh-r1-ledoc order/head-build.txt; its set = order/head-vs-base/down.txt from
  downorder.py d356381a vs eff2dcd0, imports-first consistent with order.txt). That set contains everything the brief names:
  Encoding; its unit downstream Reduction (order/head-vs-649c4888/down.txt: Encoding, Reduction, Hashing/FromDiscreteLog,
  Authentication, Hashing, TCSlib); Hashing/FromDiscreteLog; Hashing; Authentication, which imports Hashing.FromDiscreteLog
  directly (Authentication.lean:15) and so is downstream of Encoding; the #303 base-delta modules Rejection, Sampler,
  Extraction and Randomness; and root TCSlib. It also contains the DiscreteLog chain, needed because the base tree holds base
  DiscreteLog oleans, and audits/pass-shelat/Checks.
  22/22 rc 0, 0 errors, 0 sorry; warnings DDH 3, Rejection 10, Extraction 2 (all inherited, as in the LE-doc build).
  Sources: Encoding 0cea7598..., FromDiscreteLog fd4128f9..., Hashing 8a072ec7..., Authentication 27e81654..., TCSlib 942193a0...
  (build/results.jsonl). Checks log byte-identical to the LE-doc build's.
  Whole-tree head check build/tree-check-head.txt (treecheck.py; order/headfull-order.txt = LE-doc's, 1207 modules; records
  build/all-results-head.jsonl = base records + build/): every module's last record rc 0 at the d356381a source and olean hash,
  no stray olean, no empty dir: RESULT OK (build/snapshot-head.txt, 1238 files).

Rule 10 (rule10/). Tools: the dl-crh review tools from /home/user/tcslib/briefs/pass-shelat-ch5-8/fills/dl-crh/final-r1/
  review-evidence.zip (SHA-256 57461de5fb2cb5a8b9936864f3f813e1535a70535cb8b4306bc3ef030172e502; byte-equal to
  $SP/dl-review/dl-crh-r1-evidence.zip), extracted into the fresh directory $SP/dlcrh-r1-x and deleted after the job. Its tools/
  were copied unmodified to tools-used/review/ (diff -r empty) and run from that copy.
  collector: probe-sources/CollectHead.lean.txt = mkcollect.py(NmCollect.template.lean, order/head-owners.txt = the review's 8
    owners, title "dl-crh review collector (head)"), byte-identical to the review's probe-sources/head/CollectHead.lean. Run as
    DlProbe/CollectHead (probe-runs/, rc 0): CAT rows 2141 (review 2119: the definitions of the newly imported modules); MODULE
    stored counts equal to the review's (Encoding 25).
  seals for Encoding.lean (mkseals_ab.py strict, mkseals_coe.py coe; A, and B with SEAL_EVAL=1): seals/{A,B}, seals-coe/{A,B},
    mkseals-*.log. Requests A 948, B 949, coe A 947, coe B 948 (review 924/925/923/924). seal-rows-vs-review.txt: per variant, no
    review row is gone and all common rows are identical. There are 24 new rows, all homed in the 4 newly imported modules
    (preComp, wrap, finCastEquiv, Negligible, prgAdv, ...). Term readers and excluded terms are identical to the review's
    (6 terms, 0 excluded).
    Runs in seal-runs/ (seal-runner.out); summaries seals-A.tsv, seals-B.tsv, seals-coe-A.tsv, seals-coe-B.tsv (sealsum.py with
    statements/touched-after.json):
      strict A pass, strict B pass, coe A pass, coe B pass (each rc 0, 0 errors, install and EOF records present).
    As in the review (logs/seal-table.txt there: Encoding pass in A and B, strict and coe).
  paired controls for Encoding.lean (mkctl_dlcrh.py, run once on the strict records (seals-flat/) and once on the coe records
    (seals-coe-flat/); controls/, controls-coe/, controls-plan-all.json, control-runs/, controls-runner.out). Encoding's request
    sets contain 3 of the tool's rows, each a negative `rfl` body paired with its published reader: padFin (padFin_apply),
    Authentication.splitBits (splitBits_fst), and in B only Complexity.PolyExpr.eval (eval_const). The other rows
    (expSampleRaw, modularDifference, residueFinEquiv) are outside Encoding's closure. 8 probes (ControlS/ControlU for strict A,
    strict B, coe A and coe B) with 10 sealed negatives; each negative fails exactly once when sealed, and all positives and unsealed
    controls pass. ctlcheck.log (ctlcheck2.py): ALL_OK True.

axioms (axioms/, probe axioms/AxiomsHead.lean.txt run as DlProbe/AxiomsHead at d356381a, rc 0):
  TCSlib.Cryptography.Authentication.dlHash_crh depends on [propext, Classical.choice, Quot.sound];
  inputWord_take on [propext, Classical.choice, Quot.sound]; inputWord_split on [propext, Quot.sound].

lint (logs/): python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography from the worktree at d356381a
  (lint-crypto-head-d356381a.log): 92 FAIL, 102 WARN over 309 files. lint-crypto-head-649c4888.log = the LE-doc build's head
  lint (copied from dl-crh-r1-ledoc logs/): also 92/102. lint-649c4888-vs-head.diff (FAIL/WARN lines, whitespace-normalised) is
  empty: the FAIL and WARN lines are identical. lint-649c4888-vs-head-full.diff changes one line only, Encoding.lean's INFO line
  count (199 -> 201 lines).

olean tree $SP/dl-oleans:
  pre (tree/tree-check-pre.txt): at base before any Lean run: 1199 modules (order/basefull-1199.txt) rc 0 at eff2dcd0 source and
    at the object hashes of tree/base-records.jsonl (= dl-crh-r1-ledoc build/base-records.jsonl); no stray olean or empty dir;
    tree/snapshot-pre.txt (1230 files) byte-equal to dl-crh-r1-ledoc restore/snapshot-post.txt
    (tree/snapshot-ref-dl-crh-ledoc-post.txt; SHA-256 457ba704..., the same as the cca2-ett, hash-sign and lamport restores). RESULT OK.
  restore (restore/, logs/restore-runner.out): deleted the 10 probe oleans (restore/probe-oleans-deleted.txt; the 4 sealed
    controls fail by design and leave no olean), then the 8 head-only oleans (6 helpers, Rejection, Sampler) and the 2 emptied
    directories (restore/restore-deleted.txt). Then rebuilt order/restore-base.txt (= LE-doc's, 14 modules) from a git-archive
    export of eff2dcd0 (TCSlib, TCSlib.lean, audits, scripts, lean-toolchain; .lake/packages symlinked; removed afterwards):
    14/14 rc 0, 0 errors; the base FromDiscreteLog and Extraction keep their base sorry. Source and object hashes equal the
    base records (restore/restore-vs-base-records.txt RESULT OK). restore/tree-check-post.txt: RESULT OK; restore/snapshot-post.txt
    is byte-identical to tree/snapshot-pre.txt (SHA-256 457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f).
  The worktree's DlProbe/ (untracked probe sources) was removed; git status clean.

tools-used/: review/ = dl-crh review tools/ unmodified (runner, treecheck, downorder, touched, headerbytes, decls2g, mkcollect,
  mkseals_ab, mkseals_coe, mkctl_dlcrh, ctlcheck2, sealsum, archived-gate10-tools/, NmCollect.template.lean, ...).
  hunkdoc2.py, sketchaudit.py, sketchaudit_fix.py, prooflen.py = dl-crh-r1-ledoc tools-used/ unmodified (copied for
  reference, not needed here). New: impcheck.py, impdelta.py (import closure and cycle), docheader.py (docstring and header bytes).
  The cca2-ett-r1-ledoc directory no longer exists (only its zip). The build order and method are the dl-crh LE-doc job's
  (dl-crh-r1-ledoc-evidence.zip, extracted into the fresh directory $SP/dlcrh-ledoc-x, deleted after the job).
  $SP/ledoc-build-tools/ holds the LE-doc zip manifests and the rebase script; no rebase was done here.
SHA256SUMS: every file here except itself (paths without "./"); ../dl-crh-r1-reuse-evidence.zip holds exactly the manifest paths.

## ===== briefs/pass-shelat-ch5-8/gates/24-dl-crh/trial-merge-r1/PROVENANCE.txt =====

Trial-merge build of PR #307 (dl-crh, head d356381a) onto the records tip after #308 + #309, maintainer, 2026-11-14 UTC.
$SP = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad. Paths below are relative to this directory.
Method: as combined-308-309 (/home/user/tcslib/briefs/pass-shelat-ch5-8/maintainer/combined-308-309-2026-11-14/), whose
  evidence zip (SHA-256 2bf080d74de543025b9531b0ac7a43606dd60adba928eac55743502c967b51bb, = its README) was extracted into the fresh
  directory $SP/ref-308-309 (sha256sum -c of its SHA256SUMS OK; manifest byte-equal to evidence-SHA256SUMS) and deleted after the job.
  Its tools-used/ was copied unmodified to tools-used/ (diff -r empty) and run from that copy.
  Per-PR #307 records: /home/user/tcslib/briefs/pass-shelat-ch5-8/gates/24-dl-crh/landing-r1/gate24-r1-evidence.zip (SHA-256
  6c1802139817f3fc033a50ecec1e9a8ff6f953bccad5b82b02f4c9bddb94fa22, byte-equal to $SP/dl-review/dl-crh-r1-reuse-evidence.zip),
  extracted into the fresh directory $SP/ref-307-reuse (all 209 files OK against landing-r1/evidence-SHA256SUMS), deleted after.
Rules: Lean 4.25.0 (cdd38ac5115b), PATH=$HOME/.elan/bin:$PATH. One Lean process at a time. Every module checked by the export's own
  scripts/lean_check_tree.sh (SHA-256 366dab40e8e8f0f13e14118e14c3d6be1bc1b36604e6c9ccdebb03bc96cdf335, byte-equal to
  /home/user/tcslib/scripts/lean_check_tree.sh in all three exports; the script resolves ROOT from its own location, so the export
  copy is the one that compiles the trial sources) via tools-used/runner.py, TCSLIB_OLEANS=$SP/dl-oleans-2 only ($SP/dl-oleans not
  touched). No lake command. Python python3 -I. Nothing pushed; /home/user/tcslib not edited (git status clean before and after;
  only `git fetch`, `git ls-remote` and `git merge-tree --write-tree`, which writes objects to .git, were run against it).
  Full hashes from git rev-parse (order/commits.txt).

tip: origin/cryptography/pass-shelat-ch2-4 at fetch = 996d7cc2c08870c98ea6133def3f3d614fd7e9c8 (tree 64c26e6d15c0...). Records only
  after 53fb144d (b1c3cb6a, 996d7cc2; 0 .lean files changed 53fb144d..996d7cc2), so its .lean content is the combined-308-309 tip's.
  PR #307: refs/pull/307/head = d356381aadc350860f9a0e97123e84d9aefa585b (tree c7b77d28...), parent 649c4888; merge base with the tip
  a757b6a18785377c158312ed051b1789cf45badf.

step 1 (build/): build/tree-check-pre.txt: dl-oleans-2 at base before any Lean run: 1199 modules (order/basefull-1199.txt) rc 0 at
  eff2dcd0 source and at the object hashes of build/base-records.jsonl (= combined-308-309's = gate24 landing-r1 tree/base-records.jsonl);
  1230 files; no stray olean, no empty dir; build/snapshot-pre.txt byte-equal to combined-308-309 build/snapshot-pre.txt
  (build/snapshot-ref-308-309-pre.txt), SHA-256 457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f. RESULT OK.

step 2 (trial/): git merge-tree --write-tree --messages origin/cryptography/pass-shelat-ch2-4 d356381a: rc 0, no conflict, tree
  c60af4c22099ad1d595a3d8f763770c79cc25202 (trial/merge-tree.out, merge-tree.rc; trial/merge-base.txt).
  trial/tip-vs-merge-name-status.txt: the tree differs from the tip only in #307's 9 files (3 M: Candidates/DiscreteLog,
  Hashing, Hashing/FromDiscreteLog; 6 A: FromDiscreteLog/{Algebra,Coins,Encoding,Probability,Reduction,Sampling}); the path set equals
  `git diff --name-only a757b6a1 d356381a` (trial/pr307-files.txt), and every blob equals d356381a's (trial/merge-blobs-vs-307.txt, 9 SAME).
  The tip-side changes since a757b6a1 touch none of the 9 files.
  Export: git archive c60af4c2 (TCSlib, TCSlib.lean, audits, scripts, lean-toolchain = leanprover/lean4:v4.25.0; .lake/packages
  symlinked; no .lake/build) into $SP/exp-trial-307.
  order/git-diff-name-only.txt (git diff --name-only eff2dcd0 c60af4c2 -- '*.lean'): 40 files, no deletions or renames,
  = order/trial-vs-base/changed.txt (tools-used/downorder.py c60af4c2 vs eff2dcd0): #303 4, #308 9, #309 17, Authentication facade,
  #307 9. Downstream (order/trial-vs-base/down.txt) 48 = the 40 + DiscreteLogHardcore, DDH, ElGamal, Candidates, Encryption/PublicKey,
  Encryption, root TCSlib, audits/pass-shelat/Checks. order/trial-build.txt: the 48 in imports-first order (order.txt filtered to
  down.txt); order/order-check.txt: no import of a later module, and all 1182 other upstream modules are base modules with an olean.

step 3 (build/, logs/build-runner.out): 48/48 rc 0, 0 errors, 0 `declaration uses 'sorry'` (build/results.jsonl, build/mods/).
  Warnings (22): DDH 3, Lamport/Blocks 2, InversionProbability 2, MachineSpec 2, Realization 1, Rejection 10, Extraction 2; all others 0.
  build/objects-and-warnings-vs-pr-builds.txt (against the #307 per-PR build = gate24 landing-r1 build/results.jsonl at d356381a, and
  the combined-308-309 tip build): every module's source hash, olean hash and warning count equal those of a per-PR build (the #307
  modules and the DiscreteLog chain and Checks = #307's; Lamport*, HashAndSign* and Authentication = combined-308-309's; Rejection,
  Sampler, Extraction, Randomness, TCSlib = both). build/logs-vs-pr-builds.txt: every module log is byte-identical to the per-PR log
  of the same module (0 differ). So no new warning, and no new olean: the trial tree's objects are the union of the per-PR objects.
  Name clash / ambiguity: none. No log contains `ambiguous`, `already declared`, `already contains`, `import failed` or `overloaded`.
  The modules where #307's environment meets hash-sign and lamport (Authentication imports Hashing.FromDiscreteLog; root TCSlib imports
  the Hashing facade and Authentication; Checks) all give rc 0. HashAndSign* import only Hashing.CollisionResistant, not the facade.
  Supplementary probe (not in the 308-309 method), axioms/NameOverlapTrial.lean (run like the axioms probe, below): in the root
  environment, 211 constants declared in #307's 9 modules vs 430 in HashAndSign*, Lamport* and the Authentication facade:
  0 fully-qualified collisions; 12 last-component overlaps, all auto-generated `congr_simp` lemmas
  (dlHash.congr_simp, FromDiscreteLog.residueFinEquiv.congr_simp vs lamport, lamportGen, hashAndSign, LamportFill.*, LamportMachine.handler
  .congr_simp); no user-level short-name overlap.
  build/tree-check-trial.txt: 1231 modules (order/trialfull-order.txt = base 1199 + 32 new, order/trial-new-modules.txt) rc 0 at
  c60af4c2 source and olean hash (records build/all-results-trial.jsonl), 1262 files, no stray olean, no empty dir: RESULT OK
  (build/snapshot-trial.txt).

step 4 (axioms/): axioms/AxiomsTrial.lean (`import TCSlib`) run with tools-used/probe.sh (plain `lean`, same LEAN_PATH as the check
  script, no -o) from the export root; axioms/AxiomsTrial.log, lean rc 0:
    TCSlib.Cryptography.Authentication.{dlHash_crh, hashAndSign_oneTimeSecure, lamport_oneTimeSecure, exists_oneTimeSecure_of_crh_owf}:
    each depends on axioms [propext, Classical.choice, Quot.sound]; no sorryAx.
  A first attempt from axioms/ failed before Lean started (elan: no default toolchain outside a directory with lean-toolchain;
  axioms/AxiomsTrial-attempt1-no-toolchain.log). File count of dl-oleans-2 1262 before and after both probes (files-*.txt).
  Sorry census (census/): build census (tools-used/buildcensus.py, base records + build/): Authentication 1 warning in 1 of 32 modules
  (MAC/FromPRF, base, not rebuilt); Hashing 0 of 17. Source census (tools-used/srcsorry.py at c60af4c2): Authentication 1 token in 1 of
  31 files (MAC/FromPRF.lean); Hashing 0 of 16.

step 5 (lint/): python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography (script blob 88a2256b at 53fb144d, 996d7cc2, d356381a and
  c60af4c2; file SHA-256 016c1cb7...) from the trial export and from a git-archive export of the tip 996d7cc2 ($SP/exp-tip-996d):
  tip 92 FAIL, 101 WARN over 327 files; trial 92 FAIL, 101 WARN over 333 files (both rc 1, as FAIL lines exist).
  fw-*.txt = FAIL/WARN lines, whitespace-normalised. fw-tip.txt = combined-308-309 lint/fw-tip.txt (53fb144d) after normalisation.
  lint-tip-vs-trial.diff: exactly the two expected #307 WARN text changes on Candidates/DiscreteLog.lean:
    1192 -> 1212 lines > 1000; check 8: 6 -> 5 public defs without a lemma (expSampleRaw now has expSampleRaw_eq).
  lint-307head-vs-trial.diff (vs gate24 landing-r1 lint at d356381a, 92/102): one WARN fewer, Lamport.lean check 8 (lamportGen,
  lamportSign), resolved by #309. No FAIL/WARN line names an Authentication, Hashing or Randomness file.

step 6 (restore/): deleted the 32 trial-only oleans (restore/restore-delete-list.txt) and the 4 emptied directories not in the base
  snapshot (Randomness/Extraction, Hashing/FromDiscreteLog, Signatures/Lamport, Signatures/HashAndSign; restore/restore-deleted.txt).
  Rebuilt order/restore-base.txt (the 16 base modules overwritten, basefull order; imports-first checked on base sources) from a
  git-archive export of eff2dcd0 ($SP/exp-base-eff2): restore/results.jsonl, logs/restore-runner.out 16/16 rc 0, 0 errors (base
  Lamport, HashAndSign, Hashing/FromDiscreteLog, Extraction carry their base sorry). restore/restore-vs-base-records.txt: 16/16
  source and object hashes = base records. restore/tree-check-post.txt RESULT OK (1199 modules, 1230 files); restore/snapshot-post.txt
  byte-identical to build/snapshot-pre.txt and the combined-308-309 reference, SHA-256
  457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f.

addendum (trial/addendum-*): the tip moved during the job. At 22:02 UTC origin/cryptography/pass-shelat-ch2-4 became
  fb674b963b71ecdec6359133b37f0571013b6a05 ("Record #306 merge"; merge 7fdf3a9b of #306 cca2-ett, head b422ab5f): 11 .lean files
  (EncryptThenTag + 10 helpers). The build above is of #307 onto 996d7cc2 (the tip at fetch), not onto fb674b96.
  Not built: git merge-tree --write-tree fb674b96 d356381a: rc 0, clean, tree 84a1cbd822d41ffe01ac4c4a6a7cabaa04e77e0d; it differs from
  fb674b96 only in #307's 9 files, and from c60af4c2 only in #306's 11 .lean files plus records (addendum-trial1-vs-trial2.txt).
  #306's downstream from c60af4c2 (addendum-order/down.txt, 15: the 11, PrivateKey, Encryption, Composability, TCSlib) shares two
  modules with #307's (addendum-shared-downstream.txt): the Encryption facade and root TCSlib. That combination has not been built.

scratch: the three exports (trial, tip, base) and the two reference-zip extractions were deleted after use.
SHA256SUMS: every file here except itself (paths without "./"); ../trial-307-evidence.zip holds exactly the manifest paths plus SHA256SUMS.

## ===== briefs/pass-shelat-ch5-8/gates/24-dl-crh/trial-merge-r1/PROVENANCE-b.txt =====

Trial-merge build of PR #307 (dl-crh, head d356381a) onto the tip after #306 (fb674b96), maintainer, 2026-11-14 UTC.
Follow-up to ../trial-307 (onto 996d7cc2, before #306 merged; zip ../trial-307-evidence.zip, SHA-256
  a158a3d6ec689d912b7627589a613a6a91895403594a1ea49f166d35d10298c3), at the coordinator's request.
$SP = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad. Paths below are relative to this directory.
Method: as trial-307 = combined-308-309 (/home/user/tcslib/briefs/pass-shelat-ch5-8/maintainer/combined-308-309-2026-11-14/). Its
  evidence zip (SHA-256 2bf080d7..., = its README) was extracted again into the fresh directory $SP/ref-308-309 (SHA256SUMS OK); its
  tools-used/ was copied unmodified to tools-used/ (diff -r empty) and run from that copy. Per-PR references:
    pr307            = gate24 landing-r1 build at d356381a (gate24-r1-evidence.zip, SHA-256 6c180213..., extracted into fresh
                       $SP/ref-307-reuse, all files OK against landing-r1/evidence-SHA256SUMS);
    tip308-309       = combined-308-309 build/ (tip 53fb144d);
    pr306-on-308-309 = combined-308-309 trial/build/ (#306 b422ab5f merged onto 53fb144d; that README: hashes identical to Gate 23's);
    trial307         = ../trial-307/build/ (c60af4c2).
  Both extractions were deleted after the job.
Rules: Lean 4.25.0 (cdd38ac5115b), PATH=$HOME/.elan/bin:$PATH. One Lean process at a time. Every module checked by the export's own
  scripts/lean_check_tree.sh (SHA-256 366dab40e8e8f0f13e14118e14c3d6be1bc1b36604e6c9ccdebb03bc96cdf335, byte-equal to the repo's)
  via tools-used/runner.py, TCSLIB_OLEANS=$SP/dl-oleans-2 only. No lake command. Python python3 -I. Nothing pushed;
  /home/user/tcslib not edited (git status clean before and after; only git fetch, ls-remote and merge-tree --write-tree).
  Full hashes from git rev-parse (order/commits.txt).

commits: #306 merge 7fdf3a9b (parents 996d7cc2, b422ab5f) then "Record #306 merge" fb674b963b71ecdec6359133b37f0571013b6a05
  (11 .lean files 996d7cc2..fb674b96). At the end of the job origin/cryptography/pass-shelat-ch2-4 = c928e9a935487c56243b1ea43cb5759b09f0d4e5,
  records only after fb674b96 (0 .lean files), so the trial's Lean content is also that of #307 merged onto the current tip.

step 1 (build/): build/tree-check-pre.txt: dl-oleans-2 at base before any Lean run (1199 modules rc 0 at eff2dcd0 source and at the
  object hashes of build/base-records.jsonl; 1230 files; no stray olean or empty dir); build/snapshot-pre.txt byte-equal to the
  combined-308-309 reference (build/snapshot-ref-308-309-pre.txt) and to ../trial-307/restore/snapshot-post.txt, SHA-256
  457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f. RESULT OK.

step 2 (trial/): git merge-tree --write-tree --messages fb674b96 d356381a: rc 0, no conflict, tree
  84a1cbd822d41ffe01ac4c4a6a7cabaa04e77e0d (= the hash given in trial-307's addendum), merge base a757b6a18785377c158312ed051b1789cf45badf.
  trial/tip-vs-merge-name-status.txt: differs from fb674b96 only in #307's 9 files; all 9 blobs = d356381a's (merge-blobs-vs-307.txt);
  the tip-side changes since a757b6a1 touch none of them. trial/trial307-vs-trial307b.txt: 84a1cbd8 differs from c60af4c2 in exactly
  the 996d7cc2..fb674b96 paths (#306's 11 .lean + 2 records files); the 11 #306 blobs = b422ab5f's (306-blobs-vs-b422ab5f.txt, 11 SAME).
  Export: git archive 84a1cbd8 (TCSlib, TCSlib.lean, audits, scripts, lean-toolchain = v4.25.0; .lake/packages symlinked) into
  $SP/exp-trial-307b. order/git-diff-name-only.txt (eff2dcd0 vs 84a1cbd8, '*.lean'): 51 files, no deletions or renames,
  = order/trial-vs-base/changed.txt: #303 4, #306 11, #307 9, #308 9, #309 17, Authentication facade. Downstream 61 = the 51 +
  DiscreteLogHardcore, DDH, ElGamal, Candidates, Encryption/PublicKey, Encryption/PrivateKey, Encryption, Composability, root TCSlib,
  audits/pass-shelat/Checks. order/trial-build.txt: the 61 imports-first; order/order-check.txt: no violation; 1179 other upstream
  modules are base modules with an olean.

step 3 (build/, logs/build-runner.out): 61/61 rc 0, 0 errors, 0 `declaration uses 'sorry'`. Warnings 22: DDH 3, Lamport/Blocks 2,
  InversionProbability 2, MachineSpec 2, Realization 1, Rejection 10, Extraction 2; all others 0 (the 11 EncryptThenTag modules,
  PrivateKey, Encryption, Composability: 0).
  build/objects-and-warnings-vs-pr-builds.txt: every module's olean hash and (at equal source) warning count equal at least one
  per-PR reference; none unmatched. The two modules where #306 and #307 meet (Encryption facade, root TCSlib) have oleans identical to
  pr306-on-308-309's, pr307's and trial307's. build/logs-vs-pr-builds.txt: every module log byte-identical to each available per-PR
  log of the same module (0 differ). So: no new warning and no new olean.
  Clash / ambiguity: none. No log contains `ambiguous`, `already declared`, `already contains`, `import failed` or `overloaded`.
  Supplementary probe axioms/NameOverlapTrial.lean (trial-307's, with #306's EncryptThenTag* modules added to set B): 211 constants
  from #307's modules vs 725 from HashAndSign*, Lamport*, the Authentication facade and EncryptThenTag*: 0 fully-qualified collisions;
  28 last-component overlaps, all auto-generated `congr_simp` (2 #307 parents x 14 B parents); no user-level short-name overlap.
  build/tree-check-trial.txt: 1241 modules (base 1199 + 42 new, order/trialfull-order.txt) rc 0 at 84a1cbd8 source and olean hash,
  1272 files: RESULT OK.

step 4 (axioms/): axioms/AxiomsTrial.lean (`import TCSlib`) via tools-used/probe.sh (plain `lean`, no -o) from the export root,
  axioms/AxiomsTrial.log, lean rc 0:
    TCSlib.Cryptography.Composability.ccaScheme_cca2, TCSlib.Cryptography.Authentication.dlHash_crh (and, unchanged from trial-307,
    hashAndSign_oneTimeSecure, lamport_oneTimeSecure, exists_oneTimeSecure_of_crh_owf): each [propext, Classical.choice, Quot.sound].
  dl-oleans-2 file count 1272 before and after both probes.
  Census (census/): Authentication 1 sorry warning in 1 of 32 modules and 1 source token (MAC/FromPRF, base); Hashing 0 of 17 / 0 of
  16 files; Encryption/PrivateKey 0 of 27 / 0 of 26 files.
  Observation: the PrivateKey facade docstring (Encryption/PrivateKey.lean:69) still says "The CCA2 proof `ccaScheme_cca2` is pending".

step 5 (lint/): python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography (blob 88a2256b in both trees) on the trial export and a
  git-archive export of fb674b96 ($SP/exp-tip-fb67): tip 92 FAIL, 101 WARN over 337 files; trial 92 FAIL, 101 WARN over 343 files.
  lint-tip-vs-trial.diff (whitespace-normalised FAIL/WARN lines): exactly #307's two DiscreteLog.lean WARN text changes (1192 -> 1212
  lines; check 8: 6 -> 5 defs, expSampleRaw gone). lint-trial307-vs-trial307b.diff: empty (trial-307's FAIL/WARN lines identical).
  No FAIL/WARN line names an EncryptThenTag, Composability, Authentication or Hashing file.

step 6 (restore/): deleted the 42 trial-only oleans (restore-delete-list.txt) and the 5 emptied non-base directories
  (Randomness/Extraction, Hashing/FromDiscreteLog, PrivateKey/EncryptThenTag, Signatures/Lamport, Signatures/HashAndSign;
  restore-deleted.txt). Rebuilt order/restore-base.txt (19 overwritten base modules, base order, imports-first checked) from a
  git-archive export of eff2dcd0 ($SP/exp-base-eff2): 19/19 rc 0, 0 errors (base EncryptThenTag, Lamport, FromDiscreteLog,
  HashAndSign, Extraction carry their base sorry). restore-vs-base-records.txt: 19/19 source and object = base records.
  restore/tree-check-post.txt RESULT OK (1199 modules, 1230 files); restore/snapshot-post.txt byte-identical to build/snapshot-pre.txt
  and the combined-308-309 reference, SHA-256 457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f.
scratch: the three exports (trial, tip, base) and the two reference-zip extractions were deleted after use.
SHA256SUMS: every file here except itself (paths without "./"); ../trial-307b-evidence.zip holds exactly the manifest paths plus SHA256SUMS.

## ===== briefs/pass-shelat-ch5-8/fills/dl-crh/final-r1/review.md =====

# dl-crh · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS.** LE-facade and LE-doc are both done and built; see the LE-doc section at the
end (head `649c4888`, PR #307). *(Erratum 2026-11-14: this line said LE-doc was waiting for its rebuild. `DiscreteLog.lean`
goes 1192 → 1209 with the worker's readers and → 1212 with LE-doc; the issue-base-to-head diff of that file adds 20
lines and removes none.)*

## Delivery and landing branch

**Delivery**
- **Source:** Codex worker, exchange `9ad236d16ccc8054b947bb2e294f05b41842a29c` (`inbox/fills/dl-crh/`). There are 4
  patches on the issue base `eff2dcd0`.
- **Target:** `dlHash_crh`, [PS10, Theorem 142.3]: the discrete-log hash family is collision-resistant under the DL
  assumption. The brief is `../issued-r1/brief.md`, SHA-256 `21119b8a…`.
- **Files:**
  - `Hashing/FromDiscreteLog.lean`, the owned file;
  - 6 new helpers `Hashing/FromDiscreteLog/{Algebra,Coins,Encoding,Probability,Reduction,Sampling}.lean`;
  - `Candidates/DiscreteLog.lean`, the approved exception.

**Approved exception** (Seyoon, 2026-11-14)
- The frozen `Candidates/DiscreteLog.lean` gains two `rfl` readers, `expGenFun_eq` and `expSampleRaw_eq`.
- The diff is 17 lines added and none removed, in two hunks. Neither reader carries an attribute (the census
  shows `simp=false`).
- All 111 pre-existing declarations of the file are byte-identical (`landing/discretelog-readers-check.txt`).
- The file grows from 1192 to 1209 lines. This is accepted, and a split of the file is a follow-up.

**Landing branch:** `land/pass-shelat-dl-crh`.
- **Construction:** the patches were applied with `git am` at the base, keeping the worker's authorship (committed
  under Seyoon's git identity). They were then rebased onto records tip `48cd45ab`, past the #303 merge. The rebase
  had no conflict, and the unit's files are byte-identical before and after it.
- **Commits:**
  - `7a79c9cea47f554a758184a01b04045df9bed41f`: compression and collision extraction;
  - `d833008503fd92c10283d190a0e32658a2faad64`: the reduction;
  - `770789110b4f39ac55992770595cec5d2233a390`: the collision-resistance proof;
  - `5fcd585def9027dceb9922cc9f36eedf5598fdb4`: Rule-10 transports. This commit changes proofs only. It splits two
    `simp` calls and adds an explicit `congrArg` width transport in `collisionPost_split`.
  - **LE-facade** `a882dd03f14a3c9dc9b3ea3d9d6eb1fed37dda66`, tree `d392e50744a9b550686b3ac2862f863e3c662804`.
- **LE-facade** follows Seyoon's preference for a cleaner route than accepting six lint false positives. It adds exactly
  the six helper imports, alphabetically, after `…Hashing.FromDiscreteLog` in the frozen facade `Hashing.lean` (6
  insertions, 0 deletions; `landing/le-facade-diff.txt`). Lint returns to 216 FAIL.

**Evidence:** `review-evidence.zip`.
- SHA-256 `57461de5fb2cb5a8b9936864f3f813e1535a70535cb8b4306bc3ef030172e502`, 478 entries.
- Its manifest is `evidence-SHA256SUMS`, and `unzip -Z1` lists exactly the manifest's paths.
- Extracts are in `landing/`.

## Checks

**Integrity**
- `SHA256SUMS` verifies 2034/2034 and `evidence/SHA256SUMS` 2020/2020, with exact path equality.
- The issue package verifies 7/7 and `SOURCE-SHA256SUMS` 170/170.
- `git am` gives rc 0, and the resulting 8 files are byte-identical to `src/`.
- All 5 of the unit's exchange commits touch only `inbox/fills/dl-crh/`.
- The worker's commit hashes cannot be reproduced, because no committer metadata was delivered. This is recorded
  only.

**Build** on `$SP/dl-oleans-2`, verified first as a full base tree
- The 18 changed and downstream modules all give rc 0, 0 errors and 0 sorries, through root `TCSlib` and
  `audits/pass-shelat/Checks`. The Checks module is byte-identical to the base.
- After LE-facade, `Hashing`, the #303 base-delta modules and `TCSlib` give rc 0, with no name clash.
- Whole-tree check at `a882dd03`: 1207 modules plus 31 PFR modules, all at the head's hashes.
- The tree was restored to the base snapshot (`landing/tree-check-post.txt`).

**Statements**
- decls2 against `eff2dcd0`: 67 ADDED, 0 CHANGED, 0 REMOVED.
- The target's header is byte-identical, and only its body changed.
- All 128 pre-existing declarations of the two touched files are unchanged.

**Axioms**
- The target prints `[propext, Classical.choice, Quot.sound]`. At the base it also had `sorryAx`.
- Stored constants go from 172 to 265. None was removed, changed type or changed attributes. Every constant uses only
  standard axioms.
- There is no new `@[simp]`, instance or abbreviation.

**Rule 10**
- **Seals:** A and B pass for all 8 files at the head, in both the strict and the coe variant. The variants agree.
  The two pre-existing files also pass at the base.
- **Facade seals:** the LE-facade facade seals pass at the head and at the base.
- **Paired controls:** 12 probes with 21 sealed negatives, ALL_OK. They cover `padFin`, `PolyExpr.eval`, `splitBits`,
  `expSampleRaw`, `modularDifference` and `residueFinEquiv`.
- **Explicit-unfold scan:** 595 items, 0 foreign definitions.

**Admissions:** 22 → 21. Only the target was removed.

**Lint**
- The worker's head had 222 FAIL: six facade FAILs in `Hashing.lean`.
- After LE-facade the count is 216 FAIL / 102 WARN, with no new FAIL. Only the two WARN lines of `DiscreteLog`
  change: its size goes from 1192 to 1209, and `expSampleRaw` leaves the missing-reader list
  (`landing/lint-diff-final.txt`).
- No new line is over 100 characters. Every file is under 1000 lines except `DiscreteLog`, which was already over.

**Content.** The proof follows the source.
1. **Compression:** from the counts `|D| = 2m` and `|R| = p − 1 = m`.
2. **Equal selector bits:** a collision with *equal* selector bits is impossible, by cancellation and `expF_injective`; with different selector bits the reduction of step 3 applies. *(Erratum 2026-11-14, Gate 24 G24-02: this step previously said "different"; e.g. `p=3, m=2, g=2`: `(0,false)` and `(0,true)` both hash to `1`.)*
3. **The reduction:** it outputs `x' − x` or `x − x'` mod `m`, and it succeeds whenever the finder collides.
4. **Sampler switch:** switching to the close sampler costs `(1/2)^n`.
5. **Negligibility:** it follows from `hDL` from `G.n₀` on.

The edge cases are handled: parameters below `n₀`, invalid indices, `b = b'`, `x = x'` (which gives `z = 0`), the
`inDom` guards, and `w = 0`, fallback included.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| 1 | medium | 59 of the 68 new public declarations have docstrings without a formula (`landing/docaudit.tsv`). | **LE-doc**, docstrings only (the ext-nosrc and nm-sim precedents). It is written; the rebuild is pending. |
| 2 | low | **Undisclosed duplicates.** `FromDiscreteLog.inputWord_split` restates `ofFn_eq_init_append` (`Asymptotic/ReductionSupport.lean`), up to `Fin.init`. `ofFn_splitBits_fst/_snd` restate `ofFn_splitCoins_fst/_snd` (`CollectionsHelpers.lean`), because `splitBits` and `splitCoins` are the same split. There are also near relatives, listed after this table. | Ledger **DL-41**. |
| 3 | low | **Lint bug.** In `check_facade` (`scripts/campaign_style_lint.py:349`), the exemption for grandchildren imported through an intermediate facade looks for `Foo/Foo.lean` instead of the sibling facade `Foo.lean`. So the exemption never applies, and that accounts for most of the base's 173 facade-completeness FAILs. | Follow-up: fix the lint and re-baseline. This needs a decision, since every gate compares lint counts. |
| 4 | info | The approved `DiscreteLog` readers. | Recorded; see above. |
| 5 | info | Patch 4 changes proofs only. | Recorded. |
| 6 | info | The worker's commit hashes cannot be reproduced. | Recorded. |

**Near relatives for finding 2.** These are not copies:
- `expect_sample_eq_uexp`, next to `Games.Bridge.prob_sample_eq_uprob`;
- `residueFinEquiv`, which is Mathlib's `(ZMod.finEquiv m).symm` with `finCongr`;
- `boundedInputEquiv`, which resembles `Fin.snocEquiv`.

The disclosed overlaps re-derive private lemmas from public readers:
- `expUnit_pow_val`, against `dlb_expo_val`;
- `inputWord_num_ext`, against `fac_listToNat_inj`;
- `sumCoinsEquiv`, against `ofFn_splitCoins_symm_cast`;
- the `Sampling` switch, against `dla_statClose_expDec`.

## LE-doc · `649c4888` (built)

- **Head:** `649c4888f23fbb9df71d555e952d1149a0aaa00b`, tree `1d9f6d52d136f8bc8229bfaffe3c714aadb5eebd`.
- **Change:** 59 formula docstrings, including backticked equations in the docstrings of the two approved `DiscreteLog` readers (`DiscreteLog.lean` 1209 → 1212 lines). Docstrings only:
  - every hunk lies inside a doc comment, and with doc comments blanked the files are byte-identical;
  - all headers are byte-identical, and decls2 against the previous head is empty;
  - every new public declaration now passes the docaudit (68/68 OK; the target was already OK).
- **Rebase:** The branch was rebased onto `a757b6a1`; the unit files are byte-identical, and LE-facade is now `d84381ee`. The rebase makes Claude the committer of the worker commits; authors are unchanged.
- **Build** on `$SP/dl-oleans`: 22 modules (`DiscreteLog` and everything downstream, the helpers, `Hashing`, base-delta, root `TCSlib`, `audits/pass-shelat/Checks`) rc 0; Checks byte-identical to the base; full head check 1207 modules OK. The tree was restored to the base snapshot afterwards.
- **Lint (#305):** 92 FAIL / 102 WARN, with the same lines at the head as at the records tip.
- **Evidence:** `ledoc-evidence.zip`, SHA-256 `172de674962865dc2f1ab2eb754a2ee40fe13a92d35204b995b2d26d67eec4b6`, 128 entries. Its manifest is `ledoc-evidence-SHA256SUMS`, and extracts
  are in `landing-ledoc/`.
- **PR:** draft [PR #307](https://github.com/Shilun-Allan-Li/tcslib/pull/307).

## ===== briefs/pass-shelat-ch5-8/maintainer/combined-308-309-2026-11-14/README.md =====

# Combined-tree check after #308 and #309 (2026-11-14)

#308 (hash-sign) and #309 (lamport) were each built and gated on their own base. This check builds the tree that
results from merging them.

**Branch tip:** `53fb144d6658fe416ee60aa7c6ead417b8ca098c`. It is records only after merge `97ee2524`.

**Build.** Since `eff2dcd0`, 31 `.lean` files changed: #303, #308, #309 and the merged `Authentication` facade.
- All 32 modules, including root `TCSlib`, give rc 0, with 0 errors and 0 sorries.
- The merged facade is the only new source. Every other module's source and olean hashes equal those of the
  per-PR builds.
- The full tree check is OK: 1225 modules.

**Axioms at the tip.** `lamport_oneTimeSecure`, `hashAndSign_oneTimeSecure` and `exists_oneTimeSecure_of_crh_owf` each
use only `[propext, Classical.choice, Quot.sound]`. `exists_oneTimeSecure_of_crh_owf` no longer depends on `sorryAx`.

**Admissions.** The only admission left in `Authentication/` is `MAC/FromPRF.prfMAC_secure`, from the base. At
`eff2dcd0` there were 3.

**Trial merge with #306** (`b422ab5f`)
- `git merge-tree` gives tree `19fc0b6d564e805774d737904d437d68a17ec926`, with no conflict.
- The 11 `EncryptThenTag` files plus `PrivateKey`, `Encryption`, `Composability` and `TCSlib` build: 15/15 rc 0.
  Their hashes are identical to Gate 23's.
- The trial tree check is OK: 1235 modules.

**Lint:** 92 FAIL / 101 WARN at the tip and at the trial merge, with identical lines.

**Restore:** `dl-oleans-2` is back at the base snapshot (`457ba704…`).

**Evidence:** `combined-308-309-evidence.zip`, SHA-256
`2bf080d74de543025b9531b0ac7a43606dd60adba928eac55743502c967b51bb`. The manifest is `evidence-SHA256SUMS`.

## ===== briefs/pass-shelat-ch5-8/gates/24-dl-crh/pack.md =====

# Gate 24 · The discrete-log hash is collision-resistant (`dl-crh`, Theorem 142.3)

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #307](https://github.com/Shilun-Allan-Li/tcslib/pull/307) at
  `649c4888f23fbb9df71d555e952d1149a0aaa00b` (branch `land/pass-shelat-dl-crh`, tree
  `1d9f6d52d136f8bc8229bfaffe3c714aadb5eebd`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `a757b6a18785377c158312ed051b1789cf45badf` (the merge base).
  - The fill was issued on `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`, the merge of #299.
  - Between the issue base and the PR base, two merged PRs change non-record files: #303 (merge
    `d82e9a50414c6be160bcb3bd63ffdeb95e41e21c`, the four ext-nosrc files under `Randomness/`) and #305 (merge
    `8d0db40144102b847921b51ee2d1ebfd2994836d`, `scripts/campaign_style_lint.py` only). Neither touches a file of this PR.
    Every other commit in that range, and every commit from the PR base to the current records tip, touches records
    only (`PassShelatChapter5-8Plan.md` and `briefs/`). The PR diff equals the unit's diff from the issue base.
- **Commits:** 6.
  - The Codex worker's 4 patches (job `dl-crh`), applied with `git am` and rebased without conflict, authors kept
    (the worker committed under Seyoon's git identity): `4442667313d890e66bd388c7b5eebd2fc2ee1678` (compression and
    collision extraction), `aed68ef64a3f0e2a3bdca639921a5a658b1b7027` (the reduction),
    `fa182e66b0b93812a829c7f8eaa6ca3caf810733` (the collision-resistance proof) and
    `6500de6f32acaf1f18dd03a98ad3cac37e439da1` (Rule-10 transports; proofs only: two `simp` calls split and an explicit
    `congrArg` width transport in `collisionPost_split`).
  - Landing edit **LE-facade** `d84381eee69c6287174644076b1f01cbef287a2c`: import only, the six helper imports in the
    facade `Hashing.lean`.
  - Landing edit **LE-doc** `649c4888f23fbb9df71d555e952d1149a0aaa00b` (the head): 59 formula docstrings; docstrings
    only.
- **Scope:** a **proof audit**. The job proves the admitted `Authentication.dlHash_crh` [PS10, Theorem 142.3]: the
  discrete-log hash family of Protocol 142.2 compresses and is collision-resistant under the DL assumption. Its
  statement passed Gate 06 and is frozen.
- **Brief:** `fills/dl-crh/issued-r1/brief.md` on the records branch (SHA-256 `21119b8a…`; exchange pack `b436d19a`):
  three checkpoints following the docstring sketch, the owned file plus the helper directory `FromDiscreteLog/` only,
  `Games/Efficiency.lean` frozen, the duplication rule with "overlap" disclosures, and the evidence-completeness rule.

## What changed

All paths are under `TCSlib/Cryptography/`. The PR touches 9 Lean files: 3 modified and 6 new (1521 insertions,
5 deletions).

| File | Status | Lines |
|---|---|---:|
| `Hashing/FromDiscreteLog.lean` | owned, modified | 785 |
| `Hashing/FromDiscreteLog/Algebra.lean` | helper, new | 134 |
| `Hashing/FromDiscreteLog/Coins.lean` | helper, new | 67 |
| `Hashing/FromDiscreteLog/Encoding.lean` | helper, new | 199 |
| `Hashing/FromDiscreteLog/Probability.lean` | helper, new | 73 |
| `Hashing/FromDiscreteLog/Reduction.lean` | helper, new | 374 |
| `Hashing/FromDiscreteLog/Sampling.lean` | helper, new | 97 |
| `Candidates/DiscreteLog.lean` | frozen, approved exception | 1192 → 1212 |
| `Hashing.lean` | frozen facade, LE-facade | 31 → 37 |

The proof follows the source (REPORT § Delivered mathematics, review § Content):
1. **The honest key:** the approved readers `expGenFun_eq` and `expSampleRaw_eq` expose the generator and sampler; the
   key is `⟨i, expF i z⟩` with the sampled exponent (fallback included) below the positive order.
2. **Compression:** `|D| = 2m` and `|R| = p − 1 = m` with `m > 0` (`dlHash_compresses`, `card_boundedInput`,
   `card_boundedRange`), from `G.n₀` on.
3. **Collision shape:** equal images under equal selector bits are impossible (`unitCollision_selector_ne`, by
   `expF_injective`). For different selector bits `unitCollision_extract` recovers `z`: the residue of `x' + (m − x)`
   or of `x + (m − x')`.
4. **The reduction:** `collisionPost` pads or truncates the finder's output to two `(n+1)`-bit inputs and outputs the
   selected modular difference; it succeeds whenever the finder collides (`dlHash_reduction_success`).
5. **Sampler switch and negligibility:** switching to the close exponent sampler costs `(1/2)^n`
   (`sampleBelowL_uprob_le`), so for `n ≥ G.n₀` collision acceptance is at most `G.dlProb B n + (1/2)^n`
   (`dlHash_collision_bound`); `hDL B`, `negligible_two_pow_neg` and `Negligible.mono` finish.

The edge cases are parameters below `n₀`, invalid indices, `b = b'`, `x = x'` (which gives `z = 0`), inputs outside
the domain (the `inDom` guards) and `w = 0`, fallback included.

**Statements:** decls2 from the issue base to the head gives 67 ADDED, 0 CHANGED, 0 REMOVED. The target's header is
byte-identical and only its body changed; all 128 pre-existing declarations of the two touched files
(`FromDiscreteLog.lean`, `DiscreteLog.lean`) are unchanged.

## Rulings and records in force (2026-11-14)

1. **The `DiscreteLog` readers are an approved exception (Seyoon).** The worker asked in its chat; Seyoon's reply
   (verbatim in `worker/authorization/authorization.md`) allowed `expGenFun_eq` and `expSampleRaw_eq` in the frozen
   `Candidates/DiscreteLog.lean`; the decision log records the confirmation.
   - The worker's change is 17 lines added and none removed, in two hunks: two `rfl` readers placed beside their
     definitions (Rule 10's published-reader pattern), with no attribute (census `simp=false`). All 111 pre-existing
     declarations of the file are byte-identical (`landing/discretelog-readers-check.txt`).
   - LE-doc (ruling 4) then put a backticked equation into each reader's docstring; nothing else in the file changed.
   - **Size:** the file grows from 1192 to 1209 lines with the readers and to 1212 with LE-doc. `DiscreteLog` already
     held a recorded size exception; the growth is accepted, and **a split of the file is recorded as a follow-up**.
     Its 7 lines over 100 characters are the base's 7.
   - **Not a finding.** What you can raise: a reader that is not `rfl`-true to its definition, or any other change to
     the file.
2. **The six lint false positives were authorized, then replaced by LE-facade.** Under the old lint the delivery raised
   the Cryptography count from 216 to 222 FAIL: six `facade does not import child module` lines for the six helpers
   in the frozen `Hashing.lean`. Seyoon authorized exactly those six in the worker's chat ("Acknowledge exactly six lint
   false positives"; `worker/authorization/facade-lint-exception.md`), confirmed in the decision log, where Seyoon also
   states a preference for a cleaner route where one exists. The maintainer's landing edit **LE-facade** takes that
   route: it adds exactly the six helper imports, alphabetically, after `…Hashing.FromDiscreteLog` (6 insertions,
   0 deletions; `landing/le-facade-diff.txt`), the import-only pattern of the facade imports Seyoon approved for the
   other fills. The old lint returned to 216 FAIL, so the authorization is not used. The facade seals pass at the head
   and at the base (`landing/seal-table-facade.txt`).
3. **The facade-completeness lint fix, #305 (Seyoon's ruling to fix the bug by a PR on our branch; merged by
   Seyoon).** This review found the bug (finding 3): the grandchild exemption in `check_facade` looked for
   `Foo/Foo.lean` instead of the sibling facade `Foo.lean`, which produced most of the base's 173 facade FAILs. #305
   fixes it; the Cryptography baseline is now **92 FAIL / 102 WARN**, and the facade-import edits made for the old lint
   (LE-facade included) stay in place, harmless. At the head the lint gives 92 / 102 with the same FAIL and WARN lines as
   the records tip (`ledoc-evidence.zip`: `logs/lint-crypto-tip-vs-head-r3.diff`, empty).
4. **The landing edits are the maintainer's** (the ext-nosrc and nm-sim precedents; decision log rows of 2026-11-14).
   - **LE-facade** is import only (ruling 2).
   - **LE-doc** is docstrings only: its 60 hunks all lie inside doc comments; with doc comments blanked, all 8 files are
     byte-identical; all 197 declaration headers are byte-identical; decls2 against the LE-facade head is empty. It
     includes one re-wrap of a pre-existing 121-character line inside the module docstring of `FromDiscreteLog.lean`.
     The target's docstring, first line and `[PS10, Theorem 142.3]` tag are untouched.
5. **Rule 10: a `CoeFun`/`Coe` instance whose body is a structure projection is notation (Seyoon).** This is
   `FinDist`'s `⟨FinDist.prob⟩`. The coe-variant seals are canonical, and the strict variant is still run with its
   differences attributed. **For this unit the two variants agree:** seals A and B pass for all 8 files at the head and
   for the two pre-existing files at the base, with 0 failing declarations in either variant.

## What is frozen

- **The target's statement** (quoted in the brief), the 16 other pre-existing declarations of `FromDiscreteLog.lean`,
  the statement prose, the module's source notes and the global simp attributes.
- **Every file outside** `Hashing/FromDiscreteLog.lean` and `Hashing/FromDiscreteLog/`, except the two approved readers
  in `Candidates/DiscreteLog.lean` (and LE-doc's equations in their docstrings) and the six LE-facade imports in
  `Hashing.lean`. That includes `Hashing/CollisionResistant.lean` and `Games/Efficiency.lean`.
- **The landing edits:** LE-facade changes imports only, and LE-doc changes docstrings only.

## Questions for the audit

**1. Correctness against [PS10, Theorem 142.3]**
- Does the proof establish both conjuncts of the frozen statement, `Compresses` and `CollisionResistant`, under
  `hV` and `hDL`, for every parameter, including parameters below `G.n₀` and invalid indices?
- Compression: are the domain and range counts `2m` and `p − 1 = m` correct for the formal domain
  `{(x, b) : x < m}` and range `Z_p^*`, with exact output width `n`?
- Extraction: is every collision of distinct domain points either impossible (equal selectors) or a recovery of `z`
  (different selectors), including `x = x'` and `w = 0`?
- The reduction: is `collisionReduction` a legitimate DL adversary (uniform in the finder, polynomial-time
  `collisionPost`, the finder's coins and advice kept), and does it succeed on every finder collision, for arbitrary
  raw finder outputs (`collisionPost_split`)?
- Is the sampler switch's cost `(1/2)^n` correct, and does the final step use `hDL` correctly from `G.n₀` on?
- Does the edited target sketch describe the delivered proof?

**2. Frozen-statement integrity and the approved exception (ruling 1)**
- Are the target's header and every pre-existing declaration byte-identical (`landing/header-bytes.txt`,
  `landing/decls2.tsv`, `landing/touched.tsv`, `landing/discretelog-readers-check.txt`)?
- Is the `DiscreteLog` change exactly the two approved `rfl` readers plus LE-doc's docstring equations, with no
  attribute and no other effect?
- Is the `Hashing.lean` change exactly the six LE-facade imports, with no cycle and no change to what the facade's
  other imports export?

**3. Rule 10 (ruling 5)**
- Do the seals, collected from the elaborated terms plus matchers, cover every touched declaration of the 8 files over
  the full closure, at the base and at the head, in both variants (`landing/seal-table.txt`)? Do the consumers read
  `expGenFun` and `expSampleRaw` only through the new readers?
- Do the paired controls (12 probes, 21 sealed negatives, ALL_OK; `landing/ctlcheck.log`) show that the seals bite?
  They cover `padFin`, `PolyExpr.eval`, `splitBits`, `expSampleRaw`, `modularDifference` and `residueFinEquiv`.
- Explicit-unfold scan: 595 items, 0 foreign definitions.

**4. LE-doc formula accuracy**
- Does each of the 59 new formulas, including the two reader equations in `DiscreteLog.lean`, state what its
  declaration proves or defines (`landing-ledoc/0001-LE-doc.patch`; `docaudit-after.tsv` 68/68 OK)? A formula that
  misstates its declaration is a minor.
- Is LE-doc docstrings only, as ruling 4 records?

**5. Duplication**
- Does any new declaration duplicate a public TCSlib or Mathlib lemma beyond DL-41 (below)?
- Is any private lemma of another file copied rather than re-derived from published readers, beyond the four disclosed
  overlaps?

## Known dispositions (not findings)

- **DL-41** (duplication ledger, open, deferred):
  - undisclosed: `FromDiscreteLog.inputWord_split` restates `ofFn_eq_init_append` (`Asymptotic/ReductionSupport.lean`,
    up to `Fin.init`); `ofFn_splitBits_fst/_snd` restate `ofFn_splitCoins_fst/_snd` (`CollectionsHelpers.lean`),
    because `splitBits` and `splitCoins` are the same split;
  - disclosed overlaps, re-derived from public readers: `expUnit_pow_val` against `dlb_expo_val`, `inputWord_num_ext`
    against `fac_listToNat_inj`, `sumCoinsEquiv` against `ofFn_splitCoins_symm_cast`, the `Sampling` switch against
    `dla_statClose_expDec`;
  - near relatives, not copies: `residueFinEquiv` (Mathlib's `(ZMod.finEquiv m).symm` with `finCongr`),
    `boundedInputEquiv` (`Fin.snocEquiv`), `expect_sample_eq_uexp` (`Games.Bridge.prob_sample_eq_uprob`).
  The worker's promotion list is `evidence/PROMOTION.md` (exchange `9ad236d1`). What you can raise: a copy outside
  DL-41, or a disagreement with it.
- **The lint bug** the review found: fixed by #305 (ruling 3).
- **The `DiscreteLog` size and split:** accepted, with the split as a follow-up (ruling 1).
- **The worker's commit hashes** cannot be reproduced, because the delivery records no committer metadata. The content
  is verified: `git am` at the base reproduces the 8 delivered files byte for byte.
- **Patch 4 changes proofs only** (review finding 5).
- **Slips in `review.md`**, a frozen record that is not edited:
  - its verdict line says LE-doc "waits for its rebuild"; its closing LE-doc section records the build that followed;
  - that section says every new public declaration passes the docaudit "except the target, whose first line is prose".
    In fact `docaudit-after.tsv` is 68/68 OK: the target was already OK at the review (`landing-ledoc/PROVENANCE.txt`).

## Also check

**Axioms**
- The target prints `[propext, Classical.choice, Quot.sound]`. At the base it also had `sorryAx`.
- Stored constants go from 172 to 265; none was removed, changed type or changed attributes, and all use subsets of
  those three (the review's census; LE-facade and LE-doc change no proof).
- Nothing new is `@[simp]`, an instance or an abbreviation.

**Admissions:** 22 → 21 in the 12 issued modules; only the target is removed (`landing/sorry-census-final.txt`).

**Sizes and widths:** every file is under 1000 lines except `DiscreteLog` (ruling 1); no new line is over 100
characters (`source-head.json`: the 7 over-width lines of `DiscreteLog` are the base's).

**Build:** at `649c4888`, the 22 changed and downstream modules (`DiscreteLog` and its downstream `DiscreteLogHardcore`,
`DDH`, `ElGamal`, `Candidates`, `PublicKey`, `Encryption`; the helpers, `FromDiscreteLog`, `Authentication`, `Hashing`;
#303's 4 base-delta modules; root `TCSlib`; `audits/pass-shelat/Checks`, byte-identical to the base) have rc 0, 0
errors and 0 sorries (`landing/root-checks.jsonl`), and the whole-tree check passes for 1207 modules at the head's
source and olean hashes (`landing/final-tree-check.txt`). The olean tree was restored to the base snapshot afterwards.

## Evidence

- **`review.md`:** the maintainer's delivery review, verdict ACCEPT WITH LANDING EDITS, with its LE-doc section at the
  end.
- **`verification.zip`** (45 entries): every file the review cites, as byte-identical originals. Its `SHA256SUMS`
  lists every other entry, and `PROVENANCE.txt` gives each entry's source. It holds:
  - `review-evidence.zip` (`fills/dl-crh/final-r1/`, SHA-256 `57461de5…`, 478 entries) and
    `review-evidence-SHA256SUMS`, its manifest; `unzip -Z1` lists exactly the manifest's paths. It covers integrity,
    the build and the full-tree check with the restore, decls2, header bytes, `touched`, the docstring audit, the
    `DiscreteLog` readers check, the census and axioms, the strict and coe-variant seals at the base and the head, the
    facade seals, the paired controls, the scan, lint, sizes and the duplication grep;
  - `ledoc-evidence.zip` (SHA-256 `172de674…`, 128 entries) and `ledoc-evidence-SHA256SUMS`: the LE-doc patch, the
    docstring-only checks, the rebase onto `a757b6a1`, the build at the head, the #305 lint and the restore;
  - `landing/` and `landing-ledoc/`: the review's extracts, each a byte copy of an entry of the matching ZIP;
  - `records/`: the issue package `fills/dl-crh/issued-r1/`, the duplication ledger, the decision log and the #305
    record `maintainer/lint-facade-fix-2026-11-14/` (README and patch), at records
    `65d89e5700b283e5b9d373335c78b0cf8391bd35`;
  - `worker/authorization/`: the worker's `evidence/authorization.md` (Seyoon's replies, verbatim),
    `facade-lint-exception.md` (the six-FAIL request and reply) and `initial-escalation.zip` (the reader request), byte
    copies from exchange `9ad236d16ccc8054b947bb2e294f05b41842a29c`.
- **The worker's own evidence:** on the exchange at `9ad236d16ccc8054b947bb2e294f05b41842a29c`, under
  `inbox/fills/dl-crh/`. Its top-level `SHA256SUMS` lists 2034 files and `evidence/SHA256SUMS` 2020, all delivered.
- **`landing/`:** at the final head.
  - `root-checks.jsonl`: the 22 modules at `649c4888`, rc 0, each changed file's `source_sha256` matching
    `source-head.json` (= `build/results.jsonl` of `ledoc-evidence.zip`).
  - `final-tree-check.txt`: 1207/1207 modules at `649c4888`'s source and olean hashes
    (= `build/tree-check-head.txt` of `ledoc-evidence.zip`).
  - `axioms-head.txt`: the review's census and target axioms (= `final-r1/landing/axioms-summary.txt`).
- **`worker-report.md`:** the worker's `REPORT.md`, at exchange `9ad236d1`.
- **`pr.diff.txt`:** `git diff` from the base to the head (9 paths, 1521 insertions, 5 deletions).
- **`source-head.json`:** the head hashes, line counts and over-width counts of the 9 changed files.
- **`sources.zip`:** the source closure at the head of every changed module, 126 files.

## Findings delivery

Return `gate24-dl-crh-findings.md` as a Markdown file in this chat. If you have several evidence files, return a ZIP.
The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish the frozen statement, or a scope
  violation beyond the approved readers and the LE-facade imports.
- **major:** a changed frozen statement, a forbidden read in a touched declaration not covered by the rulings, an
  undisclosed copied private lemma, or necessary evidence that cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.

## ===== TCSlib/Cryptography/Hashing/FromDiscreteLog/Encoding.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Candidates.Arithmetic
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
import TCSlib.Cryptography.Asymptotic.ReductionSupport

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bounded exponents with a selector bit

The domain in Protocol 142.2 consists of an `n`-bit numeral below a bound `m`, followed
by one unrestricted selector bit. These encoding lemmas identify that domain with
`Fin m × Bool`.

## Main definitions

* `boundedInputEquiv` pairs a bounded exponent with its final selector bit.

## Main results

* `ofFn_splitBits_fst`, `ofFn_splitBits_snd` read the words of two consecutive bit vectors.
* `inputWord_num_ext` reconstructs an input from its exponent value and selector bit.
* `card_boundedInput` gives `2 * m` inputs when `m ≤ 2 ^ n`.
* `card_boundedRange` gives `p - 1` positive `n`-bit numerals below `p`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, §5.5.2, Protocol 142.2 and the proof of Theorem 142.3.
-/

namespace TCSlib.Cryptography.Authentication.FromDiscreteLog

open TCSlib.Cryptography TCSlib.Cryptography.Candidates TCSlib.Cryptography.NumberTheory

/-- The word of the first component of `splitBits w` is the first `a` bits of `w`:
`List.ofFn (splitBits w).1 = (List.ofFn w).take a`. -/
theorem ofFn_splitBits_fst {a b : ℕ} (w : Fin (a + b) → Bool) :
    List.ofFn (splitBits w).1 = (List.ofFn w).take a := by
  have hfst : (splitBits w).1 = fun j : Fin a => w (Fin.castAdd b j) :=
    funext fun j => splitBits_fst w j
  rw [hfst]
  have hwindow := ofFn_drop_take w 0 a (by omega)
  simpa only [List.drop_zero, Nat.zero_add] using hwindow.symm

/-- The word of the second component of `splitBits w` is the word of `w` after its first
`a` bits: `List.ofFn (splitBits w).2 = (List.ofFn w).drop a`. -/
theorem ofFn_splitBits_snd {a b : ℕ} (w : Fin (a + b) → Bool) :
    List.ofFn (splitBits w).2 = (List.ofFn w).drop a := by
  have hsnd : (splitBits w).2 = fun j : Fin b => w (Fin.natAdd a j) :=
    funext fun j => splitBits_snd w j
  rw [hsnd]
  have hwindow := ofFn_drop_take w a b (by omega)
  have hlen : ((List.ofFn w).drop a).length = b := by
    simp only [List.length_drop, List.length_ofFn, Nat.add_sub_cancel_left]
  rw [List.take_of_length_le hlen.le] at hwindow
  exact hwindow.symm

/-- The word of an `(n + 1)`-bit vector is its first `n` bits followed by its final bit:
`List.ofFn x = List.ofFn (fun j : Fin n => x j.castSucc) ++ [x (Fin.last n)]`. -/
theorem inputWord_split {n : ℕ} (x : Fin (n + 1) → Bool) :
    List.ofFn x = List.ofFn (fun j : Fin n => x j.castSucc) ++ [x (Fin.last n)] :=
  ofFn_eq_init_append x

/-- Taking the first `n` bits of an `(n + 1)`-bit word gives its restricted vector:
`(List.ofFn x).take n = List.ofFn (fun j : Fin n => x j.castSucc)`. -/
theorem inputWord_take {n : ℕ} (x : Fin (n + 1) → Bool) :
    (List.ofFn x).take n = List.ofFn (fun j : Fin n => x j.castSucc) :=
  (take_ofFn_castLE (Nat.le_succ n) x).trans
    (congrArg List.ofFn (funext fun _ => congrArg x (Fin.ext rfl)))

/-- Dropping the first `n` bits of an `(n + 1)`-bit word leaves its final bit:
`(List.ofFn x).drop n = [x (Fin.last n)]`. -/
theorem inputWord_drop {n : ℕ} (x : Fin (n + 1) → Bool) :
    (List.ofFn x).drop n = [x (Fin.last n)] := by
  rw [inputWord_split, List.drop_left' (by simp)]

/-- An `(n + 1)`-bit input is determined by its first `n` bits and its final bit:
`(List.ofFn x).take n = (List.ofFn y).take n → x (Fin.last n) = y (Fin.last n) → x = y`. -/
theorem inputWord_ext {n : ℕ} {x y : Fin (n + 1) → Bool}
    (hprefix : (List.ofFn x).take n = (List.ofFn y).take n)
    (hlast : x (Fin.last n) = y (Fin.last n)) : x = y := by
  apply List.ofFn_injective
  rw [inputWord_split x, inputWord_split y, ← inputWord_take x, ← inputWord_take y,
    hprefix, hlast]

/-- An `(n + 1)`-bit input is determined by the number read from its first `n` bits
and its final selector bit: `x = y` whenever `x (Fin.last n) = y (Fin.last n)` and
`listToNat ((List.ofFn x).take n) = listToNat ((List.ofFn y).take n)`. -/
theorem inputWord_num_ext {n : ℕ} {x y : Fin (n + 1) → Bool}
    (hnum : listToNat ((List.ofFn x).take n) = listToNat ((List.ofFn y).take n))
    (hlast : x (Fin.last n) = y (Fin.last n)) : x = y := by
  refine inputWord_ext ?_ hlast
  have hxlen : ((List.ofFn x).take n).length = n := by
    rw [inputWord_take, List.length_ofFn]
  have hylen : ((List.ofFn y).take n).length = n := by
    rw [inputWord_take, List.length_ofFn]
  have hxcanon := natToList_length_listToNat ((List.ofFn x).take n)
  have hycanon := natToList_length_listToNat ((List.ofFn y).take n)
  rw [hxlen] at hxcanon
  rw [hylen] at hycanon
  have hword := congrArg (natToList n) hnum
  rw [hxcanon, hycanon] at hword
  exact hword

/-- Bounded `(n + 1)`-bit inputs are exactly pairs of an exponent in `Fin m` and a selector
bit, provided `m ≤ 2 ^ n` [PS10, Protocol 142.2].

**Proof sketch.** Read the first `n` bits as the exponent and keep the last bit. In the other
direction write the exponent as an `n`-bit numeral and append the selector. Numeral
canonicity and the decomposition of an `(n + 1)`-bit vector prove the inverse laws. -/
noncomputable def boundedInputEquiv (n m : ℕ) (hm : m ≤ 2 ^ n) :
    {x : Fin (n + 1) → Bool // listToNat ((List.ofFn x).take n) < m} ≃ Fin m × Bool where
  toFun x := (⟨listToNat ((List.ofFn x.1).take n), x.2⟩, x.1 (Fin.last n))
  invFun z := ⟨padFin (n + 1) (natToList n z.1.val ++ [z.2]), by
    rw [ofFn_padFin_of_length (by simp), List.take_left' (by simp),
      listToNat_natToList (z.1.2.trans_le hm)]
    exact z.1.2⟩
  left_inv x := by
    apply Subtype.ext
    apply List.ofFn_injective
    rw [ofFn_padFin_of_length (by simp)]
    have hlen : ((List.ofFn x.1).take n).length = n := by
      simp
    have hcanon := natToList_length_listToNat ((List.ofFn x.1).take n)
    rw [hlen] at hcanon
    rw [hcanon, inputWord_take, inputWord_split x.1]
  right_inv z := by
    apply Prod.ext
    · apply Fin.ext
      change listToNat ((List.ofFn
        (padFin (n + 1) (natToList n z.1.val ++ [z.2]))).take n) = z.1.val
      rw [ofFn_padFin_of_length (by simp), List.take_left' (by simp),
        listToNat_natToList (z.1.2.trans_le hm)]
    · have hword := inputWord_drop
        (padFin (n + 1) (natToList n z.1.val ++ [z.2]))
      rw [ofFn_padFin_of_length (by simp), List.drop_left' (by simp)] at hword
      exact List.singleton_inj.mp hword.symm

/-- The bounded-input equivalence reads the exponent and the final selector bit:
`boundedInputEquiv n m hm x = (⟨listToNat ((List.ofFn x.1).take n), x.2⟩, x.1 (Fin.last n))`. -/
theorem boundedInputEquiv_apply (n m : ℕ) (hm : m ≤ 2 ^ n)
    (x : {x : Fin (n + 1) → Bool // listToNat ((List.ofFn x).take n) < m}) :
    boundedInputEquiv n m hm x =
      (⟨listToNat ((List.ofFn x.1).take n), x.2⟩, x.1 (Fin.last n)) := rfl

/-- The inverse equivalence writes an `n`-bit exponent and appends its selector bit:
`((boundedInputEquiv n m hm).symm z).1 = padFin (n + 1) (natToList n z.1.val ++ [z.2])`. -/
theorem boundedInputEquiv_symm_apply (n m : ℕ) (hm : m ≤ 2 ^ n) (z : Fin m × Bool) :
    ((boundedInputEquiv n m hm).symm z).1 =
      padFin (n + 1) (natToList n z.1.val ++ [z.2]) := rfl

/-- There are `2 * m` bounded exponents with a selector bit when `m ≤ 2 ^ n`
[PS10, proof of Theorem 142.3]. -/
theorem card_boundedInput (n m : ℕ) (hm : m ≤ 2 ^ n) :
    Fintype.card {x : Fin (n + 1) → Bool // listToNat ((List.ofFn x).take n) < m} = 2 * m := by
  classical
  rw [Fintype.card_congr (boundedInputEquiv n m hm), Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool, Nat.mul_comm]

/-- There are `p - 1` positive `n`-bit numerals below `p` when `0 < p ≤ 2 ^ n`
[PS10, proof of Theorem 142.3].

**Proof sketch.** Subtract one from the numeral's value to identify the range with
`Fin (p - 1)`. The inverse writes `j + 1` in `n` bits. Reading and writing numerals are
inverse on values below `2 ^ n`. -/
theorem card_boundedRange (n p : ℕ) (hp : 0 < p) (hpw : p ≤ 2 ^ n) :
    Fintype.card {y : Fin n → Bool //
      0 < listToNat (List.ofFn y) ∧ listToNat (List.ofFn y) < p} = p - 1 := by
  classical
  let e : {y : Fin n → Bool //
      0 < listToNat (List.ofFn y) ∧ listToNat (List.ofFn y) < p} ≃ Fin (p - 1) :=
    { toFun := fun y => ⟨listToNat (List.ofFn y.1) - 1, by
        have hpos := y.2.1
        have hlt := y.2.2
        omega⟩
      invFun := fun j => ⟨natToBits n (j.val + 1), by
        have hj : j.val + 1 < p := by have := j.2; omega
        rw [← bitsToNat_eq_listToNat, bitsToNat_natToBits (hj.trans_le hpw)]
        exact ⟨by omega, hj⟩⟩
      left_inv := fun y => by
        apply Subtype.ext
        change natToBits n (listToNat (List.ofFn y.1) - 1 + 1) = y.1
        have hpos : 1 ≤ listToNat (List.ofFn y.1) := by have := y.2.1; omega
        rw [Nat.sub_add_cancel hpos, ← bitsToNat_eq_listToNat, natToBits_bitsToNat]
      right_inv := fun j => by
        apply Fin.ext
        change listToNat (List.ofFn (natToBits n (j.val + 1))) - 1 = j.val
        have hj : j.val + 1 < p := by have := j.2; omega
        rw [← bitsToNat_eq_listToNat, bitsToNat_natToBits (hj.trans_le hpw)]
        omega }
  rw [Fintype.card_congr e, Fintype.card_fin]

end TCSlib.Cryptography.Authentication.FromDiscreteLog

## ===== TCSlib/Cryptography/Asymptotic/ReductionSupport.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.OneWayFunctions.Basic
import TCSlib.Cryptography.Pseudorandom.Generators

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Shared support for polynomial-time reductions

The one-call wrapper and the parameter-aware pre-processor expose their typed
coin conversions and run equations. The bit-string identities, uniform coin
reindexing, polynomial-time cuts, and negligible bounds support multiple reductions.

## Main definitions

* `Complexity.NUPPT.wrap` is a one-call reduction with pre- and post-processing.
* `Complexity.NUPPT.preComp` lets pre-processing inspect the security parameter.
* `TCSlib.Cryptography.finCastEquiv` transports bit strings along a length equality.

## Main results

* `Complexity.NUPPT.runAt_wrap` and `Complexity.NUPPT.runAt_preComp` give the
  typed run equations.
* `TCSlib.Cryptography.prgAdv_coins_equiv` reindexes uniform coins.
* `TCSlib.Cryptography.Negligible.polyExpr_mul` bounds multiplication by a
  syntactic polynomial.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.3.4, §3.3.5, §3.4.2, and §3.8.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §1.2 and Chapter 3.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Bit-string identities -/

/-- `List.ofFn (Fin.snoc v b) = List.ofFn v ++ [b]`. -/
theorem ofFn_snoc_eq {n : ℕ} (v : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc v b : Fin (n + 1) → Bool) = List.ofFn v ++ [b] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- `List.ofFn v = List.ofFn (Fin.init v) ++ [v (Fin.last n)]`. -/
theorem ofFn_eq_init_append {n : ℕ} (v : Fin (n + 1) → Bool) :
    List.ofFn v = List.ofFn (Fin.init v) ++ [v (Fin.last n)] := by
  have h := ofFn_snoc_eq (Fin.init v) (v (Fin.last n))
  rwa [Fin.snoc_init_self] at h

/-- `List.ofFn` of an appended pair is the concatenation of the encodings. -/
theorem ofFn_appendEquiv {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) :
    List.ofFn (Fin.appendEquiv a b (x, y)) = List.ofFn x ++ List.ofFn y :=
  List.ofFn_fin_append x y

/-- The first `a` bits of `List.ofFn x ++ List.ofFn y` with `|x| = a`. -/
theorem take_ofFn_append {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) :
    (List.ofFn x ++ List.ofFn y).take a = List.ofFn x :=
  List.take_left' (List.length_ofFn)

/-- The bits after the first `a` of `List.ofFn x ++ List.ofFn y` with `|x| = a`. -/
theorem drop_ofFn_append {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) :
    (List.ofFn x ++ List.ofFn y).drop a = List.ofFn y :=
  List.drop_left' (List.length_ofFn)

/-- Transport of bit strings along an equality of lengths (`Fin.cast` on the index). -/
def finCastEquiv {a b : ℕ} (h : a = b) : (Fin a → Bool) ≃ (Fin b → Bool) where
  toFun f j := f (Fin.cast h.symm j)
  invFun f i := f (Fin.cast h i)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The forward reader of `finCastEquiv`: bit `j` of the transported string is bit
`Fin.cast h.symm j` of `f`. -/
theorem finCastEquiv_apply {a b : ℕ} (h : a = b) (f : Fin a → Bool) (j : Fin b) :
    finCastEquiv h f j = f (Fin.cast h.symm j) :=
  rfl

/-- The function of `finCastEquiv h`: `f ↦ (j ↦ f (Fin.cast h.symm j))`. -/
theorem coe_finCastEquiv {a b : ℕ} (h : a = b) :
    ⇑(finCastEquiv h) = fun f j => f (Fin.cast h.symm j) :=
  rfl

/-- Transport along an equality of lengths does not change the encoding. -/
theorem ofFn_finCastEquiv {a b : ℕ} (h : a = b) (f : Fin a → Bool) :
    List.ofFn (finCastEquiv h f) = List.ofFn f :=
  (List.ofFn_congr h f).symm

end TCSlib.Cryptography

namespace Complexity.NUPPT

open Turing

/-! ## The one-call wrapper -/

/-- The raw function of the one-call wrapper on the layout `⟨⟨⟨1^n, y⟩, ⟨β, α⟩⟩, r⟩`: cut the
coins at `p(n)`, form the view `w := ⟨⟨⟨1^n, y⟩, r.take (p n)⟩, β⟩`, run `A` on `pre w` with
advice `α` and the remaining coins, and return `post ⟨w, answer⟩`. -/
def wrapFun (A : NUPPT) (pre post : List Bool → List Bool) (p : PolyExpr) (z : List Bool) :
    List Bool :=
  post (pairEncode
    (layout (inParam z) (inArg z)
      ((pairSndD (pairEncode (inParam z) (inCoins z))).take
        (p.eval (pairFstD (pairEncode (inParam z) (inCoins z))).length))
      (pairFstD (inAdvice z)))
    (A.output (layout (inParam z)
      (pre (layout (inParam z) (inArg z)
        ((pairSndD (pairEncode (inParam z) (inCoins z))).take
          (p.eval (pairFstD (pairEncode (inParam z) (inCoins z))).length))
        (pairFstD (inAdvice z))))
      (pairSndD (inAdvice z))
      ((pairSndD (pairEncode (inParam z) (inCoins z))).drop
        (p.eval (pairFstD (pairEncode (inParam z) (inCoins z))).length)))))

/-- The raw function of the one-call wrapper is polynomial-time (the pairing calculus, the
typed coin cuts `polyTimeComputable_pairTakePoly`/`pairDropPoly`, and `A.output`). -/
theorem wrapFun_poly (A : NUPPT) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) (p : PolyExpr) :
    PolyTimeComputable (A.wrapFun pre post p) := by
  have hcut := polyTimeComputable_inParam.pairEncode polyTimeComputable_inCoins
  have htake := (polyTimeComputable_pairTakePoly p).comp hcut
  have hdrop := (polyTimeComputable_pairDropPoly p).comp hcut
  have hw := polyTimeComputable_layout polyTimeComputable_inParam polyTimeComputable_inArg htake
    (polyTimeComputable_pairFstD.comp polyTimeComputable_inAdvice)
  have hA := A.polyTimeComputable_output.comp
    (polyTimeComputable_layout polyTimeComputable_inParam (hpre.comp hw)
      (polyTimeComputable_pairSndD.comp polyTimeComputable_inAdvice) hdrop)
  exact hpost.comp (hw.pairEncode hA)

/-- **The one-call wrapper** [PS10, §2.1, the closure properties used implicitly]: the
machine with coins `p + A.coins` and advice `⟨β n, A.advice n⟩` that, on `⟨1^n, y⟩` with coins
`r`, forms the view `w = ⟨⟨⟨1^n, y⟩, r.take (p n)⟩, β n⟩`, calls `A(1^n, pre w)` once with the
remaining coins and returns `post ⟨w, answer⟩`. Every single-call reduction of the hard-core
chapter is an instance (`runAtL_wrap`, `runAt_wrap`). -/
noncomputable def wrap (A : NUPPT) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) (β : ℕ → List Bool)
    (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) (p : PolyExpr) : NUPPT :=
  ofPolyTime (A.wrapFun_poly hpre hpost p) (.add p A.coins)
    (.add (.add (.mul (.const 2) b) (.const 2)) A.adv)
    (fun n => pairEncode (β n) (A.advice n)) (fun n => by
      rw [length_pairEncode]
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
      have h₁ := hβ n
      have h₂ := A.advice_length n
      omega)

/-- The coin polynomial of the one-call wrapper is `p + A.coins`. -/
@[simp] theorem coins_wrap (A : NUPPT) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) (β : ℕ → List Bool)
    (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) (p : PolyExpr) :
    (A.wrap hpre hpost β b hβ p).coins = .add p A.coins :=
  NUPPT.coins_ofPolyTime _ _ _ _ _

/-- **The coins of the one-call wrapper**: the published equivalence `(A.wrap …).Coins n ≃
{0,1}^{p(n) + |A's coins at n|}` (data coins, then `A`'s coins; `finCongr` along the coin count). -/
noncomputable def wrapCoinsEquiv (A : NUPPT) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) (β : ℕ → List Bool)
    (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) (p : PolyExpr) (n : ℕ) :
    (A.wrap hpre hpost β b hβ p).Coins n ≃ (Fin (p.eval n + A.coinLen n) → Bool) :=
  Equiv.arrowCongr (finCongr
    (by rw [coinLen_eq, coins_wrap, PolyExpr.eval_add, coinLen_eq])) (Equiv.refl Bool)

/-- The inverse coin equivalence of the wrapper keeps the coin string:
`List.ofFn ((wrapCoinsEquiv … n).symm w) = List.ofFn w`. -/
theorem wrapCoinsEquiv_symm_ofFn (A : NUPPT) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) (β : ℕ → List Bool)
    (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) (p : PolyExpr) (n : ℕ)
    (w : Fin (p.eval n + A.coinLen n) → Bool) :
    List.ofFn ((A.wrapCoinsEquiv hpre hpost β b hβ p n).symm w) = List.ofFn w :=
  List.ofFn_congr (by rw [coinLen_eq, coins_wrap, PolyExpr.eval_add, coinLen_eq]) _

/-- The untyped activation of the one-call wrapper. -/
theorem runAtL_wrap (A : NUPPT) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) (β : ℕ → List Bool)
    (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) (p : PolyExpr) (n : ℕ) (y r : List Bool) :
    (A.wrap hpre hpost β b hβ p).runAtL n y r =
      post (pairEncode (layout (List.replicate n true) y (r.take (p.eval n)) (β n))
        (A.runAtL n (pre (layout (List.replicate n true) y (r.take (p.eval n)) (β n)))
          (r.drop (p.eval n)))) := by
  unfold wrap
  rw [runAtL_ofPolyTime]
  simp [wrapFun, runAtL_eq, advInput_eq, layout_eq, inParam_eq, inArg_eq, inAdvice_eq, inCoins_eq]

/-- The typed activation of the one-call wrapper on coins `r` that split as `a ++ c`: the
data coins `a` (`p(n)` bits) and the coins `c` of `A`. (Stated for any coin string `r` whose
encoding is `List.ofFn a ++ List.ofFn c`, so that any coin bijection can be used.) -/
theorem runAt_wrap (A : NUPPT) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) (β : ℕ → List Bool)
    (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) (p : PolyExpr) (n : ℕ) (y : List Bool)
    {m : ℕ} (hm : m = p.eval n) (a : Fin m → Bool) (c : A.Coins n)
    (r : (A.wrap hpre hpost β b hβ p).Coins n) (hr : List.ofFn r = List.ofFn a ++ List.ofFn c) :
    (A.wrap hpre hpost β b hβ p).runAt n y r =
      post (pairEncode (layout (List.replicate n true) y (List.ofFn a) (β n))
        (A.runAt n (pre (layout (List.replicate n true) y (List.ofFn a) (β n))) c)) := by
  rw [runAt_eq, runAtL_wrap, hr, List.take_left' (by simp [hm]), List.drop_left' (by simp [hm]),
    runAt_eq]

end Complexity.NUPPT

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Reindexing the coins of an adversary -/

/-- Reindexing the coins of a distinguisher by a bijection does not change acceptance
probabilities. -/
theorem acceptProb_coins_equiv {σ γ ρ ρ' : Type*} [Fintype σ] [Fintype ρ] [Fintype ρ']
    (X : σ → γ) (D : γ → ρ → Bool) (D' : γ → ρ' → Bool) (e : ρ' ≃ ρ)
    (h : ∀ x c, D x (e c) = D' x c) : acceptProb X D = acceptProb X D' := by
  simp only [acceptProb_def]
  rw [← uprob_comp_equiv ((Equiv.refl σ).prodCongr e)]
  exact OneWay.uprob_congr fun z => by simp [h]

/-- Reindexing the coins of a distinguisher by a bijection does not change PRG advantages. -/
theorem prgAdv_coins_equiv {σ γ ρ ρ' : Type*} [Fintype σ] [Fintype γ] [Fintype ρ] [Fintype ρ']
    (G : σ → γ) (D : γ → ρ → Bool) (D' : γ → ρ' → Bool) (e : ρ' ≃ ρ)
    (h : ∀ x c, D x (e c) = D' x c) : prgAdv G D = prgAdv G D' := by
  simp only [prgAdv_eq, distAdv_def]
  rw [acceptProb_coins_equiv G D D' e h, acceptProb_coins_equiv id D D' e h]

/-- Reindexing the coins of a predictor by a bijection does not change prediction
probabilities. -/
theorem predProb_coins_equiv {α β ρ ρ' : Type*} [Fintype α] [Fintype ρ] [Fintype ρ']
    (f : α → β) (B : α → Bool) (A : β → ρ → Bool) (A' : β → ρ' → Bool) (e : ρ' ≃ ρ)
    (h : ∀ y c, A y (e c) = A' y c) : predProb f B A = predProb f B A' := by
  simp only [predProb_def]
  rw [← uprob_comp_equiv ((Equiv.refl α).prodCongr e)]
  exact OneWay.uprob_congr fun z => by simp [h]

/-! ## FP glue: cutting a string at the length of another -/

/-- `w ↦ (b w).take |a w|` is polynomial-time (`polyTimeComputable_pairTakePoly var` on
`⟨a w, b w⟩`). -/
theorem takeLen_poly {a b : List Bool → List Bool} (ha : PolyTimeComputable a)
    (hb : PolyTimeComputable b) : PolyTimeComputable fun w => (b w).take (a w).length := by
  convert (polyTimeComputable_pairTakePoly .var).comp (ha.pairEncode hb) using 1
  funext w
  simp

/-- `w ↦ (b w).drop |a w|` is polynomial-time (`polyTimeComputable_pairDropPoly var` on
`⟨a w, b w⟩`). -/
theorem dropLen_poly {a b : List Bool → List Bool} (ha : PolyTimeComputable a)
    (hb : PolyTimeComputable b) : PolyTimeComputable fun w => (b w).drop (a w).length := by
  convert (polyTimeComputable_pairDropPoly .var).comp (ha.pairEncode hb) using 1
  funext w
  simp

/-! ## Negligible functions times polynomials -/

/-- A syntactic polynomial times a negligible function is negligible
([Gar26, §1.2]; `Negligible.mul_pow` and `Negligible.const_mul` through the normal-form
majorant `C (n+1)^c ≤ C 2^c n^c` of `PolyExpr.eval_le`). -/
theorem Negligible.polyExpr_mul {μ : ℕ → ℝ} (hμ : Negligible μ) (p : PolyExpr) :
    Negligible fun n => (p.eval n : ℝ) * μ n := by
  obtain ⟨C, c, hC⟩ := p.eval_le
  refine ((hμ.mul_pow c).const_mul ((C : ℝ) * 2 ^ c)).mono ⟨1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (p.eval n : ℝ) ≤ C * ((n : ℝ) + 1) ^ c := by exact_mod_cast hC n
  have h2 : ((n : ℝ) + 1) ^ c ≤ (2 * (n : ℝ)) ^ c :=
    pow_le_pow_left₀ (by positivity) (by linarith) c
  have hp : (p.eval n : ℝ) ≤ (C : ℝ) * 2 ^ c * (n : ℝ) ^ c :=
    calc (p.eval n : ℝ) ≤ C * ((n : ℝ) + 1) ^ c := h1
      _ ≤ C * (2 * (n : ℝ)) ^ c := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
      _ = (C : ℝ) * 2 ^ c * (n : ℝ) ^ c := by rw [_root_.mul_pow, mul_assoc]
  calc |(p.eval n : ℝ) * μ n| = (p.eval n : ℝ) * |μ n| := by rw [abs_mul, Nat.abs_cast]
    _ ≤ (C : ℝ) * 2 ^ c * (n : ℝ) ^ c * |μ n| := mul_le_mul_of_nonneg_right hp (abs_nonneg _)
    _ = |(C : ℝ) * 2 ^ c * ((n : ℝ) ^ c * μ n)| := by
        rw [abs_mul ((C : ℝ) * 2 ^ c) ((n : ℝ) ^ c * μ n), abs_mul ((n : ℝ) ^ c) (μ n),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (C : ℝ) * 2 ^ c),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ c), mul_assoc]

/-- The first `m` bits of the encoding of an `ℓ`-bit string (`m ≤ ℓ`) encode its restriction
along `Fin.castLE`. -/
theorem take_ofFn_castLE {ℓ m : ℕ} (h : m ≤ ℓ) (f : Fin ℓ → Bool) :
    (List.ofFn f).take m = List.ofFn fun i : Fin m => f (Fin.castLE h i) := by
  refine List.ext_getElem (by simp [List.length_take, h]) fun j hj₁ hj₂ => ?_
  simp only [List.getElem_take, List.getElem_ofFn]
  rfl

end TCSlib.Cryptography

namespace Complexity.NUPPT

open Turing

/-! ## Parameter-aware pre-processing -/

/-- The raw function of the parameter-aware pre-processor on the layout `⟨⟨⟨1^n, y⟩, α⟩, r⟩`:
run `A.output` on `⟨⟨⟨1^n, pre ⟨1^n, y⟩⟩, α⟩, r⟩`. -/
def preFun (A : NUPPT) (pre : List Bool → List Bool) (z : List Bool) : List Bool :=
  A.output (layout (inParam z) (pre (pairEncode (inParam z) (inArg z))) (inAdvice z) (inCoins z))

/-- The raw function of the pre-processor is polynomial-time. -/
theorem preFun_poly (A : NUPPT) {pre : List Bool → List Bool} (hpre : PolyTimeComputable pre) :
    PolyTimeComputable (A.preFun pre) :=
  A.polyTimeComputable_output.comp (polyTimeComputable_layout polyTimeComputable_inParam
    (hpre.comp (polyTimeComputable_inParam.pairEncode polyTimeComputable_inArg))
    polyTimeComputable_inAdvice polyTimeComputable_inCoins)

/-- **Parameter-aware pre-processing** [PS10, §2.1, the closure properties used implicitly]:
the machine with `A`'s coins and advice computing `A(1^n, pre ⟨1^n, y⟩; r)`. Unlike
`NUPPT.exists_comp`, the pre-processing sees the parameter (needed to truncate an input to
`n + 1` bits). The coin type is definitionally `A.Coins n`. -/
noncomputable def preComp (A : NUPPT) {pre : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) : NUPPT :=
  ofPolyTime (A.preFun_poly hpre) A.coins A.adv A.advice A.advice_length

/-- The coin polynomial of the pre-processed machine is `A`'s. -/
@[simp] theorem coins_preComp (A : NUPPT) {pre : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) : (A.preComp hpre).coins = A.coins := by
  unfold preComp
  exact coins_ofPolyTime _ _ _ _ _

/-- **The pre-processed machine runs on the coins of `A`**: the published equivalence
`(A.preComp hpre).Coins n ≃ A.Coins n` (`NUPPT.coinsCongr` along `coins_preComp`). -/
noncomputable def preComp_coinsEquiv (A : NUPPT) {pre : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (n : ℕ) : (A.preComp hpre).Coins n ≃ A.Coins n :=
  coinsCongr (coins_preComp A hpre) n

/-- The coin equivalence keeps the coin string:
`List.ofFn (A.preComp_coinsEquiv hpre n r) = List.ofFn r`. -/
theorem preComp_coinsEquiv_ofFn (A : NUPPT) {pre : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (n : ℕ) (r : (A.preComp hpre).Coins n) :
    List.ofFn (A.preComp_coinsEquiv hpre n r) = List.ofFn r :=
  coinsCongr_ofFn (coins_preComp A hpre) n r

/-- The untyped activation of the pre-processed machine. -/
theorem runAtL_preComp (A : NUPPT) {pre : List Bool → List Bool} (hpre : PolyTimeComputable pre)
    (n : ℕ) (y r : List Bool) :
    (A.preComp hpre).runAtL n y r = A.runAtL n (pre (pairEncode (List.replicate n true) y)) r := by
  unfold preComp
  rw [runAtL_ofPolyTime]
  simp [preFun, runAtL_eq, advInput_eq, layout_eq, inParam_eq, inArg_eq, inAdvice_eq, inCoins_eq]

/-- The typed activation of the pre-processed machine, on the coins of `A` carried over by
`preComp_coinsEquiv`. -/
theorem runAt_preComp (A : NUPPT) {pre : List Bool → List Bool} (hpre : PolyTimeComputable pre)
    (n : ℕ) (y : List Bool) (r : (A.preComp hpre).Coins n) :
    (A.preComp hpre).runAt n y r =
      A.runAt n (pre (pairEncode (List.replicate n true) y)) (A.preComp_coinsEquiv hpre n r) := by
  rw [runAt_eq, runAtL_preComp, runAt_eq, preComp_coinsEquiv_ofFn]

end Complexity.NUPPT
