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
