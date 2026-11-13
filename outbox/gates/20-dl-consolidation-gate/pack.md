# Gate 20 · Duplication consolidation DL-30–DL-34

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #298](https://github.com/Shilun-Allan-Li/tcslib/pull/298) at
  `6f853adc61d5d175ee83c69f6c07ab2da112cabc` (branch `land/pass-shelat-dl-consolidation`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` at base
  `2ea4df08d009a4bbdb8042795ff062d7f22db325`. That is the records tip after the #297 merge `758a1030`.
- **Issue base:** `b96ab3ccc1915497ea3138df499eec00b6581db0`, the merge of #293. Between that base and the PR base,
  the Lean changes are #294 (IND-CCA2 ⇔ NM-CCA2) and #297 (Theorem 174.8). The landing edits re-point both.
- **Commits:**
  - the worker's 4 commits (Claude job `dl-consolidation`): checkpoints 1–3, then R3/R4/Eager;
  - 5 maintainer landing edits: LE-split, LE-repoint, LE-review, LE-rule10 and LE-repoint-nmsim.
- **Scope:** a **refactor audit**.
  - The job promotes generic lemmas to shared homes, deletes the copies and re-points every use.
  - It is meant to change no audited statement and no mathematical content.
  - The brief is `fills/dl-consolidation/issued-r1/brief.md` on the records branch. Its items are P1–P4, S1–S3,
    H1, A1–A6, L1–L7, R1–R7 and O1–O2. The duplication ledger is `duplication-ledger.md`, rows DL-30 to DL-34 and
    DL-37.

## What changed

All paths are under `TCSlib/Cryptography/`. Across 51 Lean files, 48 are modified, 2 are added and 1 is deleted:
- added `Foundations/BitLists.lean`;
- added `Encryption/PublicKey/OracleSecurity/PaddedCPA.lean`;
- deleted `Encryption/PublicKey/BitwiseCPA/Eager.lean`.

**New shared homes**
- `Games/Probability` (`Games.ProbComp`): `expect_sample_equiv/_comm/_unique`, `expect_sub`, `expect_sample_update`,
  `abs_expect_sub_le`.
- `Games/Simulate`: `simulate_eq_of_abs` and the bounded form `simulate_eq_of_abs_bounded`.
- `Games/Hopping`: `expect_simulate_congr`, `prob_bad_le`, `expect_sample_mem_le`.
- `Games/BitCodec`:
  - the `castImpl` family;
  - `padFin_ofFn_zeroBits`, `padFin_nil`, `padFin_replicate_false`;
  - `decodeFin_nil_getD`.
- `Asymptotic/Adversary`, beside `padFin` and `blocks`:
  - `ofFn_padFin_of_length` (root);
  - `ofFn_cast`;
  - `ofFn_arrowCongr_finCongr`;
  - `FunFamily.ofFn_blocks`.
- `Asymptotic/EnsemblesLemmas`: A4's `EnsembleLemmas.ofFn_padFin_eq_padL`.
- Published readers:
  - `indCodec_eq_bitCodec` (public and private key);
  - `hybridPre_eq`;
  - R3's `expect_simulate_indImpl_cpa`;
  - R4's padded readers;
  - R5's general `chRun_toCompOn_transport_list`;
  - R6's round-input readers `InteractiveHandler.rU`…`rCnt` and `impl_of_ret`.
- `Foundations/BitLists`: the list and vector lemmas L1–L7.
- `ChallengeSim.expect_simulate_eager` (S3b; formerly `BitwiseSim`'s).

**The census of stored constants** (issue base → delivered head): 2112 → 2099.
- 101 removed, every one a listed copy or helper, with no aliases left behind.
- 88 added and 11 moved.
- The worker's name map is `namemap.txt` in its delivery (exchange `fc1082ca`, `inbox/fills/dl-consolidation/evidence/namemap.txt`). The
  census's own map is `statements/census-namemap.tsv` in `verification.zip`. The worker's map lacks two R4 rows,
  `BitwiseSim.padded_enc_runAt`/`_coins` → `PublicKeyScheme.*`; their types are identical by the census
  (review finding 6).

**The only type change modulo the name map** is R3: `expect_simulate_indImpl_cpa` goes from a private lemma to a
public one in cast form, as Rule 10 needs. Its uses are re-pointed.

**Landing edits**
- **LE-split** `406b8d57`: `section PaddedCPA` moves verbatim to `OracleSecurity/PaddedCPA.lean`, because with
  #294 `OracleSecurity.lean` would have been 1004 lines.
  - Sizes are now 723 and 332.
  - `TrapdoorCPA`, `BitwiseCPA` and the `Encryption/PublicKey` facade import it.
  - There is no import cycle.
- **LE-repoint** `06fab435`: #294's `Indistinguishability.lean`, `Decrypt.lean` and `Encrypt.lean` are re-pointed to
  the moved names.
- **LE-review** `82f8d1bc`: docstrings only.
- **LE-rule10** `510e9d75`: the proof of `padded_cpa_advantage_eq` now reads OracleSecurity through `padded_gen`,
  `padded_enc`, R1 and `ofFn_cast`. This was needed once OracleSecurity's definitions became foreign to the new
  file.
- **LE-repoint-nmsim** `6f853adc`: #297's nm-sim files are re-pointed (25 `ofFn_padFin_of_length` sites, among
  others).
  - The selective `open AdaptiveCPA (…)` lines are removed.
  - nm-sim's private `padFin_replicate_false` is deleted in favour of `Games.padFin_replicate_false`. This is the
    first payback of DL-37.
  - The statements of `castImpl_snmImpl` and `castImpl_indImpl_abs` keep the unqualified spelling `castImpl`,
    which resolves to `Games.castImpl` through `open TCSlib.Cryptography.Games`. Their text is byte-identical.

## Questions for the audit

**1. Statement freeze**
- Does any audited statement change, up to the name map?
- decls2 from the PR base to the head gives 68 ADDED, 42 REMOVED, 2 MOVED and **0 CHANGED**
  (`review.md`; `landing.zip:statements-r2/decls2-pr.tsv`).
- `padded_cpa` moves with an identical statement.
- Check the endpoints:
  - `prfFixedScheme_cpa`, `prfFixedScheme_cca1`, `not_prfFixedScheme_cca2`, `prfFixedScheme_not_cca2`;
  - `INDSecure.adaptive_cpa`;
  - `SingleBitSecure.bitwise_padded_cpa`, `exists_adaptive_cpa` and `padded_cpa`;
  - `exists_adaptiveCPA_of_rsa`/`_of_factoring`;
  - #294's `nmSecure_cca2_of_indSecure_cca2`, `indSecure_cca2_of_nmSecure_cca2` and `indSecure_cca2_iff_nmSecure_cca2`;
  - #297's `nmSecure_of_simNMSecure`, `simNMSecure_of_nmSecure_cpa` and `simNMSecure_cpa_iff_nmSecure_cpa`.

**2. Faithful promotion**
- Is each promoted lemma at least as general as every copy it replaces?
- Is each derived lemma (S1, A5, R5) really a corollary?
- Is any deleted copy still needed under another name?
- Was any copy that the brief or the worker's grep found left in place without a recorded reason?

**3. Rule 10** (no touched declaration reads another file's definition, including generated matchers and projections)
- Whole-file seals over the full closures: A 34/41 and B 30/41 at the head, against 33/40 and 28/40 at the base.
- No head failure is new: each one sits at the same declaration as at the base.
- `PaddedCPA` and `BitLists` pass both variants, and the 11 nm-sim files pass 22/22.
- Paired controls are ALL_OK, and the explicit-unfold scan finds 0 foreign definitions.
- The worker's table says `Games/Probability` passes. Under the archived harness it fails at the unchanged
  `dist_apply`, identically at base and head.
- Is LE-rule10 sufficient?
- Did any promotion move a definition's reader so that an existing proof now reads across files?

**4. Homes and API (policy §1, §3)**
- Is each lemma at its lowest legal home, with no import cycle?
- Names, formula docstrings, module docstrings and sketches.
- No `@[simp]` is added.
- The R6 readers are public with `*_input` readers but no `_eq`; lint check 8 accepts this (review finding 7).
- Are R7 (the length vectors, escalated and recommended closed as no-fold) and P2 (kept) correctly decided?

**5. Landing correctness**
- Is the LE-split verbatim?
- Do the re-points in #294's and #297's files change only names, `open` lines and widths?
- Are the two `castImpl` statement spellings really byte-identical?

## Also check

**Axioms**
- Every stored constant is standard, except the 4 Yao constants with base admissions; they are the same 4 as at
  the base.
- All 16 endpoints above print `[propext, Classical.choice, Quot.sound]` (`landing/axioms-head.log`).

**Admissions:** issued modules go 48 → 45. That is #294's 1 fill and nm-sim's 2. Nothing outside the issued order
changed (219 warnings in all).

**Lint:** FAIL 214 → 216 and WARN 103 → 103 against the PR base.
- The delta is +4 FAILs from the split: `OracleSecurity.lean` is linted as the facade of `OracleSecurity/` but cannot
  import `PaddedCPA` without a cycle, and `Encryption.lean` does not import the new grandchild.
- It is −2 FAILs from deleting `Eager`.
- The maintainer accepted this: a content file that shares a name with a directory is not a facade.

**Sizes and widths**
- Every changed file is under 1000 lines except `ElGamal` (1830, inherited; 1835 at the base).
- No changed file gains a line over 100 characters. The 160 such lines in 13 files are inherited, and
  `EfficiencyRep` lost one. `source-head.json` has the per-file counts.

**Duplication**
- DL-36 and DL-37 are open debt, with named payback after this landing. That is not a finding.
- What you can raise:
  - a copy this job should have folded and did not;
  - a fold that `review.md` § *Debt now foldable* misses.

## Evidence

- **`review.md`:** the maintainer's delivery review, ACCEPT WITH LANDING EDITS, followed by the rebase-r1 addendum.
- **`verification.zip`** (= `fills/dl-consolidation/final-r1/review-evidence.zip`): the review's raw evidence.
  - It covers:
    - integrity (`git am` reproduces the worker's commits);
    - the fresh 1219/1219 build;
    - the census and name map;
    - decls2;
    - axioms;
    - seals at base and head, with controls;
    - the unfold scan;
    - lint;
    - sizes.
  - `PROVENANCE.txt` describes it. The inner `SHA256SUMS` (2441 entries) covers the whole review directory,
    including raw seal sources left out for size.
- **`landing.zip`** (= `fills/dl-consolidation/final-r1/rebase-r1/rebase-evidence.zip`): the rebase onto #297 and
  LE-repoint-nmsim.
  - It holds the range-diff, the rebase check, the re-point counts, the 15-module rebuild and the final-tree check.
  - It also holds statements, axioms, the nm-sim seals and controls, the consolidation seal-closure check, the
    census and lint.
  - **`statements-r2/` supersedes `statements/decls2-nmsim.tsv`.** That file was written before the amend that
    kept the `castImpl` spellings.
- **`landing/`:** at the final head.
  - `root-order.txt` and `root-checks.jsonl`: the 15 rebuilt modules through root `TCSlib`, all rc 0, each with
    its `source_sha256`.
  - `final-tree-check.txt`: all 1198 TCSlib/`audits` modules end with rc 0 at the head's source hash.
  - `axioms-head.log`.
- **`worker-report.md`:** the worker's `REPORT.md`, at exchange `fc1082caa8455afab5342e9ba444955ade2994fd`.
- **`pr.diff.txt`:** `git diff` from the base to the head.
- **`source-head.json`:** the head hashes, line counts and over-width counts of the 50 changed files, and the
  deleted file.
- **`sources.zip`:** the source closure at the head of every changed module (240 files).

## Findings delivery

Return `gate20-dl-consolidation-findings.md` as a Markdown file in this chat. If you have several evidence files,
return a ZIP. The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, or a scope violation.
- **major:** a changed audited statement, a lost generality, a forbidden new read in a touched declaration, or
  necessary evidence that cannot be verified.
- **minor:** documentation or API defects.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.
