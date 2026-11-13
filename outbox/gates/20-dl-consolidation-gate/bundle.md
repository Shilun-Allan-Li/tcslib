## ===== briefs/pass-shelat-ch5-8/gates/20-dl-consolidation/pack.md =====

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

## ===== briefs/pass-shelat-ch5-8/gates/20-dl-consolidation/review.md =====

# dl-consolidation · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS.** The delivery has no blocking defect. Four landing edits are needed and
committed on the local branch `land/pass-shelat-dl-consolidation`.

- **Delivery:** Claude worker, exchange `fc1082caa8455afab5342e9ba444955ade2994fd` (`inbox/fills/dl-consolidation/`;
  checkpoints `584e5e10b`, `64db35660`, `2aa42b298`), 4 patches on the issue base
  `b96ab3ccc1915497ea3138df499eec00b6581db0`.
- **Evidence:** `review-evidence.zip` (SHA-256 `f002416105740b4454a44a8c71425aba7a6a0e1d5ddfc668af63b960d6cb46ca`) is
  a selection of the review directory: `PROVENANCE.txt`, logs, statements, landing, tools, order, scan, final
  seals and runs, controls, edits and bootstrap. Its `SHA256SUMS` (SHA-256
  `35bfc608c5941c08b0efc448bfa528e8690f9a48256248b3683bfdeef6ae3dae`, 2441 entries) covers the whole review
  directory, including the raw first-pass and base seal sources left out of the zip for size.
- **Extracts in `landing/`:** conflict resolutions, the landing-edit diff, the seal table, the axiom summary, the
  sorry census, the lint diff and sizes.

## Checks (re-run by the reviewer)

**Integrity**
- The payload has no SHA256SUMS manifest (the brief predates that requirement); 297 files were inventoried with
  their hashes.
- `git am` at the issue base, with the worker's committer and dates, reproduces the four worker commits exactly:
  head `6917e5716066b858a4dbdc33cf7f8653f9a40aa5`, tree `1324c6c92e1a3c0df9934c76926a42f220f22635`.
- 37 paths changed: 35 modified, `Foundations/BitLists.lean` added, `BitwiseCPA/Eager.lean` deleted. The 36 files
  present are byte-identical to `src/`.

**Landing**
- Parent `f237892103a08e371c2c9c128fbc3b74202e629c` (contains the #294 merge `262d6e9a`).
- `git am -3` had no textual conflict. In `OracleSecurity.lean`, #294's readers and R1/R3/R4 are disjoint hunks;
  both are kept.
- Semantic conflicts: #294's files used moved names (LE-repoint).

**Build**
- Fresh tree: 1219/1219, 0 errors.
- Coverage: the closure of the 42 changed modules, everything downstream through root `TCSlib` and both
  `audits/*/Checks`, and PFR (copied from the pinned package, then removed).

**Admissions**
- Issued modules: 47 = the base's 48 minus #294's target.
- Nothing outside the issued order changed.

**Census (stored constants)**
- 2112 → 2099: 101 removed (every one a listed copy or helper, no aliases), 88 added, 11 moved.
- The only type change modulo the name map is R3 `expect_simulate_indImpl_cpa` (private → public cast form, needed
  for Rule 10; uses re-pointed).
- `decls2`: 0 changed public statements. `padded_cpa` moved with an identical statement. No audited statement
  changed.

**Axioms**
- Every constant is standard, except the 4 Yao constants with base admissions (the same 4 as at the base).
- All 13 endpoints print `[propext, Classical.choice, Quot.sound]`: the brief's 9, `prfFixedScheme_not_cca2`, and
  #294's 3.

**Rule 10**
- Whole-file seals over the full closures:

  | Variant | Head | Base |
  |---|---|---|
  | A | 34/41 | 33/40 |
  | B | 30/41 | 28/40 |

- 0 new failing declarations. Every head failure is at the same declaration as at the base, and `OracleFromPRF`
  B now passes. `PaddedCPA` and `BitLists` pass both variants.
- Controls: 34 probes, ALL_OK (90/90 sealed negatives fail exactly once).
- Explicit-unfold scan: 0 foreign definitions.
- The worker's table says `Games/Probability` passes. Under the archived harness it fails at the unchanged
  `dist_apply`, identically at base and head, so this is not a delivery defect.

**Sizes**
- `PublicKey/OracleSecurity.lean` **723**, `OracleSecurity/PaddedCPA.lean` **332**.
- Every changed file is < 1000 lines except ElGamal (1830, inherited; 1835 at base). No new line over 100.

## Findings and dispositions

| # | Severity | Finding | Disposition |
|---|---|---|---|
| 1 | medium | Merged with #294, `OracleSecurity.lean` would be 1004 lines. | **LE-split** `78c3a10d8e1cf58bd1434bc5f213f9e566b1b311` (ruling 2026-11-12): `section PaddedCPA` moved verbatim to `OracleSecurity/PaddedCPA.lean` with the `ChallengeSim`/`RecordHandler` imports; `TrapdoorCPA`, `BitwiseCPA` and the facade `Encryption/PublicKey.lean` import it; no cycle. |
| 2 | medium | The split exposed four Rule-10 readings in `padded_cpa_advantage_eq` (OracleSecurity's definitions read through their bodies once foreign). | **LE-rule10** `7b7d07aaad194200788fcd727955178860a2403a`: proof only, via `padded_gen`, `padded_enc`, R1 and `ofFn_cast`; both seals pass. |
| 3 | medium | #294's `Indistinguishability.lean`, `Decrypt.lean`, `Encrypt.lean` use moved names. | **LE-repoint** `818a1c8dc3eee12260de50dc8f9de2a8af195d60` (`ofFn_padFin_of_length` ×10, `Games.castImpl*`, `ProbComp.expect_sample_*`, `FixedLengthPKScheme.indCodec_eq_bitCodec`). |
| 4 | low | Label-only docstrings on the new R6 readers `rU`…`rCnt` and their `polyTimeComputable_*`, `xorPerm`, `expect_sample_mem_le`; the H1 bound `prob_bad_le` not stated as a formula; 3 docstring lines > 100 (the REPORT says they were wrapped). | **LE-review** `8e43131f64599cae617a40f5fead94eecef16e35` (docstrings only). |
| 5 | low | Lint: 4 new FAILs, all from the split (the delivery removed 2). `OracleSecurity.lean` is linted as the facade of `OracleSecurity/` but cannot import `PaddedCPA` (cycle) and no longer imports `ChallengeSim`/`RecordHandler`; `Encryption.lean` does not import the new grandchild (the same pattern as ~33 existing FAILs). Head 197 FAIL / 103 WARN vs parent 195 / 103. | Accepted and recorded: a content file sharing a name with a directory is not a facade. |
| 6 | low | `namemap.txt` lacks the R4 rows `BitwiseSim.padded_enc_runAt`/`_coins` → `PublicKeyScheme.*` (types identical by the census). | Recorded here; no code change. |
| 7 | info | The public R6 readers have `*_input` readers but no `_eq`; lint check 8 accepts them. | Needed for the DL-36 `finInput` fold. |

**Item dispositions**
- Done as reported (confirmed by the census and the build): P1, P3, P4, S2, S3a, H1, A1–A6, L1–L7, R1, R2, R4, R5,
  R6, O1, O2.
- **P2:** not a copy; correct.
- **S1, both kept:** correct. The bounded form needs a deterministic `impl₂` and a budget; `simulate_eq_of_abs`
  allows a probabilistic one.
- **S3b:** accepted. The statement is about `chRun`, so `ChallengeSim` is its lowest legal home.
- **R3:** accepted (finding 2 above).
- **R7:** accepted as an escalation. All six vectors are `![a, b]` instances, and folding them changes audited
  handler statements. Recommendation: close as no-fold.
- **§11 further duplication:** plausible; the `hybridPre` claim was verified.

**DL-36 items now foldable (not done here)**
- `ofFn_nthCt` from `FunFamily.ofFn_blocks`.
- Forward's private `rState`/`rIdx`/`rQuery`/`rLog` = R6 `rS`/`rI`/`rX`/`rL`.
- `finU`/`finZ`/`finW`/`finL` have the bodies of `rU`/`rZ`/`rW`/`rL`; folding them needs `_finInput` readers.
  `finA` has no R6 counterpart.
- Forward's `rAns` is a third copy of AdaptiveCPA `rFwd` = PRFGame `rY`.
- `logEmit` ↔ `relabelN` is independent of this consolidation.

## Landing

- Local branch `land/pass-shelat-dl-consolidation`, head `7b7d07aaad194200788fcd727955178860a2403a`, tree
  `0cc0abd15c7660318cc65ecb58da105ed6e28ecd`.
- Commits: the 4 delivered commits (authors kept) and the 4 landing edits above.
- **Order (ruling 2026-11-13):** nm-sim lands first. Before its PR, this branch must be rebased onto the nm-sim
  merge with one more landing edit:
  - re-point the nm-sim files (`NonMalleability/Simulation*`) to the moved names;
  - delete nm-sim's private `padFin_replicate_false` in favour of `Games.padFin_replicate_false` (DL-37).

  It is then rebuilt and re-sealed.

---

## Addendum · rebase r1 over #297 (nm-sim)

**Verdict: ACCEPT.** The landing branch rebases cleanly onto the #297 merge. One more landing edit,
**LE-repoint-nmsim**, re-points the nm-sim files to the consolidated names and pays the first DL-37 item. The build,
statements, axioms and Rule-10 seals all pass.

### Heads

- **Parent:** `2ea4df08d009a4bbdb8042795ff062d7f22db325`, the records tip after the #297 merge
  `758a103030728b7b6bd13bc2ca400173ee49bf58`.
- **Head:** `6f853adc61d5d175ee83c69f6c07ab2da112cabc`, tree `aa4e3e0cad4322fc8af156e399da55fbfa3a552f`.
- **The 8 rebased commits:** they keep their authorship. `range-diff.txt` shows each identical in content.

  | Commit | Content |
  |---|---|
  | `132b37c086b38e3ad677b387d6400765163c076a` | checkpoint 1 |
  | `ae24e7ec2dc783d13732872d7e4243093575223a` | checkpoint 2 |
  | `9c0023b8f7c2e6a8d68d0e9ea5bcf529270cf6fe` | checkpoint 3 |
  | `dce2820246b6736c3d7b8ef3abd8bf74460766f8` | R3/R4/Eager |
  | `406b8d57286050dc1f91cd9b3e8e6d9665f48afc` | LE-split |
  | `06fab4358e678b2ff092e5f1f3a544a3db9e635e` | LE-repoint |
  | `82f8d1bc1e6b9e89893d6c6f4dc799fe9313bb4c` | LE-review |
  | `510e9d755bd110f98624a6b15a7bfbd12bf999fc` | LE-rule10 |

- **The rebase itself:** it had no conflict. On `TCSlib/` and `audits/`, the change from the old head `7b7d07aa` to
  the rebased 8th commit equals #297's own change (`rebase-check.txt`).

### LE-repoint-nmsim (`6f853adc`)

This edit touches 8 of the 11 nm-sim files. It changes proofs and `open` lines only (`landing-edit-LE-repoint-nmsim.patch`;
counts in `repoint-counts-final.txt`).

- **Removed `open` lines.** The selective `open AdaptiveCPA (…)` lines go from `Simulation`, `SimIND`, `IndSim` and
  `Simulator`.
- **Re-pointed names.**
  - `castImpl_eq`, `expect_simulate_castImpl_toCompOn`, `padFin_ofFn_zeroBits` and `simulate_eq_of_abs` → `Games.*`.
  - `ofFn_splitHalf_fst`/`_snd` → `FixedLengthScheme.*`.
  - `expect_sample_equiv`/`_comm` and `expect_sub` → `ProbComp.*`.
  - `GGMRed.ofFn_padFin_of_length` → root, at 25 sites.
- **DL-37 (first item paid).** The private `NMSim.padFin_replicate_false` in `Simulation/Challenge.lean` is
  deleted. Its one use now reads `Games.padFin_replicate_false`.
- **Unchanged statements.** The statements of `castImpl_snmImpl` and `castImpl_indImpl_abs` keep the unqualified
  spelling `castImpl`, which resolves to `Games.castImpl` through the existing `open TCSlib.Cryptography.Games`.
  Their text is byte-identical.
- **Width.** Five lines were re-wrapped. No line is over 100 characters.

### Checks

**Statements**
- decls2 over the 11 nm-sim files from `758a1030` to the head: **0 rows**.
- `touched`: 1 REMOVED (the private lemma), 29 proof-only changes, 322 unchanged.
- **Evidence correction.** The `statements/decls2-nmsim.tsv` in the evidence zip was written 39 seconds before the
  amend that restored the `castImpl` spelling. It shows the 2 pre-amend rows. I re-ran decls2 at the head; the
  result is in the zip under `statements-r2/`, with its own `SHA256SUMS`. That re-run is authoritative.
- decls2 over all 51 Lean files changed from the parent to the head: 68 ADDED, 42 REMOVED, 2 MOVED, **0 CHANGED**
  (`decls2-pr.tsv`).

**Build**
- Rebuilt on the consolidation's full tree, 15 modules: the 10 nm-sim helpers, `Simulation`, the `PublicKey` and
  `Encryption` facades, `Composability`, and root `TCSlib`. All 15 have rc 0.
- All 1198 TCSlib/`audits` modules end with rc 0 at the final-head source hash.

**Axioms**
- The 572 stored constants of the nm-sim files use only `propext`, `Classical.choice` and `Quot.sound`.
- All 16 endpoints print `[propext, Classical.choice, Quot.sound]` (`axioms-summary.txt`):
  - nm-sim's 3 endpoints;
  - the consolidation's 10;
  - #294's 3.

**Rule 10**
- Whole-file seals of the 11 nm-sim files: A 11/11, B 11/11.
- Paired controls: ALL_OK, 38 sealed negatives.
- The consolidation's seal table (34/41 A, 30/41 B; 0 new failures) still holds. None of its 41 sealed owners has
  a file or TCSlib closure containing a module changed since `7b7d07aa` (`consolidation-seal-closure-check.txt`).

**Admissions**
- 219 warnings, down 2.
- Issued modules: 45 = base 48 − #294's 1 − nm-sim's 2.
- 174 lie outside the issued order, unchanged.

**Lint against the new parent**
- FAIL 214 → 216, WARN 103 → 103.
- The delta is the same as before the rebase:
  - +4 FAILs from the PaddedCPA split, as already accepted;
  - −2 FAILs from deleting `Eager`;
  - ElGamal's size WARN now reads 1830 lines.
- nm-sim adds nothing.

**Sizes:** every nm-sim file is under 1000 lines; the largest is `SimIND`, at 912.

### Evidence

- **`rebase-evidence.zip`** (SHA-256 `d9ab3700f4c91b0856c526769c8eaaccd014c8fb94d4709516c645c6663cc5e0`).
  - It holds the rebase-r1 directory without the raw seal sources and controls records, which were left out for
    size.
  - Its `SHA256SUMS` (SHA-256 `da4ad8b3d1039bbf534db467b91b1062dcf0e65e3abf782a9662b9dbb60c4bf5`, 188 entries,
    verified) covers the whole directory, including the excluded raw files.
  - It does not cover `statements-r2/`, which carries its own manifest.
- **Extracts in this folder:**
  - the patch;
  - `range-diff.txt` and `rebase-check.txt`;
  - the re-point counts;
  - the axioms;
  - the seal tables;
  - the closure check;
  - the census;
  - the lint diff;
  - `decls2-pr.tsv`.

### Debt now foldable (not done here)

These items are in the DL-37 and DL-36 payback for the post-consolidation window:

- `Rounds.rdU`, `rdZ`, `rdW`, `rdState`, `rdIdx`, `rdQuery`, `rdLog` and `Simulator.finSt` are identical to the published
  `InteractiveHandler.rU`, `rZ`, `rW`, `rS`, `rI`, `rX`, `rL`.
- `Rounds.impl_of_ret` → `InteractiveHandler.impl_of_ret`.
- `NMSim.ofFn_padFin_eq_padL` (public, `Rounds.lean`; disclosed in DL-37) is the A4 lemma
  `EnsembleLemmas.ofFn_padFin_eq_padL`. The ledger row now names that counterpart.
- `ChallengeSim.expect_simulate_eager` can be derived from `NMSim.expect_simulate_eager`.
- `rdAns` is a fourth copy of `rFwd`, `rY` and Forward's `rAns`. The ledger row now names it.
- The DL-36 items listed in `../review.md`.

## ===== briefs/pass-shelat-ch5-8/gates/20-dl-consolidation/worker-report.md =====

# dl-consolidation · final delivery (DL-30 to DL-34)

**Worker** Claude. **Issue base** `b96ab3ccc1915497ea3138df499eec00b6581db0` (`cryptography/pass-shelat-ch2-4`,
merge of #293). **Proof branch** `fill/dl-consolidation` (local). **Final head**
`6917e5716066b858a4dbdc33cf7f8653f9a40aa5`, which is 4 commits on the base:

| Commit | Content |
|---|---|
| `01b4f556b` | checkpoint 1: groups P, S, H (Games layer) |
| `d4639a1d1` | checkpoint 2: groups A, L (padFin and blocks readers, new `Foundations/BitLists`) |
| `454c509ed` | checkpoint 3: groups R, O (published readers, leftovers) |
| `6917e5716` | after checkpoint 3: R3 restated through `ChallengeSim.expect_simulate_eager` (this fixed a seal finding), R4 done, the emptied `BitwiseCPA/Eager` module removed |

Lean 4.25.0 and the Mathlib pin of the base manifest.

**Result.**
- 28 items are done, P2 is not a copy, and S3b and R7 are escalated with their obstruction and
  smallest correction.
- S1 is done with both forms kept, with a reason.
- No audited statement changed.
- The fresh sweep of all 407 modules passes, and the sorry census equals `base-sorries.txt`.
- Every stored constant of the changed and new files, and every campaign endpoint, uses only
  `propext`, `Classical.choice` and `Quot.sound`. The exception is the 4 Yao constants that rest on
  the base's admitted sorries, unchanged from the base.
- The whole-file closure seals introduce no new reading through a foreign body. Two pre-existing
  failures (`cca2Encrypt`, `cca2Gen`, the Gate 17 finding) are gone.
- Lint has no new FAIL, and two fewer than the base.

## 1. Environment and method

- **Pack.** Verified at exchange `abbcb1127`: all `SHA256SUMS` OK. All 406 sources of the base match
  `SOURCE-SHA256SUMS` (`evidence/logs/source-sha256.log`).
- **Checkout.** A separate git worktree at `fill/dl-consolidation`, with its own `.lake/packages`.
  - Narrowed Mathlib cache fetch of the 112 roots of `roots.txt` (`cache-get.log`, exit 0).
  - `packages-check.log` and `cache-probe.log` confirm that the packages match the manifest.
  - Preflight passes (`preflight.log`).
- **Checking.**
  - No `lake build` was run.
  - Every check is one module per `scripts/lean_check_tree.sh` call, with one Lean process at a
    time (`evidence/tools/check.sh`, `sweep_chunk.sh`, `mk.py`).
  - The repository's `AGENTS.md` asks for VS Code's infoview instead of command-line checks. That
    is not available here, and the brief and the environment addendum prescribe exactly these
    `lean_check_tree.sh` checks.
- **Bootstrap** (`bootstrap.log`): 406/406 modules, status 0. Its sorry census
  (`sorry-census-bootstrap.txt`) is `base-sorries.txt`: 48 in 26 modules.
- **Base tree for the controls** (`base-tree.log`). A second worktree, detached at the base, with
  its own olean tree and the same packages, built from `order.txt`: 406/406, status 0. It provides
  the base controls (§7) and the extended base dump (§5).

## 2. Items

`Games.ProbComp` is `TCSlib.Cryptography.Games.ProbComp`. Unqualified old names are under
`TCSlib.Cryptography.Composability`, and new names without a prefix are under `TCSlib.Cryptography`.
The census (§5) checks every row of this table against the declaration dumps.

### 2.1 P, S, H (Games layer; checkpoint 1)

| Item | Disposition | Old → new |
|---|---|---|
| P1 | done | `ChallengeSim.expect_sample_equiv`, `expect_sample_comm`, `expect_sample_unique`, `expect_sub` → `Games.ProbComp.` same names, in `Games/Probability.lean` (new section `Sampling`) |
| P2 | not a copy, kept | `ChallengeSim.expect_sample_prod` (`𝔼_{α×β} g = 𝔼_a 𝔼_b g (a, b)`) is a corollary of `Bridge.expect_sample_pair` (`𝔼 (bind-of-two-samples-then-pure) g = 𝔼_{α×β} g`), not a restatement: its proof is that lemma plus `expect_bind`/`expect_pure`. It stays in ChallengeSim. |
| P3 | done | `BitwiseSim.expect_sample_update` (general `ι`) → `Games.ProbComp.expect_sample_update`. `AdaptiveCPA.expect_sample_update` (`Fin κ`) → `Games.ProbComp.expect_sample_coord`, generalized to any finite `ι` and derived from the general form with `expect_sample_comm`. The names are distinct. |
| P4 | done | `PRFGame.abs_expect_sub_le` → `Games.ProbComp.abs_expect_sub_le` |
| S1 | done (both kept, see note) | `PRFGame.simulate_eq_of_abs_bounded` → `Games.simulate_eq_of_abs_bounded`; `AdaptiveCPA.simulate_eq_of_abs` → `Games.simulate_eq_of_abs` (`Games/Simulate.lean`) |
| S2 | done | `AdaptiveCPA.castImpl`, `castImpl_eq`, `castImpl_self`, `simulate_castImpl_toCompOn`, `expect_simulate_castImpl_toCompOn` → `Games.` same names (`Games/BitCodec.lean`, section `Transport`) |
| S3a | done | `PRFGame.expect_simulate_congr` → `Games.ProbComp.expect_simulate_congr` (`Games/Hopping.lean`) |
| S3b | escalated, moved to ChallengeSim | `BitwiseSim.expect_simulate_eager` → `ChallengeSim.expect_simulate_eager` |
| H1 | done | `PRFGame.prob_bad_le`, `PRFGame.expect_sample_mem_le` → `Games.ProbComp.` same names (`Games/Hopping.lean`). The `prob_bad_le` docstring states the per-query potential bound `Pr[bad] ≤ q·(size + q)·δ`. |

All copies were deleted, with no aliases. All uses were re-pointed:
- `AdaptiveCPA.expect_sample_update` → `expect_sample_coord` in `AdaptiveCPA/Hybrid` and
  `OracleFromPRF/Games`;
- `BitwiseSim.expect_sample_update` → `ProbComp.expect_sample_update` in `OracleFromPRF/Lazy`;
- the rest resolve to the new names unchanged through the enclosing namespaces and `open`s.

**Notes on P, S, H.**
- **S1, both forms kept.** The brief asks to derive `simulate_eq_of_abs` from the bounded form, or to
  re-point its uses and delete it. Neither is possible without a statement change, because the
  bounded form does not generalize the unbounded one:
  - The bounded form assumes that every call of `impl₂` below the budget is a deterministic
    `.pure (y, s')`, and that the computation has a query bound `c.CostBoundedBy (fun _ => 1) m`
    with `cnt s + m ≤ κ`.
  - `simulate_eq_of_abs` allows any probabilistic `impl₂` (`impl₁ i x (f s) = (impl₂ i x s).bind …`)
    and any computation.
  - Its one use (`AdaptiveCPA/Reduction`, private `prob_red_tape`) applies it to the reduction's
    handler composed with the CPA oracle, which samples. That lemma's statement has no query budget.

  Both forms now live side by side in `Games/Simulate.lean`, with no copy left anywhere else.
- **S3b, escalated.**
  - **Obstruction.** The statement of `expect_simulate_eager` is about `ChallengeSim.chRun`, which
    is defined in `Encryption/PublicKey/OracleSecurity/ChallengeSim.lean`. No Games module can state
    it without importing a downstream module.
  - **Smallest correction.** Give it its home beside `chRun` in `ChallengeSim`. This is the
    lowest module whose imports cover the statement. It is no longer a BitwiseCPA-local lemma.
- **S2.** `castImpl`'s type uses `unifSpec` and `ProbComp`. These are not in `BitCodec`'s base
  imports, so `Games/BitCodec.lean` now imports `TCSlib.Cryptography.Games.Probability` (see §3).

### 2.2 A (padFin, blocks), L (shared list module; checkpoint 2)

| Item | Disposition | Old → new |
|---|---|---|
| A1 | done | `ofFn_padFin_of_length` (public, `Asymptotic/HardCoreGLColl.lean`) moved to `Asymptotic/Adversary.lean` beside `padFin`. Full name and statement are unchanged. Deleted: `GGMRed.ofFn_padFin_of_length` (`GGM/Run.lean`, public) and ElGamal's private `dlc_ofFn_padFin`. 52 uses of the GGM name and 5 of the ElGamal name (2 in proofs, 3 in docstrings) were re-pointed. |
| A1′ | not used as the home | `Collection.ofFn_padFin_of_le` (`List.ofFn (padFin ℓ w) = w ++ 0^(ℓ - |w|)` for `|w| ≤ ℓ`) does not subsume A1 as a drop-in: getting the equality form takes three more rewrites (`h`, `Nat.sub_self`, `replicate_zero`, `append_nil`), which is exactly the deleted ElGamal copy. A1's 57 users need the equality form, and `ofFn_padFin_of_le` keeps its own users (Lamport, EncryptThenTag, the two Handlers). |
| A2 | done | `AdaptiveCPA.ofFn_cast` → `ofFn_cast` (`Adversary.lean`). The private `cca2OfFn_cast` (`OracleFromPRF.lean`) was deleted, and its 4 uses plus 9 uses of the AdaptiveCPA name were re-pointed. |
| A3 | done, home split | `ofFn_arrowCongr_finCongr` (`PRFGame`, Transfer) → `ofFn_arrowCongr_finCongr` (`Adversary.lean`). `AdaptiveCPA.padFin_ofFn_zeroBits`, `PRFGame.padFin_replicate_false` and `PRFGame.padFin_nil` → `Games.` same names (`Games/BitCodec.lean`, beside `zeroBits`). These three mention `zeroBits`, which is defined in `Games/BitCodec.lean`, downstream of `Adversary`. `BitCodec` imports `Adversary`, so they go beside `zeroBits`. Their docstrings say so; the brief allows `Games/BitCodec.lean` for group A. |
| A4 | done | Private `ofFn_padFin_eq_padL` in `AdaptiveCPA/Handler` and in `OracleFromPRF/Handler` → public `EnsembleLemmas.ofFn_padFin_eq_padL` beside `padL`. It holds by `rfl`, since `padL` is its home file's definition. |
| A5 | done | New `FunFamily.ofFn_blocks`: `⟦FunFamily.blocks q ℓ ω j⟧ = (⟦ω⟧.drop (j·ℓ)).take ℓ`, beside `FunFamily.blocks` in `Adversary.lean`, read through `FunFamily.blocks_apply`. `AdaptiveCPA.ofFn_acTapes` and `PRFGame.ofFn_pkTapes` keep their names and statements, and are now derived from it. `ofFn_pkTapes` goes through `EnsembleLemmas.blocks_eq` and `ofFn_arrowCongr_finCongr`. |
| A6 | done | `BitwiseSim.decodeFin_nil_getD` → `Games.decodeFin_nil_getD` (`Games/BitCodec.lean`; it mentions `zeroBits`) |
| L1 | done | New module `Foundations/BitLists.lean` (Mathlib imports only). `headD_drop` is generalized to lists over any type, `(l.drop i).headD d = l.getD i d`. It replaces `CommitmentLemmas.headD_drop`, `BitwiseSim.headD_drop` (the `d = false` form), NextBit's private `headD_drop_ofFn`, and the further copy `GI.getD_eq_headD_drop` (reversed, `ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean`, found by grep). |
| L2 | done | `BitwiseSim.flatten_ofFn_singleton` and Yao's private `flatten_ofFn_one` → `flatten_ofFn_one` (general blocks, Yao's form) and `flatten_ofFn_singleton` (constant blocks, derived from it), in BitLists |
| L3 | done | `AdaptiveCPA.headD_ofFn_one` → `headD_ofFn_one` (BitLists) |
| L4 | done | `PRFGame.zipWith_xor_cancel_left` → `zipWith_xor_cancel_left` (BitLists) |
| L5 | done | `PRFGame.xorPerm`, `PRFGame.xorPerm_apply` → `xorPerm`, `xorPerm_apply` (BitLists). `ctOf_xorPerm` stays in Collision. |
| L6 | done, promoted | `PRFGame.mem_keys_of_lookup_isSome` → `mem_keys_of_lookup_isSome` (BitLists). Core's `List.lookup_isSome_iff` exists at the pin, but it states `(l.lookup k).isSome ↔ ∃ p ∈ l, k == p.1`, not membership in `l.map Prod.fst`. Using it at the one use would change that proof beyond a re-pointing, so the lemma is promoted and re-proved through the core lemma (`List.mem_map`). |
| L7 | done | `AdaptiveCPA.ofFn_splitHalf_fst`, `_snd` → `FixedLengthScheme.ofFn_splitHalf_fst`, `_snd`, beside `splitHalf` in `Encryption/PrivateKey/OracleSecurity.lean`, read through `splitHalf_fst/_snd` |

**Re-pointing changes beyond renaming (A, L).**
- NextBit's one use of `headD_drop_ofFn` (a `rw` list) became
  `headD_drop, List.getD_eq_getElem?_getD, List.getElem?_ofFn`, closed by the existing `simp`.
- The ZK uses of `getD_eq_headD_drop` flip direction:
  - `getD_eq_headD_drop` becomes `← headD_drop` (2 uses);
  - `← getD_eq_headD_drop` becomes `headD_drop` (3 uses).

  Each rewrites the same pattern.
- `Games.padFin_ofFn_zeroBits` is re-proved by `getD_eq_getElem?_getD` and `getElem?_replicate`. The
  base proof used `List.getD_eq_getElem`/`getD_eq_default` from `Mathlib.Data.List.GetD`, which
  `BitCodec` does not import, and this way it needs no Mathlib import.
- Lines that became longer than 100 characters after a renaming were re-wrapped.

**L, the module choice.**
- The lemmas need only `Mathlib.Data.List.{OfFn,GetD}` and `Mathlib.Logic.Equiv.Prod`. All three are
  in `roots.txt`.
- No existing module fits:
  - `Foundations/` has no list module.
  - The only upstream homes for generic list lemmas are outside `TCSlib/Cryptography/` (out of
    scope).
  - Every cryptographic module that already holds some of these lemmas imports large parts of the
    library.
- `BitLists` is imported by its 11 consumers and listed in the `Foundations` facade's `## Contents`.

### 2.3 R (published readers), O (leftovers; checkpoint 3 and after)

| Item | Disposition | Old → new |
|---|---|---|
| R1 | done | `AdaptiveCPA.indCodec_eq_bitCodec` → `FixedLengthPKScheme.indCodec_eq_bitCodec` (`Encryption/PublicKey/OracleSecurity.lean`); `PRFGame.indCodec_eq_bitCodec` (Transfer) → `FixedLengthScheme.indCodec_eq_bitCodec` (`Encryption/PrivateKey/OracleSecurity.lean`). Both are published readers beside `indCodec` with the same statement, proved by `rfl` in their home files (the copies went through the three codec readers and structure eta). 4 uses re-pointed. |
| R2 | done, nothing to re-point | `hybridPre_eq` (the defining equation, `rfl`) added beside `hybridPre` in `HybridMachine.lean`. At the base no BitwiseCPA file reads `hybridPre` (grep receipt R2: every hit is in `HybridMachine.lean`), so there is no reading to re-point. The related `BitwiseSim.plantTuple` is recorded in §11. |
| R3 | done; statement read through readers | The private `expect_simulate_indImpl_cpa` of `Encryption/PublicKey/OracleSecurity.lean` is published under that name (`Composability.expect_simulate_indImpl_cpa`), with a formula docstring and a sketch. `BitwiseSim.expect_simulate_indImpl_cpa` (Eager) is deleted. The published lemma keeps the general state `s`, and reads the halves and the record through `indSpec_challengeDom`/`indSpec_challengeRng`. It is now a corollary of the generic `ChallengeSim.expect_simulate_eager`, which removes a second copy of the eager induction. See the note. Its uses: `padded_cpa_advantage_eq` (proof unchanged) and BitwiseCPA's `accept_indGame_eq` (now passes the state `none`). |
| R4 | done (after checkpoint 3) | `BitwiseSim.padded_enc_runAt`, `padded_enc_coins` → `PublicKeyScheme.padded_enc_runAt`, `PublicKeyScheme.padded_enc_coins`, beside the padded readers (section `PublicKeyPaddedReaders` of `Encryption/PublicKey/OracleSecurity.lean`). They take the section's variables, in the same argument order. At checkpoint 3 this was escalated for file size; R3's re-proof freed 19 lines, so the file is 987 lines with them. `BitwiseCPA/Eager.lean` was left empty and is removed (see §3). |
| R5 | done | `BitwiseSim.chRun_toCompOn_transport_list` → `ChallengeSim.chRun_toCompOn_transport_list` (same statement). `ChallengeSim.chRun_toCompOn_transport` keeps its name and statement and is derived from it with `G = fun _ => w`. |
| R6 | done | The private round-input readers `rU`, `rZ`, `rW`, `rS`, `rI`, `rX`, `rL`, `rCnt` of `AdaptiveCPA/Handler` and `rU`, `rW`, `rS`, `rI`, `rX`, `rL`, `rCnt` of `OracleFromPRF/Handler` → one public set `Games.InteractiveHandler.rU … rCnt` beside `InteractiveHandler.input` (`Games/Efficiency.lean`), with the readers `rU_input … rCnt_input` (each field of `input n z ω s i x L`) and `polyTimeComputable_rU … _rCnt`. Both private `impl_of_ret` → one generic `Games.InteractiveHandler.impl_of_ret` (any handler, any `perCall`). Both private `replicate_one` → core `List.replicate_one` after core `Fin.val_one`; core has it, so no List lemma is added. |
| R7 | escalated (one function up to parameters) | See the note below. |
| O1 | done | The private `bitwise_runAtL` (BitwiseCPA) is deleted; `bitwise_runAt_blocks` now uses the published `BitPublicKeyScheme.bitwise_enc` and `bitwise_enc_runAtL` directly. The private `ofFn_half` is kept, because no published lemma states its shape (the selected half as `List.ofFn` of `getD`, which `bitwise_runAt_blocks` needs). It is re-proved from the published `FixedLengthScheme.ofFn_splitHalf_fst/_snd` instead of re-deriving them through `splitHalf_fst/_snd` and indices. |
| O2 | done | `cca2CtLen` deleted; its 2 uses read `prf_ctLen_eval` and `ctP_eval` from PRFStep. `cca2Gen` and `cca2Encrypt` keep their statements (their existential shapes are used by `obtain`), and are now one-line corollaries of PRFStep's `prf_gen_runAt`/`ofFn_prfKeyEq` and `ofFn_prf_encryptAt`/`ofFn_prfNonceEq`. `cca2Decrypt` vs `ofFn_prf_decAnswer` is not merged; the reason is in the note. |

**Re-pointing changes beyond renaming (R, O).**
- The `fields_input` lemmas of both handlers used to unfold the private readers by
  `simp only [InteractiveHandler.input_eq, rU, …]`. They now `simp only` with the published
  `rU_input, …, rCnt_input`.
- The three `have`s of `acHandler_impl_dec` are the published `rI_input`, `rU_input`, `rS_input`.
- The `have hU : PolyTimeComputable rU := hF.comp hF` lines of `polyTimeComputable_acRun/_pkRun` are
  now the published `polyTimeComputable_rU …`. The composition proof would read the published
  definitions through their bodies.
- At the 5 uses of `impl_of_ret`, `refine InteractiveHandler.impl_of_ret _ n z ω x s _ _ ?_` is
  followed by `show acRun S cap _ = _` (resp. `pkRun`). This reads the home file's `acHandler` and
  `pkHandler`.
- One reverse use `← replicate_one` (AdaptiveCPA, before `decodeBitMove_query`) is dropped: `exact`
  checks `[true] = List.replicate ↑(1 : Fin 2) true` definitionally, which unfolds only core
  definitions.
- In O2, the two `rw [cca2CtLen]` become `rw [prf_ctLen_eval, PRFGame.ctP_eval]`.

**Notes on R, O.**
- **R3, statement.** The private lemma's statement is
  `… (chRun (fun mm => … (splitHalf mm) …) c s)`, which typechecks only by unfolding `indSpec`,
  `inLens` and `outLens`:
  - `mm : (S.indSpec n).dom 1` is fed to `splitHalf` at type `Fin (m + m) → Bool`;
  - the state `s : Option (Fin (ctLen n) → Bool)` is fed to `chRun` at type
    `Option (Fin (outLens n 1) → Bool)`.

  A consumer instantiating it, as BitwiseCPA does, would read `OracleSecurity`'s definitions
  through their bodies.
  - **The seal caught this.** The checkpoint-3 form had fixed the halves, but still passed `s`
    directly. The final-head seal of `BitwiseCPA.lean` failed at `accept_indGame_eq`, on exactly
    that state type (`seal-final.out` at `454c509ed`, kept in the dev logs).
  - **The final statement** reads both through the published casts:
    `cast (S.indSpec_challengeDom n) mm`, and the state `s.map (cast (S.indSpec_challengeRng n).symm)`.
    This is the shape of `ChallengeSim.expect_simulate_eager`, so the lemma is that generic lemma
    instantiated with the published oracle equations `indImpl_*_onSpec`. That is the proof the
    deleted BitwiseSim copy had, for the state `none`.
  - The private induction that re-proved the generic eager lemma is gone.
  - With `s = none`, the statement is the deleted copy's, up to `none.map f ≡ none`.
  - Both seals now pass.
- **R4.** At checkpoint 3, `OracleSecurity.lean` would have exceeded 1000 lines with the readers
  (989 + at least 15). The R3 re-proof through `ChallengeSim.expect_simulate_eager` replaced the
  private induction and freed 19 lines (970), so R4 was done: the file is 987 lines, below the
  limit.
  `BitwiseCPA/Eager.lean` held nothing else and was removed. Its two importers now import its only
  import, `OracleSecurity`, or nothing, so no import closure changes.
- **R7, escalated.**
  - `recDin Lc = ![Lc, 2]`, `recDout Lc = ![2, Lc]` (`RecordHandler`),
    `acDin S = ![ctLen, msgLen + msgLen]`, `acDout S = ![msgLen + 1, ctLen]` (`AdaptiveCPA/Handler`)
    and `qDin Lc Lq = ![Lc, Lq]`, `qDout Ld Lc = ![Ld, Lc]` (`QueryHandler`) are one function up to
    parameters. `qDin` and `qDout` are themselves the generic two-entry vector, and the others are
    instances of it.
  - **Obstruction.** These definitions occur in the statements of public declarations: the handler
    types `PolyHandler 2 (recDin Lc) (recDout Lc)`, `acHandler`, `qHandler`, `exists_qHandlerMachine`,
    and every lemma about their lengths. Re-pointing the uses to one published function changes
    those statements.
  - Keeping the six names as thin wrappers of a published function would delete no copy of a
    declaration. Their readers (`recDin_zero`, …) would then read a foreign body, so it would only
    add an indirection.
  - **Smallest correction.** Publish one `Games.lens2 (a b : PolyExpr) : Fin 2 → PolyExpr` with
    `lens2_zero`/`lens2_one` (or use `![a, b]`) beside `bitSpecAt` in `Games/Efficiency.lean`. Then,
    in a statement-changing follow-up approved at the gate, replace the six definitions by it. The
    3-entry `pkDin`/`pkDout` (`OracleFromPRF/Handler`) is a different arity and is not a copy.
- **O2, not merged.** `cca2Decrypt` (`decodeFin n (Dec ⟨k, ⟨x, v⟩⟩) = some (v + F n k x)` for every
  `n`) and `ofFn_prf_decAnswer` (the oracle's answer list `decAnswer`, with the well-formedness test,
  for `n > 0`) have different statements and hypotheses. They share only the core step
  `runAt_prfDec`. Neither is a restatement of the other.

## 3. Import changes

| Module | Change | Reason | Acyclic |
|---|---|---|---|
| `Games/BitCodec.lean` | + `TCSlib.Cryptography.Games.Probability` | `castImpl` (S2) is a `QueryImpl … unifSpec`, and its readers use `ProbComp.expect` | yes: `Games/Probability` imports only `Games/Simulate`, `Games/Machines` and Mathlib |
| `Foundations.lean` (facade) | + `TCSlib.Cryptography.Foundations.BitLists` | the facade imports every child | yes: `BitLists` imports only Mathlib |
| `Foundations/BitLists.lean` (new) | `Mathlib.Data.List.OfFn`, `Mathlib.Data.List.GetD`, `Mathlib.Logic.Equiv.Prod` | the L lemmas | Mathlib only; all three are in `roots.txt` |
| 11 consumers | + `TCSlib.Cryptography.Foundations.BitLists` | the L lemmas they use | yes |
| `OracleFromPRF/Lazy.lean` | `BitwiseCPA.Eager` → `Encryption.PublicKey.OracleSecurity` | `Eager` was removed; `OracleSecurity` was its only import, so the import closure is unchanged | yes |
| `BitwiseCPA.lean` | − `BitwiseCPA.Eager` | `Eager` was removed; its content now lives in `OracleSecurity`, which `BitwiseCPA` already imports through `AdaptiveCPA` | yes |

- The 11 consumers are `AdaptiveCPA/{Games,Reduction}`, `BitwiseCPA/Planted`,
  `OracleFromPRF{,/Reduction,/Lazy,/Collision}`, `Pseudorandom/NextBit`, `SecureComputation/Yao`,
  `ZeroKnowledge/CommitmentLemmas` and `ZeroKnowledge/GraphIsomorphism/EfficiencyRep{,GI}`.
- The R6 consumers use `open TCSlib.Cryptography.Games.InteractiveHandler (rU …)`, which adds no
  import.
- **Final order** (`evidence/logs/order-final.txt`, 407 modules). This is `order.txt` with three
  changes:
  - `Games/Probability` moved before `Games/BitCodec`;
  - `Foundations/BitLists` inserted before its first consumer, `Pseudorandom/NextBit`, followed by
    the `Foundations` facade (not in `order.txt`, but edited);
  - `BitwiseCPA/Eager` removed.

## 4. Changed, new and deleted files (base → final, lines)

37 paths: 35 changed, 1 new (`Foundations/BitLists.lean`), 1 deleted (`BitwiseCPA/Eager.lean`). Every
file is below 1000 lines, except `ElGamal.lean`, which is 1835 lines at the base (lint WARN at the
base) and is now 1829.

| File | Base | Final |
|---|---|---|
| `Games/Probability.lean` | 291 | 397 |
| `Games/Simulate.lean` | 276 | 327 |
| `Games/Hopping.lean` | 352 | 444 |
| `Games/BitCodec.lean` | 297 | 399 |
| `Games/Efficiency.lean` | 706 | 842 |
| `Foundations.lean` | 32 | 35 |
| `Foundations/BitLists.lean` (new) | — | 105 |
| `Asymptotic/Adversary.lean` | 323 | 373 |
| `Asymptotic/EnsemblesLemmas.lean` | 860 | 865 |
| `Asymptotic/HardCoreGLColl.lean` | 405 | 399 |
| `Pseudorandom/Functions/Asymptotic/GGM/Run.lean` | 779 | 773 |
| `Pseudorandom/NextBit.lean` | 470 | 464 |
| `SecureComputation/Yao.lean` | 951 | 942 |
| `ZeroKnowledge/CommitmentLemmas.lean` | 506 | 503 |
| `ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean` | 639 | 636 |
| `ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI.lean` | 334 | 335 |
| `Encryption/PublicKey/ElGamal.lean` | 1835 | 1829 |
| `Encryption/PublicKey/HybridMachine.lean` | 393 | 411 |
| `Encryption/PublicKey/OracleSecurity.lean` | 982 | 987 |
| `Encryption/PublicKey/OracleSecurity/ChallengeSim.lean` | 274 | 315 |
| `Encryption/PublicKey/OracleSecurity/RecordHandler.lean` | 333 | 333 |
| `Encryption/PublicKey/AdaptiveCPA/Hybrid.lean` | 411 | 289 |
| `Encryption/PublicKey/AdaptiveCPA/Handler.lean` | 596 | 543 |
| `Encryption/PublicKey/AdaptiveCPA/Games.lean` | 301 | 240 |
| `Encryption/PublicKey/AdaptiveCPA/Reduction.lean` | 274 | 275 |
| `Encryption/PublicKey/BitwiseCPA.lean` | 558 | 549 |
| `Encryption/PublicKey/BitwiseCPA/Eager.lean` (deleted) | 167 | — |
| `Encryption/PublicKey/BitwiseCPA/Planted.lean` | 323 | 304 |
| `Encryption/PublicKey/BitwiseCPA/QueryHandler.lean` | 402 | 369 |
| `Encryption/PrivateKey/OracleSecurity.lean` | 374 | 400 |
| `Encryption/PrivateKey/OracleFromPRF.lean` | 886 | 859 |
| `Encryption/PrivateKey/OracleFromPRF/Collision.lean` | 514 | 401 |
| `Encryption/PrivateKey/OracleFromPRF/Games.lean` | 329 | 307 |
| `Encryption/PrivateKey/OracleFromPRF/Handler.lean` | 753 | 702 |
| `Encryption/PrivateKey/OracleFromPRF/Lazy.lean` | 484 | 476 |
| `Encryption/PrivateKey/OracleFromPRF/Reduction.lean` | 367 | 338 |
| `Encryption/PrivateKey/OracleFromPRF/Transfer.lean` | 202 | 163 |

Net: 17,979 lines at the base, 17,929 at the final head.

## 5. Census (`evidence/logs/census.txt`, `namemap-check.txt`)

- **Dumps.**
  - `decl-dump-base-ext.log` was taken at the base tree. It has every stored constant of the 35
    candidate modules plus `ZeroKnowledge/GraphIsomorphism/EfficiencyRep{,GI}` and the
    `Foundations` facade.
  - `decl-dump-final.log` was taken at the final head over the same modules, with
    `Foundations/BitLists` added and the deleted `Eager` removed.
  - Each row is `name | module | kind | type hash | attributes (reducibility, simp, instance,
    protected) | axioms`.
  - The checkpoint-time `decl-dump-base.log` (35 modules) agrees with the extended base dump on
    every common row (1896 rows, 0 differ).
- **Comparison** (`tools/cmpdump.py`), restricted to the 37 changed paths:

  | Class | Count | Content |
  |---|---|---|
  | rows (base / final) | 1994 / 1981 | stored constants of the 37 changed paths (the 35 modified modules, `BitLists`, `Eager`) |
  | **removed** | 102 | 70 named: exactly the listed copies (§2) and the further copies folded in (`GI.getD_eq_headD_drop`, ElGamal's `dlc_ofFn_padFin`, `cca2OfFn_cast`, `cca2CtLen`, the private readers, `impl_of_ret`, `replicate_one`, `bitwise_runAtL`), and Eager's `padded_enc_runAt/_coins`. 32 are their auxiliaries (`match_`, `_proof_`, `eq_1`). |
  | **added** | 89 | 68 named: the promoted lemmas, the published readers (`indCodec_eq_bitCodec` ×2, `hybridPre_eq`, `expect_simulate_indImpl_cpa`, `rU … rCnt` with `_input` and `polyTimeComputable_`, `impl_of_ret`) and the new A5 lemma `FunFamily.ofFn_blocks`. 21 are auxiliaries. All 89 are `regular`, not `simp`, not instances, not protected. |
  | **moved** (same name, type, attributes) | 2 | `ofFn_padFin_of_length` (HardCoreGLColl → Adversary, A1), and the auto-generated `ProbComp.sample.congr_simp`. The second is now generated in `Games/Probability`, where the promoted sampling lemmas first need it, not in `PrivateKey/OracleSecurity`. |
  | **changed** (type hash) | 25 | none in statement: see the next row |
  | changed modulo the name map | **0** | `typecmp.txt`: each of the 25 base types, with every moved constant renamed by `namemap.txt`, hashes to the final type. They change only because they mention a moved declaration: `castImpl` (`castImpl_adaptiveIndImpl`, `castImpl_indImpl_challenge`, private `comp_acAbs`), `xorPerm` (`ctOf_xorPerm`), or the R6 readers (the private handler definitions' `eq_1` lemmas, `fields_input`, `polyTimeComputable_acRun` auxiliaries). Attributes and visibility: 0 changed. |
  | axioms changed | 1 | `BitwiseSim.plantOut_recorded`: `[Classical.choice, Quot.sound, propext]` → `[Quot.sound, propext]`, a subset. Its `rw` used the induction-and-`simp` proof of the deleted `BitwiseSim.headD_drop`, and now uses the `rw` proof of the promoted `headD_drop`. |


- **Name map** (`tools/namemap_check.py` over `namemap.txt`). For every old name: whether it is gone,
  whether the new name exists, and whether the types are identical (type hash).

  - **69 rows** (`evidence/namemap.txt`, `logs/namemap-check.txt`): every old name is gone except the
    moved `ofFn_padFin_of_length`, and every new name exists. The 3 that point outside the dumps are
    core `List.replicate_one` (×2) and `BitPublicKeyScheme.bitwise_enc_runAtL` (`EnsembleSecurity`).
  - **Same statement modulo renaming:** 54 pairs (`typecmp.txt`); binder names do not count. 2 rows
    are new declarations.
  - **Different statement, all intended:** 15 pairs.
    - P3: `ProbComp.expect_sample_update` binds `β` before `ι`, because `β` is the section
      variable. `expect_sample_coord` generalizes `Fin κ` to any finite `ι`.
    - L1: `headD_drop` is generalized from `Bool` (and from `d = false` for BitwiseSim's). It replaces
      NextBit's `ofFn` form and the reversed `GI.getD_eq_headD_drop`.
    - L2: Yao's `flatten_ofFn_one` differs only in the proof term `⟨0, by omega⟩` inside the
      statement.
    - R3: the cast form, see §2.3.
    - R6: the generic `impl_of_ret`, and core's `List.replicate_one`.
    - O1: `bitwise_runAtL` → `bitwise_enc_runAtL`, after `bitwise_enc`.
    - O2: `cca2CtLen` → `prf_ctLen_eval` + `ctP_eval`.

## 6. Axioms (`decl-dump-final.log`)

- **Every stored constant** of the 36 final files and the 2 further candidate modules: 1981 rows
  for the changed paths, 2011 in the dump.
  - Each uses a subset of `propext`, `Classical.choice`, `Quot.sound`: 1153 use all three, 293
    `[Quot.sound, propext]`, 185 `[propext]`, 10 `[Classical.choice]`, 6 `[Quot.sound]`, 330 none.
  - The only exceptions are the 4 Yao constants that use `sorryAx`: the 3 admitted statements of
    `base-sorries.txt` (`yaoSeed_good_whp`, `yaoHybrid_polyTime`, `yaoHybrid_simulators`), and
    `yaoHybrid_hbcSecure`, which uses them. These are the same 4 as in the extended base dump.
- **The nine campaign endpoints** each print `[Classical.choice, Quot.sound, propext]`, as at the
  base: `prfFixedScheme_cpa`, `prfFixedScheme_cca1`, `not_prfFixedScheme_cca2`,
  `FixedLengthPKScheme.INDSecure.adaptive_cpa`, `BitPublicKeyScheme.SingleBitSecure.{bitwise_padded_cpa,
  exists_adaptive_cpa, padded_cpa}` and `Implications.PublicKey.exists_adaptiveCPA_of_{rsa,factoring}`.
- **Changed axioms:** only `plantOut_recorded`, to a subset (§5).

## 7. Rule 10

### 7.1 Whole-file closure seals

The seals follow the Gate 17 audit's method: the whole import closure, abbreviations excluded, and
the instance-unfolding mask (`tools/seal_gen.py`, `tools/seal_run.py`).
- Each sealed copy is a verbatim copy of the file with its own imports and `import Lean`.
- Right after the imports, a `run_cmd` makes **every TCSlib definition of the import closure**
  `irreducible` with `attribute [local irreducible]` (between 17 and 1573 definitions
  per file; 0 for `BitLists`, whose closure is Mathlib only), and removes them from the
  instance-unfolding set.
- Two kinds of definition are excluded:
  - abbreviations (`abbrev` hints: structure projections, `casesOn`, `noConfusion`, notation such
    as `bitSpec`, `indSpec`);
  - in the second variant, `PolyExpr.eval`.
- The copy is a new module, so the file's own definitions stay transparent. The whole file must
  elaborate while reading every other TCSlib definition only through its published lemmas.

**Final head** (`seal-final.jsonl`, `seal-final.out`; `PolyExpr.eval` sealed), 36 files:
- **26 of 36 pass:**
  - all five Games files, the `Foundations` facade and `BitLists`, and `Adversary`;
  - every `OracleFromPRF` file and `PrivateKey/OracleSecurity`;
  - `AdaptiveCPA/{Games,Hybrid,Reduction}`, `BitwiseCPA` with `Planted` and `QueryHandler`;
  - `ChallengeSim`, `RecordHandler`, `ElGamal` and `NextBit`.
- **10 fail**, all at declarations that this job did not write:

| File | Final, eval sealed | Base, eval sealed | Final, eval open | Base, eval open |
|---|---|---|---|---|
| `Asymptotic/EnsemblesLemmas.lean` | 11 errors in 10 decls | 11 errors in 10 decls | 11 errors in 10 decls | 11 errors in 10 decls |
| `Asymptotic/HardCoreGLColl.lean` | 3 errors in 2 decls | 3 errors in 2 decls | pass | pass |
| `Encryption/PrivateKey/OracleFromPRF.lean` | **pass** | 2 errors in 2 decls (`cca2Encrypt`, `cca2Gen`) | — | pass |
| `Encryption/PublicKey/AdaptiveCPA/Handler.lean` | 3 errors in 3 decls (`acTapes`, `acTapes_apply`, `acHandler_finish`) | the same | pass | pass |
| `Encryption/PublicKey/HybridMachine.lean` | 1 error (`blockEncFun_flatten`) | the same | 1 error | 1 error |
| `Encryption/PublicKey/OracleSecurity.lean` | 4 errors in 2 decls (`PublicKeyScheme.padded`, `BitPublicKeyScheme.padded`) | the same | pass | pass |
| `Pseudorandom/Functions/Asymptotic/GGM/Run.lean` | 10 errors in 8 decls | the same | 9 errors in 7 decls | the same |
| `SecureComputation/Yao.lean` | 15 errors in 8 decls | the same | pass | pass |
| `ZeroKnowledge/CommitmentLemmas.lean` | 8 errors in 8 decls | the same | 6 errors in 6 decls | the same |
| `ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean` | 6 errors in 6 decls | the same | 4 errors in 4 decls | the same |
| `ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI.lean` | 3 errors in 2 decls | the same | 3 errors in 2 decls | the same |

**Base controls** (`seal-base.jsonl`, `seal-base.out`). The base copies of the 35 files that exist at
the base, sealed the same way over the base tree:
- **24 of 35 pass.**
- **11 fail.** These are the 10 above, at the same declarations with the same error counts, plus
  `OracleFromPRF.lean` at `cca2Encrypt` and `cca2Gen`. That is the Gate 17 finding: they read
  `PolyExpr.eval .var` definitionally.

**Comparison** (`tools/cmp_scans.py seals`, `logs/seal-compare.txt`):
- **New failing declarations: 0**, with `PolyExpr.eval` sealed (`seal-compare.txt`) and with it open
  (`seal-compare-evalopen.txt`). In every failing file, the failing declarations are identical at
  the base and at the final head.
- **Two failures removed.** O2 re-derived `cca2Encrypt` and `cca2Gen` from PRFStep's
  `ofFn_prf_encryptAt`/`ofFn_prfNonceEq` and `prf_gen_runAt`/`ofFn_prfKeyEq`, which read the nonce
  and key widths through `finCongr (eval_var n)`. `OracleFromPRF.lean` now passes the full seal.
- **The new code passes every seal.** That covers:
  - all promoted lemmas and published readers (`Adversary`, `BitCodec`, `Probability`, `Simulate`,
    `Hopping`, `Efficiency`, `BitLists`, `ChallengeSim`, both `OracleSecurity` files,
    `HybridMachine`'s `hybridPre_eq`, `EnsemblesLemmas`' `ofFn_padFin_eq_padL`);
  - every re-pointed use.

  None of them is among the failing declarations.
- **The legacy failures that remain with `PolyExpr.eval` open** read other bodies. These are
  pre-existing, in code this job only re-points:
  - `EnsemblesLemmas` reads `uprob`/`acceptProb`;
  - `HybridMachine.blockEncFun_flatten` reads `NUPPT.layout`;
  - `GGM/Run` reads `simulate`/`evalLazy`;
  - `CommitmentLemmas` reads `distAdv` and `EnsembleLemmas.swapAux`;
  - `EfficiencyRep` reads `pairSndD []`;
  - `EfficiencyRepGI` reads `encGraph`/`permGraph` by `Iff.rfl`.

  The rest of each failure list is `PolyExpr.eval` readings.

**`PolyExpr.eval` open** (`seal-final-evalopen.jsonl`, `seal-base-evalopen.jsonl`). The failing files
re-sealed with `PolyExpr.eval` left transparent (the Gate 17 remark):
- **10 final files re-sealed**, and the 11 failing base files re-sealed.
- **4 final files then pass**: HardCoreGLColl, AdaptiveCPA/Handler, OracleSecurity and Yao. At the
  base, OracleFromPRF passes too. Their only readings are of `PolyExpr.eval`, for example `acTapes`'s
  `(cap.mul coins).eval n` read as `cap.eval n * coins.eval n`, and Yao's `(inB.mul var).eval n`.
- **6 still fail**, at the same declarations at the base: EnsemblesLemmas, HybridMachine, GGM/Run,
  CommitmentLemmas, EfficiencyRep and EfficiencyRepGI (the readings listed above).

### 7.2 Paired controls (`seal/SealControls*.lean`, `seal-controls-*.log`)

Ten examples read one TCSlib definition each through its body (`rfl`):
- `PolyExpr.eval`, `padFin`, `zeroBits`, `FunFamily.blocks`, `EnsembleLemmas.padL`, `xorPerm`,
  `InteractiveHandler.rU`;
- the public and private `indCodec`, and `splitHalf`.

These cover the definitions that the promoted lemmas and readers are about.

| Run | Result |
|---|---|
| Unsealed (`seal-controls-unsealed.log`) | **pass**, status 0 |
| Sealed, `PolyExpr.eval` included (`seal-controls-sealed.log`) | **10/10 fail**, one error per example, at lines 57, 58, 59, 61, 62, 63, 64, 66, 68, 70 |
| Sealed, `PolyExpr.eval` open (`seal-controls-sealed-evalopen.log`) | **9/10 fail**; only the `PolyExpr.eval` example (line 57) passes |

The seal is therefore active, and the `PolyExpr.eval` exclusion does exactly what it says.

### 7.3 Explicit-unfold scan (`tools/rwids.py`, `rwids_run.sh`; `rwids-final.tsv`, `rwids-base.tsv`)

`irreducible` does not block `rw [f]`, `simp [f]`, `unfold f` or `delta f`, so a separate scan does
this:
- It collects every identifier passed to `rw`, `rwa`, `nth_rw`, `rewrite`, `erw`, `simp`,
  `simp only`, `simp_all`, `simpa`, `dsimp`, `simp_rw`, `field_simp`, `norm_num`, `unfold` and
  `delta` in **each whole changed file**.
- It resolves each one in the file's namespaces with the file's `open`s.
- It classifies each one as a theorem, a definition of the file itself, a core or Mathlib
  definition, a **foreign TCSlib definition**, or unresolved (a local hypothesis or one of the
  file's private declarations).

| Identifiers | Final (36 files) | Base (35 files) |
|---|---|---|
| theorems | 1973 | 1957 |
| the file's own definitions | 109 | 101 |
| core or Mathlib definitions | 5 | 5 |
| unresolved (local hypotheses, the file's private declarations) | 551 | 584 |
| **foreign TCSlib definitions** | **0** | **0** |

- **Core and Mathlib.** The 5 entries are the same at both: the `reduceIte` simproc in Collision
  and BitwiseCPA, and `Ne`, `Prod.map`, `id` in ElGamal.
- **Own definitions.** The only new ones are in `Games/Efficiency.lean`: its own new readers
  `rU … rCnt`, unfolded in their `_input` lemmas.
- **Foreign.** No foreign TCSlib definition is passed explicitly, at the base or at the final head
  (`rwids-compare.txt`: new foreign explicit unfolds 0).
- **What R6 removed.** At the base, the handlers' `fields_input` and `acHandler_impl_dec` unfolded
  their private readers. Those readers are now published, and the handlers use their `_input`
  lemmas.

## 8. Sweep and admissions

- **Fresh sweep** (`sweep-final.log`, order `order-final.txt`, at `6917e5716`).
  - The olean tree was removed first.
  - **407/407 modules, status 0, 0 errors**, 38.6 min of checking.
- **Admissions** (`sorry-census-final.txt`): **48 sorry warnings in 26 modules**, identical to
  `base-sorries.txt` (`cmpcensus.sh`: CENSUS IDENTICAL).
- **Other warnings.** The non-sorry warnings are identical to the bootstrap's: 129 = 129, none new,
  none gone.
- **Base tree** (`base-tree.log`). 406/406, status 0, with the same 48 sorry warnings in the same 26
  modules. In `sorry-census-base-tree.txt`, Yao's three are shown by line, because `census.py` looks
  names up in the final sources.

## 9. Lint (`lint-final.log`)

- **Command:** `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b`.
- **Result:** 188 FAIL, 103 WARN over 286 files. The base gives 190 FAIL, 103 WARN over 286 files.
- **No new FAIL** (`lint-diff.txt`).
  - The two facade FAILs `Encryption.lean`/`PublicKey.lean` "does not import child module
    `BitwiseCPA.Eager`" disappeared with `Eager`.
  - The only other difference is the ElGamal size WARN, now 1829 lines instead of 1835.

## 10. Grep receipts (`evidence/grep-receipts.txt`)

- **The searches.** One search per item over `TCSlib` and `audits` at the base, with every hit:
  - 33 searches, 1120 lines;
  - groups P1–P4, S1–S3, H1, A1–A6, R1–R7, L, O1 and O2.
- **Further copies found by these searches.**
  - Folded: `GI.getD_eq_headD_drop` into L1, and ElGamal's `dlc_ofFn_padFin` into A1.
  - Recorded: everything else, in §11.
- `audits/` uses none of the moved names.

## 11. Further duplication found (recorded, not folded)

- **The generic window of a block** has several further forms.
  - `OneWay.ofFn_block_eq_take_drop` (`Asymptotic/OneWayLemmas.lean`) states the A5 fact for
    `fun j => x (finProdFinEquiv (i, j))`. That function is `FunFamily.blocks q ℓ x i` only up to
    unfolding, so its users' `rw`s could not be re-pointed by name.
  - `EnsembleLemmas.take_drop_ofFn_blocks` is the A5 fact reversed, for the `blocks` alias in
    `EnsemblesLemmas`, which is out of scope.
  - `take_drop_ofFn_blocks` (`Encryption/PrivateKey/FromPRF/ReductionMachine.lean`, public) is
    derived from the EnsemblesLemmas one.
  - Local `have`s in `Candidates/Factoring.lean` (`fac_ofFn_halves`) and Primality's private
    `ofFn_chunk` restate it.
- **`ofFn_arrowCongr_finCongr`** has further copies:
  - the private `ofFn_arrowCongr` in `Asymptotic/UniversalPadding.lean`;
  - local `hofn` haves in `Candidates/Factoring.lean` and `ZeroKnowledge/ThreeColoring/ColZKMachine.lean`.
- **`EnsembleLemmas.padL_eq`** is `ofFn_padFin_eq_take` (`CollectionsLemmas`) read through `padL`.
- **The local `hA`/`hB` haves in `EncryptThenTag.lean`** restate A1 through `ofFn_padFin_of_le`.
- **BitwiseCPA/Planted.** `plantTuple` re-implements the `hybridPre` layout (`HybridMachine`), with a
  different input layout. This is for R2.
- **`AdaptiveCPA`'s private `rFwd` and `PRFGame`'s private `rY` are one reader**:
  `pairSndD (pairSndD (pairFstD (rL w)))`, the answer of the first entry of the outer log. They are
  not folded, because they are not among the listed R6 readers: a published version reads the
  outer codec's log encoding, not `InteractiveHandler.input`, so it would need its own reader on
  `encodeLog [⟨j, x, y⟩]`.
- **`PRFGame`'s private `impl_of_query`** (one outer query, then return) has an inline counterpart
  in `AdaptiveCPA.acHandler_impl_forward`. It is a candidate for a generic
  `InteractiveHandler.impl_of_query`, beside the published `impl_of_ret`.
- **PublicKey/OracleSecurity's private `ofFn_splitHalf_bit`** is the one-bit case of BitwiseCPA's
  private `ofFn_half`. Both are private, in files of different chapters, and outside the listed
  items.
- **`AdaptiveCPA`'s `fields_input` and `PRFGame`'s `fields_input`** (both private) have the same
  structure: the published readers on the handler's own state encoding. They differ in the state
  layout, so they are not copies.

## 12. Checkpoints

- **Checkpoint 1** (`rebuild-cp1.log`). 245/245 modules from `Games/Simulate`, status 0. 17 modules
  and 29 sorries, as at the base. Non-sorry warnings 61 = 61.
- **Checkpoint 2** (`rebuild-cp2.log`). 375/375 modules from `Asymptotic/Adversary`, status 0.
  19 modules and 31 sorries, as at the base. Non-sorry warnings 113 = 113.
- **Checkpoint 3** (`rebuild-cp3.log`). 252/252 modules from `Encryption/PublicKey/HybridMachine`,
  status 0. 17 modules and 29 sorries, as at the base. Non-sorry warnings 62 = 62.
- **After checkpoint 3** (`6917e5716`). The fresh sweep (§8) covers it.

## 13. Evidence index

- `evidence/logs/`:
  - setup: `preflight`, `source-sha256`, `package-sha256`, `mathlib-roots`, `cache-*`,
    `packages-check`;
  - bootstrap: `bootstrap`, `sorry-census-bootstrap`;
  - rebuilds and orders: `rebuild-cp{1,2,3}` with lists, `order-cp{1,2,3}`, `order-final`;
  - the base tree: `base-tree`;
  - the fresh sweep: `sweep-final`, `sorry-census-final.txt`;
  - census: `decl-dump-base.log`, `decl-dump-base-ext.log`, `decl-dump-final.log`, `census.txt`,
    `namemap-check.txt`;
  - seals: `seal-{final,base}{,-evalopen}.jsonl/.out`, `seal-compare.txt`, `seal-controls-*.log`;
  - unfold scans: `rwids-{final,base}.{log,tsv}`, `rwids-compare.txt`;
  - lint: `lint-{base,cp1,cp2,cp3,final}.log`;
  - the final head: `final-head.txt`.
- `evidence/seal/`: the sealed copies, the controls, the dump sources and the scan modules.
- `evidence/tools/`: every script used.
- `evidence/grep-receipts.txt`.
- `patches/`: `git format-patch b96ab3ccc..6917e5716`, 4 patches.
- `src/`: the 36 final files.

**Final payload delivered — ready for maintainer review and the gate**

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

## ===== briefs/pass-shelat-ch5-8/fills/dl-consolidation/issued-r1/brief.md =====

# Claude job · duplication consolidation DL-30 to DL-34 (`dl-consolidation`)

**Issue base** `b96ab3ccc1915497ea3138df499eec00b6581db0` on `cryptography/pass-shelat-ch2-4` (the merge of #293).
**Unit** `dl-consolidation`. **Worker** Claude (standing ruling, 2026-11-11). **Lean** 4.25.0 and the Mathlib
revision in that commit's `lake-manifest.json`.

This job repays the duplication debt that Seyoon accepted during the four CPA-pilot fills and the private-key
CPA/CCA1 fill. The debt is recorded as rows DL-30 to DL-34 of `briefs/pass-shelat-ch5-8/duplication-ledger.md`.
Read those five rows first.

The job is a **refactor with no mathematical change**:
- promote each generic lemma to its shared home;
- delete the copies;
- re-point every use.

No audited statement changes.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/dl-consolidation` at the exact issue base,
  and record the base in `REPORT.md`. Keep the branch local.
- Read `policy.md` (§1 file layout, Rule 10 and abbreviations; §3 docstrings), the attached environment addendum
  and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/dl-consolidation/` on
  `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `src/`: every changed or new file;
  - `evidence/`.
- Commit as `fill dl-consolidation: checkpoint N` and `fill dl-consolidation: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land by
  a maintainer PR for Seyoon's approval.

## The items

Paths are relative to `TCSlib/Cryptography/`. **Grep first:** for every item, search the whole library at the
base for further copies under other names, including private ones. List each copy you find, then fold it in or
record why not. One case is known: the private `dlc_ofFn_padFin` in `Encryption/PublicKey/ElGamal.lean` belongs
to DL-31, and the public `Collection.ofFn_padFin_of_le` may already cover it.

### P · `Games/Probability.lean` (namespace `Games.ProbComp`)

| Item | Now | Action |
|---|---|---|
| P1 | `ChallengeSim.expect_sample_equiv`, `expect_sample_comm`, `expect_sample_unique`, `expect_sub` (`Encryption/PublicKey/OracleSecurity/ChallengeSim.lean`; DL-30) | Promote all four. |
| P2 | `ChallengeSim.expect_sample_prod` (DL-30) | If it is `Bridge.expect_sample_pair` restated, delete it and re-point its uses. Otherwise keep it in ChallengeSim. |
| P3 | `expect_sample_update`, in two forms with the same name: `AdaptiveCPA` (`Encryption/PublicKey/AdaptiveCPA/Hybrid.lean`) and `BitwiseSim` (`Encryption/PublicKey/BitwiseCPA/Eager.lean`) (DL-32/33) | Promote one general form, deriving the other from it if both shapes are needed. Distinct names are required. |
| P4 | `PRFGame.abs_expect_sub_le` (`Encryption/PrivateKey/OracleFromPRF/Collision.lean`; DL-34) | Promote. |

### S · `Games/Simulate.lean`, or the lowest Games module whose imports cover the statement

| Item | Now | Action |
|---|---|---|
| S1 | `AdaptiveCPA.simulate_eq_of_abs` (Hybrid) and its generalization `PRFGame.simulate_eq_of_abs_bounded` (`OracleFromPRF/Reduction.lean`) | Promote the bounded form. Derive the other from it, or re-point its uses and delete it. |
| S2 | The `castImpl` family (`AdaptiveCPA/Hybrid.lean`) | Promote with its readers. |
| S3 | `PRFGame.expect_simulate_congr` (`OracleFromPRF/Games.lean`), `BitwiseSim.expect_simulate_eager` (Eager) | Promote. |

### H · `Games/Hopping.lean` (namespace `Games.ProbComp`)

| Item | Now | Action |
|---|---|---|
| H1 | `PRFGame.prob_bad_le`, `PRFGame.expect_sample_mem_le` (Collision) | Promote. `prob_bad_le` is the per-query potential bound, `Pr[bad] ≤ q·(size + q)·δ`. |

### A · beside `padFin`, `decodeFin` and `FunFamily.blocks` (`Asymptotic/Adversary.lean`), or `Games/BitCodec.lean`

| Item | Now | Action |
|---|---|---|
| A1 | `ofFn_padFin_of_length`: `GGMRed` public in `Pseudorandom/Functions/Asymptotic/GGM/Run.lean`, copy in `Asymptotic/HardCoreGLColl.lean`, ElGamal's private copy (DL-31) | Promote one public lemma, or reuse `Collection.ofFn_padFin_of_le` if it subsumes it. Delete all copies. |
| A2 | `ofFn_cast` (public, `AdaptiveCPA/Games.lean`), private `cca2OfFn_cast` (`Encryption/PrivateKey/OracleFromPRF.lean`) (DL-32) | Promote one. |
| A3 | `padFin_ofFn_zeroBits` (`AdaptiveCPA/Games`), `padFin_nil`, `padFin_replicate_false`, `ofFn_arrowCongr_finCongr` (`OracleFromPRF/Transfer.lean`) | Promote beside `padFin`. |
| A4 | Private `ofFn_padFin_eq_padL` in both `AdaptiveCPA/Handler.lean` and `OracleFromPRF/Handler.lean` | Promote one public lemma beside `padL` (`Asymptotic/EnsemblesLemmas.lean`). |
| A5 | `AdaptiveCPA.ofFn_acTapes` and its re-proof `PRFGame.ofFn_pkTapes` (DL-34) | Add the generic `List.ofFn (blocks q ℓ ω j) = ((List.ofFn ω).drop (j·ℓ)).take ℓ` beside `FunFamily.blocks`. Derive both from it. |
| A6 | `BitwiseSim.decodeFin_nil_getD` (`BitwiseCPA/QueryHandler.lean`) | Promote beside `decodeFin`, or into `Games/BitCodec.lean`. |

### R · published readers beside their definitions

| Item | Now | Action |
|---|---|---|
| R1 | `indCodec_eq_bitCodec`, public-key in `AdaptiveCPA/Games` and private-key in `OracleFromPRF/Transfer` (DL-32/34 reader requests) | Publish one reader in `Encryption/PublicKey/OracleSecurity.lean` and one in `Encryption/PrivateKey/OracleSecurity.lean`. Delete the helper copies. |
| R2 | Reader request `hybridPre_eq` (DL-33) | Add it beside `hybridPre` in `Encryption/PublicKey/HybridMachine.lean`. Re-point BitwiseCPA's reading of `hybridPre`. |
| R3 | `BitwiseSim.expect_simulate_indImpl_cpa`, a public near-copy of the private lemma in `Encryption/PublicKey/OracleSecurity.lean` | Publish the OracleSecurity lemma under that name, with a docstring. Delete the copy. |
| R4 | `BitwiseSim.padded_enc_runAt`, `_coins` (Eager) | Move beside the padded readers in `Encryption/PublicKey/OracleSecurity.lean`. |
| R5 | `chRun_toCompOn_transport_list` (QueryHandler), which generalizes `ChallengeSim.chRun_toCompOn_transport` | Move the general form into ChallengeSim and derive the old lemma from it. Keep the old name and statement. |
| R6 | Private round-input readers `rU`…`rCnt`, `impl_of_ret` and `replicate_one`, in both `AdaptiveCPA/Handler.lean` and `OracleFromPRF/Handler.lean` (DL-34) | Publish one set beside `InteractiveHandler.input` in `Games/Efficiency.lean` (or in `List`, for `replicate_one`, if core lacks it). Delete both copies. |
| R7 | Length vectors `recDin/recDout` (`OracleSecurity/RecordHandler.lean`), `acDin/acDout` (`AdaptiveCPA/Handler`), `qDin/qDout` (QueryHandler) | If they are one function up to parameters, publish one and re-point. Otherwise record "not a copy" with the reason. |

### L · a shared list and vector module

Create one new module, `Foundations/BitLists.lean`. It imports Mathlib only, unless an existing upstream module
fits better; check this first and justify your choice. Promote into it:
- `headD_drop`: `BitwiseSim` (`BitwiseCPA/Planted.lean`) copies the public `CommitmentLemmas.headD_drop`, and
  `Pseudorandom/NextBit.lean` has the private `headD_drop_ofFn`. Keep one public lemma and delete the others.
- `flatten_ofFn_singleton` (Planted), with the private `flatten_ofFn_one` (`SecureComputation/Yao.lean`).
- `headD_ofFn_one` (`AdaptiveCPA/Games`).
- `zipWith_xor_cancel_left` (`OracleFromPRF/Lazy.lean`).
- `xorPerm`, with `_apply` (`OracleFromPRF/Collision.lean`). `ctOf_xorPerm` stays.
- `mem_keys_of_lookup_isSome` (Collision): replace it with core's or Batteries' `List.lookup_isSome_iff`, or the
  equivalent at the pin, if one exists. Otherwise promote it.

`ofFn_splitHalf_fst/_snd` (`AdaptiveCPA/Games`) read `splitHalf`. Move them beside `splitHalf` in
`Encryption/PrivateKey/OracleSecurity.lean` as readers.

### O · leftovers in the owned files

| Item | Now | Action |
|---|---|---|
| O1 | Private `ofFn_half` and `bitwise_runAtL` (`Encryption/PublicKey/BitwiseCPA.lean`) re-prove published facts (DL-33) | Use the published ones. |
| O2 | Private overlaps between `PRFStep` and the `cca2*` helpers in `Encryption/PrivateKey/OracleFromPRF.lean` | Merge them. |

## Rules

- **No statement changes.** No existing declaration other than the listed copies may change its statement,
  name, attributes or visibility. The exceptions are the listed publications (R1–R6, a private lemma made
  public) and the promoted lemmas, which get their new names. All proofs elsewhere stay unchanged except for
  re-pointed lemma names. Each gate-audited theorem keeps its statement byte for byte.
- **Deleting copies.** Delete them; no deprecated aliases (precedent: #192). Re-point every use in the library,
  `audits/` included.
- **Names.** Choose names in the home namespace (for example `Games.ProbComp.expect_sample_equiv`, `padFin_nil`).
  The report's census maps every old name to its new name.
- **Docstrings.** Public promoted lemmas keep or gain a formula docstring, and a sketch when nontrivial (policy §3).
  Generic lemmas need no [PS10] tag. Update every module docstring's `## Contents` or main-results list that
  names a moved declaration.
- **Imports.** You may add imports to consumer files. An import added to an existing Games, Asymptotic or
  Foundations module must be acyclic and listed in the report with its reason. Do not create a cycle. Do not
  import a downstream module to reach a lemma.
- **Rule 10.** A promoted lemma reads only definitions of its new home file, through their bodies, or other
  files' definitions through published readers. Where a lemma's proof read its old file's definitions, rewrite it
  through readers or stop (see Escalation). Generated matchers and projections count.
- **Simp.** Add no `@[simp]` and do not change global simp sets.
- **Size.** Keep every file below 1000 lines.
- **Out of scope.**
  - Every file outside `TCSlib/Cryptography/`, except `audits/` uses.
  - Notably the Arora–Barak files (`TCSlib/Complexity/…`), and other campaigns' files.
  - The duplicate `blocks` in `Asymptotic/EnsemblesLemmas.lean` and the private `blocks` in
    `Asymptotic/Ensembles.lean`: record them, but do not fold them.
- **Escalation.** An item may not be promotable without a Rule-10 violation, an import cycle or a statement
  change. If so, leave it, record the exact obstruction and the smallest correction, and continue. A checkpoint
  must still compile.

## Checkpoints

1. Groups P, S, H (Games layer).
2. Groups A, L (padFin, blocks, the list module).
3. Groups R, O.

Send the final delivery with full evidence.

## Checks and report

- **Bootstrap and sweep.** Bootstrap from `order.txt` (406 modules) and the narrow `roots.txt` per the addendum,
  one module per `scripts/lean_check_tree.sh` call, one Lean process per olean tree. Insert any new module before
  its first consumer, and recompute the order if imports change.
  - At each checkpoint, rebuild every edited module and everything after it in the order.
  - At the final delivery, run a full fresh sweep with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt`: there must be **no change** (48 in 26 modules).
- **Census.** Compare all declarations of the changed files, base against final, by name, type and attributes.
  Report:
  - removed (the listed copies only);
  - added (the promoted lemmas, readers and new module);
  - changed (expected 0, apart from listed visibility changes);
  - the old → new name map.
- **Axioms.** Print the axioms of:
  - every stored constant of every changed or new file;
  - the campaign endpoints: `prfFixedScheme_cpa`, `prfFixedScheme_cca1`, `not_prfFixedScheme_cca2`,
    `INDSecure.adaptive_cpa`, `bitwise_padded_cpa`, `exists_adaptive_cpa`, `padded_cpa`, and both
    `Implications.PublicKey` entries.

  Expect only `propext`, `Classical.choice` and `Quot.sound`, as at the base. List any constant that changed
  axioms.
- **Rule 10 evidence.**
  - Run whole-file seals of every changed or new file over its full TCSlib import closure, with base controls,
    and paired controls that pass unsealed and fail sealed.
  - Run the explicit-unfold scan of every changed file.
  - The Gate 17 audit's `PolyExpr.eval` remark applies: report the seal with and without it sealed.
- **Lint.** Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b`. Allow no new FAIL
  versus the base.
- **Grep receipts.** For each item, give the search you ran for further copies and the hits.
- **Report.** Give:
  - the base, the per-item disposition (done / not a copy / escalated);
  - changed and new files with line counts;
  - the import changes;
  - the census and name map;
  - the evidence;
  - the new duplication found.

The maintainer checks `TCSlib` and `audits/pass-shelat/Checks` on the full-library tree at landing.

**Ready to dispatch**

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
| DL-30 | padded-cpa fill (delivery review 2026-11-11): generic `ProbComp` facts published in a public-key helper as `Composability.ChallengeSim.expect_sample_equiv`, `expect_sample_comm`, `expect_sample_unique`, `expect_sub` (`PublicKey/OracleSecurity/ChallengeSim.lean`); `expect_sample_prod` repeated `Bridge.expect_sample_pair`'s proof. | `ChallengeSim.lean` only | Open (deferred) | Landing edit re-proved `expect_sample_prod` from `Bridge.expect_sample_pair`. Promote the four lemmas to `ProbComp` in `Games/Probability.lean` and re-point their uses. |
| DL-31 | `ofFn_padFin_of_length` (`List.ofFn (padFin d w) = w` when `w.length = d`): `GGMRed.ofFn_padFin_of_length` (`GGM/Run.lean`), copy in `Asymptotic/HardCoreGLColl.lean`, private copy in `ElGamal.lean`; padded-cpa's `RecordHandler.lean` uses the GGM one through a transitive import. | 3 | Open (deferred) | Promote one public lemma beside `padFin` in `Asymptotic/Adversary.lean`; re-point all uses and delete the copies. |
| DL-32 | `List.ofFn (cast h f) = List.ofFn f` for a width equality: public `Composability.AdaptiveCPA.ofFn_cast` (`PublicKey/AdaptiveCPA/Games.lean`) and private `cca2OfFn_cast` (`PrivateKey/OracleFromPRF.lean`, #289). adaptive-cpa review also lists for promotion: `expect_sample_update` (→ `Games/Probability.lean`, with DL-30), `simulate_eq_of_abs` and the `castImpl` family (→ `Games/Simulate.lean`), `padFin_ofFn_zeroBits`, `headD_ofFn_one`, `ofFn_splitHalf_fst/_snd`; reader request `indCodec_eq_bitCodec`; new uses of `GGMRed.ofFn_padFin_of_length` join DL-31. | 2 (+ candidates) | Open (deferred) | Promote one generic `ofFn_cast` beside `padFin`/`BitCodec`; re-point both; promote the listed generic lemmas. |
| DL-33 | bitwise-cpa fill (delivery review 2026-11-11): `BitwiseSim.expect_sample_update` vs `AdaptiveCPA.expect_sample_update` (two forms, same name); generic `BitwiseSim.expect_simulate_eager` and public near-copy `BitwiseSim.expect_simulate_indImpl_cpa` of the private lemma in `PublicKey/OracleSecurity.lean`; `chRun_toCompOn_transport_list` generalizes `ChallengeSim.chRun_toCompOn_transport`; `BitwiseSim.headD_drop` = public `CommitmentLemmas.headD_drop` (and private `headD_drop_ofFn` in `Pseudorandom/NextBit.lean`); `flatten_ofFn_singleton` = private `flatten_ofFn_one` (`Yao.lean`); `decodeFin_nil_getD` (→ `Games/BitCodec`); `padded_enc_runAt/_coins` (→ beside the padded readers); `qDin/qDout` third copy of the two-oracle length vector (`recDin/recDout`, `acDin/acDout`); private `ofFn_half`, `bitwise_runAtL` re-prove published facts; reader request `HybridMachine.hybridPre_eq`. | several | Open (deferred) | One consolidation PR with DL-30–DL-32: promote to `Games/Probability`, `Games/Simulate`, `ChallengeSim`, `BitCodec`, a shared list module; re-point and delete copies. |
| DL-34 | pk-cpa-cca1 fill (delivery review 2026-11-12): `OracleFromPRF/Handler.lean` copies private AdaptiveCPA handler pieces (`ofFn_padFin_eq_padL`, round-input readers `rU`…`rCnt`, `impl_of_ret`, `replicate_one`); public `ofFn_pkTapes` re-proves `AdaptiveCPA.ofFn_acTapes` (a generic `⟦blocks q ℓ ω j⟧ = (⟦ω⟧.drop (j·ℓ)).take ℓ` belongs beside `FunFamily.blocks`, input-layout readers beside `InteractiveHandler.input`); private-key `indCodec_eq_bitCodec` (DL-32 reader request); `mem_keys_of_lookup_isSome` (core `List.lookup_isSome_iff`); promotion candidates `simulate_eq_of_abs_bounded` (generalizes `AdaptiveCPA.simulate_eq_of_abs`), `expect_simulate_congr` (→ `Games/Simulate`), `abs_expect_sub_le` (→ `Games/Probability`), `prob_bad_le`, `expect_sample_mem_le` (→ `Games/Hopping`), `padFin_nil`, `padFin_replicate_false`, `ofFn_arrowCongr_finCongr` (→ beside `padFin`), `zipWith_xor_cancel_left`, `xorPerm` (shared list/vector module); owned-file private overlaps with the `cca2*` helpers. | several | Open (deferred) | Fold into the DL-30–DL-34 consolidation PR. |
| DL-35 | Found while staging the consolidation (2026-11-12): public `blocks` in `Asymptotic/EnsemblesLemmas.lean` and private `blocks` in `Asymptotic/Ensembles.lean`, both the equivalence `(Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool)` of `FunFamily.blocks` (`Asymptotic/Adversary.lean`). | 2 | Open (ch. 2–4 inherited) | Re-point to `FunFamily.blocks` in a later ch. 2–4 cleanup; out of scope for `dl-consolidation`. |
| DL-36 | nm-cca2 fill (delivery review 2026-11-12): `NMCCA2.logEmit` (`PublicKey/NonMalleability/Indistinguishability/Forward.lean`) generalizes `Games.EffFill.relabelN`/`relabel` (`Games/Efficiency/OracleBridge.lean`), and its log facts `logEmit_encodeLog`, `iterate_pairSndD_encodeLog`, `flatMap_range_drop`, `length_le_length_encodeLog`, `length_iterate_pairSndD_le`, `polyTimeComputable_logEmit` mirror `relabelN_encodeHist`, `length_le_length_encodeHist` and the orbit bound of `bridgePre_poly` (undisclosed); public `finU`, `finZ`, `finW`, `finA`, `finL`, `fields_finInput` are the DL-34 round-input readers (`rU`…`rL`) again; `ofFn_nthCt` (owned file) is DL-34's generic block fact (`ofFn_acTapes`, `ofFn_pkTapes`); the private readers `rState`…`rAns` (disclosed). Promotion requests: `fwdHandler`/`fwdHandler_impl`, `exists_withAdviceOn` (→ `Games/Efficiency`), `cntRead`/`ansRead` (→ `BitCodec`), `indImpl_eq_of_msgLen_eq_zero` (→ `PublicKey/OracleSecurity`, after that file is split: it is at 999 lines). | several | Open (deferred) | After the DL-30–DL-34 consolidation lands: put `logEmit` beside `relabelN` with `relabel x = logEmit relabelEmit x`; re-point `dCnt`/`dCt`/`dIn`/`dFin`/`eBit`/`eMsg`/`eTape`/`eCt` to R6's readers and delete `finU`…`fields_finInput`; derive `ofFn_nthCt` from the generic block lemma; promote the accepted requests. |
| DL-37 | nm-sim fill (delivery review 2026-11-13; **undisclosed**, accepted as debt by Seyoon 2026-11-13): `NMSim.chunkAt`/`chunkAt_eq`/`length_chunkAt` (`PublicKey/NonMalleability/Simulation/Hybrid.lean`) and the block lemmas `ofFn_block`, `chunkAt_flatten_append`, `map_chunkAt_flatten`; private `padFin_replicate_false` (`Simulation/Challenge.lean`); `Rounds.impl_of_ret`, `rdU`…`rdLog`/`rdState`, `rdAns`, `Simulator.finSt` (`Simulation/Rounds.lean`, `Simulator.lean`); also generic neighbours `expect_eq_until_bad`, `NMSim.expect_simulate_eager`, `expect_congr_of_allOutputs`, `chunkMap`; disclosed: `flatMap_range_drop`, `ofFn_padFin_eq_padL`, `polyTimeComputable_guessBit`, `ofFn_eq_map_range` | `coinBlock`/`coinBlock_eq`/`length_coinBlock` (`Asymptotic/Adversary.lean`), `OneWayLemmas.ofFn_block_eq_take_drop`, `NMCCA2.ofFn_nthCt`, Lamport `coinBlock_flatten`; `PRFGame.padFin_replicate_false` (`OracleFromPRF/Transfer.lean`; → `Games.padFin_replicate_false` in the consolidation); DL-34 private `impl_of_ret` (`AdaptiveCPA/Handler.lean`, `PRFGame`) and readers `rU`…`rL`/`rS`; `Games.prob_eq_until_bad`, `BitwiseSim.expect_simulate_eager`, `ProbComp.expect_mono_of_allOutputs`, `relabelN`/`logEmit` (DL-36); ZK `ofFn_eq_map_range` ×2; A4 `EnsembleLemmas.ofFn_padFin_eq_padL`; `rFwd`/`rY`/Forward `rAns` | Open (deferred; first item paid at the consolidation landing, LE-repoint-nmsim `6f853adc`) | Landing of the consolidation (after nm-sim): delete the private `padFin_replicate_false` and use `Games.padFin_replicate_false`; re-point the nm-sim files to the moved names. Post-consolidation fold window, with DL-36: fold `chunkAt` onto `coinBlock` (58 uses) and place the block lemmas beside it; re-point `rdU`…`rdLog`, `rdState`, `finSt` to `InteractiveHandler.rU`…`rS` and `impl_of_ret` to `InteractiveHandler.impl_of_ret`; derive `prob_eq_until_bad` and `ChallengeSim.expect_simulate_eager` from the general nm-sim forms; one iterate-and-emit definition for `relabelN`/`logEmit`/`chunkMap`; merge the three `ofFn_eq_map_range` into `Foundations/BitLists`; make `NMSim.ofFn_padFin_eq_padL` the A4 lemma; fold `rdAns` with the `rFwd`/`rY`/`rAns` readers; promote the accepted requests (review r1 table). |

## ===== briefs/pass-shelat-ch5-8/gates/20-dl-consolidation/pr.diff.txt =====

diff --git a/TCSlib/Cryptography/Asymptotic/Adversary.lean b/TCSlib/Cryptography/Asymptotic/Adversary.lean
index da68fc408..4f1e84a21 100644
--- a/TCSlib/Cryptography/Asymptotic/Adversary.lean
+++ b/TCSlib/Cryptography/Asymptotic/Adversary.lean
@@ -62,7 +62,11 @@ by `ifEq`).
   equation and its full-length condition.
 * `TCSlib.Cryptography.decodeFin_ofFn`, `TCSlib.Cryptography.padFin_ofFn` — decoding and
   padding invert `List.ofFn`; `TCSlib.Cryptography.decodeFin_eq_some_iff` — decoding succeeds
-  exactly on the encoding.
+  exactly on the encoding; `TCSlib.Cryptography.ofFn_padFin_of_length` — padding a string of the
+  right length keeps it.
+* `TCSlib.Cryptography.ofFn_cast`, `TCSlib.Cryptography.ofFn_arrowCongr_finCongr` — a bit vector
+  read across an equality of widths keeps its string.
+* `TCSlib.Cryptography.FunFamily.ofFn_blocks` — block `j` of a string is its `j`-th window.
 * `TCSlib.Cryptography.invProbOpt_le_invProb`, `TCSlib.Cryptography.invProbOpt_some` — the
   bridges to the concrete `invProb`.
 * `TCSlib.Cryptography.invProbOpt_nonneg`, `TCSlib.Cryptography.invProbOpt_le_one` — bounds.
@@ -153,6 +157,28 @@ theorem padFin_ofFn {ℓ : ℕ} (x : Fin ℓ → Bool) : padFin ℓ (List.ofFn x
   funext i
   simp [padFin]
 
+/-- The encoding of `padFin L w` is `w` when `|w| = L`: `List.ofFn (padFin L w) = w`. -/
+theorem ofFn_padFin_of_length {L : ℕ} {w : List Bool} (hw : w.length = L) :
+    List.ofFn (padFin L w) = w := by
+  refine List.ext_getElem (by simp [hw]) fun j hj₁ hj₂ => ?_
+  simp [padFin_def, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj₂]
+
+/-! ### Bit vectors across equal widths -/
+
+/-- Reading a bit vector across an equality of widths keeps its string:
+`⟦cast h f⟧ = ⟦f⟧` when `a = b`. -/
+theorem ofFn_cast {a b : ℕ} (hab : a = b) (h : (Fin a → Bool) = (Fin b → Bool))
+    (f : Fin a → Bool) : List.ofFn (cast h f) = List.ofFn f := by
+  subst hab
+  rfl
+
+/-- Reading a vector at an equal width keeps its word:
+`⟦(arrowCongr (finCongr h) (refl Bool)) v⟧ = ⟦v⟧`. -/
+theorem ofFn_arrowCongr_finCongr {a b : ℕ} (h : a = b) (v : Fin a → Bool) :
+    List.ofFn ((Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)) v) = List.ofFn v := by
+  subst h
+  rfl
+
 /-! ### Blocks of a flat tuple -/
 
 /-- A tuple of `q · ℓ` entries with values in an arbitrary type `X` as `q` consecutive blocks of
@@ -187,6 +213,30 @@ theorem FunFamily.blocks_symm_apply (q ℓ : ℕ) (t : Fin q → Fin ℓ → Boo
     (FunFamily.blocks q ℓ).symm t k = t k.divNat k.modNat :=
   blocksEquivX_symm_apply q ℓ t k
 
+/-- **Block `j` is the `j`-th window of the string:**
+`⟦FunFamily.blocks q ℓ ω j⟧ = (⟦ω⟧.drop (j·ℓ)).take ℓ`.
+
+**Proof sketch.** Block `j` ends within the string, `j·ℓ + ℓ ≤ q·ℓ`, so both sides have `ℓ` bits.
+Position `k` of block `j` is position `finProdFinEquiv (j, k) = k + ℓ·j` of `ω`
+(`FunFamily.blocks_apply`), which is position `k` of the window. -/
+theorem FunFamily.ofFn_blocks (q ℓ : ℕ) (ω : Fin (q * ℓ) → Bool) (j : Fin q) :
+    List.ofFn (FunFamily.blocks q ℓ ω j) = ((List.ofFn ω).drop (j * ℓ)).take ℓ := by
+  have hle : (j : ℕ) * ℓ + ℓ ≤ q * ℓ := by
+    have := Nat.mul_le_mul_right ℓ (Nat.succ_le_of_lt j.isLt)
+    rw [Nat.succ_mul] at this
+    exact this
+  refine List.ext_getElem ?_ fun k h₁ h₂ => ?_
+  · simp only [List.length_ofFn, List.length_take, List.length_drop]
+    omega
+  · rw [List.getElem_ofFn, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
+    refine (FunFamily.blocks_apply q ℓ ω j ⟨k, _⟩).trans ?_
+    congr 1
+    refine Fin.ext ?_
+    rw [finProdFinEquiv_apply_val]
+    show k + ℓ * j = j * ℓ + k
+    rw [Nat.mul_comm]
+    omega
+
 /-- `A(1^n, y)` as an inverter: output decoded as an `ℓ`-bit string, wrong length = failure
 [PS10, Definitions 27.3 and 28.4, the experiment `f(A(1^n, y)) = y`].
 
diff --git a/TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean b/TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean
index 5a392edfb..710088b0d 100644
--- a/TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean
+++ b/TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean
@@ -56,6 +56,8 @@ part of the public API of the campaign.
   by exactly distributed polynomial-time samplers.
 * `TCSlib.Cryptography.EnsembleLemmas.negligible_polyExpr_mul` — a syntactic polynomial
   times a negligible function is negligible.
+* `TCSlib.Cryptography.EnsembleLemmas.ofFn_padFin_eq_padL` — the string of a padded vector is
+  `padL`.
 
 ## References
 
@@ -161,6 +163,9 @@ def padL (k : ℕ) (a : List Bool) : List Bool := List.ofFn (padFin k a)
 /-- `padL` has exactly `k` bits. -/
 theorem length_padL (k : ℕ) (a : List Bool) : (padL k a).length = k := List.length_ofFn
 
+/-- The string of a padded vector is `padL`: `⟦padFin k a⟧ = padL k a`. -/
+theorem ofFn_padFin_eq_padL (k : ℕ) (a : List Bool) : List.ofFn (padFin k a) = padL k a := rfl
+
 /-- `padL k a` is the first `k` bits of `a ++ 0^k`. -/
 theorem padL_eq (k : ℕ) (a : List Bool) : padL k a = (a ++ List.replicate k false).take k := by
   refine List.ext_getElem ?_ fun i h₁ h₂ => ?_
diff --git a/TCSlib/Cryptography/Asymptotic/HardCoreGLColl.lean b/TCSlib/Cryptography/Asymptotic/HardCoreGLColl.lean
index dd6cd5cd9..fa812959c 100644
--- a/TCSlib/Cryptography/Asymptotic/HardCoreGLColl.lean
+++ b/TCSlib/Cryptography/Asymptotic/HardCoreGLColl.lean
@@ -130,12 +130,6 @@ theorem padToLen_pairEncode_ofFn (a : List Bool) {L : ℕ} (ρ : Fin L → Bool)
       Bool.xor_self]
     rfl
 
-/-- The encoding of `padFin L w` is `w` when `|w| = L`. -/
-theorem ofFn_padFin_of_length {L : ℕ} {w : List Bool} (hw : w.length = L) :
-    List.ofFn (padFin L w) = w := by
-  refine List.ext_getElem (by simp [hw]) fun j hj₁ hj₂ => ?_
-  simp [padFin_def, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj₂]
-
 /-- **The evaluator of the hard-core bit of the padded collection** `⟨padFin(encD_i x), r⟩` on
 `⟨i, ⟨encD_i x, r⟩⟩` [PS10, Theorem 87.3, collection form, efficiency clause]. -/
 theorem exists_glBitCollEvaluator (F : Collection) :
diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF.lean b/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF.lean
index 3f0c3fa58..121800016 100644
--- a/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF.lean
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF.lean
@@ -11,6 +11,7 @@ import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Transfer
 import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Lazy
 import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Collision
 import Mathlib.Tactic.Simps.Basic
+import TCSlib.Cryptography.Foundations.BitLists
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -167,7 +168,7 @@ private theorem ofFn_prf_encryptAt (n : ℕ) (k m : Fin n → Bool)
   rw [prfFixedScheme_enc, prfScheme_enc]
   intro re hx
   rw [runAt_prfEnc hE, hx, hFE, ctOf_eq]
-  apply GGMRed.ofFn_padFin_of_length
+  apply ofFn_padFin_of_length
   simp only [length_pairEncode, List.length_ofFn, List.length_zipWith, Nat.min_self,
     PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
   omega
@@ -193,11 +194,11 @@ private theorem ofFn_prf_decAnswer (n : ℕ) (hn : 0 < n) (k : Fin n → Bool) (
       rw [h, List.length_nil] at this
       omega
     have hx : pairFstD w = List.ofFn (padFin n (pairFstD w)) :=
-      (GGMRed.ofFn_padFin_of_length hw.1).symm
+      (ofFn_padFin_of_length hw.1).symm
     have hv : List.zipWith xor (pairSndD w) (List.ofFn (F n k (padFin n (pairFstD w)))) =
         List.ofFn (padFin n (List.zipWith xor (pairSndD w)
           (List.ofFn (F n k (padFin n (pairFstD w)))))) :=
-      (GGMRed.ofFn_padFin_of_length (by
+      (ofFn_padFin_of_length (by
         rw [List.length_zipWith, List.length_ofFn, hw.2, Nat.min_self])).symm
     conv_lhs => rw [eq_pairEncode_of_pairFstD_ne hne]
     rw [runAt_prfDec hE _ n _ _ _ hw.1 hw.2, hx, hFE, ← hx, hv, decodeFin_ofFn,
@@ -240,8 +241,8 @@ reduction's lengths.
 **Proof sketch.** The key generator outputs its uniform coins (`prf_gen_runAt`, `prfKeyEq`); for
 every key, the oracles of `IND_b` and `fImpl … (F n k)` have the same laws call by call
 (`expect_indImpl_fImpl`, from `ofFn_prf_encryptAt` and `ofFn_prf_decAnswer`), so the simulations
-agree (`PRFGame.expect_simulate_congr`); the game's codec and lengths are the reduction's
-(`indCodec_eq_bitCodec`, `prf_inLens`, `prf_outLens`, `prf_ctLen_eval`). -/
+agree (`ProbComp.expect_simulate_congr`); the game's codec and lengths are the reduction's
+(`FixedLengthScheme.indCodec_eq_bitCodec`, `prf_inLens`, `prf_outLens`, `prf_ctLen_eval`). -/
 private theorem accept_prf_indGame (atkBit b : Bool) (A : NUPPT) (Q n : ℕ) (hn : 0 < n) :
     accept ((prfFixedScheme F E hE hFE).indGame (atkOf atkBit) A Q b n) =
       expect (ProbComp.sample (Fin n → Bool)) fun k =>
@@ -266,11 +267,11 @@ private theorem accept_prf_indGame (atkBit b : Bool) (A : NUPPT) (Q n : ℕ) (hn
       Bool) => ProbComp.prob (.pure (res.1 0)) (· = true)) =
       fun res => if (List.ofFn res.1).headD false = true then (1 : ℝ) else 0 := by
     funext res
-    rw [prob_pure, AdaptiveCPA.headD_ofFn_one]
+    rw [prob_pure, headD_ofFn_one]
   rw [h1, expect_simulate_congr _ _ (fun i x s g => expect_indImpl_fImpl _ atkBit b n _ _ hct
       (prfNonceEq F E hE hFE n) (fun m re => ofFn_prf_encryptAt F E hE hFE n _ m re)
       (fun w rd => ofFn_prf_decAnswer F E hE hFE n hn _ w rd) i x s g),
-    indCodec_eq_bitCodec]
+    FixedLengthScheme.indCodec_eq_bitCodec]
   exact expect_fImpl_transport (prf_inLens F E hE hFE n) (prf_outLens F E hE hFE n)
     (prf_ctLen_eval F E hE hFE n) n _ b _ A Q r
 
@@ -404,7 +405,7 @@ challenge bit in its seed. Here there is one reduction per bit (the bit hard-wir
 2. *The random-function experiment* (`PRFGame.abs_expect_fImpl_sub_le`): sample `R` lazily
    (`PRFGame.expect_lazyImpl`). The bad event is that the challenge's `r*` was already asked or
    a later `Enc` uses it; a query raises it with probability at most `(q + 1) / 2ⁿ` (`prob_mem_le`),
-   so it has probability at most `q(n)² / 2ⁿ` (`PRFGame.prob_bad_le`). Off the bad event,
+   so it has probability at most `q(n)² / 2ⁿ` (`ProbComp.prob_bad_le`). Off the bad event,
    `m_b ⊕ R(r*)` is uniform for both `b` (identical until bad, `identical_until_bad`, with the pad
    changed by `y ↦ y ⊕ m₀ ⊕ m₁`).
 3. *The bound* (`prf_advantage_le`, `prf_indSecure`): the triangle inequality gives the bound
@@ -598,25 +599,15 @@ private theorem cca2Adversary_two (n : ℕ) (i x c j y d : List Bool)
   simp only [hn, ite_false, pairFstD_pairEncode, pairSndD_pairEncode]
 
 /-- For every encryption tape there is an `n`-bit nonce `x`; the ciphertext is exactly
-the pair of that nonce and the message masked by `F n k x`. -/
+the pair of that nonce and the message masked by `F n k x` (`ofFn_prf_encryptAt` with the nonce
+`prfNonceEq r`). -/
 private theorem cca2Encrypt (n : ℕ) (k m : Fin n → Bool)
     (r : (prfFixedScheme F E hE hFE).enc.Coins n) :
     ∃ x : Fin n → Bool, List.ofFn r = List.ofFn x ∧
       List.ofFn ((prfFixedScheme F E hE hFE).encryptAt n (List.ofFn k) m r) =
         pairEncode (List.ofFn x) (List.ofFn (m + F n k x)) := by
-  revert r
-  simp only [FixedLengthScheme.encryptAt_eq, prfFixedScheme_ctLen]
-  rw [prfFixedScheme_enc, prfScheme_enc]
-  intro r
-  let x := NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var n r
-  have hx : List.ofFn x = List.ofFn r :=
-    NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn _ _ n r
-  refine ⟨x, hx.symm, ?_⟩
-  rw [runAt_prfEnc hE, ← hx, hFE, zipWith_xor_ofFn_add]
-  apply GGMRed.ofFn_padFin_of_length
-  simp only [length_pairEncode, List.length_ofFn, PolyExpr.eval_add,
-    PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
-  omega
+  refine ⟨prfNonceEq F E hE hFE n r, (ofFn_prfNonceEq F E hE hFE n r).symm, ?_⟩
+  rw [ofFn_prf_encryptAt, PRFGame.ctOf_eq, zipWith_xor_ofFn_add]
 
 /-- The challenge query concatenates the all-false and all-true messages. -/
 private def cca2Messages (n : ℕ) : Fin (n + n) → Bool :=
@@ -650,7 +641,7 @@ private def cca2Alter {d : ℕ} (c : Fin d → Bool) : Fin d → Bool :=
 /-- At positive width the modified ciphertext has exactly the flipped word. -/
 private theorem cca2Alter_ofFn {d : ℕ} (hd : 0 < d) (c : Fin d → Bool) :
     List.ofFn (cca2Alter c) = cca2FlipLast (List.ofFn c) := by
-  apply GGMRed.ofFn_padFin_of_length
+  apply ofFn_padFin_of_length
   rw [cca2FlipLast_length]
   · exact List.length_ofFn
   · intro he
@@ -670,21 +661,10 @@ private theorem cca2Alter_ne {d : ℕ} (hd : 0 < d) (c : Fin d → Bool) :
   simp only [List.length_ofFn, List.length_nil] at hl
   omega
 
-/-- The ciphertext width evaluates to `3 * n + 2`. -/
-private theorem cca2CtLen (n : ℕ) :
-    (prfFixedScheme F E hE hFE).ctLen.eval n = 3 * n + 2 := by
-  rw [prfFixedScheme_ctLen, PolyExpr.eval_add, PolyExpr.eval_mul,
-    PolyExpr.eval_const, PolyExpr.eval_const, PolyExpr.eval_var]
-
-/-- Every generated key is an `n`-bit word. -/
+/-- Every generated key is an `n`-bit word (`prf_gen_runAt`, `ofFn_prfKeyEq`). -/
 private theorem cca2Gen (n : ℕ) (rg : (prfFixedScheme F E hE hFE).gen.Coins n) :
-    ∃ k : Fin n → Bool, (prfFixedScheme F E hE hFE).gen.runAt n [] rg = List.ofFn k := by
-  revert rg
-  rw [prfFixedScheme_gen, prfScheme_gen]
-  intro rg
-  rw [runAt_coinKey]
-  exact ⟨NUPPT.coinsEquiv_ofPolyTimeUniform polyTimeComputable_pairSndD .var n rg,
-    (NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn _ _ n rg).symm⟩
+    ∃ k : Fin n → Bool, (prfFixedScheme F E hE hFE).gen.runAt n [] rg = List.ofFn k :=
+  ⟨prfKeyEq F E hE hFE n rg, by rw [prf_gen_runAt, ofFn_prfKeyEq]⟩
 
 /-- The actual encrypted word is well formed, and its last-bit modification is a
 distinct, well-formed pair with the same nonce and the flipped masked payload. -/
@@ -699,7 +679,7 @@ private theorem cca2Cipher (n : ℕ) (hn : 0 < n) (k m : Fin n → Bool)
         (prfFixedScheme F E hE hFE).encryptAt n (List.ofFn k) m r := by
   obtain ⟨x, -, hc⟩ := cca2Encrypt F E hE hFE n k m r
   have hd : 0 < (prfFixedScheme F E hE hFE).ctLen.eval n := by
-    rw [cca2CtLen]
+    rw [prf_ctLen_eval, PRFGame.ctP_eval]
     omega
   have hp : List.ofFn (m + F n k x) ≠ [] := by
     intro he
@@ -722,13 +702,6 @@ private theorem cca2Decrypt (n : ℕ) (k x v : Fin n → Bool)
   rw [runAt_prfDec hE _ n _ _ _ List.length_ofFn List.length_ofFn, hFE, zipWith_xor_ofFn_add,
     decodeFin_ofFn]
 
-/-- Transporting a bit vector along a width equality does not change its word:
-`List.ofFn (cast h f) = List.ofFn f` when `h` comes from `a = b`. -/
-private theorem cca2OfFn_cast {a b : ℕ} (hab : a = b) (h : (Fin a → Bool) = (Fin b → Bool))
-    (f : Fin a → Bool) : List.ofFn (cast h f) = List.ofFn f := by
-  subst hab
-  rfl
-
 /-- At `n > 0`, the valid answer `⟨1, b^n ⊕ e_{n-1}⟩` ends in `!b`. -/
 private theorem cca2LastBit {n : ℕ} (hn : 0 < n) (b : Bool) :
     (List.ofFn (Fin.cons (α := fun _ => Bool) true (cca2FlipBits (n := n) fun _ => b))).getLastD
@@ -767,7 +740,7 @@ private theorem cca2Run (S : FixedLengthScheme) (n : ℕ) (hd : 0 < S.ctLen.eval
     rw [MachineCodec.encodeLog_nil, cca2Adversary_run, if_pos rfl,
       FixedLengthScheme.indCodec_decodeMove]
     have hw : List.ofFn x = List.replicate n false ++ List.replicate n true := by
-      rw [hx, cca2OfFn_cast (S.inLens_two n).symm, cca2Messages_ofFn]
+      rw [hx, ofFn_cast (S.inLens_two n).symm, cca2Messages_ofFn]
     rw [← hw]
     exact decodeBitMove_query (S.inLens n) (S.outLens n) 1 2 x
   rw [NUPPT.toComp_eq, buildComp_succ_of_query (next := fun hist => (S.indCodec n).decodeMove
@@ -787,8 +760,8 @@ private theorem cca2Run (S : FixedLengthScheme) (n : ℕ) (hd : 0 < S.ctLen.eval
     simp only [MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil,
       FixedLengthScheme.indCodec_encodeEntry, cca2Adversary_one,
       FixedLengthScheme.indCodec_decodeMove]
-    rw [cca2OfFn_cast (S.outLens_two n).symm, ← cca2Alter_ofFn hd,
-      ← cca2OfFn_cast (S.inLens_one n).symm (S.indSpec_decDom n).symm]
+    rw [ofFn_cast (S.outLens_two n).symm, ← cca2Alter_ofFn hd,
+      ← ofFn_cast (S.inLens_one n).symm (S.indSpec_decDom n).symm]
     exact decodeBitMove_query (S.inLens n) (S.outLens n) 1 1 _
   rw [buildComp_succ_of_query (next := fun hist => (S.indCodec n).decodeMove
     (cca2Adversary.runAt n ((S.indCodec n).encodeLog hist) r)) h2, simulate_query,
@@ -818,7 +791,7 @@ private theorem cca2Run (S : FixedLengthScheme) (n : ℕ) (hd : 0 < S.ctLen.eval
     simp only [List.singleton_append, MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil,
       FixedLengthScheme.indCodec_encodeEntry, cca2Adversary_two,
       FixedLengthScheme.indCodec_decodeMove]
-    rw [cca2OfFn_cast (S.outLens_one n).symm, hlast, Bool.not_not]
+    rw [ofFn_cast (S.outLens_one n).symm, hlast, Bool.not_not]
     have hb : [b] = List.ofFn (fun _ : Fin 1 => b) := by
       rw [List.ofFn_const, List.replicate_one]
     rw [hb]
@@ -850,7 +823,7 @@ theorem prfFixedScheme_not_cca2 :
         ((prfFixedScheme F E hE hFE).indGame .cca2 A (q.eval n) true n) = 1 := by
   refine ⟨cca2Adversary, .const 2, fun n hn => ?_⟩
   have hd : 0 < (prfFixedScheme F E hE hFE).ctLen.eval n := by
-    rw [cca2CtLen]
+    rw [prf_ctLen_eval, PRFGame.ctP_eval]
     omega
   have hacc : ∀ b : Bool, accept ((prfFixedScheme F E hE hFE).indGame .cca2 cca2Adversary
       ((PolyExpr.const 2).eval n) b n) = if b = true then 1 else 0 := by
diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Collision.lean b/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Collision.lean
index e942f42fd..7f20a7ee6 100644
--- a/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Collision.lean
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Collision.lean
@@ -4,6 +4,7 @@ Released under Apache 2.0 license as described in the file LICENSE.
 -/
 import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Lazy
 import TCSlib.Cryptography.Games.Hopping
+import TCSlib.Cryptography.Foundations.BitLists
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -26,12 +27,11 @@ queries.
 * *The bad probability.* A query from a good state raises the flag with probability at most
   `(|T| + 1) / 2ⁿ` (`lazyImpl_step`; the first challenge's nonce hits one of the `|T|` points of
   the table, `prob_mem_le`, or an encryption's nonce hits `r*`), and adds at most one point to the
-  table (`lazyImpl_grow`). A potential argument sums these over `q` queries (`prob_bad_le`).
+  table (`lazyImpl_grow`). A potential argument sums these over `q` queries
+  (`ProbComp.prob_bad_le`).
 
 ## Main results
 
-* `PRFGame.prob_bad_le`: a bad event raised with probability at most `(size + 1) · δ` per query,
-  by queries that grow the size by at most one, has probability at most `q · (size + q) · δ`.
 * `PRFGame.lazyImpl_agree`, `lazyImpl_stick`, `lazyImpl_step`, `lazyImpl_grow`.
 * `PRFGame.abs_prob_lazyImpl_sub_le`: the two bits' lazy experiments differ by at most `q² / 2ⁿ`.
 * `PRFGame.abs_expect_fImpl_sub_le`: hence so do the experiments with a uniform random function.
@@ -48,95 +48,6 @@ namespace TCSlib.Cryptography.Composability.PRFGame
 
 open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim
 
-/-! ### A potential bound on a bad event -/
-
-section Potential
-
-variable {ι : Type} {spec : OracleSpec ι} {σ : Type}
-
-/-- **A bad event raised a little at each query:** if from a good state each query raises `bad`
-with probability at most `(sz s + 1) · δ` and grows the size `sz` by at most one, then from a good
-state `s` a computation making at most `m` queries ends in a bad state with probability at most
-`m · (sz s + m) · δ`.
-
-**Proof sketch.** Induction on the computation. At a query, a bad successor contributes at most
-its probability; a good successor `s'` has `sz s' ≤ sz s + 1` and, by induction, contributes at
-most `(m - 1) · (sz s + m) · δ`. Add `(sz s + 1) · δ ≤ (sz s + m) · δ`. -/
-theorem prob_bad_le {impl : QueryImpl spec σ unifSpec} (bad : σ → Prop) [DecidablePred bad]
-    (sz : σ → ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
-    (hstep : ∀ i x s, ¬ bad s → prob (impl i x s) (fun ys => bad ys.2) ≤ (sz s + 1) * δ)
-    (hgrow : ∀ i x s, (impl i x s).AllOutputs fun ys => sz ys.2 ≤ sz s + 1)
-    {α : Type} (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ)
-    (hs : ¬ bad s) :
-    prob (simulate impl c s) (fun r => bad r.2) ≤ m * (sz s + m) * δ := by
-  induction c generalizing m s with
-  | pure a =>
-    rw [simulate_pure, prob_pure, if_neg hs]
-    exact mul_nonneg (by positivity) hδ
-  | query i x k ih =>
-    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
-    have hm1 : 1 ≤ m := hm
-    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
-    have hk' : ∀ y, (k y).CostBoundedBy (fun _ => 1) m' := fun y => by
-      simpa using hk y
-    have hm0 : (0 : ℝ) ≤ m' := Nat.cast_nonneg m'
-    set K : ℝ := m' * (sz s + (m' + 1)) * δ with hK
-    have hK0 : 0 ≤ K := mul_nonneg (by positivity) hδ
-    rw [simulate_query, prob_bind]
-    calc expect (impl i x s) (fun ys => prob (simulate impl (k ys.1) ys.2) (fun r => bad r.2))
-        ≤ expect (impl i x s) (fun ys => (if bad ys.2 then (1 : ℝ) else 0) + K) := by
-          refine expect_mono_of_allOutputs (hgrow i x s) fun ys hys => ?_
-          by_cases hb : bad ys.2
-          · rw [if_pos hb]
-            have h1 := prob_le_one (simulate impl (k ys.1) ys.2) (fun r => bad r.2)
-            linarith
-          · rw [if_neg hb, zero_add]
-            refine (ih ys.1 m' (hk' ys.1) ys.2 hb).trans ?_
-            have hys' : (sz ys.2 : ℝ) ≤ sz s + 1 := by exact_mod_cast hys
-            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hm0) hδ
-      _ = prob (impl i x s) (fun ys => bad ys.2) + K := by
-          rw [expect_add (impl i x s) (fun ys => if bad ys.2 then (1 : ℝ) else 0) (fun _ => K),
-            expect_const, prob_eq_expect]
-      _ ≤ ((m' + 1 : ℕ) : ℝ) * (sz s + ((m' + 1 : ℕ) : ℝ)) * δ := by
-          have h3 := hstep i x s hs
-          have h4 : ((sz s : ℝ) + 1) * δ ≤ (sz s + (m' + 1)) * δ :=
-            mul_le_mul_of_nonneg_right (by linarith) hδ
-          have e : ((m' : ℝ) + 1) * (sz s + (m' + 1)) * δ = K + (sz s + (m' + 1)) * δ := by
-            rw [hK]; ring
-          push_cast
-          linarith
-
-end Potential
-
-/-! ### Hitting a list with a uniform sample -/
-
-/-- A uniform element of `T` lies in a list `L` with probability at most `|L| / |T|`
-(`prob_mem_le` for a fixed list). -/
-theorem expect_sample_mem_le {T : Type} [Fintype T] [Nonempty T] [DecidableEq T] (L : List T) :
-    expect (sample T) (fun t => if t ∈ L then (1 : ℝ) else 0) ≤ L.length / Fintype.card T := by
-  have h := prob_mem_le (OracleComp.pure L : ProbComp (List T)) (q := L.length)
-    (OracleComp.allOutputs_pure.2 le_rfl)
-  rw [prob_bind, expect_pure, prob_bind] at h
-  refine Eq.trans_le ?_ h
-  refine congrArg _ (funext fun t => ?_)
-  rw [prob_pure]
-
-/-- A key with a value in an association list is one of its keys:
-`(T.lookup x).isSome → x ∈ T.map Prod.fst`. -/
-theorem mem_keys_of_lookup_isSome {α β : Type} [DecidableEq α] (T : List (α × β)) (x : α)
-    (h : (T.lookup x).isSome = true) : x ∈ T.map Prod.fst := by
-  induction T with
-  | nil => simp at h
-  | cons p T ih =>
-    obtain ⟨k, v⟩ := p
-    rw [List.map_cons]
-    by_cases hx : x = k
-    · rw [hx]
-      exact List.mem_cons_self
-    · have hb : (x == k) = false := beq_eq_false_iff_ne.mpr hx
-      simp only [List.lookup_cons, hb] at h
-      exact List.mem_cons_of_mem _ (ih h)
-
 /-! ### The state readings -/
 
 section Records
@@ -185,14 +96,6 @@ theorem addPt_eq_of (b b' : Bool) (st : LState n d) (x y : Fin n → Bool) (hit
     addPt b st x y hit = addPt b' st x y hit := by
   rw [addPt_eq, addPt_eq, isSome_look_eq b b']
 
-/-- Exclusive-or with a fixed vector `v`, as a permutation of `{0,1}ⁿ`. -/
-def xorPerm (v : Fin n → Bool) : Equiv.Perm (Fin n → Bool) :=
-  Function.Involutive.toPerm (fun y i => xor (y i) (v i)) fun y => funext fun i => by
-    simp
-
-/-- `xorPerm v y = y ⊕ v`. -/
-theorem xorPerm_apply (v y : Fin n → Bool) : xorPerm v y = fun i => xor (y i) (v i) := rfl
-
 /-- **The change of variables at the challenge:** with `|m₀| = |m₁| = n`,
 `⟨r, m₀ ⊕ y⟩ = ⟨r, m₁ ⊕ (y ⊕ m₀ ⊕ m₁)⟩`.
 
@@ -204,7 +107,7 @@ theorem ctOf_xorPerm (r : Fin n → Bool) {m₀ m₁ : List Bool} (h₀ : m₀.l
   rw [ctOf_eq, ctOf_eq]
   congr 1
   have hv : List.ofFn (padFin n (List.zipWith xor m₀ m₁)) = List.zipWith xor m₀ m₁ :=
-    GGMRed.ofFn_padFin_of_length (by simp [h₀, h₁])
+    ofFn_padFin_of_length (by simp [h₀, h₁])
   have hY : ∀ v : Fin n → Bool,
       List.ofFn (xorPerm v y) = List.zipWith xor (List.ofFn y) (List.ofFn v) := fun v => by
     apply List.ext_getElem
@@ -460,21 +363,6 @@ theorem abs_prob_lazyImpl_sub_le (hatk : FixedLengthScheme.decOpen atk true = fa
   simp only [List.length_nil, Nat.cast_zero, zero_add]
   ring
 
-/-- Expectations of functions `ε`-close at every point are `ε`-close:
-`(∀ x, |f x - g x| ≤ ε) → |𝔼_c f - 𝔼_c g| ≤ ε`. -/
-theorem abs_expect_sub_le {ρ : Type} (c : ProbComp ρ) {f g : ρ → ℝ} {ε : ℝ}
-    (h : ∀ x, |f x - g x| ≤ ε) : |expect c f - expect c g| ≤ ε := by
-  have h1 : expect c f ≤ expect c g + ε :=
-    calc expect c f ≤ expect c (fun x => g x + ε) :=
-          expect_mono c fun x => by linarith [(abs_le.1 (h x)).2]
-      _ = expect c g + ε := by rw [expect_add c g (fun _ => ε), expect_const]
-  have h2 : expect c g ≤ expect c f + ε :=
-    calc expect c g ≤ expect c (fun x => f x + ε) :=
-          expect_mono c fun x => by linarith [(abs_le.1 (h x)).1]
-      _ = expect c f + ε := by rw [expect_add c f (fun _ => ε), expect_const]
-  rw [abs_le]
-  constructor <;> linarith
-
 /-- **Step 2 of [PS10, Thm 168.2]: with a random function the bit is hidden up to `q² / 2ⁿ`.**
 For CPA and CCA1, `d = 3n + 2`, `2n`-bit challenge queries and computations `C r` (over coins
 `r`) making at most `q` queries, the experiments with a uniform random function for `b = 0` and
diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Games.lean b/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Games.lean
index e5dbe33ba..0f61c215e 100644
--- a/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Games.lean
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Games.lean
@@ -26,7 +26,7 @@ functions; this file states the IND experiment's oracles with `f` an arbitrary f
 
 Drawing `κ` tapes uniformly gives the distribution of `fImpl` for every computation with at most
 `κ` queries (`expect_eImpl`); the proof resamples one tape at a time
-(`AdaptiveCPA.expect_sample_update`), using that the run from the counter `j` ignores the tapes
+(`ProbComp.expect_sample_coord`), using that the run from the counter `j` ignores the tapes
 below `j` (`simulate_eImpl_congr`).
 
 ## Main definitions
@@ -40,7 +40,6 @@ below `j` (`simulate_eImpl_congr`).
 * `PRFGame.fImpl_enc`, `_dec`, `_challenge_none`, `_challenge_some` and the same for `eImpl`.
 * `PRFGame.simulate_eImpl_congr`: the run from counter `j` ignores the tapes below `j`.
 * `PRFGame.expect_eImpl`: tapes in advance have the distribution of fresh nonces.
-* `PRFGame.expect_simulate_congr`: implementations with the same laws simulate alike.
 
 ## References
 
@@ -99,27 +98,6 @@ theorem decAns_eq (n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)) (op : Bo
       else [] :=
   rfl
 
-/-! ### Simulation congruence -/
-
-/-- **Implementations with the same laws simulate alike:** if every call of `impl₀` and `impl₁`
-has the same expectation of every function `g` of the answer and the new state, the simulations
-of every computation have the same expectation of every function `G` of the output and the final
-state: `𝔼[G] (simulate impl₀ c s) = 𝔼[G] (simulate impl₁ c s)`.
-
-**Proof sketch.** Induction on `c`; at a query, both sides are the expectation over the call of the
-continuation's expectation (`simulate_query`, `expect_bind`), equal by induction and the
-hypothesis. -/
-theorem expect_simulate_congr {ι : Type} {spec : OracleSpec ι} {σ α : Type}
-    (impl₀ impl₁ : QueryImpl spec σ unifSpec)
-    (h : ∀ i x s (g : spec.rng i × σ → ℝ), expect (impl₀ i x s) g = expect (impl₁ i x s) g)
-    (c : OracleComp spec α) (s : σ) (G : α × σ → ℝ) :
-    expect (simulate impl₀ c s) G = expect (simulate impl₁ c s) G := by
-  induction c generalizing s with
-  | pure a => rw [simulate_pure, simulate_pure]
-  | query i x k ih =>
-    rw [simulate_query, simulate_query, expect_bind, expect_bind, h]
-    exact congrArg _ (funext fun p => ih p.1 p.2)
-
 /-! ### The oracles with fresh nonces -/
 
 section Oracles
@@ -254,7 +232,7 @@ theorem simulate_eImpl_congr (T' : ℕ → Fin n → Bool) {α : Type}
 **Proof sketch.** Induction on `c`, generalizing the counter, the state and the budget. A query
 costs one unit, so a fresh nonce is read at a counter `j < κ`. There it reads `T j`, and the
 continuation runs from `j + 1`, so it ignores `T j` (`simulate_eImpl_congr`, `extTape_update`);
-`AdaptiveCPA.expect_sample_update` replaces `T j` by the fresh sample of `fImpl`. The other
+`ProbComp.expect_sample_coord` replaces `T j` by the fresh sample of `fImpl`. The other
 queries are answered alike. -/
 theorem expect_eImpl (κ : ℕ) {α : Type} (G : α → ℝ) (c : OracleComp (bitSpec ins outs) α)
     (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (j : ℕ) (hj : j + m ≤ κ)
@@ -291,7 +269,7 @@ theorem expect_eImpl (κ : ℕ) {α : Type} (G : α → ℝ) (c : OracleComp (bi
       have hT : ∀ T : Fin κ → Fin n → Bool, AdaptiveCPA.extTape T j = T jj :=
         fun T => AdaptiveCPA.extTape_of_lt T hjk
       simp only [hT]
-      refine (AdaptiveCPA.expect_sample_update jj (fun r T => expect (simulate
+      refine (ProbComp.expect_sample_coord jj (fun r T => expect (simulate
         (eImpl ins outs d n atk b f (AdaptiveCPA.extTape T)) (k (ans r)) (j + 1, st r))
           (fun p => G p.1)) ?_).trans ?_
       · intro r r' T
diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Handler.lean b/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Handler.lean
index 52f34aac3..121bdb30a 100644
--- a/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Handler.lean
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Handler.lean
@@ -48,6 +48,7 @@ The finalization asks nothing and outputs the adversary's bit.
 namespace TCSlib.Cryptography.Composability.PRFGame
 
 open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
+open TCSlib.Cryptography.Games.InteractiveHandler (rU rW rS rI rX rL rCnt)
 
 /-! ### Lengths and states -/
 
@@ -151,36 +152,16 @@ theorem pkTapes_apply (n : ℕ) (ω : Fin ((q.mul .var).eval n) → Bool) (j : F
 
 /-- **Tape `j` is the `j`-th block of the seed:** `⟦pkTapes q n ω j⟧ = (⟦ω⟧.drop (j·n)).take n`.
 
-**Proof sketch.** Position `k` of block `j` is position `j·n + k` of `ω` (`blocks_apply`,
-`finProdFinEquiv_apply_val`), which is position `k` of the dropped and truncated list. -/
+**Proof sketch.** The width cast keeps the string (`ofFn_arrowCongr_finCongr`), and block `j` of
+the seed is its `j`-th window (`EnsembleLemmas.blocks_eq`, `FunFamily.ofFn_blocks`). -/
 theorem ofFn_pkTapes (n : ℕ) (ω : Fin ((q.mul .var).eval n) → Bool) (j : Fin (q.eval n)) :
     List.ofFn (pkTapes q n ω j) = ((List.ofFn ω).drop (j * n)).take n := by
-  have hlen : (q.mul .var).eval n = q.eval n * n := by rw [PolyExpr.eval_mul, PolyExpr.eval_var]
-  have hj := j.isLt
-  have hle : (j : ℕ) * n + n ≤ q.eval n * n := by
-    have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hj)
-    rw [Nat.succ_mul] at this
-    exact this
-  refine List.ext_getElem ?_ fun k h₁ h₂ => ?_
-  · simp only [List.length_ofFn, List.length_take, List.length_drop]
-    omega
-  · have hpt : ∀ k' : Fin n, pkTapes q n ω j k' =
-        ω (Fin.cast hlen.symm (finProdFinEquiv (j, k'))) := fun k' => pkTapes_apply q n ω j k'
-    simp only [List.getElem_ofFn, List.getElem_take, List.getElem_drop, hpt]
-    congr 1
-    refine Fin.ext ?_
-    rw [Fin.coe_cast, finProdFinEquiv_apply_val]
-    show k + n * j = j * n + k
-    rw [Nat.mul_comm]
-    omega
+  unfold pkTapes
+  rw [Equiv.trans_apply, EnsembleLemmas.blocks_eq, FunFamily.ofFn_blocks,
+    ofFn_arrowCongr_finCongr]
 
 /-! ### Strings -/
 
-/-- `⟦padFin k a⟧ = padL k a`. -/
-private theorem ofFn_padFin_eq_padL (k : ℕ) (a : List Bool) :
-    List.ofFn (padFin k a) = EnsembleLemmas.padL k a := by
-  rw [EnsembleLemmas.padL_eq, ofFn_padFin_eq_take]
-
 /-- The fields of an encoded state with `j ≤ q(n)`: the count `1^j`, the flag and the record. -/
 private theorem fields_pkState (n j : ℕ) (o : Option (Fin (ctP.eval n) → Bool))
     (hj : j ≤ q.eval n) :
@@ -206,20 +187,6 @@ private theorem fields_pkState (n j : ℕ) (o : Option (Fin (ctP.eval n) → Boo
 
 /-! ### The round function -/
 
-/-- The parameter `1^n` of a round input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`. -/
-private def rU (w : List Bool) : List Bool := pairFstD (pairFstD w)
-/-- The seed `ω`. -/
-private def rW (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD w))
-/-- The state `s`. -/
-private def rS (w : List Bool) : List Bool := pairFstD (pairSndD w)
-/-- The oracle index `1^i`. -/
-private def rI (w : List Bool) : List Bool := pairFstD (pairFstD (pairSndD (pairSndD w)))
-/-- The query `x`. -/
-private def rX (w : List Bool) : List Bool := pairSndD (pairFstD (pairSndD (pairSndD w)))
-/-- The outer log `L` of the call. -/
-private def rL (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))
-/-- The count `1^j` of the state. -/
-private def rCnt (w : List Bool) : List Bool := pairFstD (rS w)
 /-- The challenge flag of the state. -/
 private def rFlag (w : List Bool) : Bool := (pairSndD (rS w)).headD false
 /-- The recorded challenge of the state. -/
@@ -272,13 +239,13 @@ private theorem polyTimeComputable_pkRun (atkBit b : Bool) :
     PolyTimeComputable (pkRun q atkBit b) := by
   have hF := polyTimeComputable_pairFstD
   have hD := polyTimeComputable_pairSndD
-  have hU : PolyTimeComputable rU := hF.comp hF
-  have hW : PolyTimeComputable rW := hD.comp (hD.comp hF)
-  have hS : PolyTimeComputable rS := hF.comp hD
-  have hI : PolyTimeComputable rI := hF.comp (hF.comp (hD.comp hD))
-  have hX : PolyTimeComputable rX := hD.comp (hF.comp (hD.comp hD))
-  have hL : PolyTimeComputable rL := hD.comp (hD.comp hD)
-  have hCnt : PolyTimeComputable rCnt := hF.comp hS
+  have hU : PolyTimeComputable rU := InteractiveHandler.polyTimeComputable_rU
+  have hW : PolyTimeComputable rW := InteractiveHandler.polyTimeComputable_rW
+  have hS : PolyTimeComputable rS := InteractiveHandler.polyTimeComputable_rS
+  have hI : PolyTimeComputable rI := InteractiveHandler.polyTimeComputable_rI
+  have hX : PolyTimeComputable rX := InteractiveHandler.polyTimeComputable_rX
+  have hL : PolyTimeComputable rL := InteractiveHandler.polyTimeComputable_rL
+  have hCnt : PolyTimeComputable rCnt := InteractiveHandler.polyTimeComputable_rCnt
   have hT : PolyTimeComputable fun w => pairSndD (rS w) := hD.comp hS
   have hFlag : PolyTimeComputable fun w => [rFlag w] := polyTimeComputable_headD.comp hT
   have hRec : PolyTimeComputable rRec :=
@@ -429,7 +396,7 @@ theorem pkHandler_finish (atkBit b : Bool) (n : ℕ) (z : List Bool)
     pairFstD_pairEncode]
   have hw : List.ofFn (padFin ((pkHandler q atkBit b).outLen.eval n) (List.ofFn a)) =
       List.ofFn a :=
-    GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, pkHandler_outLen])
+    ofFn_padFin_of_length (by rw [List.length_ofFn, pkHandler_outLen])
   exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).symm.trans
     (decodeBitMove_ret _ _ _ _)
 
@@ -440,25 +407,6 @@ section Answers
 variable (atkBit b : Bool) (n : ℕ) (z : List Bool)
   (ω : Fin ((pkHandler q atkBit b).seedLen.eval n) → Bool)
 
-/-- A call whose first round returns `y ‖ s'` is answered `y` with new state `s'`. -/
-private theorem impl_of_ret {i : Fin 3} (x : Fin ((pkDin i).eval n) → Bool)
-    (s : Fin ((pkStLen q).eval n) → Bool) (y : Fin ((pkDout i).eval n) → Bool)
-    (s' : Fin ((pkStLen q).eval n) → Bool)
-    (h : pkRun q atkBit b (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) i
-      (List.ofFn x) []) = pairEncode [true] (List.ofFn y ++ List.ofFn s')) :
-    (pkHandler q atkBit b).impl n z ω i x s = .pure (y, s') := by
-  rw [InteractiveHandler.impl_apply, InteractiveHandler.call_eq, pkHandler_perCall,
-    PolyExpr.eval_const]
-  rw [buildComp_succ_of_ret (a := Fin.append y s') (by
-    show decodeBitMove _ _ _ (pkRun q atkBit b _) = _
-    rw [MachineCodec.encodeLog_nil, h, ← List.ofFn_fin_append]
-    exact decodeBitMove_ret _ _ _ _), OracleComp.pure_bind]
-  congr 2
-  · funext j
-    exact Fin.append_left y s' j
-  · funext j
-    exact Fin.append_right y s' j
-
 /-- The outer log after one outer query `x'` answered `y`. -/
 private theorem encodeLog_one (x' y : Fin ((pkOut 0).eval n) → Bool) :
     (bitCodec (fun j => (pkOut j).eval n) (fun j => (pkOut j).eval n) 0).encodeLog
@@ -509,8 +457,9 @@ private theorem fields_input {i : Fin 3} (x L : List Bool) (j : ℕ)
       rL w = L ∧ rCnt w = List.replicate j true ∧ rFlag w = o.isSome ∧
       rRec w = (recBits n o).drop 1 := by
   obtain ⟨h₁, h₂, h₃⟩ := fields_pkState q n j o hj
-  simp only [InteractiveHandler.input_eq, rU, rW, rS, rI, rX, rL, rCnt, rFlag, rRec,
-    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, h₁, h₂, h₃, and_self]
+  simp only [InteractiveHandler.rU_input, InteractiveHandler.rW_input, InteractiveHandler.rS_input,
+    InteractiveHandler.rI_input, InteractiveHandler.rX_input, InteractiveHandler.rL_input,
+    InteractiveHandler.rCnt_input, rFlag, rRec, List.length_replicate, h₁, h₂, h₃, and_self]
 
 /-- The tape at the count `j < q(n)` is the `j`-th block of the seed. -/
 private theorem rNonce_fields {i : Fin 3} (x L : List Bool) (j : ℕ)
@@ -527,7 +476,8 @@ private theorem rNew_fields {i : Fin 3} (x L : List Bool) (j : ℕ)
     rNew q (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (pkState q n j o)) i x L)
         (recBits n o') = List.ofFn (pkState q n (j + 1) o') := by
   obtain ⟨hU, -, -, -, -, -, hCnt, -, -⟩ := fields_input q atkBit b n z ω (i := i) x L j o hj
-  rw [rNew, hU, hCnt, List.length_replicate, pkState_eq, ofFn_padFin_eq_padL, List.replicate_succ]
+  rw [rNew, hU, hCnt, List.length_replicate, pkState_eq, EnsembleLemmas.ofFn_padFin_eq_padL,
+    List.replicate_succ]
 
 /-- The flag and the record rebuild the record bits: `rFlag :: rRec = recBits o`. -/
 private theorem recBits_fields (o : Option (Fin (ctP.eval n) → Bool)) :
@@ -539,9 +489,6 @@ private theorem rY_one (w : List Bool) (x' y : List Bool)
     (hL : rL w = pairEncode (pairEncode [] (pairEncode x' y)) []) : rY w = y := by
   rw [rY, hL, pairFstD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode]
 
-/-- The index word of oracle `1`. -/
-private theorem replicate_one : List.replicate ((1 : Fin 3) : ℕ) true = [true] := rfl
-
 /-- The index word of oracle `2`. -/
 private theorem replicate_two : List.replicate ((2 : Fin 3) : ℕ) true = [true, true] := rfl
 
@@ -571,7 +518,7 @@ theorem pkHandler_impl_enc (x : Fin ((pkDin 0).eval n) → Bool) (j : ℕ)
   have hT : List.ofFn (padFin ((pkOut 0).eval n)
       (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩))) =
       List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) :=
-    GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hn])
+    ofFn_padFin_of_length (by rw [List.length_ofFn, hn])
   refine impl_of_query q atkBit b n z ω x _ _ _ _ ?_ ?_
   · obtain ⟨-, -, -, hI, -, hL, -, -, -⟩ :=
       fields_input q atkBit b n z ω (i := 0) (List.ofFn x) [] j o hj.le
@@ -584,11 +531,11 @@ theorem pkHandler_impl_enc (x : Fin ((pkDin 0).eval n) → Bool) (j : ℕ)
           (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)))) (List.ofFn y))) []) j o hj.le
     have hY := rY_one _ _ _ hL
     have hy : List.ofFn (padFin n (List.ofFn y)) = List.ofFn y :=
-      GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hn])
+      ofFn_padFin_of_length (by rw [List.length_ofFn, hn])
     have hct : List.ofFn (padFin ((pkDout 0).eval n) (ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)
         (List.ofFn x) (padFin n (List.ofFn y)))) =
         ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) (List.ofFn x) (padFin n (List.ofFn y)) :=
-      GGMRed.ofFn_padFin_of_length (by
+      ofFn_padFin_of_length (by
         rw [length_ctOf _ (by rw [List.length_ofFn, pkDin_zero, PolyExpr.eval_var]), pkDout_zero,
           ctP_eval])
     rw [pkRun, hI, replicate_zero', List.headD_nil, if_neg Bool.false_ne_true, hL, log_ne_nil,
@@ -616,7 +563,7 @@ theorem pkHandler_impl_dec_open (x : Fin ((pkDin 1).eval n) → Bool) (j : ℕ)
     exact hop.2
   rw [decWF_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hwf
   have hx0 : List.ofFn (padFin ((pkOut 0).eval n) (pairFstD (List.ofFn x))) =
-      pairFstD (List.ofFn x) := GGMRed.ofFn_padFin_of_length (by rw [hwf.1, hn])
+      pairFstD (List.ofFn x) := ofFn_padFin_of_length (by rw [hwf.1, hn])
   have hc : ((1 : Fin 3) : ℕ) = 1 := rfl
   refine impl_of_query q atkBit b n z ω x _ _ _ _ ?_ ?_
   · obtain ⟨hU, -, -, hI, hX, hL, -, hFlag, -⟩ :=
@@ -625,7 +572,7 @@ theorem pkHandler_impl_dec_open (x : Fin ((pkDin 1).eval n) → Bool) (j : ℕ)
         (1 : Fin 3)
         (List.ofFn x) []) = decWF n (List.ofFn x) := by
       rw [rWF, hU, hX, List.length_replicate, decWF_eq]
-    rw [pkRun, hI, replicate_one, hFlag, hWF, hop, hL, hX, hx0]
+    rw [pkRun, hI, Fin.val_one, List.replicate_one, hFlag, hWF, hop, hL, hX, hx0]
     rfl
   · intro y
     obtain ⟨hU, -, hS, hI, hX, hL, -, hFlag, -⟩ :=
@@ -641,11 +588,11 @@ theorem pkHandler_impl_dec_open (x : Fin ((pkDin 1).eval n) → Bool) (j : ℕ)
     have hans : List.ofFn (padFin ((pkDout 1).eval n)
         (true :: List.zipWith xor (pairSndD (List.ofFn x)) (List.ofFn y))) =
         true :: List.zipWith xor (pairSndD (List.ofFn x)) (List.ofFn y) :=
-      GGMRed.ofFn_padFin_of_length (by
+      ofFn_padFin_of_length (by
         rw [List.length_cons, List.length_zipWith, List.length_ofFn, hwf.2, hn, Nat.min_self,
           pkDout_one, PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const])
-    rw [pkRun, hI, replicate_one, hFlag, hWF, hop, hL, log_ne_nil, if_neg Bool.false_ne_true,
-      hans, hS, hX, hY]
+    rw [pkRun, hI, Fin.val_one, List.replicate_one, hFlag, hWF, hop, hL, log_ne_nil,
+      if_neg Bool.false_ne_true, hans, hS, hX, hY]
     rfl
 
 /-- **Closed decryption:** if the oracle is closed (CPA, or a record exists) or the query is not
@@ -655,15 +602,16 @@ theorem pkHandler_impl_dec_closed (x : Fin ((pkDin 1).eval n) → Bool) (j : ℕ
     (hcl : (atkBit && !o.isSome && decWF n (List.ofFn x)) = false) :
     (pkHandler q atkBit b).impl n z ω 1 x (pkState q n j o)
         = .pure (zeroBits _, pkState q n j o) := by
-  refine impl_of_ret q atkBit b n z ω x _ _ _ ?_
+  refine InteractiveHandler.impl_of_ret _ n z ω x _ _ _ ?_
+  show pkRun q atkBit b _ = _
   obtain ⟨hU, -, hS, hI, hX, -, -, hFlag, -⟩ :=
     fields_input q atkBit b n z ω (i := 1) (List.ofFn x) [] j o hj
   have hWF : rWF (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (pkState q n j o))
       (1 : Fin 3)
       (List.ofFn x) []) = decWF n (List.ofFn x) := by
     rw [rWF, hU, hX, List.length_replicate, decWF_eq]
-  rw [pkRun, hI, replicate_one, hFlag, hWF, hcl, hU, hS, List.length_replicate, ofFn_zeroBits,
-    pkDout_one]
+  rw [pkRun, hI, Fin.val_one, List.replicate_one, hFlag, hWF, hcl, hU, hS, List.length_replicate,
+    ofFn_zeroBits, pkDout_one]
   rfl
 
 /-- **A recorded challenge is repeated:** from `pkState j (some c)`, a challenge is answered `c` and
@@ -672,11 +620,12 @@ theorem pkHandler_impl_challenge_some (x : Fin ((pkDin 2).eval n) → Bool) (j :
     (c : Fin (ctP.eval n) → Bool) (hj : j ≤ q.eval n) :
     (pkHandler q atkBit b).impl n z ω 2 x (pkState q n j (some c)) =
       .pure (padFin _ (List.ofFn c), pkState q n j (some c)) := by
-  refine impl_of_ret q atkBit b n z ω x _ _ _ ?_
+  refine InteractiveHandler.impl_of_ret _ n z ω x _ _ _ ?_
+  show pkRun q atkBit b _ = _
   obtain ⟨-, -, hS, hI, -, -, -, hFlag, hRec⟩ :=
     fields_input q atkBit b n z ω (i := 2) (List.ofFn x) [] j (some c) hj
   have hc : List.ofFn (padFin ((pkDout 2).eval n) (List.ofFn c)) = List.ofFn c :=
-    GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, pkDout_two])
+    ofFn_padFin_of_length (by rw [List.length_ofFn, pkDout_two])
   rw [pkRun, hI, replicate_two, hFlag, hRec, hS, hc]
   rfl
 
@@ -698,7 +647,7 @@ theorem pkHandler_impl_challenge_none (x : Fin ((pkDin 2).eval n) → Bool) (j :
   have hT : List.ofFn (padFin ((pkOut 0).eval n)
       (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩))) =
       List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) :=
-    GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hn])
+    ofFn_padFin_of_length (by rw [List.length_ofFn, hn])
   have hmsg : (AdaptiveCPA.msgOf n b (List.ofFn x)).length = n := by
     have hx : (List.ofFn x).length = n + n := by
       rw [List.length_ofFn, pkDin_two, PolyExpr.eval_add, PolyExpr.eval_var]
@@ -717,7 +666,7 @@ theorem pkHandler_impl_challenge_none (x : Fin ((pkDin 2).eval n) → Bool) (j :
           (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)))) (List.ofFn y))) []) j none hj.le
     have hY := rY_one _ _ _ hL
     have hy : List.ofFn (padFin n (List.ofFn y)) = List.ofFn y :=
-      GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hn])
+      ofFn_padFin_of_length (by rw [List.length_ofFn, hn])
     have hlen : (ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) (AdaptiveCPA.msgOf n b (List.ofFn x))
         (padFin n (List.ofFn y))).length = ctP.eval n := by
       rw [length_ctOf _ hmsg, ctP_eval]
@@ -725,12 +674,12 @@ theorem pkHandler_impl_challenge_none (x : Fin ((pkDin 2).eval n) → Bool) (j :
         (AdaptiveCPA.msgOf n b (List.ofFn x)) (padFin n (List.ofFn y)))) =
         ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) (AdaptiveCPA.msgOf n b (List.ofFn x))
           (padFin n (List.ofFn y)) :=
-      GGMRed.ofFn_padFin_of_length (by rw [hlen, pkDout_two])
+      ofFn_padFin_of_length (by rw [hlen, pkDout_two])
     have hrec : true :: ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)
         (AdaptiveCPA.msgOf n b (List.ofFn x)) (padFin n (List.ofFn y)) =
         recBits n (some (padFin (ctP.eval n) (ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)
           (AdaptiveCPA.msgOf n b (List.ofFn x)) (padFin n (List.ofFn y))))) := by
-      rw [recBits_some, GGMRed.ofFn_padFin_of_length hlen]
+      rw [recBits_some, ofFn_padFin_of_length hlen]
     have hMsg : rMsg b (InteractiveHandler.input n z (List.ofFn ω)
         (List.ofFn (pkState q n j none)) (2 : Fin 3) (List.ofFn x)
         (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((pkOut 0).eval n)
diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Lazy.lean b/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Lazy.lean
index 8e4278eed..bc5867840 100644
--- a/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Lazy.lean
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Lazy.lean
@@ -3,7 +3,8 @@ Copyright (c) 2026 TCSlib contributors. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 -/
 import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Games
-import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA.Eager
+import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
+import TCSlib.Cryptography.Foundations.BitLists
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -21,7 +22,7 @@ through that recomputation. A flag records the bad events of step 2: `r*` was al
 table, or a later encryption uses `r*`.
 
 Averaging the experiment with `R` over a uniform `R` gives the lazy experiment
-(`expect_lazyImpl`): at a new point, resampling `R` there (`BitwiseSim.expect_sample_update`) is
+(`expect_lazyImpl`): at a new point, resampling `R` there (`ProbComp.expect_sample_update`) is
 the lazy sample; the table and the record determine `R` elsewhere (`ovr`).
 
 ## Main definitions
@@ -224,26 +225,17 @@ section Records
 
 variable {n d : ℕ}
 
-/-- Exclusive-or with the same list twice cancels: `(a ⊕ c) ⊕ a = c` for `|a| = |c|`. -/
-theorem zipWith_xor_cancel_left {a c : List Bool} (h : a.length = c.length) :
-    List.zipWith xor (List.zipWith xor a c) a = c := by
-  apply List.ext_getElem
-  · simp [h]
-  · intro i h₁ h₂
-    simp only [List.getElem_zipWith]
-    cases a[i] <;> cases c[i] <;> rfl
-
 /-- The record of a ciphertext `⟨r, m ⊕ y⟩` (with `|m| = n` and `d = 3n + 2`) has nonce `r`. -/
 theorem rStar_ctOf (hd : d = 3 * n + 2) (r : Fin n → Bool) {m : List Bool} (hm : m.length = n)
     (y : Fin n → Bool) : rStar (padFin d (ctOf r m y)) = r := by
-  rw [rStar_eq, GGMRed.ofFn_padFin_of_length (by rw [length_ctOf r hm, hd]), ctOf_eq,
+  rw [rStar_eq, ofFn_padFin_of_length (by rw [length_ctOf r hm, hd]), ctOf_eq,
     pairFstD_pairEncode, padFin_ofFn]
 
 /-- The record of a challenge ciphertext `⟨r, m_b ⊕ y⟩` has pad `y`. -/
 theorem padAt_ctOf (hd : d = 3 * n + 2) (b : Bool) (r : Fin n → Bool) (ml : List Bool)
     (hm : (AdaptiveCPA.msgOf n b ml).length = n) (y : Fin n → Bool) :
     padAt b ml (padFin d (ctOf r (AdaptiveCPA.msgOf n b ml) y)) = y := by
-  rw [padAt_eq, GGMRed.ofFn_padFin_of_length (by rw [length_ctOf r hm, hd]), ctOf_eq,
+  rw [padAt_eq, ofFn_padFin_of_length (by rw [length_ctOf r hm, hd]), ctOf_eq,
     pairSndD_pairEncode, zipWith_xor_cancel_left (by rw [hm, List.length_ofFn]), padFin_ofFn]
 
 /-- The flag does not change the recorded values: `look b (st.1, st.2.1, bd) = look b st`. -/
@@ -352,7 +344,7 @@ queries, for every computation `c`, state `st` and function `G` of the output,
 
 **Proof sketch.** Induction on `c`. At a point `x` with a recorded value both sides use it and the
 recorded values do not change (`ovr_addPt_of_isSome`, `ovr_record_of_some`). At a new point,
-resample `R` at `x` (`BitwiseSim.expect_sample_update`): `R(x)` becomes the lazy sample `y`, and
+resample `R` at `x` (`ProbComp.expect_sample_update`): `R(x)` becomes the lazy sample `y`, and
 `R` resampled is the override of the new state (`ovr_addPt_of_none`, `ovr_record_of_none`);
 exchange the samples (`expect_sample_comm`) and apply the induction hypothesis. Closed
 decryptions and repeated challenges are answered alike. -/
@@ -384,7 +376,7 @@ theorem expect_lazyImpl (hd : d = 3 * n + 2) (hi2 : ins 2 = n + n) {α : Type} (
         exact (congrArg _ (funext fun R => by
           rw [← ovr_addPt_of_isSome b st r y₀ (hitStar st r) hsome R]; rfl)).trans (ih _ _)
       | none =>
-        rw [← BitwiseSim.expect_sample_update r]
+        rw [← ProbComp.expect_sample_update r]
         simp only [Option.getD_none]
         have hU : ∀ R y, ovr b st (Function.update R r y) =
             ovr b (addPt b st r y (hitStar st r)) R :=
@@ -415,7 +407,7 @@ theorem expect_lazyImpl (hd : d = 3 * n + 2) (hi2 : ins 2 = n + n) {α : Type} (
           exact (congrArg _ (funext fun R => by
             rw [← ovr_addPt_of_isSome b st _ y₀ false hsome R]; rfl)).trans (ih _ _)
         | none =>
-          rw [← BitwiseSim.expect_sample_update (padFin n (pairFstD (List.ofFn c)))]
+          rw [← ProbComp.expect_sample_update (padFin n (pairFstD (List.ofFn c)))]
           simp only [Option.getD_none]
           have hU : ∀ R y, ovr b st (Function.update R (padFin n (pairFstD (List.ofFn c))) y) =
               ovr b (addPt b st (padFin n (pairFstD (List.ofFn c))) y false) R :=
@@ -450,7 +442,7 @@ theorem expect_lazyImpl (hd : d = 3 * n + 2) (hi2 : ins 2 = n + n) {α : Type} (
           cases b <;> simp [this]
         have hpad : ∀ r y, List.ofFn (padFin d (ctOf r (AdaptiveCPA.msgOf n b (List.ofFn mm)) y)) =
             ctOf r (AdaptiveCPA.msgOf n b (List.ofFn mm)) y := fun r y =>
-          GGMRed.ofFn_padFin_of_length (by rw [length_ctOf r hm, hd])
+          ofFn_padFin_of_length (by rw [length_ctOf r hm, hd])
         simp only [simulate_query, Option.map_none, fImpl_challenge_none, lazyImpl_challenge_none,
           OracleComp.bind_assoc, expect_bind, OracleComp.pure_bind, hpad]
         rw [expect_sample_comm]
@@ -466,7 +458,7 @@ theorem expect_lazyImpl (hd : d = 3 * n + 2) (hi2 : ins 2 = n + n) {α : Type} (
                 hr R]; rfl)).trans
             (ih _ _)
         | none =>
-          rw [← BitwiseSim.expect_sample_update r]
+          rw [← ProbComp.expect_sample_update r]
           simp only [Option.getD_none, Option.isSome_none]
           have hU : ∀ R y, ovr b ((T, none, bd) : LState n d) (Function.update R r y) =
               ovr b ((T, some (List.ofFn mm, padFin d (ctOf r (AdaptiveCPA.msgOf n b
diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Reduction.lean b/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Reduction.lean
index 8a4c6987f..a56ef4068 100644
--- a/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Reduction.lean
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Reduction.lean
@@ -6,6 +6,7 @@ import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Handler
 import TCSlib.Cryptography.Games.Bridges.QueryTree
 import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs
 import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Games
+import TCSlib.Cryptography.Foundations.BitLists
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -25,7 +26,7 @@ The proof answers the handler's outer queries by `f` (`fOuter`) and composes the
 implementations (`QueryImpl.comp`). Each composed call, from the encoded state `pkState j o`, is
 the call of `eImpl` from `(j, o)` with the handler's tapes in advance (`comp_pkAbs`), as long as
 `j` is below the number `q(n)` of tapes; the adversary asks at most `q(n)` queries, so this holds
-along every run (`simulate_eq_of_abs_bounded`). Drawing the seed uniformly then gives fresh
+along every run (`Games.simulate_eq_of_abs_bounded`). Drawing the seed uniformly then gives fresh
 nonces (`PRFGame.expect_eImpl`).
 
 ## Main definitions
@@ -36,8 +37,6 @@ nonces (`PRFGame.expect_eImpl`).
 
 ## Main results
 
-* `PRFGame.simulate_eq_of_abs_bounded`: simulation through a state abstraction along runs with a
-  query budget.
 * `PRFGame.exists_prfReduction`: the reduction.
 
 ## References
@@ -50,34 +49,6 @@ namespace TCSlib.Cryptography.Composability.PRFGame
 
 open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim
 
-/-! ### Simulation through a state abstraction along bounded runs -/
-
-/-- **Simulation through a state abstraction, along runs with a query budget:** let every call of
-`impl₂` from a state `s` with `cnt s < κ` be a deterministic answer `(y, s')` with
-`cnt s' ≤ cnt s + 1`, and the call of `impl₁` from `f s` be `(y, f s')`. Then for a computation
-`c` with at most `m` queries and `cnt s + m ≤ κ`,
-`simulate impl₁ c (f s) = (simulate impl₂ c s).bind fun p => pure (p.1, f p.2)`.
-
-**Proof sketch.** Induction on `c`. A query costs one unit, so it is asked from a state with
-`cnt s < κ`; both calls return the same answer, and the continuation runs from `s'` with one unit
-less, where `cnt s' + (m - 1) ≤ κ`. -/
-theorem simulate_eq_of_abs_bounded {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
-    {σ₁ σ₂ α : Type} (impl₁ : QueryImpl spec σ₁ spec') (impl₂ : QueryImpl spec σ₂ spec')
-    (f : σ₂ → σ₁) (cnt : σ₂ → ℕ) (κ : ℕ)
-    (h : ∀ i x s, cnt s < κ → ∃ (y : spec.rng i) (s' : σ₂), impl₂ i x s = .pure (y, s') ∧
-      cnt s' ≤ cnt s + 1 ∧ impl₁ i x (f s) = .pure (y, f s'))
-    (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ₂)
-    (hs : cnt s + m ≤ κ) :
-    simulate impl₁ c (f s) = (simulate impl₂ c s).bind fun p => .pure (p.1, f p.2) := by
-  induction c generalizing m s with
-  | pure a => simp only [simulate_pure, OracleComp.pure_bind]
-  | query i x k ih =>
-    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
-    have hm1 : 1 ≤ m := hm
-    obtain ⟨y, s', h₂, hcnt, h₁⟩ := h i x s (by omega)
-    rw [simulate_query, simulate_query, h₁, h₂, OracleComp.pure_bind, OracleComp.pure_bind]
-    exact ih y (m - 1) (hk y) s' (by omega)
-
 /-! ### The outer oracle and the composed calls -/
 
 /-- **The outer oracle answering with `f`:** a query `x` is answered `f x`, lengths adjusted. -/
@@ -136,8 +107,8 @@ private theorem fOuter_tape (r : Fin n → Bool) :
     padFin n (List.ofFn (padFin ((pkOut 0).eval n) (List.ofFn (f (padFin n (List.ofFn
       (padFin ((pkOut 0).eval n) (List.ofFn r)))))))) = f r := by
   have hn : (pkOut 0).eval n = n := by rw [pkOut_eq, PolyExpr.eval_var]
-  rw [GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hn]), padFin_ofFn,
-    GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hn]), padFin_ofFn]
+  rw [ofFn_padFin_of_length (by rw [List.length_ofFn, hn]), padFin_ofFn,
+    ofFn_padFin_of_length (by rw [List.length_ofFn, hn]), padFin_ofFn]
 
 /-- **One composed call is a call of `eImpl` with the tapes in advance:** from the encoded state
 `pkState j o` with `j < q(n)`, the handler composed with `fOuter f` answers as `eImpl` with pad
@@ -181,11 +152,11 @@ theorem comp_pkAbs (i : Fin 3) (x : (bitSpecAt pkDin pkDout n).dom i)
       have hn : (pkOut 0).eval n = n := by rw [pkOut_eq, PolyExpr.eval_var]
       have hx0 : padFin n (List.ofFn (padFin ((pkOut 0).eval n) (pairFstD (List.ofFn x)))) =
           padFin n (pairFstD (List.ofFn x)) := by
-        rw [GGMRed.ofFn_padFin_of_length (by rw [hwf'.1, hn])]
+        rw [ofFn_padFin_of_length (by rw [hwf'.1, hn])]
       rw [QueryImpl.comp_apply, pkAbs_eq, pkHState_eq,
         pkHandler_impl_dec_open q atkBit b n z ω x j o hj.le hop,
         simulate_query, fOuter_apply, OracleComp.pure_bind, simulate_pure, OracleComp.pure_bind,
-        hx0, GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn]; exact hn.symm),
+        hx0, ofFn_padFin_of_length (by rw [List.length_ofFn]; exact hn.symm),
         decOpen_atkOf, decAns_eq]
       simp only [Bool.and_eq_true] at hop
       rw [if_pos (by simp only [Bool.and_eq_true]; exact ⟨hop.1, hwf⟩)]
@@ -324,7 +295,7 @@ theorem exists_prfReduction (A : NUPPT) (q : PolyExpr) (atkBit b : Bool) :
     intro ω
     have key : ∀ g : Fin 1 → Bool, (if g 0 = true then (1 : ℝ) else 0) =
         if (List.ofFn g).headD false = true then 1 else 0 := fun g => by
-      rw [AdaptiveCPA.headD_ofFn_one]
+      rw [headD_ofFn_one]
     have h2 : _ = B.toCompOn (bitCodec (fun _ : Fin 1 => PolyExpr.var.eval n)
         (fun _ => PolyExpr.var.eval n) ((pkHandler q atkBit b).outLen.eval n)) n
         (q.eval n * (pkHandler q atkBit b).perCall.eval n + (pkHandler q atkBit b).finCall.eval n)
@@ -351,7 +322,7 @@ theorem exists_prfReduction (A : NUPPT) (q : PolyExpr) (atkBit b : Bool) :
       expect_bind]
     simp only [expect_pure]
     refine congrArg _ (funext fun p => ?_)
-    rw [GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, pkHandler_outLen])]
+    rw [ofFn_padFin_of_length (by rw [List.length_ofFn, pkHandler_outLen])]
   simp only [hrun]
   rw [expect_sample_equiv (pkSeedTapes q atkBit b n) (fun T => expect (simulate
       (eImpl (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) (ctP.eval n) n (atkOf atkBit)
diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Transfer.lean b/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Transfer.lean
index f98f82394..cf5157304 100644
--- a/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Transfer.lean
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Transfer.lean
@@ -15,15 +15,13 @@ Generic transfer lemmas for step 1 of [PS10, Theorem 168.2]: a fixed-length priv
 whose encryption with a key is `⟨r, m ⊕ f(r)⟩` with a uniform nonce `r`, and whose decryption is
 `⟨1, v ⊕ f(x)⟩` on well-formed `⟨x, v⟩` and `⊥` otherwise, has, call by call, the oracles
 `PRFGame.fImpl` with the pad function `f` under CPA and CCA1 (`expect_indImpl_fImpl`). The game's
-codec is a bit codec (`indCodec_eq_bitCodec`), and the experiment with `f` is transported along
-equal lengths (`expect_fImpl_transport`).
+codec is a bit codec (`FixedLengthScheme.indCodec_eq_bitCodec`), and the experiment with `f` is
+transported along equal lengths (`expect_fImpl_transport`).
 
 ## Main results
 
 * `PRFGame.expect_indImpl_fImpl`: one call of `IND_b` has the law of `fImpl`.
-* `PRFGame.indCodec_eq_bitCodec`, `PRFGame.expect_fImpl_transport`.
-* `PRFGame.padFin_nil`, `padFin_replicate_false`, `ofFn_arrowCongr_finCongr`:
-  vector readings.
+* `PRFGame.expect_fImpl_transport`: the experiment with `f` along equal lengths.
 
 ## References
 
@@ -35,23 +33,6 @@ namespace TCSlib.Cryptography.Composability.PRFGame
 
 open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim
 
-/-- Reading a vector at an equal width keeps its word:
-`⟦(arrowCongr (finCongr h) (refl Bool)) v⟧ = ⟦v⟧`. -/
-theorem ofFn_arrowCongr_finCongr {a b : ℕ} (h : a = b) (v : Fin a → Bool) :
-    List.ofFn ((Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)) v) = List.ofFn v := by
-  subst h
-  rfl
-
-
-/-- An all-`false` list reads as the all-`false` vector at every width:
-`padFin d (List.replicate m false) = zeroBits d`. -/
-theorem padFin_replicate_false (d m : ℕ) : padFin d (List.replicate m false) = zeroBits d := by
-  rw [← ofFn_zeroBits, AdaptiveCPA.padFin_ofFn_zeroBits]
-
-/-- The empty list reads as the all-`false` vector: `padFin d [] = zeroBits d`. -/
-theorem padFin_nil (d : ℕ) : padFin d [] = zeroBits d := padFin_replicate_false d 0
-
-
 /-- **One call of `IND_b` with the key `key` has the law of `fImpl` with the pad function `fk`**
 (CPA or CCA1), for every function `g` of the answer and the new state, for a scheme `S` whose
 encryption with `key` is `ctOf` with the nonce `ν re` of a bijection `ν` (`henc`), whose
@@ -88,20 +69,20 @@ theorem expect_indImpl_fImpl (S : FixedLengthScheme) (atkBit b : Bool) (n : ℕ)
     refine congrArg _ (funext fun re => ?_)
     rw [expect_pure, expect_pure]
     have hm : List.ofFn (cast (S.indSpec_encDom n) m) = List.ofFn m :=
-      AdaptiveCPA.ofFn_cast (S.inLens_zero n) _ m
+      ofFn_cast (S.inLens_zero n) _ m
     have hm' : cast (S.indSpec_encDom n) m = padFin n (List.ofFn m) :=
-      List.ofFn_injective (by rw [hm, GGMRed.ofFn_padFin_of_length (by
+      List.ofFn_injective (by rw [hm, ofFn_padFin_of_length (by
         rw [List.length_ofFn, S.inLens_zero])])
     congr 2
     refine List.ofFn_injective ?_
-    rw [AdaptiveCPA.ofFn_cast (S.outLens_zero n).symm _ _, hm', henc,
-      GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, S.inLens_zero]),
-      GGMRed.ofFn_padFin_of_length (by
+    rw [ofFn_cast (S.outLens_zero n).symm _ _, hm', henc,
+      ofFn_padFin_of_length (by rw [List.length_ofFn, S.inLens_zero]),
+      ofFn_padFin_of_length (by
         rw [hlenCt _ (by rw [List.length_ofFn, S.inLens_zero]), S.outLens_zero])]
   | 1, c =>
     rw [S.indImpl_dec_onSpec, fImpl_dec, decOpen_atkOf]
     have hc : List.ofFn (cast (S.indSpec_decDom n) c) = List.ofFn c :=
-      AdaptiveCPA.ofFn_cast (S.inLens_one n) _ c
+      ofFn_cast (S.inLens_one n) _ c
     by_cases hop : (atkBit && !s.isSome) = true
     · have hs : s = none := by
         cases s with
@@ -113,11 +94,11 @@ theorem expect_indImpl_fImpl (S : FixedLengthScheme) (atkBit b : Bool) (n : ℕ)
       rw [expect_pure, expect_pure]
       congr 2
       refine List.ofFn_injective ?_
-      rw [AdaptiveCPA.ofFn_cast (S.outLens_one n).symm _ _, hc, hdec, decAns_eq, hop, Bool.true_and]
+      rw [ofFn_cast (S.outLens_one n).symm _ _, hc, hdec, decAns_eq, hop, Bool.true_and]
       by_cases hw : decWF n (List.ofFn c) = true
       · rw [if_pos hw, if_pos hw]
         rw [decWF_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hw
-        rw [GGMRed.ofFn_padFin_of_length (by
+        rw [ofFn_padFin_of_length (by
           rw [List.length_cons, List.length_zipWith, List.length_ofFn, hw.2, Nat.min_self,
             S.outLens_one])]
       · rw [if_neg hw, if_neg hw, padFin_nil, ofFn_zeroBits, S.outLens_one]
@@ -126,7 +107,7 @@ theorem expect_indImpl_fImpl (S : FixedLengthScheme) (atkBit b : Bool) (n : ℕ)
         Bool.false_and, if_neg Bool.false_ne_true, expect_pure, expect_pure, padFin_nil]
   | 2, mm =>
     have hmm : List.ofFn (cast (S.indSpec_challengeDom n) mm) = List.ofFn mm :=
-      AdaptiveCPA.ofFn_cast (S.inLens_two n) _ mm
+      ofFn_cast (S.inLens_two n) _ mm
     have hmsg : (AdaptiveCPA.msgOf n b (List.ofFn mm)).length = n := by
       have : (List.ofFn mm).length = n + n := by rw [List.length_ofFn, S.inLens_two]
       rw [AdaptiveCPA.msgOf_eq]
@@ -136,17 +117,17 @@ theorem expect_indImpl_fImpl (S : FixedLengthScheme) (atkBit b : Bool) (n : ℕ)
         (cast (S.indSpec_challengeDom n) mm)).1) =
         padFin n (AdaptiveCPA.msgOf n b (List.ofFn mm)) := by
       refine List.ofFn_injective ?_
-      rw [GGMRed.ofFn_padFin_of_length hmsg, AdaptiveCPA.msgOf_eq, ← hmm]
+      rw [ofFn_padFin_of_length hmsg, AdaptiveCPA.msgOf_eq, ← hmm]
       cases b
-      · exact AdaptiveCPA.ofFn_splitHalf_fst _
-      · exact AdaptiveCPA.ofFn_splitHalf_snd _
+      · exact FixedLengthScheme.ofFn_splitHalf_fst _
+      · exact FixedLengthScheme.ofFn_splitHalf_snd _
     cases s with
     | some c =>
       rw [S.indImpl_challenge_repeat_onSpec, fImpl_challenge_some, expect_pure, expect_pure]
       congr 2
       refine List.ofFn_injective ?_
-      rw [AdaptiveCPA.ofFn_cast (S.outLens_two n).symm _ _,
-        GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, S.outLens_two])]
+      rw [ofFn_cast (S.outLens_two n).symm _ _,
+        ofFn_padFin_of_length (by rw [List.length_ofFn, S.outLens_two])]
     | none =>
       rw [S.indImpl_challenge_none_onSpec, fImpl_challenge_none, expect_bind, expect_bind,
         ← expect_sample_equiv ν]
@@ -156,34 +137,14 @@ theorem expect_indImpl_fImpl (S : FixedLengthScheme) (atkBit b : Bool) (n : ℕ)
           (cast (S.indSpec_challengeDom n) mm)).2 else (FixedLengthScheme.splitHalf
           (cast (S.indSpec_challengeDom n) mm)).1) re) =
           ctOf (ν re) (AdaptiveCPA.msgOf n b (List.ofFn mm)) (fk (ν re)) := by
-        rw [hsel, henc, GGMRed.ofFn_padFin_of_length hmsg]
+        rw [hsel, henc, ofFn_padFin_of_length hmsg]
       congr 2
       · refine List.ofFn_injective ?_
-        rw [AdaptiveCPA.ofFn_cast (S.outLens_two n).symm _ _, henc',
-          GGMRed.ofFn_padFin_of_length (by rw [hlenCt _ hmsg, S.outLens_two])]
+        rw [ofFn_cast (S.outLens_two n).symm _ _, henc',
+          ofFn_padFin_of_length (by rw [hlenCt _ hmsg, S.outLens_two])]
       · congr 1
         refine List.ofFn_injective ?_
-        rw [henc', GGMRed.ofFn_padFin_of_length (hlenCt _ hmsg _)]
-
-
-/-- **The game's codec is the bit codec of its lengths:**
-`S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1` (the three codec readers and structure
-eta). -/
-theorem indCodec_eq_bitCodec (S : FixedLengthScheme) (n : ℕ) :
-    S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1 := by
-  have hd : (S.indCodec n).decodeMove = (bitCodec (S.inLens n) (S.outLens n) 1).decodeMove :=
-    funext fun w => (S.indCodec_decodeMove n w).trans (bitCodec_decodeMove _ _ _ w).symm
-  have he : (S.indCodec n).encodeEntry = (bitCodec (S.inLens n) (S.outLens n) 1).encodeEntry :=
-    funext fun e => (S.indCodec_encodeEntry n e).trans (bitCodec_encodeEntry _ _ _ e).symm
-  have ht : (S.indCodec n).timeout = (bitCodec (S.inLens n) (S.outLens n) 1).timeout :=
-    (S.indCodec_timeout n).trans (bitCodec_timeout _ _ _).symm
-  calc S.indCodec n = ⟨(S.indCodec n).decodeMove, (S.indCodec n).encodeEntry,
-        (S.indCodec n).timeout⟩ := rfl
-    _ = ⟨(bitCodec (S.inLens n) (S.outLens n) 1).decodeMove,
-        (bitCodec (S.inLens n) (S.outLens n) 1).encodeEntry,
-        (bitCodec (S.inLens n) (S.outLens n) 1).timeout⟩ := by rw [hd, he, ht]
-    _ = bitCodec (S.inLens n) (S.outLens n) 1 := rfl
-
+        rw [henc', ofFn_padFin_of_length (hlenCt _ hmsg _)]
 
 /-- **The game with pad function `f` along equal lengths:** for `ins = ins'`, `outs = outs'` and
 `d = d'`, the expected first output bit of `A`'s run against `fImpl` agrees.
diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/OracleSecurity.lean b/TCSlib/Cryptography/Encryption/PrivateKey/OracleSecurity.lean
index db45c238d..8b3d56867 100644
--- a/TCSlib/Cryptography/Encryption/PrivateKey/OracleSecurity.lean
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/OracleSecurity.lean
@@ -55,6 +55,9 @@ never (CPA), before the challenge only (CCA1), or always, except on `c` itself (
 * `indImpl_dec_cpa`, `indImpl_dec_cca2_challenge`, `indImpl_challenge_repeat`: sanity checks of
   the oracles (CPA's `Dec` is closed; CCA2's `Dec` refuses the challenge; a challenge is asked
   once).
+* `FixedLengthScheme.ofFn_splitHalf_fst`, `ofFn_splitHalf_snd`: the strings of the two halves of a
+  challenge query.
+* `FixedLengthScheme.indCodec_eq_bitCodec`: the game's codec is a bit codec.
 
 The theorems on these notions (Thms 168.2 and 170.4, Claim 169.a) are stated in the statement
 phase of prong C, in their own modules.
@@ -178,6 +181,26 @@ theorem splitHalf_fst {n : ℕ} (x : Fin (n + n) → Bool) :
 theorem splitHalf_snd {n : ℕ} (x : Fin (n + n) → Bool) :
     (splitHalf x).2 = fun j => x (Fin.natAdd n j) := rfl
 
+/-- The first half of a `2m`-bit query is its first `m` bits:
+`⟦(splitHalf y).1⟧ = ⟦y⟧.take m`. -/
+theorem ofFn_splitHalf_fst {m : ℕ} (y : Fin (m + m) → Bool) :
+    List.ofFn (splitHalf y).1 = (List.ofFn y).take m := by
+  rw [splitHalf_fst]
+  refine List.ext_getElem (by simp only [List.length_ofFn, List.length_take]; omega)
+    fun i h₁ h₂ => ?_
+  rw [List.getElem_ofFn, List.getElem_take, List.getElem_ofFn]
+  rfl
+
+/-- The second half of a `2m`-bit query is its last `m` bits:
+`⟦(splitHalf y).2⟧ = ⟦y⟧.drop m`. -/
+theorem ofFn_splitHalf_snd {m : ℕ} (y : Fin (m + m) → Bool) :
+    List.ofFn (splitHalf y).2 = (List.ofFn y).drop m := by
+  rw [splitHalf_snd]
+  refine List.ext_getElem (by simp only [List.length_ofFn, List.length_drop]; omega)
+    fun i h₁ h₂ => ?_
+  rw [List.getElem_ofFn, List.getElem_drop, List.getElem_ofFn]
+  rfl
+
 /-- **The oracles of `IND_b`** at parameter `n`, for the key `k`; the state is the challenge,
 once asked.
 - `Enc` answers `Enc_k(m)` with fresh coins.
@@ -337,6 +360,9 @@ theorem indCodec_encodeEntry (n : ℕ)
 theorem indCodec_timeout (n : ℕ) : (S.indCodec n).timeout = zeroBits 1 :=
   bitCodec_timeout (S.inLens n) (S.outLens n) 1
 
+/-- The game's codec is a bit codec: `S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1`. -/
+theorem indCodec_eq_bitCodec (n : ℕ) : S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1 := rfl
+
 /-- **The experiment `IND_b^{O₁,O₂}(Π, A, n)`** [PS10, Definition 168.1] for the attack `atk`, with
 query budget `q`: sample `k ← Gen(1^n)` and `A`'s coins, run `A` against the oracles of `IND_b`
 from the unchallenged state, and output its bit. -/
diff --git a/TCSlib/Cryptography/Encryption/PublicKey.lean b/TCSlib/Cryptography/Encryption/PublicKey.lean
index 24445cebd..9fa4a9d96 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey.lean
@@ -10,6 +10,7 @@ import TCSlib.Cryptography.Encryption.PublicKey.EnsembleSecurity
 import TCSlib.Cryptography.Encryption.PublicKey.TrapdoorPredictor
 import TCSlib.Cryptography.Encryption.PublicKey.Trapdoor
 import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
+import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.PaddedCPA
 import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveSecurity
 import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA
 import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA
@@ -55,7 +56,9 @@ multi-message security.
 * `Trapdoor` proves correctness and single-bit security of Algorithm 104.3 and gives
   the Goldreich–Levin bridge [PS10, §3.10].
 * `OracleSecurity` gives the fixed-length scheme, codecs and oracle games [PS10, §7.1.4].
-  The proof of `TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.padded_cpa` is pending.
+* `OracleSecurity.PaddedCPA` proves
+  `TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.padded_cpa` (single-bit security gives
+  CPA security of the padded scheme).
 * `AdaptiveSecurity` gives the multi-challenge game and its cap-one correspondence.
 * `AdaptiveCPA` lifts single-challenge CPA security to the adaptive game (stated).
 * `BitwiseCPA` gives CPA and adaptive CPA security of the padded bitwise scheme (the first
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/Games.lean b/TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/Games.lean
index 233dc8491..8b2bdbd29 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/Games.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/Games.lean
@@ -5,6 +5,7 @@ Released under Apache 2.0 license as described in the file LICENSE.
 import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveSecurity
 import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Hybrid
 import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler
+import TCSlib.Cryptography.Foundations.BitLists
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -32,7 +33,6 @@ and `H_κ` the game with `b = true` (`acHyb_lt_zero`, `acHyb_lt_cap`).
 
 ## Main results
 
-* `AdaptiveCPA.indCodec_eq_bitCodec`: the adversary codec is a `bitCodec`.
 * `AdaptiveCPA.acDin_eval`, `acDout_eval`: the lengths of T2's codec are the game's.
 * `AdaptiveCPA.castImpl_adaptiveIndImpl`: the adaptive CPA oracles, read on T2's codec, are the
   hybrid with the constant selector.
@@ -52,26 +52,6 @@ variable (S : FixedLengthPKScheme)
 
 /-! ### Codecs and lengths -/
 
-/-- **The adversary codec is a bit codec:** `S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1`.
-
-**Proof sketch.** Both are codecs with the same three fields (`indCodec_decodeMove`,
-`indCodec_encodeEntry`, `indCodec_timeout` against the `bitCodec` readers). -/
-theorem indCodec_eq_bitCodec (n : ℕ) :
-    S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1 := by
-  have h1 := S.indCodec_decodeMove n
-  have h2 := S.indCodec_encodeEntry n
-  have h3 := S.indCodec_timeout n
-  generalize S.indCodec n = c at h1 h2 h3
-  cases c with
-  | mk d e t =>
-    have hd : d = (bitCodec (S.inLens n) (S.outLens n) 1).decodeMove :=
-      funext fun w => (h1 w).trans (bitCodec_decodeMove _ _ _ w).symm
-    have he : e = (bitCodec (S.inLens n) (S.outLens n) 1).encodeEntry :=
-      funext fun en => (h2 en).trans (bitCodec_encodeEntry _ _ _ en).symm
-    have ht : t = (bitCodec (S.inLens n) (S.outLens n) 1).timeout :=
-      h3.trans (bitCodec_timeout _ _ _).symm
-    rw [hd, he, ht]
-
 /-- The query lengths of T2's codec are the game's: `(acDin S · ).eval n = S.inLens n`. -/
 theorem acDin_eval (n : ℕ) : (fun i => (acDin S i).eval n) = S.inLens n := by
   funext i
@@ -86,48 +66,6 @@ theorem acDout_eval (n : ℕ) : (fun i => (acDout S i).eval n) = S.outLens n :=
   | 0 => rw [acDout_zero, PolyExpr.eval_add, PolyExpr.eval_const, S.outLens_zero]
   | 1 => rw [acDout_one, S.outLens_one]
 
-/-! ### Strings of the oracles -/
-
-/-- Reading a bit vector across an equality of widths keeps its string:
-`⟦cast h f⟧ = ⟦f⟧` when `a = b`. -/
-theorem ofFn_cast {a b : ℕ} (hab : a = b) (h : (Fin a → Bool) = (Fin b → Bool))
-    (f : Fin a → Bool) : List.ofFn (cast h f) = List.ofFn f := by
-  subst hab
-  rfl
-
-/-- The first half of a `2m`-bit query is its first `m` bits:
-`⟦(splitHalf y).1⟧ = ⟦y⟧.take m`. -/
-theorem ofFn_splitHalf_fst {m : ℕ} (y : Fin (m + m) → Bool) :
-    List.ofFn (FixedLengthScheme.splitHalf y).1 = (List.ofFn y).take m := by
-  rw [FixedLengthScheme.splitHalf_fst]
-  refine List.ext_getElem (by simp only [List.length_ofFn, List.length_take]; omega)
-    fun i h₁ h₂ => ?_
-  rw [List.getElem_ofFn, List.getElem_take, List.getElem_ofFn]
-  rfl
-
-/-- The second half of a `2m`-bit query is its last `m` bits:
-`⟦(splitHalf y).2⟧ = ⟦y⟧.drop m`. -/
-theorem ofFn_splitHalf_snd {m : ℕ} (y : Fin (m + m) → Bool) :
-    List.ofFn (FixedLengthScheme.splitHalf y).2 = (List.ofFn y).drop m := by
-  rw [FixedLengthScheme.splitHalf_snd]
-  refine List.ext_getElem (by simp only [List.length_ofFn, List.length_drop]; omega)
-    fun i h₁ h₂ => ?_
-  rw [List.getElem_ofFn, List.getElem_drop, List.getElem_ofFn]
-  rfl
-
-/-- The all-`false` answer, read at any width, is all-`false`:
-`padFin d ⟦zeroBits m⟧ = zeroBits d`. -/
-theorem padFin_ofFn_zeroBits (d m : ℕ) : padFin d (List.ofFn (zeroBits m)) = zeroBits d := by
-  funext i
-  rw [padFin_apply, ofFn_zeroBits, zeroBits_apply]
-  by_cases hi : (i : ℕ) < m
-  · rw [List.getD_eq_getElem _ _ (by rw [List.length_replicate]; exact hi), List.getElem_replicate]
-  · rw [List.getD_eq_default _ _ (by rw [List.length_replicate]; omega)]
-
-/-- The bit of a one-bit output is the head of its string: `⟦f⟧.headD false = f 0`. -/
-theorem headD_ofFn_one (f : Fin 1 → Bool) : (List.ofFn f).headD false = f 0 := by
-  rw [List.ofFn_succ, List.headD_cons]
-
 /-! ### The hybrid games -/
 
 /-- **The encryption of the selected message:** `E β mm r = padFin (Enc_pk(m_β); r)` for the
@@ -191,11 +129,12 @@ theorem ofFn_select (n : ℕ) (x : Fin ((acDin S 1).eval n) → Bool) (b : Bool)
       msgOf (S.msgLen.eval n) b (List.ofFn x) := by
   have hx : List.ofFn (cast (S.indSpec_challengeDom n) (padFin (S.inLens n 1) (List.ofFn x))) =
       List.ofFn x := by
-    rw [ofFn_cast (S.inLens_one n), GGMRed.ofFn_padFin_of_length (by
+    rw [ofFn_cast (S.inLens_one n), ofFn_padFin_of_length (by
       rw [List.length_ofFn, acDin_one, PolyExpr.eval_add, S.inLens_one])]
   cases b
-  · rw [if_neg Bool.false_ne_true, ofFn_splitHalf_fst, hx, msgOf_eq, if_neg Bool.false_ne_true]
-  · rw [if_pos rfl, ofFn_splitHalf_snd, hx, msgOf_eq, if_pos rfl]
+  · rw [if_neg Bool.false_ne_true, FixedLengthScheme.ofFn_splitHalf_fst, hx, msgOf_eq,
+      if_neg Bool.false_ne_true]
+  · rw [if_pos rfl, FixedLengthScheme.ofFn_splitHalf_snd, hx, msgOf_eq, if_pos rfl]
 
 /-- **The adaptive CPA oracles on T2's codec are a hybrid:** read along the lengths of T2's codec,
 `S.adaptiveIndImpl .cpa b n pk sk κ` is `hybImpl κ (acEnc S n pk) (fun _ => b)`.
@@ -254,9 +193,9 @@ theorem castImpl_adaptiveIndImpl (b : Bool) (n : ℕ) (pk sk : List Bool) (κ :
 `S.adaptiveIndGame .cpa A q κ b n = acHyb S A q κ n (fun _ => b)`.
 
 **Proof sketch.** Fix the key-generation and adversary coins. The adversary codec is a bit codec
-(`indCodec_eq_bitCodec`), its one-bit output is the head of its string (`headD_ofFn_one`), and
-the run transports to T2's codec, whose lengths are equal (`simulate_castImpl_toCompOn`), where the
-oracles are the hybrid (`castImpl_adaptiveIndImpl`). -/
+(`FixedLengthPKScheme.indCodec_eq_bitCodec`), its one-bit output is the head of its string
+(`headD_ofFn_one`), and the run transports to T2's codec, whose lengths are equal
+(`simulate_castImpl_toCompOn`), where the oracles are the hybrid (`castImpl_adaptiveIndImpl`). -/
 theorem adaptiveIndGame_eq_acHyb (A : NUPPT) (q κ : ℕ) (b : Bool) (n : ℕ) :
     S.adaptiveIndGame .cpa A q κ b n = acHyb S A q κ n (fun _ => b) := by
   rw [S.adaptiveIndGame_eq, acHyb_eq]
@@ -265,7 +204,7 @@ theorem adaptiveIndGame_eq_acHyb (A : NUPPT) (q κ : ℕ) (b : Bool) (n : ℕ) :
   congr 1
   funext r
   rw [← castImpl_adaptiveIndImpl S b n (pairFstD (S.gen.runAt n [] rg))
-    (pairSndD (S.gen.runAt n [] rg)) κ, indCodec_eq_bitCodec]
+    (pairSndD (S.gen.runAt n [] rg)) κ, FixedLengthPKScheme.indCodec_eq_bitCodec]
   have key := simulate_castImpl_toCompOn (acDin_eval S n) (acDout_eval S n)
     (PolyExpr.eval_const 1 n)
     (S.adaptiveIndImpl .cpa b n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg))
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/Handler.lean b/TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/Handler.lean
index 4983f860b..470a9e07f 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/Handler.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/Handler.lean
@@ -53,6 +53,7 @@ per inner query is the forwarded challenge; its finalization asks nothing and ou
 namespace TCSlib.Cryptography.Composability.AdaptiveCPA
 
 open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
+open TCSlib.Cryptography.Games.InteractiveHandler (rU rZ rW rS rI rX rL rCnt)
 
 /-! ### Messages, lengths and states -/
 
@@ -125,40 +126,18 @@ theorem acTapes_apply (n : ℕ) (ω : Fin ((cap.mul S.enc.coins).eval n) → Boo
 /-- **Tape `j` is the `j`-th block of the seed:**
 `⟦acTapes S cap n ω j⟧ = (⟦ω⟧.drop (j·ρ(n))).take ρ(n)`.
 
-**Proof sketch.** The coin equivalence keeps the string (`coinsEquivPoly_symm_ofFn`); position `k`
-of block `j` is position `k + ρ·j` of `ω` (`FunFamily.blocks_apply`), which is position `k` of the
-dropped and truncated list. -/
+**Proof sketch.** The coin equivalence keeps the string (`coinsEquivPoly_symm_ofFn`), and block `j`
+of the seed is its `j`-th window (`FunFamily.ofFn_blocks`). -/
 theorem ofFn_acTapes (n : ℕ) (ω : Fin ((cap.mul S.enc.coins).eval n) → Bool)
     (j : Fin (cap.eval n)) :
     List.ofFn (acTapes S cap n ω j) =
       ((List.ofFn ω).drop (j * S.enc.coins.eval n)).take (S.enc.coins.eval n) := by
   rw [acTapes, Equiv.trans_apply, Equiv.arrowCongr_apply, Function.comp_apply, Function.comp_apply,
     Equiv.refl_symm, Equiv.refl_apply, NUPPT.coinsEquivPoly_symm_ofFn]
-  have hj := j.isLt
-  have hle : (j : ℕ) * S.enc.coins.eval n + S.enc.coins.eval n ≤
-      cap.eval n * S.enc.coins.eval n := by
-    have := Nat.mul_le_mul_right (S.enc.coins.eval n) (Nat.succ_le_of_lt hj)
-    rw [Nat.succ_mul] at this
-    exact this
-  refine List.ext_getElem ?_ fun k h₁ h₂ => ?_
-  · simp only [List.length_ofFn, List.length_take, List.length_drop, PolyExpr.eval_mul]
-    omega
-  · rw [List.getElem_ofFn, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
-    refine (FunFamily.blocks_apply _ _ ω j ⟨k, _⟩).trans ?_
-    congr 1
-    refine Fin.ext ?_
-    rw [finProdFinEquiv_apply_val]
-    show k + S.enc.coins.eval n * j = j * S.enc.coins.eval n + k
-    rw [Nat.mul_comm]
-    omega
+  exact FunFamily.ofFn_blocks (cap.eval n) (S.enc.coins.eval n) ω j
 
 /-! ### Strings -/
 
-/-- `⟦padFin k a⟧ = padL k a`, the first `k` bits of `a ++ 0^k` (`ofFn_padFin_eq_take`). -/
-private theorem ofFn_padFin_eq_padL (k : ℕ) (a : List Bool) :
-    List.ofFn (padFin k a) = EnsembleLemmas.padL k a := by
-  rw [EnsembleLemmas.padL_eq, ofFn_padFin_eq_take]
-
 /-- The fields of an encoded state. -/
 private theorem fields_acState (n j : ℕ) (c : Fin (S.ctLen.eval n) → Bool) (hj : j ≤ cap.eval n)
     (hi : ist n ≤ cap.eval n) :
@@ -180,22 +159,6 @@ private theorem fields_acState (n j : ℕ) (c : Fin (S.ctLen.eval n) → Bool) (
 
 /-! ### The round function -/
 
-/-- The parameter `1^n` of a round input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`. -/
-private def rU (w : List Bool) : List Bool := pairFstD (pairFstD w)
-/-- The reduction input `z` (the public key). -/
-private def rZ (w : List Bool) : List Bool := pairFstD (pairSndD (pairFstD w))
-/-- The seed `ω`. -/
-private def rW (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD w))
-/-- The state `s`. -/
-private def rS (w : List Bool) : List Bool := pairFstD (pairSndD w)
-/-- The oracle index `1^i`. -/
-private def rI (w : List Bool) : List Bool := pairFstD (pairFstD (pairSndD (pairSndD w)))
-/-- The query `x`. -/
-private def rX (w : List Bool) : List Bool := pairSndD (pairFstD (pairSndD (pairSndD w)))
-/-- The outer log `L` of the call. -/
-private def rL (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))
-/-- The count `1^j` of the state. -/
-private def rCnt (w : List Bool) : List Bool := pairFstD (rS w)
 /-- The advised index `1^{i⋆}` of the state. -/
 private def rIst (w : List Bool) : List Bool := pairFstD (pairSndD (rS w))
 /-- The latest ciphertext of the state. -/
@@ -239,14 +202,14 @@ private def acRun (w : List Bool) : List Bool :=
 private theorem polyTimeComputable_acRun : PolyTimeComputable (acRun S cap) := by
   have hF := polyTimeComputable_pairFstD
   have hD := polyTimeComputable_pairSndD
-  have hU : PolyTimeComputable rU := hF.comp hF
-  have hZ : PolyTimeComputable rZ := hF.comp (hD.comp hF)
-  have hW : PolyTimeComputable rW := hD.comp (hD.comp hF)
-  have hS : PolyTimeComputable rS := hF.comp hD
-  have hI : PolyTimeComputable rI := hF.comp (hF.comp (hD.comp hD))
-  have hX : PolyTimeComputable rX := hD.comp (hF.comp (hD.comp hD))
-  have hL : PolyTimeComputable rL := hD.comp (hD.comp hD)
-  have hCnt : PolyTimeComputable rCnt := hF.comp hS
+  have hU : PolyTimeComputable rU := InteractiveHandler.polyTimeComputable_rU
+  have hZ : PolyTimeComputable rZ := InteractiveHandler.polyTimeComputable_rZ
+  have hW : PolyTimeComputable rW := InteractiveHandler.polyTimeComputable_rW
+  have hS : PolyTimeComputable rS := InteractiveHandler.polyTimeComputable_rS
+  have hI : PolyTimeComputable rI := InteractiveHandler.polyTimeComputable_rI
+  have hX : PolyTimeComputable rX := InteractiveHandler.polyTimeComputable_rX
+  have hL : PolyTimeComputable rL := InteractiveHandler.polyTimeComputable_rL
+  have hCnt : PolyTimeComputable rCnt := InteractiveHandler.polyTimeComputable_rCnt
   have hIst : PolyTimeComputable rIst := hF.comp (hD.comp hS)
   have hLat : PolyTimeComputable (rLat S) :=
     ((polyTimeComputable_pairTakePoly S.ctLen).comp (hU.pairEncode (hD.comp (hD.comp hS)))).congr
@@ -401,7 +364,7 @@ theorem acHandler_finish (n : ℕ) (z : List Bool)
   rw [acFin, InteractiveHandler.finInput_eq, pairSndD_pairEncode, pairSndD_pairEncode,
     pairFstD_pairEncode]
   have hw : List.ofFn (padFin ((acHandler S cap ist).outLen.eval n) (List.ofFn a)) = List.ofFn a :=
-    GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, acHandler_outLen])
+    ofFn_padFin_of_length (by rw [List.length_ofFn, acHandler_outLen])
   exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).symm.trans
     (decodeBitMove_ret _ _ _ _)
 
@@ -411,28 +374,6 @@ section Answers
 
 variable (n : ℕ) (z : List Bool) (ω : Fin ((acHandler S cap ist).seedLen.eval n) → Bool)
 
-/-- A call whose first round returns `y ‖ s'` is answered `y` with new state `s'`. -/
-private theorem impl_of_ret {i : Fin 2} (x : Fin ((acDin S i).eval n) → Bool)
-    (s : Fin ((acStLen S cap).eval n) → Bool) (y : Fin ((acDout S i).eval n) → Bool)
-    (s' : Fin ((acStLen S cap).eval n) → Bool)
-    (h : acRun S cap (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x) []) =
-      pairEncode [true] (List.ofFn y ++ List.ofFn s')) :
-    (acHandler S cap ist).impl n z ω i x s = .pure (y, s') := by
-  rw [InteractiveHandler.impl_apply, InteractiveHandler.call_eq, acHandler_perCall,
-    PolyExpr.eval_const]
-  rw [buildComp_succ_of_ret (a := Fin.append y s') (by
-    show decodeBitMove _ _ _ (acRun S cap _) = _
-    rw [MachineCodec.encodeLog_nil, h, ← List.ofFn_fin_append]
-    exact decodeBitMove_ret _ _ _ _), OracleComp.pure_bind]
-  congr 2
-  · funext j
-    exact Fin.append_left y s' j
-  · funext j
-    exact Fin.append_right y s' j
-
-/-- The index word of a challenge query is `[true]`. -/
-private theorem replicate_one : List.replicate ((1 : Fin 2) : ℕ) true = [true] := rfl
-
 /-- The round input of a call, field by field. -/
 private theorem fields_input {i : Fin 2} (x : List Bool) (L : List Bool) (j : ℕ)
     (c : Fin (S.ctLen.eval n) → Bool) (hj : j ≤ cap.eval n) (hi : ist n ≤ cap.eval n) :
@@ -442,27 +383,29 @@ private theorem fields_input {i : Fin 2} (x : List Bool) (L : List Bool) (j : 
       rL w = L ∧ rCnt w = List.replicate j true ∧ rIst w = List.replicate (ist n) true ∧
       rLat S w = List.ofFn c := by
   obtain ⟨h₁, h₂, h₃⟩ := fields_acState S cap ist n j c hj hi
-  simp only [InteractiveHandler.input_eq, rU, rZ, rW, rS, rI, rX, rL, rCnt, rIst, rLat,
-    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, h₁, h₂, h₃, and_self]
+  simp only [InteractiveHandler.rU_input, InteractiveHandler.rZ_input,
+    InteractiveHandler.rW_input, InteractiveHandler.rS_input, InteractiveHandler.rI_input,
+    InteractiveHandler.rX_input, InteractiveHandler.rL_input, InteractiveHandler.rCnt_input, rIst,
+    rLat, List.length_replicate, h₁, h₂, h₃, and_self]
 
 /-- **Decryption is refused:** `(acHandler S cap ist).impl n z ω 0 x s = pure (0, s)`. -/
 theorem acHandler_impl_dec (x : Fin ((acDin S 0).eval n) → Bool)
     (s : Fin ((acHandler S cap ist).stateLen.eval n) → Bool) :
     (acHandler S cap ist).impl n z ω 0 x s = .pure (zeroBits _, s) := by
-  refine impl_of_ret S cap ist n z ω x s _ _ ?_
+  refine InteractiveHandler.impl_of_ret _ n z ω x s _ _ ?_
+  show acRun S cap _ = _
   have hI : rI (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) (0 : Fin 2) (List.ofFn x)
       []) =
-      [] := by
-    simp only [InteractiveHandler.input_eq, rI, pairFstD_pairEncode, pairSndD_pairEncode]
-    rfl
+      [] :=
+    InteractiveHandler.rI_input _ _ _ _ _ _ _
   have hU : rU (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) (0 : Fin 2) (List.ofFn x)
       []) =
-      List.replicate n true := by
-    simp only [InteractiveHandler.input_eq, rU, pairFstD_pairEncode]
+      List.replicate n true :=
+    InteractiveHandler.rU_input _ _ _ _ _ _ _
   have hS : rS (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) (0 : Fin 2) (List.ofFn x)
       []) =
-      List.ofFn s := by
-    simp only [InteractiveHandler.input_eq, rS, pairFstD_pairEncode, pairSndD_pairEncode]
+      List.ofFn s :=
+    InteractiveHandler.rS_input _ _ _ _ _ _ _
   rw [acRun, hI, List.headD_nil, if_neg Bool.false_ne_true, hU, hS, List.length_replicate,
     ofFn_zeroBits, acDout_zero]
 
@@ -473,13 +416,14 @@ theorem acHandler_impl_full (x : Fin ((acDin S 1).eval n) → Bool)
     (acHandler S cap ist).impl n z ω 1 x (acHState S cap ist n (cap.eval n) c) =
       .pure (padFin ((acDout S 1).eval n) (List.ofFn c), acHState S cap ist n (cap.eval n) c) := by
   rw [acHState_eq]
-  refine impl_of_ret S cap ist n z ω x _ _ _ ?_
+  refine InteractiveHandler.impl_of_ret _ n z ω x _ _ _ ?_
+  show acRun S cap _ = _
   obtain ⟨hU, -, -, hS, hI, -, -, hCnt, -, hLat⟩ :=
     fields_input S cap ist n z ω (i := 1) (List.ofFn x) [] (cap.eval n) c le_rfl hi
   have hh : ([true].headD false = true) := rfl
   have hc : decide (cap.eval n ≤ cap.eval n) = true := decide_eq_true le_rfl
-  rw [acRun, hI, replicate_one, hU, hCnt, hS, hLat, List.length_replicate, List.length_replicate,
-    if_pos hh, if_pos hc, GGMRed.ofFn_padFin_of_length (List.length_ofFn)]
+  rw [acRun, hI, Fin.val_one, List.replicate_one, hU, hCnt, hS, hLat, List.length_replicate,
+    List.length_replicate, if_pos hh, if_pos hc, ofFn_padFin_of_length (List.length_ofFn)]
 
 /-- **A fresh challenge other than the advised one is encrypted by the handler:** from the state
 `acState j c` with `j < cap(n)` and `j ≠ i⋆(n)`, the challenge `x` is answered with
@@ -499,25 +443,27 @@ theorem acHandler_impl_eager (x : Fin ((acDin S 1).eval n) → Bool) (j : ℕ)
       (S.enc.runAt n (pairEncode z (msgOf (S.msgLen.eval n) (decide (j < ist n)) (List.ofFn x)))
         (acSeedTapes S cap ist n ω ⟨j, hj⟩)) := ⟨_, rfl⟩
   rw [← hc']
-  refine impl_of_ret S cap ist n z ω x _ _ _ ?_
+  refine InteractiveHandler.impl_of_ret _ n z ω x _ _ _ ?_
+  show acRun S cap _ = _
   obtain ⟨hU, hZ, hW, hS, hI, hX, -, hCnt, hIst, -⟩ :=
     fields_input S cap ist n z ω (i := 1) (List.ofFn x) [] j c hj.le hi
   have hEnc : rEnc S (InteractiveHandler.input n z (List.ofFn ω)
       (List.ofFn (acState S cap ist n j c)) (1 : Fin 2) (List.ofFn x) []) = List.ofFn c' := by
-    rw [hc', ofFn_padFin_eq_padL, rEnc, hU, List.length_replicate, NUPPT.Uniform.runAt_eq
-      S.enc_uniform, NUPPT.advInput_eq, ofFn_acSeedTapes, rTape, rMsg, hZ, hW, hCnt, hIst, hU, hX,
-      List.length_replicate, List.length_replicate, List.length_replicate, msgOf_eq]
+    rw [hc', EnsembleLemmas.ofFn_padFin_eq_padL, rEnc, hU, List.length_replicate,
+      NUPPT.Uniform.runAt_eq S.enc_uniform, NUPPT.advInput_eq, ofFn_acSeedTapes, rTape, rMsg, hZ,
+      hW, hCnt, hIst, hU, hX, List.length_replicate, List.length_replicate, List.length_replicate,
+      msgOf_eq]
   have hNew : rNew S cap (InteractiveHandler.input n z (List.ofFn ω)
       (List.ofFn (acState S cap ist n j c)) (1 : Fin 2) (List.ofFn x) []) (List.ofFn c') =
       List.ofFn (acState S cap ist n (j + 1) c') := by
-    rw [rNew, hU, hCnt, hIst, List.length_replicate, acState_eq, ofFn_padFin_eq_padL,
-      List.replicate_succ]
+    rw [rNew, hU, hCnt, hIst, List.length_replicate, acState_eq,
+      EnsembleLemmas.ofFn_padFin_eq_padL, List.replicate_succ]
   have hh : ([true].headD false = true) := rfl
   have hc1 : ¬ (decide (cap.eval n ≤ j) = true) := by rw [decide_eq_true_eq]; omega
   have hc2 : ¬ (decide (j = ist n) = true) := by rw [decide_eq_true_eq]; exact hne
-  rw [acRun, hI, replicate_one, hU, hCnt, hIst, hEnc, hNew, List.length_replicate,
+  rw [acRun, hI, Fin.val_one, List.replicate_one, hU, hCnt, hIst, hEnc, hNew, List.length_replicate,
     List.length_replicate, List.length_replicate, if_pos hh, if_neg hc1, if_neg hc2,
-    GGMRed.ofFn_padFin_of_length (List.length_ofFn)]
+    ofFn_padFin_of_length (List.length_ofFn)]
 
 /-- **The advised fresh challenge is forwarded:** from the state `acState j c` with
 `j = i⋆(n) < cap(n)`, the challenge `x` is asked to the outer challenge oracle, and its answer `y`
@@ -542,8 +488,8 @@ theorem acHandler_impl_forward (x : Fin ((acDin S 1).eval n) → Bool) (j : ℕ)
     have hc1 : ¬ (decide (cap.eval n ≤ j) = true) := by rw [decide_eq_true_eq]; omega
     have hc2 : decide (j = ist n) = true := decide_eq_true heq
     have hc3 : decide (([] : List Bool) = []) = true := decide_eq_true rfl
-    rw [acRun, hI, replicate_one, hU, hCnt, hIst, hL, hX, MachineCodec.encodeLog_nil, hlen, hlen,
-      hlen, if_pos hh, if_neg hc1, if_pos hc2, if_pos hc3, ← replicate_one]
+    rw [acRun, hI, Fin.val_one, List.replicate_one, hU, hCnt, hIst, hL, hX,
+      MachineCodec.encodeLog_nil, hlen, hlen, hlen, if_pos hh, if_neg hc1, if_pos hc2, if_pos hc3]
     exact decodeBitMove_query (fun j => (acDin S j).eval n) (fun j => (acDout S j).eval n) _ 1 x),
     OracleComp.query_bind]
   congr 1
@@ -567,8 +513,9 @@ theorem acHandler_impl_forward (x : Fin ((acDin S 1).eval n) → Bool) (j : ℕ)
         (List.ofFn (acState S cap ist n j c)) (1 : Fin 2) (List.ofFn x)
         ((bitCodec (fun j => (acDin S j).eval n) (fun j => (acDout S j).eval n) 0).encodeLog
           ([] ++ [⟨1, x, y⟩]))) (List.ofFn y) = List.ofFn s' := by
-      rw [rNew, hU, hCnt, hIst, List.length_replicate, hs', acState_eq, ofFn_padFin_eq_padL,
-        List.replicate_succ, GGMRed.ofFn_padFin_of_length (List.length_ofFn)]
+      rw [rNew, hU, hCnt, hIst, List.length_replicate, hs', acState_eq,
+        EnsembleLemmas.ofFn_padFin_eq_padL, List.replicate_succ,
+        ofFn_padFin_of_length (List.length_ofFn)]
     have hFwd : rFwd (InteractiveHandler.input n z (List.ofFn ω)
         (List.ofFn (acState S cap ist n j c)) (1 : Fin 2) (List.ofFn x)
         ((bitCodec (fun j => (acDin S j).eval n) (fun j => (acDout S j).eval n) 0).encodeLog
@@ -581,8 +528,8 @@ theorem acHandler_impl_forward (x : Fin ((acDin S 1).eval n) → Bool) (j : ℕ)
         [] = []) = true) := by
       rw [decide_eq_true_eq]
       exact pairEncode_ne_nil _ _
-    rw [acRun, hI, replicate_one, hU, hCnt, hIst, hFwd, hNew, hL, hlog, hlen, hlen, hlen,
-      if_pos hh, if_neg hc1, if_pos hc2, if_neg hc3, ← List.ofFn_fin_append]
+    rw [acRun, hI, Fin.val_one, List.replicate_one, hU, hCnt, hIst, hFwd, hNew, hL, hlog, hlen,
+      hlen, hlen, if_pos hh, if_neg hc1, if_pos hc2, if_neg hc3, ← List.ofFn_fin_append]
     exact decodeBitMove_ret _ _ _ _)]
   rw [OracleComp.pure_bind]
   congr 2
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/Hybrid.lean b/TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/Hybrid.lean
index d6b068575..244b72559 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/Hybrid.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/Hybrid.lean
@@ -24,25 +24,21 @@ answers all-`false`.
 * `tapeImpl κ E sel T kst` answers the `j`-th fresh challenge with the coins `T j` given in
   advance, except the `kst`-th, for which it samples coins. Drawing `T` uniformly gives the
   distribution of `hybImpl` (`expect_tapeImpl`); the proof resamples one coordinate at a time
-  (`expect_sample_update`), using that the run from a history of length `j + 1` ignores the
+  (`ProbComp.expect_sample_coord`), using that the run from a history of length `j + 1` ignores the
   coins `T j` (`simulate_tapeImpl_congr`).
 
-Two generic tools complete the file: `castImpl` transports an implementation along equal
-length functions (`simulate_castImpl_toCompOn`), and `simulate_eq_of_abs` relates two
-implementations through an abstraction of their states.
+The generic tools it uses live in the Games layer: `Games.castImpl` transports an implementation
+along equal length functions (`Games.simulate_castImpl_toCompOn`), and `Games.simulate_eq_of_abs`
+relates two implementations through an abstraction of their states.
 
 ## Main definitions
 
-* `AdaptiveCPA.castImpl`: an implementation read along equal length functions.
 * `AdaptiveCPA.hybImpl`, `AdaptiveCPA.tapeImpl`: the hybrid challenge oracles.
 * `AdaptiveCPA.extTape`: a finite family of coins, extended to every index.
 
 ## Main results
 
-* `AdaptiveCPA.simulate_castImpl_toCompOn`: transport of a machine's run between two codecs.
-* `AdaptiveCPA.simulate_eq_of_abs`: simulation through a state abstraction.
 * `AdaptiveCPA.hybImpl_congr`: only the selector's values below the cap matter.
-* `AdaptiveCPA.expect_sample_update`: resampling one coordinate of a uniform tuple.
 * `AdaptiveCPA.expect_tapeImpl`: coins given in advance have the lazy distribution.
 
 ## References
@@ -55,96 +51,6 @@ namespace TCSlib.Cryptography.Composability.AdaptiveCPA
 
 open Complexity TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim
 
-/-! ### Transport along equal lengths -/
-
-section Transport
-
-variable {k : ℕ} {σ : Type}
-
-/-- **An implementation read along length functions:** answer the query `x` to oracle `i` of
-`bitSpec ins outs` by asking `O` the query `padFin (ins' i) ⟦x⟧` and reading its answer `y` as
-`padFin (outs i) ⟦y⟧`. When `ins = ins'` and `outs = outs'` this is `O` itself
-(`castImpl_self`). -/
-def castImpl {ins ins' outs outs' : Fin k → ℕ} (O : QueryImpl (bitSpec ins' outs') σ unifSpec) :
-    QueryImpl (bitSpec ins outs) σ unifSpec :=
-  fun i x s => (O i (padFin (ins' i) (List.ofFn x)) s).bind fun p =>
-    .pure (padFin (outs i) (List.ofFn p.1), p.2)
-
-/-- The defining equation of `castImpl`: `castImpl O i x s =
-(O i (padFin (ins' i) ⟦x⟧) s).bind fun p => pure (padFin (outs i) ⟦p.1⟧, p.2)`. -/
-theorem castImpl_eq {ins ins' outs outs' : Fin k → ℕ}
-    (O : QueryImpl (bitSpec ins' outs') σ unifSpec) (i : Fin k) (x : Fin (ins i) → Bool)
-    (s : σ) :
-    castImpl (ins := ins) (outs := outs) O i x s =
-      (O i (padFin (ins' i) (List.ofFn x)) s).bind fun p =>
-        .pure (padFin (outs i) (List.ofFn p.1), p.2) :=
-  rfl
-
-/-- Read along the same lengths, an implementation is unchanged: `castImpl O = O`. -/
-theorem castImpl_self {ins outs : Fin k → ℕ} (O : QueryImpl (bitSpec ins outs) σ unifSpec) :
-    castImpl (ins := ins) (outs := outs) O = O := by
-  funext i x s
-  rw [castImpl_eq, padFin_ofFn]
-  simp only [padFin_ofFn]
-  exact OracleComp.bind_pure _
-
-/-- **Transport of a machine's run:** if `ins = ins'`, `outs = outs'` and `d = d'`, simulating
-`castImpl O` on the run of `M` through `bitCodec ins outs d` gives, with outputs read as lists,
-the simulation of `O` on the run of `M` through `bitCodec ins' outs' d'`.
-
-**Proof sketch.** Substitute the equalities; then `castImpl O = O` (`castImpl_self`). -/
-theorem simulate_castImpl_toCompOn {ins ins' outs outs' : Fin k → ℕ} {d d' : ℕ}
-    (hi : ins = ins') (ho : outs = outs') (hd : d = d')
-    (O : QueryImpl (bitSpec ins' outs') σ unifSpec) (M : NUPPT) (n q : ℕ) (x : List Bool)
-    (r : M.Coins n) (s : σ) :
-    (simulate (castImpl (ins := ins) (outs := outs) O)
-        (M.toCompOn (bitCodec ins outs d) n q x r) s).bind
-        (fun p => .pure (List.ofFn p.1, p.2)) =
-      (simulate O (M.toCompOn (bitCodec ins' outs' d') n q x r) s).bind
-        (fun p => .pure (List.ofFn p.1, p.2)) := by
-  subst hi ho hd
-  rw [castImpl_self]
-
-/-- **Transport of a machine's run, in expectation:** for every function `G` of the output (read
-as a list) and the final state, `simulate_castImpl_toCompOn` in the form
-`𝔼[G (⟦p.1⟧, p.2)]` over the two simulations. -/
-theorem expect_simulate_castImpl_toCompOn {ins ins' outs outs' : Fin k → ℕ} {d d' : ℕ}
-    (hi : ins = ins') (ho : outs = outs') (hd : d = d')
-    (O : QueryImpl (bitSpec ins' outs') σ unifSpec) (M : NUPPT) (n q : ℕ) (x : List Bool)
-    (r : M.Coins n) (s : σ) (G : List Bool × σ → ℝ) :
-    expect (simulate (castImpl (ins := ins) (outs := outs) O)
-        (M.toCompOn (bitCodec ins outs d) n q x r) s) (fun p => G (List.ofFn p.1, p.2)) =
-      expect (simulate O (M.toCompOn (bitCodec ins' outs' d') n q x r) s)
-        (fun p => G (List.ofFn p.1, p.2)) := by
-  have h := congrArg (fun c => expect c G) (simulate_castImpl_toCompOn hi ho hd O M n q x r s)
-  simp only [expect_bind, expect_pure] at h
-  exact h
-
-end Transport
-
-/-! ### Simulation through a state abstraction -/
-
-/-- **Simulation through an abstraction of the state:** if every call of `impl₁` from the
-abstract state `f s` is the call of `impl₂` from `s` with its new state abstracted, the same holds
-for whole simulations: `simulate impl₁ c (f s) =
-(simulate impl₂ c s).bind fun p => pure (p.1, f p.2)`.
-
-**Proof sketch.** Induction on `c`; at a query, rewrite the call by the hypothesis and use the
-induction hypothesis on each continuation after associativity. -/
-theorem simulate_eq_of_abs {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
-    {σ₁ σ₂ α : Type} (impl₁ : QueryImpl spec σ₁ spec') (impl₂ : QueryImpl spec σ₂ spec')
-    (f : σ₂ → σ₁) (h : ∀ i x s, impl₁ i x (f s) = (impl₂ i x s).bind fun p => .pure (p.1, f p.2))
-    (c : OracleComp spec α) (s : σ₂) :
-    simulate impl₁ c (f s) = (simulate impl₂ c s).bind fun p => .pure (p.1, f p.2) := by
-  induction c generalizing s with
-  | pure a => simp only [simulate_pure, OracleComp.pure_bind]
-  | query i x k ih =>
-    rw [simulate_query, simulate_query, h, OracleComp.bind_assoc, OracleComp.bind_assoc]
-    congr 1
-    funext p
-    rw [OracleComp.pure_bind]
-    exact ih p.1 p.2
-
 /-! ### The hybrid oracles -/
 
 section Hybrid
@@ -321,34 +227,6 @@ theorem extTape_update {κ : ℕ} (T : Fin κ → C) (j : Fin κ) (r : C) {m : 
 
 variable [Fintype C]
 
-/-- **Resampling one coordinate of a uniform tuple:** if `F r T` ignores the coordinate `j` of
-`T`, then `𝔼_T F (T j) T = 𝔼_r 𝔼_T F r T`.
-
-**Proof sketch.** The map `(T, r) ↦ (T[j ↦ r], T j)` is an involution of `(Fin κ → C) × C`, so
-it preserves the uniform average (`expect_sample_equiv`). It carries `F (T j) T` to
-`F r (T[j ↦ r]) = F r T`. Split the products (`expect_sample_prod`), drop the unused sample
-(`expect_const`) and exchange the order (`expect_sample_comm`). -/
-theorem expect_sample_update {κ : ℕ} (j : Fin κ) (F : C → (Fin κ → C) → ℝ)
-    (hF : ∀ r r' T, F r (Function.update T j r') = F r T) :
-    expect (sample (Fin κ → C)) (fun T => F (T j) T) =
-      expect (sample C) fun r => expect (sample (Fin κ → C)) fun T => F r T := by
-  let e : (Fin κ → C) × C ≃ (Fin κ → C) × C :=
-    { toFun := fun p => (Function.update p.1 j p.2, p.1 j)
-      invFun := fun p => (Function.update p.1 j p.2, p.1 j)
-      left_inv := fun p => by
-        simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
-      right_inv := fun p => by
-        simp only [Function.update_self, Function.update_idem, Function.update_eq_self] }
-  have he := expect_sample_equiv e (fun p => F (p.1 j) p.1)
-  have hl : (fun p : (Fin κ → C) × C => F ((e p).1 j) (e p).1) = fun p => F p.2 p.1 := by
-    funext p
-    show F ((Function.update p.1 j p.2) j) (Function.update p.1 j p.2) = F p.2 p.1
-    rw [Function.update_self, hF]
-  rw [hl, expect_sample_prod, expect_sample_prod] at he
-  rw [← expect_sample_comm, he]
-  refine congrArg _ (funext fun T => ?_)
-  exact (expect_const _ _).symm
-
 variable {ins outs : Fin 2 → ℕ} {L : ℕ}
 
 /-- **Coins in advance have the lazy distribution:** for every `kst` and every function `G` of
@@ -361,7 +239,8 @@ at the cap are answered alike. The `kst`-th fresh challenge samples coins on bot
 the order of the two samples (`expect_sample_comm`) and apply the induction hypothesis. Another
 fresh challenge, the `j`-th, reads `T j` on the left; the continuation runs from a history of
 length `j + 1`, so it ignores `T j` (`simulate_tapeImpl_congr`, `extTape_update`), and
-`expect_sample_update` replaces `T j` by fresh coins; then apply the induction hypothesis. -/
+`ProbComp.expect_sample_coord` replaces `T j` by fresh coins; then apply the induction
+hypothesis. -/
 theorem expect_tapeImpl (κ : ℕ) (E : Bool → (Fin (ins 1) → Bool) → C → (Fin L → Bool))
     (sel : ℕ → Bool) (kst : ℕ) {α : Type} (G : α × List (Fin L → Bool) → ℝ)
     (c : OracleComp (bitSpec ins outs) α) (h : List (Fin L → Bool)) :
@@ -390,7 +269,7 @@ theorem expect_tapeImpl (κ : ℕ) (E : Bool → (Fin (ins 1) → Bool) → C 
           let j : Fin κ := ⟨h.length, hh⟩
           have hj : ∀ T : Fin κ → C, extTape T h.length = T j := fun T => extTape_of_lt T hh
           simp only [hj]
-          refine (expect_sample_update j (fun r T => expect (simulate
+          refine (expect_sample_coord j (fun r T => expect (simulate
             (tapeImpl κ E sel (extTape T) kst) (k (padFin (outs 1) (List.ofFn
               (E (sel h.length) x r)))) (E (sel h.length) x r :: h)) G) ?_).trans ?_
           · intro r r' T
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/Reduction.lean b/TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/Reduction.lean
index 42f096262..ab7315389 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/Reduction.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/Reduction.lean
@@ -3,6 +3,7 @@ Copyright (c) 2026 TCSlib contributors. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 -/
 import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Games
+import TCSlib.Cryptography.Foundations.BitLists
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -141,7 +142,7 @@ private theorem comp_acAbs (b : Bool) (n : ℕ) (hist : ist n ≤ cap.eval n) (p
         simp only [OracleComp.pure_bind, simulate_pure]
         have he : padFin (S.ctLen.eval n) (List.ofFn (padFin ((acDout S 1).eval n)
             (List.ofFn (acEnc S n pk b x r)))) = acEnc S n pk b x r := by
-          rw [GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, acDout_one]), padFin_ofFn]
+          rw [ofFn_padFin_of_length (by rw [List.length_ofFn, acDout_one]), padFin_ofFn]
         rw [he, acAbs, List.length_cons, Nat.min_eq_left (by omega), List.headD_cons,
           getElem?_reverse_cons, if_pos hk.symm]
       · -- another fresh challenge: the handler's own encryption with its tape
@@ -178,7 +179,7 @@ adversary's coins `r` and the handler's seed `ω` fixed, the probability that `B
 the oracles of bit `b` outputs `1` is the expectation of `A`'s bit against `H_{i⋆+b}` with the
 handler's tapes in advance and the lazy slot `i⋆`.
 
-**Proof sketch.** Transport `B`'s run to T2's codec (`indCodec_eq_bitCodec`,
+**Proof sketch.** Transport `B`'s run to T2's codec (`FixedLengthPKScheme.indCodec_eq_bitCodec`,
 `expect_simulate_castImpl_toCompOn`), replace it by the reduction (T2's equation `hφ`, with
 `acHandler_advInput` and `acHandler_finish`), compose the two simulations (`simulate_bind`,
 `simulate_comp`) and pass to the hybrid through the state abstraction (`init_acAbs`,
@@ -213,7 +214,7 @@ private theorem prob_red_tape (hist : ist n ≤ cap.eval n)
       fun res => if (List.ofFn res.1).headD false = true then (1 : ℝ) else 0 := by
     funext res
     rw [prob_pure, headD_ofFn_one]
-  rw [prob_bind, indCodec_eq_bitCodec, h1]
+  rw [prob_bind, FixedLengthPKScheme.indCodec_eq_bitCodec, h1]
   refine (expect_simulate_castImpl_toCompOn (acDin_eval S n) (acDout_eval S n) hd
     (S.indImpl .cpa b n pk sk) B n _ pk (φ (ω, r)) none
     (fun p => if p.1.headD false = true then (1 : ℝ) else 0)).symm.trans ?_
@@ -225,7 +226,7 @@ private theorem prob_red_tape (hist : ist n ≤ cap.eval n)
     simulate_eq_of_abs _ _ (acAbs S cap ist n) (comp_acAbs S cap ist b n hist pk sk ω),
     expect_bind]
   refine congrArg _ (funext fun a => ?_)
-  rw [expect_pure, GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, acHandler_outLen])]
+  rw [expect_pure, ofFn_padFin_of_length (by rw [List.length_ofFn, acHandler_outLen])]
 
 /-- **`B`'s game is the hybrid `H_{i⋆+b}`:** if `B` is the machine of T2 for the handler
 `acHandler S cap ist` (with the coin bijection `φ` at `n`) and `i⋆(n) ≤ cap(n)`, then `B`'s
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA.lean b/TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA.lean
index 72e46ec27..4c13844fe 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA.lean
@@ -3,7 +3,7 @@ Copyright (c) 2026 TCSlib contributors. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 -/
 import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA
-import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA.Eager
+import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.PaddedCPA
 import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA.Planted
 import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA.QueryHandler
 
@@ -35,8 +35,6 @@ depend on the public key. The proof below therefore goes back to single-bit secu
 
 ## Contents
 
-* `BitwiseCPA/Eager`: eager challenge coins under CPA, resampling one coordinate of a uniform
-  tuple, and readers of the padded encryptor.
 * `BitwiseCPA/Planted`: the planted bitwise challenge answer and the reduction's final bit.
 * `BitwiseCPA/QueryHandler`: the query-recording handler with advice and its machine by T1.
 
@@ -82,43 +80,36 @@ private noncomputable def hybGame (S : BitPublicKeyScheme) (L : PolyExpr)
     (A.toCompOn ((S.bitwise.padded L hL hmsg).indCodec n) n q
       (pairFstD (S.gen.runAt n [] rg)) r) none).1 0)
 
-/-- The bitwise encryptor on a coin list: the tuple of the single-bit encryptions with the
-consecutive coin segments (`bitwise_enc`, `bitwise_enc_runAtL`). -/
-private theorem bitwise_runAtL (S : BitPublicKeyScheme) (n : ℕ) (pk : List Bool)
-    (m : Fin n → Bool) (r : List Bool) :
-    S.bitwise.enc.runAtL n (pairEncode pk (List.ofFn m)) r =
-      PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
-        S.enc.runAtL n (pairEncode pk [m i]) (coinBlock (S.enc.coinLen n) i r)) := by
-  rw [BitPublicKeyScheme.bitwise_enc]
-  exact BitPublicKeyScheme.bitwise_enc_runAtL S n pk m r
-
 /-- The bitwise encryptor on the coin blocks `v`: the tuple of the single-bit encryptions with
-coins `v_i` (`bitwiseEncCoins_ofFn`, `coinBlock_ofFn_coinBlocks`). -/
+coins `v_i` (`bitwiseEncCoins_ofFn`, `bitwise_enc`, `bitwise_enc_runAtL`,
+`coinBlock_ofFn_coinBlocks`). -/
 private theorem bitwise_runAt_blocks (S : BitPublicKeyScheme) (n : ℕ) (pk : List Bool)
     (m : Fin n → Bool) (v : Fin n → S.enc.Coins n) :
     S.bitwise.enc.runAt n (pairEncode pk (List.ofFn m)) (S.bitwiseEncCoins n v) =
       PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
         S.enc.runAt n (pairEncode pk [m i]) (v i)) := by
-  rw [NUPPT.runAt_eq, bitwise_runAtL, BitPublicKeyScheme.bitwiseEncCoins_ofFn]
+  rw [NUPPT.runAt_eq, BitPublicKeyScheme.bitwiseEncCoins_ofFn, BitPublicKeyScheme.bitwise_enc,
+    BitPublicKeyScheme.bitwise_enc_runAtL]
   refine congrArg (fun l => PrivateKeyScheme.encodeList (List.ofFn l)) (funext fun i => ?_)
   rw [coinBlock_ofFn_coinBlocks, ← NUPPT.runAt_eq]
 
-/-- The selected half of a challenge query, as the list of its `n` bits read from the query. -/
+/-- The selected half of a challenge query, as the list of its `n` bits read from the query
+(the published `FixedLengthScheme.ofFn_splitHalf_fst`, `_snd`). -/
 private theorem ofFn_half {k n : ℕ} (hk : k = n) (b : Bool) (mm : Fin (k + k) → Bool) :
     List.ofFn (if b then (FixedLengthScheme.splitHalf mm).2
       else (FixedLengthScheme.splitHalf mm).1) =
       List.ofFn (fun i : Fin n => (List.ofFn mm).getD ((if b then n else 0) + i) false) := by
   subst hk
-  apply List.ext_getElem
-  · cases b <;> simp
-  · intro t h₁ h₂
-    have ht : t < k := by cases b <;> simpa using h₂
-    cases b
-    · simp [FixedLengthScheme.splitHalf_fst, List.getD_eq_getElem?_getD]
-      rw [dif_pos (by omega)]
-      rfl
-    · simp [FixedLengthScheme.splitHalf_snd, List.getD_eq_getElem?_getD]
-      exact congrArg mm (Fin.ext (Nat.add_comm _ _))
+  cases b
+  · rw [if_neg Bool.false_ne_true, FixedLengthScheme.ofFn_splitHalf_fst]
+    refine List.ext_getElem (by simp) fun t h₁ h₂ => ?_
+    have ht : t < k := by simpa using h₂
+    simp [List.getD_eq_getElem?_getD]
+    rw [dif_pos (by omega)]
+    rfl
+  · rw [if_pos rfl, FixedLengthScheme.ofFn_splitHalf_snd]
+    refine List.ext_getElem (by simp) fun t h₁ h₂ => ?_
+    simp [List.getD_eq_getElem?_getD]
 
 /-- A list of `n + n` bits is its first and its last `n` bits. -/
 private theorem ofFn_getD_split {n : ℕ} (l : List Bool) (hl : l.length = n + n) :
@@ -140,9 +131,9 @@ private theorem ofFn_getD_split {n : ℕ} (l : List Bool) (hl : l.length = n + n
 `Pr[Ind_b = 1] = Pr[H_{j_b} = 1]` with `j_0 = 0`, `j_1 = n`.
 
 **Proof sketch.** Eager coins (`expect_simulate_indImpl_cpa`); the padded bitwise encryptor pads
-the tuple of single-bit encryptions (`padded_enc_runAt`, `bitwise_runAt_blocks`) on the coin
-blocks `v` (the bijection `bitwiseEncCoins`, then `coinsCongr`), and bit `i` of the selected
-half is `l_{n+i}` for `b = 1` and `l_i` for `b = 0` (`ofFn_half`). -/
+the tuple of single-bit encryptions (`PublicKeyScheme.padded_enc_runAt`, `bitwise_runAt_blocks`) on
+the coin blocks `v` (the bijection `bitwiseEncCoins`, then `coinsCongr`), and bit `i` of the
+selected half is `l_{n+i}` for `b = 1` and `l_i` for `b = 0` (`ofFn_half`). -/
 private theorem accept_indGame_eq (S : BitPublicKeyScheme) (L : PolyExpr)
     (hL : ∀ n (rg : S.bitwise.gen.Coins n) (m : Fin n → Bool) (re : S.bitwise.enc.Coins n),
       2 * (S.bitwise.enc.runAt n (pairEncode (pairFstD (S.bitwise.gen.runAt n [] rg))
@@ -162,16 +153,16 @@ private theorem accept_indGame_eq (S : BitPublicKeyScheme) (L : PolyExpr)
   refine congrArg _ (funext fun r => ?_)
   rw [prob_bind, prob_bind]
   refine (expect_simulate_indImpl_cpa _ b n _ _
-    (fun a : Fin 1 → Bool => ProbComp.prob (.pure (a 0)) (· = true)) _).trans ?_
+    (fun a : Fin 1 → Bool => ProbComp.prob (.pure (a 0)) (· = true)) _ none).trans ?_
   rw [← expect_sample_equiv ((S.bitwiseEncCoins n).trans
-    (NUPPT.coinsCongr (padded_enc_coins S.bitwise L hL hmsg) n))]
+    (NUPPT.coinsCongr (PublicKeyScheme.padded_enc_coins S.bitwise L hL hmsg) n))]
   refine congrArg _ (funext fun v => ?_)
   refine congrArg (fun g => ProbComp.prob (.pure ((chRun g
     (A.toCompOn ((S.bitwise.padded L hL hmsg).indCodec n) n q (pairFstD (S.gen.runAt n [] rg)) r)
       none).1 0)) (· = true)) (funext fun mm => ?_)
-  rw [padded_enc_runAt, Equiv.trans_apply, NUPPT.coinsCongr_ofFn,
+  rw [PublicKeyScheme.padded_enc_runAt, Equiv.trans_apply, NUPPT.coinsCongr_ofFn,
     ofFn_half hk b (cast ((S.bitwise.padded L hL hmsg).indSpec_challengeDom n) mm),
-    AdaptiveCPA.ofFn_cast ((S.bitwise.padded L hL hmsg).inLens_one n), ← NUPPT.runAt_eq,
+    ofFn_cast ((S.bitwise.padded L hL hmsg).inLens_one n), ← NUPPT.runAt_eq,
     bitwise_runAt_blocks]
   unfold hybCt
   refine congrArg (fun l => padCt (L.eval n) (PrivateKeyScheme.encodeList (List.ofFn l)))
@@ -374,7 +365,8 @@ private theorem hyb_advantage_eq {S : BitPublicKeyScheme} (L : PolyExpr)
         [(firstQ (comp rg r)).elim false fun l =>
           (l.getD (js n) false != l.getD (n + js n) false) &&
             (F rg r (W β rg v re l) != l.getD (js n) false)] := by
-      rw [hφ _ _ hins houts _ _ _ (hw β rg re v), hz, ← AdaptiveCPA.indCodec_eq_bitCodec, ha]
+      rw [hφ _ _ hins houts _ _ _ (hw β rg re v), hz, ← FixedLengthPKScheme.indCodec_eq_bitCodec,
+        ha]
       cases hq : firstQ (comp rg r) with
       | none => simp only [Option.elim_none, plantOut_init]
       | some l =>
@@ -467,7 +459,7 @@ messages and `L(n)`-bit ciphertexts.
    bit with independent coins `v_i`, the first `j` bits of the right message and the remaining
    bits of the left message (`hybGame`, with the encryption coins sampled in advance). `H_0` and
    `H_n` have the acceptance probabilities of the experiments with `b = false` and `b = true`
-   (`accept_indGame_eq`: eager coins `BitwiseSim.expect_simulate_indImpl_cpa`, the bitwise
+   (`accept_indGame_eq`: eager coins `expect_simulate_indImpl_cpa`, the bitwise
    layout `bitwise_enc_runAtL` and the coin blocks `bitwiseEncCoins_ofFn`).
 2. By `Games.exists_advantage_hybrid_gap`, at each `n > 0` some `j⋆(n) < n` has
    `advantage(H_{j⋆}, H_{j⋆+1}) ≥ advantage(H_0, H_n) / n`; at `n = 0` the two ends coincide and
@@ -482,7 +474,7 @@ messages and `L(n)`-bit ciphertexts.
    Then `advantage(H_{j⋆}, H_{j⋆+1})` equals `D`'s single-bit advantage between `⟨pk, Enc_pk(0)⟩`
    and `⟨pk, Enc_pk(1)⟩` exactly (`hyb_advantage_eq`): only the first challenge matters
    (`ChallengeSim.chRun_congr`); resampling coin block `j⋆` turns the two hybrids into the
-   planted tuples with `Enc(m₀_{j⋆})` and `Enc(m₁_{j⋆})` (`BitwiseSim.expect_sample_update`); and
+   planted tuples with `Enc(m₀_{j⋆})` and `Enc(m₁_{j⋆})` (`ProbComp.expect_sample_update`); and
    the signed case split on `(m₀_{j⋆}, m₁_{j⋆})` is `ChallengeSim.expect_indicator_sub`.
 4. So `A`'s advantage is at most `n` times `D`'s advantage, negligible by `singleBitSecure_iff`;
    the product is negligible by `Negligible.polyExpr_mul` with `PolyExpr.var`. -/
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA/Eager.lean b/TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA/Eager.lean
deleted file mode 100644
index 340f86303..000000000
--- a/TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA/Eager.lean
+++ /dev/null
@@ -1,167 +0,0 @@
-/-
-Copyright (c) 2026 TCSlib contributors. All rights reserved.
-Released under Apache 2.0 license as described in the file LICENSE.
--/
-import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
-
-set_option maxHeartbeats 0
-set_option relaxedAutoImplicit false
-set_option autoImplicit false
-
-/-!
-# Eager challenge coins and readers for the CPA game
-
-Generic facts used by the hybrid argument for the bitwise scheme under chosen-plaintext attack
-[PS10, p. 103, in the game of Definition 171.5]: under CPA the encryption coins of the challenge
-may be sampled in advance (`expect_simulate_indImpl_cpa`, through the oracle equations
-`indImpl_*_onSpec`); resampling one coordinate of a uniform tuple leaves it uniform
-(`expect_sample_update`); and the padded encryptor of a padded public-key scheme pads the
-original encryptor's output (`padded_enc_runAt`). All are read from the published lemmas of
-`OracleSecurity` and `ChallengeSim`. The CPA game's codec is the bit codec of the scheme's
-lengths by `AdaptiveCPA.indCodec_eq_bitCodec`, and casts are read by `AdaptiveCPA.ofFn_cast`.
-
-## Main results
-
-* `BitwiseSim.expect_simulate_eager`, `expect_simulate_indImpl_cpa`: eager challenge coins under
-  CPA, generically and for `indImpl`.
-* `BitwiseSim.expect_sample_update`: resampling a coordinate.
-* `BitwiseSim.padded_enc_runAt`, `BitwiseSim.padded_enc_coins`: readers of the padded scheme.
-
-## References
-
-* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
-  p. 103 and §7.1.4, Definition 171.5 (book p. 171).
--/
-
-namespace TCSlib.Cryptography.Composability.BitwiseSim
-
-open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ChallengeSim ProbComp
-
-/-- **Eager challenge coins, for any CPA-shaped oracle.** Let `impl` answer oracle `0`
-all-`false`, a challenge from a recorded state `c` with `c`, and the first challenge `mm` by
-sampling `re` and answering (and recording) `padFin d (g mm re)`; the state holds `d`-bit
-strings, `d = outs 1`, read through the cast `e`. Then for every `G`,
-`𝔼[G ∘ fst] (simulate impl c s) = 𝔼_{re} G (chRun (fun mm => g mm re) c (s.map (cast e))).1`.
-
-**Proof sketch.** Substitute `d = outs 1`, so that the casts are identities. Induction on the
-computation: decryption queries and repeated challenges are deterministic in both; at the first
-challenge the lazy side samples `re` and continues from the recorded answer, by the induction
-hypothesis an average over coins `re'` on which the recorded run does not depend
-(`chRun_some_congr`), so `re'` marginalizes out (`expect_const`). -/
-theorem expect_simulate_eager {ins outs : Fin 2 → ℕ} {d : ℕ} (hd : outs 1 = d)
-    (e : (Fin d → Bool) = (Fin (outs 1) → Bool)) {R : Type} [Fintype R] [Nonempty R]
-    (impl : QueryImpl (bitSpec ins outs) (Option (Fin d → Bool)) unifSpec)
-    (g : (Fin (ins 1) → Bool) → R → List Bool)
-    (h0 : ∀ x s, impl 0 x s = .pure (zeroBits _, s))
-    (hrep : ∀ mm c, impl 1 mm (some c) = .pure (cast e c, some c))
-    (hnew : ∀ mm, impl 1 mm none = (ProbComp.sample R).bind fun re =>
-      .pure (cast e (padFin d (g mm re)), some (padFin d (g mm re))))
-    {α : Type} (G : α → ℝ) (c : OracleComp (bitSpec ins outs) α) (s : Option (Fin d → Bool)) :
-    expect (simulate impl c s) (fun p => G p.1) =
-      expect (ProbComp.sample R) fun re =>
-        G (chRun (fun mm => g mm re) c (s.map (cast e))).1 := by
-  subst hd
-  have hc : ∀ x : Fin (outs 1) → Bool, cast e x = x := fun x => cast_eq e x
-  have hmap : ∀ s : Option (Fin (outs 1) → Bool), s.map (cast e) = s := fun s => by
-    cases s <;> simp
-  simp only [hc] at hrep hnew
-  simp only [hmap]
-  induction c generalizing s with
-  | pure a =>
-    rw [simulate_pure, expect_pure]
-    simp only [chRun_pure]
-    exact (expect_const _ _).symm
-  | query i x k ih =>
-    match i, x, k, ih with
-    | 0, x, k, ih =>
-      rw [simulate_query, h0, OracleComp.pure_bind]
-      simp only [chRun_query_zero]
-      exact ih _ s
-    | 1, x, k, ih =>
-      cases s with
-      | some C =>
-        rw [simulate_query, hrep, OracleComp.pure_bind]
-        simp only [chRun_query_one_some]
-        exact ih _ _
-      | none =>
-        rw [simulate_query, hnew, OracleComp.bind_assoc, expect_bind]
-        refine congrArg _ (funext fun re => ?_)
-        rw [OracleComp.pure_bind, ih, chRun_query_one_none]
-        dsimp only
-        exact (congrArg _ (funext fun re' =>
-          congrArg (fun p : α × Option (Fin (outs 1) → Bool) => G p.1)
-            (chRun_some_congr (fun mm => g mm re') (fun mm => g mm re) _ _))).trans
-          (expect_const _ _)
-
-/-- **Eager challenge coins under CPA.** Simulating the oracles of `Ind_b` from the unchallenged
-state has, for every `G`, the expectation of first sampling the encryption coins `re` and then
-running the deterministic oracles whose challenge `mm` is answered with `Enc(⟨pk, m_b⟩; re)`,
-the halves read through `indSpec_challengeDom`:
-`𝔼[G ∘ fst] (simulate (indImpl .cpa b n pk sk) c none) = 𝔼_{re} G (chRun g_re c none).1`.
-
-**Proof sketch.** `expect_simulate_eager` with `d = ctLen(n)` (`outLens_one`), the cast
-`indSpec_challengeRng`, and the oracle equations `indImpl_dec_onSpec` (with `decOpen_cpa`),
-`indImpl_challenge_repeat_onSpec` and `indImpl_challenge_none_onSpec`. -/
-theorem expect_simulate_indImpl_cpa (S : FixedLengthPKScheme) (b : Bool) (n : ℕ)
-    (pk sk : List Bool) {α : Type} (G : α → ℝ) (c : OracleComp (S.indSpec n) α) :
-    expect (simulate (S.indImpl .cpa b n pk sk) c none) (fun p => G p.1) =
-      expect (ProbComp.sample (S.enc.Coins n)) fun re =>
-        G (chRun (fun mm => S.enc.runAt n (pairEncode pk (List.ofFn
-          (if b then (FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n) mm)).2
-            else (FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n) mm)).1))) re)
-          c none).1 :=
-  expect_simulate_eager (S.outLens_one n) (S.indSpec_challengeRng n).symm _ _
-    (fun x s => by
-      rw [S.indImpl_dec_onSpec]
-      simp only [FixedLengthScheme.decOpen_cpa, Bool.false_and, Bool.false_eq_true, if_false])
-    (fun mm C => S.indImpl_challenge_repeat_onSpec .cpa b n pk sk mm C)
-    (fun mm => S.indImpl_challenge_none_onSpec .cpa b n pk sk mm) G c none
-
-/-- **Resampling one coordinate of a uniform tuple leaves it uniform**:
-`𝔼_{v} 𝔼_{b} f (update v j b) = 𝔼_{v} f v`.
-
-**Proof sketch.** The map `(v, b) ↦ (update v j b, v j)` is an involution of
-`(ι → β) × β` (`Function.update_idem`, `Function.update_eq_self`); reindexing the product sample
-along it (`expect_sample_equiv`, `expect_sample_prod`) turns the left side into
-`𝔼_{v} 𝔼_{b} f v = 𝔼_{v} f v` (`expect_const`). -/
-theorem expect_sample_update {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [Nonempty β]
-    (j : ι) (f : (ι → β) → ℝ) :
-    (expect (sample (ι → β)) fun v => expect (sample β) fun b => f (Function.update v j b)) =
-      expect (sample (ι → β)) f := by
-  let e : (ι → β) × β ≃ (ι → β) × β :=
-    { toFun := fun p => (Function.update p.1 j p.2, p.1 j)
-      invFun := fun p => (Function.update p.1 j p.2, p.1 j)
-      left_inv := fun p => by simp
-      right_inv := fun p => by simp }
-  rw [← expect_sample_prod (fun p : (ι → β) × β => f (Function.update p.1 j p.2))]
-  have h := expect_sample_equiv e (fun p : (ι → β) × β => f p.1)
-  refine h.trans ?_
-  rw [expect_sample_prod]
-  exact congrArg _ (funext fun v => expect_const (sample β) (f v))
-
-/-- **The padded encryptor pads the original encryptor's output**: for a padded public-key
-scheme, `Enc'(1^n, y; r) = padCt L(n) (Enc(1^n, y; r))`, with the coin string read as a list
-(`PublicKeyScheme.padded_enc`, `runAt_padEnc`, `NUPPT.coinsCongr_ofFn`). -/
-theorem padded_enc_runAt (S : PublicKeyScheme) (L : PolyExpr)
-    (hL : ∀ n (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.enc.Coins n),
-      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re).length
-        + 2 ≤ L.eval n)
-    (hmsg : ∀ n, n ≤ L.eval n) (n : ℕ) (y : List Bool)
-    (r : (S.padded L hL hmsg).enc.Coins n) :
-    (S.padded L hL hmsg).enc.runAt n y r = padCt (L.eval n) (S.enc.runAtL n y (List.ofFn r)) := by
-  have key : ∀ E : NUPPT, E = padEnc S.enc L → ∀ r : E.Coins n,
-      E.runAt n y r = padCt (L.eval n) (S.enc.runAtL n y (List.ofFn r)) := by
-    rintro E rfl r
-    rw [runAt_padEnc S.enc_uniform L n y r, NUPPT.runAt_eq, NUPPT.coinsCongr_ofFn]
-  exact key _ (PublicKeyScheme.padded_enc S L hL hmsg) r
-
-/-- The padded scheme's encryptor has the coin polynomial of the original encryptor:
-`S.enc.coins = (S.padded L hL hmsg).enc.coins`. -/
-theorem padded_enc_coins (S : PublicKeyScheme) (L : PolyExpr)
-    (hL : ∀ n (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.enc.Coins n),
-      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re).length
-        + 2 ≤ L.eval n)
-    (hmsg : ∀ n, n ≤ L.eval n) : S.enc.coins = (S.padded L hL hmsg).enc.coins := by
-  rw [PublicKeyScheme.padded_enc, padEnc_coins]
-
-end TCSlib.Cryptography.Composability.BitwiseSim
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA/Planted.lean b/TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA/Planted.lean
index 93e93023a..a3b025afa 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA/Planted.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA/Planted.lean
@@ -5,6 +5,7 @@ Released under Apache 2.0 license as described in the file LICENSE.
 import TCSlib.Cryptography.Encryption.PublicKey.HybridMachine
 import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.RecordHandler
 import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
+import TCSlib.Cryptography.Foundations.BitLists
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -52,20 +53,6 @@ theorem ofFn_const_of_eq_one {p : ℕ} (hp : p = 1) (b : Bool) :
   subst hp
   rfl
 
-/-- Flattening singletons: `(List.ofFn fun i => List.ofFn fun _ : Fin p => f i).flatten =
-List.ofFn f` when `p = 1`. -/
-theorem flatten_ofFn_singleton {p : ℕ} (hp : p = 1) :
-    ∀ {k : ℕ} (f : Fin k → Bool),
-      (List.ofFn fun i => List.ofFn fun _ : Fin p => f i).flatten = List.ofFn f := by
-  intro k
-  induction k with
-  | zero => intro f; rfl
-  | succ k ih =>
-    intro f
-    rw [List.ofFn_succ, List.ofFn_succ, List.flatten_cons, ih (fun i => f i.succ),
-      ofFn_const_of_eq_one hp]
-    rfl
-
 /-- The first `j` bits of `List.ofFn m`, as a flattening of singletons (`p = 1`):
 `(ofFn m).take j = (ofFn fun i : Fin j => ofFn fun _ : Fin p => m i).flatten`. -/
 theorem take_ofFn_flatten {p n j : ℕ} (hp : p = 1) (m : Fin n → Bool) (hj : j ≤ n) :
@@ -93,12 +80,6 @@ theorem drop_ofFn_flatten {p n j : ℕ} (hp : p = 1) (m : Fin n → Bool) (hj :
   · intro t h₁ h₂
     simp only [List.getElem_drop, List.getElem_ofFn]
 
-/-- The head of a suffix is an entry: `(l.drop k).headD false = l.getD k false`. -/
-theorem headD_drop (l : List Bool) (k : ℕ) : (l.drop k).headD false = l.getD k false := by
-  induction l generalizing k with
-  | nil => simp
-  | cons b l ih => cases k <;> simp
-
 /-! ### The planted tuple -/
 
 /-- **The planted tuple** on `⟨⟨u, ⟨⟨pk, c⟩, ω⟩⟩, ⟨⟨u_j, ⟨u_b, Z⟩⟩, x⟩⟩` (unary parameter
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA/QueryHandler.lean b/TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA/QueryHandler.lean
index 85ee5a1fd..12008db2a 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA/QueryHandler.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA/QueryHandler.lean
@@ -32,8 +32,6 @@ first challenge query (`exists_qHandlerMachine`).
 * `BitwiseSim.simulate_qHandler_recorded`, `simulate_qHandler_init`: the handler's simulation is
   the deterministic run with the answer function, and its final state records the first
   challenge query.
-* `BitwiseSim.chRun_toCompOn_transport_list`: transport of a run with a query-dependent answer
-  along equal lengths.
 * `BitwiseSim.exists_qHandlerMachine`: the machine of the handler, by T1.
 
 ## References
@@ -184,17 +182,6 @@ attribute [simps (config := { isSimp := false }) stateLen seedLen init run advIn
 
 /-! ### The handler's simulation -/
 
-/-- An empty answer decodes to all-`false` at every length:
-`(decodeFin ℓ []).getD (zeroBits ℓ) = zeroBits ℓ`. -/
-theorem decodeFin_nil_getD (ℓ : ℕ) : (decodeFin ℓ []).getD (zeroBits ℓ) = zeroBits ℓ := by
-  rw [decodeFin_eq]
-  split
-  · next h =>
-    subst h
-    funext i
-    exact absurd i.isLt (Nat.not_lt_zero _)
-  · rfl
-
 section Simulation
 
 variable {α : Type} (Lc Lq Ld Laux Lseed : PolyExpr) (aux : ℕ → List Bool)
@@ -250,7 +237,7 @@ theorem simulate_qHandler_recorded
           (padFin _ (ans (pairEncode (seedIn n z (List.ofFn ω))
             (pairEncode (aux n) (List.ofFn mm)))), s) := by
         refine PolyHandler.answer_of_run_eq _ ?_
-        rw [qHandler_run, PolyHandler.input_eq, GGMRed.ofFn_padFin_of_length (by
+        rw [qHandler_run, PolyHandler.input_eq, ofFn_padFin_of_length (by
           rw [hw _ hlen, qDout_one]), hs, seedIn_eq]
         exact qRun_recorded ans _ _ _ _
       rw [simulate_query, PolyHandler.impl_apply, hans1, OracleComp.pure_bind,
@@ -282,7 +269,7 @@ theorem simulate_qHandler_init (haux : (aux n).length = Laux.eval n)
     rw [show (qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).init n =
         padFin _ (pairEncode (aux n) (false :: List.replicate (Lq.eval n) false)) from
       funext (qHandler_init Lc Lq Ld Laux Lseed aux ans hans fin hfin n)]
-    refine GGMRed.ofFn_padFin_of_length ?_
+    refine ofFn_padFin_of_length ?_
     rw [qHandler_stateLen, length_pairEncode, List.length_cons, List.length_replicate, haux]
     simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
     omega
@@ -311,41 +298,21 @@ theorem simulate_qHandler_init (haux : (aux n).length = Laux.eval n)
             (pairEncode (aux n) (List.ofFn x)))),
             padFin _ (pairEncode (aux n) (true :: List.ofFn x))) := by
         refine PolyHandler.answer_of_run_eq _ ?_
-        rw [qHandler_run, PolyHandler.input_eq, GGMRed.ofFn_padFin_of_length (by
-          rw [hw _ hxlen, qDout_one]), GGMRed.ofFn_padFin_of_length hlen, hinit, seedIn_eq]
+        rw [qHandler_run, PolyHandler.input_eq, ofFn_padFin_of_length (by
+          rw [hw _ hxlen, qDout_one]), ofFn_padFin_of_length hlen, hinit, seedIn_eq]
         exact qRun_fresh ans _ _ _ _ rfl
       refine ⟨padFin _ (pairEncode (aux n) (true :: List.ofFn x)), ?_, ?_⟩
       · rw [simulate_query, PolyHandler.impl_apply, hans1, OracleComp.pure_bind,
           chRun_query_one_none]
         exact simulate_qHandler_recorded Lc Lq Ld Laux Lseed aux hans hfin n z ω hw _ x _
-          (GGMRed.ofFn_padFin_of_length hlen)
-      · rw [GGMRed.ofFn_padFin_of_length hlen, firstQ_query_one]
+          (ofFn_padFin_of_length hlen)
+      · rw [ofFn_padFin_of_length hlen, firstQ_query_one]
         rfl
 
 end Simulation
 
 /-! ### Transport and the machine -/
 
-/-- **Transport of a run with a query-dependent answer along equal lengths:** for a machine
-adversary run through `bitCodec`, if `ins = ins'`, `outs = outs'` and `d = d'`, then for every
-`G : List Bool → List Bool`,
-`List.ofFn (chRun (fun y => G ⟦y⟧) (A.toCompOn (bitCodec ins outs d) n q x r) none).1 =
-List.ofFn (chRun (fun y => G ⟦y⟧) (A.toCompOn (bitCodec ins' outs' d') n q x r) none).1`, and
-the two runs have the same `firstQ`.
-
-**Proof sketch.** Substitute the equalities; both sides become identical. -/
-theorem chRun_toCompOn_transport_list {ins outs ins' outs' : Fin 2 → ℕ} {d d' : ℕ}
-    (hi : ins = ins') (ho : outs = outs') (hd : d = d') (A : NUPPT) (n q : ℕ) (x : List Bool)
-    (r : A.Coins n) (G : List Bool → List Bool) :
-    List.ofFn (chRun (ins := ins) (outs := outs) (fun y => G (List.ofFn y))
-        (A.toCompOn (bitCodec ins outs d) n q x r) none).1 =
-      List.ofFn (chRun (ins := ins') (outs := outs') (fun y => G (List.ofFn y))
-        (A.toCompOn (bitCodec ins' outs' d') n q x r) none).1 ∧
-    firstQ (A.toCompOn (bitCodec ins outs d) n q x r) =
-      firstQ (A.toCompOn (bitCodec ins' outs' d') n q x r) := by
-  subst hi ho hd
-  exact ⟨rfl, rfl⟩
-
 /-- **The machine of the query-recording handler** (T1 for `qHandler`). For a machine adversary
 `A` with query budget `q` and one-bit output, there is a machine `D` and, at every parameter, a
 bijection `φ` from (seed, `A`'s coins) to `D`'s coins with the following property. For lengths
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/ElGamal.lean b/TCSlib/Cryptography/Encryption/PublicKey/ElGamal.lean
index 2a4f397ee..59166a10b 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/ElGamal.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/ElGamal.lean
@@ -1077,12 +1077,6 @@ private theorem dlc_splitEquiv_symm_ofFn {L a b : ℕ} (h : L = a + b) (u : Fin
   subst h
   exact ofFn_splitCoins_symm a b u v
 
-/-- Padding a string of the right length is lossless: `List.ofFn (padFin ℓ w) = w` for `|w| = ℓ`
-(`Collection.ofFn_padFin_of_le`). -/
-private theorem dlc_ofFn_padFin {ℓ : ℕ} {w : List Bool} (h : w.length = ℓ) :
-    List.ofFn (padFin ℓ w) = w := by
-  rw [Collection.ofFn_padFin_of_le h.le, h, Nat.sub_self, List.replicate_zero, List.append_nil]
-
 /-- The public key `⟨i, X⟩` read from a DDH tuple `⟨i, ⟨X, ⟨Y, Z⟩⟩⟩`. -/
 private def dlc_tuplePk (t : List Bool) : List Bool := pairEncode (pairFstD t) (pairFstD (pairSndD t))
 
@@ -1433,8 +1427,9 @@ the same coins (the exponents are the same samplers, `h^{(ab mod q)} = h^{ab}` s
 `NUPPT.distinguisherL_eq`, `he`, `dlc_challenge_eq`). The derived index `i` (`dlc_grp_runAt`) is
 valid and well formed, `⟨p, ⟨q, h⟩⟩` with `p`, `q` from `G`'s index (`wellFormedIndex_iff`,
 `safePrimeValid_iff`) and `h = egSquareGen p g = g² mod p` off the bad event, of order `q`
-(`egSquareGen_valid`). The padding of the tuple is lossless (`dlc_ofFn_padFin`, `length_ddhTuple`),
-so `D_b` reads `⟨i, X⟩`, `Y` and `Z` back. The exponent `ddhExpo n i u` has the value of the sampler
+(`egSquareGen_valid`). The padding of the tuple is lossless (`ofFn_padFin_of_length`,
+`length_ddhTuple`), so `D_b` reads `⟨i, X⟩`, `Y` and `Z` back. The exponent `ddhExpo n i u` has
+the value of the sampler
 `sampleBelowL q (Nat.size q) n n u` of `egGenParts`/`egEncParts` (`expOrd_of_valid`,
 `ZMod.val_natCast`, `sampleBelowL_lt`), `expF i z` is the numeral of `h^z mod p` (`expF_eq`,
 `WellFormedIndex.dlW_eq`), and `(h^x mod p)^y · c ≡ h^{xy mod q} · c (mod p)` since `h` has order
@@ -1484,7 +1479,7 @@ private theorem dlc_hyb1_point (H : ArithmeticFP) (G : SafePrimeGen) (M D Db : N
   simp only [pairFstD_pairEncode, pairSndD_pairEncode, dlP_eq, dlM_eq, dlG_eq]
   generalize egUnit n (listToNat a) (List.ofFn u₁) ^ 2 % listToNat a = h at hord hi hhp ⊢
   -- the tuple
-  rw [dlc_ofFn_padFin (by rw [length_ddhTuple hwi, eval_ddhLen])]
+  rw [ofFn_padFin_of_length (by rw [length_ddhTuple hwi, eval_ddhLen])]
   unfold dlc_ddhInput dlc_tuplePk
   rw [ddhTuple_eq]
   simp only [pairFstD_pairEncode, pairSndD_pairEncode]
@@ -1615,7 +1610,7 @@ private theorem dlc_rand_term {n : ℕ} {i : List Bool} (hvi : SafePrimeValid i)
 runs `D` on `⟨⟨i, g^a⟩, ⟨g^b, ⟦g^z · m'_b mod p⟧_n⟩⟩` with `z = ddhExpo n i u₃`.
 
 **Proof sketch.** Unfold `D_b` on the random tuple (`NUPPT.distinguisher_eq`,
-`NUPPT.distinguisherL_eq`, `he`, `ddhRandom`). The padding is lossless (`dlc_ofFn_padFin`,
+`NUPPT.distinguisherL_eq`, `he`, `ddhRandom`). The padding is lossless (`ofFn_padFin_of_length`,
 `length_ddhTuple`), so the projections of `dlc_ddhInput` and `dlc_tuplePk` read the components of
 the tuple back, and the numeral `Z = expF i z` reads as `g^z mod p` (`expF_eq`,
 `listToNat_natToList` below `dlP_lt_two_pow`). -/
@@ -1648,7 +1643,7 @@ private theorem dlc_rand_accept (H : ArithmeticFP) (G : SafePrimeGen) (M D Db :
   dsimp only
   generalize (egGroupGen H G).gen.runAt n [] r = i at hvi hwi ⊢
   have hp0 : 0 < dlP i := ((expValid_iff i).1 hvi.expValid).1.pos
-  rw [dlc_ofFn_padFin (by rw [length_ddhTuple hwi, eval_ddhLen])]
+  rw [ofFn_padFin_of_length (by rw [length_ddhTuple hwi, eval_ddhLen])]
   unfold dlc_ddhInput dlc_tuplePk
   rw [ddhTuple_eq]
   simp only [pairFstD_pairEncode, pairSndD_pairEncode]
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/HybridMachine.lean b/TCSlib/Cryptography/Encryption/PublicKey/HybridMachine.lean
index de55a939c..976d99962 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/HybridMachine.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/HybridMachine.lean
@@ -25,6 +25,7 @@ hybrid index, the messages and the coin offsets.
 
 ## Main results
 
+* `TCSlib.Cryptography.hybridPre_eq` is the defining equation of the pre-processing.
 * `TCSlib.Cryptography.blockEncFun_flatten` describes block encryption on a concatenation
   of messages. `TCSlib.Cryptography.encodeList_ofFn_split` splits an encoded tuple.
 * `TCSlib.Cryptography.exists_hybridMachine` constructs the reduction with its coin count
@@ -233,6 +234,23 @@ def hybridPre (E : List Bool → List Bool) (L B : PolyExpr) (y : List Bool) : L
           (pairSndD (pairSndD (pairSndD (pairSndD y))))
           ((pairSndD (pairFstD y)).drop (pairSndD (pairFstD (pairSndD (pairSndD y)))).length))))
 
+/-- The defining equation of `hybridPre`: on `y = ⟨⟨⟨pk, c⟩, w⟩, ⟨u, ⟨⟨u₁, u₂⟩, ⟨M₁, M₂⟩⟩⟩⟩` it is
+`⟨pk, blockEncFun E L B (blockState u pk M₁ (w.take |u₁|)) ++
+⟨c, blockEncFun E L B (blockState u pk M₂ (w.drop |u₂|))⟩⟩`. -/
+theorem hybridPre_eq (E : List Bool → List Bool) (L B : PolyExpr) (y : List Bool) :
+    hybridPre E L B y =
+      pairEncode (pairFstD (pairFstD (pairFstD y)))
+        (blockEncFun E L B (blockState (pairFstD (pairSndD y)) (pairFstD (pairFstD (pairFstD y)))
+            (pairFstD (pairSndD (pairSndD (pairSndD y))))
+            ((pairSndD (pairFstD y)).take (pairFstD (pairFstD (pairSndD (pairSndD y)))).length)) ++
+          pairEncode (pairSndD (pairFstD (pairFstD y)))
+            (blockEncFun E L B
+              (blockState (pairFstD (pairSndD y)) (pairFstD (pairFstD (pairFstD y)))
+                (pairSndD (pairSndD (pairSndD (pairSndD y))))
+                ((pairSndD (pairFstD y)).drop
+                  (pairSndD (pairFstD (pairSndD (pairSndD y)))).length)))) :=
+  rfl
+
 /-- The pre-processing of the hybrid machine is polynomial-time.
 
 **Proof sketch.** Pair projections for the eleven slots, the typed coin cuts
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability.lean b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability.lean
index f1b2870c0..4d25cc629 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability.lean
@@ -240,11 +240,11 @@ the recorded challenge with `⊥ = 0`, as `nmDecrypt` does (`nmDecrypt_eq`); the
 strings (`ofFn_cast`, `ofFn_zeroBits`, `outLens_zero`). -/
 private theorem castImpl_indImpl_dec (b : Bool) (n : ℕ) (pk sk : List Bool)
     (x : Fin ((acDin S 0).eval n) → Bool) (st : Option (Fin (S.ctLen.eval n) → Bool)) :
-    castImpl (ins := fun i => (acDin S i).eval n) (outs := fun i => (acDout S i).eval n)
+    Games.castImpl (ins := fun i => (acDin S i).eval n) (outs := fun i => (acDout S i).eval n)
       (S.indImpl .cca2 b n pk sk) 0 x st =
       .pure (padFin ((acDout S 0).eval n) (List.ofFn (S.nmDecrypt sk st
         (cast (S.indSpec_decDom n) (padFin (S.inLens n 0) (List.ofFn x))))), st) := by
-  rw [castImpl_eq, S.indImpl_dec_onSpec_cast, FixedLengthScheme.decOpen_cca2, Bool.true_and,
+  rw [Games.castImpl_eq, S.indImpl_dec_onSpec_cast, FixedLengthScheme.decOpen_cca2, Bool.true_and,
     S.nmDecrypt_eq]
   by_cases hs : st = some (cast (S.indSpec_decDom n) (padFin (S.inLens n 0) (List.ofFn x)))
   · rw [if_neg (by rw [decide_eq_true hs, Bool.not_true]; exact Bool.false_ne_true), if_pos hs,
@@ -278,8 +278,8 @@ private theorem decBlock_eq_nthCt (ℓ : PolyExpr) (n : ℕ)
     rw [decBlock_eq, ofFn_padFin_eq_take, hct,
       List.take_append_of_le_length (by rw [List.length_drop, ha]; omega)]
   apply List.ofFn_injective
-  rw [ofFn_cast hin, GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hct, hin]), hblk,
-    ofFn_nthCt, GGMRed.ofFn_padFin_of_length ha]
+  rw [ofFn_cast hin, ofFn_padFin_of_length (by rw [List.length_ofFn, hct, hin]), hblk,
+    ofFn_nthCt, ofFn_padFin_of_length ha]
 
 /-- **The reduction's collected answers are the experiment's output:** the concatenated answers
 of the CCA2 decryption oracle on the `ℓ(n)` blocks of `a`, in state `st`, are
@@ -301,7 +301,7 @@ private theorem decAnswers_eq_nmOutput (ℓ : PolyExpr) (n : ℕ) (sk : List Boo
   refine List.ext_getElem (by rw [List.length_map, List.length_range, List.length_ofFn])
     fun i h₁ h₂ => ?_
   rw [List.getElem_map, List.getElem_range, List.getElem_ofFn,
-    GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hout]),
+    ofFn_padFin_of_length (by rw [List.length_ofFn, hout]),
     decBlock_eq_nthCt S ℓ n a i (by rw [List.length_map, List.length_range] at h₁; exact h₁)]
 
 /-- **The reduction's game is the non-malleability experiment.** Let `B` be T2's machine for the
@@ -346,11 +346,11 @@ private theorem accept_indGame_decRed (A D B B' : NUPPT) (q ℓ : PolyExpr) (n :
     NUPPT.coinsEquivPoly (decHandler_seedLen S ℓ D).symm n
   rw [accept_eq, accept_eq, S.indGame_eq, S.nmGame_eq, prob_bind, prob_bind]
   refine congrArg _ (funext fun rg => ?_)
-  conv_lhs => rw [prob_bind, ← expect_sample_equiv (φ.trans (NUPPT.coinsCongr hc n)),
-    expect_sample_prod, expect_sample_comm]
+  conv_lhs => rw [prob_bind, ← ProbComp.expect_sample_equiv (φ.trans (NUPPT.coinsCongr hc n)),
+    expect_sample_prod, ProbComp.expect_sample_comm]
   conv_rhs => rw [prob_bind]
   refine congrArg _ (funext fun r => ?_)
-  conv_lhs => rw [← expect_sample_equiv e]
+  conv_lhs => rw [← ProbComp.expect_sample_equiv e]
   conv_rhs => rw [prob_bind]
   refine congrArg _ (funext fun ρ => ?_)
   -- The reduction's side: transport to T2's codec and unfold the reduction.
@@ -362,8 +362,8 @@ private theorem accept_indGame_decRed (A D B B' : NUPPT) (q ℓ : PolyExpr) (n :
     rw [prob_pure]
     dsimp only
     rw [headD_ofFn_one]
-  rw [Equiv.trans_apply, hB', prob_bind, indCodec_eq_bitCodec, h1]
-  refine (expect_simulate_castImpl_toCompOn (acDin_eval S n) (acDout_eval S n) hd1 _ B n _ _ _
+  rw [Equiv.trans_apply, hB', prob_bind, FixedLengthPKScheme.indCodec_eq_bitCodec, h1]
+  refine (Games.expect_simulate_castImpl_toCompOn (acDin_eval S n) (acDout_eval S n) hd1 _ B n _ _ _
     none (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
       if p.1.headD false = true then (1 : ℝ) else 0)).symm.trans ?_
   rw [← hφ, decHandler_advInput, pairFstD_pairEncode, simulate_decHandler_impl,
@@ -386,13 +386,13 @@ private theorem accept_indGame_decRed (A D B B' : NUPPT) (q ℓ : PolyExpr) (n :
     dsimp only
     rw [padFin_ofFn]
   rw [prob_bind, nmCodec_eq_bitCodec, h2]
-  refine Eq.trans ?_ (expect_simulate_castImpl_toCompOn (acDin_eval S n) (acDout_eval S n) hdα _
-    A n _ _ _ none (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
+  refine Eq.trans ?_ (Games.expect_simulate_castImpl_toCompOn (acDin_eval S n) (acDout_eval S n)
+    hdα _ A n _ _ _ none (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
       if D.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) p.2
         (padFin (ℓ.eval n * S.ctLen.eval n) p.1)) ρ = true then (1 : ℝ) else 0))
   refine congrArg _ (funext fun p => ?_)
   -- Pointwise: the verdict on the collected answers is `D`'s verdict on `NM_b`'s output.
-  rw [GGMRed.ofFn_padFin_of_length (by rw [List.length_singleton, hd1]), List.headD_cons,
+  rw [ofFn_padFin_of_length (by rw [List.length_singleton, hd1]), List.headD_cons,
     pairSndD_pairEncode, decAnswers_eq_nmOutput, NUPPT.coinsEquivPoly_ofFn,
     ← NUPPT.runAtL_eq_output_layout, ← NUPPT.runAt_eq, ← NUPPT.distinguisherL_eq]
 
@@ -463,7 +463,7 @@ private theorem guessDist_nmOutput (n : ℕ) (hm : 0 < S.msgLen.eval n) (rg : S.
     exact S.correct n _ rg (encTape S n ω β)
   -- The two blocks of the output.
   set W := padFin ((PolyExpr.const 2).eval n * S.ctLen.eval n) (c₁ ++ c₂)
-  have hW : List.ofFn W = c₁ ++ c₂ := GGMRed.ofFn_padFin_of_length (by
+  have hW : List.ofFn W = c₁ ++ c₂ := ofFn_padFin_of_length (by
     rw [List.length_append, hlen, hlen, h2]; omega)
   have hblk : ∀ (i : Fin ((PolyExpr.const 2).eval n)) (β : Bool), (i : ℕ) = (if β then 0 else 1) →
       List.ofFn (S.nthCt W i) = encCt S n pk ω g β := by
@@ -537,7 +537,7 @@ private theorem accept_nmGame_encRed (A B : NUPPT) (q : PolyExpr) (n : ℕ)
     omega
   rw [accept_eq, accept_eq, S.nmGame_eq, S.indGame_eq, prob_bind, prob_bind]
   refine congrArg _ (funext fun rg => ?_)
-  rw [prob_bind, prob_bind, ← expect_sample_equiv φ, expect_sample_prod]
+  rw [prob_bind, prob_bind, ← ProbComp.expect_sample_equiv φ, expect_sample_prod]
   refine (congrArg _ (funext fun ω => ?_)).trans (expect_const _ _)
   refine congrArg _ (funext fun r => ?_)
   rw [prob_bind]
@@ -556,7 +556,7 @@ private theorem accept_nmGame_encRed (A B : NUPPT) (q : PolyExpr) (n : ℕ)
     dsimp only
     rw [padFin_ofFn]
   rw [prob_bind, nmCodec_eq_bitCodec, h2]
-  refine (expect_simulate_castImpl_toCompOn (acDin_eval S n) (acDout_eval S n) hd2 _ B n _ _ _
+  refine (Games.expect_simulate_castImpl_toCompOn (acDin_eval S n) (acDout_eval S n) hd2 _ B n _ _ _
     none (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
       if guessDist.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) p.2
         (padFin ((PolyExpr.const 2).eval n * S.ctLen.eval n) p.1)) ρ = true then (1 : ℝ)
@@ -574,9 +574,9 @@ private theorem accept_nmGame_encRed (A B : NUPPT) (q : PolyExpr) (n : ℕ)
     rw [prob_pure]
     dsimp only
     rw [headD_ofFn_one]
-  rw [prob_bind, indCodec_eq_bitCodec, h1]
-  refine Eq.trans ?_ (expect_simulate_castImpl_toCompOn (acDin_eval S n) (acDout_eval S n) hd1 _
-    A n _ _ _ none (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
+  rw [prob_bind, FixedLengthPKScheme.indCodec_eq_bitCodec, h1]
+  refine Eq.trans ?_ (Games.expect_simulate_castImpl_toCompOn (acDin_eval S n) (acDout_eval S n)
+    hd1 _ A n _ _ _ none (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
       if p.1.headD false = true then (1 : ℝ) else 0))
   refine congrArg _ (funext fun p => ?_)
   -- Pointwise: the distinguisher outputs `A`'s guess.
@@ -585,7 +585,7 @@ private theorem accept_nmGame_encRed (A B : NUPPT) (q : PolyExpr) (n : ℕ)
         encCt S n (pairFstD (S.gen.runAt n [] rg)) ω ((List.ofFn p.1).headD false) false)) =
       encCt S n (pairFstD (S.gen.runAt n [] rg)) ω ((List.ofFn p.1).headD false) true ++
         encCt S n (pairFstD (S.gen.runAt n [] rg)) ω ((List.ofFn p.1).headD false) false :=
-    GGMRed.ofFn_padFin_of_length (by
+    ofFn_padFin_of_length (by
       rw [List.length_append, encCt_eq, encCt_eq, EnsembleLemmas.length_padL,
         EnsembleLemmas.length_padL, encHandler_outLen, PolyExpr.eval_add])
   dsimp only
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Decrypt.lean b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Decrypt.lean
index 7acb81676..36b61a520 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Decrypt.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Decrypt.lean
@@ -297,7 +297,7 @@ theorem simulate_decHandler_finish (n : ℕ) (z : List Bool)
           [decide (D.output (NUPPT.layout (List.replicate n true)
             ((List.range (ℓ.eval n)).map fun i => List.ofFn (ans (decBlock S n a i) st)).flatten
             (pairSndD z) (List.ofFn ω)) = [true])] :=
-        GGMRed.ofFn_padFin_of_length (by rw [List.length_singleton, hout])
+        ofFn_padFin_of_length (by rw [List.length_singleton, hout])
       exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).symm.trans
         (decodeBitMove_ret _ _ _ _)
     | succ m ih =>
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Encrypt.lean b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Encrypt.lean
index fc9acf3b7..491119076 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Encrypt.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Encrypt.lean
@@ -175,9 +175,9 @@ theorem ofFn_encTape (n : ℕ) (ω : Fin ((encHandler S).seedLen.eval n) → Boo
     rw [List.length_ofFn, encHandler_seedLen, PolyExpr.eval_add]
   rw [encTape_eq, NUPPT.coinsEquivPoly_symm_ofFn]
   cases β
-  · exact GGMRed.ofFn_padFin_of_length (by
+  · exact ofFn_padFin_of_length (by
       rw [if_neg Bool.false_ne_true, List.length_drop, hω]; omega)
-  · exact GGMRed.ofFn_padFin_of_length (by rw [if_pos rfl, List.length_take, hω]; omega)
+  · exact ofFn_padFin_of_length (by rw [if_pos rfl, List.length_take, hω]; omega)
 
 /-- **Ciphertext `β` of the reduction's output**, for the public key `z`, the seed `ω` and the
 guess `g`: `padL ctLen(n) (Enc_z(b^{msgLen(n)}); encTape β)` with `b = g` for `β = true` and
@@ -234,7 +234,7 @@ theorem encHandler_finish (n : ℕ) (z : List Bool)
         encCt S n z ω ((List.ofFn a).headD false) false)) =
       encCt S n z ω ((List.ofFn a).headD false) true ++
         encCt S n z ω ((List.ofFn a).headD false) false :=
-    GGMRed.ofFn_padFin_of_length (by
+    ofFn_padFin_of_length (by
       rw [List.length_append, encCt_eq, encCt_eq, EnsembleLemmas.length_padL,
         EnsembleLemmas.length_padL, encHandler_outLen, PolyExpr.eval_add])
   show decodeBitMove _ _ _ ((encHandler S).finRun _) = _
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation.lean b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation.lean
index a20f63411..ef63d352c 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation.lean
@@ -478,7 +478,6 @@ theorem snmIdeal_eq (M : MsgSampler) (Sim : NUPPT) (r sl : ℕ) (D : NUPPT) (n :
 section Transport
 
 open NMSim
-open AdaptiveCPA (castImpl castImpl_eq expect_simulate_castImpl_toCompOn padFin_ofFn_zeroBits)
 
 /-- **The real experiment's oracles on T2's lengths are the hybrid oracle with `b = false`:**
 read along `snmDin`, `snmDout`, `snmImpl` is `NMSim.rImpl … false … ρ ρ' none` (for every `ρ'`).
@@ -492,11 +491,11 @@ theorem castImpl_snmImpl (atk : Attack) (M : MsgSampler) (n : ℕ) (pk sk : List
         (outs := fun i => (snmDout S M.histLen i).eval n) (S.snmImpl atk M n pk sk ρ) =
       rImpl S atk false M.samp M.paramLen M.histLen M.hist n pk sk ρ ρ' none := by
   funext i x s
-  rw [castImpl_eq]
+  rw [Games.castImpl_eq]
   match i, s with
   | 0, s =>
     have hx : List.ofFn (padFin (S.ctLen.eval n) (List.ofFn x)) = List.ofFn x :=
-      GGMRed.ofFn_padFin_of_length (by
+      ofFn_padFin_of_length (by
         rw [List.length_ofFn]; show (snmDin S M.paramLen 0).eval n = _; rw [snmDin_zero])
     erw [S.snmImpl_dec atk M n pk sk ρ (padFin (S.ctLen.eval n) (List.ofFn x)) s]
     rw [rImpl_dec, hx]
@@ -505,7 +504,7 @@ theorem castImpl_snmImpl (atk : Attack) (M : MsgSampler) (n : ℕ) (pk sk : List
     · rw [if_pos hc, if_pos hc, OracleComp.pure_bind]
     · rw [if_neg hc, if_neg hc, OracleComp.pure_bind]
       dsimp only
-      erw [padFin_ofFn_zeroBits]
+      erw [Games.padFin_ofFn_zeroBits]
   | 1, some (y, a) =>
     erw [S.snmImpl_challenge atk M n pk sk ρ (padFin (M.paramLen.eval n) (List.ofFn x))
       (some (y, a))]
@@ -630,7 +629,7 @@ theorem accept_snmReal_eq (atk : Attack) (M : MsgSampler) (A : NUPPT) (q r sl :
     funext res
     rw [ProbComp.prob_pure, snmView_realView]
   exact (congrArg (ProbComp.expect _) hG).trans
-    (expect_simulate_castImpl_toCompOn (snmDin_eval S M n) (snmDout_eval S M n)
+    (Games.expect_simulate_castImpl_toCompOn (snmDin_eval S M n) (snmDout_eval S M n)
       (rfl : r * S.ctLen.eval n + sl = r * S.ctLen.eval n + sl)
       (S.snmImpl atk M n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg)) ρ) A n q
       (pairFstD (S.gen.runAt n [] rg)) rA none fun p : List Bool × S.SnmState M n =>
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Challenge.lean b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Challenge.lean
index 94eefbf83..8915ae42d 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Challenge.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Challenge.lean
@@ -207,7 +207,7 @@ theorem ofFn_chalState_some (y : Fin (S.ctLen.eval n) → Bool) (h : Fin (hl.eva
     List.ofFn (chalState P n (some (y, h, a))) =
       true :: (List.ofFn y ++ List.ofFn h ++ List.ofFn a) := by
   rw [chalState_some]
-  refine GGMRed.ofFn_padFin_of_length ?_
+  refine ofFn_padFin_of_length ?_
   rw [List.length_cons, List.length_append, List.length_append, List.length_ofFn, List.length_ofFn,
     List.length_ofFn, chalHandler_stateLen_eval]
   omega
@@ -235,15 +235,6 @@ theorem headD_ofFn_chalState
 
 end State
 
-/-- A padded run of `false`s is all `false`: `padFin d (0^m) = 0`. -/
-private theorem padFin_replicate_false (d m : ℕ) :
-    padFin d (List.replicate m false) = zeroBits d := by
-  funext i
-  rw [padFin_apply, zeroBits_apply]
-  by_cases h : (i : ℕ) < m
-  · rw [List.getD_eq_getElem _ _ (by rw [List.length_replicate]; exact h), List.getElem_replicate]
-  · rw [List.getD_eq_default _ _ (by rw [List.length_replicate]; omega)]
-
 section Calls
 
 variable (P : ChalParams S pl hl k' din' dout') (n : ℕ) (z : List Bool)
@@ -261,7 +252,7 @@ theorem chalHandler_impl_dec (x : Fin ((snmDin S pl 0).eval n) → Bool)
     (by rw [List.length_replicate, snmDout_zero]) List.length_ofFn (by
       show chalRun P _ = _
       rw [chalRun_eq, hI, hU, hS, List.length_replicate]
-      rfl), padFin_replicate_false, padFin_ofFn]
+      rfl), Games.padFin_replicate_false, padFin_ofFn]
 
 /-- **A repeated challenge answers the recorded `⟨Y, H⟩`** and keeps the state, asking nothing. -/
 theorem chalHandler_impl_some (x : Fin ((snmDin S pl 1).eval n) → Bool)
@@ -327,14 +318,14 @@ theorem chalHandler_impl_none (x : Fin ((snmDin S pl 1).eval n) → Bool) :
   obtain ⟨hU₀, -, -, hS₀, hI₀, -, hL₀⟩ := fields_input (k := 2) n z (List.ofFn ω)
     (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x) []
   have hq : List.ofFn (padFin ((din' P.j).eval n) (P.qry w₀)) = P.qry w₀ :=
-    GGMRed.ofFn_padFin_of_length (by rw [P.qry_len, hU₀, List.length_replicate])
+    ofFn_padFin_of_length (by rw [P.qry_len, hU₀, List.length_replicate])
   have hxl : (List.ofFn x).length = pl.eval n := by
     rw [List.length_ofFn]
     show (snmDin S pl 1).eval n = _
     rw [snmDin_one]
   have hx : EnsembleLemmas.padL (pl.eval n) (List.ofFn x) =
       List.ofFn (padFin (pl.eval n) (List.ofFn x)) := by
-    rw [EnsembleLemmas.padL_eq, GGMRed.ofFn_padFin_of_length hxl]
+    rw [EnsembleLemmas.padL_eq, ofFn_padFin_of_length hxl]
     exact List.take_left' hxl
   have hpc : 1 ≤ (chalHandler P).perCall.eval n := by
     rw [chalHandler_perCall, PolyExpr.eval_const]
@@ -368,7 +359,7 @@ theorem chalHandler_impl_none (x : Fin ((snmDin S pl 1).eval n) → Bool) :
     rw [chalRun_eq, hW₁]
     beta_reduce
     rw [hI₁, hU₁, hS₁, hL₁, hQ₁, List.length_replicate, headD_ofFn_chalState, hx,
-      ofFn_chalState_some, GGMRed.ofFn_padFin_of_length (hY y), GGMRed.ofFn_padFin_of_length (hH y)]
+      ofFn_chalState_some, ofFn_padFin_of_length (hY y), ofFn_padFin_of_length (hH y)]
     rw [if_neg (by simp), if_neg (by simp),
       if_neg (fun h => pairEncode_ne_nil _ _ (of_decide_eq_true h))]
 
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/IndSim.lean b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/IndSim.lean
index 035c0da6a..dedbe2166 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/IndSim.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/IndSim.lean
@@ -39,7 +39,6 @@ None: this module only proves results. `B`'s handler parameters `nmParams` and t
 namespace TCSlib.Cryptography.Composability.NMSim
 
 open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
-open AdaptiveCPA (simulate_eq_of_abs)
 
 variable (S : FixedLengthPKScheme) (samp : NUPPT) (pl hl : PolyExpr)
   (hist : List Bool → List Bool) (hist_poly : PolyTimeComputable hist) (r sl : PolyExpr)
@@ -130,7 +129,7 @@ theorem recView_nmOut (rg : S.gen.Coins n) (hL : 0 < S.msgLen.eval n) (ρ ρ' :
       (pairEncode (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re))
         (List.ofFn (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s).1))) a _ _ ha haP hmP
   rw [← nmParams_outLen_eval S samp pl hl hist hist_poly r sl n] at hlen
-  rw [GGMRed.ofFn_padFin_of_length hlen, nmAbs_snd_fst,
+  rw [ofFn_padFin_of_length hlen, nmAbs_snd_fst,
     recView_nmOutL S pl r sl samp n rg hL (s.map Prod.fst) _ _ _ a _ _
       (pairFstD_pairEncode _ _) re
       (by rw [hω, PolyExpr.eval_add, ← List.append_assoc, List.drop_left' (by
@@ -218,7 +217,8 @@ theorem nmRun_eq (B₀ : NUPPT) (n : ℕ)
       (NUPPT.coinsCongr (recDist_coins S pl r X).symm n rX) = true then 1 else 0)).trans ?_
   rw [← hφ, nmParams_advInput, chalHandler_init, simulate_bind, simulate_comp,
     ← nmAbs_none S samp pl hl hist hist_poly r sl n ρ ρ',
-    simulate_eq_of_abs _ _ _ (nmComp_abs S samp pl hl hist hist_poly r sl n _ _ ρ ρ' re b ρ''),
+    Games.simulate_eq_of_abs _ _ _
+      (nmComp_abs S samp pl hl hist hist_poly r sl n _ _ ρ ρ' re b ρ''),
     OracleComp.bind_assoc, OracleComp.bind_assoc]
   simp only [OracleComp.pure_bind, hfin, simulate_pure]
   rw [ProbComp.expect_bind]
@@ -271,19 +271,19 @@ theorem exists_nmAdversary : ∃ (B : NUPPT) (qB : PolyExpr), ∀ (X : NUPPT) (n
   rw [accept_nmGame_eq_rImpl S .cpa B _ _ (recDist S pl r X) b n (fun _ => [])
     ((halfCoins S n).symm false), hybAcc_eq, hK]
   refine congrArg _ (funext fun rg => ?_)
-  rw [← ChallengeSim.expect_sample_equiv (NUPPT.coinsCongr hc n)]
+  rw [← ProbComp.expect_sample_equiv (NUPPT.coinsCongr hc n)]
   simp only [hB]
-  rw [← ChallengeSim.expect_sample_equiv φ, ChallengeSim.expect_sample_prod,
-    ← ChallengeSim.expect_sample_equiv
+  rw [← ProbComp.expect_sample_equiv φ, ChallengeSim.expect_sample_prod,
+    ← ProbComp.expect_sample_equiv
       (seedEquivPoly (nmParams_seedLen_handler S samp pl hl hist hist_poly r sl) n),
     ChallengeSim.expect_sample_prod]
   refine congrArg _ (funext fun ρ => ?_)
-  rw [← ChallengeSim.expect_sample_equiv (seedEquiv (A := samp) (B := S.enc) rfl n),
+  rw [← ProbComp.expect_sample_equiv (seedEquiv (A := samp) (B := S.enc) rfl n),
     ChallengeSim.expect_sample_prod]
   refine congrArg _ (funext fun ρ' => ?_)
   refine Eq.trans ?_ (ProbComp.expect_const (ProbComp.sample (S.enc.Coins n)) _)
   refine congrArg _ (funext fun re => congrArg _ (funext fun rA => ?_))
-  rw [← ChallengeSim.expect_sample_equiv (NUPPT.coinsCongr (recDist_coins S pl r X).symm n)]
+  rw [← ProbComp.expect_sample_equiv (NUPPT.coinsCongr (recDist_coins S pl r X).symm n)]
   refine congrArg _ (funext fun rX => ?_)
   rw [← nmSeed_eq]
   exact nmRun_eq S samp pl hl hist hist_poly r sl A q B₀ n φ hφ rg hL ρ ρ' re rA b _ X rX
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Reduction.lean b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Reduction.lean
index 595c20d44..61d805562 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Reduction.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Reduction.lean
@@ -494,7 +494,7 @@ theorem nmMsgs_input (pk : List Bool) (ρ ρ' : samp.Coins n) (re : S.enc.Coins
   have hρ' := length_ofFn_coins samp n ρ'
   rw [simMsg_eq, altMsg_eq, hU, hZ, hW, hQ, List.length_replicate, pairSndD_pairEncode,
     nmSeed_ofFn, List.take_left' hρ, List.drop_left' hρ, List.take_left' hρ', drawWith_eq,
-    drawWith_eq, GGMRed.ofFn_padFin_of_length hxs, ofFn_padFin_eq_padL, ofFn_padFin_eq_padL,
+    drawWith_eq, ofFn_padFin_of_length hxs, ofFn_padFin_eq_padL, ofFn_padFin_eq_padL,
     NUPPT.runAt_eq, NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout, NUPPT.runAtL_eq_output_layout]
   exact ⟨rfl, rfl⟩
 
@@ -623,7 +623,7 @@ theorem nmComp_abs (pk sk : List Bool) (ρ ρ' : samp.Coins n) (re : S.enc.Coins
             ρ')).length = (S.msgLen.add S.msgLen).eval n := by
         rw [List.length_append, List.length_ofFn, List.length_ofFn, hpl]
       rw [encWith_eq, encWith_eq, ofFn_drawWith_half S n _ hpl, nmPair_eq,
-        GGMRed.ofFn_padFin_of_length hlen]
+        ofFn_padFin_of_length hlen]
       cases b
       · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
           List.take_left' List.length_ofFn]
@@ -637,13 +637,13 @@ theorem nmComp_abs (pk sk : List Bool) (ρ ρ' : samp.Coins n) (re : S.enc.Coins
     have hx' : List.ofFn (padFin ((snmDin S (S.msgLen.add S.msgLen) 1).eval n)
         (List.ofFn (nmPair S samp pl n ρ ρ' (padFin (pl.eval n) (List.ofFn x))))) =
         List.ofFn (nmPair S samp pl n ρ ρ' (padFin (pl.eval n) (List.ofFn x))) :=
-      GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, snmDin_one])
+      ofFn_padFin_of_length (by rw [List.length_ofFn, snmDin_one])
     have hlen : (List.ofFn (encWith S n pk (drawWith samp (S.msgLen.eval n) n
         (padFin (pl.eval n) (List.ofFn x)) (if b then ρ' else ρ)) re') ++ []).length =
         (snmDout S (.const 0) 1).eval n := by
       rw [List.append_nil, List.length_ofFn, snmDout_one, PolyExpr.eval_add, PolyExpr.eval_const,
         Nat.add_zero]
-    have hans := GGMRed.ofFn_padFin_of_length hlen
+    have hans := ofFn_padFin_of_length hlen
     rw [rImpl_none_eager, rImpl_none_eager]
     simp only [OracleComp.pure_bind, simulate_pure, nmAbs_some, Bool.false_eq_true, ↓reduceIte, hq]
     rw [hx', padFin_ofFn (nmPair S samp pl n ρ ρ' (padFin (pl.eval n) (List.ofFn x))), hdraw, h0]
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Rounds.lean b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Rounds.lean
index ce201832d..0bd479f47 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Rounds.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Rounds.lean
@@ -177,7 +177,7 @@ theorem impl_of_ret (i : Fin k) (x : Fin ((din i).eval n) → Bool)
       pairEncode [true] (u ++ v)) :
     H.impl n z ω i x s = .pure (padFin _ u, padFin _ v) := by
   have hw : u ++ v = List.ofFn (padFin ((dout i).eval n + H.stateLen.eval n) (u ++ v)) :=
-    (GGMRed.ofFn_padFin_of_length (by rw [List.length_append, hu, hv])).symm
+    (ofFn_padFin_of_length (by rw [List.length_append, hu, hv])).symm
   rw [InteractiveHandler.impl_apply, InteractiveHandler.call_eq,
     buildComp_of_ret (a := padFin ((dout i).eval n + H.stateLen.eval n) (u ++ v)) (by
       rw [MachineCodec.encodeLog_nil, hrun]
@@ -220,7 +220,7 @@ theorem impl_of_query (i : Fin k) (x : Fin ((din i).eval n) → Bool)
     rw [List.nil_append, MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil,
       bitCodec_encodeEntry]
   have hw : u y ++ v y = List.ofFn (padFin ((dout i).eval n + H.stateLen.eval n) (u y ++ v y)) :=
-    (GGMRed.ofFn_padFin_of_length (by rw [List.length_append, hu, hv])).symm
+    (ofFn_padFin_of_length (by rw [List.length_append, hu, hv])).symm
   rw [buildComp_of_ret (a := padFin ((dout i).eval n + H.stateLen.eval n) (u y ++ v y)) (by
       rw [hlog, hrun₁]
       exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).trans
@@ -239,7 +239,7 @@ theorem finish_of_ret (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ} (a : Fin
   refine buildComp_of_ret ?_
   rw [MachineCodec.encodeLog_nil, hrun]
   exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w))
-    (GGMRed.ofFn_padFin_of_length hb).symm).trans (decodeBitMove_ret _ _ _ _)
+    (ofFn_padFin_of_length hb).symm).trans (decodeBitMove_ret _ _ _ _)
 
 end Calls
 
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean
index f027536d5..3e06a04d2 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean
@@ -46,8 +46,6 @@ oracle's run with the coin `β` (`accept_nmGame_eq_rImpl`).
 namespace TCSlib.Cryptography.Composability.NMSim
 
 open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim
-open AdaptiveCPA (castImpl castImpl_eq ofFn_cast ofFn_splitHalf_fst ofFn_splitHalf_snd
-  padFin_ofFn_zeroBits expect_simulate_castImpl_toCompOn simulate_eq_of_abs)
 
 variable (S : FixedLengthPKScheme)
 
@@ -128,7 +126,7 @@ theorem ofFn_drawWith_half (n : ℕ) {k : ℕ} (a : Fin k → Bool)
     List.ofFn (drawWith (halfSamp S) (S.msgLen.eval n) n a ((halfCoins S n).symm β)) =
       if β then (List.ofFn a).drop (S.msgLen.eval n) else (List.ofFn a).take (S.msgLen.eval n) := by
   rw [drawWith_eq, halfSamp_runAt, headD_ofFn_halfCoins_symm]
-  refine GGMRed.ofFn_padFin_of_length ?_
+  refine ofFn_padFin_of_length ?_
   cases β <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_take, List.length_drop,
     List.length_ofFn] <;> omega
 
@@ -137,7 +135,7 @@ theorem ofFn_drawWith_half (n : ℕ) {k : ℕ} (a : Fin k → Bool)
 theorem expect_sample_halfCoins (n : ℕ) (g : (halfSamp S).Coins n → ℝ) :
     expect (sample ((halfSamp S).Coins n)) g =
       (g ((halfCoins S n).symm false) + g ((halfCoins S n).symm true)) / 2 := by
-  rw [← expect_sample_equiv (halfCoins S n).symm, expect_sample, Fintype.sum_bool,
+  rw [← ProbComp.expect_sample_equiv (halfCoins S n).symm, expect_sample, Fintype.sum_bool,
     Fintype.card_bool]
   ring
 
@@ -178,11 +176,11 @@ theorem castImpl_indImpl_abs (atk : Attack) (β : Bool) (n : ℕ) (pk sk : List
         padFin (S.ctLen.eval n) (List.ofFn x) := by
       apply List.ofFn_injective
       rw [ofFn_cast (S.inLens_zero n),
-        GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hd0, S.inLens_zero]),
-        GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hd0])]
+        ofFn_padFin_of_length (by rw [List.length_ofFn, hd0, S.inLens_zero]),
+        ofFn_padFin_of_length (by rw [List.length_ofFn, hd0])]
     have hx : List.ofFn (padFin (S.ctLen.eval n) (List.ofFn x)) = List.ofFn x :=
-      GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hd0])
-    rw [castImpl_eq, S.indImpl_dec_onSpec_cast, rImpl_dec, hc, Option.isSome_map, hx]
+      ofFn_padFin_of_length (by rw [List.length_ofFn, hd0])
+    rw [Games.castImpl_eq, S.indImpl_dec_onSpec_cast, rImpl_dec, hc, Option.isSome_map, hx]
     by_cases hcond : (FixedLengthScheme.decOpen atk s.isSome &&
         !decide (s.map Prod.fst = some (padFin (S.ctLen.eval n) (List.ofFn x)))) = true
     · rw [if_pos hcond, if_pos hcond, OracleComp.pure_bind, OracleComp.pure_bind]
@@ -190,7 +188,7 @@ theorem castImpl_indImpl_abs (atk : Attack) (β : Bool) (n : ℕ) (pk sk : List
       rw [ofFn_cast (S.outLens_zero n).symm]
     · rw [if_neg hcond, if_neg hcond, OracleComp.pure_bind, OracleComp.pure_bind]
       dsimp only
-      rw [padFin_ofFn_zeroBits]
+      rw [Games.padFin_ofFn_zeroBits]
   | 1, x =>
     have hh : ∀ {ℓ : ℕ} (m : Fin ℓ → Bool),
         List.ofFn (histWith hist ((PolyExpr.const 0).eval n) m) = [] := fun m =>
@@ -198,12 +196,12 @@ theorem castImpl_indImpl_abs (atk : Attack) (β : Bool) (n : ℕ) (pk sk : List
     cases s with
     | some ya =>
       obtain ⟨y, a⟩ := ya
-      rw [Option.map_some, castImpl_eq, S.indImpl_challenge_repeat_onSpec, OracleComp.pure_bind,
-        rImpl_some, OracleComp.pure_bind]
+      rw [Option.map_some, Games.castImpl_eq, S.indImpl_challenge_repeat_onSpec,
+        OracleComp.pure_bind, rImpl_some, OracleComp.pure_bind]
       dsimp only
       rw [ofFn_cast (S.outLens_one n).symm, hh, List.append_nil, Option.map_some]
     | none =>
-      rw [Option.map_none, castImpl_eq, S.indImpl_challenge_none_onSpec, rImpl_none_lazy,
+      rw [Option.map_none, Games.castImpl_eq, S.indImpl_challenge_none_onSpec, rImpl_none_lazy,
         OracleComp.bind_assoc, OracleComp.bind_assoc]
       refine congrArg _ (funext fun re => ?_)
       rw [OracleComp.pure_bind, rImpl_none_eager, OracleComp.pure_bind]
@@ -217,12 +215,13 @@ theorem castImpl_indImpl_abs (atk : Attack) (β : Bool) (n : ℕ) (pk sk : List
             (padFin (S.inLens n 1) (List.ofFn x))) =
             List.ofFn (padFin ((S.msgLen.add S.msgLen).eval n) (List.ofFn x)) := by
           rw [ofFn_cast (S.inLens_one n),
-            GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hd1, hpl, S.inLens_one]),
-            GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hd1])]
+            ofFn_padFin_of_length (by rw [List.length_ofFn, hd1, hpl, S.inLens_one]),
+            ofFn_padFin_of_length (by rw [List.length_ofFn, hd1])]
         rw [ofFn_drawWith_half S n _ hpl]
         cases β
-        · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, ofFn_splitHalf_fst, hx]
-        · rw [if_pos rfl, if_pos rfl, ofFn_splitHalf_snd, hx]
+        · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
+            FixedLengthScheme.ofFn_splitHalf_fst, hx]
+        · rw [if_pos rfl, if_pos rfl, FixedLengthScheme.ofFn_splitHalf_snd, hx]
       have he : encWith S n pk (drawWith (halfSamp S) (S.msgLen.eval n) n
           (padFin ((S.msgLen.add S.msgLen).eval n) (List.ofFn x))
           (if false = true then ρ' else (halfCoins S n).symm β)) re =
@@ -276,12 +275,13 @@ theorem accept_nmGame_eq_rImpl (atk : Attack) (A : NUPPT) (q ℓ : ℕ) (D : NUP
     dsimp only
     rw [padFin_ofFn]
   rw [prob_bind, S.nmCodec_eq_bitCodec, h2]
-  refine (expect_simulate_castImpl_toCompOn (snmDin_eval_inLens S n) (snmDout_eval_outLens S n)
-    rfl (S.indImpl atk β n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg))) A n q
+  refine (Games.expect_simulate_castImpl_toCompOn (snmDin_eval_inLens S n)
+    (snmDout_eval_outLens S n) rfl
+    (S.indImpl atk β n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg))) A n q
     _ r none (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
       if D.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) p.2
         (padFin (ℓ * S.ctLen.eval n) p.1)) rD = true then (1 : ℝ) else 0)).symm.trans ?_
-  have habs := simulate_eq_of_abs _ _ (Option.map Prod.fst)
+  have habs := Games.simulate_eq_of_abs _ _ (Option.map Prod.fst)
     (fun i x s => castImpl_indImpl_abs S atk β n (pairFstD (S.gen.runAt n [] rg))
       (pairSndD (S.gen.runAt n [] rg)) hist ρ' i x s)
     (A.toCompOn (bitCodec (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n)
@@ -358,7 +358,7 @@ theorem copyHandler_finish (pl hl outLen : PolyExpr) (n : ℕ) (z : List Bool)
   show decodeBitMove _ _ _ ((copyHandler S pl hl outLen).finRun _) = _
   rw [hfin, copyFin, (fields_finInput _ _ _ _ _ _).2.2.2.1]
   have hw : List.ofFn (padFin ((copyHandler S pl hl outLen).outLen.eval n) (List.ofFn a)) =
-      List.ofFn a := GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hol, hd])
+      List.ofFn a := ofFn_padFin_of_length (by rw [List.length_ofFn, hol, hd])
   exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).symm.trans
     (decodeBitMove_ret _ _ _ _)
 
@@ -624,7 +624,7 @@ theorem nmOutput_eq_entryTails (n ℓ : ℕ) (sk : List Bool)
   rw [List.getElem_ofFn, List.getElem_map, List.getElem_range, entryL_drop_one, S.nmDecrypt_eq]
   have hc : List.ofFn (S.nthCt (padFin (ℓ * S.ctLen.eval n) w) ⟨i, by
       rw [List.length_ofFn] at h₁; exact h₁⟩) = chunkAt (S.ctLen.eval n) i w := by
-    rw [S.ofFn_nthCt, GGMRed.ofFn_padFin_of_length hw, chunkAt_eq]
+    rw [S.ofFn_nthCt, ofFn_padFin_of_length hw, chunkAt_eq]
   have hcopy : (s' = some (S.nthCt (padFin (ℓ * S.ctLen.eval n) w) ⟨i, by
       rw [List.length_ofFn] at h₁; exact h₁⟩)) ↔
       s'.map List.ofFn = some (chunkAt (S.ctLen.eval n) i w) := by
@@ -846,21 +846,21 @@ theorem real_identity (D : NUPPT) (rD : D.Coins n) (ρ'' : (halfDist S).Coins n)
           expect (runB S atk A q ℓ n hist pk sk r ρ' β) (fun p => if badHalves S n p.2 then 0
             else f p) := by
     intro β f
-    rw [← expect_sub]
+    rw [← ProbComp.expect_sub]
     refine congrArg _ (funext fun p => ?_)
     split <;> ring
   simp only [fun β p => (hview β p).1, fun β p => (hview β p).2]
   simp only [Bool.false_eq_true, ↓reduceIte]
   have hsub0 : expect (runB S atk A q ℓ n hist pk sk r ρ' false) (fun p => 1 - v p) =
       1 - expect (runB S atk A q ℓ n hist pk sk r ρ' false) v := by
-    rw [expect_sub, expect_const]
+    rw [ProbComp.expect_sub, expect_const]
   have hsub0' : expect (runB S atk A q ℓ n hist pk sk r ρ' false)
       (fun p => if badHalves S n p.2 then 0 else 1 - v p) =
       expect (runB S atk A q ℓ n hist pk sk r ρ' false)
         (fun p => if badHalves S n p.2 then 0 else 1) -
       expect (runB S atk A q ℓ n hist pk sk r ρ' false)
         (fun p => if badHalves S n p.2 then 0 else v p) := by
-    rw [← expect_sub]
+    rw [← ProbComp.expect_sub]
     refine congrArg _ (funext fun p => ?_)
     split <;> ring
   rw [hsplit false (fun p => 1 - v p), hsplit true v, hsplit false (fun _ => 1),
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/SimINDGap.lean b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/SimINDGap.lean
index d4419e234..0dd5adcfe 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/SimINDGap.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/SimINDGap.lean
@@ -55,14 +55,14 @@ private theorem lin_expect {α : Type} (c : ProbComp α) (A₀ A₁ B₀ B₁ C
   have hC : expect c (fun x => C₁ x - C₀ x) =
       expect c (fun x => (A₀ x + A₁ x) - 2⁻¹ * (B₀ x + B₁ x)) :=
     congrArg _ (funext fun x => by linarith [h x])
-  rw [← expect_sub, hC, expect_sub, expect_const_mul, expect_add, expect_add]
+  rw [← ProbComp.expect_sub, hC, ProbComp.expect_sub, expect_const_mul, expect_add, expect_add]
   ring
 
 /-- `2·f − g = h₁ − h₀` pointwise passes to expectations. -/
 private theorem lin_expect' {α : Type} (c : ProbComp α) (f g h₀ h₁ : α → ℝ)
     (h : ∀ x, 2 * f x - g x = h₁ x - h₀ x) :
     2 * expect c f - expect c g = expect c h₁ - expect c h₀ := by
-  rw [← expect_const_mul, ← expect_sub, ← expect_sub]
+  rw [← expect_const_mul, ← ProbComp.expect_sub, ← ProbComp.expect_sub]
   exact congrArg _ (funext h)
 
 /-- **The coupling in expectation:** if `T₀(e c) + T₁(e c) − (H₀ b + H₁ b)/2 = V₁ c − V₀ c` for all
@@ -82,8 +82,8 @@ private theorem lin_sample {α β γ : Type} [Fintype α] [Nonempty α] [Fintype
   have hT : expect (sample γ) (fun c => T₀ (e c) + T₁ (e c) - (V₁ c - V₀ c)) =
       expect (sample γ) (fun _ => (H₀ b₀ + H₁ b₀) / 2) :=
     congrArg _ (funext fun c => by linarith [h c b₀])
-  rw [expect_sub, expect_add, expect_sub, expect_const,
-    expect_sample_equiv e T₀, expect_sample_equiv e T₁] at hT
+  rw [ProbComp.expect_sub, expect_add, ProbComp.expect_sub, expect_const,
+    ProbComp.expect_sample_equiv e T₀, ProbComp.expect_sample_equiv e T₁] at hT
   rw [expect_add, expect_const] at hH
   linarith [h c₀ b₀]
 
@@ -127,7 +127,7 @@ theorem realAcc_copyHandler (atk : Attack) (samp : NUPPT) (pl hl : PolyExpr)
   subst hK
   rw [realAcc_eq]
   refine congrArg _ (funext fun rg => congrArg _ (funext fun ρ => ?_))
-  rw [← expect_sample_equiv φ, expect_sample_prod]
+  rw [← ProbComp.expect_sample_equiv φ, expect_sample_prod]
   refine Eq.trans ?_
     (expect_const (sample (Fin ((copyHandler S pl hl outL).seedLen.eval n) → Bool)) _)
   refine congrArg _ (funext fun ω => congrArg _ (funext fun rA => congrArg _ (funext fun rX => ?_)))
@@ -140,7 +140,7 @@ theorem realAcc_copyHandler (atk : Attack) (samp : NUPPT) (pl hl : PolyExpr)
   refine congrArg _ (funext fun p => ?_)
   rw [expect_pure]
   dsimp only
-  rw [GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, copyHandler_outLen, hd])]
+  rw [ofFn_padFin_of_length (by rw [List.length_ofFn, copyHandler_outLen, hd])]
 
 /-- **The SIM adversary's handler** for an NM adversary with `ℓ` output ciphertexts:
 `copyHandler` on
@@ -324,9 +324,9 @@ theorem ideal_gap (Sim D : NUPPT) (r n : ℕ) :
     intro X
     rw [idealAcc_eq]
     refine congrArg _ (funext fun rg => ?_)
-    rw [expect_sample_comm]
+    rw [ProbComp.expect_sample_comm]
     refine congrArg _ (funext fun rS => ?_)
-    rw [expect_sample_comm]
+    rw [ProbComp.expect_sample_comm]
     refine congrArg _ (funext fun rX => ?_)
     rw [expect_sample_halfCoins, histImpl_coins S _ _ _ _ n ((halfCoins S n).symm true)
       ((halfCoins S n).symm false) hhl, ← expect_add, div_eq_inv_mul, ← expect_const_mul]
@@ -336,7 +336,8 @@ theorem ideal_gap (Sim D : NUPPT) (r n : ℕ) :
   refine congrArg _ (funext fun rS => ?_)
   symm
   refine Eq.trans (congrArg _ (funext fun ρ'' => ?_)) (expect_const (sample _) _)
-  rw [← expect_sample_equiv (NUPPT.coinsCongr (tailDist_coins S D).symm n), ← expect_const_mul]
+  rw [← ProbComp.expect_sample_equiv (NUPPT.coinsCongr (tailDist_coins S D).symm n),
+    ← expect_const_mul]
   symm
   refine Eq.trans (congrArg _ (funext fun rD => ?_)) (expect_const (sample _) _)
   rw [← expect_const_mul]
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Simulator.lean b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Simulator.lean
index 5a3e0f550..2e67f7489 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Simulator.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Simulator.lean
@@ -45,7 +45,6 @@ namespace TCSlib.Cryptography.Composability.NMSim
 
 open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
 open NMCCA2 (finU finA fields_finInput polyTimeComputable_finFields)
-open AdaptiveCPA (simulate_eq_of_abs)
 
 variable (S : FixedLengthPKScheme) (samp : NUPPT)
 
@@ -388,7 +387,7 @@ theorem simCt_input (pk : List Bool) (ρ' : samp.Coins n) (re : S.enc.Coins n) (
     pairSndD_pairEncode, seedEquiv_ofFn,
     List.take_left' (length_ofFn_coins samp n ρ'), List.drop_left' (length_ofFn_coins samp n ρ'),
     encWith_eq, drawWith_eq, ofFn_padFin_eq_padL, ofFn_padFin_eq_padL,
-    GGMRed.ofFn_padFin_of_length hxl, NUPPT.Uniform.runAt_eq S.enc_uniform, NUPPT.advInput_eq,
+    ofFn_padFin_of_length hxl, NUPPT.Uniform.runAt_eq S.enc_uniform, NUPPT.advInput_eq,
     NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout]
 
 /-- **The simulator against the history oracle is the hybrid with an independent draw:** for the
@@ -485,7 +484,7 @@ theorem idealView_simOut (sk : List Bool) (ρ : samp.Coins n)
     rw [simParams_outLen_eval, simOutL_eq, List.length_append, List.length_drop, ha,
       length_flatten_map_range (S.ctLen.eval n + 1) _ _ hg, Nat.mul_add, Nat.mul_one]
     omega
-  rw [GGMRed.ofFn_padFin_of_length hlen, simAbs_snd, idealView_eq, realView_eq, simOutL_eq,
+  rw [ofFn_padFin_of_length hlen, simAbs_snd, idealView_eq, realView_eq, simOutL_eq,
     drop_flatten_append _ _ _ hg]
   congr 3
   refine List.map_congr_left fun i hi => ?_
@@ -575,7 +574,7 @@ theorem simRun_eq (Sim₀ : NUPPT) (n : ℕ)
     exact OracleComp.costBoundedBy_pure _ _ _), ← hφ z ω rA, simParams_advInput, chalHandler_init,
     simulate_bind,
     simulate_comp, ← simAbs_none S samp pl hl hist r sl n ρ,
-    simulate_eq_of_abs _ _ _ (simComp_abs S samp pl hl hist r sl n pk sk ρ ρ' re),
+    Games.simulate_eq_of_abs _ _ _ (simComp_abs S samp pl hl hist r sl n pk sk ρ ρ' re),
     OracleComp.bind_assoc, OracleComp.bind_assoc]
   simp only [OracleComp.pure_bind, hfin, simulate_pure]
   rw [ProbComp.expect_bind]
@@ -610,19 +609,19 @@ theorem exists_simulator : ∃ Sim : NUPPT, ∀ (X : NUPPT) (n : ℕ),
   obtain ⟨φ, hφ⟩ := hT2 n
   rw [idealAcc_eq, hybAcc_eq]
   refine congrArg _ (funext fun rg => congrArg _ (funext fun ρ => ?_))
-  rw [← ChallengeSim.expect_sample_equiv (NUPPT.coinsCongr hc n)]
+  rw [← ProbComp.expect_sample_equiv (NUPPT.coinsCongr hc n)]
   simp only [hSim]
-  rw [← ChallengeSim.expect_sample_equiv φ, ChallengeSim.expect_sample_prod,
-    ← ChallengeSim.expect_sample_equiv (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n),
+  rw [← ProbComp.expect_sample_equiv φ, ChallengeSim.expect_sample_prod,
+    ← ProbComp.expect_sample_equiv (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n),
     ChallengeSim.expect_sample_prod]
   refine congrArg _ (funext fun ρ' => ?_)
   simp only [expect_simulate_rImpl_eager]
   refine (congrArg _ (funext fun re => congrArg _ (funext fun rA => congrArg _ (funext fun rX =>
     simRun_eq S samp pl hl hist A q r sl Sim₀ n φ hφ _ _ ρ ρ' re rA fun v =>
       if X.distinguisherL n v rX = true then 1 else 0)))).trans ?_
-  rw [ChallengeSim.expect_sample_comm]
+  rw [ProbComp.expect_sample_comm]
   refine congrArg _ (funext fun rA => ?_)
-  rw [ChallengeSim.expect_sample_comm]
+  rw [ProbComp.expect_sample_comm]
 
 end Ideal
 
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean b/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean
index a6bdf09b6..ad93fad9b 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean
@@ -8,8 +8,6 @@ import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
 import TCSlib.Cryptography.Encryption.PublicKey.EnsembleSecurity
 import TCSlib.Complexity.ClassP.BinaryArith.Loops
 import TCSlib.Cryptography.Games.Bridges.Experiments
-import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.ChallengeSim
-import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.RecordHandler
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -56,9 +54,14 @@ Security is stated for each admissible `L`; a larger `L` admits longer `Dec` que
 * `pairFstD_padCt`, `isPadded_padCt`, `padCt_of_isPadded`: padding is a bijection onto the
   canonical strings.
 * `PublicKeyScheme.exists_padBound`, `BitPublicKeyScheme.exists_padBound`: padding bounds exist.
-* `BitPublicKeyScheme.SingleBitSecure.padded_cpa`: single-bit security gives CPA security.
-  Its helpers are `OracleSecurity.ChallengeSim` (the deterministic CPA run and first-challenge
-  congruence) and `OracleSecurity.RecordHandler` (the recording handler for T1).
+* `FixedLengthPKScheme.indCodec_eq_bitCodec`: the adversary codec is a bit codec;
+  `PublicKeyScheme.padded_enc_runAt`, `padded_enc_coins`: the padded encryptor.
+
+The claim after Definition 171.5, `BitPublicKeyScheme.SingleBitSecure.padded_cpa` (single-bit
+security gives CPA security), and its eager-coins lemma `expect_simulate_indImpl_cpa` are in
+`OracleSecurity.PaddedCPA`. Its helpers are `OracleSecurity.ChallengeSim` (the deterministic CPA
+run and first-challenge congruence) and `OracleSecurity.RecordHandler` (the recording handler
+for T1).
 
 ## References
 
@@ -358,6 +361,22 @@ theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_enc :
 theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_dec :
     (S.padded L hL hmsg).dec = padDecFun S.dec := rfl
 
+/-- **The padded encryptor pads the original encryptor's output**, the coins read as a list:
+`Enc'(1^n, y; r) = padCt L(n) (Enc(1^n, y; ⟦r⟧))` (`runAt_padEnc`, `coinsCongr_ofFn`). -/
+theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_enc_runAt (n : ℕ) (y : List Bool)
+    (r : (S.padded L hL hmsg).enc.Coins n) :
+    (S.padded L hL hmsg).enc.runAt n y r = padCt (L.eval n) (S.enc.runAtL n y (List.ofFn r)) := by
+  have key : ∀ E : NUPPT, E = padEnc S.enc L → ∀ r : E.Coins n,
+      E.runAt n y r = padCt (L.eval n) (S.enc.runAtL n y (List.ofFn r)) := by
+    rintro E rfl r
+    rw [runAt_padEnc S.enc_uniform L n y r, NUPPT.runAt_eq, NUPPT.coinsCongr_ofFn]
+  exact key _ (PublicKeyScheme.padded_enc S L hL hmsg) r
+
+/-- The padded encryptor keeps the coins: `S.enc.coins = (S.padded L hL hmsg).enc.coins`. -/
+theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_enc_coins :
+    S.enc.coins = (S.padded L hL hmsg).enc.coins := by
+  rw [PublicKeyScheme.padded_enc, padEnc_coins]
+
 end PublicKeyPaddedReaders
 
 /-- **A ch. 2–4 single-bit public-key scheme, padded** to `L(n)`-bit ciphertexts: one-bit
@@ -661,6 +680,9 @@ theorem indCodec_encodeEntry (n : ℕ)
 theorem indCodec_timeout (n : ℕ) : (S.indCodec n).timeout = zeroBits 1 :=
   bitCodec_timeout (S.inLens n) (S.outLens n) 1
 
+/-- The adversary codec is a bit codec: `S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1`. -/
+theorem indCodec_eq_bitCodec (n : ℕ) : S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1 := rfl
+
 /-- **The experiment `Ind_b(Π, A, n)`** [PS10, Definition 171.5] for the attack `atk`, with query
 budget `q`: sample `(pk, sk) ← Gen(1^n)` and `A`'s coins, run `A` on `pk` against the oracles
 from the unchallenged state, and output its bit. -/
@@ -698,302 +720,4 @@ theorem INDSecure_iff (atk : Attack) :
 
 end FixedLengthPKScheme
 
-/-! ### From ensemble security to CPA -/
-
-section PaddedCPA
-
-open ChallengeSim ProbComp
-
-/-- The reduction's challenge answer, read from its context `⟨1^n, ⟨⟨pk, c⟩, ω⟩⟩`: the padding
-`padCt L(n) c` of the ciphertext it received. -/
-private def cpaAns (L : PolyExpr) (ctx : List Bool) : List Bool :=
-  padCt (L.eval (pairFstD ctx).length) (pairSndD (pairFstD (pairSndD ctx)))
-
-/-- The challenge answer is polynomial-time (as `padEncFun`). -/
-private theorem polyTimeComputable_cpaAns (L : PolyExpr) : PolyTimeComputable (cpaAns L) := by
-  have hc : PolyTimeComputable fun ctx => pairSndD (pairFstD (pairSndD ctx)) :=
-    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
-  have h := hc.pairEncode ((polyTimeComputable_pairDropPoly .var).comp
-    ((hc.pairEncode (polyTimeComputable_const [])).pairEncode
-      ((polyTimeComputable_unaryPoly L).comp polyTimeComputable_pairFstD)))
-  convert h using 1
-  funext ctx
-  simp [cpaAns, padCt_eq, Function.comp_apply, length_pairEncode]
-
-/-- On the context `⟨1^n, ⟨z, ω⟩⟩` the challenge answer is `padCt L(n) (pairSndD z)`. -/
-private theorem cpaAns_seedIn (L : PolyExpr) (n : ℕ) (z ω : List Bool) :
-    cpaAns L (seedIn n z ω) = padCt (L.eval n) (pairSndD z) := by
-  simp only [cpaAns, seedIn_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
-
-/-- The selected half of a two-bit challenge query, as a list, is its bit `0` or `1`. -/
-private theorem ofFn_splitHalf_bit {k : ℕ} (hk : k = 1) (b : Bool) (mm : Fin (k + k) → Bool) :
-    List.ofFn (if b then (FixedLengthScheme.splitHalf mm).2
-      else (FixedLengthScheme.splitHalf mm).1) =
-      [(List.ofFn mm).getD (if b then 1 else 0) false] := by
-  subst hk
-  cases b <;> simp [FixedLengthScheme.splitHalf_fst, FixedLengthScheme.splitHalf_snd,
-    List.ofFn_succ]
-
-/-- **Eager challenge coins** (checkpoint 1). Under CPA, simulating the oracles of `Ind_b` from
-the state `s` has, for every function `G` of the output, the expectation of first sampling the
-encryption coins `re` and then running the deterministic oracles whose challenge answer is the
-encryption of `m_b` with coins `re` (`chRun`).
-
-**Proof sketch.** Induction on the computation. Decryption queries are answered all-`false`
-in both (`indImpl_dec_cpa`); a repeated challenge repeats the recorded ciphertext in both. At the
-first challenge the lazy side samples `re` and continues from the recorded ciphertext; by the
-induction hypothesis the continuation is again an average over coins `re'`, and from a recorded
-state the deterministic run does not depend on `re'` (`chRun_some_congr`), so `re'`
-marginalizes out (`expect_const`). -/
-private theorem expect_simulate_indImpl_cpa (S : FixedLengthPKScheme) (b : Bool) (n : ℕ)
-    (pk sk : List Bool) {α : Type} (G : α → ℝ) (c : OracleComp (S.indSpec n) α)
-    (s : Option (Fin (S.ctLen.eval n) → Bool)) :
-    expect (simulate (S.indImpl .cpa b n pk sk) c s) (fun p => G p.1) =
-      expect (ProbComp.sample (S.enc.Coins n)) fun re =>
-        G (chRun (fun mm => S.enc.runAt n (pairEncode pk (List.ofFn
-          (if b then (FixedLengthScheme.splitHalf mm).2
-            else (FixedLengthScheme.splitHalf mm).1))) re) c s).1 := by
-  induction c generalizing s with
-  | pure a =>
-    rw [simulate_pure, expect_pure]
-    simp only [chRun_pure]
-    exact (expect_const _ _).symm
-  | query i x k ih =>
-    match i, x, k, ih with
-    | 0, x, k, ih =>
-      rw [simulate_query, S.indImpl_dec_cpa, OracleComp.pure_bind]
-      simp only [chRun_query_zero]
-      exact ih _ s
-    | 1, x, k, ih =>
-      cases s with
-      | some C =>
-        rw [simulate_query, S.indImpl_challenge_repeat, OracleComp.pure_bind]
-        simp only [chRun_query_one_some]
-        exact ih _ _
-      | none =>
-        rw [simulate_query, S.indImpl_challenge_none, OracleComp.bind_assoc, expect_bind]
-        refine congrArg _ (funext fun re => ?_)
-        rw [OracleComp.pure_bind, ih, chRun_query_one_none]
-        exact (congrArg _ (funext fun re' =>
-          congrArg (fun p : α × Option (Fin (S.ctLen.eval n) → Bool) => G p.1)
-            (chRun_some_congr _ _ _ _))).trans (expect_const _ _)
-
-/-- **The exact identity of step 4.** Let `B` be the machine of T1 for the recording handler
-with challenge answer `cpaAns L` (with its coin bijection `φ`). At every `n`, `A`'s CPA advantage
-against the padded scheme equals `B`'s advantage between `⟨pk, Enc_pk(0)⟩` and `⟨pk, Enc_pk(1)⟩`.
-
-**Proof sketch.** Fix `n`. Game `b` samples `rg`, `A`'s coins `r` and (eagerly,
-`expect_simulate_indImpl_cpa`) encryption coins `re`; by first-challenge congruence (`chRun_congr`)
-its output is `A`'s bit `F(w)` when the challenge is answered with `w = padCt L(n) (Enc(m_b; re))`,
-where `(m₀, m₁)` is `A`'s first challenge query (`firstQ`), or `F` of anything without one. On
-`z = ⟨pk, Enc(β; re)⟩`, T1 and `simulate_recHandler_init` show that `B` with coins `φ (ω, r)` runs
-`A` with the same answers `padCt L(n) (Enc(β; re))` and outputs the post-processed bit
-(`recOut_init`, `recOut_recorded`), after transporting the run between the two equal codecs
-(`chRun_toCompOn_transport`). Rearranging the samples (`expect_sample_prod`, `_comm`, `_equiv`
-along `φ` and `padEnc_coins`, `_unique` for the empty seed), both differences of acceptance
-rates become `𝔼_{rg, r}` of a pointwise difference, which agree by `expect_indicator_sub`. -/
-private theorem padded_cpa_advantage_eq {S : BitPublicKeyScheme} (L : PolyExpr)
-    (hL : ∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
-      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
-        ≤ L.eval n)
-    (hmsg : ∀ n, 1 ≤ L.eval n) (A : NUPPT) (q : PolyExpr) (B : NUPPT) (n : ℕ)
-    (φ : (Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).seedLen.eval n) → Bool) ×
-      A.Coins n ≃ B.Coins n)
-    (hφ : ∀ (z : List Bool)
-      (ω : Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).seedLen.eval n) → Bool)
-      (r : A.Coins n),
-      ∃ (a : Fin ((PolyExpr.const 1).eval n) → Bool)
-        (s : Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).stateLen.eval n) → Bool),
-        simulate ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).impl n z ω)
-            (A.toCompOn (bitCodec (fun i => (recDin L i).eval n) (fun i => (recDout L i).eval n)
-              ((PolyExpr.const 1).eval n)) n (q.eval n)
-              ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).advInput n z ω) r)
-            ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).init n) = .pure (a, s) ∧
-          B.runAt n z (φ (ω, r)) =
-            (recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).result n z ω s a) :
-    advantage ((S.padded L hL hmsg).indGame .cpa A (q.eval n) false n)
-        ((S.padded L hL hmsg).indGame .cpa A (q.eval n) true n) =
-      distAdv (S.pkEncDist n false) (S.pkEncDist n true) (B.distinguisherL n) := by
-  -- Notation: the game's computation, the padded ciphertexts, and `A`'s bit.
-  set S' := S.padded L hL hmsg with hS'
-  let comp : S.gen.Coins n → A.Coins n → OracleComp (S'.indSpec n) (Fin 1 → Bool) :=
-    fun rg r => A.toCompOn (S'.indCodec n) n (q.eval n) (pairFstD (S.gen.runAt n [] rg)) r
-  let W : Bool → S.gen.Coins n → S.enc.Coins n → List Bool := fun β rg re =>
-    padCt (L.eval n) (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [β]) re)
-  let F : S.gen.Coins n → A.Coins n → List Bool → Bool := fun rg r w =>
-    (chRun (fun _ => w) (comp rg r) none).1 0
-  -- The two codecs have equal lengths.
-  have hins : (fun i => (recDin L i).eval n) = S'.inLens n := by
-    funext i
-    match i with
-    | 0 => rw [recDin_zero, FixedLengthPKScheme.inLens_zero, BitPublicKeyScheme.padded_ctLen]
-    | 1 =>
-      rw [recDin_one, FixedLengthPKScheme.inLens_one, BitPublicKeyScheme.padded_msgLen,
-        PolyExpr.eval_const, PolyExpr.eval_const]
-  have houts : (fun i => (recDout L i).eval n) = S'.outLens n := by
-    funext i
-    match i with
-    | 0 =>
-      rw [recDout_zero, FixedLengthPKScheme.outLens_zero, BitPublicKeyScheme.padded_msgLen,
-        PolyExpr.eval_const, PolyExpr.eval_const]
-    | 1 => rw [recDout_one, FixedLengthPKScheme.outLens_one, BitPublicKeyScheme.padded_ctLen]
-  -- Step 4, game side: eager coins, first-challenge congruence, and the coin transport.
-  have hG : ∀ b : Bool, accept (S'.indGame .cpa A (q.eval n) b n) =
-      expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
-        expect (ProbComp.sample (A.Coins n)) fun r =>
-          expect (ProbComp.sample (S.enc.Coins n)) fun re =>
-            if F rg r ((firstQ (comp rg r)).elim []
-                fun l => W (l.getD (if b then 1 else 0) false) rg re) = true then 1 else 0 := by
-    intro b
-    rw [accept_eq, FixedLengthPKScheme.indGame_eq, prob_bind]
-    refine congrArg _ (funext fun rg => ?_)
-    rw [prob_bind]
-    refine congrArg _ (funext fun r => ?_)
-    rw [prob_bind]
-    refine (expect_simulate_indImpl_cpa S' b n _ _
-      (fun a => ProbComp.prob (.pure (a 0)) (· = true)) (comp rg r) none).trans ?_
-    rw [← expect_sample_equiv (NUPPT.coinsCongr (padEnc_coins S.enc L) n)]
-    refine congrArg _ (funext fun re' => ?_)
-    rw [prob_pure]
-    congr 2
-    refine congrArg (fun p : (Fin 1 → Bool) × Option (Fin (S'.ctLen.eval n) → Bool) => p.1 0)
-      (chRun_congr _ _ _ fun mm hmm => ?_)
-    rw [hmm, Option.elim_some]
-    exact (runAt_padEnc S.enc_uniform L n _ re').trans (by
-      rw [ofFn_splitHalf_bit (by rw [BitPublicKeyScheme.padded_msgLen, PolyExpr.eval_const])]
-      rfl)
-  -- Step 4, distinguisher side: T1, the handler's simulation, and the codec transport.
-  have hpt : ∀ (β : Bool) (rg : S.gen.Coins n) (r : A.Coins n) (re : S.enc.Coins n)
-      (ω : Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).seedLen.eval n) → Bool),
-      B.distinguisherL n (S.pkEncDist n β (rg, re)) (φ (ω, r)) =
-        (firstQ (comp rg r)).elim false fun l =>
-          (l.getD 0 false != l.getD 1 false) && (F rg r (W β rg re) != l.getD 0 false) := by
-    intro β rg r re ω
-    obtain ⟨a, s, hsim, hrun⟩ := hφ (S.pkEncDist n β (rg, re)) ω r
-    have hadv :
-        (recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).advInput n
-          (S.pkEncDist n β (rg, re)) ω =
-        pairFstD (S.gen.runAt n [] rg) := by
-      rw [PolyHandler.advInput_eq, recHandler_advIn, recAdvIn_eq, seedIn_eq,
-        BitPublicKeyScheme.pkEncDist_eq, pairSndD_pairEncode, pairFstD_pairEncode,
-        pairFstD_pairEncode]
-    have hans : cpaAns L (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn ω)) = W β rg re := by
-      rw [cpaAns_seedIn, BitPublicKeyScheme.pkEncDist_eq, pairSndD_pairEncode]
-    have hw : (cpaAns L (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn ω))).length =
-        L.eval n := by
-      rw [hans]
-      exact length_padCt (hL n rg β re)
-    obtain ⟨s', hsim', hs'⟩ := simulate_recHandler_init L (polyTimeComputable_cpaAns L) n
-      (S.pkEncDist n β (rg, re)) ω hw _
-    rw [hsim, OracleComp.pure.injEq, Prod.mk.injEq] at hsim'
-    obtain ⟨rfl, rfl⟩ := hsim'
-    obtain ⟨h₁, h₂⟩ := chRun_toCompOn_transport hins houts (PolyExpr.eval_const 1 n)
-      A n (q.eval n) ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).advInput n
-        (S.pkEncDist n β (rg, re)) ω) r (W β rg re)
-    rw [hadv] at h₁ h₂ hs'
-    rw [h₂] at hs'
-    rw [NUPPT.distinguisherL_eq, hrun, PolyHandler.result_eq, recHandler_out]
-    have ha : List.ofFn (chRun (fun _ => cpaAns L (seedIn n (S.pkEncDist n β (rg, re))
-        (List.ofFn ω))) (A.toCompOn (bitCodec (fun i => (recDin L i).eval n)
-          (fun i => (recDout L i).eval n) ((PolyExpr.const 1).eval n)) n (q.eval n)
-            ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).advInput n
-              (S.pkEncDist n β (rg, re)) ω) r) none).1 =
-        [F rg r (W β rg re)] := by
-      rw [hans, hadv, h₁, List.ofFn_succ, List.ofFn_zero]
-      rfl
-    rw [ha]
-    cases hq : firstQ (comp rg r) with
-    | none =>
-      have hq' : firstQ (A.toCompOn (bitCodec (S'.inLens n) (S'.outLens n) 1) n (q.eval n)
-          (pairFstD (S.gen.runAt n [] rg)) r) = none := hq
-      rw [hq', Option.elim_none] at hs'
-      rw [hs', recOut_init, Option.elim_none]
-      decide
-    | some l =>
-      have hq' : firstQ (A.toCompOn (bitCodec (S'.inLens n) (S'.outLens n) 1) n (q.eval n)
-          (pairFstD (S.gen.runAt n [] rg)) r) = some l := hq
-      have hl : l.length = 2 := by
-        rw [length_of_firstQ_eq_some _ hq', FixedLengthPKScheme.inLens_one,
-          BitPublicKeyScheme.padded_msgLen, PolyExpr.eval_const]
-      obtain ⟨m₀, m₁, rfl⟩ := List.length_eq_two.1 hl
-      rw [hq', Option.elim_some] at hs'
-      rw [hs', recOut_recorded, Option.elim_some]
-      simp only [List.headD_cons, List.getD_cons_zero, List.getD_cons_succ, List.cons.injEq,
-        and_true, Bool.decide_eq_true]
-  have hD : ∀ β : Bool, acceptProb (S.pkEncDist n β) (B.distinguisherL n) =
-      expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
-        expect (ProbComp.sample (A.Coins n)) fun r =>
-          expect (ProbComp.sample (S.enc.Coins n)) fun re =>
-            if ((firstQ (comp rg r)).elim false fun l =>
-              (l.getD 0 false != l.getD 1 false) && (F rg r (W β rg re) != l.getD 0 false)) = true
-            then 1 else 0 := by
-    intro β
-    rw [Bridge.acceptProb_eq, accept_eq, Bridge.acceptGame_eq, prob_bind, expect_sample_prod]
-    refine congrArg _ (funext fun rg => ?_)
-    simp only [prob_bind, prob_pure]
-    haveI : Unique (Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).seedLen.eval n) →
-        Bool) := by
-      rw [recHandler_seedLen, PolyExpr.eval_const]
-      infer_instance
-    rw [expect_sample_comm, ← expect_sample_equiv φ, expect_sample_prod, expect_sample_unique]
-    refine congrArg _ (funext fun r => congrArg _ (funext fun re => ?_))
-    rw [hpt β rg r re]
-  -- Assemble: both differences are `𝔼_{rg, r}` of equal pointwise differences.
-  rw [advantage_eq, distAdv_def, hG false, hG true, hD false, hD true]
-  congr 1
-  rw [← expect_sub]
-  conv_rhs => rw [← expect_sub]
-  refine congrArg _ (funext fun rg => ?_)
-  rw [← expect_sub]
-  conv_rhs => rw [← expect_sub]
-  refine congrArg _ (funext fun r => ?_)
-  cases hq : firstQ (comp rg r) with
-  | none =>
-    simp only [Option.elim_none, Bool.false_eq_true, if_false, sub_self]
-  | some l =>
-    have hl : l.length = 2 := by
-      rw [length_of_firstQ_eq_some _ hq, FixedLengthPKScheme.inLens_one,
-        BitPublicKeyScheme.padded_msgLen, PolyExpr.eval_const]
-    obtain ⟨m₀, m₁, rfl⟩ := List.length_eq_two.1 hl
-    simp only [Option.elim_some, List.getD_cons_zero, List.getD_cons_succ, Bool.false_eq_true,
-      if_false, if_true]
-    exact expect_indicator_sub (fun β re => F rg r (W β rg re)) m₀ m₁
-
-/-- **Single-bit security gives CPA security** for a padded single-bit scheme.
-
-**Proof sketch.**
-1. With CPA there is no `Dec` oracle, so the adversary's view is `pk`, its coins and the padded
-   challenge `padCt L (Enc_pk(m_b))`, where its messages `m₀, m₁ ∈ {0,1}` are chosen after
-   seeing `pk`. Only the first challenge query uses coins, so the encryption coins may be sampled
-   in advance (`expect_simulate_indImpl_cpa`); then `A`'s bit depends on the challenge answer only
-   through its value at `A`'s first challenge query `(m₀, m₁)`, which itself does not depend on
-   that answer (`ChallengeSim.chRun_congr`).
-2. If `m₀ = m₁` both games are identical. Otherwise `m_b` is `b` or `¬b`. The distinguisher `D`
-   on `⟨pk, c⟩` runs `A` on `pk`, answers every challenge with `padCt L c` and every `Dec` query
-   with `⊥`, records `A`'s first challenge `(m₀, m₁)`, and outputs `A`'s bit, flipped when
-   `(m₀, m₁) = (1, 0)` and replaced by `0` when `m₀ = m₁` or no challenge was asked. T1
-   (`Games.exists_handlerMachine`, for the handler `ChallengeSim.recHandler`) makes `D` a
-   machine, whose output is exactly this bit (`ChallengeSim.simulate_recHandler_init`).
-3. Fixing `pk` and `A`'s coins, the case split on `(m₀, m₁)` gives the same difference of
-   acceptance rates on both sides (`ChallengeSim.expect_indicator_sub`); so `A`'s CPA advantage
-   equals `D`'s advantage between `⟨pk, Enc_pk(0)⟩` and `⟨pk, Enc_pk(1)⟩` at every `n`
-   (`padded_cpa_advantage_eq`), which is negligible (`BitPublicKeyScheme.singleBitSecure_iff`). -/
-theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.padded_cpa
-    {S : BitPublicKeyScheme} (h : S.SingleBitSecure) (L : PolyExpr)
-    (hL : ∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
-      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
-        ≤ L.eval n)
-    (hmsg : ∀ n, 1 ≤ L.eval n) : (S.padded L hL hmsg).INDSecure .cpa := by
-  rw [FixedLengthPKScheme.INDSecure_iff]
-  intro A q
-  -- Step 3: the distinguisher `D` is T1's machine for the recording handler.
-  obtain ⟨B, hB⟩ := exists_handlerMachine A q (recDin L) (recDout L) (.const 1)
-    (recHandler L (cpaAns L) (polyTimeComputable_cpaAns L))
-  refine ⟨_, (BitPublicKeyScheme.singleBitSecure_iff S).1 h B, fun n => le_of_eq ?_⟩
-  -- Step 4: the advantages are equal.
-  obtain ⟨φ, hφ⟩ := hB n
-  exact padded_cpa_advantage_eq L hL hmsg A q B n φ hφ
-
-end PaddedCPA
-
 end TCSlib.Cryptography.Composability
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/ChallengeSim.lean b/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/ChallengeSim.lean
index 77b7bd503..cefc63457 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/ChallengeSim.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/ChallengeSim.lean
@@ -42,9 +42,11 @@ reduction: reindexing by an equivalence, products, exchange of order, and single
 * `ChallengeSim.chRun_some_congr`: once the challenge is recorded, `g` no longer matters.
 * `ChallengeSim.chRun_congr`: the run depends on `g` only at the first challenge query.
 * `ChallengeSim.length_of_firstQ_eq_some`: the first challenge query has `ins 1` bits.
-* `ChallengeSim.chRun_toCompOn_transport`: transport along equal length functions.
-* `ChallengeSim.expect_sample_equiv`, `expect_sample_prod`, `expect_sample_comm`,
-  `expect_sample_unique`, `expect_sub`: sampling identities.
+* `ChallengeSim.chRun_toCompOn_transport_list`, `ChallengeSim.chRun_toCompOn_transport`: transport
+  along equal length functions, with a query-dependent and with a constant answer.
+* `ChallengeSim.expect_simulate_eager`: eager challenge coins, for any CPA-shaped oracle.
+* `ChallengeSim.expect_sample_prod`: sampling a product is sampling its factors (the other
+  sampling identities are `Games.ProbComp`'s).
 * `ChallengeSim.expect_indicator_sub`: the case split on the first challenge `(m₀, m₁)`.
 
 ## References
@@ -130,6 +132,62 @@ theorem chRun_some_congr (g g' : (Fin (ins 1) → Bool) → List Bool)
     | 0, x, k, ih => rw [chRun_query_zero, chRun_query_zero, ih]
     | 1, x, k, ih => rw [chRun_query_one_some, chRun_query_one_some, ih]
 
+/-- **Eager challenge coins, for any CPA-shaped oracle.** Let `impl` answer oracle `0`
+all-`false`, a challenge from a recorded state `c` with `c`, and the first challenge `mm` by
+sampling `re` and answering (and recording) `padFin d (g mm re)`; the state holds `d`-bit
+strings, `d = outs 1`, read through the cast `e`. Then for every `G`,
+`𝔼[G ∘ fst] (simulate impl c s) = 𝔼_{re} G (chRun (fun mm => g mm re) c (s.map (cast e))).1`.
+
+**Proof sketch.** Substitute `d = outs 1`, so that the casts are identities. Induction on the
+computation: decryption queries and repeated challenges are deterministic in both; at the first
+challenge the lazy side samples `re` and continues from the recorded answer, by the induction
+hypothesis an average over coins `re'` on which the recorded run does not depend
+(`chRun_some_congr`), so `re'` marginalizes out (`expect_const`). -/
+theorem expect_simulate_eager {ins outs : Fin 2 → ℕ} {d : ℕ} (hd : outs 1 = d)
+    (e : (Fin d → Bool) = (Fin (outs 1) → Bool)) {R : Type} [Fintype R] [Nonempty R]
+    (impl : QueryImpl (bitSpec ins outs) (Option (Fin d → Bool)) unifSpec)
+    (g : (Fin (ins 1) → Bool) → R → List Bool)
+    (h0 : ∀ x s, impl 0 x s = .pure (zeroBits _, s))
+    (hrep : ∀ mm c, impl 1 mm (some c) = .pure (cast e c, some c))
+    (hnew : ∀ mm, impl 1 mm none = (ProbComp.sample R).bind fun re =>
+      .pure (cast e (padFin d (g mm re)), some (padFin d (g mm re))))
+    {α : Type} (G : α → ℝ) (c : OracleComp (bitSpec ins outs) α) (s : Option (Fin d → Bool)) :
+    expect (simulate impl c s) (fun p => G p.1) =
+      expect (ProbComp.sample R) fun re =>
+        G (chRun (fun mm => g mm re) c (s.map (cast e))).1 := by
+  subst hd
+  have hc : ∀ x : Fin (outs 1) → Bool, cast e x = x := fun x => cast_eq e x
+  have hmap : ∀ s : Option (Fin (outs 1) → Bool), s.map (cast e) = s := fun s => by
+    cases s <;> simp
+  simp only [hc] at hrep hnew
+  simp only [hmap]
+  induction c generalizing s with
+  | pure a =>
+    rw [simulate_pure, expect_pure]
+    simp only [chRun_pure]
+    exact (expect_const _ _).symm
+  | query i x k ih =>
+    match i, x, k, ih with
+    | 0, x, k, ih =>
+      rw [simulate_query, h0, OracleComp.pure_bind]
+      simp only [chRun_query_zero]
+      exact ih _ s
+    | 1, x, k, ih =>
+      cases s with
+      | some C =>
+        rw [simulate_query, hrep, OracleComp.pure_bind]
+        simp only [chRun_query_one_some]
+        exact ih _ _
+      | none =>
+        rw [simulate_query, hnew, OracleComp.bind_assoc, expect_bind]
+        refine congrArg _ (funext fun re => ?_)
+        rw [OracleComp.pure_bind, ih, chRun_query_one_none]
+        dsimp only
+        exact (congrArg _ (funext fun re' =>
+          congrArg (fun p : α × Option (Fin (outs 1) → Bool) => G p.1)
+            (chRun_some_congr (fun mm => g mm re') (fun mm => g mm re) _ _))).trans
+          (expect_const _ _)
+
 /-- **First-challenge congruence:** if `g` and `g'` agree at the first challenge query of `c`
 (vacuous when there is none), the runs from the unchallenged state agree:
 `chRun g c none = chRun g' c none`.
@@ -171,13 +229,33 @@ theorem length_of_firstQ_eq_some (c : OracleComp (bitSpec ins outs) α) {l : Lis
       rw [firstQ_query_one, Option.some.injEq] at h
       rw [← h, List.length_ofFn]
 
+/-- **Transport of a run with a query-dependent answer along equal lengths:** for a machine
+adversary run through `bitCodec`, if `ins = ins'`, `outs = outs'` and `d = d'`, then for every
+`G : List Bool → List Bool`,
+`List.ofFn (chRun (fun y => G ⟦y⟧) (A.toCompOn (bitCodec ins outs d) n q x r) none).1 =
+List.ofFn (chRun (fun y => G ⟦y⟧) (A.toCompOn (bitCodec ins' outs' d') n q x r) none).1`, and
+the two runs have the same `firstQ`.
+
+**Proof sketch.** Substitute the equalities; both sides become identical. -/
+theorem chRun_toCompOn_transport_list {ins' outs' : Fin 2 → ℕ} {d d' : ℕ}
+    (hi : ins = ins') (ho : outs = outs') (hd : d = d') (A : NUPPT) (n q : ℕ) (x : List Bool)
+    (r : A.Coins n) (G : List Bool → List Bool) :
+    List.ofFn (chRun (ins := ins) (outs := outs) (fun y => G (List.ofFn y))
+        (A.toCompOn (bitCodec ins outs d) n q x r) none).1 =
+      List.ofFn (chRun (ins := ins') (outs := outs') (fun y => G (List.ofFn y))
+        (A.toCompOn (bitCodec ins' outs' d') n q x r) none).1 ∧
+    firstQ (A.toCompOn (bitCodec ins outs d) n q x r) =
+      firstQ (A.toCompOn (bitCodec ins' outs' d') n q x r) := by
+  subst hi ho hd
+  exact ⟨rfl, rfl⟩
+
 /-- **Transport along equal lengths:** for a machine adversary run through `bitCodec`, if
 `ins = ins'`, `outs = outs'` and `d = d'`, then
 `List.ofFn (chRun (fun _ => w) (A.toCompOn (bitCodec ins outs d) n q x r) none).1 =
 List.ofFn (chRun (fun _ => w) (A.toCompOn (bitCodec ins' outs' d') n q x r) none).1` and the
 two runs have the same `firstQ`.
 
-**Proof sketch.** Substitute the equalities; both sides become identical. -/
+**Proof sketch.** `chRun_toCompOn_transport_list` with the constant answer `G = fun _ => w`. -/
 theorem chRun_toCompOn_transport {ins' outs' : Fin 2 → ℕ} {d d' : ℕ} (hi : ins = ins')
     (ho : outs = outs') (hd : d = d') (A : NUPPT) (n q : ℕ) (x : List Bool) (r : A.Coins n)
     (w : List Bool) :
@@ -186,9 +264,8 @@ theorem chRun_toCompOn_transport {ins' outs' : Fin 2 → ℕ} {d d' : ℕ} (hi :
       List.ofFn (chRun (ins := ins') (outs := outs') (fun _ => w)
         (A.toCompOn (bitCodec ins' outs' d') n q x r) none).1 ∧
     firstQ (A.toCompOn (bitCodec ins outs d) n q x r) =
-      firstQ (A.toCompOn (bitCodec ins' outs' d') n q x r) := by
-  subst hi ho hd
-  exact ⟨rfl, rfl⟩
+      firstQ (A.toCompOn (bitCodec ins' outs' d') n q x r) :=
+  chRun_toCompOn_transport_list hi ho hd A n q x r fun _ => w
 
 /-! ### Sampling identities -/
 
@@ -196,14 +273,6 @@ section Sampling
 
 variable {β : Type}
 
-/-- **Reindexing a sample by an equivalence:** `𝔼_{a ← α} g (e a) = 𝔼_{b ← β} g b`.
-
-**Proof sketch.** Both are uniform averages (`expect_sample`); the cardinalities agree
-(`Fintype.card_congr`) and the sums agree by reindexing along `e` (`Equiv.sum_comp`). -/
-theorem expect_sample_equiv [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (e : α ≃ β)
-    (g : β → ℝ) : expect (sample α) (fun a => g (e a)) = expect (sample β) g := by
-  rw [expect_sample, expect_sample, Fintype.card_congr e, Equiv.sum_comp e g]
-
 /-- **Sampling a product is sampling its factors:**
 `𝔼_{(a, b) ← α × β} g (a, b) = 𝔼_{a ← α} 𝔼_{b ← β} g (a, b)`. -/
 theorem expect_sample_prod [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
@@ -212,34 +281,6 @@ theorem expect_sample_prod [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
   rw [← Bridge.expect_sample_pair]
   simp only [expect_bind, expect_pure]
 
-/-- **Independent samples commute:**
-`𝔼_{a ← α} 𝔼_{b ← β} g a b = 𝔼_{b ← β} 𝔼_{a ← α} g a b`.
-
-**Proof sketch.** Both are the average over the product (`expect_sample_prod`), reindexed by
-the swap equivalence (`expect_sample_equiv`). -/
-theorem expect_sample_comm [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
-    (g : α → β → ℝ) :
-    (expect (sample α) fun a => expect (sample β) fun b => g a b) =
-      expect (sample β) fun b => expect (sample α) fun a => g a b := by
-  rw [← expect_sample_prod (fun p : α × β => g p.1 p.2),
-    ← expect_sample_prod (fun p : β × α => g p.2 p.1),
-    ← expect_sample_equiv (Equiv.prodComm β α) (fun p : α × β => g p.1 p.2)]
-  rfl
-
-/-- **Sampling a singleton type** returns its element: `𝔼_{a ← α} g a = g default`. -/
-theorem expect_sample_unique [Fintype α] [Unique α] (g : α → ℝ) :
-    expect (sample α) g = g default := by
-  rw [expect_sample, Fintype.card_unique, Fintype.sum_unique]
-  simp
-
-/-- Expectation is subtractive: `𝔼[f − g] = 𝔼 f − 𝔼 g`. -/
-theorem expect_sub (c : ProbComp α) (f g : α → ℝ) :
-    expect c (fun a => f a - g a) = expect c f - expect c g := by
-  have h := expect_add c f (fun a => -1 * g a)
-  rw [expect_const_mul] at h
-  simp only [neg_one_mul, ← sub_eq_add_neg] at h
-  exact h
-
 /-- **The pointwise case split of the CPA reduction:** for the first challenge `(m₀, m₁)`, the
 difference of the acceptance rates of `A` against `Enc(m₀)` and `Enc(m₁)` equals the difference of
 the acceptance rates of the post-processed bit `(m₀ ≠ m₁) ∧ (a ≠ m₀)` against `Enc(0)` and `Enc(1)`.
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/PaddedCPA.lean b/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/PaddedCPA.lean
new file mode 100644
index 000000000..192064c3f
--- /dev/null
+++ b/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/PaddedCPA.lean
@@ -0,0 +1,332 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
+import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.ChallengeSim
+import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.RecordHandler
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Single-bit security gives CPA security of the padded scheme
+
+The claim after [PS10, Definition 171.5]: a single-bit secure public-key scheme, padded to fixed
+length (`BitPublicKeyScheme.padded`, `Encryption.PublicKey.OracleSecurity`), is CPA-secure in the
+oracle game `FixedLengthPKScheme.indGame`.
+
+Under CPA the adversary's view is `pk`, its coins and the padded challenge. Only the first
+challenge query uses coins, so the encryption coins may be sampled in advance
+(`expect_simulate_indImpl_cpa`). The distinguisher answers every challenge with its own padded
+ciphertext and outputs the adversary's bit, corrected by the first challenge pair; it is T1's
+machine for the recording handler (`OracleSecurity.RecordHandler`). The two advantages are equal
+at every `n` (`padded_cpa_advantage_eq`). The deterministic run and first-challenge congruence
+are `OracleSecurity.ChallengeSim`'s.
+
+## Main results
+
+* `expect_simulate_indImpl_cpa`: eager challenge coins under CPA.
+* `BitPublicKeyScheme.SingleBitSecure.padded_cpa`: single-bit security gives CPA security of
+  the padded scheme.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §7.1.4, Definition 171.5 and the claim after it (book pp. 171–172).
+-/
+
+namespace TCSlib.Cryptography.Composability
+
+open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
+
+/-! ### From ensemble security to CPA -/
+
+section PaddedCPA
+
+open ChallengeSim ProbComp
+
+/-- The reduction's challenge answer, read from its context `⟨1^n, ⟨⟨pk, c⟩, ω⟩⟩`: the padding
+`padCt L(n) c` of the ciphertext it received. -/
+private def cpaAns (L : PolyExpr) (ctx : List Bool) : List Bool :=
+  padCt (L.eval (pairFstD ctx).length) (pairSndD (pairFstD (pairSndD ctx)))
+
+/-- The challenge answer is polynomial-time (as `padEncFun`). -/
+private theorem polyTimeComputable_cpaAns (L : PolyExpr) : PolyTimeComputable (cpaAns L) := by
+  have hc : PolyTimeComputable fun ctx => pairSndD (pairFstD (pairSndD ctx)) :=
+    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
+  have h := hc.pairEncode ((polyTimeComputable_pairDropPoly .var).comp
+    ((hc.pairEncode (polyTimeComputable_const [])).pairEncode
+      ((polyTimeComputable_unaryPoly L).comp polyTimeComputable_pairFstD)))
+  convert h using 1
+  funext ctx
+  simp [cpaAns, padCt_eq, Function.comp_apply, length_pairEncode]
+
+/-- On the context `⟨1^n, ⟨z, ω⟩⟩` the challenge answer is `padCt L(n) (pairSndD z)`. -/
+private theorem cpaAns_seedIn (L : PolyExpr) (n : ℕ) (z ω : List Bool) :
+    cpaAns L (seedIn n z ω) = padCt (L.eval n) (pairSndD z) := by
+  simp only [cpaAns, seedIn_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
+
+/-- The selected half of a two-bit challenge query, as a list, is its bit `0` or `1`. -/
+private theorem ofFn_splitHalf_bit {k : ℕ} (hk : k = 1) (b : Bool) (mm : Fin (k + k) → Bool) :
+    List.ofFn (if b then (FixedLengthScheme.splitHalf mm).2
+      else (FixedLengthScheme.splitHalf mm).1) =
+      [(List.ofFn mm).getD (if b then 1 else 0) false] := by
+  subst hk
+  cases b <;> simp [FixedLengthScheme.splitHalf_fst, FixedLengthScheme.splitHalf_snd,
+    List.ofFn_succ]
+
+/-- **Eager challenge coins under CPA.** Simulating the oracles of `Ind_b` from the state `s` has,
+for every `G`, the expectation of first sampling the encryption coins `re` and then running the
+deterministic oracles whose challenge `mm` is answered with `Enc(⟨pk, m_b⟩; re)`, the halves and the
+recorded ciphertext read through `indSpec_challengeDom` and `indSpec_challengeRng`:
+`𝔼[G ∘ fst] (simulate (indImpl .cpa b n pk sk) c s) = 𝔼_{re} G (chRun g_re c s).1`.
+
+**Proof sketch.** `ChallengeSim.expect_simulate_eager` with `d = ctLen(n)` (`outLens_one`), the
+cast `indSpec_challengeRng`, and the oracle equations `indImpl_dec_onSpec` (with `decOpen_cpa`),
+`indImpl_challenge_repeat_onSpec` and `indImpl_challenge_none_onSpec`: decryption queries are
+answered all-`false`, a repeated challenge repeats the record, and the first challenge samples the
+coins and records the encryption. -/
+theorem expect_simulate_indImpl_cpa (S : FixedLengthPKScheme) (b : Bool) (n : ℕ)
+    (pk sk : List Bool) {α : Type} (G : α → ℝ) (c : OracleComp (S.indSpec n) α)
+    (s : Option (Fin (S.ctLen.eval n) → Bool)) :
+    expect (simulate (S.indImpl .cpa b n pk sk) c s) (fun p => G p.1) =
+      expect (ProbComp.sample (S.enc.Coins n)) fun re =>
+        G (chRun (fun mm => S.enc.runAt n (pairEncode pk (List.ofFn
+          (if b then (FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n) mm)).2
+            else (FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n) mm)).1))) re)
+          c (s.map (cast (S.indSpec_challengeRng n).symm))).1 :=
+  expect_simulate_eager (S.outLens_one n) (S.indSpec_challengeRng n).symm _ _
+    (fun x s => by
+      rw [S.indImpl_dec_onSpec]
+      simp only [FixedLengthScheme.decOpen_cpa, Bool.false_and, Bool.false_eq_true, if_false])
+    (fun mm C => S.indImpl_challenge_repeat_onSpec .cpa b n pk sk mm C)
+    (fun mm => S.indImpl_challenge_none_onSpec .cpa b n pk sk mm) G c s
+
+/-- **The exact identity of step 4.** Let `B` be the machine of T1 for the recording handler
+with challenge answer `cpaAns L` (with its coin bijection `φ`). At every `n`, `A`'s CPA advantage
+against the padded scheme equals `B`'s advantage between `⟨pk, Enc_pk(0)⟩` and `⟨pk, Enc_pk(1)⟩`.
+
+**Proof sketch.** Fix `n`. Game `b` samples `rg`, `A`'s coins `r` and (eagerly,
+`expect_simulate_indImpl_cpa`) encryption coins `re`; by first-challenge congruence (`chRun_congr`)
+its output is `A`'s bit `F(w)` when the challenge is answered with `w = padCt L(n) (Enc(m_b; re))`,
+where `(m₀, m₁)` is `A`'s first challenge query (`firstQ`), or `F` of anything without one. On
+`z = ⟨pk, Enc(β; re)⟩`, T1 and `simulate_recHandler_init` show that `B` with coins `φ (ω, r)` runs
+`A` with the same answers `padCt L(n) (Enc(β; re))` and outputs the post-processed bit
+(`recOut_init`, `recOut_recorded`), after transporting the run between the two equal codecs
+(`chRun_toCompOn_transport`). Rearranging the samples (`expect_sample_prod`, `_comm`, `_equiv`
+along `φ` and `padEnc_coins`, `_unique` for the empty seed), both differences of acceptance
+rates become `𝔼_{rg, r}` of a pointwise difference, which agree by `expect_indicator_sub`. -/
+private theorem padded_cpa_advantage_eq {S : BitPublicKeyScheme} (L : PolyExpr)
+    (hL : ∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
+      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
+        ≤ L.eval n)
+    (hmsg : ∀ n, 1 ≤ L.eval n) (A : NUPPT) (q : PolyExpr) (B : NUPPT) (n : ℕ)
+    (φ : (Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).seedLen.eval n) → Bool) ×
+      A.Coins n ≃ B.Coins n)
+    (hφ : ∀ (z : List Bool)
+      (ω : Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).seedLen.eval n) → Bool)
+      (r : A.Coins n),
+      ∃ (a : Fin ((PolyExpr.const 1).eval n) → Bool)
+        (s : Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).stateLen.eval n) → Bool),
+        simulate ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).impl n z ω)
+            (A.toCompOn (bitCodec (fun i => (recDin L i).eval n) (fun i => (recDout L i).eval n)
+              ((PolyExpr.const 1).eval n)) n (q.eval n)
+              ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).advInput n z ω) r)
+            ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).init n) = .pure (a, s) ∧
+          B.runAt n z (φ (ω, r)) =
+            (recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).result n z ω s a) :
+    advantage ((S.padded L hL hmsg).indGame .cpa A (q.eval n) false n)
+        ((S.padded L hL hmsg).indGame .cpa A (q.eval n) true n) =
+      distAdv (S.pkEncDist n false) (S.pkEncDist n true) (B.distinguisherL n) := by
+  -- Notation: the game's computation, the padded ciphertexts, and `A`'s bit.
+  set S' := S.padded L hL hmsg with hS'
+  let comp : S.gen.Coins n → A.Coins n → OracleComp (S'.indSpec n) (Fin 1 → Bool) :=
+    fun rg r => A.toCompOn (S'.indCodec n) n (q.eval n) (pairFstD (S.gen.runAt n [] rg)) r
+  let W : Bool → S.gen.Coins n → S.enc.Coins n → List Bool := fun β rg re =>
+    padCt (L.eval n) (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [β]) re)
+  let F : S.gen.Coins n → A.Coins n → List Bool → Bool := fun rg r w =>
+    (chRun (fun _ => w) (comp rg r) none).1 0
+  -- `A`'s computation, read on the bit codec (`indCodec_eq_bitCodec`).
+  have hcomp : ∀ rg r, comp rg r =
+      A.toCompOn (bitCodec (S'.inLens n) (S'.outLens n) 1) n (q.eval n)
+        (pairFstD (S.gen.runAt n [] rg)) r := fun rg r => by
+    show A.toCompOn (S'.indCodec n) n (q.eval n) (pairFstD (S.gen.runAt n [] rg)) r = _
+    rw [FixedLengthPKScheme.indCodec_eq_bitCodec]
+  -- The two codecs have equal lengths.
+  have hins : (fun i => (recDin L i).eval n) = S'.inLens n := by
+    funext i
+    match i with
+    | 0 => rw [recDin_zero, FixedLengthPKScheme.inLens_zero, BitPublicKeyScheme.padded_ctLen]
+    | 1 =>
+      rw [recDin_one, FixedLengthPKScheme.inLens_one, BitPublicKeyScheme.padded_msgLen,
+        PolyExpr.eval_const, PolyExpr.eval_const]
+  have houts : (fun i => (recDout L i).eval n) = S'.outLens n := by
+    funext i
+    match i with
+    | 0 =>
+      rw [recDout_zero, FixedLengthPKScheme.outLens_zero, BitPublicKeyScheme.padded_msgLen,
+        PolyExpr.eval_const, PolyExpr.eval_const]
+    | 1 => rw [recDout_one, FixedLengthPKScheme.outLens_one, BitPublicKeyScheme.padded_ctLen]
+  -- Step 4, game side: eager coins, first-challenge congruence, and the coin transport.
+  have hG : ∀ b : Bool, accept (S'.indGame .cpa A (q.eval n) b n) =
+      expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
+        expect (ProbComp.sample (A.Coins n)) fun r =>
+          expect (ProbComp.sample (S.enc.Coins n)) fun re =>
+            if F rg r ((firstQ (comp rg r)).elim []
+                fun l => W (l.getD (if b then 1 else 0) false) rg re) = true then 1 else 0 := by
+    intro b
+    rw [accept_eq, FixedLengthPKScheme.indGame_eq, prob_bind,
+      show S'.gen = S.gen from BitPublicKeyScheme.padded_gen S L hL hmsg]
+    refine congrArg _ (funext fun rg => ?_)
+    rw [prob_bind]
+    refine congrArg _ (funext fun r => ?_)
+    rw [prob_bind]
+    refine (expect_simulate_indImpl_cpa S' b n _ _
+      (fun a => ProbComp.prob (.pure (a 0)) (· = true)) (comp rg r) none).trans ?_
+    rw [← expect_sample_equiv (NUPPT.coinsCongr (padEnc_coins S.enc L) n),
+      show S'.enc = padEnc S.enc L from BitPublicKeyScheme.padded_enc S L hL hmsg]
+    refine congrArg _ (funext fun re' => ?_)
+    rw [prob_pure]
+    congr 2
+    refine congrArg (fun p : (Fin 1 → Bool) × Option (Fin (S'.outLens n 1) → Bool) => p.1 0)
+      (chRun_congr _ _ _ fun mm hmm => ?_)
+    rw [hmm, Option.elim_some]
+    exact (runAt_padEnc S.enc_uniform L n _ re').trans (by
+      rw [ofFn_splitHalf_bit (by rw [BitPublicKeyScheme.padded_msgLen, PolyExpr.eval_const]),
+        ofFn_cast (S'.inLens_one n)])
+  -- Step 4, distinguisher side: T1, the handler's simulation, and the codec transport.
+  have hpt : ∀ (β : Bool) (rg : S.gen.Coins n) (r : A.Coins n) (re : S.enc.Coins n)
+      (ω : Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).seedLen.eval n) → Bool),
+      B.distinguisherL n (S.pkEncDist n β (rg, re)) (φ (ω, r)) =
+        (firstQ (comp rg r)).elim false fun l =>
+          (l.getD 0 false != l.getD 1 false) && (F rg r (W β rg re) != l.getD 0 false) := by
+    intro β rg r re ω
+    obtain ⟨a, s, hsim, hrun⟩ := hφ (S.pkEncDist n β (rg, re)) ω r
+    have hadv :
+        (recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).advInput n
+          (S.pkEncDist n β (rg, re)) ω =
+        pairFstD (S.gen.runAt n [] rg) := by
+      rw [PolyHandler.advInput_eq, recHandler_advIn, recAdvIn_eq, seedIn_eq,
+        BitPublicKeyScheme.pkEncDist_eq, pairSndD_pairEncode, pairFstD_pairEncode,
+        pairFstD_pairEncode]
+    have hans : cpaAns L (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn ω)) = W β rg re := by
+      rw [cpaAns_seedIn, BitPublicKeyScheme.pkEncDist_eq, pairSndD_pairEncode]
+    have hw : (cpaAns L (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn ω))).length =
+        L.eval n := by
+      rw [hans]
+      exact length_padCt (hL n rg β re)
+    obtain ⟨s', hsim', hs'⟩ := simulate_recHandler_init L (polyTimeComputable_cpaAns L) n
+      (S.pkEncDist n β (rg, re)) ω hw _
+    rw [hsim, OracleComp.pure.injEq, Prod.mk.injEq] at hsim'
+    obtain ⟨rfl, rfl⟩ := hsim'
+    obtain ⟨h₁, h₂⟩ := chRun_toCompOn_transport hins houts (PolyExpr.eval_const 1 n)
+      A n (q.eval n) ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).advInput n
+        (S.pkEncDist n β (rg, re)) ω) r (W β rg re)
+    rw [hadv] at h₁ h₂ hs'
+    rw [h₂] at hs'
+    rw [NUPPT.distinguisherL_eq, hrun, PolyHandler.result_eq, recHandler_out]
+    have ha : List.ofFn (chRun (fun _ => cpaAns L (seedIn n (S.pkEncDist n β (rg, re))
+        (List.ofFn ω))) (A.toCompOn (bitCodec (fun i => (recDin L i).eval n)
+          (fun i => (recDout L i).eval n) ((PolyExpr.const 1).eval n)) n (q.eval n)
+            ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).advInput n
+              (S.pkEncDist n β (rg, re)) ω) r) none).1 =
+        [F rg r (W β rg re)] := by
+      rw [hans, hadv, h₁, List.ofFn_succ, List.ofFn_zero, ← hcomp]
+    rw [ha]
+    cases hq : firstQ (comp rg r) with
+    | none =>
+      have hq' : firstQ (A.toCompOn (bitCodec (S'.inLens n) (S'.outLens n) 1) n (q.eval n)
+          (pairFstD (S.gen.runAt n [] rg)) r) = none := by rw [← hcomp]; exact hq
+      rw [hq', Option.elim_none] at hs'
+      rw [hs', recOut_init, Option.elim_none]
+      decide
+    | some l =>
+      have hq' : firstQ (A.toCompOn (bitCodec (S'.inLens n) (S'.outLens n) 1) n (q.eval n)
+          (pairFstD (S.gen.runAt n [] rg)) r) = some l := by rw [← hcomp]; exact hq
+      have hl : l.length = 2 := by
+        rw [length_of_firstQ_eq_some _ hq', FixedLengthPKScheme.inLens_one,
+          BitPublicKeyScheme.padded_msgLen, PolyExpr.eval_const]
+      obtain ⟨m₀, m₁, rfl⟩ := List.length_eq_two.1 hl
+      rw [hq', Option.elim_some] at hs'
+      rw [hs', recOut_recorded, Option.elim_some]
+      simp only [List.headD_cons, List.getD_cons_zero, List.getD_cons_succ, List.cons.injEq,
+        and_true, Bool.decide_eq_true]
+  have hD : ∀ β : Bool, acceptProb (S.pkEncDist n β) (B.distinguisherL n) =
+      expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
+        expect (ProbComp.sample (A.Coins n)) fun r =>
+          expect (ProbComp.sample (S.enc.Coins n)) fun re =>
+            if ((firstQ (comp rg r)).elim false fun l =>
+              (l.getD 0 false != l.getD 1 false) && (F rg r (W β rg re) != l.getD 0 false)) = true
+            then 1 else 0 := by
+    intro β
+    rw [Bridge.acceptProb_eq, accept_eq, Bridge.acceptGame_eq, prob_bind, expect_sample_prod]
+    refine congrArg _ (funext fun rg => ?_)
+    simp only [prob_bind, prob_pure]
+    haveI : Unique (Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).seedLen.eval n) →
+        Bool) := by
+      rw [recHandler_seedLen, PolyExpr.eval_const]
+      infer_instance
+    rw [expect_sample_comm, ← expect_sample_equiv φ, expect_sample_prod, expect_sample_unique]
+    refine congrArg _ (funext fun r => congrArg _ (funext fun re => ?_))
+    rw [hpt β rg r re]
+  -- Assemble: both differences are `𝔼_{rg, r}` of equal pointwise differences.
+  rw [advantage_eq, distAdv_def, hG false, hG true, hD false, hD true]
+  congr 1
+  rw [← expect_sub]
+  conv_rhs => rw [← expect_sub]
+  refine congrArg _ (funext fun rg => ?_)
+  rw [← expect_sub]
+  conv_rhs => rw [← expect_sub]
+  refine congrArg _ (funext fun r => ?_)
+  cases hq : firstQ (comp rg r) with
+  | none =>
+    simp only [Option.elim_none, Bool.false_eq_true, if_false, sub_self]
+  | some l =>
+    have hl : l.length = 2 := by
+      rw [length_of_firstQ_eq_some _ hq, FixedLengthPKScheme.inLens_one,
+        BitPublicKeyScheme.padded_msgLen, PolyExpr.eval_const]
+    obtain ⟨m₀, m₁, rfl⟩ := List.length_eq_two.1 hl
+    simp only [Option.elim_some, List.getD_cons_zero, List.getD_cons_succ, Bool.false_eq_true,
+      if_false, if_true]
+    exact expect_indicator_sub (fun β re => F rg r (W β rg re)) m₀ m₁
+
+/-- **Single-bit security gives CPA security** for a padded single-bit scheme.
+
+**Proof sketch.**
+1. With CPA there is no `Dec` oracle, so the adversary's view is `pk`, its coins and the padded
+   challenge `padCt L (Enc_pk(m_b))`, where its messages `m₀, m₁ ∈ {0,1}` are chosen after
+   seeing `pk`. Only the first challenge query uses coins, so the encryption coins may be sampled
+   in advance (`expect_simulate_indImpl_cpa`); then `A`'s bit depends on the challenge answer only
+   through its value at `A`'s first challenge query `(m₀, m₁)`, which itself does not depend on
+   that answer (`ChallengeSim.chRun_congr`).
+2. If `m₀ = m₁` both games are identical. Otherwise `m_b` is `b` or `¬b`. The distinguisher `D`
+   on `⟨pk, c⟩` runs `A` on `pk`, answers every challenge with `padCt L c` and every `Dec` query
+   with `⊥`, records `A`'s first challenge `(m₀, m₁)`, and outputs `A`'s bit, flipped when
+   `(m₀, m₁) = (1, 0)` and replaced by `0` when `m₀ = m₁` or no challenge was asked. T1
+   (`Games.exists_handlerMachine`, for the handler `ChallengeSim.recHandler`) makes `D` a
+   machine, whose output is exactly this bit (`ChallengeSim.simulate_recHandler_init`).
+3. Fixing `pk` and `A`'s coins, the case split on `(m₀, m₁)` gives the same difference of
+   acceptance rates on both sides (`ChallengeSim.expect_indicator_sub`); so `A`'s CPA advantage
+   equals `D`'s advantage between `⟨pk, Enc_pk(0)⟩` and `⟨pk, Enc_pk(1)⟩` at every `n`
+   (`padded_cpa_advantage_eq`), which is negligible (`BitPublicKeyScheme.singleBitSecure_iff`). -/
+theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.padded_cpa
+    {S : BitPublicKeyScheme} (h : S.SingleBitSecure) (L : PolyExpr)
+    (hL : ∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
+      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
+        ≤ L.eval n)
+    (hmsg : ∀ n, 1 ≤ L.eval n) : (S.padded L hL hmsg).INDSecure .cpa := by
+  rw [FixedLengthPKScheme.INDSecure_iff]
+  intro A q
+  -- Step 3: the distinguisher `D` is T1's machine for the recording handler.
+  obtain ⟨B, hB⟩ := exists_handlerMachine A q (recDin L) (recDout L) (.const 1)
+    (recHandler L (cpaAns L) (polyTimeComputable_cpaAns L))
+  refine ⟨_, (BitPublicKeyScheme.singleBitSecure_iff S).1 h B, fun n => le_of_eq ?_⟩
+  -- Step 4: the advantages are equal.
+  obtain ⟨φ, hφ⟩ := hB n
+  exact padded_cpa_advantage_eq L hL hmsg A q B n φ hφ
+
+end PaddedCPA
+
+end TCSlib.Cryptography.Composability
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/RecordHandler.lean b/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/RecordHandler.lean
index 8e670d56a..346f45408 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/RecordHandler.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/RecordHandler.lean
@@ -264,7 +264,7 @@ theorem simulate_recHandler_recorded
       have hans1 : (recHandler Lc ans hans).answer n z ω s 1 x =
           (padFin _ (ans (seedIn n z (List.ofFn ω))), s) := by
         refine PolyHandler.answer_of_run_eq _ ?_
-        rw [recHandler_run, PolyHandler.input_eq, GGMRed.ofFn_padFin_of_length (by
+        rw [recHandler_run, PolyHandler.input_eq, ofFn_padFin_of_length (by
           rw [hw, recDout_one]), seedIn_eq]
         exact recRun_recorded ans _ _ _ hs
       rw [simulate_query, PolyHandler.impl_apply, hans1, OracleComp.pure_bind,
@@ -315,8 +315,8 @@ theorem simulate_recHandler_init
       have hans1 : (recHandler Lc ans hans).answer n z ω ((recHandler Lc ans hans).init n) 1 x =
           (padFin _ (ans (seedIn n z (List.ofFn ω))), padFin _ (true :: List.ofFn x)) := by
         refine PolyHandler.answer_of_run_eq _ ?_
-        rw [recHandler_run, PolyHandler.input_eq, GGMRed.ofFn_padFin_of_length (by
-          rw [hw, recDout_one]), GGMRed.ofFn_padFin_of_length hlen, seedIn_eq]
+        rw [recHandler_run, PolyHandler.input_eq, ofFn_padFin_of_length (by
+          rw [hw, recDout_one]), ofFn_padFin_of_length hlen, seedIn_eq]
         refine recRun_fresh ans _ _ _ ?_
         rw [hinit]
         rfl
@@ -324,8 +324,8 @@ theorem simulate_recHandler_init
       · rw [simulate_query, PolyHandler.impl_apply, hans1, OracleComp.pure_bind,
           chRun_query_one_none]
         exact simulate_recHandler_recorded Lc hans n z ω hw _ _
-          (by rw [GGMRed.ofFn_padFin_of_length hlen]; rfl)
-      · rw [GGMRed.ofFn_padFin_of_length hlen, firstQ_query_one]
+          (by rw [ofFn_padFin_of_length hlen]; rfl)
+      · rw [ofFn_padFin_of_length hlen, firstQ_query_one]
         rfl
 
 end Simulation
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/TrapdoorCPA.lean b/TCSlib/Cryptography/Encryption/PublicKey/TrapdoorCPA.lean
index 875906c3f..5b211d9c5 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/TrapdoorCPA.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/TrapdoorCPA.lean
@@ -3,7 +3,7 @@ Copyright (c) 2026 TCSlib contributors. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 -/
 import TCSlib.Cryptography.Encryption.PublicKey.Trapdoor
-import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
+import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.PaddedCPA
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -23,7 +23,8 @@ This module provides the original public-key game import through
 
 `TCSlib.Cryptography.TrapdoorCollection.tdpBitScheme_padded_cpa` applies the
 ensemble-to-CPA bridge to the trapdoor construction of Algorithm 104.3.
-It uses the stated `BitPublicKeyScheme.SingleBitSecure.padded_cpa` bridge.
+It uses the `BitPublicKeyScheme.SingleBitSecure.padded_cpa` bridge of
+`TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.PaddedCPA`.
 
 ## References
 
diff --git a/TCSlib/Cryptography/Foundations.lean b/TCSlib/Cryptography/Foundations.lean
index 5b01fd51e..2cd2acc8e 100644
--- a/TCSlib/Cryptography/Foundations.lean
+++ b/TCSlib/Cryptography/Foundations.lean
@@ -5,6 +5,7 @@ Released under Apache 2.0 license as described in the file LICENSE.
 import TCSlib.Cryptography.Foundations.Negligible
 import TCSlib.Cryptography.Foundations.Probability
 import TCSlib.Cryptography.Foundations.Experiments
+import TCSlib.Cryptography.Foundations.BitLists
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -24,6 +25,8 @@ one-way function, hard-concentrate bit and pseudorandomness developments are bui
   Fubini, averaging and the hybrid argument.
 * `Experiments`: `invProb`, `predProb`, `acceptProb`, `distAdv`, and the bound of
   distinguishing advantage by statistical distance.
+* `BitLists`: generic facts about bit lists and bit vectors (heads of suffixes, flattening
+  one-bit blocks, cancellation of exclusive-or, `xorPerm`, keys of an association list).
 
 ## References
 
diff --git a/TCSlib/Cryptography/Foundations/BitLists.lean b/TCSlib/Cryptography/Foundations/BitLists.lean
new file mode 100644
index 000000000..54e270a2e
--- /dev/null
+++ b/TCSlib/Cryptography/Foundations/BitLists.lean
@@ -0,0 +1,105 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import Mathlib.Data.List.OfFn
+import Mathlib.Data.List.GetD
+import Mathlib.Logic.Equiv.Prod
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Bit lists and bit vectors
+
+Generic facts about lists, lists of bits and bit vectors `Fin n → Bool`, shared by the
+cryptographic developments: heads of suffixes, flattening singleton blocks, the bit of a one-bit
+vector, cancellation of exclusive-or, exclusive-or with a fixed vector as a permutation, and keys of
+an association list. They depend on Mathlib only.
+
+## Main definitions
+
+* `TCSlib.Cryptography.xorPerm v`: exclusive-or with the vector `v`, as a permutation.
+
+## Main results
+
+* `TCSlib.Cryptography.headD_drop`: the head of a suffix is an entry.
+* `TCSlib.Cryptography.flatten_ofFn_one`, `flatten_ofFn_singleton`: flattening one-element blocks.
+* `TCSlib.Cryptography.headD_ofFn_one`: the bit of a one-bit vector is the head of its string.
+* `TCSlib.Cryptography.zipWith_xor_cancel_left`: `(a ⊕ c) ⊕ a = c`.
+* `TCSlib.Cryptography.xorPerm_apply`: `xorPerm v y = y ⊕ v`.
+* `TCSlib.Cryptography.mem_keys_of_lookup_isSome`: a key with a value in an association list is
+  one of its keys.
+
+## References
+
+Generic list facts; no textbook counterpart.
+-/
+
+namespace TCSlib.Cryptography
+
+/-- The head of a dropped list is the element at the dropping index:
+`(l.drop i).headD d = l.getD i d`. -/
+theorem headD_drop {α : Type*} (l : List α) (i : ℕ) (d : α) : (l.drop i).headD d = l.getD i d := by
+  rw [List.headD_eq_head?, List.head?_drop, List.getD_eq_getElem?_getD]
+
+/-- **Flattening one-element blocks:** concatenating the one-bit blocks `g j` gives their bits,
+`(List.ofFn fun j => List.ofFn (g j)).flatten = List.ofFn fun j => g j 0` when the blocks have
+length `l = 1`.
+
+**Proof sketch.** Induction on the number `k` of blocks (`List.ofFn_succ`, `List.flatten_cons`). -/
+theorem flatten_ofFn_one {k l : ℕ} (hl : l = 1) (g : Fin k → Fin l → Bool) :
+    (List.ofFn fun j => List.ofFn (g j)).flatten = List.ofFn fun j => g j ⟨0, by omega⟩ := by
+  subst hl
+  induction k with
+  | zero => rfl
+  | succ k ih =>
+    rw [List.ofFn_succ, List.flatten_cons, ih (fun j => g j.succ), List.ofFn_succ (n := k)]
+    simp
+
+/-- Flattening singletons: `(List.ofFn fun i => List.ofFn fun _ : Fin p => f i).flatten =
+List.ofFn f` when `p = 1` (`flatten_ofFn_one` with constant blocks). -/
+theorem flatten_ofFn_singleton {p : ℕ} (hp : p = 1) :
+    ∀ {k : ℕ} (f : Fin k → Bool),
+      (List.ofFn fun i => List.ofFn fun _ : Fin p => f i).flatten = List.ofFn f :=
+  fun f => flatten_ofFn_one hp fun i _ => f i
+
+/-- The bit of a one-bit output is the head of its string: `⟦f⟧.headD false = f 0`. -/
+theorem headD_ofFn_one (f : Fin 1 → Bool) : (List.ofFn f).headD false = f 0 := by
+  rw [List.ofFn_succ, List.headD_cons]
+
+/-- Exclusive-or with the same list twice cancels: `(a ⊕ c) ⊕ a = c` for `|a| = |c|`. -/
+theorem zipWith_xor_cancel_left {a c : List Bool} (h : a.length = c.length) :
+    List.zipWith xor (List.zipWith xor a c) a = c := by
+  apply List.ext_getElem
+  · simp [h]
+  · intro i h₁ h₂
+    simp only [List.getElem_zipWith]
+    cases a[i] <;> cases c[i] <;> rfl
+
+section XorPerm
+
+variable {n : ℕ}
+
+/-- Exclusive-or with a fixed vector `v`, as a permutation of `{0,1}ⁿ`: `xorPerm v y = y ⊕ v`. -/
+def xorPerm (v : Fin n → Bool) : Equiv.Perm (Fin n → Bool) :=
+  Function.Involutive.toPerm (fun y i => xor (y i) (v i)) fun y => funext fun i => by
+    simp
+
+/-- `xorPerm v y = y ⊕ v`. -/
+theorem xorPerm_apply (v y : Fin n → Bool) : xorPerm v y = fun i => xor (y i) (v i) := rfl
+
+end XorPerm
+
+/-- A key with a value in an association list is one of its keys:
+`(T.lookup x).isSome → x ∈ T.map Prod.fst`.
+
+**Proof sketch.** Core's `List.lookup_isSome_iff` gives a pair `p ∈ T` with `x == p.1`, so `x`
+is the first component of an element of `T` (`List.mem_map`). -/
+theorem mem_keys_of_lookup_isSome {α β : Type} [DecidableEq α] (T : List (α × β)) (x : α)
+    (h : (T.lookup x).isSome = true) : x ∈ T.map Prod.fst := by
+  obtain ⟨p, hp, hx⟩ := List.lookup_isSome_iff.1 h
+  exact List.mem_map.2 ⟨p, hp, (beq_iff_eq.1 hx).symm⟩
+
+end TCSlib.Cryptography
diff --git a/TCSlib/Cryptography/Games/BitCodec.lean b/TCSlib/Cryptography/Games/BitCodec.lean
index b00fa697a..3fa41a97b 100644
--- a/TCSlib/Cryptography/Games/BitCodec.lean
+++ b/TCSlib/Cryptography/Games/BitCodec.lean
@@ -4,6 +4,7 @@ Released under Apache 2.0 license as described in the file LICENSE.
 -/
 import TCSlib.Cryptography.Games.Machines
 import TCSlib.Cryptography.Asymptotic.Adversary
+import TCSlib.Cryptography.Games.Probability
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -34,6 +35,7 @@ It is the shared codec of every prong's statements, and the T0 definitions of th
   a move.
 * `Games.encodeBitMove`: the canonical word of a move.
 * `Games.bitCodec din dout dα`: the codec.
+* `Games.castImpl`: an implementation of bit-string oracles read along equal length functions.
 
 ## Main results
 
@@ -42,6 +44,10 @@ It is the shared codec of every prong's statements, and the T0 definitions of th
 * `Games.decodeIdx_eq_some_iff`, `Games.decodeBitMove_eq_query_iff`: only the canonical words
   decode as an index or a query.
 * `Games.decodeBitMove_of_not_canonical`: every other word decodes to the all-`false` output.
+* `Games.padFin_ofFn_zeroBits`, `Games.padFin_replicate_false`, `Games.padFin_nil`,
+  `Games.decodeFin_nil_getD`: all-`false` strings and the empty answer read as `zeroBits`.
+* `Games.simulate_castImpl_toCompOn`, `Games.expect_simulate_castImpl_toCompOn`: transport of a
+  machine's run between two codecs with equal lengths.
 
 ## References
 
@@ -121,6 +127,33 @@ theorem zeroBits_apply (d : ℕ) (j : Fin d) : zeroBits d j = false :=
 theorem ofFn_zeroBits (d : ℕ) : List.ofFn (zeroBits d) = List.replicate d false := by
   rw [show zeroBits d = fun _ => false from rfl, List.ofFn_const]
 
+/-- The all-`false` answer, read at any width, is all-`false`:
+`padFin d ⟦zeroBits m⟧ = zeroBits d`. -/
+theorem padFin_ofFn_zeroBits (d m : ℕ) : padFin d (List.ofFn (zeroBits m)) = zeroBits d := by
+  funext i
+  rw [padFin_apply, ofFn_zeroBits, zeroBits_apply, List.getD_eq_getElem?_getD,
+    List.getElem?_replicate]
+  split <;> rfl
+
+/-- An all-`false` list reads as the all-`false` vector at every width:
+`padFin d (List.replicate m false) = zeroBits d`. -/
+theorem padFin_replicate_false (d m : ℕ) : padFin d (List.replicate m false) = zeroBits d := by
+  rw [← ofFn_zeroBits, padFin_ofFn_zeroBits]
+
+/-- The empty list reads as the all-`false` vector: `padFin d [] = zeroBits d`. -/
+theorem padFin_nil (d : ℕ) : padFin d [] = zeroBits d := padFin_replicate_false d 0
+
+/-- An empty answer decodes to all-`false` at every length:
+`(decodeFin ℓ []).getD (zeroBits ℓ) = zeroBits ℓ`. -/
+theorem decodeFin_nil_getD (ℓ : ℕ) : (decodeFin ℓ []).getD (zeroBits ℓ) = zeroBits ℓ := by
+  rw [decodeFin_eq]
+  split
+  · next h =>
+    subst h
+    funext i
+    exact absurd i.isLt (Nat.not_lt_zero _)
+  · rfl
+
 /-- Decoding of a machine output as a move against `bitSpec din dout` with `dα`-bit outputs:
 `⟨[false], ⟨1^i, x⟩⟩` with `i < k` and `|x| = din i` is the query `x` to oracle `i`;
 `⟨[true], a⟩` with `|a| = dα` is the output `a`; anything else is the output `zeroBits dα`. -/
@@ -294,4 +327,73 @@ theorem encodeBitMove_injective (din dout : Fin k → ℕ) (dα : ℕ) :
     Function.Injective (encodeBitMove din dout dα) := fun m m' h => by
   rw [← decodeBitMove_encodeBitMove din dout dα m, h, decodeBitMove_encodeBitMove]
 
+/-! ### Transport along equal lengths -/
+
+section Transport
+
+open ProbComp
+
+variable {σ : Type}
+
+/-- **An implementation read along length functions:** answer the query `x` to oracle `i` of
+`bitSpec ins outs` by asking `O` the query `padFin (ins' i) ⟦x⟧` and reading its answer `y` as
+`padFin (outs i) ⟦y⟧`. When `ins = ins'` and `outs = outs'` this is `O` itself
+(`castImpl_self`). -/
+def castImpl {ins ins' outs outs' : Fin k → ℕ} (O : QueryImpl (bitSpec ins' outs') σ unifSpec) :
+    QueryImpl (bitSpec ins outs) σ unifSpec :=
+  fun i x s => (O i (padFin (ins' i) (List.ofFn x)) s).bind fun p =>
+    .pure (padFin (outs i) (List.ofFn p.1), p.2)
+
+/-- The defining equation of `castImpl`: `castImpl O i x s =
+(O i (padFin (ins' i) ⟦x⟧) s).bind fun p => pure (padFin (outs i) ⟦p.1⟧, p.2)`. -/
+theorem castImpl_eq {ins ins' outs outs' : Fin k → ℕ}
+    (O : QueryImpl (bitSpec ins' outs') σ unifSpec) (i : Fin k) (x : Fin (ins i) → Bool)
+    (s : σ) :
+    castImpl (ins := ins) (outs := outs) O i x s =
+      (O i (padFin (ins' i) (List.ofFn x)) s).bind fun p =>
+        .pure (padFin (outs i) (List.ofFn p.1), p.2) :=
+  rfl
+
+/-- Read along the same lengths, an implementation is unchanged: `castImpl O = O`. -/
+theorem castImpl_self {ins outs : Fin k → ℕ} (O : QueryImpl (bitSpec ins outs) σ unifSpec) :
+    castImpl (ins := ins) (outs := outs) O = O := by
+  funext i x s
+  rw [castImpl_eq, padFin_ofFn]
+  simp only [padFin_ofFn]
+  exact OracleComp.bind_pure _
+
+/-- **Transport of a machine's run:** if `ins = ins'`, `outs = outs'` and `d = d'`, simulating
+`castImpl O` on the run of `M` through `bitCodec ins outs d` gives, with outputs read as lists,
+the simulation of `O` on the run of `M` through `bitCodec ins' outs' d'`.
+
+**Proof sketch.** Substitute the equalities; then `castImpl O = O` (`castImpl_self`). -/
+theorem simulate_castImpl_toCompOn {ins ins' outs outs' : Fin k → ℕ} {d d' : ℕ}
+    (hi : ins = ins') (ho : outs = outs') (hd : d = d')
+    (O : QueryImpl (bitSpec ins' outs') σ unifSpec) (M : NUPPT) (n q : ℕ) (x : List Bool)
+    (r : M.Coins n) (s : σ) :
+    (simulate (castImpl (ins := ins) (outs := outs) O)
+        (M.toCompOn (bitCodec ins outs d) n q x r) s).bind
+        (fun p => .pure (List.ofFn p.1, p.2)) =
+      (simulate O (M.toCompOn (bitCodec ins' outs' d') n q x r) s).bind
+        (fun p => .pure (List.ofFn p.1, p.2)) := by
+  subst hi ho hd
+  rw [castImpl_self]
+
+/-- **Transport of a machine's run, in expectation:** for every function `G` of the output (read
+as a list) and the final state, `simulate_castImpl_toCompOn` in the form
+`𝔼[G (⟦p.1⟧, p.2)]` over the two simulations. -/
+theorem expect_simulate_castImpl_toCompOn {ins ins' outs outs' : Fin k → ℕ} {d d' : ℕ}
+    (hi : ins = ins') (ho : outs = outs') (hd : d = d')
+    (O : QueryImpl (bitSpec ins' outs') σ unifSpec) (M : NUPPT) (n q : ℕ) (x : List Bool)
+    (r : M.Coins n) (s : σ) (G : List Bool × σ → ℝ) :
+    expect (simulate (castImpl (ins := ins) (outs := outs) O)
+        (M.toCompOn (bitCodec ins outs d) n q x r) s) (fun p => G (List.ofFn p.1, p.2)) =
+      expect (simulate O (M.toCompOn (bitCodec ins' outs' d') n q x r) s)
+        (fun p => G (List.ofFn p.1, p.2)) := by
+  have h := congrArg (fun c => expect c G) (simulate_castImpl_toCompOn hi ho hd O M n q x r s)
+  simp only [expect_bind, expect_pure] at h
+  exact h
+
+end Transport
+
 end TCSlib.Cryptography.Games
diff --git a/TCSlib/Cryptography/Games/Efficiency.lean b/TCSlib/Cryptography/Games/Efficiency.lean
index 139d77324..c17489bb6 100644
--- a/TCSlib/Cryptography/Games/Efficiency.lean
+++ b/TCSlib/Cryptography/Games/Efficiency.lean
@@ -91,6 +91,8 @@ handler, the reduction's output. This bounds every history, which the guarded st
   times per inner query, and its semantics as a `QueryImpl` of the inner oracles by the outer ones;
   `InteractiveHandler.advInput` and `InteractiveHandler.finish`: the adversary's input and the
   finalization, with up to `finCall(n)` outer queries.
+* `Games.InteractiveHandler.rU`, `rZ`, `rW`, `rS`, `rI`, `rX`, `rL`, `rCnt`: the fields of a
+  round input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩` (and the first component of the state).
 
 ## Main results
 
@@ -101,6 +103,9 @@ handler, the reduction's output. This bounds every history, which the guarded st
   `q(n) · perCall(n) + finCall(n)`, whose computation is exactly the simulation followed by the
   finalization. The reductions that forward or answer queries with their own oracle need it (the
   PRF MAC's distinguisher, hash-and-sign's forger, the CPA and CCA reductions).
+* `Games.InteractiveHandler.rU_input`, …, `rCnt_input`: the readers of a round input on
+  `InteractiveHandler.input`; `Games.InteractiveHandler.impl_of_ret`: a call whose first round
+  returns.
 * `Games.exists_toCompOn_of_toComp` (the fill's target): a machine without input is a machine
   with an input that it ignores, with the same coins.
 * `Games.exists_toOracleAdversary_of_bitCodec` (T4, the fill's target): an oracle machine
@@ -442,6 +447,106 @@ theorem input_eq (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
         (pairEncode s (pairEncode (pairEncode (List.replicate i true) x) L)) :=
   rfl
 
+/-! #### Readers of a round input
+
+The fields of a round input `w = ⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`, read with `pairFstD` and
+`pairSndD`, as a handler's round function reads them; on `input n z ω s i x L` they return the
+field (`rU_input`, …), and each is polynomial-time (`polyTimeComputable_rU`, …). `rCnt` reads the
+first component of the state, the call count `1^j` of the handlers that keep one there. -/
+
+/-- The parameter `1^n` of a round input: `rU w = pairFstD (pairFstD w)`. -/
+def rU (w : List Bool) : List Bool := pairFstD (pairFstD w)
+/-- The reduction input `z` of a round input: `rZ w = pairFstD (pairSndD (pairFstD w))`. -/
+def rZ (w : List Bool) : List Bool := pairFstD (pairSndD (pairFstD w))
+/-- The seed `ω` of a round input: `rW w = pairSndD (pairSndD (pairFstD w))`. -/
+def rW (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD w))
+/-- The state `s` of a round input: `rS w = pairFstD (pairSndD w)`. -/
+def rS (w : List Bool) : List Bool := pairFstD (pairSndD w)
+/-- The oracle index `1^i` of a round input:
+`rI w = pairFstD (pairFstD (pairSndD (pairSndD w)))`. -/
+def rI (w : List Bool) : List Bool := pairFstD (pairFstD (pairSndD (pairSndD w)))
+/-- The query `x` of a round input: `rX w = pairSndD (pairFstD (pairSndD (pairSndD w)))`. -/
+def rX (w : List Bool) : List Bool := pairSndD (pairFstD (pairSndD (pairSndD w)))
+/-- The outer log `L` of a round input: `rL w = pairSndD (pairSndD (pairSndD w))`. -/
+def rL (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))
+/-- The first component `pairFstD s` of the state of a round input:
+`rCnt w = pairFstD (rS w)`. -/
+def rCnt (w : List Bool) : List Bool := pairFstD (rS w)
+
+/-- `rU (input n z ω s i x L) = 1^n`. -/
+theorem rU_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
+    rU (input n z ω s i x L) = List.replicate n true := by
+  simp only [rU, input_eq, pairFstD_pairEncode]
+
+/-- `rZ (input n z ω s i x L) = z`. -/
+theorem rZ_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
+    rZ (input n z ω s i x L) = z := by
+  simp only [rZ, input_eq, pairFstD_pairEncode, pairSndD_pairEncode]
+
+/-- `rW (input n z ω s i x L) = ω`. -/
+theorem rW_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
+    rW (input n z ω s i x L) = ω := by
+  simp only [rW, input_eq, pairFstD_pairEncode, pairSndD_pairEncode]
+
+/-- `rS (input n z ω s i x L) = s`. -/
+theorem rS_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
+    rS (input n z ω s i x L) = s := by
+  simp only [rS, input_eq, pairFstD_pairEncode, pairSndD_pairEncode]
+
+/-- `rI (input n z ω s i x L) = 1^i`. -/
+theorem rI_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
+    rI (input n z ω s i x L) = List.replicate i true := by
+  simp only [rI, input_eq, pairFstD_pairEncode, pairSndD_pairEncode]
+
+/-- `rX (input n z ω s i x L) = x`. -/
+theorem rX_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
+    rX (input n z ω s i x L) = x := by
+  simp only [rX, input_eq, pairFstD_pairEncode, pairSndD_pairEncode]
+
+/-- `rL (input n z ω s i x L) = L`. -/
+theorem rL_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
+    rL (input n z ω s i x L) = L := by
+  simp only [rL, input_eq, pairSndD_pairEncode]
+
+/-- `rCnt (input n z ω s i x L) = pairFstD s`. -/
+theorem rCnt_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
+    rCnt (input n z ω s i x L) = pairFstD s := by
+  rw [rCnt, rS_input]
+
+/-- `rU` is polynomial-time: `PolyTimeComputable rU`. -/
+theorem polyTimeComputable_rU : PolyTimeComputable rU :=
+  polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD
+
+/-- `rZ` is polynomial-time: `PolyTimeComputable rZ`. -/
+theorem polyTimeComputable_rZ : PolyTimeComputable rZ :=
+  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)
+
+/-- `rW` is polynomial-time: `PolyTimeComputable rW`. -/
+theorem polyTimeComputable_rW : PolyTimeComputable rW :=
+  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)
+
+/-- `rS` is polynomial-time: `PolyTimeComputable rS`. -/
+theorem polyTimeComputable_rS : PolyTimeComputable rS :=
+  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
+
+/-- `rI` is polynomial-time: `PolyTimeComputable rI`. -/
+theorem polyTimeComputable_rI : PolyTimeComputable rI :=
+  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp
+    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
+
+/-- `rX` is polynomial-time: `PolyTimeComputable rX`. -/
+theorem polyTimeComputable_rX : PolyTimeComputable rX :=
+  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp
+    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
+
+/-- `rL` is polynomial-time: `PolyTimeComputable rL`. -/
+theorem polyTimeComputable_rL : PolyTimeComputable rL :=
+  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
+
+/-- `rCnt` is polynomial-time: `PolyTimeComputable rCnt`. -/
+theorem polyTimeComputable_rCnt : PolyTimeComputable rCnt :=
+  polyTimeComputable_pairFstD.comp polyTimeComputable_rS
+
 /-- The adversary's input at parameter `n`, for the reduction input `z` and the seed `ω`: `advIn`
 of the context `⟨1^n, ⟨z, ω⟩⟩`. -/
 def advInput (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
@@ -504,6 +609,39 @@ theorem impl_apply (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (
         .pure (fun j => w (Fin.castAdd _ j), fun j => w (Fin.natAdd _ j)) :=
   rfl
 
+/-- **A call whose first round returns `y ‖ s'`** is answered `y` with the new state `s'`: if
+`H.run (input n z ⟦ω⟧ ⟦s⟧ i ⟦x⟧ []) = ⟨[true], ⟦y⟧ ++ ⟦s'⟧⟩`, then
+`H.impl n z ω i x s = pure (y, s')`.
+
+**Proof sketch.** One call is `buildComp` of the rounds from the empty log (`call_eq`). The first
+round decodes as the final output `y ‖ s'` (`decodeBitMove_ret`), which stops the computation at
+every budget (`buildComp_zero_of_ret`, `buildComp_succ_of_ret`); the output splits back into `y`
+and `s'` (`Fin.append_left`, `Fin.append_right`). -/
+theorem impl_of_ret (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
+    (ω : Fin (H.seedLen.eval n) → Bool) {i : Fin k} (x : Fin ((din i).eval n) → Bool)
+    (s : Fin (H.stateLen.eval n) → Bool) (y : Fin ((dout i).eval n) → Bool)
+    (s' : Fin (H.stateLen.eval n) → Bool)
+    (h : H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x) []) =
+      pairEncode [true] (List.ofFn y ++ List.ofFn s')) :
+    H.impl n z ω i x s = .pure (y, s') := by
+  rw [impl_apply, call_eq]
+  have hy : (fun j => Fin.append y s' (Fin.castAdd (H.stateLen.eval n) j)) = y :=
+    funext fun j => Fin.append_left y s' j
+  have hs : (fun j => Fin.append y s' (Fin.natAdd ((dout i).eval n) j)) = s' :=
+    funext fun j => Fin.append_right y s' j
+  generalize H.perCall.eval n = q
+  cases q with
+  | zero =>
+    rw [buildComp_zero_of_ret (a := Fin.append y s') (by
+      show decodeBitMove _ _ _ (H.run _) = _
+      rw [MachineCodec.encodeLog_nil, h, ← List.ofFn_fin_append]
+      exact decodeBitMove_ret _ _ _ _), OracleComp.pure_bind, hy, hs]
+  | succ q =>
+    rw [buildComp_succ_of_ret (a := Fin.append y s') (by
+      show decodeBitMove _ _ _ (H.run _) = _
+      rw [MachineCodec.encodeLog_nil, h, ← List.ofFn_fin_append]
+      exact decodeBitMove_ret _ _ _ _), OracleComp.pure_bind, hy, hs]
+
 /-- The input string of one round of the finalization: `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`, with the
 final state `s`, the adversary's output `a` and the outer log `L` of the finalization so far. -/
 def finInput (n : ℕ) (z ω s a L : List Bool) : List Bool :=
diff --git a/TCSlib/Cryptography/Games/Hopping.lean b/TCSlib/Cryptography/Games/Hopping.lean
index 3a6a3130b..5fc1e5184 100644
--- a/TCSlib/Cryptography/Games/Hopping.lean
+++ b/TCSlib/Cryptography/Games/Hopping.lean
@@ -35,7 +35,10 @@ The hybrid argument itself is `advantage_hybrid` (`TCSlib.Cryptography.Games.Adv
 * `ProbComp.prob_eq_one_of_allOutputs`, `ProbComp.expect_mono_of_allOutputs`: reasoning on the
   possible outputs only.
 * `ProbComp.abs_prob_sub_le_of_agree`: the difference lemma [Sho04, §1.1, Lemma 1].
-* `ProbComp.prob_mem_le`: the collision bound.
+* `ProbComp.prob_mem_le`: the collision bound; `ProbComp.expect_sample_mem_le`, its form for a
+  uniform sample and a fixed list.
+* `ProbComp.expect_simulate_congr`: implementations with the same laws simulate alike.
+* `ProbComp.prob_bad_le`: the per-query potential bound `Pr[bad] ≤ q · (size + q) · δ`.
 * `Games.prob_eq_until_bad`, `Games.identical_until_bad`, `Games.identical_until_bad_init`: the
   code-based fundamental lemma [BR06], in semantic form, from a fixed or a sampled initial
   state; `Games.hagree_of_eq` recovers the syntactic hypothesis.
@@ -349,4 +352,94 @@ theorem identical_until_bad_init {spec : OracleSpec ι}
   rw [abs_le]
   constructor <;> linarith
 
+namespace ProbComp
+
+/-! ### Simulation congruence and a bad-event potential -/
+
+/-- **Implementations with the same laws simulate alike:** if every call of `impl₀` and `impl₁`
+has the same expectation of every function `g` of the answer and the new state, the simulations
+of every computation have the same expectation of every function `G` of the output and the final
+state: `𝔼[G] (simulate impl₀ c s) = 𝔼[G] (simulate impl₁ c s)`.
+
+**Proof sketch.** Induction on `c`; at a query, both sides are the expectation over the call of the
+continuation's expectation (`simulate_query`, `expect_bind`), equal by induction and the
+hypothesis. -/
+theorem expect_simulate_congr {ι : Type} {spec : OracleSpec ι} {σ α : Type}
+    (impl₀ impl₁ : QueryImpl spec σ unifSpec)
+    (h : ∀ i x s (g : spec.rng i × σ → ℝ), expect (impl₀ i x s) g = expect (impl₁ i x s) g)
+    (c : OracleComp spec α) (s : σ) (G : α × σ → ℝ) :
+    expect (simulate impl₀ c s) G = expect (simulate impl₁ c s) G := by
+  induction c generalizing s with
+  | pure a => rw [simulate_pure, simulate_pure]
+  | query i x k ih =>
+    rw [simulate_query, simulate_query, expect_bind, expect_bind, h]
+    exact congrArg _ (funext fun p => ih p.1 p.2)
+
+/-- **A bad event raised a little at each query:** if from a good state each query raises `bad`
+with probability at most `(sz s + 1) · δ` and grows the size `sz` by at most one, then from a good
+state `s` a computation making at most `m` queries ends in a bad state with probability at most
+`m · (sz s + m) · δ`: `Pr[bad (simulate impl c s).2] ≤ m · (sz s + m) · δ`.
+
+**Proof sketch.** Induction on the computation. At a query, a bad successor contributes at most
+its probability; a good successor `s'` has `sz s' ≤ sz s + 1` and, by induction, contributes at
+most `(m - 1) · (sz s + m) · δ`. Add `(sz s + 1) · δ ≤ (sz s + m) · δ`. -/
+theorem prob_bad_le {ι : Type} {spec : OracleSpec ι} {σ : Type} {impl : QueryImpl spec σ unifSpec}
+    (bad : σ → Prop) [DecidablePred bad]
+    (sz : σ → ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
+    (hstep : ∀ i x s, ¬ bad s → prob (impl i x s) (fun ys => bad ys.2) ≤ (sz s + 1) * δ)
+    (hgrow : ∀ i x s, (impl i x s).AllOutputs fun ys => sz ys.2 ≤ sz s + 1)
+    {α : Type} (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ)
+    (hs : ¬ bad s) :
+    prob (simulate impl c s) (fun r => bad r.2) ≤ m * (sz s + m) * δ := by
+  induction c generalizing m s with
+  | pure a =>
+    rw [simulate_pure, prob_pure, if_neg hs]
+    exact mul_nonneg (by positivity) hδ
+  | query i x k ih =>
+    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
+    have hm1 : 1 ≤ m := hm
+    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
+    have hk' : ∀ y, (k y).CostBoundedBy (fun _ => 1) m' := fun y => by
+      simpa using hk y
+    have hm0 : (0 : ℝ) ≤ m' := Nat.cast_nonneg m'
+    set K : ℝ := m' * (sz s + (m' + 1)) * δ with hK
+    have hK0 : 0 ≤ K := mul_nonneg (by positivity) hδ
+    rw [simulate_query, prob_bind]
+    calc expect (impl i x s) (fun ys => prob (simulate impl (k ys.1) ys.2) (fun r => bad r.2))
+        ≤ expect (impl i x s) (fun ys => (if bad ys.2 then (1 : ℝ) else 0) + K) := by
+          refine expect_mono_of_allOutputs (hgrow i x s) fun ys hys => ?_
+          by_cases hb : bad ys.2
+          · rw [if_pos hb]
+            have h1 := prob_le_one (simulate impl (k ys.1) ys.2) (fun r => bad r.2)
+            linarith
+          · rw [if_neg hb, zero_add]
+            refine (ih ys.1 m' (hk' ys.1) ys.2 hb).trans ?_
+            have hys' : (sz ys.2 : ℝ) ≤ sz s + 1 := by exact_mod_cast hys
+            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hm0) hδ
+      _ = prob (impl i x s) (fun ys => bad ys.2) + K := by
+          rw [expect_add (impl i x s) (fun ys => if bad ys.2 then (1 : ℝ) else 0) (fun _ => K),
+            expect_const, prob_eq_expect]
+      _ ≤ ((m' + 1 : ℕ) : ℝ) * (sz s + ((m' + 1 : ℕ) : ℝ)) * δ := by
+          have h3 := hstep i x s hs
+          have h4 : ((sz s : ℝ) + 1) * δ ≤ (sz s + (m' + 1)) * δ :=
+            mul_le_mul_of_nonneg_right (by linarith) hδ
+          have e : ((m' : ℝ) + 1) * (sz s + (m' + 1)) * δ = K + (sz s + (m' + 1)) * δ := by
+            rw [hK]; ring
+          push_cast
+          linarith
+
+/-- **Hitting a list with a uniform sample:** a uniform element of `T` lies in a list `L` with
+probability at most `|L| / |T|`: `𝔼_{t ← T} [t ∈ L] ≤ |L| / |T|` (`prob_mem_le` for a fixed
+list). -/
+theorem expect_sample_mem_le {T : Type} [Fintype T] [Nonempty T] [DecidableEq T] (L : List T) :
+    expect (sample T) (fun t => if t ∈ L then (1 : ℝ) else 0) ≤ L.length / Fintype.card T := by
+  have h := prob_mem_le (OracleComp.pure L : ProbComp (List T)) (q := L.length)
+    (OracleComp.allOutputs_pure.2 le_rfl)
+  rw [prob_bind, expect_pure, prob_bind] at h
+  refine Eq.trans_le ?_ h
+  refine congrArg _ (funext fun t => ?_)
+  rw [prob_pure]
+
+end ProbComp
+
 end TCSlib.Cryptography.Games
diff --git a/TCSlib/Cryptography/Games/Probability.lean b/TCSlib/Cryptography/Games/Probability.lean
index 81a91dc5c..3ffd71753 100644
--- a/TCSlib/Cryptography/Games/Probability.lean
+++ b/TCSlib/Cryptography/Games/Probability.lean
@@ -43,6 +43,9 @@ information-theory layer, so statistical distance and closeness (`EpsClose`) app
   monotonicity.
 * `ProbComp.prob_nonneg`, `prob_le_one`, `prob_mono`, `prob_or_le` (the union bound),
   `prob_not`, `prob_bind`.
+* `ProbComp.expect_sample_equiv`, `expect_sample_comm`, `expect_sample_unique`,
+  `expect_sample_update`, `expect_sample_coord`: reindexing, exchanging and resampling uniform
+  samples; `expect_sub`, `abs_expect_sub_le`: subtraction and pointwise closeness.
 
 ## References
 
@@ -286,6 +289,109 @@ noncomputable def dist [Fintype α] [DecidableEq α] (c : ProbComp α) : FinDist
 theorem dist_apply [Fintype α] [DecidableEq α] (c : ProbComp α) (a : α) :
     dist c a = prob c (· = a) := rfl
 
+/-! ### Sampling identities -/
+
+section Sampling
+
+variable {β : Type}
+
+/-- **Reindexing a sample by an equivalence:** `𝔼_{a ← α} g (e a) = 𝔼_{b ← β} g b`.
+
+**Proof sketch.** Both are uniform averages (`expect_sample`); the cardinalities agree
+(`Fintype.card_congr`) and the sums agree by reindexing along `e` (`Equiv.sum_comp`). -/
+theorem expect_sample_equiv [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (e : α ≃ β)
+    (g : β → ℝ) : expect (sample α) (fun a => g (e a)) = expect (sample β) g := by
+  rw [expect_sample, expect_sample, Fintype.card_congr e, Equiv.sum_comp e g]
+
+/-- **Independent samples commute:**
+`𝔼_{a ← α} 𝔼_{b ← β} g a b = 𝔼_{b ← β} 𝔼_{a ← α} g a b`.
+
+**Proof sketch.** Both sides are the double uniform average (`expect_sample`); exchange the two
+finite sums (`Finset.sum_comm`). -/
+theorem expect_sample_comm [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
+    (g : α → β → ℝ) :
+    (expect (sample α) fun a => expect (sample β) fun b => g a b) =
+      expect (sample β) fun b => expect (sample α) fun a => g a b := by
+  simp only [expect_sample, mul_sum]
+  rw [sum_comm]
+  refine sum_congr rfl fun b _ => sum_congr rfl fun a _ => ?_
+  ring
+
+/-- **Sampling a singleton type** returns its element: `𝔼_{a ← α} g a = g default`. -/
+theorem expect_sample_unique [Fintype α] [Unique α] (g : α → ℝ) :
+    expect (sample α) g = g default := by
+  rw [expect_sample, Fintype.card_unique, Fintype.sum_unique]
+  simp
+
+/-- Expectation is subtractive: `𝔼[f − g] = 𝔼 f − 𝔼 g`. -/
+theorem expect_sub (c : ProbComp α) (f g : α → ℝ) :
+    expect c (fun a => f a - g a) = expect c f - expect c g := by
+  have h := expect_add c f (fun a => -1 * g a)
+  rw [expect_const_mul] at h
+  simp only [neg_one_mul, ← sub_eq_add_neg] at h
+  exact h
+
+/-- **Resampling one coordinate of a uniform tuple leaves it uniform**:
+`𝔼_{v} 𝔼_{b} f (update v j b) = 𝔼_{v} f v`.
+
+**Proof sketch.** The map `(v, b) ↦ (update v j b, v j)` is an involution of `(ι → β) × β`
+(`Function.update_idem`, `Function.update_eq_self`). Written as uniform averages
+(`expect_sample`), the double sum of `f (update v j b)` over pairs is the sum of `f v` over pairs
+reindexed along it (`Fintype.sum_prod_type'`, `Equiv.sum_comp`), which is `|β|` times the sum of
+`f`. -/
+theorem expect_sample_update {ι : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [Nonempty β]
+    (j : ι) (f : (ι → β) → ℝ) :
+    (expect (sample (ι → β)) fun v => expect (sample β) fun b => f (Function.update v j b)) =
+      expect (sample (ι → β)) f := by
+  let e : (ι → β) × β ≃ (ι → β) × β :=
+    { toFun := fun p => (Function.update p.1 j p.2, p.1 j)
+      invFun := fun p => (Function.update p.1 j p.2, p.1 j)
+      left_inv := fun p => by
+        simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
+      right_inv := fun p => by
+        simp only [Function.update_self, Function.update_idem, Function.update_eq_self] }
+  have hpair : (∑ v : ι → β, ∑ b : β, f (Function.update v j b)) =
+      ∑ v : ι → β, ∑ _b : β, f v := by
+    rw [← Fintype.sum_prod_type' (fun v b => f (Function.update v j b)),
+      ← Fintype.sum_prod_type' (fun v (_ : β) => f v)]
+    exact Equiv.sum_comp e (fun p => f p.1)
+  have hβ : (Fintype.card β : ℝ) ≠ 0 := by positivity
+  simp only [expect_sample, ← mul_sum]
+  rw [hpair]
+  simp only [sum_const, card_univ, nsmul_eq_mul, ← mul_sum]
+  rw [inv_mul_cancel_left₀ hβ]
+
+/-- **One coordinate of a uniform tuple, sampled apart:** if `F r T` does not depend on the
+coordinate `j` of `T`, then `𝔼_{T} F (T j) T = 𝔼_{r} 𝔼_{T} F r T`.
+
+**Proof sketch.** Exchange the samples on the right (`expect_sample_comm`) and resample the
+coordinate `j` on the left (`expect_sample_update`); pointwise,
+`F ((update T j r) j) (update T j r) = F r T` (`Function.update_self` and the hypothesis). -/
+theorem expect_sample_coord {ι : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [Nonempty β]
+    (j : ι) (F : β → (ι → β) → ℝ) (hF : ∀ r r' T, F r (Function.update T j r') = F r T) :
+    expect (sample (ι → β)) (fun T => F (T j) T) =
+      expect (sample β) fun r => expect (sample (ι → β)) fun T => F r T := by
+  rw [expect_sample_comm, ← expect_sample_update j (fun T => F (T j) T)]
+  refine congrArg _ (funext fun T => congrArg _ (funext fun r => ?_))
+  rw [Function.update_self, hF]
+
+/-- Expectations of functions `ε`-close at every point are `ε`-close:
+`(∀ x, |f x - g x| ≤ ε) → |𝔼_c f - 𝔼_c g| ≤ ε`. -/
+theorem abs_expect_sub_le (c : ProbComp α) {f g : α → ℝ} {ε : ℝ}
+    (h : ∀ x, |f x - g x| ≤ ε) : |expect c f - expect c g| ≤ ε := by
+  have h1 : expect c f ≤ expect c g + ε :=
+    calc expect c f ≤ expect c (fun x => g x + ε) :=
+          expect_mono c fun x => by linarith [(abs_le.1 (h x)).2]
+      _ = expect c g + ε := by rw [expect_add c g (fun _ => ε), expect_const]
+  have h2 : expect c g ≤ expect c f + ε :=
+    calc expect c g ≤ expect c (fun x => f x + ε) :=
+          expect_mono c fun x => by linarith [(abs_le.1 (h x)).1]
+      _ = expect c f + ε := by rw [expect_add c f (fun _ => ε), expect_const]
+  rw [abs_le]
+  constructor <;> linarith
+
+end Sampling
+
 end ProbComp
 
 end TCSlib.Cryptography.Games
diff --git a/TCSlib/Cryptography/Games/Simulate.lean b/TCSlib/Cryptography/Games/Simulate.lean
index acf23f38e..cb906962a 100644
--- a/TCSlib/Cryptography/Games/Simulate.lean
+++ b/TCSlib/Cryptography/Games/Simulate.lean
@@ -44,6 +44,8 @@ queried" are predicates on that log. Logging never changes the computation
 * `Games.simulate_costBoundedBy`: if each query of `c` to oracle `i` is answered by a computation
   of cost at most `b i`, and `c` is cost-bounded by `q` when oracle `i` costs `b i`, then the
   simulation is cost-bounded by `q`.
+* `Games.simulate_eq_of_abs`, `Games.simulate_eq_of_abs_bounded`: simulation through an
+  abstraction of the state, on every run or along runs with a query budget.
 
 ## References
 
@@ -273,4 +275,53 @@ theorem simulate_costBoundedBy {spec : OracleSpec ι} {spec' : OracleSpec ι'}
     rw [simulate_query]
     exact h
 
+/-! ### Simulation through a state abstraction -/
+
+/-- **Simulation through an abstraction of the state:** if every call of `impl₁` from the
+abstract state `f s` is the call of `impl₂` from `s` with its new state abstracted, the same holds
+for whole simulations: `simulate impl₁ c (f s) =
+(simulate impl₂ c s).bind fun p => pure (p.1, f p.2)`.
+
+**Proof sketch.** Induction on `c`; at a query, rewrite the call by the hypothesis and use the
+induction hypothesis on each continuation after associativity. -/
+theorem simulate_eq_of_abs {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
+    {σ₁ σ₂ α : Type} (impl₁ : QueryImpl spec σ₁ spec') (impl₂ : QueryImpl spec σ₂ spec')
+    (f : σ₂ → σ₁) (h : ∀ i x s, impl₁ i x (f s) = (impl₂ i x s).bind fun p => .pure (p.1, f p.2))
+    (c : OracleComp spec α) (s : σ₂) :
+    simulate impl₁ c (f s) = (simulate impl₂ c s).bind fun p => .pure (p.1, f p.2) := by
+  induction c generalizing s with
+  | pure a => simp only [simulate_pure, OracleComp.pure_bind]
+  | query i x k ih =>
+    rw [simulate_query, simulate_query, h, OracleComp.bind_assoc, OracleComp.bind_assoc]
+    congr 1
+    funext p
+    rw [OracleComp.pure_bind]
+    exact ih p.1 p.2
+
+/-- **Simulation through a state abstraction, along runs with a query budget:** let every call of
+`impl₂` from a state `s` with `cnt s < κ` be a deterministic answer `(y, s')` with
+`cnt s' ≤ cnt s + 1`, and the call of `impl₁` from `f s` be `(y, f s')`. Then for a computation
+`c` with at most `m` queries and `cnt s + m ≤ κ`,
+`simulate impl₁ c (f s) = (simulate impl₂ c s).bind fun p => pure (p.1, f p.2)`.
+
+**Proof sketch.** Induction on `c`. A query costs one unit, so it is asked from a state with
+`cnt s < κ`; both calls return the same answer, and the continuation runs from `s'` with one unit
+less, where `cnt s' + (m - 1) ≤ κ`. -/
+theorem simulate_eq_of_abs_bounded {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
+    {σ₁ σ₂ α : Type} (impl₁ : QueryImpl spec σ₁ spec') (impl₂ : QueryImpl spec σ₂ spec')
+    (f : σ₂ → σ₁) (cnt : σ₂ → ℕ) (κ : ℕ)
+    (h : ∀ i x s, cnt s < κ → ∃ (y : spec.rng i) (s' : σ₂), impl₂ i x s = .pure (y, s') ∧
+      cnt s' ≤ cnt s + 1 ∧ impl₁ i x (f s) = .pure (y, f s'))
+    (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ₂)
+    (hs : cnt s + m ≤ κ) :
+    simulate impl₁ c (f s) = (simulate impl₂ c s).bind fun p => .pure (p.1, f p.2) := by
+  induction c generalizing m s with
+  | pure a => simp only [simulate_pure, OracleComp.pure_bind]
+  | query i x k ih =>
+    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
+    have hm1 : 1 ≤ m := hm
+    obtain ⟨y, s', h₂, hcnt, h₁⟩ := h i x s (by omega)
+    rw [simulate_query, simulate_query, h₁, h₂, OracleComp.pure_bind, OracleComp.pure_bind]
+    exact ih y (m - 1) (hk y) s' (by omega)
+
 end TCSlib.Cryptography.Games
diff --git a/TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Run.lean b/TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Run.lean
index b60d08fe6..744448baa 100644
--- a/TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Run.lean
+++ b/TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Run.lean
@@ -173,12 +173,6 @@ theorem queryOf_eq_some_iff (ℓ : ℕ) (w : List Bool) (x : Fin ℓ → Bool) :
     rw [h]
     exact decodeFin_ofFn x
 
-/-- The encoding of the padding of a string of the right length is the string. -/
-theorem ofFn_padFin_of_length {ℓ : ℕ} {w : List Bool} (h : w.length = ℓ) :
-    List.ofFn (padFin ℓ w) = w := by
-  refine List.ext_getElem (by simp [h]) fun k hk₁ hk₂ => ?_
-  simp [padFin_def, List.getElem?_eq_getElem hk₂]
-
 /-- A machine output is a query iff its first component is `[false]` and its second has
 length `ℓ`. -/
 theorem exists_queryOf_iff (ℓ : ℕ) (w : List Bool) :
diff --git a/TCSlib/Cryptography/Pseudorandom/NextBit.lean b/TCSlib/Cryptography/Pseudorandom/NextBit.lean
index 6a835134a..8bda935ae 100644
--- a/TCSlib/Cryptography/Pseudorandom/NextBit.lean
+++ b/TCSlib/Cryptography/Pseudorandom/NextBit.lean
@@ -5,6 +5,7 @@ Authors: TCSlib contributors
 -/
 import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.Defs
 import TCSlib.Cryptography.Pseudorandom.NextBit.Concrete
+import TCSlib.Cryptography.Foundations.BitLists
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -80,13 +81,6 @@ theorem Ensemble.nextBitUnpredictable_iff_lt {ℓ : PolyExpr} (X : Ensemble ℓ)
     obtain ⟨ε, hε, hlt⟩ := h A
     exact ⟨ε, hε, fun n i => (hlt n i).le⟩
 
-/-- Bit `i` of `u` is the head of the suffix `(ofFn u).drop i` — the readout
-`polyTimeComputable_headD` of the machines below (`List.head?_drop`, `List.getElem?_ofFn`). -/
-private theorem headD_drop_ofFn {ℓ : ℕ} (i : Fin ℓ) (u : Fin ℓ → Bool) :
-    ((List.ofFn u).drop i).headD false = u i := by
-  rw [List.headD_eq_head?, List.head?_drop, List.getElem?_ofFn]
-  simp [i.isLt]
-
 /-- A distinguisher whose coin string is reindexed by a bijection has the same acceptance
 probability (`uprob_comp_equiv` on the coin factor of the sample space). -/
 private theorem acceptProb_coins_equiv {σ γ ρ ρ' : Type*} [Fintype σ] [Fintype ρ] [Fintype ρ']
@@ -121,7 +115,7 @@ of the advice's second component (`polyTimeComputable_headD`), and combines them
 `A := ofPolyTime` of it with coins `add ℓ D.coins` and advice bound `2·D.adv + 3`
 (`length_pairEncode`); the coin split is `Fin.appendEquiv` composed with `finCongr`, and the
 identity is `runAtL_ofPolyTime`, the projection identities of the layout,
-`List.take_left'`/`List.drop_left'`, `ofFn_completePrefix` and `headD_drop_ofFn`. -/
+`List.take_left'`/`List.drop_left'`, `ofFn_completePrefix` and `headD_drop`. -/
 private theorem exists_nextBitPredMachine (ℓ : PolyExpr) (D : NUPPT) (flip : ℕ → Bool) :
     ∃ (A : NUPPT) (e : ∀ n, (Fin (ℓ.eval n) → Bool) × D.Coins n ≃ A.Coins n),
       ∀ n (i : Fin (ℓ.eval n)) (t : Fin i → Bool) (u : Fin (ℓ.eval n) → Bool) (c : D.Coins n),
@@ -399,7 +393,7 @@ gives a positive `p` with `1/p(n) ≤ |ε n|` infinitely often. The distinguishe
 reads bit `k n` of `t` and outputs `[decide (verdict = [bit])]`. At every `n` with `ε n ≠ 0`
 (every `n` of the infinite set), `ε n` is attained at `i_n = k n`, and the functional identity
 `D.distinguisher n (ℓ n) t (e r) = nextBitDist i_n (A.predictor n i_n) t r` (`ofFn_prefixOf`,
-`headD_drop_ofFn`, coins reindexed by `e : A.Coins n ≃ D.Coins n` from `finCongr`) gives, by
+`headD_drop`, coins reindexed by `e : A.Coins n ≃ D.Coins n` from `finCongr`) gives, by
 `prgAdv_nextBitDist` and `acceptProb_coins_equiv`,
 `prgAdv (X_n) (D.distinguisher n (ℓ n)) = |nextBitProb (X_n) i_n (A.predictor n i_n) − 1/2| =
 |ε n| ≥ 1/p(n)` — the advantage being an absolute value, no choice between the predictor and
@@ -457,7 +451,7 @@ theorem Ensemble.Pseudorandom.nextBitUnpredictable {ℓ : PolyExpr} {X : Ensembl
     rw [NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq, hofn, hDm, hkn]
     rw [nextBitDist_eq]
     rw [NUPPT.predictor_eq, NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq,
-      ofFn_prefixOf, headD_drop_ofFn]
+      ofFn_prefixOf, headD_drop, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
     simp
   have hadv : prgAdv (X.X n) (Dm.distinguisher n (ℓ.eval n)) = |ε n| := by
     rw [← hspec, ← prgAdv_nextBitDist (X.X n) j₀ (A.predictor n j₀)]
diff --git a/TCSlib/Cryptography/SecureComputation/Yao.lean b/TCSlib/Cryptography/SecureComputation/Yao.lean
index a0327ad2d..e4a546c2d 100644
--- a/TCSlib/Cryptography/SecureComputation/Yao.lean
+++ b/TCSlib/Cryptography/SecureComputation/Yao.lean
@@ -6,6 +6,7 @@ import TCSlib.Cryptography.SecureComputation.Hybrid
 import TCSlib.Cryptography.SecureComputation.GarblingSecurity
 import TCSlib.Complexity.CircuitComplexity.Uniform
 import TCSlib.Complexity.ClassP.BinaryArith.Words
+import TCSlib.Cryptography.Foundations.BitLists
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -701,16 +702,6 @@ theorem yaoBobOut_yaoMsg (n : ℕ) (x : Fin (Y.inA.eval n) → Bool)
   · exact decodeOut_fst _ _
   · exact decodeOut_snd _ _ fun h => hdist j (List.ofFn_injective h).symm
 
-/-- Concatenating singleton lists: `[g₀ 0] ++ ⋯ ++ [g_{k−1} 0] = [g₀ 0, …, g_{k−1} 0]`. -/
-private theorem flatten_ofFn_one {k l : ℕ} (hl : l = 1) (g : Fin k → Fin l → Bool) :
-    (List.ofFn fun j => List.ofFn (g j)).flatten = List.ofFn fun j => g j ⟨0, by omega⟩ := by
-  subst hl
-  induction k with
-  | zero => rfl
-  | succ k ih =>
-    rw [List.ofFn_succ, List.flatten_cons, ih (fun j => g j.succ), List.ofFn_succ (n := k)]
-    simp
-
 /-- **Bob's OT answers are the keys of his bits**: in the hybrid execution, bit `i · n + t` of
 Bob's answers is bit `t` of the key `k_{inA + i}^{y_i}` of his wire `inA + i` for his bit `y_i`
 (`otFunctionality_f_snd`). -/
diff --git a/TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas.lean b/TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas.lean
index d631c6f07..36d815937 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas.lean
@@ -6,6 +6,7 @@ Authors: TCSlib contributors
 import TCSlib.Cryptography.Asymptotic.HardCore
 import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.FromPermutation
 import TCSlib.Cryptography.ZeroKnowledge.Interaction
+import TCSlib.Cryptography.Foundations.BitLists
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -267,10 +268,6 @@ theorem flatMap_range_eq_of_nil (F : ℕ → List Bool) {n m : ℕ} (hnm : n ≤
     List.flatMap_eq_nil_iff.2 fun x _ => hF _ (Nat.le_add_right n x)
   rw [h, List.append_nil]
 
-/-- The head of a dropped list is the element at the dropping index (`List.getD`). -/
-theorem headD_drop (l : List Bool) (i : ℕ) (d : Bool) : (l.drop i).headD d = l.getD i d := by
-  rw [List.headD_eq_head?, List.head?_drop, List.getD_eq_getElem?_getD]
-
 /-! ### The splice machines -/
 
 /-- The splice pre-processing on the argument `⟨z, ⟨pre, suf⟩⟩`: `pre ++ z ++ suf`. -/
diff --git a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean
index 4ce866b9d..1e3db04a3 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean
@@ -5,6 +5,7 @@ Authors: TCSlib contributors
 -/
 import TCSlib.Complexity.ClassP.BinaryArith.Loops
 import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Efficiency
+import TCSlib.Cryptography.Foundations.BitLists
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -585,10 +586,6 @@ theorem headD_take {c : ℕ} (hc : 0 < c) (l : List Bool) : (l.take c).headD fal
     | zero => omega
     | succ c => simp
 
-/-- An entry of a list with default is the first entry of the corresponding suffix. -/
-theorem getD_eq_headD_drop {α : Type*} (l : List α) (j : ℕ) (d : α) : l.getD j d = (l.drop j).headD d := by
-  rw [List.headD_eq_head?, List.head?_drop, List.getD_eq_getElem?_getD]
-
 /-- The verdict condition of the `|x|`-fold graph non-isomorphism verifier, read through the
 scan: message `j` is `pairFstD (pairSndD^[j] msgs)` and the first bit of coin block `j` is the
 first bit of `r.drop (j c)`. -/
@@ -599,7 +596,7 @@ theorem gni_verdict_iff (hist : List (List Bool)) (r : List Bool) (N c : ℕ) (h
   rw [Fin.forall_iff]
   refine forall_congr' fun j => forall_congr' fun _ => ?_
   rw [iterate_pairSndD_encodeMsgs, Strategy.pairFstD_encodeMsgs, coinBlock_eq, headD_take hc, Fin.val_mk,
-    getD_eq_headD_drop]
+    ← headD_drop]
 
 /-- The verifier of the `|x|`-fold graph non-isomorphism protocol is efficient (D8) (Inf-4.2).
 
diff --git a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI.lean b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI.lean
index b532d32af..3899a77df 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI.lean
@@ -4,6 +4,7 @@ Released under Apache 2.0 license as described in the file LICENSE.
 Authors: TCSlib contributors
 -/
 import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRep
+import TCSlib.Cryptography.Foundations.BitLists
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -300,8 +301,8 @@ theorem gi_verdict_iff (x : List Bool) (hist : List (List Bool)) (r : List Bool)
   rw [Fin.forall_iff]
   refine forall_congr' fun j => forall_congr' fun _ => ?_
   rw [Fin.val_mk, iterate_sndD_two_encodeMsgs, pairSndD_encodeMsgs, Strategy.pairFstD_encodeMsgs,
-    Strategy.pairFstD_encodeMsgs, List.drop_drop, relabelAt_replicate, ← getD_eq_headD_drop,
-    ← getD_eq_headD_drop, ← getD_eq_headD_drop]
+    Strategy.pairFstD_encodeMsgs, List.drop_drop, relabelAt_replicate, headD_drop,
+    headD_drop, headD_drop]
   cases r.getD j false <;> exact Iff.rfl
 
 /-- The verifier of the `|x|`-fold graph isomorphism protocol is efficient (D8) (Inf-4.2).
@@ -323,7 +324,7 @@ theorem giVerifierRep_efficient : giVerifierRep.Efficient := by
     List.length_replicate, inCoins_ilayout, argX_ilayout, vcount_ilayout, PolyExpr.eval_mul,
     PolyExpr.eval_const, PolyExpr.eval_var, decide_eq_true_eq]
   by_cases hodd : hist.length % 2 = 1
-  · rw [if_pos hodd, if_pos hodd, getD_eq_headD_drop]
+  · rw [if_pos hodd, if_pos hodd, ← headD_drop]
   · rw [if_neg hodd, if_neg hodd]
     by_cases hlt : hist.length < 2 * x.length
     · rw [if_pos hlt, if_pos hlt]

## ===== TCSlib/Cryptography/Games/Probability.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.OracleComp
import TCSlib.InformationTheory.FinDist

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Probabilistic computations

Randomness enters the framework as one more oracle: oracle `m` of `unifSpec` answers a uniformly
random element of `Fin (m + 1)`, and a uniform element of any nonempty finite type is obtained
through an enumeration. A *probabilistic computation* (`ProbComp`) is an oracle computation whose
only oracle is this one. Security games, once their adversary is plugged in and their oracles
implemented, are probabilistic computations.

The semantics is elementary and real-valued. The expectation of `g` over the output of a
computation is defined by recursion on the computation: a return contributes `g a`, and a sampling
step averages over its `m + 1` equally likely answers. There are no measures and no extended
reals: every computation is a finite tree with finite branching, so every probability is a finite
sum of rationals. The probability of an event is the expectation of its indicator. For a
computation with a finite output type, its output distribution is a `FinDist` of the library's
information-theory layer, so statistical distance and closeness (`EpsClose`) apply directly.

## Main definitions

* `Games.unifSpec`: the uniform-sampling oracles; `Games.ProbComp`: computations over them.
* `Games.ProbComp.sampleFin m`, `Games.ProbComp.sample T`: a uniform element of `Fin (m + 1)`, and
  of a nonempty finite type `T`.
* `Games.ProbComp.expect c g`: the expectation of `g` over the output of `c`.
* `Games.ProbComp.prob c p`: the probability that the output of `c` satisfies `p`.
* `Games.ProbComp.dist c`: the output distribution of `c`, for a finite output type.

## Main results

* `ProbComp.expect_bind`: **total expectation**; sequencing averages the continuations.
* `ProbComp.expect_sample`: sampling a finite type is the uniform average.
* `ProbComp.expect_add`, `expect_const_mul`, `expect_sum`, `expect_mono`: linearity and
  monotonicity.
* `ProbComp.prob_nonneg`, `prob_le_one`, `prob_mono`, `prob_or_le` (the union bound),
  `prob_not`, `prob_bind`.
* `ProbComp.expect_sample_equiv`, `expect_sample_comm`, `expect_sample_unique`,
  `expect_sample_update`, `expect_sample_coord`: reindexing, exchanging and resampling uniform
  samples; `expect_sub`, `abs_expect_sub_le`: subtraction and pointwise closeness.

## References

* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
  Uniform sampling as an oracle follows VCVio's uniform-selection oracle; the real-valued
  finite-sum semantics here is not VCVio's (which is measure-valued).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (probabilistic algorithms; the uniform distribution over coin strings).
-/

namespace TCSlib.Cryptography.Games

open Finset TCSlib.InformationTheory

/-- The **uniform-sampling oracles**: oracle `m` takes no query and answers a uniformly random
element of `Fin (m + 1)`. [VCVio, OracleComp/ProbComp] -/
abbrev unifSpec : OracleSpec ℕ := ⟨fun _ => Unit, fun m => Fin (m + 1)⟩

/-- **Probabilistic computations**: oracle computations whose only oracles draw uniform samples.
[VCVio, OracleComp/ProbComp/Basic] -/
abbrev ProbComp := OracleComp unifSpec

namespace ProbComp

variable {α β : Type}

/-- A uniformly random element of `Fin (m + 1)`. [VCVio, OracleComp/ProbComp/Basic (uniformFin)] -/
def sampleFin (m : ℕ) : ProbComp (Fin (m + 1)) := .query m () .pure

/-- Sampling `Fin (m + 1)` is one query to the `m`-th sampling oracle:
`sampleFin m = .query m () .pure`. -/
theorem sampleFin_eq (m : ℕ) : sampleFin m = .query m () .pure := rfl

/-- A uniformly random element of the nonempty finite type `T`, through its enumeration
`Fintype.equivFin`. -/
noncomputable def sample (T : Type) [Fintype T] [Nonempty T] : ProbComp T :=
  (fun j : Fin (Fintype.card T - 1 + 1) =>
    (Fintype.equivFin T).symm (Fin.cast (Nat.sub_add_cancel Fintype.card_pos) j)) <$>
      sampleFin (Fintype.card T - 1)

/-- Sampling `T` is sampling an index below `|T|` and reading it through `Fintype.equivFin`:
`sample T = (fun j => (equivFin T).symm (Fin.cast _ j)) <$> sampleFin (|T| − 1)`. -/
theorem sample_eq (T : Type) [Fintype T] [Nonempty T] :
    sample T = (fun j : Fin (Fintype.card T - 1 + 1) =>
      (Fintype.equivFin T).symm (Fin.cast (Nat.sub_add_cancel Fintype.card_pos) j)) <$>
        sampleFin (Fintype.card T - 1) := rfl

/-- The **expectation** of `g` over the output of `c`: `g a` for a return, and the average over
the `m + 1` equally likely answers at a sampling step. -/
noncomputable def expect : ProbComp α → (α → ℝ) → ℝ
  | .pure a, g => g a
  | .query m _ k, g => ((m : ℝ) + 1)⁻¹ * ∑ j : Fin (m + 1), expect (k j) g

/-- The **probability** that the output of `c` satisfies `p`: the expectation of the indicator
of `p`. -/
noncomputable def prob (c : ProbComp α) (p : α → Prop) : ℝ := by
  classical exact expect c (fun a => if p a then 1 else 0)

/-- A return is its own expectation. -/
@[simp] theorem expect_pure (a : α) (g : α → ℝ) : expect (.pure a) g = g a := rfl

/-- A sampling step averages over its answers. -/
theorem expect_query (m : ℕ) (x : Unit) (k : Fin (m + 1) → ProbComp α) (g : α → ℝ) :
    expect (.query m x k) g = ((m : ℝ) + 1)⁻¹ * ∑ j : Fin (m + 1), expect (k j) g := rfl

/-- **Total expectation:** the expectation over `c` followed by `f` is the expectation over `c`
of the expectation over `f a`.

**Proof sketch.** Induction on `c`: a return is immediate, and at a sampling step both sides
average the same continuations. -/
theorem expect_bind (c : ProbComp α) (f : α → ProbComp β) (g : β → ℝ) :
    expect (c.bind f) g = expect c (fun a => expect (f a) g) := by
  induction c with
  | pure a => simp only [OracleComp.pure_bind, expect_pure]
  | query m x k ih => simp only [OracleComp.query_bind, expect_query, ih]

/-- The expectation over a mapped computation is the expectation of the composite. -/
theorem expect_map (h : α → β) (c : ProbComp α) (g : β → ℝ) :
    expect (h <$> c) g = expect c (fun a => g (h a)) := by
  rw [OracleComp.map_eq_bind, expect_bind]; rfl

/-- Sampling `Fin (m + 1)` is the uniform average over it. -/
theorem expect_sampleFin (m : ℕ) (g : Fin (m + 1) → ℝ) :
    expect (sampleFin m) g = ((m : ℝ) + 1)⁻¹ * ∑ j, g j := rfl

/-- Sampling a nonempty finite type is the uniform average over it.

**Proof sketch.** The sample is the image of a uniform element of `Fin |T|` under the bijection
`Fintype.equivFin`, and a sum is invariant under reindexing by a bijection. -/
theorem expect_sample (T : Type) [Fintype T] [Nonempty T] (g : T → ℝ) :
    expect (sample T) g = (Fintype.card T : ℝ)⁻¹ * ∑ t, g t := by
  have hc : Fintype.card T - 1 + 1 = Fintype.card T := Nat.sub_add_cancel Fintype.card_pos
  rw [sample, expect_map, expect_sampleFin]
  congr 1
  · congr 1
    exact_mod_cast hc
  · exact Fintype.sum_equiv ((finCongr hc).trans (Fintype.equivFin T).symm) _ _
      (fun j => by simp)

/-- Expectation is additive. -/
theorem expect_add (c : ProbComp α) (f g : α → ℝ) :
    expect c (fun a => f a + g a) = expect c f + expect c g := by
  induction c with
  | pure a => rfl
  | query m x k ih => simp only [expect_query, ih, sum_add_distrib, mul_add]

/-- Expectation commutes with scaling by a constant. -/
theorem expect_const_mul (c : ProbComp α) (r : ℝ) (f : α → ℝ) :
    expect c (fun a => r * f a) = r * expect c f := by
  induction c with
  | pure a => rfl
  | query m x k ih =>
    simp only [expect_query, ih, ← mul_sum]
    ring

/-- The expectation of a constant is that constant. -/
theorem expect_const (c : ProbComp α) (r : ℝ) : expect c (fun _ => r) = r := by
  induction c with
  | pure a => rfl
  | query m x k ih =>
    simp only [expect_query, ih, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (m : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp

/-- Expectation commutes with finite sums. -/
theorem expect_sum {ι : Type} (c : ProbComp α) (s : Finset ι) (f : ι → α → ℝ) :
    expect c (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, expect c (f i) := by
  induction c with
  | pure a => rfl
  | query m x k ih =>
    simp only [expect_query, ih, mul_sum]
    exact sum_comm

/-- Expectation is monotone. -/
theorem expect_mono (c : ProbComp α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    expect c f ≤ expect c g := by
  induction c with
  | pure a => exact h a
  | query m x k ih =>
    simp only [expect_query]
    exact mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => ih j) (by positivity)

/-- The expectation of a nonnegative function is nonnegative. -/
theorem expect_nonneg (c : ProbComp α) {f : α → ℝ} (h : ∀ a, 0 ≤ f a) : 0 ≤ expect c f := by
  simpa [expect_const] using expect_mono c (f := fun _ => 0) h

/-! ### Probabilities of events -/

/-- The probability of `p` is the expectation of its indicator (any decidability instance). -/
theorem prob_eq_expect (c : ProbComp α) (p : α → Prop) [DecidablePred p] :
    prob c p = expect c (fun a => if p a then 1 else 0) := by
  unfold prob
  congr 1
  funext a
  congr 1

/-- A return satisfies `p` with probability one or zero. -/
theorem prob_pure (a : α) (p : α → Prop) [Decidable (p a)] :
    prob (.pure a) p = if p a then 1 else 0 := by
  classical
  rw [prob_eq_expect, expect_pure]
  congr 1

/-- **Total probability:** the probability over `c` followed by `f` is the expectation over `c`
of the probability over `f a`. -/
theorem prob_bind (c : ProbComp α) (f : α → ProbComp β) (p : β → Prop) :
    prob (c.bind f) p = expect c (fun a => prob (f a) p) := by
  classical
  simp only [prob_eq_expect, expect_bind]

/-- Probabilities are nonnegative. -/
theorem prob_nonneg (c : ProbComp α) (p : α → Prop) : 0 ≤ prob c p := by
  classical
  rw [prob_eq_expect]
  exact expect_nonneg c fun a => by split_ifs <;> norm_num

/-- Probabilities are at most one. -/
theorem prob_le_one (c : ProbComp α) (p : α → Prop) : prob c p ≤ 1 := by
  classical
  rw [prob_eq_expect]
  calc expect c (fun a => if p a then (1 : ℝ) else 0) ≤ expect c (fun _ => 1) :=
        expect_mono c fun a => by split_ifs <;> norm_num
    _ = 1 := expect_const c 1

/-- An event implied by another has at least its probability. -/
theorem prob_mono (c : ProbComp α) {p q : α → Prop} (h : ∀ a, p a → q a) :
    prob c p ≤ prob c q := by
  classical
  rw [prob_eq_expect, prob_eq_expect]
  exact expect_mono c fun a => by
    by_cases hp : p a
    · simp [hp, h a hp]
    · simp only [hp, if_false]; split_ifs <;> norm_num

/-- Events that agree on every output have the same probability. -/
theorem prob_congr (c : ProbComp α) {p q : α → Prop} (h : ∀ a, p a ↔ q a) :
    prob c p = prob c q :=
  le_antisymm (prob_mono c fun a => (h a).1) (prob_mono c fun a => (h a).2)

/-- **The union bound** for two events. -/
theorem prob_or_le (c : ProbComp α) (p q : α → Prop) :
    prob c (fun a => p a ∨ q a) ≤ prob c p + prob c q := by
  classical
  rw [prob_eq_expect, prob_eq_expect, prob_eq_expect, ← expect_add]
  exact expect_mono c fun a => by
    by_cases hp : p a <;> by_cases hq : q a <;> simp [hp, hq]

/-- The complement of an event has one minus its probability. -/
theorem prob_not (c : ProbComp α) (p : α → Prop) :
    prob c (fun a => ¬ p a) = 1 - prob c p := by
  classical
  rw [prob_eq_expect, prob_eq_expect, eq_sub_iff_add_eq, ← expect_add]
  calc expect c (fun a => (if ¬ p a then (1 : ℝ) else 0) + if p a then 1 else 0)
      = expect c (fun _ => 1) := by
        congr 1; funext a; by_cases hp : p a <;> simp [hp]
    _ = 1 := expect_const c 1

/-! ### Output distributions -/

/-- The **output distribution** of a computation with a finite output type: the probability of
each outcome. -/
noncomputable def dist [Fintype α] [DecidableEq α] (c : ProbComp α) : FinDist α where
  prob a := prob c (· = a)
  nonneg a := prob_nonneg c _
  sum_prob := by
    simp only [prob_eq_expect]
    rw [← expect_sum]
    calc expect c (fun x => ∑ a, if x = a then (1 : ℝ) else 0) = expect c (fun _ => 1) := by
          congr 1; funext x; simp
      _ = 1 := expect_const c 1

/-- The output distribution gives each outcome its probability. -/
theorem dist_apply [Fintype α] [DecidableEq α] (c : ProbComp α) (a : α) :
    dist c a = prob c (· = a) := rfl

/-! ### Sampling identities -/

section Sampling

variable {β : Type}

/-- **Reindexing a sample by an equivalence:** `𝔼_{a ← α} g (e a) = 𝔼_{b ← β} g b`.

**Proof sketch.** Both are uniform averages (`expect_sample`); the cardinalities agree
(`Fintype.card_congr`) and the sums agree by reindexing along `e` (`Equiv.sum_comp`). -/
theorem expect_sample_equiv [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (e : α ≃ β)
    (g : β → ℝ) : expect (sample α) (fun a => g (e a)) = expect (sample β) g := by
  rw [expect_sample, expect_sample, Fintype.card_congr e, Equiv.sum_comp e g]

/-- **Independent samples commute:**
`𝔼_{a ← α} 𝔼_{b ← β} g a b = 𝔼_{b ← β} 𝔼_{a ← α} g a b`.

**Proof sketch.** Both sides are the double uniform average (`expect_sample`); exchange the two
finite sums (`Finset.sum_comm`). -/
theorem expect_sample_comm [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (g : α → β → ℝ) :
    (expect (sample α) fun a => expect (sample β) fun b => g a b) =
      expect (sample β) fun b => expect (sample α) fun a => g a b := by
  simp only [expect_sample, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun b _ => sum_congr rfl fun a _ => ?_
  ring

/-- **Sampling a singleton type** returns its element: `𝔼_{a ← α} g a = g default`. -/
theorem expect_sample_unique [Fintype α] [Unique α] (g : α → ℝ) :
    expect (sample α) g = g default := by
  rw [expect_sample, Fintype.card_unique, Fintype.sum_unique]
  simp

/-- Expectation is subtractive: `𝔼[f − g] = 𝔼 f − 𝔼 g`. -/
theorem expect_sub (c : ProbComp α) (f g : α → ℝ) :
    expect c (fun a => f a - g a) = expect c f - expect c g := by
  have h := expect_add c f (fun a => -1 * g a)
  rw [expect_const_mul] at h
  simp only [neg_one_mul, ← sub_eq_add_neg] at h
  exact h

/-- **Resampling one coordinate of a uniform tuple leaves it uniform**:
`𝔼_{v} 𝔼_{b} f (update v j b) = 𝔼_{v} f v`.

**Proof sketch.** The map `(v, b) ↦ (update v j b, v j)` is an involution of `(ι → β) × β`
(`Function.update_idem`, `Function.update_eq_self`). Written as uniform averages
(`expect_sample`), the double sum of `f (update v j b)` over pairs is the sum of `f v` over pairs
reindexed along it (`Fintype.sum_prod_type'`, `Equiv.sum_comp`), which is `|β|` times the sum of
`f`. -/
theorem expect_sample_update {ι : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [Nonempty β]
    (j : ι) (f : (ι → β) → ℝ) :
    (expect (sample (ι → β)) fun v => expect (sample β) fun b => f (Function.update v j b)) =
      expect (sample (ι → β)) f := by
  let e : (ι → β) × β ≃ (ι → β) × β :=
    { toFun := fun p => (Function.update p.1 j p.2, p.1 j)
      invFun := fun p => (Function.update p.1 j p.2, p.1 j)
      left_inv := fun p => by
        simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
      right_inv := fun p => by
        simp only [Function.update_self, Function.update_idem, Function.update_eq_self] }
  have hpair : (∑ v : ι → β, ∑ b : β, f (Function.update v j b)) =
      ∑ v : ι → β, ∑ _b : β, f v := by
    rw [← Fintype.sum_prod_type' (fun v b => f (Function.update v j b)),
      ← Fintype.sum_prod_type' (fun v (_ : β) => f v)]
    exact Equiv.sum_comp e (fun p => f p.1)
  have hβ : (Fintype.card β : ℝ) ≠ 0 := by positivity
  simp only [expect_sample, ← mul_sum]
  rw [hpair]
  simp only [sum_const, card_univ, nsmul_eq_mul, ← mul_sum]
  rw [inv_mul_cancel_left₀ hβ]

/-- **One coordinate of a uniform tuple, sampled apart:** if `F r T` does not depend on the
coordinate `j` of `T`, then `𝔼_{T} F (T j) T = 𝔼_{r} 𝔼_{T} F r T`.

**Proof sketch.** Exchange the samples on the right (`expect_sample_comm`) and resample the
coordinate `j` on the left (`expect_sample_update`); pointwise,
`F ((update T j r) j) (update T j r) = F r T` (`Function.update_self` and the hypothesis). -/
theorem expect_sample_coord {ι : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [Nonempty β]
    (j : ι) (F : β → (ι → β) → ℝ) (hF : ∀ r r' T, F r (Function.update T j r') = F r T) :
    expect (sample (ι → β)) (fun T => F (T j) T) =
      expect (sample β) fun r => expect (sample (ι → β)) fun T => F r T := by
  rw [expect_sample_comm, ← expect_sample_update j (fun T => F (T j) T)]
  refine congrArg _ (funext fun T => congrArg _ (funext fun r => ?_))
  rw [Function.update_self, hF]

/-- Expectations of functions `ε`-close at every point are `ε`-close:
`(∀ x, |f x - g x| ≤ ε) → |𝔼_c f - 𝔼_c g| ≤ ε`. -/
theorem abs_expect_sub_le (c : ProbComp α) {f g : α → ℝ} {ε : ℝ}
    (h : ∀ x, |f x - g x| ≤ ε) : |expect c f - expect c g| ≤ ε := by
  have h1 : expect c f ≤ expect c g + ε :=
    calc expect c f ≤ expect c (fun x => g x + ε) :=
          expect_mono c fun x => by linarith [(abs_le.1 (h x)).2]
      _ = expect c g + ε := by rw [expect_add c g (fun _ => ε), expect_const]
  have h2 : expect c g ≤ expect c f + ε :=
    calc expect c g ≤ expect c (fun x => f x + ε) :=
          expect_mono c fun x => by linarith [(abs_le.1 (h x)).1]
      _ = expect c f + ε := by rw [expect_add c f (fun _ => ε), expect_const]
  rw [abs_le]
  constructor <;> linarith

end Sampling

end ProbComp

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Simulate.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.OracleComp

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Implementing oracles: simulation and logging

An oracle computation only *asks* its oracles. A security game decides how they answer: with a
keyed function, with fresh coins on every query (a randomized encryption oracle), refusing some
queries (a CCA2 decryption oracle that will not decrypt the challenge), or by asking other
oracles (a reduction that answers its adversary's queries with queries of its own). All of these
are *implementations*: for each oracle and query, a computation over a target specification that
returns the answer and updates a state. `simulate` runs a computation with every query answered
by an implementation, threading the state.

Logging is an implementation transformer: it answers as before and also appends every query and
its answer to a log kept in the state. Win conditions such as "the forged message was never
queried" are predicates on that log. Logging never changes the computation
(`simulate_withLog`).

## Main definitions

* `Games.QueryImpl spec σ spec'`: implementations of the oracles of `spec` by computations over
  `spec'`, with state `σ`.
* `Games.simulate impl c s`: run `c` from state `s`, answering its queries with `impl`.
* `Games.QueryImpl.ofComp`, `QueryImpl.passthrough`, `QueryImpl.sum`: stateless implementations,
  forwarding queries unchanged, and implementing two oracle families side by side.
* `Games.QueryLog spec`, `Games.QueryImpl.withLog`: the record of a run's queries and answers, and
  the logging transformer.
* `Games.QueryImpl.comp`: answering one implementation's queries with another.

## Main results

* `Games.simulate_bind`: simulation commutes with sequencing.
* `Games.simulate_withLog`: forgetting the log of a logged simulation gives the plain simulation.
* `Games.simulate_comp`: simulation composes; a reduction run against an implementation of its
  oracles is a single implementation of its adversary's oracles.
* `Games.simulate_costBoundedBy`: if each query of `c` to oracle `i` is answered by a computation
  of cost at most `b i`, and `c` is cost-bounded by `q` when oracle `i` costs `b i`, then the
  simulation is cost-bounded by `q`.
* `Games.simulate_eq_of_abs`, `Games.simulate_eq_of_abs_bounded`: simulation through an
  abstraction of the state, on every run or along runs with a query budget.

## References

* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
  22 January 2026, Definition 3.9 (answering an adversary's queries in a reduction).
-/

namespace TCSlib.Cryptography.Games

variable {ι ι' ι₁ ι₂ : Type} {α β σ : Type}

/-- An **implementation** of the oracles of `spec` by computations over `spec'`, with state `σ`:
on oracle `i`, query `x` and state `s`, a computation returning the answer and the new state.
[VCVio, SimSemantics] -/
abbrev QueryImpl {ι ι' : Type} (spec : OracleSpec ι) (σ : Type) (spec' : OracleSpec ι') : Type :=
  ∀ i, spec.dom i → σ → OracleComp spec' (spec.rng i × σ)

/-- An implementation is a function of the oracle, the query and the state:
`QueryImpl spec σ spec' = ∀ i, spec.dom i → σ → OracleComp spec' (spec.rng i × σ)`. -/
theorem queryImpl_def {ι ι' : Type} (spec : OracleSpec ι) (σ : Type) (spec' : OracleSpec ι') :
    QueryImpl spec σ spec' = ∀ i, spec.dom i → σ → OracleComp spec' (spec.rng i × σ) := rfl

/-- **Simulation:** run `c` from state `s`, answering each of its queries with `impl` and
threading the state; return `c`'s result and the final state. [VCVio, SimSemantics] -/
def simulate {spec : OracleSpec ι} {spec' : OracleSpec ι'} (impl : QueryImpl spec σ spec') :
    OracleComp spec α → σ → OracleComp spec' (α × σ)
  | .pure a, s => .pure (a, s)
  | .query i x k, s => (impl i x s).bind (fun ys => simulate impl (k ys.1) ys.2)

section Simulate

variable {spec : OracleSpec ι} {spec' : OracleSpec ι'} (impl : QueryImpl spec σ spec')

/-- Simulating a return returns it with the state unchanged. -/
@[simp] theorem simulate_pure (a : α) (s : σ) :
    simulate impl (OracleComp.pure a) s = .pure (a, s) := rfl

/-- Simulating a query runs the implementation, then simulates the continuation. -/
@[simp] theorem simulate_query (i : ι) (x : spec.dom i) (k : spec.rng i → OracleComp spec α)
    (s : σ) :
    simulate impl (OracleComp.query i x k) s =
      (impl i x s).bind (fun ys => simulate impl (k ys.1) ys.2) := rfl

/-- **Simulation commutes with sequencing:** simulating `c` followed by `f` is simulating `c`,
then simulating `f` on its result from the state it reached.

**Proof sketch.** Induction on `c`; at a query, both sides run the implementation first, and the
monad's associativity lines up the continuations. -/
theorem simulate_bind (c : OracleComp spec α) (f : α → OracleComp spec β) (s : σ) :
    simulate impl (c.bind f) s = (simulate impl c s).bind (fun p => simulate impl (f p.1) p.2) := by
  induction c generalizing s with
  | pure a => simp only [OracleComp.pure_bind, simulate_pure]
  | query i x k ih => simp only [OracleComp.query_bind, simulate_query, OracleComp.bind_assoc, ih]

/-- Simulating a single call is running the implementation. -/
theorem simulate_call (i : ι) (x : spec.dom i) (s : σ) :
    simulate impl (OracleComp.call i x) s = impl i x s := by
  rw [← OracleComp.bind_pure (OracleComp.call i x), OracleComp.call_bind, simulate_query]
  simp only [simulate_pure]
  exact OracleComp.bind_pure _

end Simulate

namespace QueryImpl

/-- A **stateless** implementation: oracle `i` answers query `x` by running `f i x`. -/
def ofComp {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (f : ∀ i, spec.dom i → OracleComp spec' (spec.rng i)) : QueryImpl spec σ spec' :=
  fun i x s => (f i x).bind (fun y => .pure (y, s))

/-- A stateless implementation runs `f i x` and keeps the state:
`ofComp f i x s = (f i x).bind (fun y => .pure (y, s))`. -/
theorem ofComp_apply {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (f : ∀ i, spec.dom i → OracleComp spec' (spec.rng i)) (i : ι) (x : spec.dom i) (s : σ) :
    ofComp f i x s = (f i x).bind (fun y => .pure (y, s)) :=
  rfl

/-- **Forwarding:** every query is passed unchanged to the same oracle of the target. -/
def passthrough {spec : OracleSpec ι} : QueryImpl spec σ spec :=
  ofComp (fun i x => OracleComp.call i x)

/-- Forwarding asks the same oracle the same query and keeps the state:
`passthrough i x s = .query i x (fun y => .pure (y, s))`. -/
theorem passthrough_apply {spec : OracleSpec ι} (i : ι) (x : spec.dom i) (s : σ) :
    passthrough (σ := σ) i x s = .query i x (fun y => .pure (y, s)) := by
  rw [passthrough, ofComp_apply, OracleComp.call_bind]

/-- Implement two oracle families **side by side**, sharing one state: `.inl i` is answered by
`impl₁`, and `.inr j` by `impl₂`. -/
def sum {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} {spec' : OracleSpec ι'}
    (impl₁ : QueryImpl s₁ σ spec') (impl₂ : QueryImpl s₂ σ spec') :
    QueryImpl (s₁.add s₂) σ spec'
  | .inl i => impl₁ i
  | .inr j => impl₂ j

/-- Side by side, the oracle `.inl i` is answered by `impl₁`: `sum impl₁ impl₂ (.inl i) x s =
impl₁ i x s`. -/
theorem sum_inl {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} {spec' : OracleSpec ι'}
    (impl₁ : QueryImpl s₁ σ spec') (impl₂ : QueryImpl s₂ σ spec') (i : ι₁) (x : s₁.dom i)
    (s : σ) : sum impl₁ impl₂ (.inl i) x s = impl₁ i x s :=
  rfl

/-- Side by side, the oracle `.inr j` is answered by `impl₂`: `sum impl₁ impl₂ (.inr j) x s =
impl₂ j x s`. -/
theorem sum_inr {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} {spec' : OracleSpec ι'}
    (impl₁ : QueryImpl s₁ σ spec') (impl₂ : QueryImpl s₂ σ spec') (j : ι₂) (x : s₂.dom j)
    (s : σ) : sum impl₁ impl₂ (.inr j) x s = impl₂ j x s :=
  rfl

end QueryImpl

/-! ### Composing implementations -/

/-- **Composition:** answer the queries of `spec` with `impl₁`, whose own queries (to `spec'`)
are answered by `impl₂`; the state is the pair of the two states. This is how a reduction that
answers its adversary's queries by querying its own oracles becomes, after its oracles are
implemented, a single implementation of the adversary's oracles.
[VCVio, SimSemantics/QueryImpl/Compose (QueryImpl.compose)] -/
def QueryImpl.comp {ι'' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {spec'' : OracleSpec ι''} {σ₁ σ₂ : Type} (impl₂ : QueryImpl spec' σ₂ spec'')
    (impl₁ : QueryImpl spec σ₁ spec') : QueryImpl spec (σ₁ × σ₂) spec'' :=
  fun i x s => (simulate impl₂ (impl₁ i x s.1) s.2).bind (fun p => .pure (p.1.1, (p.1.2, p.2)))

/-- The composed implementation simulates `impl₁`'s answer with `impl₂` and regroups the states:
`impl₂.comp impl₁ i x s =
(simulate impl₂ (impl₁ i x s.1) s.2).bind (fun p => .pure (p.1.1, (p.1.2, p.2)))`. -/
theorem QueryImpl.comp_apply {ι'' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {spec'' : OracleSpec ι''} {σ₁ σ₂ : Type} (impl₂ : QueryImpl spec' σ₂ spec'')
    (impl₁ : QueryImpl spec σ₁ spec') (i : ι) (x : spec.dom i) (s : σ₁ × σ₂) :
    impl₂.comp impl₁ i x s =
      (simulate impl₂ (impl₁ i x s.1) s.2).bind (fun p => .pure (p.1.1, (p.1.2, p.2))) :=
  rfl

/-- **Simulation composes:** simulating with `impl₂` a simulation by `impl₁` is simulating once
with the composed implementation, up to regrouping the states.
[VCVio, SimSemantics/QueryImpl/Compose (simulateQ_compose)]

**Proof sketch.** Induction on the computation. At a query, both sides first run `impl₁`'s answer
under `impl₂` (`simulate_bind` on the left, the definition of `comp` on the right), and the
continuations agree by induction after associativity. -/
theorem simulate_comp {ι'' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {spec'' : OracleSpec ι''} {σ₁ σ₂ : Type} (impl₂ : QueryImpl spec' σ₂ spec'')
    (impl₁ : QueryImpl spec σ₁ spec') (c : OracleComp spec α) (s₁ : σ₁) (s₂ : σ₂) :
    simulate impl₂ (simulate impl₁ c s₁) s₂ =
      (simulate (impl₂.comp impl₁) c (s₁, s₂)).bind (fun p => .pure ((p.1, p.2.1), p.2.2)) := by
  induction c generalizing s₁ s₂ with
  | pure a => simp only [simulate_pure, OracleComp.pure_bind]
  | query i x k ih =>
    simp only [simulate_query, simulate_bind, QueryImpl.comp, OracleComp.bind_assoc,
      OracleComp.pure_bind]
    congr 1
    funext p
    exact ih p.1.1 p.1.2 p.2

/-! ### Logging -/

/-- The **log** of a run: the list of its queries, each with the oracle asked, the query and the
answer, in order. [VCVio, QueryTracking/LoggingOracle] -/
abbrev QueryLog {ι : Type} (spec : OracleSpec ι) : Type :=
  List (Σ i, spec.dom i × spec.rng i)

/-- **Logging:** answer as `impl` does, and append each query and its answer to the log kept
beside the state. [VCVio, QueryTracking/LoggingOracle] -/
def QueryImpl.withLog {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (impl : QueryImpl spec σ spec') : QueryImpl spec (σ × QueryLog spec) spec' :=
  fun i x s => (impl i x s.1).bind (fun ys => .pure (ys.1, (ys.2, s.2 ++ [⟨i, x, ys.1⟩])))

/-- The logged implementation answers as `impl` and appends the entry to the log:
`impl.withLog i x s = (impl i x s.1).bind (fun ys => .pure (ys.1, (ys.2, s.2 ++ [⟨i, x, ys.1⟩])))`.
-/
theorem QueryImpl.withLog_apply {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (impl : QueryImpl spec σ spec') (i : ι) (x : spec.dom i) (s : σ × QueryLog spec) :
    impl.withLog i x s =
      (impl i x s.1).bind (fun ys => .pure (ys.1, (ys.2, s.2 ++ [⟨i, x, ys.1⟩]))) :=
  rfl

/-- **Logging is conservative:** forgetting the log of a logged simulation gives the plain
simulation, whatever the initial log.

**Proof sketch.** Induction on the computation: at a query, the logged implementation is the
plain one followed by a return that only extends the log, and the continuations agree by
induction. -/
theorem simulate_withLog {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (impl : QueryImpl spec σ spec') (c : OracleComp spec α) (s : σ) (log : QueryLog spec) :
    (simulate impl.withLog c (s, log)).bind (fun p => .pure (p.1, p.2.1)) =
      simulate impl c s := by
  induction c generalizing s log with
  | pure a => simp only [simulate_pure, OracleComp.pure_bind]
  | query i x k ih =>
    simp only [simulate_query, QueryImpl.withLog, OracleComp.bind_assoc, OracleComp.pure_bind]
    congr 1
    funext ys
    exact ih ys.1 ys.2 _

/-! ### Costs under simulation -/

/-- **Costs under simulation:** if every call to oracle `i` is answered by a computation of cost
at most `b i` (target costs `cost'`), and `c` is cost-bounded by `q` when oracle `i` costs
`b i`, then the simulation of `c` is cost-bounded by `q`. With `b i = 1` for every oracle the
reduction asks once per query, the reduction makes no more target queries than its adversary
makes queries.

**Proof sketch.** Induction on `c`. At a query to oracle `i` with budget `q ≥ b i`, the
implementation fits in `b i`, and the simulated continuation fits in `q - b i` by induction, so
the sequence fits in `b i + (q - b i) = q` (`CostBoundedBy.bind`). -/
theorem simulate_costBoundedBy {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {impl : QueryImpl spec σ spec'} {cost' : ι' → ℕ} {b : ι → ℕ}
    (himpl : ∀ i x s, OracleComp.CostBoundedBy cost' (impl i x s) (b i))
    {c : OracleComp spec α} {q : ℕ} (hc : OracleComp.CostBoundedBy b c q) (s : σ) :
    OracleComp.CostBoundedBy cost' (simulate impl c s) q := by
  induction c generalizing q s with
  | pure a =>
    rw [simulate_pure]
    exact OracleComp.costBoundedBy_pure cost' (a, s) q
  | query i x k ih =>
    obtain ⟨hi, hk⟩ := (OracleComp.costBoundedBy_query b i x k q).1 hc
    have h := OracleComp.CostBoundedBy.bind (himpl i x s) (fun ys => ih ys.1 (hk ys.1) ys.2)
    rw [Nat.add_sub_cancel' hi] at h
    rw [simulate_query]
    exact h

/-! ### Simulation through a state abstraction -/

/-- **Simulation through an abstraction of the state:** if every call of `impl₁` from the
abstract state `f s` is the call of `impl₂` from `s` with its new state abstracted, the same holds
for whole simulations: `simulate impl₁ c (f s) =
(simulate impl₂ c s).bind fun p => pure (p.1, f p.2)`.

**Proof sketch.** Induction on `c`; at a query, rewrite the call by the hypothesis and use the
induction hypothesis on each continuation after associativity. -/
theorem simulate_eq_of_abs {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {σ₁ σ₂ α : Type} (impl₁ : QueryImpl spec σ₁ spec') (impl₂ : QueryImpl spec σ₂ spec')
    (f : σ₂ → σ₁) (h : ∀ i x s, impl₁ i x (f s) = (impl₂ i x s).bind fun p => .pure (p.1, f p.2))
    (c : OracleComp spec α) (s : σ₂) :
    simulate impl₁ c (f s) = (simulate impl₂ c s).bind fun p => .pure (p.1, f p.2) := by
  induction c generalizing s with
  | pure a => simp only [simulate_pure, OracleComp.pure_bind]
  | query i x k ih =>
    rw [simulate_query, simulate_query, h, OracleComp.bind_assoc, OracleComp.bind_assoc]
    congr 1
    funext p
    rw [OracleComp.pure_bind]
    exact ih p.1 p.2

/-- **Simulation through a state abstraction, along runs with a query budget:** let every call of
`impl₂` from a state `s` with `cnt s < κ` be a deterministic answer `(y, s')` with
`cnt s' ≤ cnt s + 1`, and the call of `impl₁` from `f s` be `(y, f s')`. Then for a computation
`c` with at most `m` queries and `cnt s + m ≤ κ`,
`simulate impl₁ c (f s) = (simulate impl₂ c s).bind fun p => pure (p.1, f p.2)`.

**Proof sketch.** Induction on `c`. A query costs one unit, so it is asked from a state with
`cnt s < κ`; both calls return the same answer, and the continuation runs from `s'` with one unit
less, where `cnt s' + (m - 1) ≤ κ`. -/
theorem simulate_eq_of_abs_bounded {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {σ₁ σ₂ α : Type} (impl₁ : QueryImpl spec σ₁ spec') (impl₂ : QueryImpl spec σ₂ spec')
    (f : σ₂ → σ₁) (cnt : σ₂ → ℕ) (κ : ℕ)
    (h : ∀ i x s, cnt s < κ → ∃ (y : spec.rng i) (s' : σ₂), impl₂ i x s = .pure (y, s') ∧
      cnt s' ≤ cnt s + 1 ∧ impl₁ i x (f s) = .pure (y, f s'))
    (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ₂)
    (hs : cnt s + m ≤ κ) :
    simulate impl₁ c (f s) = (simulate impl₂ c s).bind fun p => .pure (p.1, f p.2) := by
  induction c generalizing m s with
  | pure a => simp only [simulate_pure, OracleComp.pure_bind]
  | query i x k ih =>
    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
    have hm1 : 1 ≤ m := hm
    obtain ⟨y, s', h₂, hcnt, h₁⟩ := h i x s (by omega)
    rw [simulate_query, simulate_query, h₁, h₂, OracleComp.pure_bind, OracleComp.pure_bind]
    exact ih y (m - 1) (hk y) s' (by omega)

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Hopping.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Simulate
import TCSlib.Cryptography.Games.Advantage

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Game hopping

The steps of a game-based security proof, proved once:
- **the difference lemma**: two events that agree unless a "bad" event happens differ in
  probability by at most the probability of the bad event;
- **identical until bad**: two oracle implementations that give the same law to good successors
  until a flag in their state is raised, and never lower it, give simulations whose outputs differ
  in probability by at most the probability that the flag is raised;
- **a collision bound**: one fresh uniform sample lands in a list of at most `q` values fixed
  before it with probability at most `q / |T|`. The adaptive repeated-nonce event of
  [PS10, Thm 168.2] (later nonces hitting an earlier one) is a union of such steps; its lemma is
  scheduled with the statement phase.

The hybrid argument itself is `advantage_hybrid` (`TCSlib.Cryptography.Games.Advantage`).

## Main definitions

* `Games.OracleComp.AllOutputs P c` (in `TCSlib.Cryptography.Games.OracleComp`): every possible
  output of `c` satisfies `P`.

## Main results

* `ProbComp.prob_eq_one_of_allOutputs`, `ProbComp.expect_mono_of_allOutputs`: reasoning on the
  possible outputs only.
* `ProbComp.abs_prob_sub_le_of_agree`: the difference lemma [Sho04, §1.1, Lemma 1].
* `ProbComp.prob_mem_le`: the collision bound; `ProbComp.expect_sample_mem_le`, its form for a
  uniform sample and a fixed list.
* `ProbComp.expect_simulate_congr`: implementations with the same laws simulate alike.
* `ProbComp.prob_bad_le`: the per-query potential bound `Pr[bad] ≤ q · (size + q) · δ`.
* `Games.prob_eq_until_bad`, `Games.identical_until_bad`, `Games.identical_until_bad_init`: the
  code-based fundamental lemma [BR06], in semantic form, from a fixed or a sampled initial
  state; `Games.hagree_of_eq` recovers the syntactic hypothesis.

## References

* [BR06] M. Bellare, P. Rogaway, *The security of triple encryption and a framework for
  code-based game-playing proofs*, EUROCRYPT 2006; full version IACR ePrint 2004/331 (the
  fundamental lemma of game playing).
* [Sho04] V. Shoup, *Sequences of games: a tool for taming complexity in security proofs*,
  IACR ePrint 2004/332, revision of 18 January 2006 (https://www.shoup.net/papers/games.pdf),
  §1.1, Lemma 1 (the difference lemma).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Thm 168.2 (proof sketch: the bad events of the CPA analysis).
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
-/

namespace TCSlib.Cryptography.Games

open Finset

variable {ι : Type} {α β σ : Type}

namespace ProbComp

/-- An event splits by a second event: `Pr[A] = Pr[A ∧ ¬F] + Pr[A ∧ F]`. -/
theorem prob_split (c : ProbComp α) (A F : α → Prop) :
    prob c A = prob c (fun a => A a ∧ ¬ F a) + prob c (fun a => A a ∧ F a) := by
  classical
  rw [prob_eq_expect, prob_eq_expect, prob_eq_expect, ← expect_add]
  congr 1
  funext a
  by_cases hA : A a <;> by_cases hF : F a <;> simp [hA, hF]

/-- If every possible output of `c` satisfies `P`, and `f ≤ g` at every output satisfying `P`,
then the expectation of `f` over `c` is at most that of `g`. -/
theorem expect_mono_of_allOutputs {c : ProbComp α} {P : α → Prop} (hc : c.AllOutputs P)
    {f g : α → ℝ} (h : ∀ a, P a → f a ≤ g a) : expect c f ≤ expect c g := by
  induction c with
  | pure a =>
    rw [expect_pure, expect_pure]
    exact h a (OracleComp.allOutputs_pure.1 hc)
  | query m x k ih =>
    simp only [expect_query]
    exact mul_le_mul_of_nonneg_left
      (sum_le_sum fun j _ => ih j (OracleComp.allOutputs_query.1 hc j)) (by positivity)

/-- An event holding at every possible output has probability one. -/
theorem prob_eq_one_of_allOutputs {c : ProbComp α} {p : α → Prop} (hc : c.AllOutputs p) :
    prob c p = 1 := by
  classical
  refine le_antisymm (prob_le_one c p) ?_
  rw [prob_eq_expect]
  calc (1 : ℝ) = expect c (fun _ => 1) := (expect_const c 1).symm
    _ ≤ _ := expect_mono_of_allOutputs hc fun a ha => by simp [ha]

/-- An event failing at every possible output has probability zero. -/
theorem prob_eq_zero_of_allOutputs {c : ProbComp α} {p : α → Prop}
    (hc : c.AllOutputs fun a => ¬ p a) : prob c p = 0 := by
  have h := prob_not c p
  rw [prob_eq_one_of_allOutputs hc] at h
  linarith

/-- **The difference lemma:** if the events `A` and `B` agree at every output where `F` fails,
their probabilities differ by at most the probability of `F`. [Sho04, §1.1, Lemma 1]

**Proof sketch.** Pointwise, the indicators of `A` and `B` differ by at most the indicator of
`F`; take expectations in both directions (linearity and monotonicity). -/
theorem abs_prob_sub_le_of_agree (c : ProbComp α) {A B F : α → Prop}
    (h : ∀ a, ¬ F a → (A a ↔ B a)) : |prob c A - prob c B| ≤ prob c F := by
  classical
  have key : ∀ (A B : α → Prop), (∀ a, ¬ F a → (A a ↔ B a)) →
      prob c A ≤ prob c B + prob c F := by
    intro A B hAB
    rw [prob_eq_expect, prob_eq_expect, prob_eq_expect, ← expect_add]
    exact expect_mono c fun a => by
      by_cases hF : F a
      · by_cases hA : A a <;> by_cases hB : B a <;> simp [hA, hB, hF]
      · have := hAB a hF
        by_cases hA : A a
        · simp [hA, this.1 hA, hF]
        · simp [hA, hF]; split_ifs <;> norm_num
  rw [abs_le]
  constructor
  · linarith [key B A fun a ha => (h a ha).symm]
  · linarith [key A B h]

/-- **The collision bound:** if every possible output list has length at most `q`, one fresh
uniform element of `T`, drawn after the list, lies in it with probability at most `q / |T|`.
A standard union-bound fact behind the bad events of [PS10, Thm 168.2]'s proof sketch; the
adaptive repeated-nonce event is a union of such steps.

**Proof sketch.** By total probability over the list, it suffices that a fixed list `L` of length
at most `q` is hit with probability `#{t ∈ L} / |T| ≤ q / |T|`; average over the possible lists
with `expect_mono_of_allOutputs`. -/
theorem prob_mem_le {T : Type} [Fintype T] [Nonempty T] [DecidableEq T] (c : ProbComp (List T))
    {q : ℕ} (hc : c.AllOutputs fun L => L.length ≤ q) :
    prob (c.bind fun L => (sample T).bind fun t => .pure (L, t)) (fun p => p.2 ∈ p.1) ≤
      q / Fintype.card T := by
  have hT : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  rw [prob_bind]
  calc expect c (fun L => prob ((sample T).bind fun t => .pure (L, t)) (fun p => p.2 ∈ p.1))
      ≤ expect c (fun _ => (q : ℝ) / Fintype.card T) := by
        refine expect_mono_of_allOutputs hc fun L hL => ?_
        rw [prob_bind, expect_sample]
        have hsum : ∑ t : T, prob (OracleComp.pure (L, t)) (fun p : List T × T => p.2 ∈ p.1) =
            (L.toFinset.card : ℝ) := by
          simp only [prob_pure, Finset.sum_boole]
          congr 2
          ext t
          simp
        rw [hsum, inv_mul_eq_div]
        refine div_le_div_of_nonneg_right ?_ hT.le
        exact_mod_cast (List.toFinset_card_le L).trans hL
    _ = q / Fintype.card T := expect_const c _

end ProbComp

/-- From a bad state, every possible final state of the simulation is bad, when the
implementation never leaves a bad state. -/
theorem simulate_allOutputs_bad {spec : OracleSpec ι} {impl : QueryImpl spec σ unifSpec}
    (bad : σ → Prop) (hstick : ∀ i x s, bad s → (impl i x s).AllOutputs fun ys => bad ys.2)
    (c : OracleComp spec α) {s : σ} (hs : bad s) :
    (simulate impl c s).AllOutputs fun r => bad r.2 := by
  induction c generalizing s with
  | pure a =>
    rw [simulate_pure, OracleComp.allOutputs_pure]
    exact hs
  | query i x k ih =>
    rw [simulate_query]
    exact OracleComp.AllOutputs.bind (hstick i x s hs) fun ys hys => ih ys.1 hys

/-- Splitting an expectation on a predicate: on `b` the function is `1`, elsewhere `f`. -/
private theorem expect_ite_one_split {γ : Type} (c : ProbComp γ) (b : γ → Prop) [DecidablePred b]
    (f : γ → ℝ) :
    ProbComp.expect c (fun y => if b y then 1 else f y) =
      (1 - ProbComp.expect c (fun y => if b y then 0 else 1)) +
        ProbComp.expect c (fun y => if b y then 0 else f y) := by
  have h : (fun y => if b y then (1 : ℝ) else f y) =
      fun y => (1 + (-1) * (if b y then (0 : ℝ) else 1)) + (if b y then 0 else f y) := by
    funext y
    by_cases hy : b y <;> simp [hy]
  rw [h, ProbComp.expect_add c (fun y => 1 + (-1) * (if b y then (0 : ℝ) else 1))
      (fun y => if b y then 0 else f y),
    ProbComp.expect_add c (fun _ => (1 : ℝ)) (fun y => (-1) * (if b y then (0 : ℝ) else 1)),
    ProbComp.expect_const, ProbComp.expect_const_mul]
  ring

/-- **Equal until bad:** let two implementations give, from every good state, the same law to good
successors (they may differ arbitrarily on bad successors, including in the call that makes the
state bad), and let each keep bad states bad. Then, from a good state, the two simulations give
the same probability to "`Q` holds and the final state is good", and the same probability to "the
final state is bad".

**Proof sketch.** Induction on the computation. At a query from a good state, write `F_b` for the
continuation's probability of the event. On a bad successor `F_b` is `0` (for "good at the end")
or `1` (for "bad at the end") on both sides (`simulate_allOutputs_bad`). So each expectation only
depends on `F_b` at good successors, where `F₀ = F₁` by induction; and the two implementations give
good successors the same law (`hagree`, once with `g := F₁` and once with `g := 1`). -/
theorem prob_eq_until_bad {spec : OracleSpec ι} {impl₀ impl₁ : QueryImpl spec σ unifSpec}
    (bad : σ → Prop) [DecidablePred bad]
    (hagree : ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
      ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
        ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys))
    (hstick₀ : ∀ i x s, bad s → (impl₀ i x s).AllOutputs fun ys => bad ys.2)
    (hstick₁ : ∀ i x s, bad s → (impl₁ i x s).AllOutputs fun ys => bad ys.2)
    (c : OracleComp spec α) (Q : α → Prop) {s : σ} (hs : ¬ bad s) :
    ProbComp.prob (simulate impl₀ c s) (fun r => Q r.1 ∧ ¬ bad r.2) =
        ProbComp.prob (simulate impl₁ c s) (fun r => Q r.1 ∧ ¬ bad r.2) ∧
      ProbComp.prob (simulate impl₀ c s) (fun r => bad r.2) =
        ProbComp.prob (simulate impl₁ c s) (fun r => bad r.2) := by
  induction c generalizing s with
  | pure a => simp only [simulate_pure, and_self]
  | query i x k ih =>
    simp only [simulate_query, ProbComp.prob_bind]
    constructor
    · -- "`Q` and good at the end"
      have h0 : ∀ ys : spec.rng i × σ,
          ProbComp.prob (simulate impl₀ (k ys.1) ys.2) (fun r => Q r.1 ∧ ¬ bad r.2) =
            if bad ys.2 then 0 else
              ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => Q r.1 ∧ ¬ bad r.2) := by
        intro ys
        by_cases hb : bad ys.2
        · rw [if_pos hb]
          exact ProbComp.prob_eq_zero_of_allOutputs
            ((simulate_allOutputs_bad bad hstick₀ _ hb).mono fun r hr h => h.2 hr)
        · rw [if_neg hb]
          exact (ih ys.1 hb).1
      have h1 : ∀ ys : spec.rng i × σ,
          ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => Q r.1 ∧ ¬ bad r.2) =
            if bad ys.2 then 0 else
              ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => Q r.1 ∧ ¬ bad r.2) := by
        intro ys
        by_cases hb : bad ys.2
        · rw [if_pos hb]
          exact ProbComp.prob_eq_zero_of_allOutputs
            ((simulate_allOutputs_bad bad hstick₁ _ hb).mono fun r hr h => h.2 hr)
        · rw [if_neg hb]
      rw [funext h0, hagree i x s hs, ← funext h1]
    · -- "bad at the end"
      have h0 : ∀ ys : spec.rng i × σ,
          ProbComp.prob (simulate impl₀ (k ys.1) ys.2) (fun r => bad r.2) =
            if bad ys.2 then 1 else
              ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => bad r.2) := by
        intro ys
        by_cases hb : bad ys.2
        · rw [if_pos hb]
          exact ProbComp.prob_eq_one_of_allOutputs (simulate_allOutputs_bad bad hstick₀ _ hb)
        · rw [if_neg hb]
          exact (ih ys.1 hb).2
      have h1 : ∀ ys : spec.rng i × σ,
          ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => bad r.2) =
            if bad ys.2 then 1 else
              ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => bad r.2) := by
        intro ys
        by_cases hb : bad ys.2
        · rw [if_pos hb]
          exact ProbComp.prob_eq_one_of_allOutputs (simulate_allOutputs_bad bad hstick₁ _ hb)
        · rw [if_neg hb]
      rw [funext h0, expect_ite_one_split, hagree i x s hs (fun _ => 1), hagree i x s hs,
        ← expect_ite_one_split, ← funext h1]

/-- **Identical until bad** (the code-based fundamental lemma): let two implementations of the
same oracles give, from every good state, the same law to good successors, and let each keep `bad`
once it holds (every possible new state of a bad state is bad). Then, from a good state, for any
computation `c` and event `p` on its output, the probabilities of `p` under the two simulations
differ by at most the probability that the first simulation ends in a bad state.
[BR06] (the fundamental lemma)

**Deviation:** [BR06] assumes the two games' code is syntactically identical up to `bad ← true`.
Here the hypothesis is semantic: from a good state the two implementations give the same law to
good successors, and may differ arbitrarily on bad ones, including in the call that raises the
flag. Stickiness is required; without it the bound fails.

**Proof sketch.**
1. *Sticky:* from a bad state, every possible final state of either simulation is bad
   (`simulate_allOutputs_bad`).
2. *Equal until bad:* `prob_eq_until_bad`.
3. Write each probability of `p` as "`p` and good" plus at most "bad", and conclude with the
   difference lemma's arithmetic. -/
theorem identical_until_bad {spec : OracleSpec ι}
    {impl₀ impl₁ : QueryImpl spec σ unifSpec} (bad : σ → Prop) [DecidablePred bad]
    (hagree : ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
      ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
        ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys))
    (hstick₀ : ∀ i x s, bad s → (impl₀ i x s).AllOutputs fun ys => bad ys.2)
    (hstick₁ : ∀ i x s, bad s → (impl₁ i x s).AllOutputs fun ys => bad ys.2)
    (c : OracleComp spec α) (p : α → Prop) {s : σ} (hs : ¬ bad s) :
    |ProbComp.prob (simulate impl₀ c s) (fun r => p r.1) -
        ProbComp.prob (simulate impl₁ c s) (fun r => p r.1)| ≤
      ProbComp.prob (simulate impl₀ c s) (fun r => bad r.2) := by
  obtain ⟨h1, h2⟩ := prob_eq_until_bad bad hagree hstick₀ hstick₁ c p hs
  rw [ProbComp.prob_split (simulate impl₀ c s) (fun r => p r.1) (fun r => bad r.2),
    ProbComp.prob_split (simulate impl₁ c s) (fun r => p r.1) (fun r => bad r.2), h1]
  have a0 := ProbComp.prob_nonneg (simulate impl₀ c s) (fun r => p r.1 ∧ bad r.2)
  have a1 := ProbComp.prob_nonneg (simulate impl₁ c s) (fun r => p r.1 ∧ bad r.2)
  have b0 := ProbComp.prob_mono (simulate impl₀ c s) (p := fun r => p r.1 ∧ bad r.2)
    (q := fun r => bad r.2) fun r h => h.2
  have b1 := ProbComp.prob_mono (simulate impl₁ c s) (p := fun r => p r.1 ∧ bad r.2)
    (q := fun r => bad r.2) fun r h => h.2
  rw [abs_le]
  constructor <;> linarith

/-- Equal implementations on good states give the same law to good successors: the hypothesis of
`identical_until_bad` in its syntactic form. -/
theorem hagree_of_eq {spec : OracleSpec ι} {impl₀ impl₁ : QueryImpl spec σ unifSpec}
    (bad : σ → Prop) [DecidablePred bad] (h : ∀ i x s, ¬ bad s → impl₀ i x s = impl₁ i x s) :
    ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
      ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
        ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys) :=
  fun i x s hs _ => by rw [h i x s hs]

/-- **Identical until bad, from a sampled initial state:** if every possible initial state is
good, the bound of `identical_until_bad` holds for the games that first sample the state.

**Proof sketch.** Total probability over the initial state, the pointwise bound at every possible
(good) initial state (`identical_until_bad`), and monotonicity and linearity of expectation. -/
theorem identical_until_bad_init {spec : OracleSpec ι}
    {impl₀ impl₁ : QueryImpl spec σ unifSpec} (bad : σ → Prop) [DecidablePred bad]
    (hagree : ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
      ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
        ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys))
    (hstick₀ : ∀ i x s, bad s → (impl₀ i x s).AllOutputs fun ys => bad ys.2)
    (hstick₁ : ∀ i x s, bad s → (impl₁ i x s).AllOutputs fun ys => bad ys.2)
    (c : OracleComp spec α) (p : α → Prop) (init : ProbComp σ)
    (hinit : init.AllOutputs fun s => ¬ bad s) :
    |ProbComp.prob (init.bind fun s => simulate impl₀ c s) (fun r => p r.1) -
        ProbComp.prob (init.bind fun s => simulate impl₁ c s) (fun r => p r.1)| ≤
      ProbComp.prob (init.bind fun s => simulate impl₀ c s) (fun r => bad r.2) := by
  rw [ProbComp.prob_bind, ProbComp.prob_bind, ProbComp.prob_bind]
  have key := fun s (hs : ¬ bad s) =>
    abs_le.1 (identical_until_bad bad hagree hstick₀ hstick₁ c p hs)
  have u := ProbComp.expect_mono_of_allOutputs hinit
    (f := fun s => ProbComp.prob (simulate impl₀ c s) (fun r => p r.1))
    (g := fun s => ProbComp.prob (simulate impl₁ c s) (fun r => p r.1) +
      ProbComp.prob (simulate impl₀ c s) (fun r => bad r.2))
    (fun s hs => by linarith [(key s hs).2])
  have v := ProbComp.expect_mono_of_allOutputs hinit
    (f := fun s => ProbComp.prob (simulate impl₁ c s) (fun r => p r.1))
    (g := fun s => ProbComp.prob (simulate impl₀ c s) (fun r => p r.1) +
      ProbComp.prob (simulate impl₀ c s) (fun r => bad r.2))
    (fun s hs => by linarith [(key s hs).1])
  rw [ProbComp.expect_add] at u v
  rw [abs_le]
  constructor <;> linarith

namespace ProbComp

/-! ### Simulation congruence and a bad-event potential -/

/-- **Implementations with the same laws simulate alike:** if every call of `impl₀` and `impl₁`
has the same expectation of every function `g` of the answer and the new state, the simulations
of every computation have the same expectation of every function `G` of the output and the final
state: `𝔼[G] (simulate impl₀ c s) = 𝔼[G] (simulate impl₁ c s)`.

**Proof sketch.** Induction on `c`; at a query, both sides are the expectation over the call of the
continuation's expectation (`simulate_query`, `expect_bind`), equal by induction and the
hypothesis. -/
theorem expect_simulate_congr {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (impl₀ impl₁ : QueryImpl spec σ unifSpec)
    (h : ∀ i x s (g : spec.rng i × σ → ℝ), expect (impl₀ i x s) g = expect (impl₁ i x s) g)
    (c : OracleComp spec α) (s : σ) (G : α × σ → ℝ) :
    expect (simulate impl₀ c s) G = expect (simulate impl₁ c s) G := by
  induction c generalizing s with
  | pure a => rw [simulate_pure, simulate_pure]
  | query i x k ih =>
    rw [simulate_query, simulate_query, expect_bind, expect_bind, h]
    exact congrArg _ (funext fun p => ih p.1 p.2)

/-- **A bad event raised a little at each query:** if from a good state each query raises `bad`
with probability at most `(sz s + 1) · δ` and grows the size `sz` by at most one, then from a good
state `s` a computation making at most `m` queries ends in a bad state with probability at most
`m · (sz s + m) · δ`: `Pr[bad (simulate impl c s).2] ≤ m · (sz s + m) · δ`.

**Proof sketch.** Induction on the computation. At a query, a bad successor contributes at most
its probability; a good successor `s'` has `sz s' ≤ sz s + 1` and, by induction, contributes at
most `(m - 1) · (sz s + m) · δ`. Add `(sz s + 1) · δ ≤ (sz s + m) · δ`. -/
theorem prob_bad_le {ι : Type} {spec : OracleSpec ι} {σ : Type} {impl : QueryImpl spec σ unifSpec}
    (bad : σ → Prop) [DecidablePred bad]
    (sz : σ → ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hstep : ∀ i x s, ¬ bad s → prob (impl i x s) (fun ys => bad ys.2) ≤ (sz s + 1) * δ)
    (hgrow : ∀ i x s, (impl i x s).AllOutputs fun ys => sz ys.2 ≤ sz s + 1)
    {α : Type} (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ)
    (hs : ¬ bad s) :
    prob (simulate impl c s) (fun r => bad r.2) ≤ m * (sz s + m) * δ := by
  induction c generalizing m s with
  | pure a =>
    rw [simulate_pure, prob_pure, if_neg hs]
    exact mul_nonneg (by positivity) hδ
  | query i x k ih =>
    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
    have hm1 : 1 ≤ m := hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hk' : ∀ y, (k y).CostBoundedBy (fun _ => 1) m' := fun y => by
      simpa using hk y
    have hm0 : (0 : ℝ) ≤ m' := Nat.cast_nonneg m'
    set K : ℝ := m' * (sz s + (m' + 1)) * δ with hK
    have hK0 : 0 ≤ K := mul_nonneg (by positivity) hδ
    rw [simulate_query, prob_bind]
    calc expect (impl i x s) (fun ys => prob (simulate impl (k ys.1) ys.2) (fun r => bad r.2))
        ≤ expect (impl i x s) (fun ys => (if bad ys.2 then (1 : ℝ) else 0) + K) := by
          refine expect_mono_of_allOutputs (hgrow i x s) fun ys hys => ?_
          by_cases hb : bad ys.2
          · rw [if_pos hb]
            have h1 := prob_le_one (simulate impl (k ys.1) ys.2) (fun r => bad r.2)
            linarith
          · rw [if_neg hb, zero_add]
            refine (ih ys.1 m' (hk' ys.1) ys.2 hb).trans ?_
            have hys' : (sz ys.2 : ℝ) ≤ sz s + 1 := by exact_mod_cast hys
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hm0) hδ
      _ = prob (impl i x s) (fun ys => bad ys.2) + K := by
          rw [expect_add (impl i x s) (fun ys => if bad ys.2 then (1 : ℝ) else 0) (fun _ => K),
            expect_const, prob_eq_expect]
      _ ≤ ((m' + 1 : ℕ) : ℝ) * (sz s + ((m' + 1 : ℕ) : ℝ)) * δ := by
          have h3 := hstep i x s hs
          have h4 : ((sz s : ℝ) + 1) * δ ≤ (sz s + (m' + 1)) * δ :=
            mul_le_mul_of_nonneg_right (by linarith) hδ
          have e : ((m' : ℝ) + 1) * (sz s + (m' + 1)) * δ = K + (sz s + (m' + 1)) * δ := by
            rw [hK]; ring
          push_cast
          linarith

/-- **Hitting a list with a uniform sample:** a uniform element of `T` lies in a list `L` with
probability at most `|L| / |T|`: `𝔼_{t ← T} [t ∈ L] ≤ |L| / |T|` (`prob_mem_le` for a fixed
list). -/
theorem expect_sample_mem_le {T : Type} [Fintype T] [Nonempty T] [DecidableEq T] (L : List T) :
    expect (sample T) (fun t => if t ∈ L then (1 : ℝ) else 0) ≤ L.length / Fintype.card T := by
  have h := prob_mem_le (OracleComp.pure L : ProbComp (List T)) (q := L.length)
    (OracleComp.allOutputs_pure.2 le_rfl)
  rw [prob_bind, expect_pure, prob_bind] at h
  refine Eq.trans_le ?_ h
  refine congrArg _ (funext fun t => ?_)
  rw [prob_pure]

end ProbComp

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/BitCodec.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Machines
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Games.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bit-string oracles and their machine codec

The security games of [PS10] ch. 5–8 give machine adversaries a finite family of oracles on
fixed-length bit strings: a tagging oracle, a signing oracle, encryption and decryption oracles,
and so on. At parameter `n` oracle `i` takes `din i` bits and answers with `dout i` bits
(`bitSpec`). This file fixes the codec through which a next-move machine (`NUPPT.toComp`) plays
against such a family, and through which it returns a fixed-length output (`bitCodec`):
- **a query** to oracle `i` on `x` is the output `⟨[false], ⟨1^i, x⟩⟩`;
- **a final output** `a` is `⟨[true], a⟩`;
- **anything else**, a malformed or wrong-length string, decodes to the all-`false` output (the
  ch. 2–4 layer's convention D7: ill-formed outputs count as a fixed default);
- **a log entry** `(i, x, y)` is encoded as `⟨1^i, ⟨x, y⟩⟩`;
- **when the query budget runs out**, the output is the all-`false` string.

It is the shared codec of every prong's statements, and the T0 definitions of the efficiency fill
(`briefs/pass-shelat-ch5-8/fills/efficiency/`).

## Main definitions

* `Games.bitSpec din dout`: `k` oracles on fixed-length bit strings.
* `Games.decodeIdx`, `Games.decodeBitMove`: decoding of an oracle index and of a machine output as
  a move.
* `Games.encodeBitMove`: the canonical word of a move.
* `Games.bitCodec din dout dα`: the codec.
* `Games.castImpl`: an implementation of bit-string oracles read along equal length functions.

## Main results

* `Games.decodeIdx_replicate`, `Games.decodeBitMove_query`, `Games.decodeBitMove_ret`: the
  well-formed encodings decode as intended.
* `Games.decodeIdx_eq_some_iff`, `Games.decodeBitMove_eq_query_iff`: only the canonical words
  decode as an index or a query.
* `Games.decodeBitMove_of_not_canonical`: every other word decodes to the all-`false` output.
* `Games.padFin_ofFn_zeroBits`, `Games.padFin_replicate_false`, `Games.padFin_nil`,
  `Games.decodeFin_nil_getD`: all-`false` strings and the empty answer read as `zeroBits`.
* `Games.simulate_castImpl_toCompOn`, `Games.expect_simulate_castImpl_toCompOn`: transport of a
  machine's run between two codecs with equal lengths.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.8.1 (oracle machines) and Definitions 134.2, 136.2 and 168.1 (oracle adversaries).
-/

namespace TCSlib.Cryptography.Games

open Complexity Turing

variable {k : ℕ}

/-- **`k` oracles on fixed-length bit strings:** oracle `i` takes `din i` bits and answers with
`dout i` bits. -/
abbrev bitSpec (din dout : Fin k → ℕ) : OracleSpec (Fin k) :=
  ⟨fun i => Fin (din i) → Bool, fun i => Fin (dout i) → Bool⟩

/-- Oracle `i` of `bitSpec din dout` takes `din i`-bit strings. -/
theorem bitSpec_dom (din dout : Fin k → ℕ) (i : Fin k) :
    (bitSpec din dout).dom i = (Fin (din i) → Bool) :=
  rfl

/-- Oracle `i` of `bitSpec din dout` answers with `dout i`-bit strings. -/
theorem bitSpec_rng (din dout : Fin k → ℕ) (i : Fin k) :
    (bitSpec din dout).rng i = (Fin (dout i) → Bool) :=
  rfl

/-- Decoding of an oracle index written in unary: `1^i` with `i < k` is `i`; every other word
(one containing `false`, or of length at least `k`) is `none`. -/
def decodeIdx (k : ℕ) (iw : List Bool) : Option (Fin k) :=
  if h : iw.length < k ∧ iw = List.replicate iw.length true then some ⟨iw.length, h.1⟩ else none

/-- The unary code of an index decodes to it. -/
theorem decodeIdx_replicate (i : Fin k) : decodeIdx k (List.replicate i true) = some i := by
  unfold decodeIdx
  have h : (List.replicate (i : ℕ) true).length < k ∧
      List.replicate (i : ℕ) true =
        List.replicate (List.replicate (i : ℕ) true).length true := by
    simp
  rw [dif_pos h]
  exact congrArg some (Fin.ext (by simp))

/-- **Exactly the unary codes decode**, each to its index:
`decodeIdx k iw = some i ↔ iw = 1^i`. -/
theorem decodeIdx_eq_some_iff {iw : List Bool} {i : Fin k} :
    decodeIdx k iw = some i ↔ iw = List.replicate i true := by
  refine ⟨fun h => ?_, fun h => h ▸ decodeIdx_replicate i⟩
  unfold decodeIdx at h
  split_ifs at h with hw
  rw [Option.some.injEq] at h
  rw [← h]
  exact hw.2

/-- **Every other word is rejected:** `decodeIdx k iw = none` exactly when `iw` is the unary code
of no index below `k`. -/
theorem decodeIdx_eq_none_iff {iw : List Bool} :
    decodeIdx k iw = none ↔ ∀ i : Fin k, iw ≠ List.replicate i true := by
  constructor
  · intro h i hi
    rw [decodeIdx_eq_some_iff.2 hi] at h
    exact Option.some_ne_none i h
  · intro h
    cases hd : decodeIdx k iw with
    | none => rfl
    | some i => exact absurd (decodeIdx_eq_some_iff.1 hd) (h i)

/-- The default output: the all-`false` string. -/
def zeroBits (d : ℕ) : Fin d → Bool := fun _ => false

/-- Every bit of the default output is `false`: `zeroBits d j = false`. -/
theorem zeroBits_apply (d : ℕ) (j : Fin d) : zeroBits d j = false :=
  rfl

/-- The default output, written as a string, is `d` copies of `false`:
`List.ofFn (zeroBits d) = List.replicate d false`. -/
theorem ofFn_zeroBits (d : ℕ) : List.ofFn (zeroBits d) = List.replicate d false := by
  rw [show zeroBits d = fun _ => false from rfl, List.ofFn_const]

/-- The all-`false` answer, read at any width, is all-`false`:
`padFin d ⟦zeroBits m⟧ = zeroBits d`. -/
theorem padFin_ofFn_zeroBits (d m : ℕ) : padFin d (List.ofFn (zeroBits m)) = zeroBits d := by
  funext i
  rw [padFin_apply, ofFn_zeroBits, zeroBits_apply, List.getD_eq_getElem?_getD,
    List.getElem?_replicate]
  split <;> rfl

/-- An all-`false` list reads as the all-`false` vector at every width:
`padFin d (List.replicate m false) = zeroBits d`. -/
theorem padFin_replicate_false (d m : ℕ) : padFin d (List.replicate m false) = zeroBits d := by
  rw [← ofFn_zeroBits, padFin_ofFn_zeroBits]

/-- The empty list reads as the all-`false` vector: `padFin d [] = zeroBits d`. -/
theorem padFin_nil (d : ℕ) : padFin d [] = zeroBits d := padFin_replicate_false d 0

/-- An empty answer decodes to all-`false` at every length:
`(decodeFin ℓ []).getD (zeroBits ℓ) = zeroBits ℓ`. -/
theorem decodeFin_nil_getD (ℓ : ℕ) : (decodeFin ℓ []).getD (zeroBits ℓ) = zeroBits ℓ := by
  rw [decodeFin_eq]
  split
  · next h =>
    subst h
    funext i
    exact absurd i.isLt (Nat.not_lt_zero _)
  · rfl

/-- Decoding of a machine output as a move against `bitSpec din dout` with `dα`-bit outputs:
`⟨[false], ⟨1^i, x⟩⟩` with `i < k` and `|x| = din i` is the query `x` to oracle `i`;
`⟨[true], a⟩` with `|a| = dα` is the output `a`; anything else is the output `zeroBits dα`. -/
def decodeBitMove (din dout : Fin k → ℕ) (dα : ℕ) (w : List Bool) :
    Move (bitSpec din dout) (Fin dα → Bool) :=
  match pairDecode w with
  | some ([false], rest) =>
    match pairDecode rest with
    | some (iw, xw) =>
      match decodeIdx k iw with
      | some i =>
        match decodeFin (din i) xw with
        | some x => .query i x
        | none => .ret (zeroBits dα)
      | none => .ret (zeroBits dα)
    | none => .ret (zeroBits dα)
  | some ([true], aw) =>
    match decodeFin dα aw with
    | some a => .ret a
    | none => .ret (zeroBits dα)
  | _ => .ret (zeroBits dα)

/-- **The canonical word of a move:** the query `x` to oracle `i` is `⟨[false], ⟨1^i, x⟩⟩`, and
the output `a` is `⟨[true], a⟩`. `decodeBitMove` inverts it (`decodeBitMove_encodeBitMove`). -/
def encodeBitMove (din dout : Fin k → ℕ) (dα : ℕ) :
    Move (bitSpec din dout) (Fin dα → Bool) → List Bool
  | .query i x => pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x))
  | .ret a => pairEncode [true] (List.ofFn a)

/-- The canonical word of a query:
`encodeBitMove din dout dα (query i x) = ⟨[false], ⟨1^i, x⟩⟩`. -/
theorem encodeBitMove_query (din dout : Fin k → ℕ) (dα : ℕ) (i : Fin k)
    (x : Fin (din i) → Bool) :
    encodeBitMove din dout dα (.query i x) =
      pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x)) :=
  rfl

/-- The canonical word of an output: `encodeBitMove din dout dα (ret a) = ⟨[true], a⟩`. -/
theorem encodeBitMove_ret (din dout : Fin k → ℕ) (dα : ℕ) (a : Fin dα → Bool) :
    encodeBitMove din dout dα (.ret a) = pairEncode [true] (List.ofFn a) :=
  rfl

/-- **The codec of bit-string oracles:** moves decoded by `decodeBitMove`, a log entry
`(i, x, y)` encoded as `⟨1^i, ⟨x, y⟩⟩`, and the all-`false` output when the budget runs out. -/
def bitCodec (din dout : Fin k → ℕ) (dα : ℕ) :
    MachineCodec (bitSpec din dout) (Fin dα → Bool) where
  decodeMove := decodeBitMove din dout dα
  encodeEntry e :=
    pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2))
  timeout := zeroBits dα

/-- The codec decodes moves with `decodeBitMove`: `(bitCodec din dout dα).decodeMove w =
decodeBitMove din dout dα w`. -/
theorem bitCodec_decodeMove (din dout : Fin k → ℕ) (dα : ℕ) (w : List Bool) :
    (bitCodec din dout dα).decodeMove w = decodeBitMove din dout dα w :=
  rfl

/-- The codec encodes the log entry `(i, x, y)` as `⟨1^i, ⟨x, y⟩⟩`. -/
theorem bitCodec_encodeEntry (din dout : Fin k → ℕ) (dα : ℕ)
    (e : Σ i, (bitSpec din dout).dom i × (bitSpec din dout).rng i) :
    (bitCodec din dout dα).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  rfl

/-- When the budget runs out, the codec's output is all-`false`:
`(bitCodec din dout dα).timeout = zeroBits dα`. -/
theorem bitCodec_timeout (din dout : Fin k → ℕ) (dα : ℕ) :
    (bitCodec din dout dα).timeout = zeroBits dα :=
  rfl

/-- The codec's log encoding does not depend on the output length: `bitCodec din dout dα` and
`bitCodec din dout dα'` encode every log alike. -/
theorem encodeLog_bitCodec (din dout : Fin k → ℕ) (dα dα' : ℕ) (h : QueryLog (bitSpec din dout)) :
    (bitCodec din dout dα).encodeLog h = (bitCodec din dout dα').encodeLog h := by
  induction h with
  | nil => rw [MachineCodec.encodeLog_nil, MachineCodec.encodeLog_nil]
  | cons e h ih =>
    rw [MachineCodec.encodeLog_cons, MachineCodec.encodeLog_cons, ih, bitCodec_encodeEntry,
      bitCodec_encodeEntry]

/-- A well-formed query decodes as the query. -/
theorem decodeBitMove_query (din dout : Fin k → ℕ) (dα : ℕ) (i : Fin k)
    (x : Fin (din i) → Bool) :
    decodeBitMove din dout dα
        (pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x))) = .query i x := by
  simp [decodeBitMove, pairDecode_pairEncode, decodeIdx_replicate, decodeFin_ofFn]

/-- A well-formed output decodes as the output. -/
theorem decodeBitMove_ret (din dout : Fin k → ℕ) (dα : ℕ) (a : Fin dα → Bool) :
    decodeBitMove din dout dα (pairEncode [true] (List.ofFn a)) = .ret a := by
  simp [decodeBitMove, pairDecode_pairEncode, decodeFin_ofFn]

/-- **Only the canonical query word decodes as a query:** `decodeBitMove din dout dα w` is the
query `x` to oracle `i` exactly when `w = ⟨[false], ⟨1^i, x⟩⟩` (the converse of
`decodeBitMove_query`).

**Proof sketch.** Follow `decodeBitMove`'s branches: only the branch in which the tag is `[false]`,
the rest parses as a pair, the index word decodes and the payload has the right length returns a
query. There, each successful parse determines its input: a parsed pair is the pairing of its parts
(`eq_pairEncode_of_pairDecode`), a decoded index word is `1^i` (`decodeIdx_eq_some_iff`), and a
decoded payload is `List.ofFn x`. -/
theorem decodeBitMove_eq_query_iff {din dout : Fin k → ℕ} {dα : ℕ} {w : List Bool} {i : Fin k}
    {x : Fin (din i) → Bool} :
    decodeBitMove din dout dα w = .query i x ↔
      w = pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x)) := by
  refine ⟨fun h => ?_, fun h => h ▸ decodeBitMove_query din dout dα i x⟩
  unfold decodeBitMove at h
  split at h
  · rename_i rest hw
    split at h
    · rename_i iw xw hr
      split at h
      · rename_i j hj
        split at h
        · rename_i x' hx
          cases h
          rw [eq_pairEncode_of_pairDecode _ _ _ hw, eq_pairEncode_of_pairDecode _ _ _ hr,
            decodeIdx_eq_some_iff.1 hj, (decodeFin_eq_some_iff _ _ _).1 hx]
        · cases h
      · cases h
    · cases h
  · split at h <;> cases h
  · cases h

/-- **The default:** a word that is neither a canonical query `⟨[false], ⟨1^i, x⟩⟩` nor a
canonical output `⟨[true], a⟩` decodes to the output `zeroBits dα`. With `decodeBitMove_query`
and `decodeBitMove_ret` this determines `decodeBitMove` on every word.

**Proof sketch.** Follow `decodeBitMove`'s branches. Every branch but two returns `zeroBits dα`.
In the query branch, the successful parses make `w` a canonical query word, as in
`decodeBitMove_eq_query_iff`, against `hq`; in the output branch, they make `w` a canonical output
word, against `hr`. -/
theorem decodeBitMove_of_not_canonical {din dout : Fin k → ℕ} {dα : ℕ} {w : List Bool}
    (hq : ∀ (i : Fin k) (x : Fin (din i) → Bool),
      w ≠ pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x)))
    (hr : ∀ a : Fin dα → Bool, w ≠ pairEncode [true] (List.ofFn a)) :
    decodeBitMove din dout dα w = .ret (zeroBits dα) := by
  unfold decodeBitMove
  split
  · rename_i rest hw
    split
    · rename_i iw xw hr'
      split
      · rename_i j hj
        split
        · rename_i x hx
          refine absurd ?_ (hq j x)
          rw [eq_pairEncode_of_pairDecode _ _ _ hw, eq_pairEncode_of_pairDecode _ _ _ hr',
            decodeIdx_eq_some_iff.1 hj, (decodeFin_eq_some_iff _ _ _).1 hx]
        · rfl
      · rfl
    · rfl
  · rename_i aw hw
    split
    · rename_i a ha
      refine absurd ?_ (hr a)
      rw [eq_pairEncode_of_pairDecode _ _ _ hw, (decodeFin_eq_some_iff _ _ _).1 ha]
    · rfl
  · rfl

/-- **Canonical words decode to their move:** `decodeBitMove (encodeBitMove m) = m`. -/
theorem decodeBitMove_encodeBitMove (din dout : Fin k → ℕ) (dα : ℕ)
    (m : Move (bitSpec din dout) (Fin dα → Bool)) :
    decodeBitMove din dout dα (encodeBitMove din dout dα m) = m := by
  cases m with
  | query i x => exact decodeBitMove_query din dout dα i x
  | ret a => exact decodeBitMove_ret din dout dα a

/-- Distinct moves have distinct canonical words. -/
theorem encodeBitMove_injective (din dout : Fin k → ℕ) (dα : ℕ) :
    Function.Injective (encodeBitMove din dout dα) := fun m m' h => by
  rw [← decodeBitMove_encodeBitMove din dout dα m, h, decodeBitMove_encodeBitMove]

/-! ### Transport along equal lengths -/

section Transport

open ProbComp

variable {σ : Type}

/-- **An implementation read along length functions:** answer the query `x` to oracle `i` of
`bitSpec ins outs` by asking `O` the query `padFin (ins' i) ⟦x⟧` and reading its answer `y` as
`padFin (outs i) ⟦y⟧`. When `ins = ins'` and `outs = outs'` this is `O` itself
(`castImpl_self`). -/
def castImpl {ins ins' outs outs' : Fin k → ℕ} (O : QueryImpl (bitSpec ins' outs') σ unifSpec) :
    QueryImpl (bitSpec ins outs) σ unifSpec :=
  fun i x s => (O i (padFin (ins' i) (List.ofFn x)) s).bind fun p =>
    .pure (padFin (outs i) (List.ofFn p.1), p.2)

/-- The defining equation of `castImpl`: `castImpl O i x s =
(O i (padFin (ins' i) ⟦x⟧) s).bind fun p => pure (padFin (outs i) ⟦p.1⟧, p.2)`. -/
theorem castImpl_eq {ins ins' outs outs' : Fin k → ℕ}
    (O : QueryImpl (bitSpec ins' outs') σ unifSpec) (i : Fin k) (x : Fin (ins i) → Bool)
    (s : σ) :
    castImpl (ins := ins) (outs := outs) O i x s =
      (O i (padFin (ins' i) (List.ofFn x)) s).bind fun p =>
        .pure (padFin (outs i) (List.ofFn p.1), p.2) :=
  rfl

/-- Read along the same lengths, an implementation is unchanged: `castImpl O = O`. -/
theorem castImpl_self {ins outs : Fin k → ℕ} (O : QueryImpl (bitSpec ins outs) σ unifSpec) :
    castImpl (ins := ins) (outs := outs) O = O := by
  funext i x s
  rw [castImpl_eq, padFin_ofFn]
  simp only [padFin_ofFn]
  exact OracleComp.bind_pure _

/-- **Transport of a machine's run:** if `ins = ins'`, `outs = outs'` and `d = d'`, simulating
`castImpl O` on the run of `M` through `bitCodec ins outs d` gives, with outputs read as lists,
the simulation of `O` on the run of `M` through `bitCodec ins' outs' d'`.

**Proof sketch.** Substitute the equalities; then `castImpl O = O` (`castImpl_self`). -/
theorem simulate_castImpl_toCompOn {ins ins' outs outs' : Fin k → ℕ} {d d' : ℕ}
    (hi : ins = ins') (ho : outs = outs') (hd : d = d')
    (O : QueryImpl (bitSpec ins' outs') σ unifSpec) (M : NUPPT) (n q : ℕ) (x : List Bool)
    (r : M.Coins n) (s : σ) :
    (simulate (castImpl (ins := ins) (outs := outs) O)
        (M.toCompOn (bitCodec ins outs d) n q x r) s).bind
        (fun p => .pure (List.ofFn p.1, p.2)) =
      (simulate O (M.toCompOn (bitCodec ins' outs' d') n q x r) s).bind
        (fun p => .pure (List.ofFn p.1, p.2)) := by
  subst hi ho hd
  rw [castImpl_self]

/-- **Transport of a machine's run, in expectation:** for every function `G` of the output (read
as a list) and the final state, `simulate_castImpl_toCompOn` in the form
`𝔼[G (⟦p.1⟧, p.2)]` over the two simulations. -/
theorem expect_simulate_castImpl_toCompOn {ins ins' outs outs' : Fin k → ℕ} {d d' : ℕ}
    (hi : ins = ins') (ho : outs = outs') (hd : d = d')
    (O : QueryImpl (bitSpec ins' outs') σ unifSpec) (M : NUPPT) (n q : ℕ) (x : List Bool)
    (r : M.Coins n) (s : σ) (G : List Bool × σ → ℝ) :
    expect (simulate (castImpl (ins := ins) (outs := outs) O)
        (M.toCompOn (bitCodec ins outs d) n q x r) s) (fun p => G (List.ofFn p.1, p.2)) =
      expect (simulate O (M.toCompOn (bitCodec ins' outs' d') n q x r) s)
        (fun p => G (List.ofFn p.1, p.2)) := by
  have h := congrArg (fun c => expect c G) (simulate_castImpl_toCompOn hi ho hd O M n q x r s)
  simp only [expect_bind, expect_pure] at h
  exact h

end Transport

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Efficiency.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Probability
import TCSlib.Cryptography.Games.Bridges.Machines
import TCSlib.Cryptography.Games.Efficiency.Strings
import TCSlib.Cryptography.Games.Efficiency.Replay
import TCSlib.Cryptography.Games.Efficiency.Handler
import TCSlib.Cryptography.Games.Efficiency.OracleBridge
import TCSlib.Cryptography.Games.Efficiency.Interactive
import TCSlib.Cryptography.Games.Efficiency.InteractiveSpec

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The efficiency of reductions

A reduction runs a machine adversary `A` and answers `A`'s queries with a polynomial-time
**handler**. Proved once, the targets below say that the result is again a machine, so the
hardness assumptions, which quantify over machines (`Complexity.NUPPT`), apply to it. The route is
`briefs/pass-shelat-ch5-8/design/S2b-efficiency.md`. The template is Frederick Dehmel's GGM
reduction machine (`Asymptotic/GGMReduction*.lean`), whose loop `GGMRed.stateLoopFun` is reused.

**Status: proved.** The definitions (T0) are final. The statements of T1, T2 and T4 and of the
companion `exists_toCompOn_of_toComp` were frozen at the issue of the fill brief
(`briefs/pass-shelat-ch5-8/fills/efficiency/`); the efficiency fill (`s2b-efficiency`) proved them,
with the helper modules below (namespace `TCSlib.Cryptography.Games.EffFill`).

## Contents

* `Games.Efficiency.Strings`: the string layer (log append, fixed-length decoding, the canonical
  decoder, the activation loop over `GGMRed.stateLoopFun`, the machine glue).
* `Games.Efficiency.Replay`: replaying a computation with a next-move function; cost scaling.
* `Games.Efficiency.Handler`: the machine of a non-interactive handler (T1).
* `Games.Efficiency.OracleBridge`: the translators to next-query machines (T4).
* `Games.Efficiency.Interactive`: the replay machine of an interactive handler (T2).
* `Games.Efficiency.InteractiveSpec`: its functional equation (T2).

## The shape of a reduction

A handler describes everything a reduction does around one run of the adversary. At parameter
`n` the reduction has an input `z` and a seed `ω` (its own coins). Every function of the handler
reads them from the **context** `⟨1^n, ⟨z, ω⟩⟩` (`seedIn`):
1. **the adversary's input** is a polynomial-time function of the context (`advIn`), for example
   a public key built from `z` and `ω`; the adversary runs as `A.toCompOn` on it;
2. **each query** of the adversary is answered from the handler's state, by the handler alone
   (`PolyHandler`) or with queries to the reduction's own oracles (`InteractiveHandler`);
3. **the reduction's output** is computed from the context, the final state and the adversary's
   output: by a polynomial-time function (`PolyHandler.out`), or by a last phase that may itself
   query the reduction's oracles, within its own budget (`InteractiveHandler.finish`).

## Fixed lengths

Every length is an explicit polynomial in the parameter `n`: queries and answers (`din i`,
`dout i`), the adversary's output (`dα`), the handler's state and seed, and, for an interactive
handler, the reduction's output. This bounds every history, which the guarded state loop needs.

## Scope

* **Covered:** a reduction that runs one adversary once, on an input computed from its own,
  answers the adversary's queries with or without its own oracles, and post-processes the final
  state and the adversary's output (with further oracle queries if it is interactive). T1 makes
  the machine's output exactly the finalized output; T2 makes the machine's computation exactly
  the simulation followed by the finalization, with the budgets added.
* **Adversaries without input** are adversaries with an input they ignore
  (`exists_toCompOn_of_toComp`).
* **Reductions to a pseudorandom function** reach `OracleEnsemble.Indist` through T4: an oracle
  machine against one bit-string oracle with a one-bit output is, on evaluations, a next-query
  machine of the ch. 2–4 layer (`NUPPT.toOracleAdversary`).
* **Non-uniform handlers** (for example one that runs a non-uniform distinguisher) receive their
  advice through the input `z`; it is hard-wired into the machine afterwards
  (`NUPPT.exists_withAdvice`, with `NUPPT.exists_comp` to re-pair the input).
* **Not covered:** reductions that rewind the adversary or run it more than once, and variable
  lengths.

## Main definitions

* `Games.seedIn n z ω`: the context `⟨1^n, ⟨z, ω⟩⟩`.
* `Games.PolyHandler k din dout`: a polynomial-time handler for `k` bit-string oracles, with its
  state and seed lengths, initial state, adversary input and finalization.
* `Games.PolyHandler.answer`, `Games.PolyHandler.impl`: its answers, and its semantics as a
  stateful `QueryImpl` that asks no oracle, at parameter `n`, reduction input `z` and seed `ω`;
  `PolyHandler.advInput` and `PolyHandler.result`: the adversary's input and the reduction's
  output.
* `Games.InteractiveHandler`, `InteractiveHandler.call`, `InteractiveHandler.impl`: a
  polynomial-time handler that may itself query outer bit-string oracles, up to `perCall(n)`
  times per inner query, and its semantics as a `QueryImpl` of the inner oracles by the outer ones;
  `InteractiveHandler.advInput` and `InteractiveHandler.finish`: the adversary's input and the
  finalization, with up to `finCall(n)` outer queries.
* `Games.InteractiveHandler.rU`, `rZ`, `rW`, `rS`, `rI`, `rX`, `rL`, `rCnt`: the fields of a
  round input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩` (and the first component of the state).

## Main results

* `Games.exists_handlerMachine` (T1, the fill's target): a reduction with a polynomial-time
  handler is a machine, whose output is exactly the finalized output of the simulation.
* `Games.exists_interactiveHandlerMachine` (T2, the fill's target): a reduction with an
  interactive handler is an oracle machine against the outer oracles, with budget
  `q(n) · perCall(n) + finCall(n)`, whose computation is exactly the simulation followed by the
  finalization. The reductions that forward or answer queries with their own oracle need it (the
  PRF MAC's distinguisher, hash-and-sign's forger, the CPA and CCA reductions).
* `Games.InteractiveHandler.rU_input`, …, `rCnt_input`: the readers of a round input on
  `InteractiveHandler.input`; `Games.InteractiveHandler.impl_of_ret`: a call whose first round
  returns.
* `Games.exists_toCompOn_of_toComp` (the fill's target): a machine without input is a machine
  with an input that it ignores, with the same coins.
* `Games.exists_toOracleAdversary_of_bitCodec` (T4, the fill's target): an oracle machine
  against one `bitCodec` oracle with a one-bit output, on the empty input, evaluates as a
  next-query machine of the ch. 2–4 layer.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010:
  every reduction of ch. 5–8 (for example the proofs of Thms 135.4 and 168.2).
-/

namespace TCSlib.Cryptography.Games

open Complexity Turing

variable {k : ℕ}

/-- The bit-string oracles at parameter `n`, with polynomial lengths. -/
abbrev bitSpecAt (din dout : Fin k → PolyExpr) (n : ℕ) : OracleSpec (Fin k) :=
  bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n)

/-- The bit-string oracles at parameter `n` are `bitSpec` of the evaluated lengths:
`bitSpecAt din dout n = bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n)`. -/
theorem bitSpecAt_eq (din dout : Fin k → PolyExpr) (n : ℕ) :
    bitSpecAt din dout n = bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n) :=
  rfl

/-- The **context** of a reduction at parameter `n`, with the reduction's input `z` and its seed
`ω`: the string `⟨1^n, ⟨z, ω⟩⟩`. Every function of a handler reads it. -/
def seedIn (n : ℕ) (z ω : List Bool) : List Bool :=
  pairEncode (List.replicate n true) (pairEncode z ω)

/-- The context is `⟨1^n, ⟨z, ω⟩⟩`:
`seedIn n z ω = pairEncode (List.replicate n true) (pairEncode z ω)`. -/
theorem seedIn_eq (n : ℕ) (z ω : List Bool) :
    seedIn n z ω = pairEncode (List.replicate n true) (pairEncode z ω) :=
  rfl

/-- A **polynomial-time handler** for `k` bit-string oracles with query lengths `din` and answer
lengths `dout`: a reduction that runs the adversary once and answers its queries by itself. Its
three functions are polynomial-time, and each reads the context `⟨1^n, ⟨z, ω⟩⟩` (`seedIn`: the
parameter, the reduction's input `z` and its seed `ω`):
- `advIn` maps the context to the adversary's input;
- `run` answers one query: on `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨1^i, x⟩⟩⟩` (the context, the state `s`, and
  the query `x` to oracle `i`), it returns `⟨y, s'⟩`, the answer and the new state;
- `out` maps `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩` (the context, the final state and the adversary's output)
  to the reduction's output. -/
structure PolyHandler (k : ℕ) (din dout : Fin k → PolyExpr) where
  /-- The length of the state. -/
  stateLen : PolyExpr
  /-- The length of the seed (the handler's own coins). -/
  seedLen : PolyExpr
  /-- The initial state at each parameter. -/
  init : ∀ n, Fin (stateLen.eval n) → Bool
  /-- The handler as a string function. -/
  run : List Bool → List Bool
  /-- It is polynomial-time computable. -/
  poly : PolyTimeComputable run
  /-- The adversary's input, as a function of the context `⟨1^n, ⟨z, ω⟩⟩` (for example a public
  key built from `z` and the seed). For an adversary without input it is ignored. -/
  advIn : List Bool → List Bool
  /-- The adversary's input is polynomial-time computable. -/
  advIn_poly : PolyTimeComputable advIn
  /-- The finalization: the reduction's output, as a function of `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩` (the
  context, the final state `s` and the adversary's output `a`). -/
  out : List Bool → List Bool
  /-- The finalization is polynomial-time computable. -/
  out_poly : PolyTimeComputable out

namespace PolyHandler

variable {din dout : Fin k → PolyExpr}

/-- The handler's input string for the query `x` to oracle `i` in state `s`. -/
def input (n : ℕ) (z : List Bool) (ω : List Bool) (s : List Bool) (i : Fin k) (x : List Bool) :
    List Bool :=
  pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
    (pairEncode s (pairEncode (List.replicate i true) x))

/-- The handler's input string is `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨1^i, x⟩⟩⟩`. -/
theorem input_eq (n : ℕ) (z ω s : List Bool) (i : Fin k) (x : List Bool) :
    input n z ω s i x =
      pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
        (pairEncode s (pairEncode (List.replicate i true) x)) :=
  rfl

/-- The adversary's input at parameter `n`, for the reduction input `z` and the seed `ω`: `advIn`
of the context `⟨1^n, ⟨z, ω⟩⟩`. -/
def advInput (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) : List Bool :=
  H.advIn (seedIn n z (List.ofFn ω))

/-- The adversary's input is `advIn` of the context:
`H.advInput n z ω = H.advIn (seedIn n z (List.ofFn ω))`. -/
theorem advInput_eq (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) :
    H.advInput n z ω = H.advIn (seedIn n z (List.ofFn ω)) :=
  rfl

/-- The reduction's output at parameter `n`, for the reduction input `z` and the seed `ω`, when
the final state is `s` and the adversary's output is `a`: `out` of
`⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩`. -/
def result (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) : List Bool :=
  H.out (pairEncode (seedIn n z (List.ofFn ω)) (pairEncode (List.ofFn s) (List.ofFn a)))

/-- The reduction's output is `out` of the context, the final state and the adversary's output:
`H.result n z ω s a = H.out (pairEncode (seedIn n z (List.ofFn ω))
(pairEncode (List.ofFn s) (List.ofFn a)))`. -/
theorem result_eq (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) :
    H.result n z ω s a =
      H.out (pairEncode (seedIn n z (List.ofFn ω)) (pairEncode (List.ofFn s) (List.ofFn a))) :=
  rfl

/-- The handler's answer and new state, decoded with fixed lengths. If `run`'s output is not a
pair, both are all-`false`; otherwise each component of the wrong length is replaced by
all-`false` independently (a total default; well-behaved handlers never produce one). An
interactive handler defaults jointly instead (`InteractiveHandler`). -/
def answer (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) :
    (Fin ((dout i).eval n) → Bool) × (Fin (H.stateLen.eval n) → Bool) :=
  match pairDecode (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x))) with
  | some (yw, sw) =>
    ((decodeFin _ yw).getD (zeroBits _), (decodeFin _ sw).getD (zeroBits _))
  | none => (zeroBits _, zeroBits _)

section Answer

variable (H : PolyHandler k din dout) {n : ℕ} {z : List Bool} {ω : Fin (H.seedLen.eval n) → Bool}
  {s : Fin (H.stateLen.eval n) → Bool} {i : Fin k} {x : Fin ((din i).eval n) → Bool}

/-- If `run`'s output is not a pair, the answer and the new state are all-`false`. -/
theorem answer_of_pairDecode_eq_none
    (h : pairDecode (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x))) = none) :
    H.answer n z ω s i x = (zeroBits _, zeroBits _) := by
  unfold answer
  rw [h]

/-- If `run`'s output is the pair `⟨yw, sw⟩`, the answer is `yw` and the new state `sw`, each
decoded with its fixed length and all-`false` if that length is wrong:
`H.answer n z ω s i x = ((decodeFin _ yw).getD (zeroBits _), (decodeFin _ sw).getD (zeroBits _))`.
-/
theorem answer_of_pairDecode_eq_some {yw sw : List Bool}
    (h : pairDecode (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x))) =
      some (yw, sw)) :
    H.answer n z ω s i x =
      ((decodeFin _ yw).getD (zeroBits _), (decodeFin _ sw).getD (zeroBits _)) := by
  unfold answer
  rw [h]

/-- **A well-formed output:** if `run` returns `⟨y, s'⟩` with `y` and `s'` of the fixed lengths,
the answer is `y` and the new state `s'`. -/
theorem answer_of_run_eq {y : Fin ((dout i).eval n) → Bool} {s' : Fin (H.stateLen.eval n) → Bool}
    (h : H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)) =
      pairEncode (List.ofFn y) (List.ofFn s')) :
    H.answer n z ω s i x = (y, s') := by
  have h' : pairDecode (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x))) =
      some (List.ofFn y, List.ofFn s') := by
    rw [h, pairDecode_pairEncode]
  rw [answer_of_pairDecode_eq_some H h', decodeFin_ofFn, decodeFin_ofFn, Option.getD_some,
    Option.getD_some]

end Answer

/-- The handler as an implementation of the bit-string oracles at parameter `n`, for the
reduction input `z` and seed `ω`: it keeps its state and asks no oracle (the non-interactive
case). -/
def impl (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) :
    QueryImpl (bitSpecAt din dout n) (Fin (H.stateLen.eval n) → Bool) unifSpec :=
  fun i x s => .pure (H.answer n z ω s i x)

/-- The handler answers the query `x` to oracle `i` in state `s` with no coins and no queries:
`H.impl n z ω i x s = pure (H.answer n z ω s i x)`. -/
theorem impl_apply (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (i : Fin k) (x : Fin ((din i).eval n) → Bool)
    (s : Fin (H.stateLen.eval n) → Bool) :
    H.impl n z ω i x s = .pure (H.answer n z ω s i x) :=
  rfl

end PolyHandler

/-- **T1 (the efficiency fill's target; non-interactive handlers).** For a machine adversary `A`
with query budget `q` and `dα`-bit outputs against `k` bit-string oracles, and a polynomial-time
handler `H`, there is a machine `B` and, at every parameter, a bijection `φ` from (the handler's
seed, `A`'s coins) to `B`'s coins, with the following property. Run `A` on the input
`H.advInput n z ω`, answer its queries by `H` (input `z`, seed `ω`) from `H`'s initial state, and
let `a` be `A`'s output and `s` the final state. Then `B`'s output on input `z` with coins
`φ (ω, r)` is exactly the reduction's output `H.result n z ω s a`.

**Proof sketch** (the fill's; route note §"T1").
1. `B`'s raw function is the activation loop `EffFill.hRaw` (`GGMRed.stateLoopFun` through
   `EffFill.actLoop`) on the layout `⟨⟨⟨1^n, ⟨z, ω⟩⟩, ⟨α_A, s₀⟩⟩, r⟩`. The initial state
   `s₀ = H.init n` is part of the advice, beside `A`'s advice `α_A`, since `init` is an arbitrary
   function of `n`; so `B` is non-uniform even when `A` is uniform. The loop state is
   `⟨L, ⟨s, 1^t⟩⟩` (`A`'s encoded log, `H`'s state, the answered queries); the context
   `seedIn n z ω` and `A`'s input are recomputed in every round.
2. A round runs `A` on `⟨A's input, L⟩` (`NUPPT.polyTimeComputable_output`) and reads its move
   through the canonical decoder `EffFill.canonWord`, which returns the canonical word of
   `decodeBitMove`'s move on every word (`EffFill.canonWord_eq`, canonicity tested by re-encoding).
   It stops with `H.out ⟨ctx, ⟨s, a⟩⟩` on an output `a`, and with `H.out ⟨ctx, ⟨s, 0^{dα(n)}⟩⟩` on a
   query when `t = q(n)`. Otherwise it feeds the query to `H.run`, decodes the answer and the new
   state componentwise (`EffFill.fixLen`, `EffFill.ofFn_getD_decodeFin` and the `answer` lemmas),
   and appends the entry to `L` (`EffFill.encodeLog_append_single`).
3. At most `q(n) + 1` rounds, with states of polynomial length (all lengths are fixed), so the raw
   function is polynomial-time (`EffFill.hRaw_poly`, from `GGMRed.stateLoopFun_poly`).
4. The functional equation (`EffFill.hRaw_spec`): by induction on the remaining budget, the loop's
   state after `t` rounds encodes the simulation after `t` queries (`toCompOn_eq`, `buildComp`'s
   case lemmas, `simulate_query`, `PolyHandler.impl_apply`); `GGMRed.stateLoopFun_eval` reads off
   the output (`EffFill.runsTo_stop`), and `result_eq` and `seedIn_eq` identify it.
5. `B` is `NUPPT.ofPolyTime` of the raw function followed by `NUPPT.exists_split` with
   `p = H.seedLen` (`EffFill.exists_splitMachine`); `φ` appends the seed and the coins. -/
theorem exists_handlerMachine (A : NUPPT) (q : PolyExpr) (din dout : Fin k → PolyExpr)
    (dα : PolyExpr) (H : PolyHandler k din dout) :
    ∃ B : NUPPT, ∀ n : ℕ, ∃ φ : (Fin (H.seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n,
      ∀ (z : List Bool) (ω : Fin (H.seedLen.eval n) → Bool) (r : A.Coins n),
        ∃ (a : Fin (dα.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool),
          simulate (H.impl n z ω)
              (A.toCompOn
                (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n))
                n (q.eval n) (H.advInput n z ω) r) (H.init n) = .pure (a, s) ∧
            B.runAt n z (φ (ω, r)) = H.result n z ω s a := by
  -- The machine: the handler loop of `EffFill.hRaw`, with `⟨A.advice n, s₀⟩` as advice and the
  -- seed passed as data.
  obtain ⟨B, hB⟩ := EffFill.exists_splitMachine A
    (EffFill.hRaw_poly A q dα din dout H.stateLen H.poly H.advIn_poly H.out_poly)
    (.add (.add (.mul (.const 2) A.adv) (.const 2)) H.stateLen)
    (fun n => pairEncode (A.advice n) (List.ofFn (H.init n))) (fun n => by
      rw [length_pairEncode, List.length_ofFn]
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
      have := A.advice_length n
      omega) H.seedLen
  refine ⟨B, fun n => ?_⟩
  obtain ⟨φ, hφ⟩ := hB n
  refine ⟨φ, fun z ω r => ?_⟩
  -- The handler's answers are `run`'s output decoded componentwise.
  have hans : ∀ (i : Fin k) (x : Fin ((din i).eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool),
      List.ofFn (H.answer n z ω s i x).1 = EffFill.fixLen ((dout i).eval n) (pairFstD (H.run
        (pairEncode (pairEncode (List.replicate n true) (pairEncode z (List.ofFn ω)))
          (pairEncode (List.ofFn s) (pairEncode (List.replicate i true) (List.ofFn x)))))) ∧
      List.ofFn (H.answer n z ω s i x).2 = EffFill.fixLen (H.stateLen.eval n) (pairSndD (H.run
        (pairEncode (pairEncode (List.replicate n true) (pairEncode z (List.ofFn ω)))
          (pairEncode (List.ofFn s) (pairEncode (List.replicate i true) (List.ofFn x)))))) := by
    intro i x s
    rw [← PolyHandler.input_eq]
    cases h : pairDecode (H.run (PolyHandler.input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)))
      with
    | none =>
      rw [PolyHandler.answer_of_pairDecode_eq_none H h, pairFstD_of_pairDecode_eq_none h,
        pairSndD_of_pairDecode_eq_none h, EffFill.fixLen_nil, EffFill.fixLen_nil, ofFn_zeroBits,
        ofFn_zeroBits]
      exact ⟨rfl, rfl⟩
    | some p =>
      obtain ⟨yw, sw⟩ := p
      rw [PolyHandler.answer_of_pairDecode_eq_some H h, eq_pairEncode_of_pairDecode _ _ _ h,
        pairFstD_pairEncode, pairSndD_pairEncode, EffFill.ofFn_getD_decodeFin,
        EffFill.ofFn_getD_decodeFin]
      exact ⟨rfl, rfl⟩
  obtain ⟨a, s, hsim, hraw⟩ := EffFill.hRaw_spec A q dα din dout H.stateLen H.run H.advIn H.out
    (spec' := unifSpec) n z (List.ofFn ω) r (H.init n) (fun i x s => H.answer n z ω s i x) hans
  refine ⟨a, s, ?_, ?_⟩
  · have himpl : H.impl n z ω = fun i x s => OracleComp.pure (H.answer n z ω s i x) := by
      funext i x s
      exact H.impl_apply n z ω i x s
    rw [himpl, PolyHandler.advInput_eq, seedIn_eq]
    exact hsim
  · rw [hφ, hraw, PolyHandler.result_eq, seedIn_eq]

/-! ### Interactive handlers (T2) -/

variable {k' : ℕ}

/-- A **polynomial-time interactive handler** for `k` inner bit-string oracles that may itself
query `k'` outer bit-string oracles. Like `PolyHandler`, it computes the adversary's input from
the context `⟨1^n, ⟨z, ω⟩⟩` (`advIn`); it answers the adversary's queries (`run`), and computes the
reduction's output in a last phase (`finRun`), both with outer queries.

One inner query `x` to oracle `i` is answered with at most `perCall(n)` outer queries, in at most
`perCall(n) + 1` rounds of `run` (the last returns the answer; a further query after the budget
is spent is cut off with the default). In each round, `run` sees `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`, where `L` is
the outer log of the call so far (encoded as `bitCodec` encodes logs), and returns a move in
`bitCodec`'s format: a query `⟨[false], ⟨1^j, x'⟩⟩` to outer oracle `j`, or the answer
`⟨[true], y ‖ s'⟩` (the inner answer, then the new state). A malformed round output, including a
payload `y ‖ s'` of the wrong total length, gives the all-`false` answer and state together (a
joint default, unlike `PolyHandler.answer`, which defaults each component separately).

The finalization works the same way on `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩` (the final state, the
adversary's output and the outer log of the finalization so far), with at most `finCall(n)` outer
queries; it returns the reduction's `outLen(n)`-bit output as `⟨[true], b⟩`, the all-`false`
output on a malformed round output or on a further query after the budget is spent. (A return at
zero remaining budget is accepted: only a query then hits the timeout.) -/
structure InteractiveHandler (k : ℕ) (din dout : Fin k → PolyExpr) (k' : ℕ)
    (din' dout' : Fin k' → PolyExpr) where
  /-- The length of the state. -/
  stateLen : PolyExpr
  /-- The length of the seed. -/
  seedLen : PolyExpr
  /-- The bound on outer queries per inner query. -/
  perCall : PolyExpr
  /-- The initial state at each parameter. -/
  init : ∀ n, Fin (stateLen.eval n) → Bool
  /-- One round of the handler, as a string function. -/
  run : List Bool → List Bool
  /-- It is polynomial-time computable. -/
  poly : PolyTimeComputable run
  /-- The adversary's input, as a function of the context `⟨1^n, ⟨z, ω⟩⟩`. For an adversary
  without input it is ignored. -/
  advIn : List Bool → List Bool
  /-- The adversary's input is polynomial-time computable. -/
  advIn_poly : PolyTimeComputable advIn
  /-- The length of the reduction's output. -/
  outLen : PolyExpr
  /-- The bound on the outer queries of the finalization. -/
  finCall : PolyExpr
  /-- One round of the finalization, as a string function: on `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩` it
  returns an outer query `⟨[false], ⟨1^j, x'⟩⟩` or the reduction's output `⟨[true], b⟩`. -/
  finRun : List Bool → List Bool
  /-- The finalization's round is polynomial-time computable. -/
  finRun_poly : PolyTimeComputable finRun

namespace InteractiveHandler

variable {din dout : Fin k → PolyExpr} {din' dout' : Fin k' → PolyExpr}

/-- The handler's input string for one round. -/
def input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) : List Bool :=
  pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
    (pairEncode s (pairEncode (pairEncode (List.replicate i true) x) L))

/-- The handler's input string for one round is `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`. -/
theorem input_eq (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
    input n z ω s i x L =
      pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
        (pairEncode s (pairEncode (pairEncode (List.replicate i true) x) L)) :=
  rfl

/-! #### Readers of a round input

The fields of a round input `w = ⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`, read with `pairFstD` and
`pairSndD`, as a handler's round function reads them; on `input n z ω s i x L` they return the
field (`rU_input`, …), and each is polynomial-time (`polyTimeComputable_rU`, …). `rCnt` reads the
first component of the state, the call count `1^j` of the handlers that keep one there. -/

/-- The parameter `1^n` of a round input: `rU w = pairFstD (pairFstD w)`. -/
def rU (w : List Bool) : List Bool := pairFstD (pairFstD w)
/-- The reduction input `z` of a round input: `rZ w = pairFstD (pairSndD (pairFstD w))`. -/
def rZ (w : List Bool) : List Bool := pairFstD (pairSndD (pairFstD w))
/-- The seed `ω` of a round input: `rW w = pairSndD (pairSndD (pairFstD w))`. -/
def rW (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD w))
/-- The state `s` of a round input: `rS w = pairFstD (pairSndD w)`. -/
def rS (w : List Bool) : List Bool := pairFstD (pairSndD w)
/-- The oracle index `1^i` of a round input:
`rI w = pairFstD (pairFstD (pairSndD (pairSndD w)))`. -/
def rI (w : List Bool) : List Bool := pairFstD (pairFstD (pairSndD (pairSndD w)))
/-- The query `x` of a round input: `rX w = pairSndD (pairFstD (pairSndD (pairSndD w)))`. -/
def rX (w : List Bool) : List Bool := pairSndD (pairFstD (pairSndD (pairSndD w)))
/-- The outer log `L` of a round input: `rL w = pairSndD (pairSndD (pairSndD w))`. -/
def rL (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))
/-- The first component `pairFstD s` of the state of a round input:
`rCnt w = pairFstD (rS w)`. -/
def rCnt (w : List Bool) : List Bool := pairFstD (rS w)

/-- `rU (input n z ω s i x L) = 1^n`. -/
theorem rU_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
    rU (input n z ω s i x L) = List.replicate n true := by
  simp only [rU, input_eq, pairFstD_pairEncode]

/-- `rZ (input n z ω s i x L) = z`. -/
theorem rZ_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
    rZ (input n z ω s i x L) = z := by
  simp only [rZ, input_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-- `rW (input n z ω s i x L) = ω`. -/
theorem rW_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
    rW (input n z ω s i x L) = ω := by
  simp only [rW, input_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-- `rS (input n z ω s i x L) = s`. -/
theorem rS_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
    rS (input n z ω s i x L) = s := by
  simp only [rS, input_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-- `rI (input n z ω s i x L) = 1^i`. -/
theorem rI_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
    rI (input n z ω s i x L) = List.replicate i true := by
  simp only [rI, input_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-- `rX (input n z ω s i x L) = x`. -/
theorem rX_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
    rX (input n z ω s i x L) = x := by
  simp only [rX, input_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-- `rL (input n z ω s i x L) = L`. -/
theorem rL_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
    rL (input n z ω s i x L) = L := by
  simp only [rL, input_eq, pairSndD_pairEncode]

/-- `rCnt (input n z ω s i x L) = pairFstD s`. -/
theorem rCnt_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
    rCnt (input n z ω s i x L) = pairFstD s := by
  rw [rCnt, rS_input]

/-- `rU` is polynomial-time: `PolyTimeComputable rU`. -/
theorem polyTimeComputable_rU : PolyTimeComputable rU :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD

/-- `rZ` is polynomial-time: `PolyTimeComputable rZ`. -/
theorem polyTimeComputable_rZ : PolyTimeComputable rZ :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)

/-- `rW` is polynomial-time: `PolyTimeComputable rW`. -/
theorem polyTimeComputable_rW : PolyTimeComputable rW :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)

/-- `rS` is polynomial-time: `PolyTimeComputable rS`. -/
theorem polyTimeComputable_rS : PolyTimeComputable rS :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- `rI` is polynomial-time: `PolyTimeComputable rI`. -/
theorem polyTimeComputable_rI : PolyTimeComputable rI :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))

/-- `rX` is polynomial-time: `PolyTimeComputable rX`. -/
theorem polyTimeComputable_rX : PolyTimeComputable rX :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))

/-- `rL` is polynomial-time: `PolyTimeComputable rL`. -/
theorem polyTimeComputable_rL : PolyTimeComputable rL :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- `rCnt` is polynomial-time: `PolyTimeComputable rCnt`. -/
theorem polyTimeComputable_rCnt : PolyTimeComputable rCnt :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_rS

/-- The adversary's input at parameter `n`, for the reduction input `z` and the seed `ω`: `advIn`
of the context `⟨1^n, ⟨z, ω⟩⟩`. -/
def advInput (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) : List Bool :=
  H.advIn (seedIn n z (List.ofFn ω))

/-- The adversary's input is `advIn` of the context:
`H.advInput n z ω = H.advIn (seedIn n z (List.ofFn ω))`. -/
theorem advInput_eq (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) :
    H.advInput n z ω = H.advIn (seedIn n z (List.ofFn ω)) :=
  rfl

/-- **One call** of the handler on the inner query `x` to oracle `i` in state `s`: at most
`perCall(n)` outer queries, in at most `perCall(n) + 1` rounds of `run`. A malformed round output
is the all-`false` answer and state (`decodeBitMove`'s default), and so is a further query after
the budget is spent (a return at zero remaining budget is accepted). -/
def call (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) :
    OracleComp (bitSpecAt din' dout' n) (Fin ((dout i).eval n + H.stateLen.eval n) → Bool) :=
  buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n) _
      (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)
        ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
    (zeroBits _) (H.perCall.eval n) []

/-- One call is `buildComp` of the handler's rounds, from the empty outer log, with budget
`perCall(n)` and the all-`false` result on a query after it is spent: `H.call n z ω s i x =
buildComp (fun L => decodeBitMove _ _ _ (H.run (input … L))) (zeroBits _) (H.perCall.eval n) []`.
-/
theorem call_eq (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) :
    H.call n z ω s i x =
      buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
          ((dout i).eval n + H.stateLen.eval n)
          (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)
            ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
        (zeroBits _) (H.perCall.eval n) [] :=
  rfl

/-- The interactive handler as an implementation of the inner oracles by the outer ones, at
parameter `n`, reduction input `z` and seed `ω`: one `call` per inner query, its result split
into the answer and the new state. -/
def impl (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) :
    QueryImpl (bitSpecAt din dout n) (Fin (H.stateLen.eval n) → Bool) (bitSpecAt din' dout' n) :=
  fun i x s => (H.call n z ω s i x).bind fun w =>
    .pure (fun j => w (Fin.castAdd _ j), fun j => w (Fin.natAdd _ j))

/-- The inner query `x` to oracle `i` in state `s` is answered by one `call`, whose result is
split into the answer (its first `dout i` bits) and the new state (the rest):
`H.impl n z ω i x s = (H.call n z ω s i x).bind fun w =>
pure (fun j => w (Fin.castAdd _ j), fun j => w (Fin.natAdd _ j))`. -/
theorem impl_apply (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (i : Fin k) (x : Fin ((din i).eval n) → Bool)
    (s : Fin (H.stateLen.eval n) → Bool) :
    H.impl n z ω i x s =
      (H.call n z ω s i x).bind fun w =>
        .pure (fun j => w (Fin.castAdd _ j), fun j => w (Fin.natAdd _ j)) :=
  rfl

/-- **A call whose first round returns `y ‖ s'`** is answered `y` with the new state `s'`: if
`H.run (input n z ⟦ω⟧ ⟦s⟧ i ⟦x⟧ []) = ⟨[true], ⟦y⟧ ++ ⟦s'⟧⟩`, then
`H.impl n z ω i x s = pure (y, s')`.

**Proof sketch.** One call is `buildComp` of the rounds from the empty log (`call_eq`). The first
round decodes as the final output `y ‖ s'` (`decodeBitMove_ret`), which stops the computation at
every budget (`buildComp_zero_of_ret`, `buildComp_succ_of_ret`); the output splits back into `y`
and `s'` (`Fin.append_left`, `Fin.append_right`). -/
theorem impl_of_ret (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) {i : Fin k} (x : Fin ((din i).eval n) → Bool)
    (s : Fin (H.stateLen.eval n) → Bool) (y : Fin ((dout i).eval n) → Bool)
    (s' : Fin (H.stateLen.eval n) → Bool)
    (h : H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x) []) =
      pairEncode [true] (List.ofFn y ++ List.ofFn s')) :
    H.impl n z ω i x s = .pure (y, s') := by
  rw [impl_apply, call_eq]
  have hy : (fun j => Fin.append y s' (Fin.castAdd (H.stateLen.eval n) j)) = y :=
    funext fun j => Fin.append_left y s' j
  have hs : (fun j => Fin.append y s' (Fin.natAdd ((dout i).eval n) j)) = s' :=
    funext fun j => Fin.append_right y s' j
  generalize H.perCall.eval n = q
  cases q with
  | zero =>
    rw [buildComp_zero_of_ret (a := Fin.append y s') (by
      show decodeBitMove _ _ _ (H.run _) = _
      rw [MachineCodec.encodeLog_nil, h, ← List.ofFn_fin_append]
      exact decodeBitMove_ret _ _ _ _), OracleComp.pure_bind, hy, hs]
  | succ q =>
    rw [buildComp_succ_of_ret (a := Fin.append y s') (by
      show decodeBitMove _ _ _ (H.run _) = _
      rw [MachineCodec.encodeLog_nil, h, ← List.ofFn_fin_append]
      exact decodeBitMove_ret _ _ _ _), OracleComp.pure_bind, hy, hs]

/-- The input string of one round of the finalization: `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`, with the
final state `s`, the adversary's output `a` and the outer log `L` of the finalization so far. -/
def finInput (n : ℕ) (z ω s a L : List Bool) : List Bool :=
  pairEncode (seedIn n z ω) (pairEncode s (pairEncode a L))

/-- The input string of one round of the finalization is `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`:
`finInput n z ω s a L = pairEncode (seedIn n z ω) (pairEncode s (pairEncode a L))`. -/
theorem finInput_eq (n : ℕ) (z ω s a L : List Bool) :
    finInput n z ω s a L = pairEncode (seedIn n z ω) (pairEncode s (pairEncode a L)) :=
  rfl

/-- **The finalization** in the final state `s`, after the adversary's output `a`: the
reduction's `outLen(n)`-bit output, computed with at most `finCall(n)` outer queries, in at most
`finCall(n) + 1` rounds of `finRun`. A malformed round output is the all-`false` output
(`decodeBitMove`'s default), and so is a further query after the budget is spent (a return at
zero remaining budget is accepted). -/
def finish (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) : OracleComp (bitSpecAt din' dout' n) (Fin (H.outLen.eval n) → Bool) :=
  buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
      (H.outLen.eval n)
      (H.finRun (finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
        ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
    (zeroBits _) (H.finCall.eval n) []

/-- The finalization is `buildComp` of its rounds, from the empty outer log, with budget
`finCall(n)` and the all-`false` output on a query after it is spent: `H.finish n z ω s a =
buildComp (fun L => decodeBitMove _ _ _ (H.finRun (finInput … L))) (zeroBits _)
(H.finCall.eval n) []`. -/
theorem finish_eq (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) :
    H.finish n z ω s a =
      buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
          (H.outLen.eval n)
          (H.finRun (finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
            ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
        (zeroBits _) (H.finCall.eval n) [] :=
  rfl

end InteractiveHandler

/-- **T2 (the efficiency fill's target; interactive handlers).** For a machine adversary `A`
with query budget `q` and `dα`-bit outputs against `k` bit-string oracles, and an interactive
handler `H` answering them through `k'` outer oracles, there is an oracle machine `B` against the
outer oracles, with budget `q(n) · perCall(n) + finCall(n)`, and at every parameter a bijection
`φ` from (`H`'s seed, `A`'s coins) to `B`'s coins, with the following property. `B` on input `z`
with coins `φ (ω, r)` is, as an oracle computation, exactly the reduction: `A` run on the input
`H.advInput n z ω`, its queries answered by `H` (input `z`, seed `ω`) from `H`'s initial state,
followed by `H`'s finalization on the final state and `A`'s output.

**Proof sketch** (the fill's; route note §"T2", with the log replay).
1. `B`'s next-move function, on `⟨z, O⟩` (`O` its encoded outer log) with the seed `ω`, `A`'s coins
   `r` and the advice `⟨α_A, s₀⟩` (`s₀ = H.init n`, as in T1), is the activation loop
   `EffFill.iRaw`, which **replays** the whole reduction, one activation per round: a round of `A`
   opens a call (a query within budget) or the finalization (an output, or a query at budget `0`
   with the all-`false` output); a round of a call reruns `H.run` on
   `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`, its answer (or the joint default at budget `0`) appending
   the entry to `A`'s log; a round of the finalization reruns `H.finRun`. An outer query within
   budget is answered by the next entry of `O`; when `O` is exhausted it is `B`'s next move, its
   canonical word (`EffFill.canonWord_eq`), and so is the finalization's output.
2. At most `2 + finCall(n) + q(n)(perCall(n) + 2)` rounds, with states of polynomial length
   (the unreplayed part of `O` is bounded by the input), so the raw function is polynomial-time
   (`EffFill.iRaw_poly`, from `GGMRed.stateLoopFun_poly`).
3. The reduction tree makes at most `q(n) · perCall(n) + finCall(n)` queries
   (`toCompOn_costBoundedBy`, `buildComp_costBoundedBy`, `EffFill.costBoundedBy_mul`,
   `simulate_costBoundedBy`, `CostBoundedBy.bind`), so `B`'s budget never cuts the replay short.
4. The functional equation (`EffFill.iRaw_spec`): `B`'s next-move function replays the reduction
   tree from the empty log (`EffFill.ReplaysFrom`), by induction along the phases
   (`EffFill.adv_phase`, `call_phase`, `fin_phase`) on every branch, since the outer answers are
   arbitrary; then `EffFill.buildComp_of_replaysFrom` gives the equality of trees. The handler's
   calls and finalization are read through `impl_apply`, `call_eq`, `input_eq`, `finish_eq` and
   `finInput_eq`.
5. Coins and advice as in T1 (`EffFill.exists_splitMachine`). -/
theorem exists_interactiveHandlerMachine (A : NUPPT) (q : PolyExpr)
    (din dout : Fin k → PolyExpr) (din' dout' : Fin k' → PolyExpr) (dα : PolyExpr)
    (H : InteractiveHandler k din dout k' din' dout') :
    ∃ B : NUPPT, ∀ n : ℕ, ∃ φ : (Fin (H.seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n,
      ∀ (z : List Bool) (ω : Fin (H.seedLen.eval n) → Bool) (r : A.Coins n),
        (simulate (H.impl n z ω)
            (A.toCompOn (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n))
              n (q.eval n) (H.advInput n z ω) r) (H.init n)).bind
            (fun res => H.finish n z ω res.2 res.1) =
          B.toCompOn
            (bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) (H.outLen.eval n))
            n (q.eval n * H.perCall.eval n + H.finCall.eval n) z (φ (ω, r)) := by
  -- The machine: the replay loop of `EffFill.iRaw`, with `⟨A.advice n, s₀⟩` as advice and the
  -- seed passed as data.
  obtain ⟨B, hB⟩ := EffFill.exists_splitMachine A
    (EffFill.iRaw_poly A q dα din dout din' H.stateLen H.perCall H.outLen H.finCall dout' H.poly
      H.advIn_poly H.finRun_poly)
    (.add (.add (.mul (.const 2) A.adv) (.const 2)) H.stateLen)
    (fun n => pairEncode (A.advice n) (List.ofFn (H.init n))) (fun n => by
      rw [length_pairEncode, List.length_ofFn]
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
      have := A.advice_length n
      omega) H.seedLen
  refine ⟨B, fun n => ?_⟩
  obtain ⟨φ, hφ⟩ := hB n
  refine ⟨φ, fun z ω r => ?_⟩
  -- The handler's calls and finalization are the raw ones of `EffFill`.
  have himpl : H.impl n z ω =
      EffFill.iImpl din dout din' dout' H.stateLen H.perCall H.run n z (List.ofFn ω) := by
    funext i x s
    rw [InteractiveHandler.impl_apply, EffFill.iImpl_apply, InteractiveHandler.call_eq,
      EffFill.iCall_eq]
    simp only [InteractiveHandler.input_eq]
  have hfin : ∀ (s : Fin (H.stateLen.eval n) → Bool) (a : Fin (dα.eval n) → Bool),
      H.finish n z ω s a =
        EffFill.iFinish din' dout' H.stateLen H.outLen H.finCall H.finRun n z (List.ofFn ω) s a :=
            by
    intro s a
    rw [InteractiveHandler.finish_eq, EffFill.iFinish_eq]
    simp only [InteractiveHandler.finInput_eq, seedIn_eq]
  rw [himpl, InteractiveHandler.advInput_eq, seedIn_eq]
  simp only [hfin]
  rw [← EffFill.iRaw_spec A q dα din dout din' dout' H.stateLen H.perCall H.outLen H.finCall H.run
    H.advIn H.finRun n z (List.ofFn ω) r (H.init n), NUPPT.toCompOn_eq, bitCodec_timeout]
  congr 1
  funext O
  rw [bitCodec_decodeMove, hφ, EffFill.iX_eq]

/-! ### Companions: adversaries without input, and the bridge to pseudorandom functions (T4) -/

/-- **A machine without input is a machine with an input that it ignores.** For every machine
`A` there is a machine `A'` with the same coins whose computation on any input `x` is `A`'s
computation, for every codec and budget, the coins related by a bijection `φ`. So T1 and T2,
stated for adversaries with input, cover adversaries without one.

**Proof sketch.** `A'` is `NUPPT.exists_comp` of `A` with `pre = pairSndD` and `post = id`, so
`A'.coins = A.coins` and `A'.runAtL n ⟨x, L⟩ r = A.runAtL n L r` (`pairSndD_pairEncode`). The
bijection `φ` is `NUPPT.coinsCongr`, which transports the coins along the equal coin polynomials
and keeps the coin string (`NUPPT.runAt_coinsCongr`); with `runAt_eq` the next-move functions of
`A'.toCompOn codec n q x (φ r)` and `A.toComp codec n q r` agree on every log, and
`toCompOn_eq`, `toComp_eq` conclude. -/
theorem exists_toCompOn_of_toComp (A : NUPPT) :
    ∃ A' : NUPPT, A'.coins = A.coins ∧ ∀ n : ℕ, ∃ φ : A.Coins n ≃ A'.Coins n,
      ∀ {ι α : Type} {spec : OracleSpec ι} (codec : MachineCodec spec α) (q : ℕ)
        (x : List Bool) (r : A.Coins n),
        A'.toCompOn codec n q x (φ r) = A.toComp codec n q r := by
  obtain ⟨A', hc, -, -, hA'⟩ :=
    NUPPT.exists_comp A polyTimeComputable_pairSndD polyTimeComputable_id
  refine ⟨A', hc, fun n => ⟨NUPPT.coinsCongr hc.symm n, ?_⟩⟩
  intro ι α spec codec q x r
  have hnext : (fun hist => codec.decodeMove
      (A'.runAt n (pairEncode x (codec.encodeLog hist)) (NUPPT.coinsCongr hc.symm n r))) =
      fun hist => codec.decodeMove (A.runAt n (codec.encodeLog hist) r) := by
    funext hist
    rw [NUPPT.runAt_coinsCongr, hA', pairSndD_pairEncode, id_eq, ← NUPPT.runAt_eq]
  rw [NUPPT.toCompOn_eq, NUPPT.toComp_eq, hnext]

/-- **T4 (the efficiency fill's target; the bridge to pseudorandom functions).** An oracle
machine `B` against one `bitCodec` oracle (`ℓ₁(n)`-bit queries, `ℓ₂(n)`-bit answers) with a
one-bit output, run on the empty input, is a next-query machine of the ch. 2–4 layer: there is a
machine `B'` with the same coins whose oracle adversary `B'.toOracleAdversary`, run against any
`f`, returns the bit of `B`'s computation evaluated with `f`, the coins related by a bijection
`φ`. So `OracleEnsemble.Indist`, and with it `PRF`, applies to the machines of T2 with one outer
oracle and a one-bit output (through `oracleDist_apply` and `Bridge.eval_eq_evalFn`).

**Proof sketch.**
1. `B'` is `NUPPT.exists_comp` of `B` with two polynomial-time translators, so `B'.coins = B.coins`:
   - `EffFill.bridgePre` maps the history `⟨⟨x₁, y₁⟩, ⟨…, []⟩⟩` (`encodeHist`) to
     `⟨[], ⟨⟨[], ⟨x₁, y₁⟩⟩, ⟨…, []⟩⟩⟩`, `B`'s empty input and its log (`bitCodec_encodeEntry` with
     `1^0 = []`), by emitting one piece per suffix (`Complexity.polyTimeComputable_iterateEmit` with
     the step `pairSndD`; `EffFill.bridgePre_encodeHist`);
   - `EffFill.bridgePost` maps a canonical query word `⟨[false], ⟨[], x⟩⟩` (tested by re-encoding)
     to `⟨[false], x⟩`, the word `⟨[true], [true]⟩` to the verdict `[true, true]`, and every other
     word to `[true, false]`; then `decodeOracleMove` and `decodeBitMove` read corresponding moves
     (`EffFill.bridgePost_spec`, from `decodeBitMove_query`, `decodeBitMove_ret`,
     `decodeBitMove_of_not_canonical` and the case lemmas of `decodeOracleMove`), a payload of the
     wrong length included.
2. Both trees branch on corresponding moves, so by induction on the budget
   (`EffFill.eval_buildTree_bridge`: `buildTree`'s and `buildComp`'s case lemmas) their
   evaluations against `f` and `fun _ => f` agree (`QueryTree.eval_query`,
   `OracleComp.evalFn_query`); at the timeout the verdict `false` is bit `0` of `zeroBits 1`
   (`zeroBits_apply`). `toOracleAdversary_eq` and `toCompOn_eq` unfold the two sides.
3. `φ` is `NUPPT.coinsCongr`, as in `exists_toCompOn_of_toComp`. -/
theorem exists_toOracleAdversary_of_bitCodec (B : NUPPT) (ℓ₁ ℓ₂ : PolyExpr) :
    ∃ B' : NUPPT, B'.coins = B.coins ∧ ∀ n : ℕ, ∃ φ : B.Coins n ≃ B'.Coins n,
      ∀ (q : ℕ) (r : B.Coins n) (f : (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)),
        (B'.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) q (φ r)).eval f =
          (B.toCompOn (bitCodec (fun _ : Fin 1 => ℓ₁.eval n) (fun _ => ℓ₂.eval n) 1) n q []
              r).evalFn (fun _ => f) 0 := by
  obtain ⟨B', hc, -, -, hB'⟩ :=
    NUPPT.exists_comp B EffFill.bridgePre_poly EffFill.bridgePost_poly
  refine ⟨B', hc, fun n => ⟨NUPPT.coinsCongr hc.symm n, fun q r f => ?_⟩⟩
  have hnext : (fun hist : List ((Fin (ℓ₁.eval n) → Bool) × (Fin (ℓ₂.eval n) → Bool)) =>
      decodeOracleMove (ℓ₁.eval n)
      (B'.runAt n (encodeHist hist) (NUPPT.coinsCongr hc.symm n r))) =
      fun hist => decodeOracleMove (ℓ₁.eval n)
        (EffFill.bridgePost (B.runAt n (EffFill.bridgePre (encodeHist hist)) r)) := by
    funext hist
    rw [NUPPT.runAt_coinsCongr, hB', ← NUPPT.runAt_eq]
  have h := EffFill.eval_buildTree_bridge (ℓ₁.eval n) (ℓ₂.eval n) (fun y => B.runAt n y r) f q []
  rw [EffFill.logHist_eq, List.map_nil] at h
  rw [NUPPT.toOracleAdversary_eq, hnext, NUPPT.toCompOn_eq]
  simp only [bitCodec_decodeMove, bitCodec_timeout]
  exact h

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Asymptotic/Adversary.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Cryptography.Foundations.Experiments
import TCSlib.Cryptography.HardcoreBit.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machines as adversaries of the concrete experiments

The bridge between the machine layer (`Complexity.NUPPT`, strings `List Bool`) and the
concrete security experiments of `TCSlib.Cryptography.Foundations.Experiments` (typed
inputs `Fin m → Bool`, adversaries as functions of the input and of a uniform coin string).
An `NUPPT` `A` activated at parameter `n` becomes

* an *inverter* `A.inverter n ℓ m : (Fin m → Bool) → A.Coins n → Option (Fin ℓ → Bool)`
  [PS10, Definitions 27.3, 28.4]: `A(1^n, y)` with the output decoded as an `ℓ`-bit string;
* its literal variant `A.inverterLit ℓ m` for [PS10, Definition 26.1] (`A(f(x))`, activation
  at the input length `m`, no `1^n`);
* a *distinguisher* / *predictor* `A.distinguisher n m`, `A.predictor n m`
  [PS10, Definitions 69.4, 75.2, 78.3]: `A(1^n, t) = 1`, i.e. the output is the string `[true]`;
  `A.distinguisherL n` takes an untyped sample.

Inversion with a possibly failing decoder is `invProbOpt` (the probability that the decoded
output is a preimage); it is bridged to the concrete `invProb` by `invProbOpt_le_invProb`
(any default for a failure can only increase the probability) and `invProbOpt_some` (a total
inverter has the same probability). Foundation decision D5: inverses are sought in the
domain at the current parameter, and a wrong-length output counts as failure.

The file also records that "computes `f` with probability one" [PS10, Definition 24.6]
is, on the finite uniform coin space, the same as "for every coin string"
(`Complexity.NUPPT.computes_iff_uprob`), which justifies the frozen form of
`Complexity.NUPPT.Computes`.

**Deviation:** `inverter`: wrong-length output = failure (D5); verdict `= [true]` (normalisable
by `ifEq`).

## Main definitions

* `TCSlib.Cryptography.coinBlock` — the common indexed coin-tape segment.
* `TCSlib.Cryptography.decodeFin` — decode a string as an `ℓ`-bit string, failure on a wrong
  length; `TCSlib.Cryptography.padFin` — pad/truncate (for samplers).
* `TCSlib.Cryptography.blocksEquivX`, `TCSlib.Cryptography.FunFamily.blocks` — the canonical
  block bijection `(Fin (q·ℓ) → X) ≃ (Fin q → Fin ℓ → X)` and its Bool form, with the readers
  `blocksEquivX_apply`, `blocksEquivX_symm_apply`, `FunFamily.blocks_apply`,
  `FunFamily.blocks_symm_apply`.
* `Complexity.NUPPT.inverter`, `Complexity.NUPPT.inverterLit` — an `NUPPT` as an inverter
  (with `1^n`, and literal).
* `Complexity.NUPPT.distinguisher`, `Complexity.NUPPT.distinguisherL`,
  `Complexity.NUPPT.predictor` — an `NUPPT` as a distinguisher / predictor.
* `TCSlib.Cryptography.invProbOpt` — inversion probability of a possibly failing inverter.

## Main results

* `TCSlib.Cryptography.coinBlock_eq`, `TCSlib.Cryptography.length_coinBlock` — the segment
  equation and its full-length condition.
* `TCSlib.Cryptography.decodeFin_ofFn`, `TCSlib.Cryptography.padFin_ofFn` — decoding and
  padding invert `List.ofFn`; `TCSlib.Cryptography.decodeFin_eq_some_iff` — decoding succeeds
  exactly on the encoding; `TCSlib.Cryptography.ofFn_padFin_of_length` — padding a string of the
  right length keeps it.
* `TCSlib.Cryptography.ofFn_cast`, `TCSlib.Cryptography.ofFn_arrowCongr_finCongr` — a bit vector
  read across an equality of widths keeps its string.
* `TCSlib.Cryptography.FunFamily.ofFn_blocks` — block `j` of a string is its `j`-th window.
* `TCSlib.Cryptography.invProbOpt_le_invProb`, `TCSlib.Cryptography.invProbOpt_some` — the
  bridges to the concrete `invProb`.
* `TCSlib.Cryptography.invProbOpt_nonneg`, `TCSlib.Cryptography.invProbOpt_le_one` — bounds.
* `Complexity.NUPPT.computes_iff_uprob` — probability one is every coin string
  [PS10, Definition 24.6].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1–2.2: Definitions 24.6, 26.1, 27.3; §3.1–3.3: Definitions 69.4, 75.2, 78.3.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Definitions 2.1, 2.3, 3.2–3.4 (the concrete experiments).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-- The `i`-th segment of `B` bits of a coin string; a short final segment is truncated. -/
def coinBlock (B i : ℕ) (r : List Bool) : List Bool := (r.drop (i * B)).take B

/-- The defining equation of `coinBlock`: `coinBlock B i r = (r.drop (i·B)).take B`. -/
theorem coinBlock_eq (B i : ℕ) (r : List Bool) : coinBlock B i r = (r.drop (i * B)).take B := rfl

/-- A coin segment has exactly `B` bits when its end lies within the input tape. -/
theorem length_coinBlock {B i : ℕ} {r : List Bool} (h : (i + 1) * B ≤ r.length) :
    (coinBlock B i r).length = B := by
  simp only [coinBlock_eq, List.length_take, List.length_drop]
  rw [Nat.add_mul, Nat.one_mul] at h
  omega

/-- Decode a string as an `ℓ`-bit string: `some` of its bits if the length is exactly `ℓ`,
`none` otherwise (a wrong-length answer of an inverter is a failure, D5). -/
def decodeFin (ℓ : ℕ) (w : List Bool) : Option (Fin ℓ → Bool) :=
  if h : w.length = ℓ then some (fun i => w.get (Fin.cast h.symm i)) else none

/-- The defining equation of `decodeFin`: `decodeFin ℓ w` is `some` of the bits of `w` when
`|w| = ℓ`, and `none` otherwise. -/
theorem decodeFin_eq (ℓ : ℕ) (w : List Bool) :
    decodeFin ℓ w = if h : w.length = ℓ then some (fun i => w.get (Fin.cast h.symm i)) else none :=
  rfl

/-- Pad with `false` or truncate a string to exactly `ℓ` bits (the output convention of
samplers, where no failure is possible). -/
def padFin (ℓ : ℕ) (w : List Bool) : Fin ℓ → Bool := fun i => w.getD i false

/-- The defining equation of `padFin`: `padFin ℓ w = fun i => w.getD i false`. -/
theorem padFin_def (ℓ : ℕ) (w : List Bool) :
    padFin ℓ w =
      (fun i => w.getD i false :
        Fin ℓ → Bool) := rfl

/-- Bit `i` of `padFin ℓ w` is bit `i` of `w`, default `false`. -/
theorem padFin_apply (ℓ : ℕ) (w : List Bool) (i : Fin ℓ) : padFin ℓ w i = w.getD i false :=
  rfl

/-- Decoding the encoding of an `ℓ`-bit string returns it. -/
theorem decodeFin_ofFn {ℓ : ℕ} (x : Fin ℓ → Bool) : decodeFin ℓ (List.ofFn x) = some x := by
  simp [decodeFin]

/-- A decoded string has exactly the decoded length. -/
theorem length_eq_of_decodeFin_eq_some {ℓ : ℕ} {w : List Bool} {x : Fin ℓ → Bool}
    (h : decodeFin ℓ w = some x) : w.length = ℓ := by
  by_contra hw
  simp [decodeFin, hw] at h

/-- **Decoding succeeds exactly on the encoding**: `decodeFin ℓ w = some x ↔ w = List.ofFn x`,
for every width `ℓ` (`ℓ = 0` included) and every string `w`.

**Proof sketch.** A successful decoding has `|w| = ℓ` (`length_eq_of_decodeFin_eq_some`); after
substituting the width, `w = List.ofFn (w.get ·)` (`List.ofFn_get`) decodes to the bits of `w`
(`decodeFin_ofFn`), which are therefore `x`. Conversely `decodeFin_ofFn`. -/
theorem decodeFin_eq_some_iff (ℓ : ℕ) (w : List Bool) (x : Fin ℓ → Bool) :
    decodeFin ℓ w = some x ↔ w = List.ofFn x := by
  constructor
  · intro h
    have hw := length_eq_of_decodeFin_eq_some h
    subst hw
    have h' := decodeFin_ofFn (fun j : Fin w.length => w.get j)
    rw [List.ofFn_get, h, Option.some.injEq] at h'
    rw [h']
    exact (List.ofFn_get w).symm
  · rintro rfl
    exact decodeFin_ofFn x

/-- Padding the encoding of an `ℓ`-bit string returns it. -/
theorem padFin_ofFn {ℓ : ℕ} (x : Fin ℓ → Bool) : padFin ℓ (List.ofFn x) = x := by
  funext i
  simp [padFin]

/-- The encoding of `padFin L w` is `w` when `|w| = L`: `List.ofFn (padFin L w) = w`. -/
theorem ofFn_padFin_of_length {L : ℕ} {w : List Bool} (hw : w.length = L) :
    List.ofFn (padFin L w) = w := by
  refine List.ext_getElem (by simp [hw]) fun j hj₁ hj₂ => ?_
  simp [padFin_def, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj₂]

/-! ### Bit vectors across equal widths -/

/-- Reading a bit vector across an equality of widths keeps its string:
`⟦cast h f⟧ = ⟦f⟧` when `a = b`. -/
theorem ofFn_cast {a b : ℕ} (hab : a = b) (h : (Fin a → Bool) = (Fin b → Bool))
    (f : Fin a → Bool) : List.ofFn (cast h f) = List.ofFn f := by
  subst hab
  rfl

/-- Reading a vector at an equal width keeps its word:
`⟦(arrowCongr (finCongr h) (refl Bool)) v⟧ = ⟦v⟧`. -/
theorem ofFn_arrowCongr_finCongr {a b : ℕ} (h : a = b) (v : Fin a → Bool) :
    List.ofFn ((Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)) v) = List.ofFn v := by
  subst h
  rfl

/-! ### Blocks of a flat tuple -/

/-- A tuple of `q · ℓ` entries with values in an arbitrary type `X` as `q` consecutive blocks of
`ℓ` entries: block `i`, position `j` is entry `finProdFinEquiv (i, j) = j + ℓ·i` (Mathlib's
`finProdFinEquiv` and `Equiv.curry`). All `q`, `ℓ` (zero included). -/
def blocksEquivX (q ℓ : ℕ) (X : Type*) : (Fin (q * ℓ) → X) ≃ (Fin q → Fin ℓ → X) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl X)).trans (Equiv.curry _ _ _)

/-- The forward reader of `blocksEquivX`: block `i`, position `j` of `x` is entry
`finProdFinEquiv (i, j)` of `x`. -/
theorem blocksEquivX_apply (q ℓ : ℕ) {X : Type*} (x : Fin (q * ℓ) → X) (i : Fin q) (j : Fin ℓ) :
    blocksEquivX q ℓ X x i j = x (finProdFinEquiv (i, j)) := rfl

/-- The inverse of `blocksEquivX` reads block `p.divNat`, position `p.modNat`. -/
theorem blocksEquivX_symm_apply (q ℓ : ℕ) {X : Type*} (t : Fin q → Fin ℓ → X) (p : Fin (q * ℓ)) :
    (blocksEquivX q ℓ X).symm t p = t p.divNat p.modNat := rfl

/-- A string of `q · ℓ` bits as `q` consecutive blocks of `ℓ` bits (block `i` occupies the
positions `ℓ·i, …, ℓ·i + ℓ - 1`): the encoding of the tuple `(x₁, …, x_q)` of
[PS10, Theorem 35.1] as the `q·ℓ`-bit concatenation; the Bool specialization of
`blocksEquivX`. -/
def FunFamily.blocks (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool) :=
  blocksEquivX q ℓ Bool

/-- The defining equation of `blocks`: block `i`, position `j` is position `ℓ·i + j` of `x`. -/
theorem FunFamily.blocks_apply (q ℓ : ℕ) (x : Fin (q * ℓ) → Bool) (i : Fin q) (j : Fin ℓ) :
    FunFamily.blocks q ℓ x i j = x (finProdFinEquiv (i, j)) :=
  blocksEquivX_apply q ℓ x i j

/-- The inverse of `blocks` reads block `k.divNat`, position `k.modNat`. -/
theorem FunFamily.blocks_symm_apply (q ℓ : ℕ) (t : Fin q → Fin ℓ → Bool) (k : Fin (q * ℓ)) :
    (FunFamily.blocks q ℓ).symm t k = t k.divNat k.modNat :=
  blocksEquivX_symm_apply q ℓ t k

/-- **Block `j` is the `j`-th window of the string:**
`⟦FunFamily.blocks q ℓ ω j⟧ = (⟦ω⟧.drop (j·ℓ)).take ℓ`.

**Proof sketch.** Block `j` ends within the string, `j·ℓ + ℓ ≤ q·ℓ`, so both sides have `ℓ` bits.
Position `k` of block `j` is position `finProdFinEquiv (j, k) = k + ℓ·j` of `ω`
(`FunFamily.blocks_apply`), which is position `k` of the window. -/
theorem FunFamily.ofFn_blocks (q ℓ : ℕ) (ω : Fin (q * ℓ) → Bool) (j : Fin q) :
    List.ofFn (FunFamily.blocks q ℓ ω j) = ((List.ofFn ω).drop (j * ℓ)).take ℓ := by
  have hle : (j : ℕ) * ℓ + ℓ ≤ q * ℓ := by
    have := Nat.mul_le_mul_right ℓ (Nat.succ_le_of_lt j.isLt)
    rw [Nat.succ_mul] at this
    exact this
  refine List.ext_getElem ?_ fun k h₁ h₂ => ?_
  · simp only [List.length_ofFn, List.length_take, List.length_drop]
    omega
  · rw [List.getElem_ofFn, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    refine (FunFamily.blocks_apply q ℓ ω j ⟨k, _⟩).trans ?_
    congr 1
    refine Fin.ext ?_
    rw [finProdFinEquiv_apply_val]
    show k + ℓ * j = j * ℓ + k
    rw [Nat.mul_comm]
    omega

/-- `A(1^n, y)` as an inverter: output decoded as an `ℓ`-bit string, wrong length = failure
[PS10, Definitions 27.3 and 28.4, the experiment `f(A(1^n, y)) = y`].

**Deviation:** wrong-length output = failure (D5). For a typed family this loses nothing. For
a string function `f : {0,1}* → {0,1}*` the text's experiment also accepts a preimage of
another length, so the typed experiment can count fewer successes and typed one-wayness is
implied by, but weaker than, the text's, unless `|f(x)|` determines `|x|` (length-regular `f`
whose output length is a non-constant `PolyExpr`, hence injective in the input length; with
constant output length neither notion is satisfiable). The proviso is stated where string functions enter the typed world,
`FunFamily.ofString` (`Asymptotic/OneWay.lean`; gate 03a, note 15). -/
def _root_.Complexity.NUPPT.inverter (A : NUPPT) (n ℓ m : ℕ) :
    (Fin m → Bool) → A.Coins n → Option (Fin ℓ → Bool) :=
  fun y r => decodeFin ℓ (A.runAt n (List.ofFn y) r)

/-- The defining equation of `NUPPT.inverter`: the output of `A(1^n, y; r)` decoded as an
`ℓ`-bit string, `A.inverter n ℓ m y r = decodeFin ℓ (A.runAt n (List.ofFn y) r)`. -/
theorem _root_.Complexity.NUPPT.inverter_def (A : NUPPT) (n ℓ m : ℕ) (y : Fin m → Bool)
    (r : A.Coins n) : A.inverter n ℓ m y r = decodeFin ℓ (A.runAt n (List.ofFn y) r) := rfl

/-- The literal inverter `A(y)` of [PS10, Definition 26.1]: activation at parameter `|y| = m`
(the text gives the adversary `f(x)` only; the `1^{|y|}` prefix carries no information). -/
def _root_.Complexity.NUPPT.inverterLit (A : NUPPT) (ℓ m : ℕ) :
    (Fin m → Bool) → A.Coins m → Option (Fin ℓ → Bool) :=
  fun y r => decodeFin ℓ (A.runAt m (List.ofFn y) r)

/-- `A(1^n, t)` as a distinguisher: accepts iff the output is the string `[true]`
[PS10, Definition 69.4]. -/
def _root_.Complexity.NUPPT.distinguisher (A : NUPPT) (n m : ℕ) :
    (Fin m → Bool) → A.Coins n → Bool :=
  fun t r => decide (A.runAt n (List.ofFn t) r = [true])

/-- `A(1^n, w)` as a distinguisher of untyped samples (ciphertexts, views, histories). -/
def _root_.Complexity.NUPPT.distinguisherL (A : NUPPT) (n : ℕ) : List Bool → A.Coins n → Bool :=
  fun w r => decide (A.runAt n w r = [true])

/-- The defining equation of `distinguisherL`:
`A.distinguisherL n w r = decide (A.runAt n w r = [true])`. -/
theorem _root_.Complexity.NUPPT.distinguisherL_eq (A : NUPPT) (n : ℕ) (w : List Bool)
    (r : A.Coins n) : A.distinguisherL n w r = decide (A.runAt n w r = [true]) := rfl

/-- `A(1^n, y)` as a predictor of a bit: the same verdict convention as a distinguisher
[PS10, Definitions 75.2 and 78.3]. -/
def _root_.Complexity.NUPPT.predictor (A : NUPPT) (n m : ℕ) :
    (Fin m → Bool) → A.Coins n → Bool :=
  A.distinguisher n m

/-- The literal inverter is the inverter at parameter `m`. -/
theorem _root_.Complexity.NUPPT.inverterLit_eq (A : NUPPT) (ℓ m : ℕ) :
    A.inverterLit ℓ m = A.inverter m ℓ m := rfl

/-- The typed distinguisher is the untyped one on `List.ofFn t`. -/
theorem _root_.Complexity.NUPPT.distinguisher_eq (A : NUPPT) (n m : ℕ) (t : Fin m → Bool)
    (r : A.Coins n) : A.distinguisher n m t r = A.distinguisherL n (List.ofFn t) r := rfl

/-- The predictor is the distinguisher. -/
theorem _root_.Complexity.NUPPT.predictor_eq (A : NUPPT) (n m : ℕ) :
    A.predictor n m = A.distinguisher n m := rfl

/-- The inverter succeeds on `(y, r)` iff the machine's output is the encoding of some `x'`. -/
theorem _root_.Complexity.NUPPT.inverter_eq_some_iff (A : NUPPT) (n ℓ m : ℕ) (y : Fin m → Bool)
    (r : A.Coins n) (x' : Fin ℓ → Bool) :
    A.inverter n ℓ m y r = some x' ↔ A.runAt n (List.ofFn y) r = List.ofFn x' := by
  constructor
  · intro h
    have hw : (A.runAt n (List.ofFn y) r).length = ℓ := length_eq_of_decodeFin_eq_some h
    simp only [NUPPT.inverter, decodeFin, dif_pos hw, Option.some.injEq] at h
    subst h
    refine List.ext_get (by simp [hw]) fun i h₁ h₂ => ?_
    simp
  · intro h
    show decodeFin ℓ _ = _
    rw [h, decodeFin_ofFn]

/-- The probability that a possibly failing inverter `A`, given `f x` for uniform `x` and
uniform coins, outputs `some x'` with `f x' = f x` (the typed experiment of
[PS10, Definition 27.3] with a wrong-length output counted as failure, D5). -/
noncomputable def invProbOpt {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) : ℝ :=
  uprob fun z : α × ρ => ∃ x', A (f z.1) z.2 = some x' ∧ f x' = f z.1

/-- The defining equation of `invProbOpt`:
`invProbOpt f A = Pr_{(x, r)}[∃ x', A(f x, r) = some x' ∧ f x' = f x]`, over uniform
`(x, r) ∈ α × ρ`. -/
theorem invProbOpt_def {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) :
    invProbOpt f A = uprob fun z : α × ρ => ∃ x', A (f z.1) z.2 = some x' ∧ f x' = f z.1 := rfl

/-- Replacing a failure by any default can only increase the inversion probability: the
bridge from `invProbOpt` to the concrete `invProb` [Gar26, Definition 2.1]. -/
theorem invProbOpt_le_invProb {α β ρ : Type*} [Fintype α] [Fintype ρ] [Inhabited α] (f : α → β)
    (A : β → ρ → Option α) :
    invProbOpt f A ≤ invProb f (fun y r => (A y r).getD default) := by
  rw [invProbOpt_def, invProb_def]
  refine uprob_mono ?_
  rintro ⟨x, r⟩ ⟨x', hx', hf⟩
  simp [hx', hf]

/-- A total inverter has the same probability under both conventions. -/
theorem invProbOpt_some {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β) (A : β → ρ → α) :
    invProbOpt f (fun y r => some (A y r)) = invProb f A := by
  unfold invProbOpt
  simp only [invProb_def]
  congr 1
  funext z
  simp

/-- The inversion probability is nonnegative. -/
theorem invProbOpt_nonneg {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) : 0 ≤ invProbOpt f A :=
  uprob_nonneg _

/-- The inversion probability is at most one. -/
theorem invProbOpt_le_one {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) : invProbOpt f A ≤ 1 :=
  uprob_le_one _

/-- **"With probability one" is "for every coin string"** [PS10, Definition 24.6]: `A`
computes `f` in the frozen sense (`Complexity.NUPPT.Computes`, equality for every coin
string) iff at every parameter and argument the event `A(1^n, y; r) = f(⟨1^n, y⟩)` has
probability one over the uniform coins. (On a finite uniform space an event of probability
one is the whole space, `HardcoreBit.forall_of_uprob_eq_one`.) -/
theorem _root_.Complexity.NUPPT.computes_iff_uprob (A : NUPPT) (f : List Bool → List Bool) :
    A.Computes f ↔
      ∀ n y, uprob (fun r : A.Coins n => A.runAt n y r = f (NUPPT.advInput n y)) = 1 := by
  rw [NUPPT.computes_iff]
  constructor
  · intro h n y
    have hp : (fun r : A.Coins n => A.runAt n y r = f (NUPPT.advInput n y)) = fun _ => True :=
      funext fun r => propext ⟨fun _ => trivial, fun _ => h n y r⟩
    rw [hp, uprob_true]
  · intro h n y r
    exact HardcoreBit.forall_of_uprob_eq_one (h n y) r

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.Pseudorandom.Indistinguishability
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Proof infrastructure for ensembles and computational indistinguishability

The machine constructions and probability bookkeeping behind the theorems of
`TCSlib.Cryptography.Asymptotic.Ensembles` ([PS10, §3.1.1]: Lemma 71.5, the literal/`1^n`
bridges of Definition 69.4, the multicopy corollary of Lemma 71.6 and the prediction
Lemma 73.8). Everything here is ensemble-free: samplers at one parameter, `Complexity.NUPPT`
machines built by the closure calculus of `TCSlib.Complexity.Randomized.Closure`, and the
statistical-closeness device of `TCSlib.Cryptography.Asymptotic.Sampling`. The file exists
only to keep `Ensembles.lean` within the repository's size limit (workflow §4 (4)); its
declarations live in the inner namespace `TCSlib.Cryptography.EnsembleLemmas` and are not
part of the public API of the campaign.

## Main definitions

* `TCSlib.Cryptography.EnsembleLemmas.coinsEquiv` — the coin-splitting bijection
  `{0,1}^a × {0,1}^b ≃ {0,1}^m` for `m = a + b` (`Fin.appendEquiv` transported along the
  length equation).
* `TCSlib.Cryptography.EnsembleLemmas.padL` — the padded/truncated string `padFin` as a list.
* `TCSlib.Cryptography.EnsembleLemmas.blocks` — the blockwise bijection
  `{0,1}^{q·ℓ} ≃ ({0,1}^ℓ)^q` (an alias of `FunFamily.blocks`, `Asymptotic/Adversary.lean`).
* `TCSlib.Cryptography.EnsembleLemmas.CopiesLoop` — the state loop sampling `t(n)` copies
  with the challenge planted at a hard-wired position (the multicopy reduction as an FP
  function).

## Main results

* `TCSlib.Cryptography.EnsembleLemmas.acceptProb_coins_equiv`, `acceptProb_coins_fst`,
  `acceptProb_not` — reindexing the coins of a distinguisher.
* `TCSlib.Cryptography.EnsembleLemmas.distAdv_eq_zero_of_subsingleton` — no advantage on a
  one-point sample space.
* `TCSlib.Cryptography.EnsembleLemmas.exists_negRed`, `exists_pushRed`, `exists_copiesRed`
  — the machines of Lemmas 73.8, 71.5 and the multicopy corollary.
* `TCSlib.Cryptography.EnsembleLemmas.acceptProb_reparam`, `acceptProb_reparam_advice`,
  `acceptProb_pushRed`, `acceptProb_negRed` — the acceptance probabilities of the
  reparametrised and composed machines.
* `TCSlib.Cryptography.EnsembleLemmas.statClose_copies`,
  `acceptProb_multicopyRed_congr` — replacing the ideal samplers of the multicopy reduction
  by exactly distributed polynomial-time samplers.
* `TCSlib.Cryptography.EnsembleLemmas.negligible_polyExpr_mul` — a syntactic polynomial
  times a negligible function is negligible.
* `TCSlib.Cryptography.EnsembleLemmas.ofFn_padFin_eq_padL` — the string of a padded vector is
  `padL`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.1.1: Lemmas 71.5, 71.6 and 73.8.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.2 (Lemmas 3.2 and 3.3).
-/

namespace TCSlib.Cryptography.EnsembleLemmas

open Complexity Turing Finset

/-! ### Reindexing acceptance probabilities -/

section Probability

variable {σ τ γ ρ κ : Type*} [Fintype σ] [Fintype τ] [Fintype ρ] [Fintype κ]

/-- Relabelling the coin space of a distinguisher by a bijection does not change the
acceptance probability (the coin analogue of `acceptProb_comp_equiv`). -/
theorem acceptProb_coins_equiv (e : κ ≃ ρ) (X : σ → γ) (D : γ → ρ → Bool) :
    acceptProb X (fun z c => D z (e c)) = acceptProb X D :=
  uprob_eq_of_equiv ((Equiv.refl σ).prodCongr e)
    (q := fun w : σ × ρ => D (X w.1) w.2 = true) fun _ => Iff.rfl

/-- Coins the distinguisher never reads (a second, ignored coin factor) do not change the
acceptance probability. -/
theorem acceptProb_coins_fst [Nonempty κ] (X : σ → γ) (D : γ → ρ → Bool) :
    acceptProb X (fun z (c : ρ × κ) => D z c.1) = acceptProb X D :=
  (uprob_eq_of_equiv (Equiv.prodAssoc σ ρ κ).symm
    (q := fun w : (σ × ρ) × κ => D (X w.1.1) w.1.2 = true) fun _ => Iff.rfl).trans
    (uprob_fst fun w : σ × ρ => D (X w.1) w.2 = true)

/-- Negating the verdict complements the acceptance probability. -/
theorem acceptProb_not [Nonempty σ] [Nonempty ρ] (X : σ → γ) (D : γ → ρ → Bool) :
    acceptProb X (fun z c => !(D z c)) = 1 - acceptProb X D := by
  simp only [acceptProb_def]
  rw [← uprob_not]
  congr 1
  funext w
  simp

/-- The probability of a constant event on a nonempty type is its indicator. -/
theorem uprob_const {α : Type*} [Fintype α] [Nonempty α] (p : Prop) [Decidable p] :
    uprob (fun _ : α => p) = if p then 1 else 0 := by
  by_cases hp : p
  · rw [if_pos hp]
    have : (fun _ : α => p) = fun _ => True :=
      funext fun _ => propext ⟨fun _ => trivial, fun _ => hp⟩
    rw [this, uprob_true]
  · rw [if_neg hp]
    have : (fun _ : α => p) = fun _ => False := funext fun _ => propext ⟨hp, False.elim⟩
    rw [this, uprob_false]

/-- Two samplers into a subsingleton type have the same law. -/
theorem statClose_of_subsingleton [Subsingleton γ] [Nonempty σ] [Nonempty τ] (X : σ → γ)
    (Y : τ → γ) : StatClose X Y 0 := by
  classical
  intro T
  have c := X (Classical.arbitrary σ)
  have hX : ∀ s, X s = c := fun s => Subsingleton.elim _ _
  have hY : ∀ t, Y t = c := fun t => Subsingleton.elim _ _
  simp only [hX, hY, uprob_const, sub_self, abs_zero, le_refl]

/-- No distinguisher has an advantage between two samplers into a subsingleton type (the
case `t(n) = 0` of the multicopy corollary). -/
theorem distAdv_eq_zero_of_subsingleton [Subsingleton γ] [Nonempty σ] [Nonempty τ] (X : σ → γ)
    (Y : τ → γ) (D : γ → ρ → Bool) : distAdv X Y D = 0 :=
  le_antisymm (distAdv_le_of_statClose X Y (statClose_of_subsingleton X Y) D) (abs_nonneg _)

end Probability

/-! ### Coin splitting -/

/-- The coin-splitting bijection `{0,1}^a × {0,1}^b ≃ {0,1}^m` for `m = a + b`:
`Fin.appendEquiv` transported along the length equation. -/
def coinsEquiv {m a b : ℕ} (h : m = a + b) : (Fin a → Bool) × (Fin b → Bool) ≃ (Fin m → Bool) :=
  (Fin.appendEquiv a b).trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool))

/-- The coin string of a split pair is the concatenation of the two coin strings. -/
theorem ofFn_coinsEquiv {m a b : ℕ} (h : m = a + b) (c : (Fin a → Bool) × (Fin b → Bool)) :
    List.ofFn (coinsEquiv h c) = List.ofFn c.1 ++ List.ofFn c.2 := by
  rw [← List.ofFn_fin_append]
  exact (List.ofFn_congr h.symm (Fin.append c.1 c.2)).symm

/-- The first `a` coins of a split pair. -/
theorem take_ofFn_coinsEquiv {m a b : ℕ} (h : m = a + b) (c : (Fin a → Bool) × (Fin b → Bool)) :
    (List.ofFn (coinsEquiv h c)).take a = List.ofFn c.1 := by
  rw [ofFn_coinsEquiv, List.take_left' List.length_ofFn]

/-- The coins of a split pair after the first `a`. -/
theorem drop_ofFn_coinsEquiv {m a b : ℕ} (h : m = a + b) (c : (Fin a → Bool) × (Fin b → Bool)) :
    (List.ofFn (coinsEquiv h c)).drop a = List.ofFn c.2 := by
  rw [ofFn_coinsEquiv, List.drop_left' List.length_ofFn]

/-! ### Padding as an FP function -/

/-- The padded/truncated string of `padFin` as a list: exactly `k` bits, the bits of `a`
followed by `false`s. -/
def padL (k : ℕ) (a : List Bool) : List Bool := List.ofFn (padFin k a)

/-- `padL` has exactly `k` bits. -/
theorem length_padL (k : ℕ) (a : List Bool) : (padL k a).length = k := List.length_ofFn

/-- The string of a padded vector is `padL`: `⟦padFin k a⟧ = padL k a`. -/
theorem ofFn_padFin_eq_padL (k : ℕ) (a : List Bool) : List.ofFn (padFin k a) = padL k a := rfl

/-- `padL k a` is the first `k` bits of `a ++ 0^k`. -/
theorem padL_eq (k : ℕ) (a : List Bool) : padL k a = (a ++ List.replicate k false).take k := by
  refine List.ext_getElem ?_ fun i h₁ h₂ => ?_
  · simp [padL]
  · simp only [padL, List.getElem_ofFn, padFin_def, List.getD_eq_getElem?_getD, List.getElem_take,
      List.getElem_append]
    split_ifs with h
    · simp [List.getElem?_eq_getElem h]
    · simp [List.getElem?_eq_none_iff.2 (not_lt.1 h)]

/-- The all-`false` string `0^{p(|u z|)}` is polynomial-time: the bitwise xor of `1^{p(|u z|)}`
with itself (`Complexity.polyTimeComputable_pairXor`, `Complexity.polyTimeComputable_unaryPoly`). -/
theorem polyTimeComputable_zeros (p : PolyExpr) {u : List Bool → List Bool}
    (hu : PolyTimeComputable u) :
    PolyTimeComputable fun z => List.replicate (p.eval (u z).length) false := by
  have h1 := StateLoop.unaryPoly_comp p hu
  convert PolyTimeComputable.comp' polyTimeComputable_pairXor (h1.pairEncode h1) using 1
  funext z
  simp

/-- **Padding is polynomial-time:** `z ↦ padL (p(|u z|)) (a z)` for polynomial-time `u`, `a`
(the first `p(|u z|)` bits of `a z ++ 0^{p(|u z|)}`, a typed cut
`Complexity.polyTimeComputable_pairTakePoly`). -/
theorem polyTimeComputable_padL (p : PolyExpr) {u a : List Bool → List Bool}
    (hu : PolyTimeComputable u) (ha : PolyTimeComputable a) :
    PolyTimeComputable fun z => padL (p.eval (u z).length) (a z) := by
  convert PolyTimeComputable.comp' (polyTimeComputable_pairTakePoly p)
    (hu.pairEncode (ha.append (polyTimeComputable_zeros p hu))) using 1
  funext z
  simp [padL_eq]

/-! ### The negated distinguisher of the prediction lemma -/

/-- Negating a verdict (`[true] ↦ [false]`, anything else `↦ [true]`) is polynomial-time
(`Complexity.polyTimeComputable_ite` on the equality test `Complexity.polyTimeComputable_pairEq`). -/
theorem polyTimeComputable_negVerdict :
    PolyTimeComputable fun w => if w = [true] then [false] else [true] := by
  have htest : PolyTimeComputable fun w => [decide (w = [true])] := by
    convert PolyTimeComputable.comp' polyTimeComputable_pairEq
      (polyTimeComputable_id.pairEncode (polyTimeComputable_const [true])) using 1
    funext w
    simp
  convert polyTimeComputable_ite htest (polyTimeComputable_const [false])
    (polyTimeComputable_const [true]) using 1
  funext w
  simp

/-- **The negated machine** of [PS10, Lemma 73.8]: for an `NUPPT` `D` there is an `NUPPT`
`B` with the same coins outputting `[true]` iff `D` does not output `[true]`
(`Complexity.NUPPT.exists_comp` with the post-processing `polyTimeComputable_negVerdict`). -/
theorem exists_negRed (D : NUPPT) :
    ∃ B : NUPPT, B.coins = D.coins ∧
      ∀ n y r, B.runAtL n y r = if D.runAtL n y r = [true] then [false] else [true] := by
  obtain ⟨B, hc, -, -, hB⟩ := D.exists_comp polyTimeComputable_id polyTimeComputable_negVerdict
  exact ⟨B, hc, hB⟩

/-- The negated machine accepts exactly when the original rejects: its acceptance probability
is the complement. -/
theorem acceptProb_negRed {σ : Type*} [Fintype σ] [Nonempty σ] {B D : NUPPT} (hBc : B.coins = D.coins)
    (hB : ∀ n y r, B.runAtL n y r = if D.runAtL n y r = [true] then [false] else [true])
    (n m : ℕ) (X : σ → Fin m → Bool) :
    acceptProb X (B.distinguisher n m) = 1 - acceptProb X (D.distinguisher n m) := by
  have hlen : D.coinLen n = B.coinLen n := by simp [NUPPT.coinLen_eq, hBc]
  let e : D.Coins n ≃ B.Coins n := Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
  rw [← acceptProb_coins_equiv e, ← acceptProb_not]
  congr 1
  funext z c
  have hofn : List.ofFn (e c) = List.ofFn c := (List.ofFn_congr hlen c).symm
  simp only [NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq, hofn, hB]
  split_ifs <;> simp_all

/-! ### Parameter changes -/

/-- The acceptance probability of `NUPPT.exists_reparam D p` at parameter `n` is that of `D`
at parameter `p(n)`: the coin types correspond along `PolyExpr.eval_subst`. -/
theorem acceptProb_reparam {σ : Type*} [Fintype σ] {B D : NUPPT} {p : PolyExpr}
    (hBc : B.coins = D.coins.subst p) (hB : ∀ n y r, B.runAtL n y r = D.runAtL (p.eval n) y r)
    (n m : ℕ) (X : σ → Fin m → Bool) :
    acceptProb X (B.distinguisher n m) = acceptProb X (D.distinguisher (p.eval n) m) := by
  have hlen : D.coinLen (p.eval n) = B.coinLen n := by
    simp [NUPPT.coinLen_eq, hBc, PolyExpr.eval_subst]
  let e : D.Coins (p.eval n) ≃ B.Coins n := Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
  rw [← acceptProb_coins_equiv e]
  congr 1
  funext z c
  have hofn : List.ofFn (e c) = List.ofFn c := (List.ofFn_congr hlen c).symm
  simp only [NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq, hofn, hB]

/-- The acceptance probability of `NUPPT.exists_reparam_advice D φ p` at parameter `m` is that
of `D` at parameter `φ m`: the unread coins are an independent uniform factor
(`acceptProb_coins_fst`) after the split `coinsEquiv`. -/
theorem acceptProb_reparam_advice {σ : Type*} [Fintype σ] {A D : NUPPT} {φ : ℕ → ℕ} {p : PolyExpr}
    (hAc : A.coins = D.coins.subst p)
    (hA : ∀ n y r, A.runAtL n y r = D.runAtL (φ n) y (r.take (D.coinLen (φ n))))
    (m : ℕ) (hle : D.coinLen (φ m) ≤ D.coinLen (p.eval m)) (k : ℕ) (X : σ → Fin k → Bool) :
    acceptProb X (A.distinguisher m k) = acceptProb X (D.distinguisher (φ m) k) := by
  have hlen : A.coinLen m = D.coinLen (φ m) + (D.coinLen (p.eval m) - D.coinLen (φ m)) := by
    have : A.coinLen m = D.coinLen (p.eval m) := by
      simp [NUPPT.coinLen_eq, hAc, PolyExpr.eval_subst]
    omega
  rw [← acceptProb_coins_equiv (coinsEquiv hlen)]
  conv_rhs => rw [← acceptProb_coins_fst (κ := Fin (D.coinLen (p.eval m) - D.coinLen (φ m)) → Bool)
    X (D.distinguisher (φ m) k)]
  congr 1
  funext z c
  simp only [NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq, hA,
      take_ofFn_coinsEquiv]

/-! ### The machine of Lemma 71.5 -/

/-- **The machine of [PS10, Lemma 71.5]:** for `NUPPT`s `M`, `D` and an output length `ℓ'`
there is an `NUPPT` `B` with coins `M.coins + D.coins` that runs `M` on its input with the
first `M.coins n` coins, pads the result to `ℓ'(n)` bits and hands it to `D` with the remaining
coins. The padding is done inside the raw function of the layout, where `1^n` is available
(run-3 audit note P2-4: `NUPPT.exists_comp` sees only `y`).

**Proof sketch.** As `Complexity.NUPPT.exists_seq`: advice `combineAdvice (M.advice n) (D.advice n)`;
the raw function cuts the coins at `M.coins(|1^n|)` (`polyTimeComputable_pairTakePoly`/`pairDropPoly`),
runs `M.output` on `layout (inParam z) (inArg z) (pairFstD (inAdvice z)) r₁`, pads with
`polyTimeComputable_padL ℓ'` against `inParam z`, and runs `D.output` on
`layout (inParam z) (padded) (pairSndD (inAdvice z)) r₂`; the equation is
`NUPPT.runAtL_ofPolyTime` plus the projection identities. -/
theorem exists_pushRed (M D : NUPPT) (ℓ' : PolyExpr) :
    ∃ B : NUPPT, B.coins = .add M.coins D.coins ∧
      ∀ n y r, B.runAtL n y r =
        D.runAtL n (padL (ℓ'.eval n) (M.runAtL n y (r.take (M.coinLen n)))) (r.drop (M.coinLen n)) := by
  have hcut := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins
  have hr₁ := PolyTimeComputable.comp' (polyTimeComputable_pairTakePoly M.coins) hcut
  have hr₂ := PolyTimeComputable.comp' (polyTimeComputable_pairDropPoly M.coins) hcut
  have ha := PolyTimeComputable.comp' M.polyTimeComputable_output
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam
      NUPPT.polyTimeComputable_inArg
      (PolyTimeComputable.comp' polyTimeComputable_pairFstD NUPPT.polyTimeComputable_inAdvice) hr₁)
  have hpad := polyTimeComputable_padL ℓ' NUPPT.polyTimeComputable_inParam ha
  have hF := PolyTimeComputable.comp' D.polyTimeComputable_output
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam hpad
      (PolyTimeComputable.comp' polyTimeComputable_pairSndD NUPPT.polyTimeComputable_inAdvice) hr₂)
  have hadv : ∀ n, (NUPPT.combineAdvice (M.advice n) (D.advice n)).length ≤
      (PolyExpr.add (.add (.mul (.const 2) M.adv) (.const 2)) D.adv).eval n := fun n => by
    have h₁ := NUPPT.length_combineAdvice_le (M.advice n) (D.advice n)
    have h₂ := M.advice_length n
    have h₃ := D.advice_length n
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega
  refine ⟨NUPPT.ofPolyTime hF (.add M.coins D.coins) _
    (fun n => NUPPT.combineAdvice (M.advice n) (D.advice n)) hadv, rfl, fun n y r => ?_⟩
  rw [NUPPT.runAtL_ofPolyTime]
  simp [NUPPT.runAtL_eq, NUPPT.advInput_eq, NUPPT.coinLen_eq, NUPPT.layout_eq, NUPPT.inParam_eq,
      NUPPT.inArg_eq,
    NUPPT.inAdvice_eq, NUPPT.inCoins_eq]

/-- The acceptance probability of the machine of `exists_pushRed` on a sampler `X` is the
acceptance probability of `D` on the pushed sampler `(s, c) ↦ padFin (ℓ' n) (M(1^n, X s; c))`
(`acceptProb_bind` after the coin split `coinsEquiv`). -/
theorem acceptProb_pushRed {σ : Type*} [Fintype σ] {M D B : NUPPT} {ℓ' : PolyExpr}
    (hBc : B.coins = .add M.coins D.coins)
    (hB : ∀ n y r, B.runAtL n y r =
      D.runAtL n (padL (ℓ'.eval n) (M.runAtL n y (r.take (M.coinLen n)))) (r.drop (M.coinLen n)))
    (n m : ℕ) (X : σ → Fin m → Bool) :
    acceptProb X (B.distinguisher n m) =
      acceptProb (fun z : σ × M.Coins n => padFin (ℓ'.eval n) (M.runAt n (List.ofFn (X z.1)) z.2))
        (D.distinguisher n (ℓ'.eval n)) := by
  have hlen : B.coinLen n = M.coinLen n + D.coinLen n := by simp [NUPPT.coinLen_eq, hBc]
  rw [← acceptProb_coins_equiv (coinsEquiv hlen),
    ← acceptProb_bind X (fun t c => padFin (ℓ'.eval n) (M.runAt n (List.ofFn t) c))
      (D.distinguisher n (ℓ'.eval n))]
  congr 1
  funext z c
  simp only [NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq, hB,
      take_ofFn_coinsEquiv, drop_ofFn_coinsEquiv,
    padL]

/-! ### Negligible functions and syntactic polynomials -/

/-- A syntactic polynomial times a negligible function is negligible: `p(n) ≤ C(n+1)^c ≤
C 2^c n^c` for `n ≥ 1` (`PolyExpr.eval_le`), then `Negligible.mul_pow` and
`Negligible.const_mul`. -/
theorem negligible_polyExpr_mul (p : PolyExpr) {μ : ℕ → ℝ} (hμ : Negligible μ) :
    Negligible fun n => (p.eval n : ℝ) * μ n := by
  obtain ⟨C, e, hCe⟩ := p.eval_le
  refine ((hμ.mul_pow e).const_mul ((C * 2 ^ e : ℕ) : ℝ)).mono ⟨1, fun n hn => ?_⟩
  have hp : (0 : ℝ) ≤ p.eval n := by positivity
  have hC : (0 : ℝ) ≤ ((C * 2 ^ e : ℕ) : ℝ) := by positivity
  have hne : (0 : ℝ) ≤ (n : ℝ) ^ e := by positivity
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hC, abs_of_nonneg hne]
  have h1 : (p.eval n : ℝ) ≤ (C : ℝ) * ((n : ℝ) + 1) ^ e := by exact_mod_cast hCe n
  have h2 : ((n : ℝ) + 1) ^ e ≤ (2 * (n : ℝ)) ^ e := by
    apply pow_le_pow_left₀ (by positivity)
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  calc (p.eval n : ℝ) * |μ n| ≤ (C : ℝ) * (2 * (n : ℝ)) ^ e * |μ n| :=
        mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity)))
          (abs_nonneg _)
    _ = ((C * 2 ^ e : ℕ) : ℝ) * ((n : ℝ) ^ e * |μ n|) := by push_cast; ring

/-! ### Blocks and chunks -/

/-- The blockwise bijection `{0,1}^{q·ℓ} ≃ ({0,1}^ℓ)^q`: a compatibility alias of the canonical
Bool block bijection `FunFamily.blocks` of `Asymptotic/Adversary.lean` (block `i`, bit `j` is bit
`finProdFinEquiv (i, j) = j + ℓ·i` of the string). -/
def blocks (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool) :=
  FunFamily.blocks q ℓ

/-- `blocks` is the canonical block bijection: `blocks q ℓ = FunFamily.blocks q ℓ`. -/
theorem blocks_eq (q ℓ : ℕ) : blocks q ℓ = FunFamily.blocks q ℓ := rfl

/-- Block `i`, bit `j` of `w` is bit `finProdFinEquiv (i, j)` (`FunFamily.blocks_apply`). -/
theorem blocks_apply (q ℓ : ℕ) (w : Fin (q * ℓ) → Bool) (i : Fin q) (j : Fin ℓ) :
    blocks q ℓ w i j = w (finProdFinEquiv (i, j)) :=
  FunFamily.blocks_apply q ℓ w i j

/-- Bit `x` of `(blocks q ℓ).symm V` is bit `(finProdFinEquiv.symm x).2` of block
`(finProdFinEquiv.symm x).1` (`FunFamily.blocks_symm_apply`, `finProdFinEquiv_symm_apply`). -/
theorem blocks_symm_apply (q ℓ : ℕ) (V : Fin q → Fin ℓ → Bool) (x : Fin (q * ℓ)) :
    (blocks q ℓ).symm V x = V (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2 := by
  rw [blocks_eq, FunFamily.blocks_symm_apply, finProdFinEquiv_symm_apply]

/-- The index `i·ℓ + j` decodes to block `i`, bit `j`. -/
theorem finProdFinEquiv_symm_mk {q ℓ : ℕ} (i : Fin q) (j : Fin ℓ) (h : i * ℓ + j < q * ℓ) :
    finProdFinEquiv.symm (⟨i * ℓ + j, h⟩ : Fin (q * ℓ)) = (i, j) := by
  rw [Equiv.symm_apply_eq]
  ext
  simp [finProdFinEquiv_apply_val]
  ring

/-- The `i`-th chunk of `s` bits of the string of a `q·s`-bit word is its block `i`. -/
theorem take_drop_ofFn_blocks {q s : ℕ} (w : Fin (q * s) → Bool) (i : ℕ) (hi : i < q) :
    ((List.ofFn w).drop (i * s)).take s = List.ofFn (blocks q s w ⟨i, hi⟩) := by
  have hle : i * s + s ≤ q * s := by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right s hi
  refine List.ext_getElem ?_ fun j h₁ h₂ => ?_
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn, blocks_apply]
    congr 1
    ext
    simp [finProdFinEquiv_apply_val]
    ring

/-- The string of `(blocks q ℓ).symm V` is the concatenation of the `q` block strings
(`List.ofFn_mul`). -/
theorem ofFn_blocks_symm {q ℓ : ℕ} (V : Fin q → Fin ℓ → Bool) (F : ℕ → List Bool)
    (hF : ∀ i (h : i < q), F i = List.ofFn (V ⟨i, h⟩)) :
    List.ofFn ((blocks q ℓ).symm V) = (List.range q).flatMap F := by
  rw [List.ofFn_mul, List.flatMap_def, ← List.map_coe_finRange, List.map_map, List.ofFn_eq_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  rw [Function.comp_apply, hF i i.isLt]
  congr 1
  funext j
  rw [blocks_symm_apply, finProdFinEquiv_symm_mk]

/-- The concatenation of `q` chunks of `ℓ` bits has `q·ℓ` bits. -/
theorem length_flatMap_range (F : ℕ → List Bool) {q ℓ : ℕ} (hF : ∀ i < q, (F i).length = ℓ) :
    ((List.range q).flatMap F).length = q * ℓ := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append,
      ih fun i hi => hF i (Nat.lt_succ_of_lt hi), List.flatMap_singleton,
      hF q (Nat.lt_succ_self q), Nat.succ_mul]

/-- Truncating the concatenation of `m ≥ q` chunks to `q·ℓ` bits keeps the first `q` chunks. -/
theorem take_flatMap_range (F : ℕ → List Bool) {q m ℓ : ℕ} (hq : q ≤ m)
    (hF : ∀ i < q, (F i).length = ℓ) :
    ((List.range m).flatMap F).take (q * ℓ) = (List.range q).flatMap F := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hq
  rw [List.range_add, List.flatMap_append, List.take_left' (length_flatMap_range F hF)]

/-! ### Exactly distributed samplers under `copies` -/

/-- Splitting a tuple into its head and its tail. -/
def consSplit (κ : Type*) (t : ℕ) : (Fin (t + 1) → κ) ≃ κ × (Fin t → κ) where
  toFun f := (f 0, Fin.tail f)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by
    ext <;> simp [Fin.tail_cons]

/-- Exactly distributed samplers stay exactly distributed under `copies`.

**Proof sketch.** Induction on the number of copies `t`. For `t = 0` both samplers take
values in the one-point type `Fin 0 → γ` (`statClose_of_subsingleton`). For `t + 1`,
`StatClose.prod` of the hypothesis with the induction hypothesis gives the pair sampler
`c ↦ (X' (c 0), copies t X' (tail c))`, `StatClose.map` with `Fin.cons` reassembles the
tuple, and `consSplit` reindexes both seed spaces along `(Fin (t+1) → κ) ≃ κ × (Fin t → κ)`;
the composite is `copies (t + 1)` by `Fin.cases`. -/
theorem statClose_copies {κ σ γ : Type*} [Fintype κ] [Fintype σ] {X' : κ → γ} {X : σ → γ}
    (h : StatClose X' X 0) : ∀ t : ℕ, StatClose (copies t X') (copies t X) 0
  | 0 => statClose_of_subsingleton _ _
  | t + 1 => by
    have hp := (h.prod (statClose_copies h t)).map
      fun p : γ × (Fin t → γ) => (Fin.cons p.1 p.2 : Fin (t + 1) → γ)
    rw [add_zero] at hp
    have e := (hp.comp_equiv_left (consSplit κ t)).comp_equiv_right (consSplit σ t)
    have h1 : copies (t + 1) X' =
        fun f => Fin.cons (X' ((consSplit κ t) f).1) (copies t X' ((consSplit κ t) f).2) := by
      funext f i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [copies_def, consSplit]
      · simp [copies_def, consSplit, Fin.tail_def]
    have h2 : copies (t + 1) X =
        fun f => Fin.cons (X ((consSplit σ t) f).1) (copies t X ((consSplit σ t) f).2) := by
      funext f i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [copies_def, consSplit]
      · simp [copies_def, consSplit, Fin.tail_def]
    rw [h1, h2]
    exact e

/-- Reindexing `ζ × (S × ρ) ≃ S × (ζ × ρ)`. -/
def swapAux (ζ S ρ : Type*) : ζ × (S × ρ) ≃ S × (ζ × ρ) where
  toFun w := (w.2.1, (w.1, w.2.2))
  invFun v := (v.2.1, (v.1, v.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Replacing the ideal samplers of the multicopy reduction by exactly distributed ones**
leaves the acceptance probability unchanged: the other `t − 1` copies are drawn from
`X'`, `Y'` (statistically identical to `X`, `Y`), the challenge `Z` and the coins of `D` are
auxiliary coins (`StatClose.abs_uprob_sub_le_prod` at `δ = 0` after `statClose_copies` and
`StatClose.prod`). -/
theorem acceptProb_multicopyRed_congr {κX κY σ τ ζ γ ρ : Type*} [Fintype κX] [Fintype κY]
    [Fintype σ] [Fintype τ] [Fintype ζ] [Fintype ρ] {X' : κX → γ} {X : σ → γ} {Y' : κY → γ}
    {Y : τ → γ} (hX : StatClose X' X 0) (hY : StatClose Y' Y 0) (Z : ζ → γ) (t k : ℕ)
    (D : (Fin t → γ) → ρ → Bool) :
    acceptProb Z (multicopyRed X' Y' t k D) = acceptProb Z (multicopyRed X Y t k D) := by
  have hG := (statClose_copies hX t).prod (statClose_copies hY t)
  rw [add_zero] at hG
  have key := hG.abs_uprob_sub_le_prod fun (uv : (Fin t → γ) × (Fin t → γ)) (w : ζ × ρ) =>
    D (fun i => if (i : ℕ) < k then uv.2 i else if (i : ℕ) = k then Z w.1 else uv.1 i) w.2 = true
  rw [abs_nonpos_iff, sub_eq_zero] at key
  calc acceptProb Z (multicopyRed X' Y' t k D)
      = uprob fun v : ((Fin t → κX) × (Fin t → κY)) × (ζ × ρ) =>
          D (fun i => if (i : ℕ) < k then copies t Y' v.1.2 i
            else if (i : ℕ) = k then Z v.2.1 else copies t X' v.1.1 i) v.2.2 = true :=
        uprob_eq_of_equiv (swapAux ζ ((Fin t → κX) × (Fin t → κY)) ρ) fun _ => Iff.rfl
    _ = uprob fun v : ((Fin t → σ) × (Fin t → τ)) × (ζ × ρ) =>
          D (fun i => if (i : ℕ) < k then copies t Y v.1.2 i
            else if (i : ℕ) = k then Z v.2.1 else copies t X v.1.1 i) v.2.2 = true := key
    _ = acceptProb Z (multicopyRed X Y t k D) :=
        (uprob_eq_of_equiv (swapAux ζ ((Fin t → σ) × (Fin t → τ)) ρ) fun _ => Iff.rfl).symm

/-! ### The sampler loop of the multicopy reduction -/

namespace CopiesLoop

/-- The parameter slot `u` of the state word `⟨u, ⟨cnt, ⟨kk, ⟨z, ⟨rX, rY⟩⟩⟩⟩⟩`. -/
def p₁ (w : List Bool) : List Bool := pairFstD w

/-- The unary round counter `cnt` of the state word. -/
def p₂ (w : List Bool) : List Bool := pairFstD (pairSndD w)

/-- The unary hybrid index `kk` of the state word. -/
def p₃ (w : List Bool) : List Bool := pairFstD (pairSndD (pairSndD w))

/-- The challenge `z` of the state word. -/
def p₄ (w : List Bool) : List Bool := pairFstD (pairSndD (pairSndD (pairSndD w)))

/-- The remaining coins `rX` for the copies of `X`. -/
def p₅ (w : List Bool) : List Bool := pairFstD (pairSndD (pairSndD (pairSndD (pairSndD w))))

/-- The remaining coins `rY` for the copies of `Y`. -/
def p₆ (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD (pairSndD (pairSndD w))))

/-- The state word `⟨u, ⟨cnt, ⟨kk, ⟨z, ⟨rX, rY⟩⟩⟩⟩⟩`. -/
def st (u cnt kk z rX rY : List Bool) : List Bool :=
  pairEncode u (pairEncode cnt (pairEncode kk (pairEncode z (pairEncode rX rY))))

/-- Reading the parameter slot. -/
@[simp] theorem p₁_st (u cnt kk z rX rY : List Bool) : p₁ (st u cnt kk z rX rY) = u := by
  simp [p₁, st]

/-- Reading the counter. -/
@[simp] theorem p₂_st (u cnt kk z rX rY : List Bool) : p₂ (st u cnt kk z rX rY) = cnt := by
  simp [p₂, st]

/-- Reading the hybrid index. -/
@[simp] theorem p₃_st (u cnt kk z rX rY : List Bool) : p₃ (st u cnt kk z rX rY) = kk := by
  simp [p₃, st]

/-- Reading the challenge. -/
@[simp] theorem p₄_st (u cnt kk z rX rY : List Bool) : p₄ (st u cnt kk z rX rY) = z := by
  simp [p₄, st]

/-- Reading the coins for `X`. -/
@[simp] theorem p₅_st (u cnt kk z rX rY : List Bool) : p₅ (st u cnt kk z rX rY) = rX := by
  simp [p₅, st]

/-- Reading the coins for `Y`. -/
@[simp] theorem p₆_st (u cnt kk z rX rY : List Bool) : p₆ (st u cnt kk z rX rY) = rY := by
  simp [p₆, st]

/-- The projections are polynomial-time. -/
theorem p₁_poly : PolyTimeComputable p₁ := polyTimeComputable_pairFstD

/-- The projections are polynomial-time. -/
theorem p₂_poly : PolyTimeComputable p₂ :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- The projections are polynomial-time. -/
theorem p₃_poly : PolyTimeComputable p₃ :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The projections are polynomial-time. -/
theorem p₄_poly : PolyTimeComputable p₄ :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))

/-- The projections are polynomial-time. -/
theorem p₅_poly : PolyTimeComputable p₅ :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)))

/-- The projections are polynomial-time. -/
theorem p₆_poly : PolyTimeComputable p₆ :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)))

/-- Assembling a state word from six polynomial-time components is polynomial-time. -/
theorem st_poly {f₁ f₂ f₃ f₄ f₅ f₆ : List Bool → List Bool} (h₁ : PolyTimeComputable f₁)
    (h₂ : PolyTimeComputable f₂) (h₃ : PolyTimeComputable f₃) (h₄ : PolyTimeComputable f₄)
    (h₅ : PolyTimeComputable f₅) (h₆ : PolyTimeComputable f₆) :
    PolyTimeComputable fun z => st (f₁ z) (f₂ z) (f₃ z) (f₄ z) (f₅ z) (f₆ z) :=
  h₁.pairEncode (h₂.pairEncode (h₃.pairEncode (h₄.pairEncode (h₅.pairEncode h₆))))

/-- `2|fst z| + |snd z| ≤ |z|` for every word (equality plus two on pairs, `0 ≤ |z|` on
malformed words). -/
theorem two_mul_length_pairFstD_add_le (z : List Bool) :
    2 * (pairFstD z).length + (pairSndD z).length ≤ z.length := by
  cases h : pairDecode z with
  | none => simp [pairFstD_eq, pairSndD_eq, h]
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have hz := eq_pairEncode_of_pairDecode z a b h
    subst hz
    rw [pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode]
    omega

variable (sX sY : PolyExpr)

/-- The step: append a token to the counter and drop one chunk from each coin string
(`sX(|u|)` bits of `rX`, `sY(|u|)` bits of `rY`). -/
def step (w : List Bool) : List Bool :=
  st (p₁ w) (true :: p₂ w) (p₃ w) (p₄ w) ((p₅ w).drop (sX.eval (p₁ w).length))
    ((p₆ w).drop (sY.eval (p₁ w).length))

/-- The step is polynomial-time (`Complexity.polyTimeComputable_pairDropPoly` on `⟨u, rX⟩`,
`⟨u, rY⟩`). -/
theorem step_poly : PolyTimeComputable (step sX sY) := by
  convert st_poly p₁_poly (PolyTimeComputable.comp' (StateLoop.cons_poly true)
      p₂_poly) p₃_poly p₄_poly
    (PolyTimeComputable.comp' (polyTimeComputable_pairDropPoly sX) (p₁_poly.pairEncode p₅_poly))
    (PolyTimeComputable.comp' (polyTimeComputable_pairDropPoly sY)
        (p₁_poly.pairEncode p₆_poly)) using 1
  funext w
  simp [step]

/-- One step grows a word by at most `12` symbols (the pairing overhead; the coins only
shrink). -/
theorem length_step_le (w : List Bool) : (step sX sY w).length ≤ w.length + 12 := by
  have h₁ := two_mul_length_pairFstD_add_le w
  have h₂ := two_mul_length_pairFstD_add_le (pairSndD w)
  have h₃ := two_mul_length_pairFstD_add_le (pairSndD (pairSndD w))
  have h₄ := two_mul_length_pairFstD_add_le (pairSndD (pairSndD (pairSndD w)))
  have h₅ := two_mul_length_pairFstD_add_le (pairSndD (pairSndD (pairSndD (pairSndD w))))
  have d₅ : ((p₅ w).drop (sX.eval (p₁ w).length)).length ≤ (p₅ w).length := by simp
  have d₆ : ((p₆ w).drop (sY.eval (p₁ w).length)).length ≤ (p₆ w).length := by simp
  simp only [step, st, length_pairEncode, List.length_cons, p₁, p₂, p₃, p₄, p₅, p₆] at *
  omega

/-- The orbit of any word grows at most linearly in the number of rounds. -/
theorem length_iterate_step_le (w : List Bool) (i : ℕ) :
    ((step sX sY)^[i] w).length ≤ w.length + 12 * i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have := length_step_le sX sY ((step sX sY)^[i] w)
    omega

/-- The closed form of the orbit from `⟨u, ⟨[], ⟨kk, ⟨z, ⟨rX, rY⟩⟩⟩⟩⟩`: after `i` rounds the
counter is `1^i` and `i` chunks have been dropped from each coin string. -/
theorem iterate_step (u kk z rX rY : List Bool) (i : ℕ) :
    (step sX sY)^[i] (st u [] kk z rX rY) =
      st u (List.replicate i true) kk z (rX.drop (i * sX.eval u.length))
        (rY.drop (i * sY.eval u.length)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [step, List.replicate_succ, List.drop_drop, Nat.succ_mul]

variable (SX SY : List Bool → List Bool) (ℓ : PolyExpr)

/-- The emission at a state word: a padded sample of `Y` from the next `sY(|u|)` coins while
the counter is below the hybrid index, the challenge `z` at the hybrid index, and a padded
sample of `X` from the next `sX(|u|)` coins afterwards. -/
def emit (w : List Bool) : List Bool :=
  if (p₂ w).length < (p₃ w).length then
    padL (ℓ.eval (p₁ w).length) (SY (pairEncode (p₁ w) ((p₆ w).take (sY.eval (p₁ w).length))))
  else if (p₂ w).length = (p₃ w).length then p₄ w
  else padL (ℓ.eval (p₁ w).length) (SX (pairEncode (p₁ w) ((p₅ w).take (sX.eval (p₁ w).length))))

/-- The emission is polynomial-time: two length tests (`StateLoop.lenLe_comp`,
`Complexity.polyTimeComputable_lenEq`), two padded sampler calls (`polyTimeComputable_padL`,
`Complexity.polyTimeComputable_pairTakePoly`) and `Complexity.polyTimeComputable_ite`. -/
theorem emit_poly (hSX : PolyTimeComputable SX) (hSY : PolyTimeComputable SY) :
    PolyTimeComputable (emit sX sY SX SY ℓ) := by
  have hlt : PolyTimeComputable fun w => [decide ((p₂ w).length < (p₃ w).length)] := by
    exact StateLoop.lenLe_comp p₃_poly (PolyTimeComputable.comp' (StateLoop.cons_poly true) p₂_poly)
  have heq : PolyTimeComputable fun w => [decide ((p₂ w).length = (p₃ w).length)] := by
    convert PolyTimeComputable.comp' polyTimeComputable_lenEq (p₂_poly.pairEncode p₃_poly) using 1
    funext w
    simp
  have hY := polyTimeComputable_padL ℓ p₁_poly (PolyTimeComputable.comp' hSY (p₁_poly.pairEncode
    (PolyTimeComputable.comp' (polyTimeComputable_pairTakePoly sY) (p₁_poly.pairEncode p₆_poly))))
  have hX := polyTimeComputable_padL ℓ p₁_poly (PolyTimeComputable.comp' hSX (p₁_poly.pairEncode
    (PolyTimeComputable.comp' (polyTimeComputable_pairTakePoly sX) (p₁_poly.pairEncode p₅_poly))))
  convert polyTimeComputable_ite hlt hY (polyTimeComputable_ite heq p₄_poly hX) using 1
  funext w
  simp [emit]

/-- The emission at a genuine state word with unary parameter, counter and index. -/
theorem emit_st (n cnt k : ℕ) (z rX rY : List Bool) :
    emit sX sY SX SY ℓ
        (st (List.replicate n true) (List.replicate cnt true) (List.replicate k true) z rX rY) =
      if cnt < k then
        padL (ℓ.eval n) (SY (pairEncode (List.replicate n true) (rY.take (sY.eval n))))
      else if cnt = k then z
      else padL (ℓ.eval n) (SX (pairEncode (List.replicate n true) (rX.take (sX.eval n)))) := by
  simp [emit]

variable (t : PolyExpr)

/-- The loop output: the `t(|x|) + 1` emissions along the orbit of `x`, concatenated. -/
def loopOut (x : List Bool) : List Bool :=
  (List.range (t.eval x.length + 1)).flatMap fun i => emit sX sY SX SY ℓ ((step sX sY)^[i] x)

/-- The loop output is polynomial-time (`Complexity.polyTimeComputable_iterateEmit` with the
orbit bound `|x| + 12 t(|x|)`). -/
theorem loopOut_poly (hSX : PolyTimeComputable SX) (hSY : PolyTimeComputable SY) :
    PolyTimeComputable (loopOut sX sY SX SY ℓ t) := by
  unfold loopOut
  refine polyTimeComputable_iterateEmit (step_poly sX sY) (emit_poly sX sY SX SY ℓ hSX hSY) t
    (.add .var (.mul (.const 12) t)) fun x i hi => ?_
  have h := length_iterate_step_le sX sY x i
  have h' : 12 * i ≤ 12 * t.eval x.length := Nat.mul_le_mul_left 12 hi
  simp only [PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_mul, PolyExpr.eval_const]
  omega

/-- The loop output on the genuine initial state: chunk `i` is a padded sample of `Y` from
the `i`-th chunk of `rY` below the index `k`, the challenge at `k`, and a padded sample of `X`
from the `i`-th chunk of `rX` above `k`. -/
theorem loopOut_st (n k : ℕ) (z rX rY : List Bool) :
    loopOut sX sY SX SY ℓ t (st (List.replicate n true) [] (List.replicate k true) z rX rY) =
      (List.range (t.eval (st (List.replicate n true) [] (List.replicate k true) z rX rY).length
        + 1)).flatMap fun i =>
          if i < k then
            padL (ℓ.eval n) (SY (pairEncode (List.replicate n true)
              ((rY.drop (i * sY.eval n)).take (sY.eval n))))
          else if i = k then z
          else padL (ℓ.eval n) (SX (pairEncode (List.replicate n true)
            ((rX.drop (i * sX.eval n)).take (sX.eval n)))) := by
  unfold loopOut
  congr 1
  funext i
  rw [iterate_step, emit_st]
  simp

end CopiesLoop

/-- The initial state of the sampler loop as a function of the raw layout
`⟨⟨⟨1^n, ⟨z, 1^k⟩⟩, α⟩, r⟩`: `⟨1^n, ⟨[], ⟨1^k, ⟨z, ⟨r.take (t·sX)(n), r.drop (t·sX)(n)⟩⟩⟩⟩⟩`. -/
def copiesInit (sX t : PolyExpr) (w : List Bool) : List Bool :=
  CopiesLoop.st (NUPPT.inParam w) [] (pairSndD (NUPPT.inArg w)) (pairFstD (NUPPT.inArg w))
    ((NUPPT.inCoins w).take ((PolyExpr.mul t sX).eval (NUPPT.inParam w).length))
    ((NUPPT.inCoins w).drop ((PolyExpr.mul t sX).eval (NUPPT.inParam w).length))

/-- The initial state is polynomial-time in the raw layout. -/
theorem copiesInit_poly (sX t : PolyExpr) : PolyTimeComputable (copiesInit sX t) := by
  have hcut := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins
  convert CopiesLoop.st_poly NUPPT.polyTimeComputable_inParam (polyTimeComputable_const [])
    (PolyTimeComputable.comp' polyTimeComputable_pairSndD NUPPT.polyTimeComputable_inArg)
    (PolyTimeComputable.comp' polyTimeComputable_pairFstD NUPPT.polyTimeComputable_inArg)
    (PolyTimeComputable.comp' (polyTimeComputable_pairTakePoly (.mul t sX)) hcut)
    (PolyTimeComputable.comp' (polyTimeComputable_pairDropPoly (.mul t sX)) hcut) using 1
  funext w
  simp [copiesInit]

/-- The raw function of the sampler machine: the loop output on the initial state, truncated
to `t(n)·ℓ(n)` bits. -/
def copiesSampler (SX SY : List Bool → List Bool) (sX sY ℓ t : PolyExpr) (w : List Bool) :
    List Bool :=
  (CopiesLoop.loopOut sX sY SX SY ℓ t (copiesInit sX t w)).take
    ((PolyExpr.mul t ℓ).eval (NUPPT.inParam w).length)

/-- The sampler function is polynomial-time. -/
theorem copiesSampler_poly {SX SY : List Bool → List Bool} (hSX : PolyTimeComputable SX)
    (hSY : PolyTimeComputable SY) (sX sY ℓ t : PolyExpr) :
    PolyTimeComputable (copiesSampler SX SY sX sY ℓ t) := by
  convert PolyTimeComputable.comp' (polyTimeComputable_pairTakePoly (.mul t ℓ))
    (NUPPT.polyTimeComputable_inParam.pairEncode
      (PolyTimeComputable.comp' (CopiesLoop.loopOut_poly sX sY SX SY ℓ t hSX hSY)
          (copiesInit_poly sX t))) using 1
  funext w
  simp [copiesSampler]

/-- **The machine of the multicopy corollary** [PS10, Lemma 71.6; Gar26, Lemma 3.3]: for an
`NUPPT` `D`, polynomial-time samplers `SX`, `SY` with seed lengths `sX`, `sY`, a sample length
`ℓ`, a number of copies `t` and a hybrid index `k n ≤ t n`, there is an `NUPPT` `B` with coins
`t·sX + t·sY + D.coins` that on the challenge `z` and the coins `⟨cX, cY⟩ ++ cD` (the coins of
the samplers in blocks, then the coins of `D`) runs `D` on the tuple with the `i`-th position
holding a padded sample of `Y` from `cY i` for `i < k n`, the challenge at `i = k n`, and a
padded sample of `X` from `cX i` for `i > k n`.

**Proof sketch.** The uniform sampler machine `M₀ := ofPolyTimeUniform copiesSampler_poly`
runs the state loop `CopiesLoop` on `⟨1^n, ⟨[], ⟨1^k, ⟨z, ⟨rX, rY⟩⟩⟩⟩⟩` for `t(|x|) + 1 ≥ t(n)`
rounds and truncates to `t(n)·ℓ(n)` bits (`take_flatMap_range`); the `i`-th chunk is the
`i`-th block of the coins (`take_drop_ofFn_blocks`) and the concatenation of the blocks is the
string of `(blocks t ℓ).symm` (`ofFn_blocks_symm`). The reduction is
`NUPPT.exists_withAdvice (NUPPT.exists_seq M₀ (NUPPT.exists_comp D pairSndD id)) (1^{k n})`,
which hard-wires the hybrid index and hands the tuple to `D` with the remaining coins. -/
theorem exists_copiesRed (D : NUPPT) {SX SY : List Bool → List Bool} (hSX : PolyTimeComputable SX)
    (hSY : PolyTimeComputable SY) (sX sY ℓ t : PolyExpr) (k : ℕ → ℕ) (hk : ∀ n, k n ≤ t.eval n) :
    ∃ B : NUPPT, B.coins = .add (.add (.mul t sX) (.mul t sY)) D.coins ∧
      ∀ n (z : Fin (ℓ.eval n) → Bool) (cX : Fin (t.eval n) → Fin (sX.eval n) → Bool)
        (cY : Fin (t.eval n) → Fin (sY.eval n) → Bool) (cD : List Bool),
        B.runAtL n (List.ofFn z)
          (List.ofFn ((blocks (t.eval n) (sX.eval n)).symm cX) ++
            List.ofFn ((blocks (t.eval n) (sY.eval n)).symm cY) ++ cD) =
        D.runAtL n (List.ofFn ((blocks (t.eval n) (ℓ.eval n)).symm fun i =>
          if (i : ℕ) < k n then padFin (ℓ.eval n) (SY (NUPPT.advInput n (List.ofFn (cY i))))
          else if (i : ℕ) = k n then z
          else padFin (ℓ.eval n) (SX (NUPPT.advInput n (List.ofFn (cX i)))))) cD := by
  obtain ⟨D₂, hD₂c, -, -, hD₂⟩ := D.exists_comp polyTimeComputable_pairSndD polyTimeComputable_id
  obtain ⟨C, hCc, -, hC⟩ := NUPPT.exists_seq
    (NUPPT.ofPolyTimeUniform (copiesSampler_poly hSX hSY sX sY ℓ t) (.add (.mul t sX) (.mul t sY)))
    D₂
  obtain ⟨B, hBc, hB⟩ := C.exists_withAdvice (fun n => List.replicate (k n) true) t
    (fun n => by simpa using hk n)
  refine ⟨B, by rw [hBc, hCc, hD₂c]; rfl, fun n z cX cY cD => ?_⟩
  rw [hB, hC, hD₂]
  have hlen : (List.ofFn ((blocks (t.eval n) (sX.eval n)).symm cX) ++
      List.ofFn ((blocks (t.eval n) (sY.eval n)).symm cY)).length =
      (NUPPT.ofPolyTimeUniform (copiesSampler_poly hSX hSY sX sY ℓ t)
        (.add (.mul t sX) (.mul t sY))).coinLen n := by
    simp [NUPPT.coinLen_eq]
  rw [List.take_left' hlen, List.drop_left' hlen, id_eq, pairSndD_pairEncode]
  congr 1
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  -- the sampler function on the layout
  have hX' : (List.ofFn ((blocks (t.eval n) (sX.eval n)).symm cX) ++
      List.ofFn ((blocks (t.eval n) (sY.eval n)).symm cY)).take
        ((PolyExpr.mul t sX).eval (List.replicate n true).length) =
      List.ofFn ((blocks (t.eval n) (sX.eval n)).symm cX) := by
    rw [List.take_left']
    simp
  have hY' : (List.ofFn ((blocks (t.eval n) (sX.eval n)).symm cX) ++
      List.ofFn ((blocks (t.eval n) (sY.eval n)).symm cY)).drop
        ((PolyExpr.mul t sX).eval (List.replicate n true).length) =
      List.ofFn ((blocks (t.eval n) (sY.eval n)).symm cY) := by
    rw [List.drop_left']
    simp
  simp only [copiesSampler, copiesInit, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inCoins_eq,
      NUPPT.advInput_eq,
    pairFstD_pairEncode, pairSndD_pairEncode, hX', hY']
  rw [CopiesLoop.loopOut_st]
  set F : ℕ → List Bool := fun i =>
    if i < k n then
      padL (ℓ.eval n) (SY (pairEncode (List.replicate n true)
        (((List.ofFn ((blocks (t.eval n) (sY.eval n)).symm cY)).drop (i * sY.eval n)).take
          (sY.eval n))))
    else if i = k n then List.ofFn z
    else padL (ℓ.eval n) (SX (pairEncode (List.replicate n true)
      (((List.ofFn ((blocks (t.eval n) (sX.eval n)).symm cX)).drop (i * sX.eval n)).take
        (sX.eval n)))) with hF
  have hFlen : ∀ i < t.eval n, (F i).length = ℓ.eval n := by
    intro i _
    simp only [hF]
    split_ifs <;> simp [length_padL]
  have hq : t.eval n ≤ t.eval (CopiesLoop.st (List.replicate n true) [] (List.replicate (k n) true)
      (List.ofFn z) (List.ofFn ((blocks (t.eval n) (sX.eval n)).symm cX))
      (List.ofFn ((blocks (t.eval n) (sY.eval n)).symm cY))).length + 1 := by
    refine (t.eval_mono ?_).trans (Nat.le_succ _)
    simp only [CopiesLoop.st, length_pairEncode, List.length_replicate]
    omega
  rw [PolyExpr.eval_mul, List.length_replicate, take_flatMap_range F hq hFlen]
  refine (ofFn_blocks_symm _ F fun i hi => ?_).symm
  simp only [hF]
  split_ifs with h₁ h₂
  · simp only [padL, take_drop_ofFn_blocks _ i hi, Equiv.apply_symm_apply]
  · rfl
  · simp only [padL, take_drop_ofFn_blocks _ i hi, Equiv.apply_symm_apply]

end TCSlib.Cryptography.EnsembleLemmas

## ===== TCSlib/Cryptography/Foundations/BitLists.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD
import Mathlib.Logic.Equiv.Prod

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
* `TCSlib.Cryptography.flatten_ofFn_one`, `flatten_ofFn_singleton`: flattening one-element blocks.
* `TCSlib.Cryptography.headD_ofFn_one`: the bit of a one-bit vector is the head of its string.
* `TCSlib.Cryptography.zipWith_xor_cancel_left`: `(a ⊕ c) ⊕ a = c`.
* `TCSlib.Cryptography.xorPerm_apply`: `xorPerm v y = y ⊕ v`.
* `TCSlib.Cryptography.mem_keys_of_lookup_isSome`: a key with a value in an association list is
  one of its keys.

## References

Generic list facts; no textbook counterpart.
-/

namespace TCSlib.Cryptography

/-- The head of a dropped list is the element at the dropping index:
`(l.drop i).headD d = l.getD i d`. -/
theorem headD_drop {α : Type*} (l : List α) (i : ℕ) (d : α) : (l.drop i).headD d = l.getD i d := by
  rw [List.headD_eq_head?, List.head?_drop, List.getD_eq_getElem?_getD]

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

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
import TCSlib.Cryptography.Encryption.PublicKey.EnsembleSecurity
import TCSlib.Complexity.ClassP.BinaryArith.Loops
import TCSlib.Cryptography.Games.Bridges.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# CPA, CCA1 and CCA2 security of public-key encryption

[PS10, Definition 171.5], the public-key form of Definition 168.1: `(pk, sk) ← Gen(1^n)`;
`(m₀, m₁, state) ← A^{O₁(sk)}(1^n, pk)`; `c ← Enc_pk(m_b)`; output `A^{O₂(sk)}(c, state)`. The
oracle pairs are `[·, ·]` (CPA), `[Dec, ·]` (CCA1) and `[Dec, Dec*]` (CCA2), where `Dec*` answers
every query except the challenge. There is no encryption oracle: the adversary holds `pk`.
The trapdoor application of Claim 172.a is in `Encryption.PublicKey.TrapdoorCPA`.

**Its encoding.** As in the private-key game (`Encryption/PrivateKey/OracleSecurity.lean`), one
machine plays both phases. It takes `pk` and queries the bit-string oracles `Dec` and `Challenge`.
The oracle state records the challenge and uses it to gate `Dec` by phase (`decOpen`).

**Fixed lengths by canonical padding** (ruling of 2026-11-05). The codec's oracles take and return
fixed-length strings. Public-key schemes of the ch. 2–4 layer have ciphertexts of varying length,
for example Algorithm 104.3's `⟨f_i(r), b ⊕ m⟩`. A generic wrapper (`FixedLengthPKScheme.ofPadded`)
pads every ciphertext `c` to `L(n)` bits as `⟨c, 1^{L(n) − 2|c| − 2}⟩` (`padCt`). Its decryptor
answers `⊥` on every string that is not such a canonical padding (`isPadded`). Without that check
the padded scheme would be malleable: changing a padding bit of the challenge gives a different
string that decrypts to the same message, which breaks CCA2. Padding is a bijection between
ciphertexts and canonical strings (`pairFstD_padCt`, `padCt_of_isPadded`). So `Dec*` refusing the
padded challenge is `Dec*` refusing the challenge. A bound `L` always exists
(`PublicKeyScheme.exists_padBound`, from the machines' time bounds).

**Deviations** (beyond those of Definition 168.1): ciphertexts reach the adversary padded, and
`Dec` takes only `L(n)`-bit queries, so it decrypts only ciphertexts with `2|c| + 2 ≤ L(n)`.
Security is stated for each admissible `L`; a larger `L` admits longer `Dec` queries.

## Main definitions

* `Composability.padCt`, `Composability.isPadded`: canonical padding and its test.
* `Composability.FixedLengthPKScheme`: a public-key scheme with `msgLen(n)`-bit messages and
  `ctLen(n)`-bit ciphertexts; `FixedLengthPKScheme.ofPadded` builds one by padding.
* `PublicKeyScheme.padded`, `BitPublicKeyScheme.padded`: the ch. 2–4 schemes, padded.
* `FixedLengthPKScheme.indImpl`, `indGame`, `INDSecure`: [PS10, Definition 171.5].

## Main results

* `pairFstD_padCt`, `isPadded_padCt`, `padCt_of_isPadded`: padding is a bijection onto the
  canonical strings.
* `PublicKeyScheme.exists_padBound`, `BitPublicKeyScheme.exists_padBound`: padding bounds exist.
* `FixedLengthPKScheme.indCodec_eq_bitCodec`: the adversary codec is a bit codec;
  `PublicKeyScheme.padded_enc_runAt`, `padded_enc_coins`: the padded encryptor.

The claim after Definition 171.5, `BitPublicKeyScheme.SingleBitSecure.padded_cpa` (single-bit
security gives CPA security), and its eager-coins lemma `expect_simulate_indImpl_cpa` are in
`OracleSecurity.PaddedCPA`. Its helpers are `OracleSecurity.ChallengeSim` (the deterministic CPA
run and first-challenge congruence) and `OracleSecurity.RecordHandler` (the recording handler
for T1).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.4, Definition 171.5 and the claim after it on Construction 104.3 (book pp. 171–172).
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! ### Canonical padding -/

/-- **Canonical padding** of a ciphertext `c` to `L` bits: `⟨c, 1^{L − 2|c| − 2}⟩`. -/
def padCt (L : ℕ) (c : List Bool) : List Bool :=
  pairEncode c (List.replicate (L - (2 * c.length + 2)) true)

/-- Padding pairs `c` with `L - (2 * c.length + 2)` true bits. -/
theorem padCt_eq (L : ℕ) (c : List Bool) :
    padCt L c = pairEncode c (List.replicate (L - (2 * c.length + 2)) true) := rfl

/-- Whether `w` is a canonical padding: a pair `⟨c, s⟩` whose second part `s` is all `true`. -/
def isPadded (w : List Bool) : Bool :=
  decide (pairEncode (pairFstD w) (pairSndD w) = w) && !BinArith.hasFalse (pairSndD w)

/-- The canonical-padding test checks that `w` is its decoded pair and that its second
component contains no false bit. -/
theorem isPadded_eq (w : List Bool) :
    isPadded w =
      (decide (pairEncode (pairFstD w) (pairSndD w) = w) && !BinArith.hasFalse (pairSndD w)) := rfl

/-- A padding to `L ≥ 2|c| + 2` bits has `L` bits. -/
theorem length_padCt {L : ℕ} {c : List Bool} (h : 2 * c.length + 2 ≤ L) :
    (padCt L c).length = L := by
  simp only [padCt, length_pairEncode, List.length_replicate]
  omega

/-- Unpadding recovers the ciphertext. -/
@[simp] theorem pairFstD_padCt (L : ℕ) (c : List Bool) : pairFstD (padCt L c) = c := by
  simp [padCt]

/-- A padding is canonical. -/
theorem isPadded_padCt (L : ℕ) (c : List Bool) : isPadded (padCt L c) = true := by
  simp [isPadded, padCt, BinArith.hasFalse_eq]

/-- A canonical string is the padding of its first part to its own length. -/
theorem padCt_of_isPadded {w : List Bool} (h : isPadded w = true) :
    padCt w.length (pairFstD w) = w := by
  simp only [isPadded, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨h₁, h₂⟩ := h
  have hall : pairSndD w = List.replicate (pairSndD w).length true := by
    refine List.eq_replicate_iff.2 ⟨rfl, fun b hb => ?_⟩
    cases b
    · simp only [BinArith.hasFalse_eq, List.any_eq_false, List.mem_map, id_eq,
        forall_exists_index, and_imp] at h₂
      exact absurd rfl (h₂ _ false hb rfl)
    · rfl
  have hlen : w.length = 2 * (pairFstD w).length + 2 + (pairSndD w).length := by
    conv_lhs => rw [← h₁]
    simp only [length_pairEncode]
  unfold padCt
  rw [hlen, show 2 * (pairFstD w).length + 2 + (pairSndD w).length -
    (2 * (pairFstD w).length + 2) = (pairSndD w).length by omega, ← hall]
  exact h₁

/-- The canonical test is polynomial-time. -/
theorem polyTimeComputable_isPadded : PolyTimeComputable (fun w => [isPadded w]) := by
  have heq : PolyTimeComputable fun w => [decide (pairEncode (pairFstD w) (pairSndD w) = w)] := by
    convert polyTimeComputable_pairEq.comp
      ((polyTimeComputable_pairFstD.pairEncode polyTimeComputable_pairSndD).pairEncode
        polyTimeComputable_id) using 1
    funext w
    simp [Function.comp_apply]
  exact polyTimeComputable_and heq
    (polyTimeComputable_not (BinArith.polyTimeComputable_hasFalse.comp polyTimeComputable_pairSndD))

/-! ### The padded encryptor and decryptor -/

/-- The padded encryptor's string function: run `Enc` on the same parameter, argument and coins,
and pad its ciphertext to `L(n)` bits. -/
def padEncFun (enc : NUPPT) (L : PolyExpr) (z : List Bool) : List Bool :=
  padCt (L.eval (NUPPT.inParam z).length)
    (enc.output (NUPPT.layout (NUPPT.inParam z) (NUPPT.inArg z) [] (NUPPT.inCoins z)))

/-- The padded encryptor's string function pads the original output at the same parameter,
argument and coins, with empty advice, to the length prescribed by `L`. -/
theorem padEncFun_eq (enc : NUPPT) (L : PolyExpr) (z : List Bool) :
    padEncFun enc L z = padCt (L.eval (NUPPT.inParam z).length)
      (enc.output (NUPPT.layout (NUPPT.inParam z) (NUPPT.inArg z) [] (NUPPT.inCoins z))) := rfl

/-- The padded encryptor is polynomial-time. -/
theorem polyTimeComputable_padEncFun (enc : NUPPT) (L : PolyExpr) :
    PolyTimeComputable (padEncFun enc L) := by
  have ho : PolyTimeComputable fun z =>
      enc.output (NUPPT.layout (NUPPT.inParam z) (NUPPT.inArg z) [] (NUPPT.inCoins z)) :=
    enc.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
      NUPPT.polyTimeComputable_inParam NUPPT.polyTimeComputable_inArg
      (polyTimeComputable_const []) NUPPT.polyTimeComputable_inCoins)
  have h := ho.pairEncode ((polyTimeComputable_pairDropPoly .var).comp
    ((ho.pairEncode (polyTimeComputable_const [])).pairEncode
      ((polyTimeComputable_unaryPoly L).comp NUPPT.polyTimeComputable_inParam)))
  convert h using 1
  funext z
  simp [padEncFun, padCt, Function.comp_apply, length_pairEncode]

/-- The padded decryptor's string function on `⟨sk, w⟩`: `Dec ⟨sk, c⟩` if `w` is the canonical
padding of `c`, and `⊥` otherwise, here `true :: w`, one bit longer than the query. -/
def padDecFun (dec : List Bool → List Bool) (z : List Bool) : List Bool :=
  if isPadded (pairSndD z) then dec (pairEncode (pairFstD z) (pairFstD (pairSndD z)))
  else true :: pairSndD z

/-- The padded decryptor decrypts the unpadded query when its canonical test passes and
returns `true :: pairSndD z` otherwise. -/
theorem padDecFun_eq (dec : List Bool → List Bool) (z : List Bool) :
    padDecFun dec z =
      if isPadded (pairSndD z) then dec (pairEncode (pairFstD z) (pairFstD (pairSndD z)))
      else true :: pairSndD z := rfl

/-- The padded decryptor is polynomial-time when `Dec` is. -/
theorem polyTimeComputable_padDecFun {dec : List Bool → List Bool}
    (hdec : PolyTimeComputable dec) : PolyTimeComputable (padDecFun dec) :=
  polyTimeComputable_ite (polyTimeComputable_isPadded.comp polyTimeComputable_pairSndD)
    (hdec.comp (polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)))
    ((polyTimeComputable_const [true]).append polyTimeComputable_pairSndD)

/-- The padded encryptor as a machine, with the coins of `Enc`. -/
noncomputable abbrev padEnc (enc : NUPPT) (L : PolyExpr) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_padEncFun enc L) enc.coins

/-- The padded encryptor uses the original encryptor's coin polynomial. -/
theorem padEnc_coins (enc : NUPPT) (L : PolyExpr) : (padEnc enc L).coins = enc.coins :=
  NUPPT.coins_ofPolyTimeUniform (polyTimeComputable_padEncFun enc L) enc.coins

/-- The padded encryptor pads the ciphertext of the uniform `Enc` with the same coin string,
read in `enc` through the public `padEnc_coins` identification. -/
theorem runAt_padEnc {enc : NUPPT} (henc : enc.Uniform) (L : PolyExpr) (n : ℕ) (y : List Bool)
    (r : (padEnc enc L).Coins n) : (padEnc enc L).runAt n y r =
      padCt (L.eval n) (enc.runAt n y (NUPPT.coinsCongr (padEnc_coins enc L) n r)) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform, henc.runAt_eq,
    NUPPT.coinsCongr_ofFn]
  simp only [padEncFun_eq, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inCoins_eq,
    NUPPT.layout_eq, NUPPT.advInput_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate]

/-- The padded decryptor on a padding is `Dec`. -/
theorem padDecFun_padCt (dec : List Bool → List Bool) (sk c : List Bool) (L : ℕ) :
    padDecFun dec (pairEncode sk (padCt L c)) = dec (pairEncode sk c) := by
  simp [padDecFun, isPadded_padCt]

/-- The padded decryptor answers a non-canonical query `w` with a string of `|w| + 1` bits. -/
theorem padDecFun_of_not_isPadded (dec : List Bool → List Bool) (sk w : List Bool)
    (hw : isPadded w = false) : padDecFun dec (pairEncode sk w) = true :: w := by
  simp [padDecFun, hw]

/-! ### Fixed-length public-key schemes -/

/-- A **public-key scheme with fixed-length ciphertexts** [PS10, Definition 102.1]: `msgLen(n)`-bit
messages; `Gen(1^n) = ⟨pk, sk⟩`; `Enc_pk(m)` activated on `⟨pk, m⟩`, whose ciphertexts under
generated keys have `ctLen(n)` bits; a deterministic polynomial-time `Dec` on `⟨sk, c⟩`, with
`⊥` any output that decodes to no message; perfect correctness. -/
structure FixedLengthPKScheme where
  /-- The message length. -/
  msgLen : PolyExpr
  /-- The ciphertext length. -/
  ctLen : PolyExpr
  /-- The key generator. -/
  gen : NUPPT
  /-- The encryptor. -/
  enc : NUPPT
  /-- The decryptor. -/
  dec : List Bool → List Bool
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- `Enc` is a PPT. -/
  enc_uniform : enc.Uniform
  /-- `Dec` is polynomial-time. -/
  dec_poly : PolyTimeComputable dec
  /-- Perfect correctness. -/
  correct : ∀ n (m : Fin (msgLen.eval n) → Bool) (rg : gen.Coins n) (re : enc.Coins n),
    decodeFin _ (dec (pairEncode (pairSndD (gen.runAt n [] rg))
      (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re))) = some m
  /-- Ciphertexts under generated keys have `ctLen(n)` bits. -/
  enc_length : ∀ n (rg : gen.Coins n) (m : Fin (msgLen.eval n) → Bool) (re : enc.Coins n),
    (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re).length =
      ctLen.eval n

namespace FixedLengthPKScheme

/-- **The padded scheme**: a public-key scheme with ciphertexts padded to `L(n)` bits, given that
`L` bounds the honest ciphertexts (`2|c| + 2 ≤ L(n)`) and the message length (so that `⊥` on a
non-canonical `L(n)`-bit query, `|w| + 1` bits, decodes to no message). -/
noncomputable def ofPadded (msgLen : PolyExpr) (gen enc : NUPPT) (dec : List Bool → List Bool)
    (gen_uniform : gen.Uniform) (enc_uniform : enc.Uniform) (dec_poly : PolyTimeComputable dec)
    (correct : ∀ n (m : Fin (msgLen.eval n) → Bool) (rg : gen.Coins n) (re : enc.Coins n),
      decodeFin _ (dec (pairEncode (pairSndD (gen.runAt n [] rg))
        (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re))) = some m)
    (L : PolyExpr)
    (hL : ∀ n (rg : gen.Coins n) (m : Fin (msgLen.eval n) → Bool) (re : enc.Coins n),
      2 * (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re).length + 2
        ≤ L.eval n)
    (_hmsg : ∀ n, msgLen.eval n ≤ L.eval n) : FixedLengthPKScheme where
  msgLen := msgLen
  ctLen := L
  gen := gen
  enc := padEnc enc L
  dec := padDecFun dec
  gen_uniform := gen_uniform
  enc_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  dec_poly := polyTimeComputable_padDecFun dec_poly
  correct := by
    intro n m rg re
    rw [runAt_padEnc enc_uniform, padDecFun_padCt]
    exact correct n m rg (NUPPT.coinsCongr (padEnc_coins enc L) n re)
  enc_length := by
    intro n rg m re
    rw [runAt_padEnc enc_uniform]
    exact length_padCt (hL n rg m (NUPPT.coinsCongr (padEnc_coins enc L) n re))

section PaddedReaders

variable (msgLen : PolyExpr) (gen enc : NUPPT) (dec : List Bool → List Bool)
    (gen_uniform : gen.Uniform) (enc_uniform : enc.Uniform) (dec_poly : PolyTimeComputable dec)
    (correct : ∀ n (m : Fin (msgLen.eval n) → Bool) (rg : gen.Coins n) (re : enc.Coins n),
      decodeFin _ (dec (pairEncode (pairSndD (gen.runAt n [] rg))
        (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re))) = some m)
    (L : PolyExpr)
    (hL : ∀ n (rg : gen.Coins n) (m : Fin (msgLen.eval n) → Bool) (re : enc.Coins n),
      2 * (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, msgLen.eval n ≤ L.eval n)

/-- The padded constructor preserves the supplied message-length polynomial. -/
theorem ofPadded_msgLen :
    (ofPadded msgLen gen enc dec gen_uniform enc_uniform dec_poly correct L hL hmsg).msgLen =
      msgLen := rfl

/-- The padded constructor's ciphertext-length polynomial is `L`. -/
theorem ofPadded_ctLen :
    (ofPadded msgLen gen enc dec gen_uniform enc_uniform dec_poly correct L hL hmsg).ctLen =
      L := rfl

/-- The padded constructor preserves the supplied key generator. -/
theorem ofPadded_gen :
    (ofPadded msgLen gen enc dec gen_uniform enc_uniform dec_poly correct L hL hmsg).gen =
      gen := rfl

/-- The padded constructor uses `padEnc enc L` as its encryptor. -/
theorem ofPadded_enc :
    (ofPadded msgLen gen enc dec gen_uniform enc_uniform dec_poly correct L hL hmsg).enc =
      padEnc enc L := rfl

/-- The padded constructor uses `padDecFun dec` as its decryptor. -/
theorem ofPadded_dec :
    (ofPadded msgLen gen enc dec gen_uniform enc_uniform dec_poly correct L hL hmsg).dec =
      padDecFun dec := rfl

end PaddedReaders

end FixedLengthPKScheme

/-- **A ch. 2–4 public-key scheme, padded** to `L(n)`-bit ciphertexts. -/
noncomputable def _root_.TCSlib.Cryptography.PublicKeyScheme.padded (S : PublicKeyScheme)
    (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re).length
        + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) : FixedLengthPKScheme :=
  .ofPadded .var S.gen S.enc S.dec S.gen_uniform S.enc_uniform S.dec_poly
    (fun n m rg re => S.correct n m rg re) L hL hmsg

section PublicKeyPaddedReaders

variable (S : PublicKeyScheme) (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re).length
        + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n)

/-- Padding a public-key scheme preserves its message-length polynomial `PolyExpr.var`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_msgLen :
    (S.padded L hL hmsg).msgLen = PolyExpr.var := rfl

/-- The padded public-key scheme's ciphertext-length polynomial is `L`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_ctLen :
    (S.padded L hL hmsg).ctLen = L := rfl

/-- Padding a public-key scheme preserves its key generator. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_gen :
    (S.padded L hL hmsg).gen = S.gen := rfl

/-- The padded public-key scheme encrypts with `padEnc S.enc L`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_enc :
    (S.padded L hL hmsg).enc = padEnc S.enc L := rfl

/-- The padded public-key scheme decrypts with `padDecFun S.dec`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_dec :
    (S.padded L hL hmsg).dec = padDecFun S.dec := rfl

/-- **The padded encryptor pads the original encryptor's output**, the coins read as a list:
`Enc'(1^n, y; r) = padCt L(n) (Enc(1^n, y; ⟦r⟧))` (`runAt_padEnc`, `coinsCongr_ofFn`). -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_enc_runAt (n : ℕ) (y : List Bool)
    (r : (S.padded L hL hmsg).enc.Coins n) :
    (S.padded L hL hmsg).enc.runAt n y r = padCt (L.eval n) (S.enc.runAtL n y (List.ofFn r)) := by
  have key : ∀ E : NUPPT, E = padEnc S.enc L → ∀ r : E.Coins n,
      E.runAt n y r = padCt (L.eval n) (S.enc.runAtL n y (List.ofFn r)) := by
    rintro E rfl r
    rw [runAt_padEnc S.enc_uniform L n y r, NUPPT.runAt_eq, NUPPT.coinsCongr_ofFn]
  exact key _ (PublicKeyScheme.padded_enc S L hL hmsg) r

/-- The padded encryptor keeps the coins: `S.enc.coins = (S.padded L hL hmsg).enc.coins`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_enc_coins :
    S.enc.coins = (S.padded L hL hmsg).enc.coins := by
  rw [PublicKeyScheme.padded_enc, padEnc_coins]

end PublicKeyPaddedReaders

/-- **A ch. 2–4 single-bit public-key scheme, padded** to `L(n)`-bit ciphertexts: one-bit
messages, `Enc` activated on `⟨pk, [b]⟩`. -/
noncomputable def _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded (S : BitPublicKeyScheme)
    (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, 1 ≤ L.eval n) : FixedLengthPKScheme :=
  .ofPadded (.const 1) S.gen S.enc S.dec S.gen_uniform S.enc_uniform S.dec_poly
    (fun n (m : Fin 1 → Bool) rg re => by
      have hm : List.ofFn m = [m 0] := by simp
      rw [hm, S.correct n (m 0) rg re, ← hm, decodeFin_ofFn])
    L
    (fun n rg (m : Fin 1 → Bool) re => by
      have hm : List.ofFn m = [m 0] := by simp
      rw [hm]
      exact hL n rg (m 0) re)
    hmsg

section BitPublicKeyPaddedReaders

variable (S : BitPublicKeyScheme) (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, 1 ≤ L.eval n)

/-- Padding a single-bit public-key scheme preserves its constant one-bit message length. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded_msgLen :
    (S.padded L hL hmsg).msgLen = PolyExpr.const 1 := rfl

/-- The padded single-bit scheme's ciphertext-length polynomial is `L`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded_ctLen :
    (S.padded L hL hmsg).ctLen = L := rfl

/-- Padding a single-bit public-key scheme preserves its key generator. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded_gen :
    (S.padded L hL hmsg).gen = S.gen := rfl

/-- The padded single-bit scheme encrypts with `padEnc S.enc L`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded_enc :
    (S.padded L hL hmsg).enc = padEnc S.enc L := rfl

/-- The padded single-bit scheme decrypts with `padDecFun S.dec`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded_dec :
    (S.padded L hL hmsg).dec = padDecFun S.dec := rfl

end BitPublicKeyPaddedReaders

/-- **A padding bound exists** for every ch. 2–4 public-key scheme, from the time bounds of
`Gen` and `Enc` (`NUPPT.length_runAt_le_runLenPoly`): `|pk| ≤ Q₁(n)`, the input `⟨pk, m⟩` has at
most `2Q₁(n) + 2 + n` bits, and the ciphertext at most `Q₂(n)`; `L = 2Q₂ + 2 + n` works.

**Proof sketch.** Bound the generator's output by its running-time polynomial, which also
bounds its public-key projection. The pair-encoding length formula then bounds the encryptor's
input by `2Q₁(n) + 2 + n`. Applying the encryptor's output-length bound to this input gives
`Q₂(n)`. Choose `L(n) = 2Q₂(n) + 2 + n`: it covers the ciphertext's pair-encoding overhead and
is at least the message length `n`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.exists_padBound (S : PublicKeyScheme) :
    ∃ L : PolyExpr,
      (∀ n (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.enc.Coins n),
        2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re).length
          + 2 ≤ L.eval n) ∧ ∀ n, n ≤ L.eval n := by
  have hY : ∀ n (rg : S.gen.Coins n) (m : Fin n → Bool),
      (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)).length ≤
        (PolyExpr.add (.add (.mul (.const 2) (S.gen.runLenPoly (.const 0))) (.const 2)) .var).eval
          n := by
    intro n rg m
    have h₀ := length_pairFstD_le (S.gen.runAt n [] rg)
    have h₁ := S.gen.length_runAt_le_runLenPoly (Y := .const 0) n (y := []) (by simp) rg
    simp only [length_pairEncode, List.length_ofFn, PolyExpr.eval_add, PolyExpr.eval_mul,
      PolyExpr.eval_const, PolyExpr.eval_var]
    omega
  refine ⟨.add (.add (.mul (.const 2) (S.enc.runLenPoly
    (.add (.add (.mul (.const 2) (S.gen.runLenPoly (.const 0))) (.const 2)) .var))) (.const 2))
      .var, fun n rg m re => ?_, fun n => ?_⟩
  · have h₂ := S.enc.length_runAt_le_runLenPoly n (hY n rg m) re
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    omega
  · simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    omega

/-- **A padding bound exists** for every ch. 2–4 single-bit public-key scheme (as for
`PublicKeyScheme.exists_padBound`).

**Proof sketch.** The generator's output-length bound also bounds the public key by `Q₁(n)`.
Pairing that key with one bit gives an encryptor input of at most `2Q₁(n) + 3` bits. Its
running-time bound therefore supplies a ciphertext-length polynomial `Q₂(n)`. The polynomial
`L(n) = 2Q₂(n) + 2` covers the ciphertext encoding and is at least one, as required for the
single-bit message length. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.exists_padBound (S : BitPublicKeyScheme) :
    ∃ L : PolyExpr,
      (∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
        2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
          ≤ L.eval n) ∧ ∀ n, 1 ≤ L.eval n := by
  have hY : ∀ n (rg : S.gen.Coins n) (b : Bool),
      (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]).length ≤
        (PolyExpr.add (.mul (.const 2) (S.gen.runLenPoly (.const 0))) (.const 3)).eval n := by
    intro n rg b
    have h₀ := length_pairFstD_le (S.gen.runAt n [] rg)
    have h₁ := S.gen.length_runAt_le_runLenPoly (Y := .const 0) n (y := []) (by simp) rg
    simp only [length_pairEncode, List.length_singleton, PolyExpr.eval_add, PolyExpr.eval_mul,
      PolyExpr.eval_const]
    omega
  refine ⟨.add (.mul (.const 2) (S.enc.runLenPoly
    (.add (.mul (.const 2) (S.gen.runLenPoly (.const 0))) (.const 3)))) (.const 2),
      fun n rg b re => ?_, fun n => ?_⟩
  · have h₂ := S.enc.length_runAt_le_runLenPoly n (hY n rg b) re
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega
  · simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega

/-! ### The experiment of Definition 171.5 -/

namespace FixedLengthPKScheme

variable (S : FixedLengthPKScheme)

/-- The query lengths of the two oracles `Dec` and `Challenge` at parameter `n`. -/
def inLens (n : ℕ) : Fin 2 → ℕ
  | 0 => S.ctLen.eval n
  | 1 => S.msgLen.eval n + S.msgLen.eval n

/-- Decryption queries have the scheme's ciphertext length. -/
theorem inLens_zero (n : ℕ) : S.inLens n 0 = S.ctLen.eval n := rfl

/-- Challenge queries contain two messages of the scheme's message length. -/
theorem inLens_one (n : ℕ) : S.inLens n 1 = S.msgLen.eval n + S.msgLen.eval n := rfl

/-- The answer lengths: `Dec` answers a validity flag and a message; `Challenge` a ciphertext. -/
def outLens (n : ℕ) : Fin 2 → ℕ
  | 0 => S.msgLen.eval n + 1
  | 1 => S.ctLen.eval n

/-- Decryption answers contain a validity bit followed by one message. -/
theorem outLens_zero (n : ℕ) : S.outLens n 0 = S.msgLen.eval n + 1 := rfl

/-- Challenge answers have the scheme's ciphertext length. -/
theorem outLens_one (n : ℕ) : S.outLens n 1 = S.ctLen.eval n := rfl

/-- The two oracles of the experiment at parameter `n`. -/
abbrev indSpec (n : ℕ) : OracleSpec (Fin 2) := bitSpec (S.inLens n) (S.outLens n)

/-- The public-key IND oracle specification is the bit specification at the scheme's query
and answer lengths. -/
theorem indSpec_eq (n : ℕ) : S.indSpec n = bitSpec (S.inLens n) (S.outLens n) := rfl

/-- Oracle `i` accepts bit strings of length `S.inLens n i`. -/
theorem indSpec_dom (n : ℕ) (i : Fin 2) :
    (S.indSpec n).dom i = (Fin (S.inLens n i) → Bool) :=
  bitSpec_dom (S.inLens n) (S.outLens n) i

/-- The decryption oracle accepts a ciphertext at the scheme's encoded width. -/
theorem indSpec_decDom (n : ℕ) : (S.indSpec n).dom 0 = (Fin (S.ctLen.eval n) → Bool) := by
  rw [S.indSpec_dom, S.inLens_zero]

/-- Oracle `i` returns bit strings of length `S.outLens n i`. -/
theorem indSpec_rng (n : ℕ) (i : Fin 2) :
    (S.indSpec n).rng i = (Fin (S.outLens n i) → Bool) :=
  bitSpec_rng (S.inLens n) (S.outLens n) i

/-- **The oracles of `Ind_b`** at parameter `n`, for the keys `pk`, `sk`; the state is the
challenge, once asked.
- `Dec` answers `⟨1, Dec_sk(c)⟩` when it is open (`decOpen`) and `c` is not the challenge, and
  `⊥` (all `false`) otherwise; an output that decodes to no message is `⊥` as well.
- `Challenge` answers `Enc_pk(m_b)` on `⟨m₀, m₁⟩` the first time it is asked, and records it;
  later it repeats the recorded challenge. -/
noncomputable def indImpl (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool) :
    QueryImpl (S.indSpec n) (Option (Fin (S.ctLen.eval n) → Bool)) unifSpec
  | 0, c, s =>
    if FixedLengthScheme.decOpen atk s.isSome && !decide (s = some c) then
      .pure (FixedLengthScheme.decAnswer (decodeFin _ (S.dec (pairEncode sk (List.ofFn c)))), s)
    else .pure (zeroBits _, s)
  | 1, mm, s =>
    match s with
    | some c => .pure (c, s)
    | none =>
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let c := padFin _ (S.enc.runAt n (pairEncode pk (List.ofFn
          (if b then (FixedLengthScheme.splitHalf mm).2 else (FixedLengthScheme.splitHalf mm).1)))
          r)
        .pure (c, some c)

/-- A decryption query checks oracle availability and refuses the recorded challenge;
otherwise it returns the decoded plaintext with its validity flag, preserving the state. -/
theorem indImpl_dec (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n pk sk 0 c s =
      if FixedLengthScheme.decOpen atk s.isSome && !decide (s = some c) then
        .pure (FixedLengthScheme.decAnswer
          (decodeFin _ (S.dec (pairEncode sk (List.ofFn c)))), s)
      else .pure (zeroBits _, s) := rfl

/-- The first challenge query encrypts the selected message half using fresh coins and
records the padded ciphertext. -/
theorem indImpl_challenge_none (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (mm : Fin (S.msgLen.eval n + S.msgLen.eval n) → Bool) :
    S.indImpl atk b n pk sk 1 mm none =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let c := padFin (S.ctLen.eval n) (S.enc.runAt n (pairEncode pk (List.ofFn
          (if b then (FixedLengthScheme.splitHalf mm).2 else (FixedLengthScheme.splitHalf mm).1)))
          r)
        .pure (c, some c) := rfl

/-- A repeated challenge query returns the recorded ciphertext and preserves it as state. -/
theorem indImpl_challenge_repeat (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (mm : Fin (S.msgLen.eval n + S.msgLen.eval n) → Bool) (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl atk b n pk sk 1 mm (some c) = .pure (c, some c) := rfl

/-- The decryption equation on the query specification's type. Read the ciphertext through
the width equality before checking challenge refusal and decrypting. -/
theorem indImpl_dec_onSpec (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (c : (S.indSpec n).dom 0) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n pk sk 0 c s =
      if FixedLengthScheme.decOpen atk s.isSome && !decide (s = some (cast (S.indSpec_decDom n) c))
      then .pure (FixedLengthScheme.decAnswer
        (decodeFin _ (S.dec (pairEncode sk (List.ofFn (cast (S.indSpec_decDom n) c))))), s)
      else .pure (zeroBits _, s) := by
  simpa only [cast_eq] using S.indImpl_dec atk b n pk sk c s

/-- The decryption oracle answers a validity bit followed by one message:
`(S.indSpec n).rng 0 = (Fin (S.msgLen.eval n + 1) → Bool)`. -/
theorem indSpec_decRng (n : ℕ) : (S.indSpec n).rng 0 = (Fin (S.msgLen.eval n + 1) → Bool) := by
  rw [S.indSpec_rng, S.outLens_zero]

/-- `indImpl_dec_onSpec` with the answer cast through `indSpec_decRng`: for `c' = cast _ c`,
`S.indImpl atk b n pk sk 0 c s = if decOpen atk s.isSome && s ≠ some c' then
pure (cast _ (decAnswer (decodeFin _ (Dec ⟨sk, c'⟩))), s) else pure (zeroBits _, s)`. -/
theorem indImpl_dec_onSpec_cast (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (c : (S.indSpec n).dom 0) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n pk sk 0 c s =
      if FixedLengthScheme.decOpen atk s.isSome && !decide (s = some (cast (S.indSpec_decDom n) c))
      then .pure (cast (S.indSpec_decRng n).symm (FixedLengthScheme.decAnswer
        (decodeFin _ (S.dec (pairEncode sk (List.ofFn (cast (S.indSpec_decDom n) c)))))), s)
      else .pure (zeroBits _, s) := by
  simpa only [cast_eq] using S.indImpl_dec_onSpec atk b n pk sk c s

/-- The challenge oracle returns a ciphertext at the scheme's encoded width. -/
theorem indSpec_challengeRng (n : ℕ) :
    (S.indSpec n).rng 1 = (Fin (S.ctLen.eval n) → Bool) := by
  rw [S.indSpec_rng, S.outLens_one]

/-- A challenge query contains two messages at the scheme's message width. -/
theorem indSpec_challengeDom (n : ℕ) :
    (S.indSpec n).dom 1 = (Fin (S.msgLen.eval n + S.msgLen.eval n) → Bool) := by
  rw [S.indSpec_dom, S.inLens_one]

/-- The fresh challenge equation on the query specification's type. Draw new encryption
coins, encrypt the selected half of the query, and record the resulting ciphertext. -/
theorem indImpl_challenge_none_onSpec (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (mm : (S.indSpec n).dom 1) :
    S.indImpl atk b n pk sk 1 mm none =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let halves := FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n) mm)
        let c := padFin (S.ctLen.eval n) (S.enc.runAt n
          (pairEncode pk (List.ofFn (if b then halves.2 else halves.1))) r)
        .pure (cast (S.indSpec_challengeRng n).symm c, some c) := by
  simpa only [cast_eq] using S.indImpl_challenge_none atk b n pk sk mm

/-- Repeating the challenge preserves the previous state for a query of the specification's
type. -/
theorem indImpl_challenge_repeat_onSpec (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (mm : (S.indSpec n).dom 1) (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl atk b n pk sk 1 mm (some c) = .pure (cast (S.indSpec_challengeRng n).symm c, some c) := by
  simpa only [cast_eq] using S.indImpl_challenge_repeat atk b n pk sk mm c

/-- Under CPA, `Dec` never answers. -/
theorem indImpl_dec_cpa (b : Bool) (n : ℕ) (pk sk : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl .cpa b n pk sk 0 c s = .pure (zeroBits _, s) := by
  simp [indImpl, FixedLengthScheme.decOpen_cpa]

/-- Under CCA2, `Dec` refuses the challenge. -/
theorem indImpl_dec_cca2_challenge (b : Bool) (n : ℕ) (pk sk : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl .cca2 b n pk sk 0 c (some c) = .pure (zeroBits _, some c) := by
  simp [indImpl, FixedLengthScheme.decOpen_cca2]

/-- The codec of the adversary: the two oracles, and a one-bit final output. -/
def indCodec (n : ℕ) : MachineCodec (S.indSpec n) (Fin 1 → Bool) :=
  bitCodec (S.inLens n) (S.outLens n) 1

/-- The public-key IND codec decodes a move with the bit decoder at the scheme's oracle
lengths and a one-bit final output. -/
theorem indCodec_decodeMove (n : ℕ) (w : List Bool) :
    (S.indCodec n).decodeMove w = decodeBitMove (S.inLens n) (S.outLens n) 1 w :=
  bitCodec_decodeMove (S.inLens n) (S.outLens n) 1 w

/-- The public-key IND codec encodes an entry by pairing the unary oracle index with its
query and answer strings. -/
theorem indCodec_encodeEntry (n : ℕ)
    (e : Σ i, (S.indSpec n).dom i × (S.indSpec n).rng i) :
    (S.indCodec n).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  bitCodec_encodeEntry (S.inLens n) (S.outLens n) 1 e

/-- The public-key IND codec returns the false one-bit result on timeout. -/
theorem indCodec_timeout (n : ℕ) : (S.indCodec n).timeout = zeroBits 1 :=
  bitCodec_timeout (S.inLens n) (S.outLens n) 1

/-- The adversary codec is a bit codec: `S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1`. -/
theorem indCodec_eq_bitCodec (n : ℕ) : S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1 := rfl

/-- **The experiment `Ind_b(Π, A, n)`** [PS10, Definition 171.5] for the attack `atk`, with query
budget `q`: sample `(pk, sk) ← Gen(1^n)` and `A`'s coins, run `A` on `pk` against the oracles
from the unchallenged state, and output its bit. -/
noncomputable def indGame (atk : Attack) (A : NUPPT) (q : ℕ) (b : Bool) (n : ℕ) : ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
  (simulate (S.indImpl atk b n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg)))
      (A.toCompOn (S.indCodec n) n q (pairFstD (S.gen.runAt n [] rg)) r) none).bind
    fun res => .pure (res.1 0)

/-- The public-key IND game samples key-generation and adversary coins, simulates the
oracles on the public-key input from the unchallenged state, and returns the final bit. -/
theorem indGame_eq (atk : Attack) (A : NUPPT) (q : ℕ) (b : Bool) (n : ℕ) :
    S.indGame atk A q b n =
      (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
      (ProbComp.sample (A.Coins n)).bind fun r =>
      (simulate (S.indImpl atk b n (pairFstD (S.gen.runAt n [] rg))
          (pairSndD (S.gen.runAt n [] rg)))
        (A.toCompOn (S.indCodec n) n q (pairFstD (S.gen.runAt n [] rg)) r) none).bind
        fun res => .pure (res.1 0) := rfl

/-- **CPA, CCA1 or CCA2 security of a public-key scheme** [PS10, Definition 171.5]: for every
non-uniform PPT `A` and every polynomial query budget, `A`'s advantage between `Ind_0` and
`Ind_1` is negligible. -/
def INDSecure (atk : Attack) : Prop :=
  ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n, advantage (S.indGame atk A (q.eval n) false n) (S.indGame atk A (q.eval n) true n) ≤ ε n

/-- Public-key IND security is exactly negligible advantage for every non-uniform PPT
adversary and polynomial query budget, uniformly over the security parameter. -/
theorem INDSecure_iff (atk : Attack) :
    S.INDSecure atk ↔ ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n, advantage (S.indGame atk A (q.eval n) false n)
        (S.indGame atk A (q.eval n) true n) ≤ ε n := Iff.rfl

end FixedLengthPKScheme

end TCSlib.Cryptography.Composability

## ===== TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/PaddedCPA.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.ChallengeSim
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.RecordHandler

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Single-bit security gives CPA security of the padded scheme

The claim after [PS10, Definition 171.5]: a single-bit secure public-key scheme, padded to fixed
length (`BitPublicKeyScheme.padded`, `Encryption.PublicKey.OracleSecurity`), is CPA-secure in the
oracle game `FixedLengthPKScheme.indGame`.

Under CPA the adversary's view is `pk`, its coins and the padded challenge. Only the first
challenge query uses coins, so the encryption coins may be sampled in advance
(`expect_simulate_indImpl_cpa`). The distinguisher answers every challenge with its own padded
ciphertext and outputs the adversary's bit, corrected by the first challenge pair; it is T1's
machine for the recording handler (`OracleSecurity.RecordHandler`). The two advantages are equal
at every `n` (`padded_cpa_advantage_eq`). The deterministic run and first-challenge congruence
are `OracleSecurity.ChallengeSim`'s.

## Main results

* `expect_simulate_indImpl_cpa`: eager challenge coins under CPA.
* `BitPublicKeyScheme.SingleBitSecure.padded_cpa`: single-bit security gives CPA security of
  the padded scheme.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.4, Definition 171.5 and the claim after it (book pp. 171–172).
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! ### From ensemble security to CPA -/

section PaddedCPA

open ChallengeSim ProbComp

/-- The reduction's challenge answer, read from its context `⟨1^n, ⟨⟨pk, c⟩, ω⟩⟩`: the padding
`padCt L(n) c` of the ciphertext it received. -/
private def cpaAns (L : PolyExpr) (ctx : List Bool) : List Bool :=
  padCt (L.eval (pairFstD ctx).length) (pairSndD (pairFstD (pairSndD ctx)))

/-- The challenge answer is polynomial-time (as `padEncFun`). -/
private theorem polyTimeComputable_cpaAns (L : PolyExpr) : PolyTimeComputable (cpaAns L) := by
  have hc : PolyTimeComputable fun ctx => pairSndD (pairFstD (pairSndD ctx)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  have h := hc.pairEncode ((polyTimeComputable_pairDropPoly .var).comp
    ((hc.pairEncode (polyTimeComputable_const [])).pairEncode
      ((polyTimeComputable_unaryPoly L).comp polyTimeComputable_pairFstD)))
  convert h using 1
  funext ctx
  simp [cpaAns, padCt_eq, Function.comp_apply, length_pairEncode]

/-- On the context `⟨1^n, ⟨z, ω⟩⟩` the challenge answer is `padCt L(n) (pairSndD z)`. -/
private theorem cpaAns_seedIn (L : PolyExpr) (n : ℕ) (z ω : List Bool) :
    cpaAns L (seedIn n z ω) = padCt (L.eval n) (pairSndD z) := by
  simp only [cpaAns, seedIn_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- The selected half of a two-bit challenge query, as a list, is its bit `0` or `1`. -/
private theorem ofFn_splitHalf_bit {k : ℕ} (hk : k = 1) (b : Bool) (mm : Fin (k + k) → Bool) :
    List.ofFn (if b then (FixedLengthScheme.splitHalf mm).2
      else (FixedLengthScheme.splitHalf mm).1) =
      [(List.ofFn mm).getD (if b then 1 else 0) false] := by
  subst hk
  cases b <;> simp [FixedLengthScheme.splitHalf_fst, FixedLengthScheme.splitHalf_snd,
    List.ofFn_succ]

/-- **Eager challenge coins under CPA.** Simulating the oracles of `Ind_b` from the state `s` has,
for every `G`, the expectation of first sampling the encryption coins `re` and then running the
deterministic oracles whose challenge `mm` is answered with `Enc(⟨pk, m_b⟩; re)`, the halves and the
recorded ciphertext read through `indSpec_challengeDom` and `indSpec_challengeRng`:
`𝔼[G ∘ fst] (simulate (indImpl .cpa b n pk sk) c s) = 𝔼_{re} G (chRun g_re c s).1`.

**Proof sketch.** `ChallengeSim.expect_simulate_eager` with `d = ctLen(n)` (`outLens_one`), the
cast `indSpec_challengeRng`, and the oracle equations `indImpl_dec_onSpec` (with `decOpen_cpa`),
`indImpl_challenge_repeat_onSpec` and `indImpl_challenge_none_onSpec`: decryption queries are
answered all-`false`, a repeated challenge repeats the record, and the first challenge samples the
coins and records the encryption. -/
theorem expect_simulate_indImpl_cpa (S : FixedLengthPKScheme) (b : Bool) (n : ℕ)
    (pk sk : List Bool) {α : Type} (G : α → ℝ) (c : OracleComp (S.indSpec n) α)
    (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    expect (simulate (S.indImpl .cpa b n pk sk) c s) (fun p => G p.1) =
      expect (ProbComp.sample (S.enc.Coins n)) fun re =>
        G (chRun (fun mm => S.enc.runAt n (pairEncode pk (List.ofFn
          (if b then (FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n) mm)).2
            else (FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n) mm)).1))) re)
          c (s.map (cast (S.indSpec_challengeRng n).symm))).1 :=
  expect_simulate_eager (S.outLens_one n) (S.indSpec_challengeRng n).symm _ _
    (fun x s => by
      rw [S.indImpl_dec_onSpec]
      simp only [FixedLengthScheme.decOpen_cpa, Bool.false_and, Bool.false_eq_true, if_false])
    (fun mm C => S.indImpl_challenge_repeat_onSpec .cpa b n pk sk mm C)
    (fun mm => S.indImpl_challenge_none_onSpec .cpa b n pk sk mm) G c s

/-- **The exact identity of step 4.** Let `B` be the machine of T1 for the recording handler
with challenge answer `cpaAns L` (with its coin bijection `φ`). At every `n`, `A`'s CPA advantage
against the padded scheme equals `B`'s advantage between `⟨pk, Enc_pk(0)⟩` and `⟨pk, Enc_pk(1)⟩`.

**Proof sketch.** Fix `n`. Game `b` samples `rg`, `A`'s coins `r` and (eagerly,
`expect_simulate_indImpl_cpa`) encryption coins `re`; by first-challenge congruence (`chRun_congr`)
its output is `A`'s bit `F(w)` when the challenge is answered with `w = padCt L(n) (Enc(m_b; re))`,
where `(m₀, m₁)` is `A`'s first challenge query (`firstQ`), or `F` of anything without one. On
`z = ⟨pk, Enc(β; re)⟩`, T1 and `simulate_recHandler_init` show that `B` with coins `φ (ω, r)` runs
`A` with the same answers `padCt L(n) (Enc(β; re))` and outputs the post-processed bit
(`recOut_init`, `recOut_recorded`), after transporting the run between the two equal codecs
(`chRun_toCompOn_transport`). Rearranging the samples (`expect_sample_prod`, `_comm`, `_equiv`
along `φ` and `padEnc_coins`, `_unique` for the empty seed), both differences of acceptance
rates become `𝔼_{rg, r}` of a pointwise difference, which agree by `expect_indicator_sub`. -/
private theorem padded_cpa_advantage_eq {S : BitPublicKeyScheme} (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, 1 ≤ L.eval n) (A : NUPPT) (q : PolyExpr) (B : NUPPT) (n : ℕ)
    (φ : (Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).seedLen.eval n) → Bool) ×
      A.Coins n ≃ B.Coins n)
    (hφ : ∀ (z : List Bool)
      (ω : Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).seedLen.eval n) → Bool)
      (r : A.Coins n),
      ∃ (a : Fin ((PolyExpr.const 1).eval n) → Bool)
        (s : Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).stateLen.eval n) → Bool),
        simulate ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).impl n z ω)
            (A.toCompOn (bitCodec (fun i => (recDin L i).eval n) (fun i => (recDout L i).eval n)
              ((PolyExpr.const 1).eval n)) n (q.eval n)
              ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).advInput n z ω) r)
            ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).init n) = .pure (a, s) ∧
          B.runAt n z (φ (ω, r)) =
            (recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).result n z ω s a) :
    advantage ((S.padded L hL hmsg).indGame .cpa A (q.eval n) false n)
        ((S.padded L hL hmsg).indGame .cpa A (q.eval n) true n) =
      distAdv (S.pkEncDist n false) (S.pkEncDist n true) (B.distinguisherL n) := by
  -- Notation: the game's computation, the padded ciphertexts, and `A`'s bit.
  set S' := S.padded L hL hmsg with hS'
  let comp : S.gen.Coins n → A.Coins n → OracleComp (S'.indSpec n) (Fin 1 → Bool) :=
    fun rg r => A.toCompOn (S'.indCodec n) n (q.eval n) (pairFstD (S.gen.runAt n [] rg)) r
  let W : Bool → S.gen.Coins n → S.enc.Coins n → List Bool := fun β rg re =>
    padCt (L.eval n) (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [β]) re)
  let F : S.gen.Coins n → A.Coins n → List Bool → Bool := fun rg r w =>
    (chRun (fun _ => w) (comp rg r) none).1 0
  -- `A`'s computation, read on the bit codec (`indCodec_eq_bitCodec`).
  have hcomp : ∀ rg r, comp rg r =
      A.toCompOn (bitCodec (S'.inLens n) (S'.outLens n) 1) n (q.eval n)
        (pairFstD (S.gen.runAt n [] rg)) r := fun rg r => by
    show A.toCompOn (S'.indCodec n) n (q.eval n) (pairFstD (S.gen.runAt n [] rg)) r = _
    rw [FixedLengthPKScheme.indCodec_eq_bitCodec]
  -- The two codecs have equal lengths.
  have hins : (fun i => (recDin L i).eval n) = S'.inLens n := by
    funext i
    match i with
    | 0 => rw [recDin_zero, FixedLengthPKScheme.inLens_zero, BitPublicKeyScheme.padded_ctLen]
    | 1 =>
      rw [recDin_one, FixedLengthPKScheme.inLens_one, BitPublicKeyScheme.padded_msgLen,
        PolyExpr.eval_const, PolyExpr.eval_const]
  have houts : (fun i => (recDout L i).eval n) = S'.outLens n := by
    funext i
    match i with
    | 0 =>
      rw [recDout_zero, FixedLengthPKScheme.outLens_zero, BitPublicKeyScheme.padded_msgLen,
        PolyExpr.eval_const, PolyExpr.eval_const]
    | 1 => rw [recDout_one, FixedLengthPKScheme.outLens_one, BitPublicKeyScheme.padded_ctLen]
  -- Step 4, game side: eager coins, first-challenge congruence, and the coin transport.
  have hG : ∀ b : Bool, accept (S'.indGame .cpa A (q.eval n) b n) =
      expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
        expect (ProbComp.sample (A.Coins n)) fun r =>
          expect (ProbComp.sample (S.enc.Coins n)) fun re =>
            if F rg r ((firstQ (comp rg r)).elim []
                fun l => W (l.getD (if b then 1 else 0) false) rg re) = true then 1 else 0 := by
    intro b
    rw [accept_eq, FixedLengthPKScheme.indGame_eq, prob_bind,
      show S'.gen = S.gen from BitPublicKeyScheme.padded_gen S L hL hmsg]
    refine congrArg _ (funext fun rg => ?_)
    rw [prob_bind]
    refine congrArg _ (funext fun r => ?_)
    rw [prob_bind]
    refine (expect_simulate_indImpl_cpa S' b n _ _
      (fun a => ProbComp.prob (.pure (a 0)) (· = true)) (comp rg r) none).trans ?_
    rw [← expect_sample_equiv (NUPPT.coinsCongr (padEnc_coins S.enc L) n),
      show S'.enc = padEnc S.enc L from BitPublicKeyScheme.padded_enc S L hL hmsg]
    refine congrArg _ (funext fun re' => ?_)
    rw [prob_pure]
    congr 2
    refine congrArg (fun p : (Fin 1 → Bool) × Option (Fin (S'.outLens n 1) → Bool) => p.1 0)
      (chRun_congr _ _ _ fun mm hmm => ?_)
    rw [hmm, Option.elim_some]
    exact (runAt_padEnc S.enc_uniform L n _ re').trans (by
      rw [ofFn_splitHalf_bit (by rw [BitPublicKeyScheme.padded_msgLen, PolyExpr.eval_const]),
        ofFn_cast (S'.inLens_one n)])
  -- Step 4, distinguisher side: T1, the handler's simulation, and the codec transport.
  have hpt : ∀ (β : Bool) (rg : S.gen.Coins n) (r : A.Coins n) (re : S.enc.Coins n)
      (ω : Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).seedLen.eval n) → Bool),
      B.distinguisherL n (S.pkEncDist n β (rg, re)) (φ (ω, r)) =
        (firstQ (comp rg r)).elim false fun l =>
          (l.getD 0 false != l.getD 1 false) && (F rg r (W β rg re) != l.getD 0 false) := by
    intro β rg r re ω
    obtain ⟨a, s, hsim, hrun⟩ := hφ (S.pkEncDist n β (rg, re)) ω r
    have hadv :
        (recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).advInput n
          (S.pkEncDist n β (rg, re)) ω =
        pairFstD (S.gen.runAt n [] rg) := by
      rw [PolyHandler.advInput_eq, recHandler_advIn, recAdvIn_eq, seedIn_eq,
        BitPublicKeyScheme.pkEncDist_eq, pairSndD_pairEncode, pairFstD_pairEncode,
        pairFstD_pairEncode]
    have hans : cpaAns L (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn ω)) = W β rg re := by
      rw [cpaAns_seedIn, BitPublicKeyScheme.pkEncDist_eq, pairSndD_pairEncode]
    have hw : (cpaAns L (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn ω))).length =
        L.eval n := by
      rw [hans]
      exact length_padCt (hL n rg β re)
    obtain ⟨s', hsim', hs'⟩ := simulate_recHandler_init L (polyTimeComputable_cpaAns L) n
      (S.pkEncDist n β (rg, re)) ω hw _
    rw [hsim, OracleComp.pure.injEq, Prod.mk.injEq] at hsim'
    obtain ⟨rfl, rfl⟩ := hsim'
    obtain ⟨h₁, h₂⟩ := chRun_toCompOn_transport hins houts (PolyExpr.eval_const 1 n)
      A n (q.eval n) ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).advInput n
        (S.pkEncDist n β (rg, re)) ω) r (W β rg re)
    rw [hadv] at h₁ h₂ hs'
    rw [h₂] at hs'
    rw [NUPPT.distinguisherL_eq, hrun, PolyHandler.result_eq, recHandler_out]
    have ha : List.ofFn (chRun (fun _ => cpaAns L (seedIn n (S.pkEncDist n β (rg, re))
        (List.ofFn ω))) (A.toCompOn (bitCodec (fun i => (recDin L i).eval n)
          (fun i => (recDout L i).eval n) ((PolyExpr.const 1).eval n)) n (q.eval n)
            ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).advInput n
              (S.pkEncDist n β (rg, re)) ω) r) none).1 =
        [F rg r (W β rg re)] := by
      rw [hans, hadv, h₁, List.ofFn_succ, List.ofFn_zero, ← hcomp]
    rw [ha]
    cases hq : firstQ (comp rg r) with
    | none =>
      have hq' : firstQ (A.toCompOn (bitCodec (S'.inLens n) (S'.outLens n) 1) n (q.eval n)
          (pairFstD (S.gen.runAt n [] rg)) r) = none := by rw [← hcomp]; exact hq
      rw [hq', Option.elim_none] at hs'
      rw [hs', recOut_init, Option.elim_none]
      decide
    | some l =>
      have hq' : firstQ (A.toCompOn (bitCodec (S'.inLens n) (S'.outLens n) 1) n (q.eval n)
          (pairFstD (S.gen.runAt n [] rg)) r) = some l := by rw [← hcomp]; exact hq
      have hl : l.length = 2 := by
        rw [length_of_firstQ_eq_some _ hq', FixedLengthPKScheme.inLens_one,
          BitPublicKeyScheme.padded_msgLen, PolyExpr.eval_const]
      obtain ⟨m₀, m₁, rfl⟩ := List.length_eq_two.1 hl
      rw [hq', Option.elim_some] at hs'
      rw [hs', recOut_recorded, Option.elim_some]
      simp only [List.headD_cons, List.getD_cons_zero, List.getD_cons_succ, List.cons.injEq,
        and_true, Bool.decide_eq_true]
  have hD : ∀ β : Bool, acceptProb (S.pkEncDist n β) (B.distinguisherL n) =
      expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
        expect (ProbComp.sample (A.Coins n)) fun r =>
          expect (ProbComp.sample (S.enc.Coins n)) fun re =>
            if ((firstQ (comp rg r)).elim false fun l =>
              (l.getD 0 false != l.getD 1 false) && (F rg r (W β rg re) != l.getD 0 false)) = true
            then 1 else 0 := by
    intro β
    rw [Bridge.acceptProb_eq, accept_eq, Bridge.acceptGame_eq, prob_bind, expect_sample_prod]
    refine congrArg _ (funext fun rg => ?_)
    simp only [prob_bind, prob_pure]
    haveI : Unique (Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).seedLen.eval n) →
        Bool) := by
      rw [recHandler_seedLen, PolyExpr.eval_const]
      infer_instance
    rw [expect_sample_comm, ← expect_sample_equiv φ, expect_sample_prod, expect_sample_unique]
    refine congrArg _ (funext fun r => congrArg _ (funext fun re => ?_))
    rw [hpt β rg r re]
  -- Assemble: both differences are `𝔼_{rg, r}` of equal pointwise differences.
  rw [advantage_eq, distAdv_def, hG false, hG true, hD false, hD true]
  congr 1
  rw [← expect_sub]
  conv_rhs => rw [← expect_sub]
  refine congrArg _ (funext fun rg => ?_)
  rw [← expect_sub]
  conv_rhs => rw [← expect_sub]
  refine congrArg _ (funext fun r => ?_)
  cases hq : firstQ (comp rg r) with
  | none =>
    simp only [Option.elim_none, Bool.false_eq_true, if_false, sub_self]
  | some l =>
    have hl : l.length = 2 := by
      rw [length_of_firstQ_eq_some _ hq, FixedLengthPKScheme.inLens_one,
        BitPublicKeyScheme.padded_msgLen, PolyExpr.eval_const]
    obtain ⟨m₀, m₁, rfl⟩ := List.length_eq_two.1 hl
    simp only [Option.elim_some, List.getD_cons_zero, List.getD_cons_succ, Bool.false_eq_true,
      if_false, if_true]
    exact expect_indicator_sub (fun β re => F rg r (W β rg re)) m₀ m₁

/-- **Single-bit security gives CPA security** for a padded single-bit scheme.

**Proof sketch.**
1. With CPA there is no `Dec` oracle, so the adversary's view is `pk`, its coins and the padded
   challenge `padCt L (Enc_pk(m_b))`, where its messages `m₀, m₁ ∈ {0,1}` are chosen after
   seeing `pk`. Only the first challenge query uses coins, so the encryption coins may be sampled
   in advance (`expect_simulate_indImpl_cpa`); then `A`'s bit depends on the challenge answer only
   through its value at `A`'s first challenge query `(m₀, m₁)`, which itself does not depend on
   that answer (`ChallengeSim.chRun_congr`).
2. If `m₀ = m₁` both games are identical. Otherwise `m_b` is `b` or `¬b`. The distinguisher `D`
   on `⟨pk, c⟩` runs `A` on `pk`, answers every challenge with `padCt L c` and every `Dec` query
   with `⊥`, records `A`'s first challenge `(m₀, m₁)`, and outputs `A`'s bit, flipped when
   `(m₀, m₁) = (1, 0)` and replaced by `0` when `m₀ = m₁` or no challenge was asked. T1
   (`Games.exists_handlerMachine`, for the handler `ChallengeSim.recHandler`) makes `D` a
   machine, whose output is exactly this bit (`ChallengeSim.simulate_recHandler_init`).
3. Fixing `pk` and `A`'s coins, the case split on `(m₀, m₁)` gives the same difference of
   acceptance rates on both sides (`ChallengeSim.expect_indicator_sub`); so `A`'s CPA advantage
   equals `D`'s advantage between `⟨pk, Enc_pk(0)⟩` and `⟨pk, Enc_pk(1)⟩` at every `n`
   (`padded_cpa_advantage_eq`), which is negligible (`BitPublicKeyScheme.singleBitSecure_iff`). -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.padded_cpa
    {S : BitPublicKeyScheme} (h : S.SingleBitSecure) (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, 1 ≤ L.eval n) : (S.padded L hL hmsg).INDSecure .cpa := by
  rw [FixedLengthPKScheme.INDSecure_iff]
  intro A q
  -- Step 3: the distinguisher `D` is T1's machine for the recording handler.
  obtain ⟨B, hB⟩ := exists_handlerMachine A q (recDin L) (recDout L) (.const 1)
    (recHandler L (cpaAns L) (polyTimeComputable_cpaAns L))
  refine ⟨_, (BitPublicKeyScheme.singleBitSecure_iff S).1 h B, fun n => le_of_eq ?_⟩
  -- Step 4: the advantages are equal.
  obtain ⟨φ, hφ⟩ := hB n
  exact padded_cpa_advantage_eq L hL hmsg A q B n φ hφ

end PaddedCPA

end TCSlib.Cryptography.Composability

## ===== TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/ChallengeSim.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Machines
import TCSlib.Cryptography.Games.Probability
import TCSlib.Cryptography.Games.Bridges.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A deterministic challenge oracle under CPA

Under a chosen-plaintext attack the IND experiment of [PS10, Definition 171.5] has two oracles
in the encoding of `Encryption.PublicKey.OracleSecurity`: a decryption oracle that always
answers all-`false`, and a challenge oracle that answers the first query `⟨m₀, m₁⟩` with a
ciphertext and repeats it afterwards. This file studies that pair of oracles on bit strings of
arbitrary lengths (`bitSpec ins outs`) when the first challenge answer is a deterministic
function `g` of the query, for example once the encryption coins have been sampled in advance.

The run is a pure function of the computation (`chRun`). Its result depends on `g` only through
`g` at the first challenge query (`firstQ`), which does not depend on `g` at all
(`chRun_congr`). This replaces the informal "condition on the adversary's choice of messages"
in the proof of the claim after Definition 171.5. Both the run and the first query transport
along equalities of the length functions (`chRun_toCompOn_transport`), which aligns two codecs
with propositionally equal lengths.

The last section collects sampling identities used to rearrange the expectations of the CPA
reduction: reindexing by an equivalence, products, exchange of order, and singleton types.

## Main definitions

* `Composability.ChallengeSim.chRun g c s`: the run of `c` against the CPA oracles with the
  deterministic challenge answer `g`, from the challenge state `s`.
* `Composability.ChallengeSim.firstQ c`: the first challenge query of `c`, as a list.

## Main results

* `ChallengeSim.chRun_some_congr`: once the challenge is recorded, `g` no longer matters.
* `ChallengeSim.chRun_congr`: the run depends on `g` only at the first challenge query.
* `ChallengeSim.length_of_firstQ_eq_some`: the first challenge query has `ins 1` bits.
* `ChallengeSim.chRun_toCompOn_transport_list`, `ChallengeSim.chRun_toCompOn_transport`: transport
  along equal length functions, with a query-dependent and with a constant answer.
* `ChallengeSim.expect_simulate_eager`: eager challenge coins, for any CPA-shaped oracle.
* `ChallengeSim.expect_sample_prod`: sampling a product is sampling its factors (the other
  sampling identities are `Games.ProbComp`'s).
* `ChallengeSim.expect_indicator_sub`: the case split on the first challenge `(m₀, m₁)`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.4, Definition 171.5 and the claim after it (book pp. 171–172).
-/

namespace TCSlib.Cryptography.Composability.ChallengeSim

open Complexity TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

variable {ins outs : Fin 2 → ℕ} {α : Type}

/-! ### The deterministic run -/

/-- **The run of `c` against the CPA oracles with the challenge answer `g`**, from the challenge
state `s`: oracle `0` answers all-`false` and keeps the state; oracle `1` answers the first query
`mm` with `padFin (outs 1) (g mm)` and records it, and later repeats the recorded answer. The
result is `c`'s output and the final state. -/
def chRun (g : (Fin (ins 1) → Bool) → List Bool) :
    OracleComp (bitSpec ins outs) α → Option (Fin (outs 1) → Bool) →
      α × Option (Fin (outs 1) → Bool)
  | .pure a, s => (a, s)
  | .query 0 _ k, s => chRun g (k (zeroBits _)) s
  | .query 1 mm k, none => chRun g (k (padFin _ (g mm))) (some (padFin _ (g mm)))
  | .query 1 _ k, some c => chRun g (k c) (some c)

/-- A return ends the run: `chRun g (pure a) s = (a, s)`. -/
theorem chRun_pure (g : (Fin (ins 1) → Bool) → List Bool) (a : α)
    (s : Option (Fin (outs 1) → Bool)) : chRun g (.pure a) s = (a, s) := rfl

/-- A query to oracle `0` is answered all-`false`, keeping the state:
`chRun g (query 0 x k) s = chRun g (k 0) s`. -/
theorem chRun_query_zero (g : (Fin (ins 1) → Bool) → List Bool) (x : Fin (ins 0) → Bool)
    (k : (Fin (outs 0) → Bool) → OracleComp (bitSpec ins outs) α)
    (s : Option (Fin (outs 1) → Bool)) :
    chRun g (.query 0 x k) s = chRun g (k (zeroBits _)) s := rfl

/-- The first challenge query `mm` is answered with `padFin (outs 1) (g mm)`, which is recorded. -/
theorem chRun_query_one_none (g : (Fin (ins 1) → Bool) → List Bool) (mm : Fin (ins 1) → Bool)
    (k : (Fin (outs 1) → Bool) → OracleComp (bitSpec ins outs) α) :
    chRun g (.query 1 mm k) none = chRun g (k (padFin _ (g mm))) (some (padFin _ (g mm))) := rfl

/-- A later challenge query repeats the recorded answer `c`. -/
theorem chRun_query_one_some (g : (Fin (ins 1) → Bool) → List Bool) (mm : Fin (ins 1) → Bool)
    (k : (Fin (outs 1) → Bool) → OracleComp (bitSpec ins outs) α) (c : Fin (outs 1) → Bool) :
    chRun g (.query 1 mm k) (some c) = chRun g (k c) (some c) := rfl

/-- **The first challenge query** of `c` against the CPA oracles, as a list: queries to oracle `0`
are answered all-`false` and skipped; the first query `mm` to oracle `1` gives `List.ofFn mm`; a
computation that returns before it gives `none`. -/
def firstQ : OracleComp (bitSpec ins outs) α → Option (List Bool)
  | .pure _ => none
  | .query 0 _ k => firstQ (k (zeroBits _))
  | .query 1 mm _ => some (List.ofFn mm)

/-- A return asks no challenge: `firstQ (pure a) = none`. -/
theorem firstQ_pure (a : α) : firstQ (ins := ins) (outs := outs) (.pure a) = none := rfl

/-- A query to oracle `0` is skipped: `firstQ (query 0 x k) = firstQ (k 0)`. -/
theorem firstQ_query_zero (x : Fin (ins 0) → Bool)
    (k : (Fin (outs 0) → Bool) → OracleComp (bitSpec ins outs) α) :
    firstQ (.query 0 x k) = firstQ (k (zeroBits _)) := rfl

/-- A query `mm` to oracle `1` is the first challenge: `firstQ (query 1 mm k) = some ⟦mm⟧`. -/
theorem firstQ_query_one (mm : Fin (ins 1) → Bool)
    (k : (Fin (outs 1) → Bool) → OracleComp (bitSpec ins outs) α) :
    firstQ (.query 1 mm k) = some (List.ofFn mm) := rfl

/-- **Once the challenge is recorded, the answer function no longer matters**:
`chRun g c (some C) = chRun g' c (some C)`.

**Proof sketch.** Induction on `c`: from a recorded state both runs answer oracle `0` with
all-`false` and oracle `1` with the recorded `C`, and keep the state. -/
theorem chRun_some_congr (g g' : (Fin (ins 1) → Bool) → List Bool)
    (c : OracleComp (bitSpec ins outs) α) (C : Fin (outs 1) → Bool) :
    chRun g c (some C) = chRun g' c (some C) := by
  induction c with
  | pure a => rfl
  | query i x k ih =>
    match i, x, k, ih with
    | 0, x, k, ih => rw [chRun_query_zero, chRun_query_zero, ih]
    | 1, x, k, ih => rw [chRun_query_one_some, chRun_query_one_some, ih]

/-- **Eager challenge coins, for any CPA-shaped oracle.** Let `impl` answer oracle `0`
all-`false`, a challenge from a recorded state `c` with `c`, and the first challenge `mm` by
sampling `re` and answering (and recording) `padFin d (g mm re)`; the state holds `d`-bit
strings, `d = outs 1`, read through the cast `e`. Then for every `G`,
`𝔼[G ∘ fst] (simulate impl c s) = 𝔼_{re} G (chRun (fun mm => g mm re) c (s.map (cast e))).1`.

**Proof sketch.** Substitute `d = outs 1`, so that the casts are identities. Induction on the
computation: decryption queries and repeated challenges are deterministic in both; at the first
challenge the lazy side samples `re` and continues from the recorded answer, by the induction
hypothesis an average over coins `re'` on which the recorded run does not depend
(`chRun_some_congr`), so `re'` marginalizes out (`expect_const`). -/
theorem expect_simulate_eager {ins outs : Fin 2 → ℕ} {d : ℕ} (hd : outs 1 = d)
    (e : (Fin d → Bool) = (Fin (outs 1) → Bool)) {R : Type} [Fintype R] [Nonempty R]
    (impl : QueryImpl (bitSpec ins outs) (Option (Fin d → Bool)) unifSpec)
    (g : (Fin (ins 1) → Bool) → R → List Bool)
    (h0 : ∀ x s, impl 0 x s = .pure (zeroBits _, s))
    (hrep : ∀ mm c, impl 1 mm (some c) = .pure (cast e c, some c))
    (hnew : ∀ mm, impl 1 mm none = (ProbComp.sample R).bind fun re =>
      .pure (cast e (padFin d (g mm re)), some (padFin d (g mm re))))
    {α : Type} (G : α → ℝ) (c : OracleComp (bitSpec ins outs) α) (s : Option (Fin d → Bool)) :
    expect (simulate impl c s) (fun p => G p.1) =
      expect (ProbComp.sample R) fun re =>
        G (chRun (fun mm => g mm re) c (s.map (cast e))).1 := by
  subst hd
  have hc : ∀ x : Fin (outs 1) → Bool, cast e x = x := fun x => cast_eq e x
  have hmap : ∀ s : Option (Fin (outs 1) → Bool), s.map (cast e) = s := fun s => by
    cases s <;> simp
  simp only [hc] at hrep hnew
  simp only [hmap]
  induction c generalizing s with
  | pure a =>
    rw [simulate_pure, expect_pure]
    simp only [chRun_pure]
    exact (expect_const _ _).symm
  | query i x k ih =>
    match i, x, k, ih with
    | 0, x, k, ih =>
      rw [simulate_query, h0, OracleComp.pure_bind]
      simp only [chRun_query_zero]
      exact ih _ s
    | 1, x, k, ih =>
      cases s with
      | some C =>
        rw [simulate_query, hrep, OracleComp.pure_bind]
        simp only [chRun_query_one_some]
        exact ih _ _
      | none =>
        rw [simulate_query, hnew, OracleComp.bind_assoc, expect_bind]
        refine congrArg _ (funext fun re => ?_)
        rw [OracleComp.pure_bind, ih, chRun_query_one_none]
        dsimp only
        exact (congrArg _ (funext fun re' =>
          congrArg (fun p : α × Option (Fin (outs 1) → Bool) => G p.1)
            (chRun_some_congr (fun mm => g mm re') (fun mm => g mm re) _ _))).trans
          (expect_const _ _)

/-- **First-challenge congruence:** if `g` and `g'` agree at the first challenge query of `c`
(vacuous when there is none), the runs from the unchallenged state agree:
`chRun g c none = chRun g' c none`.

**Proof sketch.** Induction on `c`. Queries to oracle `0` are answered all-`false` by both runs
and do not change the first challenge query. At the first query `mm` to oracle `1` both runs
record `padFin (g mm) = padFin (g' mm)`, and from then on `chRun_some_congr` applies. -/
theorem chRun_congr (g g' : (Fin (ins 1) → Bool) → List Bool)
    (c : OracleComp (bitSpec ins outs) α)
    (h : ∀ mm : Fin (ins 1) → Bool, firstQ c = some (List.ofFn mm) → g mm = g' mm) :
    chRun g c none = chRun g' c none := by
  induction c with
  | pure a => rfl
  | query i x k ih =>
    match i, x, k, ih, h with
    | 0, x, k, ih, h =>
      rw [chRun_query_zero, chRun_query_zero]
      exact ih _ fun mm hmm => h mm (by rw [firstQ_query_zero]; exact hmm)
    | 1, x, k, ih, h =>
      have hx : g x = g' x := h x (firstQ_query_one x k)
      rw [chRun_query_one_none, chRun_query_one_none, hx]
      exact chRun_some_congr g g' _ _

/-- **The first challenge query has the challenge length**: if `firstQ c = some l` then
`|l| = ins 1`.

**Proof sketch.** Induction on `c`: the first query to oracle `1` is `List.ofFn mm` with
`mm : Fin (ins 1) → Bool`. -/
theorem length_of_firstQ_eq_some (c : OracleComp (bitSpec ins outs) α) {l : List Bool}
    (h : firstQ c = some l) : l.length = ins 1 := by
  induction c with
  | pure a => exact absurd h (by rw [firstQ_pure]; exact Option.noConfusion)
  | query i x k ih =>
    match i, x, k, ih, h with
    | 0, x, k, ih, h =>
      rw [firstQ_query_zero] at h
      exact ih _ h
    | 1, x, k, _, h =>
      rw [firstQ_query_one, Option.some.injEq] at h
      rw [← h, List.length_ofFn]

/-- **Transport of a run with a query-dependent answer along equal lengths:** for a machine
adversary run through `bitCodec`, if `ins = ins'`, `outs = outs'` and `d = d'`, then for every
`G : List Bool → List Bool`,
`List.ofFn (chRun (fun y => G ⟦y⟧) (A.toCompOn (bitCodec ins outs d) n q x r) none).1 =
List.ofFn (chRun (fun y => G ⟦y⟧) (A.toCompOn (bitCodec ins' outs' d') n q x r) none).1`, and
the two runs have the same `firstQ`.

**Proof sketch.** Substitute the equalities; both sides become identical. -/
theorem chRun_toCompOn_transport_list {ins' outs' : Fin 2 → ℕ} {d d' : ℕ}
    (hi : ins = ins') (ho : outs = outs') (hd : d = d') (A : NUPPT) (n q : ℕ) (x : List Bool)
    (r : A.Coins n) (G : List Bool → List Bool) :
    List.ofFn (chRun (ins := ins) (outs := outs) (fun y => G (List.ofFn y))
        (A.toCompOn (bitCodec ins outs d) n q x r) none).1 =
      List.ofFn (chRun (ins := ins') (outs := outs') (fun y => G (List.ofFn y))
        (A.toCompOn (bitCodec ins' outs' d') n q x r) none).1 ∧
    firstQ (A.toCompOn (bitCodec ins outs d) n q x r) =
      firstQ (A.toCompOn (bitCodec ins' outs' d') n q x r) := by
  subst hi ho hd
  exact ⟨rfl, rfl⟩

/-- **Transport along equal lengths:** for a machine adversary run through `bitCodec`, if
`ins = ins'`, `outs = outs'` and `d = d'`, then
`List.ofFn (chRun (fun _ => w) (A.toCompOn (bitCodec ins outs d) n q x r) none).1 =
List.ofFn (chRun (fun _ => w) (A.toCompOn (bitCodec ins' outs' d') n q x r) none).1` and the
two runs have the same `firstQ`.

**Proof sketch.** `chRun_toCompOn_transport_list` with the constant answer `G = fun _ => w`. -/
theorem chRun_toCompOn_transport {ins' outs' : Fin 2 → ℕ} {d d' : ℕ} (hi : ins = ins')
    (ho : outs = outs') (hd : d = d') (A : NUPPT) (n q : ℕ) (x : List Bool) (r : A.Coins n)
    (w : List Bool) :
    List.ofFn (chRun (ins := ins) (outs := outs) (fun _ => w)
        (A.toCompOn (bitCodec ins outs d) n q x r) none).1 =
      List.ofFn (chRun (ins := ins') (outs := outs') (fun _ => w)
        (A.toCompOn (bitCodec ins' outs' d') n q x r) none).1 ∧
    firstQ (A.toCompOn (bitCodec ins outs d) n q x r) =
      firstQ (A.toCompOn (bitCodec ins' outs' d') n q x r) :=
  chRun_toCompOn_transport_list hi ho hd A n q x r fun _ => w

/-! ### Sampling identities -/

section Sampling

variable {β : Type}

/-- **Sampling a product is sampling its factors:**
`𝔼_{(a, b) ← α × β} g (a, b) = 𝔼_{a ← α} 𝔼_{b ← β} g (a, b)`. -/
theorem expect_sample_prod [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (g : α × β → ℝ) :
    expect (sample (α × β)) g = expect (sample α) fun a => expect (sample β) fun b => g (a, b) := by
  rw [← Bridge.expect_sample_pair]
  simp only [expect_bind, expect_pure]

/-- **The pointwise case split of the CPA reduction:** for the first challenge `(m₀, m₁)`, the
difference of the acceptance rates of `A` against `Enc(m₀)` and `Enc(m₁)` equals the difference of
the acceptance rates of the post-processed bit `(m₀ ≠ m₁) ∧ (a ≠ m₀)` against `Enc(0)` and `Enc(1)`.

**Proof sketch.** Four cases. Equal messages give `0 = 0`; `(0, 1)` gives the same difference;
`(1, 0)` gives `(1 − p₀) − (1 − p₁) = p₁ − p₀` for the negated bit. -/
theorem expect_indicator_sub {ρ : Type} [Fintype ρ] [Nonempty ρ] (f : Bool → ρ → Bool)
    (m₀ m₁ : Bool) :
    expect (sample ρ) (fun re => if f m₀ re = true then (1 : ℝ) else 0) -
        expect (sample ρ) (fun re => if f m₁ re = true then (1 : ℝ) else 0) =
      expect (sample ρ)
          (fun re => if ((m₀ != m₁) && (f false re != m₀)) = true then (1 : ℝ) else 0) -
        expect (sample ρ)
          (fun re => if ((m₀ != m₁) && (f true re != m₀)) = true then (1 : ℝ) else 0) := by
  have hneg : ∀ x : Bool, (if (!x) = true then (1 : ℝ) else 0) = 1 - if x = true then 1 else 0 := by
    intro x
    cases x <;> norm_num
  have hf : ∀ x : Bool, (x != false) = x := fun x => by cases x <;> rfl
  have ht : ∀ x : Bool, (x != true) = !x := fun x => by cases x <;> rfl
  cases m₀ <;> cases m₁
  · simp only [bne_self_eq_false, Bool.false_and, Bool.false_eq_true, if_false, expect_const,
      sub_self]
  · simp only [show (false != true) = true from rfl, Bool.true_and, hf]
  · simp only [show (true != false) = true from rfl, Bool.true_and, ht, hneg, expect_sub,
      expect_const]
    ring
  · simp only [bne_self_eq_false, Bool.false_and, Bool.false_eq_true, if_false, expect_const,
      sub_self]

end Sampling

end TCSlib.Cryptography.Composability.ChallengeSim

## ===== TCSlib/Cryptography/Encryption/PublicKey/HybridMachine.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.BlockEncryptor

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The public-key hybrid machine

The machine encrypts the messages outside the challenge position, inserts the
challenge ciphertext, then runs the tuple distinguisher. Its advice supplies the
hybrid index, the messages and the coin offsets.

## Main definitions

* `TCSlib.Cryptography.coinBlocks` identifies typed coin blocks with one coin string.
* `TCSlib.Cryptography.hybridPre` prepares the encoded tuple for the distinguisher.
* `TCSlib.Cryptography.hybridCoins` splits the hybrid machine's coins into encryptor
  blocks and distinguisher coins.

## Main results

* `TCSlib.Cryptography.hybridPre_eq` is the defining equation of the pre-processing.
* `TCSlib.Cryptography.blockEncFun_flatten` describes block encryption on a concatenation
  of messages. `TCSlib.Cryptography.encodeList_ofFn_split` splits an encoded tuple.
* `TCSlib.Cryptography.exists_hybridMachine` constructs the reduction with its coin count
  and run equation.
* `TCSlib.Cryptography.ofFn_hybridCoins` and
  `TCSlib.Cryptography.acceptProb_distinguisherL_coins` relate the machine to typed coins.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (p. 103.)
-/

namespace TCSlib.Cryptography

open Complexity Turing
open PrivateKeyScheme (encodeList)

/-! ## Coin blocks -/

/-- The blockwise coin bijection `({0,1}^B)^k ≃ {0,1}^{k·B}`: block `i` occupies the positions
`i·B, …, i·B + B − 1` (`finProdFinEquiv`, `Equiv.curry`). -/
def coinBlocks (k B : ℕ) : (Fin k → Fin B → Bool) ≃ (Fin (k * B) → Bool) :=
  (Equiv.curry _ _ _).symm.trans (Equiv.arrowCongr finProdFinEquiv (Equiv.refl Bool))

/-- Unfolding of `coinBlocks`: bit `x` is bit `x mod B` of block `x / B`. -/
theorem coinBlocks_apply (k B : ℕ) (v : Fin k → Fin B → Bool) (x : Fin (k * B)) :
    coinBlocks k B v x = v (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2 := rfl

/-- The `i`-th coin segment (`coinBlock`) of the flattening of `v` is the block `v i`.

**Proof sketch.** `List.ext_getElem`: both sides have length `B` (`i < k`), and position `t` of
the segment is bit `i·B + t` of the flat string, which is `finProdFinEquiv (i, t)`
(`finProdFinEquiv_apply_val`), so `coinBlocks_apply` and `Equiv.symm_apply_apply` give
`v i t`. -/
theorem coinBlock_ofFn_coinBlocks (k B : ℕ) (v : Fin k → Fin B → Bool) (i : Fin k) :
    coinBlock B i (List.ofFn (coinBlocks k B v)) = List.ofFn (v i) := by
  have hle : (i : ℕ) * B + B ≤ k * B := by
    have := Nat.mul_le_mul_right B i.isLt
    rw [Nat.succ_mul] at this
    exact this
  have key : ∀ (x : Fin (k * B)) (t : ℕ) (ht : t < B), (x : ℕ) = (i : ℕ) * B + t →
      coinBlocks k B v x = v i ⟨t, ht⟩ := by
    intro x t ht hx
    have hx' : x = finProdFinEquiv (i, ⟨t, ht⟩) := by
      apply Fin.ext
      rw [hx, finProdFinEquiv_apply_val]
      ring
    rw [hx', coinBlocks_apply, Equiv.symm_apply_apply]
  apply List.ext_getElem
  · simp only [coinBlock_eq, List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro t h1 h2
    simp only [coinBlock_eq, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    rw [List.length_ofFn] at h2
    exact key _ t h2 (by simp)

/-- A segment below the cut of a truncated coin string is the segment of the string. -/
theorem coinBlock_take (B i k : ℕ) (r : List Bool) (h : i < k) :
    coinBlock B i (r.take (k * B)) = coinBlock B i r := by
  have hle : i * B + B ≤ k * B := by
    have := Nat.mul_le_mul_right B h
    rw [Nat.succ_mul] at this
    exact this
  simp only [coinBlock_eq, List.drop_take, List.take_take]
  congr 1
  omega

/-- A segment of a coin string shifted by `k` blocks is the segment `k + i` of the string. -/
theorem coinBlock_drop (B i k : ℕ) (r : List Bool) :
    coinBlock B i (r.drop (k * B)) = coinBlock B (k + i) r := by
  simp only [coinBlock_eq, List.drop_drop]
  congr 2
  ring

/-- The length of the concatenation of `j` strings of `L` bits. -/
theorem length_flatten_ofFn {L : ℕ} : ∀ (j : ℕ) (f : Fin j → Fin L → Bool),
    (List.ofFn fun i => List.ofFn (f i)).flatten.length = j * L
  | 0, _ => by simp
  | j + 1, f => by
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, List.length_ofFn,
      length_flatten_ofFn j (fun i => f i.succ)]
    ring

/-! ## The block encryptor on a tuple of messages -/

/-- `blockList` with `L`-bit blocks (`0 < L`) and enough fuel on the concatenation of `j`
strings of `L` bits is the list of their `j` encryptions with the consecutive coin segments
(the `L`-bit analogue of `blockList_ofFn`).

**Proof sketch.** Induction on `j`; `List.ofFn_succ` and `List.flatten_cons` split off the
first string, which is nonempty (`0 < L`) so the step fires, `List.take_left'`/`drop_left'`
cut it off exactly, and the segments of `r.drop B` are the shifted segments of `r`
(`List.drop_drop`). -/
theorem blockList_flatten (E : List Bool → List Bool) (L B : ℕ) (hL : 0 < L) (u pk : List Bool) :
    ∀ (j : ℕ) (msg : Fin j → Fin L → Bool) (r : List Bool) (k : ℕ), j ≤ k →
      blockList E L B u pk k (List.ofFn fun i => List.ofFn (msg i)).flatten r =
        List.ofFn fun i : Fin j =>
          E (NUPPT.layout u (pairEncode pk (List.ofFn (msg i))) [] (coinBlock B i r)) := by
  intro j
  induction j with
  | zero =>
    intro msg r k _
    cases k <;> simp [blockList_zero, blockList_succ]
  | succ j ih =>
    intro msg r k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [List.ofFn_succ, List.ofFn_succ, List.flatten_cons]
    have hne : List.ofFn (msg 0) ++ (List.ofFn fun i => List.ofFn (msg i.succ)).flatten ≠ [] := by
      intro h
      have := congrArg List.length h
      rw [List.length_append, List.length_ofFn, List.length_nil] at this
      omega
    simp only [blockList_zero, blockList_succ, hne, if_false, List.cons.injEq]
    rw [List.take_left' (by simp), List.drop_left' (by simp)]
    refine ⟨?_, ?_⟩
    · simp [coinBlock_eq]
    · rw [ih (fun i => msg i.succ) (r.drop B) k (by omega)]
      congr 1
      funext i
      simp only [coinBlock_eq, Fin.val_succ, List.drop_drop]
      rw [show (B + ↑i * B) = (↑i + 1) * B by ring]

/-- **The block encryptor of a uniform machine on a tuple of messages**: on the state
`⟨1^n, ⟨pk, ⟨m_0 ‖ ⋯ ‖ m_{k-1}, r⟩⟩⟩` with `L(n)`-bit messages (`0 < L(n)`) it returns the tuple
of the activations `Enc(1^n, ⟨pk, m_i⟩; r_i)` with the consecutive `B(n)`-coin segments `r_i`
of `r`.

**Proof sketch.** The state word has at least `k` symbols (`0 < L(n)`), so `blockEncFun_spec`
applies with the word length as fuel; `blockList_flatten` lists the `k` block evaluations and
`Uniform.runAtL_eq` identifies each with an activation of `Enc`. -/
theorem blockEncFun_flatten (Enc : NUPPT) (hEnc : Enc.Uniform) (L : PolyExpr) (n : ℕ)
    (hL : 0 < L.eval n) (pk : List Bool) (k : ℕ) (msg : Fin k → Fin (L.eval n) → Bool)
    (r : List Bool) :
    blockEncFun Enc.output L Enc.coins
        (blockState (List.replicate n true) pk (List.ofFn fun i => List.ofFn (msg i)).flatten r) =
      encodeList (List.ofFn fun i : Fin k =>
        Enc.runAtL n (pairEncode pk (List.ofFn (msg i))) (coinBlock (Enc.coinLen n) i r)) := by
  have hk : k ≤ (blockState (List.replicate n true) pk
      (List.ofFn fun i => List.ofFn (msg i)).flatten r).length := by
    simp only [blockState_eq, length_pairEncode, length_flatten_ofFn]
    have := Nat.le_mul_of_pos_right k hL
    omega
  simp only [blockEncFun_eq]
  rw [blockEncFun_spec Enc.output L Enc.coins (List.replicate n true) pk _ _ r (by
    rw [length_flatten_ofFn, List.length_replicate]
    exact Nat.mul_le_mul_right _ hk)]
  simp only [List.length_replicate]
  rw [blockList_flatten Enc.output (L.eval n) (Enc.coins.eval n) hL (List.replicate n true) pk k
    msg r _ (Nat.le_succ_of_le hk)]
  refine congrArg (fun l => encodeList (List.ofFn l)) (funext fun i => ?_)
  rw [hEnc.runAtL_eq]
  rfl

/-! ## Splitting a tuple at a position -/

/-- Splitting `List.ofFn F` at position `j`: the first `j` entries, the entry `j`, the rest
(`List.ext_getElem` with `List.getElem_append`, `List.getElem_cons`). -/
theorem ofFn_eq_append_cons {α : Type*} {N : ℕ} (F : Fin N → α) (j : Fin N) :
    List.ofFn F = (List.ofFn fun i : Fin j => F (Fin.castLE j.2.le i)) ++
      F j :: List.ofFn fun i : Fin (N - j - 1) => F ⟨j + 1 + i, by omega⟩ := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_cons]
    omega
  · intro t h1 h2
    rw [List.getElem_append]
    simp only [List.length_ofFn]
    split_ifs with h
    · simp only [List.getElem_ofFn]
      congr 1
    · rw [List.getElem_cons]
      split_ifs with h'
      · simp only [List.getElem_ofFn]
        congr 1
        exact Fin.ext (by dsimp only; omega)
      · simp only [List.getElem_ofFn]
        congr 1
        exact Fin.ext (by dsimp only; omega)

/-- The tuple encoding of `List.ofFn F` split at position `j`: the encoding of the first `j`
entries, then the block `⟨F j, ·⟩` around the encoding of the rest
(`encodeList_eq_flatMap`, `pairEncode_nil_append`). -/
theorem encodeList_ofFn_split {N : ℕ} (F : Fin N → List Bool) (j : Fin N) :
    encodeList (List.ofFn F) =
      encodeList (List.ofFn fun i : Fin j => F (Fin.castLE j.2.le i)) ++
        pairEncode (F j)
          (encodeList (List.ofFn fun i : Fin (N - j - 1) => F ⟨j + 1 + i, by omega⟩)) := by
  rw [ofFn_eq_append_cons F j, encodeList_eq_flatMap, List.flatMap_append, List.flatMap_cons,
    pairEncode_nil_append, ← encodeList_eq_flatMap, ← encodeList_eq_flatMap]

/-! ## The hybrid machine -/

/-- The pre-processing of the hybrid machine on the argument
`y = ⟨⟨⟨pk, c⟩, w⟩, ⟨u, ⟨⟨u₁, u₂⟩, ⟨M₁, M₂⟩⟩⟩⟩` (sample `⟨pk, c⟩`, own coins `w`, advice
`⟨u, …⟩` with `u = 1^n`, `u₁ = 1^{j·B(n)}`, `u₂ = 1^{(j+1)·B(n)}`, `M₁` the first `j` messages and
`M₂` the last `K(n) − j − 1` messages concatenated): encrypt the blocks of `M₁` with the first
`|u₁|` coins of `w` and those of `M₂` with the coins of `w` after the first `|u₂|`
(`blockEncFun`), and return `⟨pk, T₁ ++ ⟨c, T₂⟩⟩`, the tuple with `c` planted at position `j`. -/
def hybridPre (E : List Bool → List Bool) (L B : PolyExpr) (y : List Bool) : List Bool :=
  pairEncode (pairFstD (pairFstD (pairFstD y)))
    (blockEncFun E L B (blockState (pairFstD (pairSndD y)) (pairFstD (pairFstD (pairFstD y)))
        (pairFstD (pairSndD (pairSndD (pairSndD y))))
        ((pairSndD (pairFstD y)).take (pairFstD (pairFstD (pairSndD (pairSndD y)))).length)) ++
      pairEncode (pairSndD (pairFstD (pairFstD y)))
        (blockEncFun E L B (blockState (pairFstD (pairSndD y)) (pairFstD (pairFstD (pairFstD y)))
          (pairSndD (pairSndD (pairSndD (pairSndD y))))
          ((pairSndD (pairFstD y)).drop (pairSndD (pairFstD (pairSndD (pairSndD y)))).length))))

/-- The defining equation of `hybridPre`: on `y = ⟨⟨⟨pk, c⟩, w⟩, ⟨u, ⟨⟨u₁, u₂⟩, ⟨M₁, M₂⟩⟩⟩⟩` it is
`⟨pk, blockEncFun E L B (blockState u pk M₁ (w.take |u₁|)) ++
⟨c, blockEncFun E L B (blockState u pk M₂ (w.drop |u₂|))⟩⟩`. -/
theorem hybridPre_eq (E : List Bool → List Bool) (L B : PolyExpr) (y : List Bool) :
    hybridPre E L B y =
      pairEncode (pairFstD (pairFstD (pairFstD y)))
        (blockEncFun E L B (blockState (pairFstD (pairSndD y)) (pairFstD (pairFstD (pairFstD y)))
            (pairFstD (pairSndD (pairSndD (pairSndD y))))
            ((pairSndD (pairFstD y)).take (pairFstD (pairFstD (pairSndD (pairSndD y)))).length)) ++
          pairEncode (pairSndD (pairFstD (pairFstD y)))
            (blockEncFun E L B
              (blockState (pairFstD (pairSndD y)) (pairFstD (pairFstD (pairFstD y)))
                (pairSndD (pairSndD (pairSndD (pairSndD y))))
                ((pairSndD (pairFstD y)).drop
                  (pairSndD (pairFstD (pairSndD (pairSndD y)))).length)))) :=
  rfl

/-- The pre-processing of the hybrid machine is polynomial-time.

**Proof sketch.** Pair projections for the eleven slots, the typed coin cuts
`polyTimeComputable_pairTakePoly`/`pairDropPoly` (`p := var`) on `⟨u₁, w⟩` and `⟨u₂, w⟩` for the
coin segments, `blockEncFun_poly` for the two block encryptors, `PolyTimeComputable.append` and
`pairEncode` for the assembly; the composite equals `hybridPre` by the projection identities. -/
theorem hybridPre_poly {E : List Bool → List Bool} (hE : PolyTimeComputable E) (L B : PolyExpr) :
    PolyTimeComputable (hybridPre E L B) := by
  have hF := polyTimeComputable_pairFstD
  have hS := polyTimeComputable_pairSndD
  have hpk := hF.comp (hF.comp hF)
  have hc := hS.comp (hF.comp hF)
  have hw := hS.comp hF
  have hu := hF.comp hS
  have hrest := hS.comp hS
  have hu₁ := hF.comp (hF.comp hrest)
  have hu₂ := hS.comp (hF.comp hrest)
  have hM₁ := hF.comp (hS.comp hrest)
  have hM₂ := hS.comp (hS.comp hrest)
  have hw₁ := (polyTimeComputable_pairTakePoly .var).comp (hu₁.pairEncode hw)
  have hw₂ := (polyTimeComputable_pairDropPoly .var).comp (hu₂.pairEncode hw)
  have hT₁ := (blockEncFun_poly hE L B).comp (hu.pairEncode (hpk.pairEncode (hM₁.pairEncode hw₁)))
  have hT₂ := (blockEncFun_poly hE L B).comp (hu.pairEncode (hpk.pairEncode (hM₂.pairEncode hw₂)))
  have h := hpk.pairEncode (hT₁.append (hc.pairEncode hT₂))
  convert h using 1
  funext y
  simp only [hybridPre, blockState_eq, Function.comp_apply, pairFstD_pairEncode,
      pairSndD_pairEncode,
    PolyExpr.eval_var]

/-- **The hybrid machine** of the single ⇒ multi-message and bitwise theorems
[PS10, p. 103]: for a uniform encryptor `Enc`, a distinguisher `D`, a number of positions `K`,
a block length `L`, hybrid indices `j n` and message vectors `m n, m' n`, there is a
non-uniform PPT `B` with coins `K · Enc.coins + D.coins` such that at every parameter `n` with
`j n < K(n)` and `0 < L(n)`, on the sample `⟨pk, c⟩` with coins `v ‖ ρ` (`v` the `K(n)` coin blocks of `Enc`,
`ρ` the coins of `D`), `B` runs `D` on `⟨pk, ⟨c_0, …, c_{K(n)-1}⟩⟩` with coins `ρ`, where
`c_i = Enc(1^n, ⟨pk, m'_i⟩; v_i)` for `i < j`, `c_j = c`, and `c_i = Enc(1^n, ⟨pk, m_i⟩; v_i)`
for `i > j`.

**Proof sketch.** `B` is `D` pre-processed by `hybridPre` (`NUPPT.exists_comp`), with the
advice `⟨1^n, ⟨⟨1^{j·B}, 1^{(j+1)·B}⟩, ⟨M₁, M₂⟩⟩⟩` hard-wired at the parameters with
`j n < K(n)` and empty elsewhere (`NUPPT.exists_withAdvice`; length
at most `2n + 10 + 6·K·B + 3·K·L` by `length_pairEncode` and `length_flatten_ofFn`) and the first
`K · B` coins passed as data (`NUPPT.exists_split`). On the hybrid layout the two block
encryptors unfold by `blockEncFun_flatten`, their coin segments are the blocks of `v`
(`coinBlock_take`, `coinBlock_drop`, `coinBlock_ofFn_coinBlocks`), and the planted tuple is the
split `encodeList_ofFn_split` of the hybrid tuple at `j`. -/
theorem exists_hybridMachine (Enc D : NUPPT) (hEnc : Enc.Uniform) (K L : PolyExpr)
    (j : ℕ → ℕ) (m m' : ∀ n, Fin (K.eval n) → Fin (L.eval n) → Bool) :
    ∃ B : NUPPT, B.coins = .add (.mul K Enc.coins) D.coins ∧
      ∀ n, j n < K.eval n → 0 < L.eval n →
        ∀ (pk c : List Bool) (v : Fin (K.eval n) → Enc.Coins n) (ρ : D.Coins n),
        B.runAtL n (pairEncode pk c)
            (List.ofFn (coinBlocks (K.eval n) (Enc.coinLen n) v) ++ List.ofFn ρ) =
          D.runAtL n (pairEncode pk (encodeList (List.ofFn fun i : Fin (K.eval n) =>
            if (i : ℕ) < j n then Enc.runAt n (pairEncode pk (List.ofFn (m' n i))) (v i)
            else if (i : ℕ) = j n then c
            else Enc.runAt n (pairEncode pk (List.ofFn (m n i))) (v i)))) (List.ofFn ρ) := by
  obtain ⟨D₁, hD₁c, -, -, hD₁⟩ :=
    D.exists_comp (hybridPre_poly Enc.polyTimeComputable_output L Enc.coins) polyTimeComputable_id
  let β : ℕ → List Bool := fun n => if hj : j n < K.eval n then pairEncode (List.replicate n true)
    (pairEncode
      (pairEncode (List.replicate (j n * Enc.coinLen n) true)
        (List.replicate ((j n + 1) * Enc.coinLen n) true))
      (pairEncode (List.ofFn fun i : Fin (j n) => List.ofFn (m' n (Fin.castLE hj.le i))).flatten
        (List.ofFn fun i : Fin (K.eval n - j n - 1) =>
          List.ofFn (m n ⟨j n + 1 + i, by omega⟩)).flatten)) else []
  have hβ : ∀ n, (β n).length ≤ (PolyExpr.add (.add (.mul (.const 2) .var) (.const 10))
      (.add (.mul (.const 6) (.mul K Enc.coins)) (.mul (.const 3) (.mul K L)))).eval n := by
    intro n
    by_cases hj : j n < K.eval n
    · simp only [β, dif_pos hj, length_pairEncode, List.length_replicate, length_flatten_ofFn,
        PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var, NUPPT.coinLen_eq]
      have h2 : j n * Enc.coins.eval n ≤ K.eval n * Enc.coins.eval n :=
        Nat.mul_le_mul_right _ hj.le
      have h3 : (j n + 1) * Enc.coins.eval n ≤ K.eval n * Enc.coins.eval n :=
        Nat.mul_le_mul_right _ hj
      have h4 : j n * L.eval n ≤ K.eval n * L.eval n := Nat.mul_le_mul_right _ hj.le
      have h5 : (K.eval n - j n - 1) * L.eval n ≤ K.eval n * L.eval n :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    · simp [β, dif_neg hj]
  obtain ⟨D₂, hD₂c, hD₂⟩ := D₁.exists_withAdvice β _ hβ
  obtain ⟨B, hBc, -, hB⟩ := D₂.exists_split (.mul K Enc.coins)
  refine ⟨B, by rw [hBc, hD₂c, hD₁c], fun n hj hL pk c v ρ => ?_⟩
  rw [hB, hD₂, hD₁, id_eq]
  have hlen : (List.ofFn (coinBlocks (K.eval n) (Enc.coinLen n) v)).length =
      (PolyExpr.mul K Enc.coins).eval n := by
    simp [NUPPT.coinLen_eq]
  rw [List.take_left' hlen, List.drop_left' hlen]
  congr 1
  -- the pre-processing on the hybrid layout
  simp only [hybridPre, β, dif_pos hj, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate]
  rw [blockEncFun_flatten Enc hEnc L n hL pk, blockEncFun_flatten Enc hEnc L n hL pk,
    encodeList_ofFn_split _ ⟨j n, hj⟩]
  congr 1
  congr 1
  · refine congrArg (fun l => encodeList (List.ofFn l)) (funext fun i => ?_)
    have hi : (i : ℕ) < j n := i.isLt
    rw [coinBlock_take _ _ _ _ hi, ← Fin.coe_castLE hj.le i, coinBlock_ofFn_coinBlocks,
      ← NUPPT.runAt_eq]
    simp only [Fin.coe_castLE, hi, if_true]
  · congr 1
    · simp
    · refine congrArg (fun l => encodeList (List.ofFn l)) (funext fun i => ?_)
      have hidx : coinBlock (Enc.coinLen n) (j n + 1 + i)
          (List.ofFn (coinBlocks (K.eval n) (Enc.coinLen n) v)) =
          List.ofFn (v ⟨j n + 1 + i, by have := i.isLt; omega⟩) :=
        coinBlock_ofFn_coinBlocks (K.eval n) (Enc.coinLen n) v ⟨j n + 1 + i, by have := i.isLt; omega⟩
      rw [coinBlock_drop, hidx, ← NUPPT.runAt_eq]
      simp only [Fin.val_mk]
      rw [if_neg (by omega), if_neg (by omega)]

/-- The coin length of a hybrid machine with coin polynomial `K · Enc.coins + D.coins`. -/
theorem hybridCoins_len (B Enc D : NUPPT) (K : PolyExpr) (n : ℕ)
    (hBc : B.coins = .add (.mul K Enc.coins) D.coins) :
    K.eval n * Enc.coinLen n + D.coinLen n = B.coinLen n := by
  simp [NUPPT.coinLen_eq, hBc]

/-- The coins of a hybrid machine with coin polynomial `K · Enc.coins + D.coins`: the `K(n)`
coin blocks of `Enc` followed by the coins of `D` (`coinBlocks`, `Fin.appendEquiv`). -/
def hybridCoins (B Enc D : NUPPT) (K : PolyExpr) (n : ℕ)
    (hBc : B.coins = .add (.mul K Enc.coins) D.coins) :
    (Fin (K.eval n) → Enc.Coins n) × D.Coins n ≃ B.Coins n :=
  ((coinBlocks (K.eval n) (Enc.coinLen n)).prodCongr (Equiv.refl _)).trans
    ((Fin.appendEquiv _ _).trans
      (Equiv.arrowCongr (finCongr (hybridCoins_len B Enc D K n hBc)) (Equiv.refl Bool)))

/-- The coin string of `hybridCoins (v, ρ)` is the flattening of `v` followed by `ρ`
(`List.ofFn_fin_append`, `List.ofFn_congr`). -/
theorem ofFn_hybridCoins (B Enc D : NUPPT) (K : PolyExpr) (n : ℕ)
    (hBc : B.coins = .add (.mul K Enc.coins) D.coins) (v : Fin (K.eval n) → Enc.Coins n)
    (ρ : D.Coins n) :
    List.ofFn (hybridCoins B Enc D K n hBc (v, ρ)) =
      List.ofFn (coinBlocks (K.eval n) (Enc.coinLen n) v) ++ List.ofFn ρ := by
  rw [← List.ofFn_fin_append]
  exact (List.ofFn_congr (hybridCoins_len B Enc D K n hBc)
    (Fin.append (coinBlocks (K.eval n) (Enc.coinLen n) v) ρ)).symm

/-- **A machine's acceptance probability with its coins read through a bijection** `e`: if the
verdict of `B` on `X s` with coins `e t` is `A (X s) t`, the acceptance probabilities of `B`
and `A` on `X` agree (`uprob_comp_equiv` on the coin factor). -/
theorem acceptProb_distinguisherL_coins {σ τ : Type*} [Fintype σ] [Fintype τ] (B : NUPPT)
    (n : ℕ) (X : σ → List Bool) (e : τ ≃ B.Coins n) (A : List Bool → τ → Bool)
    (h : ∀ s t, B.distinguisherL n (X s) (e t) = A (X s) t) :
    acceptProb X (B.distinguisherL n) = acceptProb X A := by
  simp only [acceptProb_def]
  rw [← uprob_comp_equiv ((Equiv.refl σ).prodCongr e)]
  congr 1
  funext z
  simp [h]

/-- `List.ofFn` of a constant on `Fin 1` is the one-letter string. -/
theorem ofFn_fin_one (b : Bool) : List.ofFn (fun _ : Fin 1 => b) = [b] := by
  simp [List.ofFn_succ]

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Encryption/PrivateKey/OracleSecurity.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Encryption.PrivateKey.Scheme
import TCSlib.Cryptography.Foundations.Negligible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# CPA, CCA1 and CCA2 security of private-key encryption (definitions)

[PS10, Definition 168.1], the first definition of ch. 7 (prong C of the ch. 5–8 campaign), stated
as a game of the `Games` framework over the ch. 2–4 layer's `PrivateKeyScheme`.

**The experiment** `IND_b^{O₁,O₂}(Π, A, n)`: `k ← Gen(1^n)`; `(m₀, m₁, state) ← A^{O₁(k)}(1^n)`;
`c ← Enc_k(m_b)`; output `A^{O₂(k)}(c, state)`. The oracle pairs are `[Enc; Enc]` (CPA),
`[Enc, Dec; Enc]` (CCA1) and `[Enc, Dec; Enc, Dec]` (CCA2). Under CCA2, `Dec` returns `⊥` on the
challenge `c`.

**Its encoding.** One machine plays both phases against three bit-string oracles:
- `Enc` (`n`-bit messages, `ct(n)`-bit ciphertexts);
- `Dec` (`ct(n)`-bit ciphertexts; an `(n + 1)`-bit answer, a validity flag followed by the message);
- `Challenge`, which takes `⟨m₀, m₁⟩` and returns `c ← Enc_k(m_b)`.

The oracles' state remembers the challenge, once asked. That state decides the phase: `Dec` answers
never (CPA), before the challenge only (CCA1), or always, except on `c` itself (CCA2). A refused
`Dec` query, or a repeated challenge, gets a fixed answer. The machine's final output is one bit.

**Deviations, declared once here.**
- **One machine for both phases.** The source's two-phase adversary passes `state` from phase 1
  to phase 2. Here a single next-move machine plays both phases, and its query log (which includes
  the challenge `c`) is that state. Either form simulates the other, at polynomial cost.
- **Fixed-length ciphertexts.** The scheme's ciphertexts at parameter `n` have exactly `ct(n)`
  bits (`FixedLengthScheme`), as the oracle codec needs.
- **Query budgets.** The adversary's number of oracle queries is an explicit polynomial `q`,
  universally quantified, as in the ch. 2–4 layer's `OracleEnsemble.Indist`.
- **Indistinguishability** of the two one-bit outputs is a negligible distinguishing advantage
  between the games for `b = 0` and `b = 1`.

## Main definitions

* `Composability.Attack`: CPA, CCA1, CCA2.
* `Composability.FixedLengthScheme`: a `PrivateKeyScheme` with fixed-length ciphertexts.
* `FixedLengthScheme.indImpl`, `FixedLengthScheme.indGame`: the oracles and the experiment
  `IND_b`.
* `FixedLengthScheme.INDSecure`: [PS10, Definition 168.1].

## Main results

* `indImpl_dec_cpa`, `indImpl_dec_cca2_challenge`, `indImpl_challenge_repeat`: sanity checks of
  the oracles (CPA's `Dec` is closed; CCA2's `Dec` refuses the challenge; a challenge is asked
  once).
* `FixedLengthScheme.ofFn_splitHalf_fst`, `ofFn_splitHalf_snd`: the strings of the two halves of a
  challenge query.
* `FixedLengthScheme.indCodec_eq_bitCodec`: the game's codec is a bit codec.

The theorems on these notions (Thms 168.2 and 170.4, Claim 169.a) are stated in the statement
phase of prong C, in their own modules.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.1, Definition 168.1 (book p. 168).
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-- The three attacks of [PS10, Definition 168.1]. -/
inductive Attack : Type where
  /-- Chosen-plaintext: `[Enc; Enc]`. -/
  | cpa
  /-- Non-adaptive chosen-ciphertext: `[Enc, Dec; Enc]`. -/
  | cca1
  /-- Adaptive chosen-ciphertext: `[Enc, Dec; Enc, Dec]`, `Dec` refusing the challenge. -/
  | cca2
  deriving DecidableEq

/-- A **private-key encryption scheme with fixed-length ciphertexts**: every encryption of an
`n`-bit message under a generated key has exactly `ct(n)` bits. -/
structure FixedLengthScheme extends PrivateKeyScheme where
  /-- The ciphertext length `ct(n)`. -/
  ctLen : PolyExpr
  /-- Ciphertexts of `n`-bit messages under generated keys have `ct(n)` bits. -/
  enc_length : ∀ n (rg : gen.Coins n) (m : Fin n → Bool) (r : enc.Coins n),
    (enc.runAt n (pairEncode (gen.runAt n [] rg) (List.ofFn m)) r).length = ctLen.eval n

namespace FixedLengthScheme

variable (S : FixedLengthScheme)

/-- The query lengths of the three oracles `Enc`, `Dec`, `Challenge` at parameter `n`. -/
def inLens (n : ℕ) : Fin 3 → ℕ
  | 0 => n
  | 1 => S.ctLen.eval n
  | 2 => n + n

/-- The encryption oracle accepts `n`-bit messages. -/
theorem inLens_zero (n : ℕ) : S.inLens n 0 = n := rfl

/-- The decryption oracle accepts ciphertexts of the fixed ciphertext length. -/
theorem inLens_one (n : ℕ) : S.inLens n 1 = S.ctLen.eval n := rfl

/-- The challenge oracle accepts a pair of `n`-bit messages. -/
theorem inLens_two (n : ℕ) : S.inLens n 2 = n + n := rfl

/-- The answer lengths of the three oracles at parameter `n`; `Dec`'s answer is a validity flag
followed by the message. -/
def outLens (n : ℕ) : Fin 3 → ℕ
  | 0 => S.ctLen.eval n
  | 1 => n + 1
  | 2 => S.ctLen.eval n

/-- Encryption returns the fixed ciphertext length. -/
theorem outLens_zero (n : ℕ) : S.outLens n 0 = S.ctLen.eval n := rfl

/-- Decryption returns a validity bit followed by an `n`-bit message. -/
theorem outLens_one (n : ℕ) : S.outLens n 1 = n + 1 := rfl

/-- The challenge returns the fixed ciphertext length. -/
theorem outLens_two (n : ℕ) : S.outLens n 2 = S.ctLen.eval n := rfl

/-- The three oracles of the experiment at parameter `n`. -/
abbrev indSpec (n : ℕ) : OracleSpec (Fin 3) := bitSpec (S.inLens n) (S.outLens n)

/-- The IND oracle specification has the published input and output lengths. -/
theorem indSpec_eq (n : ℕ) : S.indSpec n = bitSpec (S.inLens n) (S.outLens n) := rfl

/-- Whether `Dec` answers, given the attack and whether the challenge has been asked. -/
def decOpen : Attack → Bool → Bool
  | .cpa, _ => false
  | .cca1, challenged => !challenged
  | .cca2, _ => true

/-- CPA never opens the decryption oracle. -/
theorem decOpen_cpa (challenged : Bool) : decOpen .cpa challenged = false := rfl

/-- CCA1 opens decryption exactly before the challenge. -/
theorem decOpen_cca1 (challenged : Bool) : decOpen .cca1 challenged = !challenged := rfl

/-- CCA2 always opens decryption, with the challenge refusal checked separately. -/
theorem decOpen_cca2 (challenged : Bool) : decOpen .cca2 challenged = true := rfl

/-- The ciphertext `Enc_k(m)` with coins `r`, read at `ct(n)` bits. -/
def encryptAt (n : ℕ) (k : List Bool) (m : Fin n → Bool) (r : S.enc.Coins n) :
    Fin (S.ctLen.eval n) → Bool :=
  padFin _ (S.enc.runAt n (pairEncode k (List.ofFn m)) r)

/-- Encryption is the padded reading of the underlying encryption machine's output. -/
theorem encryptAt_eq (n : ℕ) (k : List Bool) (m : Fin n → Bool) (r : S.enc.Coins n) :
    S.encryptAt n k m r = padFin (S.ctLen.eval n)
      (S.enc.runAt n (pairEncode k (List.ofFn m)) r) := rfl

/-- `Dec`'s answer `⟨1, m⟩` on a valid decryption `m`, and the all-`false` `⊥` otherwise. -/
def decAnswer {n : ℕ} : Option (Fin n → Bool) → (Fin (n + 1) → Bool)
  | some m => Fin.cons (α := fun _ => Bool) true m
  | none => zeroBits _

/-- A successful decryption is prefixed by its `true` validity bit. -/
theorem decAnswer_some {n : ℕ} (m : Fin n → Bool) :
    decAnswer (some m) = Fin.cons (α := fun _ => Bool) true m := rfl

/-- Failed decryption is the all-false answer. -/
theorem decAnswer_none (n : ℕ) : decAnswer (n := n) none = zeroBits (n + 1) := rfl

/-- The first and the second `n` bits of a `2n`-bit query: the challenge messages `m₀, m₁`. -/
def splitHalf {n : ℕ} (x : Fin (n + n) → Bool) : (Fin n → Bool) × (Fin n → Bool) :=
  (fun i => x (Fin.castAdd n i), fun j => x (Fin.natAdd n j))

/-- The first half of a challenge query consists of its first `n` bits. -/
theorem splitHalf_fst {n : ℕ} (x : Fin (n + n) → Bool) :
    (splitHalf x).1 = fun i => x (Fin.castAdd n i) := rfl

/-- The second half of a challenge query consists of its final `n` bits. -/
theorem splitHalf_snd {n : ℕ} (x : Fin (n + n) → Bool) :
    (splitHalf x).2 = fun j => x (Fin.natAdd n j) := rfl

/-- The first half of a `2m`-bit query is its first `m` bits:
`⟦(splitHalf y).1⟧ = ⟦y⟧.take m`. -/
theorem ofFn_splitHalf_fst {m : ℕ} (y : Fin (m + m) → Bool) :
    List.ofFn (splitHalf y).1 = (List.ofFn y).take m := by
  rw [splitHalf_fst]
  refine List.ext_getElem (by simp only [List.length_ofFn, List.length_take]; omega)
    fun i h₁ h₂ => ?_
  rw [List.getElem_ofFn, List.getElem_take, List.getElem_ofFn]
  rfl

/-- The second half of a `2m`-bit query is its last `m` bits:
`⟦(splitHalf y).2⟧ = ⟦y⟧.drop m`. -/
theorem ofFn_splitHalf_snd {m : ℕ} (y : Fin (m + m) → Bool) :
    List.ofFn (splitHalf y).2 = (List.ofFn y).drop m := by
  rw [splitHalf_snd]
  refine List.ext_getElem (by simp only [List.length_ofFn, List.length_drop]; omega)
    fun i h₁ h₂ => ?_
  rw [List.getElem_ofFn, List.getElem_drop, List.getElem_ofFn]
  rfl

/-- **The oracles of `IND_b`** at parameter `n`, for the key `k`; the state is the challenge,
once asked.
- `Enc` answers `Enc_k(m)` with fresh coins.
- `Dec` answers `⟨1, Dec_k(c)⟩` with fresh coins when it is open (`decOpen`) and `c` is not the
  challenge, and `⊥` (all `false`) otherwise; a ciphertext that fails to decrypt is `⊥` as well.
- `Challenge` answers `Enc_k(m_b)` on `⟨m₀, m₁⟩` the first time it is asked, and records it;
  later it repeats the recorded challenge. -/
noncomputable def indImpl (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool) :
    QueryImpl (S.indSpec n) (Option (Fin (S.ctLen.eval n) → Bool)) unifSpec
  | 0, m, s => (ProbComp.sample (S.enc.Coins n)).bind fun r => .pure (S.encryptAt n k m r, s)
  | 1, c, s =>
    if decOpen atk s.isSome && !decide (s = some c) then
      (ProbComp.sample (S.dec.Coins n)).bind fun r =>
        .pure (decAnswer (decodeFin n (S.dec.runAt n (pairEncode k (List.ofFn c)) r)), s)
    else .pure (zeroBits _, s)
  | 2, mm, s =>
    match s with
    | some c => .pure (c, s)
    | none =>
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let c := S.encryptAt n k (if b then (splitHalf mm).2 else (splitHalf mm).1) r
        .pure (c, some c)

/-- An encryption query samples fresh encryption coins and preserves the challenge state. -/
theorem indImpl_enc (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (m : Fin n → Bool) (st : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n k 0 m st =
      (ProbComp.sample (S.enc.Coins n)).bind fun r => .pure (S.encryptAt n k m r, st) := rfl

/-- Decryption queries test oracle availability and refuse the recorded challenge before
running the decryption machine. -/
theorem indImpl_dec (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) (st : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n k 1 c st =
      if decOpen atk st.isSome && !decide (st = some c) then
        (ProbComp.sample (S.dec.Coins n)).bind fun r =>
          .pure (decAnswer (decodeFin n (S.dec.runAt n (pairEncode k (List.ofFn c)) r)), st)
      else .pure (zeroBits _, st) := rfl

/-- A first challenge query encrypts the selected half and records that ciphertext. -/
theorem indImpl_challenge_none (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (mm : Fin (n + n) → Bool) :
    S.indImpl atk b n k 2 mm none =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let c := S.encryptAt n k (if b then (splitHalf mm).2 else (splitHalf mm).1) r
        .pure (c, some c) := rfl

/-- Under CPA, `Dec` never answers: every decryption query gets `⊥`. -/
theorem indImpl_dec_cpa (b : Bool) (n : ℕ) (k : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl .cpa b n k 1 c s = .pure (zeroBits _, s) := by
  simp [indImpl, decOpen]

/-- Under CCA2, `Dec` refuses the challenge: on the recorded challenge `c` it answers `⊥`. -/
theorem indImpl_dec_cca2_challenge (b : Bool) (n : ℕ) (k : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl .cca2 b n k 1 c (some c) = .pure (zeroBits _, some c) := by
  simp [indImpl, decOpen]

/-- A repeated challenge query returns the recorded challenge and changes nothing. -/
theorem indImpl_challenge_repeat (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (mm : Fin (n + n) → Bool) (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl atk b n k 2 mm (some c) = .pure (c, some c) := rfl

/-- The encryption oracle accepts an `n`-bit message:
`(S.indSpec n).dom 0 = (Fin n → Bool)`. -/
theorem indSpec_encDom (n : ℕ) : (S.indSpec n).dom 0 = (Fin n → Bool) := by
  rw [S.indSpec_eq, bitSpec_dom, S.inLens_zero]

/-- The encryption oracle answers a ciphertext at the fixed ciphertext width:
`(S.indSpec n).rng 0 = (Fin (S.ctLen.eval n) → Bool)`. -/
theorem indSpec_encRng (n : ℕ) : (S.indSpec n).rng 0 = (Fin (S.ctLen.eval n) → Bool) := by
  rw [S.indSpec_eq, bitSpec_rng, S.outLens_zero]

/-- The decryption oracle accepts a ciphertext at the fixed ciphertext width:
`(S.indSpec n).dom 1 = (Fin (S.ctLen.eval n) → Bool)`. -/
theorem indSpec_decDom (n : ℕ) : (S.indSpec n).dom 1 = (Fin (S.ctLen.eval n) → Bool) := by
  rw [S.indSpec_eq, bitSpec_dom, S.inLens_one]

/-- The decryption oracle answers a validity bit followed by an `n`-bit message:
`(S.indSpec n).rng 1 = (Fin (n + 1) → Bool)`. -/
theorem indSpec_decRng (n : ℕ) : (S.indSpec n).rng 1 = (Fin (n + 1) → Bool) := by
  rw [S.indSpec_eq, bitSpec_rng, S.outLens_one]

/-- A challenge query contains two `n`-bit messages:
`(S.indSpec n).dom 2 = (Fin (n + n) → Bool)`. -/
theorem indSpec_challengeDom (n : ℕ) : (S.indSpec n).dom 2 = (Fin (n + n) → Bool) := by
  rw [S.indSpec_eq, bitSpec_dom, S.inLens_two]

/-- The challenge oracle answers a ciphertext at the fixed ciphertext width:
`(S.indSpec n).rng 2 = (Fin (S.ctLen.eval n) → Bool)`. -/
theorem indSpec_challengeRng (n : ℕ) : (S.indSpec n).rng 2 = (Fin (S.ctLen.eval n) → Bool) := by
  rw [S.indSpec_eq, bitSpec_rng, S.outLens_two]

/-- The decryption equation on the query specification's type: with `c' = cast _ c` the
ciphertext read at width `ct(n)`, `S.indImpl atk b n k 1 c st` is
`if decOpen atk st.isSome && !decide (st = some c')` then a fresh `r ← Dec.Coins n` and the answer
`cast _ (decAnswer (decodeFin n (Dec.runAt n ⟨k, c'⟩ r)))` with state `st`, else `⊥` with `st`. -/
theorem indImpl_dec_onSpec (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (c : (S.indSpec n).dom 1) (st : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n k 1 c st =
      if decOpen atk st.isSome && !decide (st = some (cast (S.indSpec_decDom n) c)) then
        (ProbComp.sample (S.dec.Coins n)).bind fun r =>
          .pure (cast (S.indSpec_decRng n).symm (decAnswer (decodeFin n
            (S.dec.runAt n (pairEncode k (List.ofFn (cast (S.indSpec_decDom n) c))) r))), st)
      else .pure (zeroBits _, st) := by
  simpa only [cast_eq] using S.indImpl_dec atk b n k c st

/-- The fresh challenge equation on the query specification's type: with
`⟨m₀, m₁⟩ = splitHalf (cast _ mm)`, `S.indImpl atk b n k 2 mm none` draws `r ← Enc.Coins n`,
sets `c = S.encryptAt n k m_b r`, and returns `cast _ c` with the state `some c`. -/
theorem indImpl_challenge_none_onSpec (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (mm : (S.indSpec n).dom 2) :
    S.indImpl atk b n k 2 mm none =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let halves := splitHalf (cast (S.indSpec_challengeDom n) mm)
        let c := S.encryptAt n k (if b then halves.2 else halves.1) r
        .pure (cast (S.indSpec_challengeRng n).symm c, some c) := by
  simpa only [cast_eq] using S.indImpl_challenge_none atk b n k mm

/-- The encryption equation on the query specification's type: with `m' = cast _ m` the message
read at width `n`, `S.indImpl atk b n k 0 m st` draws `r ← Enc.Coins n` and answers
`cast _ (S.encryptAt n k m' r)`, keeping the state `st`. -/
theorem indImpl_enc_onSpec (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (m : (S.indSpec n).dom 0) (st : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n k 0 m st =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        .pure (cast (S.indSpec_encRng n).symm (S.encryptAt n k (cast (S.indSpec_encDom n) m) r),
          st) := by
  simpa only [cast_eq] using S.indImpl_enc atk b n k m st

/-- The repeated challenge equation on the query specification's type:
`S.indImpl atk b n k 2 mm (some c) = pure (cast _ c, some c)`, the recorded ciphertext `c` read at
the challenge oracle's answer type. -/
theorem indImpl_challenge_repeat_onSpec (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (mm : (S.indSpec n).dom 2) (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl atk b n k 2 mm (some c) = .pure (cast (S.indSpec_challengeRng n).symm c, some c) := by
  simpa only [cast_eq] using S.indImpl_challenge_repeat atk b n k mm c

/-- The codec of the adversary: the three oracles, and a one-bit final output. -/
def indCodec (n : ℕ) : MachineCodec (S.indSpec n) (Fin 1 → Bool) :=
  bitCodec (S.inLens n) (S.outLens n) 1

/-- The IND codec decodes a move using the bit-string decoder at its oracle lengths. -/
theorem indCodec_decodeMove (n : ℕ) (w : List Bool) :
    (S.indCodec n).decodeMove w = decodeBitMove (S.inLens n) (S.outLens n) 1 w :=
  bitCodec_decodeMove (S.inLens n) (S.outLens n) 1 w

/-- The IND codec records a log entry as the oracle index paired with its query and answer. -/
theorem indCodec_encodeEntry (n : ℕ)
    (e : Σ i, (S.indSpec n).dom i × (S.indSpec n).rng i) :
    (S.indCodec n).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  bitCodec_encodeEntry (S.inLens n) (S.outLens n) 1 e

/-- The IND codec returns the false verdict when its budget expires. -/
theorem indCodec_timeout (n : ℕ) : (S.indCodec n).timeout = zeroBits 1 :=
  bitCodec_timeout (S.inLens n) (S.outLens n) 1

/-- The game's codec is a bit codec: `S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1`. -/
theorem indCodec_eq_bitCodec (n : ℕ) : S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1 := rfl

/-- **The experiment `IND_b^{O₁,O₂}(Π, A, n)`** [PS10, Definition 168.1] for the attack `atk`, with
query budget `q`: sample `k ← Gen(1^n)` and `A`'s coins, run `A` against the oracles of `IND_b`
from the unchallenged state, and output its bit. -/
noncomputable def indGame (atk : Attack) (A : NUPPT) (q : ℕ) (b : Bool) (n : ℕ) : ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
  (simulate (S.indImpl atk b n (S.gen.runAt n [] rg)) (A.toComp (S.indCodec n) n q r) none).bind
    fun res => .pure (res.1 0)

/-- The IND experiment samples keys and adversary coins, simulates the recorded oracle
interaction from the unchallenged state, and returns the final bit. -/
theorem indGame_eq (atk : Attack) (A : NUPPT) (q : ℕ) (b : Bool) (n : ℕ) :
    S.indGame atk A q b n =
      (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
      (ProbComp.sample (A.Coins n)).bind fun r =>
      (simulate (S.indImpl atk b n (S.gen.runAt n [] rg))
        (A.toComp (S.indCodec n) n q r) none).bind fun res => .pure (res.1 0) := rfl

/-- **CPA, CCA1 or CCA2 security** [PS10, Definition 168.1]: for every non-uniform PPT `A` and
every polynomial query budget, `IND_0` and `IND_1` are indistinguishable: `A`'s advantage between
them is negligible. -/
def INDSecure (atk : Attack) : Prop :=
  ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n, advantage (S.indGame atk A (q.eval n) false n) (S.indGame atk A (q.eval n) true n) ≤ ε n

/-- IND security is exactly negligible advantage for every PPT adversary and polynomial
query budget, uniformly over the security parameter. -/
theorem INDSecure_iff (atk : Attack) :
    S.INDSecure atk ↔ ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n, advantage (S.indGame atk A (q.eval n) false n)
        (S.indGame atk A (q.eval n) true n) ≤ ε n := Iff.rfl

end FixedLengthScheme

end TCSlib.Cryptography.Composability
