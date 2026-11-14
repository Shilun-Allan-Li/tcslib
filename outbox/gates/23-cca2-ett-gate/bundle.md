## ===== briefs/pass-shelat-ch5-8/gates/23-cca2-ett/pack.md =====

# Gate 23 · Encrypt-then-tag is CCA2-secure (`cca2-ett`, Theorem 170.4)

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #306](https://github.com/Shilun-Allan-Li/tcslib/pull/306) at
  `c1a3ba5623febf318a56a0f84be885f262e0f86e` (branch `land/pass-shelat-cca2-ett`, tree
  `a64aea92b6384058304ee8cb8f48f61d97d4ad71`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `a757b6a18785377c158312ed051b1789cf45badf` (the merge base).
  - The fill was issued on `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`, the merge of #299.
  - Between the issue base and the PR base, two merged PRs change non-record files: #303 (merge
    `d82e9a50414c6be160bcb3bd63ffdeb95e41e21c`, the four ext-nosrc files under `Randomness/`) and #305 (merge
    `8d0db40144102b847921b51ee2d1ebfd2994836d`, `scripts/campaign_style_lint.py` only). Neither touches a file of this PR.
    Every other commit in that range, and every commit from the PR base to the current records tip, touches records
    only (`PassShelatChapter5-8Plan.md` and `briefs/`). The PR diff equals the unit's diff from the issue base.
- **Commits:** 10.
  - The Claude worker's 8 commits (job `cca2-ett`), rebased twice without conflict (patch ids unchanged; the 11 unit
    files byte-identical before and after each rebase): `a2a147c049bff43b66e10e0b9a2752d1feb9e264` (checkpoint 1, step
    1), `63ec9d0e6dd305d86b12405b56f70b14897dc849` (checkpoint 2, step 2), `82370f12a89db9f0677aadf61c3c689052784f51`
    (step 3), `5f10fc1b022994098340961e597151d1fe23cc45` (the combination), `3acee79b2508398f2c9528d9209c6c2f75b4404e`
    (published readers only, docstrings, lint), `c413c243399ade5832ff1f945be9981ba0d3c2c0` (the public width
    transport), `49309a4f15daf2790c58a543e88e05081839ce59` (general one-entry log readers) and
    `de6d7827454c7f1faed95c754d9d5c1024ad5e2c` (`rCnt` through its published reader). The worker's own hashes
    (head `b66a81a1af45bc158fa2405cf8150058a4a805b4`) reproduce exactly at the issue base.
  - Landing edit **LE-width** `edcbb3c14b58eec424f8c5444ca87d015a49ff19`: whitespace only, re-wrapping the 40 lines
    over 100 characters in 9 files.
  - Landing edit **LE-doc** `c1a3ba5623febf318a56a0f84be885f262e0f86e` (the head): 94 formula docstrings, 15 proof
    sketches and `## Main definitions` in `Forgery` and `Transfer`; docstrings only.
- **Scope:** a **proof audit**. The job proves the admitted `Composability.ccaScheme_cca2` [PS10, Theorem 170.4]:
  Algorithm 169.3 (the §3.9 scheme with its ciphertext `(r, c₁)` tagged by `f_{k₂}(r ‖ c₁)`) is CCA2-secure when `F`
  is a PRF. Its statement passed Gate 06 and is frozen.
- **Brief:** `fills/cca2-ett/issued-r1/brief.md` on the records branch (SHA-256 `ebffc522…`; exchange pack
  `3f8f3744`): three checkpoints following the docstring sketch, the owned file plus the helper directory
  `EncryptThenTag/` only, `Games/Efficiency.lean` frozen, the duplication rule with "PRFGame overlap" disclosures,
  and the evidence-completeness rule.

## What changed

All paths are under `TCSlib/Cryptography/Encryption/PrivateKey/`. The PR touches 11 Lean files: 1 modified and 10
new (5364 insertions, 31 deletions).

| File | Status | Lines |
|---|---|---:|
| `EncryptThenTag.lean` | owned, modified | 753 |
| `EncryptThenTag/CPAHandler.lean` | helper, new | 806 |
| `EncryptThenTag/CPAReduction.lean` | helper, new | 370 |
| `EncryptThenTag/Forgery.lean` | helper, new | 559 |
| `EncryptThenTag/Games.lean` | helper, new | 460 |
| `EncryptThenTag/Handler.lean` | helper, new | 886 |
| `EncryptThenTag/Lazy.lean` | helper, new | 630 |
| `EncryptThenTag/Machines.lean` | helper, new | 359 |
| `EncryptThenTag/Reduction.lean` | helper, new | 395 |
| `EncryptThenTag/Tools.lean` | helper, new | 295 |
| `EncryptThenTag/Transfer.lean` | helper, new | 222 |

No facade changes: `PrivateKey.lean` and `Encryption.lean` are untouched, as is `Games/Efficiency.lean`.

The proof has four steps, each an equality or a bound at every `n` (step 2 at `n > 0`; REPORT § 1, review § Content).
Write `P_b` for the acceptance of the CCA2 game with challenge bit `b`.
1. **Tag key → random function** (`cca_tag_step`, from `ETTGame.exists_tagStep`):
   `|P_b − 𝔼_{k₁} 𝔼_R ettAcc(f_{k₁}, R, rej = false, b)| = prfAdv(F_{2n}, D_b)` for a PRF distinguisher `D_b` at
   parameter `2n` (T2 handler `dHandler`, T4 at length `2n`).
2. **Fresh decryption queries rejected** (`cca_rej_step`, from `ETTGame.abs_ettAcc_rej_sub_le`): for `n > 0` the
   rejecting experiment differs by at most `q(n) · 2^{−2n}` (identical-until-bad and a union bound).
3. **The rejecting experiment is a CPA experiment of the §3.9 scheme** (`ETTGame.exists_cpaStep`): lazy tags
   (`Lazy.lean`, `expect_ettImpl_lazy`), the handler `bHandler` (`CPAHandler.lean`) from the CCA2 oracles to the CPA
   oracles `PRFGame.fImpl`, and the reduction (`CPAReduction.lean`) give one machine `B`, independent of `b`.
4. **The CPA experiment hides the bit** (owned file): `PRFGame.exists_prfReduction` gives `C_b`, with
   `ETTGame.prfAdv_eq_expect`, and `PRFGame.abs_expect_fImpl_sub_le` gives the collision term `Q(n)²/2ⁿ`,
   `Q = qRed q`.

**Combination:** for `n > 0`,
`|P₀ − P₁| ≤ adv(D₀) + adv(D₁) + 2q(n)/2^{2n} + adv(C₀) + adv(C₁) + Q(n)²/2ⁿ`; the witness adds
`if n = 0 then 1 else 0`. Negligibility uses `PRF.negligible_prfAdv` for `D_b` composed with `n ↦ 2n`
(`Negligible.comp_of_le`) and for `C_b`, then `Negligible.add`.

The edge cases are `n = 0` (including the malformed-but-accepted four-bit words of the module's source notes), budget
0, no challenge, repeated challenges, `Dec′` on the challenge or on a word with the challenge's pair, malformed and
over-long words, nonce collisions and codec timeouts.

**Statements:** decls2 from the issue base to the head gives 249 ADDED, 0 CHANGED, 0 REMOVED. The target's header and
the other 24 pre-existing declarations of the owned file are byte-identical; only the target's body and sketch
changed.

## Rulings and records in force (2026-11-14)

1. **Rule 10: a `CoeFun`/`Coe` instance whose body is a structure projection is notation (Seyoon).** This is
   `FinDist`'s `⟨FinDist.prob⟩`, treated like reducible abbreviations (ruling of 2026-10-26). The coe-variant seals
   are canonical, and the strict variant (the archived Gate 10 harness, which also seals instances) is still run with
   its differences attributed. **For this unit the two variants agree:** seals A and B pass for all 11 files at the
   head and for the owned file at the base, with 0 failing declarations in either variant. So no result here rests on
   the ruling.
2. **The facade-completeness lint fix, #305 (Seyoon's ruling to fix the bug by a PR on our branch; merged by
   Seyoon).** `check_facade` now walks intermediate facades. The Cryptography lint baseline is now **92 FAIL /
   102 WARN**. At the head the lint gives 92 / 102 with the same FAIL and WARN lines as the records tip
   (`ledoc-evidence.zip`: `logs/lint-crypto-tip-vs-head-r3.diff`, empty).
   - Under the old lint the unit raised the count from 216 to 235 FAIL: **19 facade-completeness FAILs**, because
     the frozen `PrivateKey.lean` and `Encryption.lean` do not import the 10 helpers directly. The maintainer review
     accepted them as recorded (finding 4, the consolidation precedent; a Cryptography-wide facade sweep is a
     follow-up). **Under #305 they are false positives and are moot.** The frozen facades were not edited.
   - Brief-scoped lint (`PrivateKey`, `--check8b`): 0 FAIL / 5 WARN at the base and at the head.
3. **The landing edits are the maintainer's** (the ext-nosrc and nm-sim precedents; decision log rows of 2026-11-14).
   - **LE-width** is whitespace only: every file's token sequence is unchanged (`landing/lewidth-wscheck.txt`).
   - **LE-doc** is docstrings only: its 108 hunks all lie inside doc comments (`/-- -/` or `/-! -/`); with doc
     comments blanked, all 11 files are byte-identical; the 372 declaration headers are byte-identical; decls2 against
     the LE-width head is empty. The target's docstring is untouched: it keeps its book-statement first line and its
     `[PS10, Theorem 170.4]` tag.
4. **The disclosed route deviation** (REPORT § 1, "Deviation from the route"; review § Content). The brief's step 3
   suggested `prfFixedScheme_cpa` and `PRFGame.lazyImpl`. The proof instead builds the CPA adversary `B` against
   `PRFGame.fImpl` and assembles the CPA bound from `PRFGame.exists_prfReduction`, `PRFGame.abs_expect_fImpl_sub_le`
   and `ETTGame.prfAdv_eq_expect`. The worker's reason: going through `prfFixedScheme_cpa` would need the private
   readers of `OracleFromPRF.lean`, and `lazyImpl` has `n`-bit points while the tags need `2n`-bit points with the CCA2
   table and record. The maintainer review found the route sound and accepted it. The statement is unchanged; the brief
   allowed the worker to edit the sketch to describe the delivered proof. **Not a finding** unless the route is
   unsound or its sketch misdescribes it.

## What is frozen

- **The target's statement** (quoted in the brief), the 24 other pre-existing declarations of `EncryptThenTag.lean`,
  the statement prose, the module's source notes and the global simp attributes.
- **Every file outside** `EncryptThenTag.lean` and `EncryptThenTag/`. That includes the facades `PrivateKey.lean` and
  `Encryption.lean`, the `OracleFromPRF/` files whose public API the proof imports, and `Games/Efficiency.lean`.
- **The landing edits:** LE-width changes whitespace only, and LE-doc changes docstrings only.

## Questions for the audit

**1. Correctness against [PS10, Theorem 170.4]**
- Does the proof establish the frozen statement for every adversary, budget polynomial `q` and challenge bit,
  including `n = 0`, budget 0, no challenge and repeated challenges?
- Step 1: is `D_b` a legitimate PRF distinguisher at parameter `2n`, and is the transport back to `n` through
  `Negligible.comp_of_le` correct?
- Step 2: is `q(n) · 2^{−2n}` a correct bound for accepting a fresh decryption query, including a valid word that
  carries the challenge's pair, the challenge with a changed tag, and malformed words?
- Step 3: is the lazy-tag experiment (`tagOf`, `lazyDec`, `expect_ettImpl_lazy`) equal in law to the rejecting
  experiment, with no tag-collision term? Is `bHandler` a uniform, polynomial-time handler for every outer answer, and
  does `comp_bAbs` with `expect_simulate_abs_inv` under the invariant `bInv` lift to whole runs?
- Step 4 and the combination: is `Q(n)²/2ⁿ` the right collision term for the §3.9 scheme with `Q = qRed q`, and is the
  final sum, with the `n = 0` correction, negligible?
- Does the edited target sketch describe the delivered proof?

**2. The route deviation (ruling 4)**
- Is assembling the CPA bound from `exists_prfReduction`, `abs_expect_fImpl_sub_le` and `prfAdv_eq_expect` a sound
  substitute for `prfFixedScheme_cpa`? Does any step use a private lemma of `OracleFromPRF/` rather than its published
  readers?

**3. Frozen-statement integrity**
- Are the target's header and the other 24 pre-existing declarations byte-identical (`landing/header-bytes.txt`,
  `landing/decls2.tsv`, `landing/touched.tsv`)? Is every changed path inside the owned file and helper directory?

**4. Rule 10 (ruling 1)**
- Do the seals, collected from the elaborated terms plus matchers, cover every touched declaration of the 11 files over
  the full closure, at the base and at the head, in both variants (`landing/seal-table.txt`)?
- Do the paired controls (20 probes, 51 sealed negatives, ALL_OK; `landing/ctlcheck.log`) show that the seals bite?
- Explicit-unfold scan: 2290 items at the head and 88 at the base, 0 foreign definitions.
- The new abbreviations `St`, `tagOut`, `LEntry` and `LSt` are notation, each with an `_eq` reader.

**5. LE-doc formula and sketch accuracy**
- Does each of the 94 new formulas state what its declaration proves or defines, and does each of the 15 new sketches
  describe its proof (`landing-ledoc/0001-LE-doc.patch`; `docaudit-after.tsv` 249 OK plus the target,
  `sketchaudit-after.tsv` 0 missing)? A formula or sketch that misstates its declaration is a minor.
- Is LE-doc docstrings only, as ruling 3 records?

**6. Duplication**
- Does any new declaration duplicate a public TCSlib or Mathlib lemma beyond DL-40 (below)?
- Is any private lemma of another file copied rather than re-derived from published readers, beyond the disclosed
  PRFGame overlaps?

## Known dispositions (not findings)

- **DL-40** (duplication ledger, open, deferred):
  - undisclosed: `ETTGame.eval_toOracleAdversary_len` generalizes the public `PRFGame.eval_toOracleAdversary_width`
    (its case `ℓ = n`);
  - disclosed: `ETTGame.zipWith_xor_cancel` has the statement of four private `zipWith_xor_xor_self` copies (`FromPRF`,
    `FromPRG`, `SpecialEncryption` and the owned file's own copy); `ETTGame.prfAdv_eq_expect` re-derives the private
    `prfAdv_prfReduction`;
  - generic or parallel restatements, none an exact copy: `ETTGame.tapeImpl` with `simulate_tapeImpl_congr` and
    `expect_simulate_tapeImpl` (AdaptiveCPA), the `recBits` family and `ovr` (PRFGame), `expect_simulate_abs`
    (`Games.simulate_eq_of_abs_bounded`) and a private `abs_expect_sub_le_expect` (`ProbComp.abs_expect_sub_le`).
  What you can raise: a copy outside DL-40, or a disagreement with it.
- **The disclosed PRFGame overlaps** (`rY_one`, `log_ne_nil`, the handler-field readers; REPORT § 4): private lemmas of
  `OracleFromPRF/` re-derived from published readers. Accepted (review finding 8).
- **The 19 old-lint facade FAILs:** moot under #305 (ruling 2).
- **No top-level manifest** in the delivery: the brief requires only `evidence/SHA256SUMS` (review finding 9).
- **Soft size target:** `Lazy.lean` has 630 lines, an INFO line over the 600-line soft target; the hard limit is 1000.
- **The census count:** 551 stored constants are 551 census rows; 6 names occur twice (private and generated names
  repeated in `Handler` and `CPAHandler`), so there are 545 distinct names (`logs/census-base-vs-head.txt` in
  `review-evidence.zip`).
- **The review's verdict line** says LE-doc "waits for its rebuild". Its closing LE-doc section records the build that
  followed; the review record is not edited.

## Also check

**Axioms**
- The target prints `[propext, Classical.choice, Quot.sound]`. At the base it also had `sorryAx`.
- All 551 stored constants of the 11 files use subsets of those three (the review's census; LE-width and LE-doc change
  no code).
- Nothing new is `@[simp]` or an instance.

**Admissions:** 24 → 23 in the 10 issued modules; only the target is removed (`landing/sorry-census-r2.txt`).

**Sizes and widths:** 222–886 lines per file; 0 lines over 100 characters (`source-head.json`).

**Build:** at `c1a3ba56`, the 19 changed and downstream modules (the 10 helpers, `EncryptThenTag`, `PrivateKey`,
`Encryption`, `Composability`, #303's 4 base-delta modules and root `TCSlib`) have rc 0, 0 errors and 0 sorries
(`landing/root-checks.jsonl`), and the whole-tree check passes for 1211 modules at the head's source and olean hashes
(`landing/final-tree-check.txt`). No `audits/*/Checks` module imports the unit. The olean tree was restored to the
base snapshot afterwards.

## Evidence

- **`review.md`:** the maintainer's delivery review, verdict ACCEPT WITH LANDING EDITS, with its LE-doc section at the
  end.
- **`verification.zip`** (43 entries): every file the review cites, as byte-identical originals. Its `SHA256SUMS`
  lists every other entry, and `PROVENANCE.txt` gives each entry's source. It holds:
  - `review-evidence.zip` (`fills/cca2-ett/final-r1/`, SHA-256 `766872ef…`, 446 entries) and
    `review-evidence-SHA256SUMS`, its manifest; `unzip -Z1` lists exactly the manifest's paths. It covers integrity,
    the base and head builds, the full-tree check and the restore, decls2, header bytes, `touched`, the docstring and
    sketch audits, the census and axioms, the strict and coe-variant seals at the base and the head, the paired
    controls, the scan, lint, sizes and the duplication grep;
  - `ledoc-evidence.zip` (SHA-256 `38505c81…`, 116 entries) and `ledoc-evidence-SHA256SUMS`: the LE-doc patch, the
    docstring-only checks, the rebase onto `a757b6a1`, the build at the head, the #305 lint and the restore;
  - `landing/` and `landing-ledoc/`: the review's extracts, each a byte copy of an entry of the matching ZIP;
  - `records/`: the issue package `fills/cca2-ett/issued-r1/`, the duplication ledger, the decision log and the #305
    record `maintainer/lint-facade-fix-2026-11-14/` (README and patch), at records
    `65d89e5700b283e5b9d373335c78b0cf8391bd35`;
  - no `worker/` folder: this worker made no scope request and needed no authorization.
- **The worker's own evidence:** on the exchange at `74f0ba5ffcf82e33c6b3be5da7ba63087a1bca07`, under
  `inbox/fills/cca2-ett/evidence/`. Its `SHA256SUMS` lists 118 files, all delivered.
- **`landing/`:** at the final head.
  - `root-checks.jsonl`: the 19 modules at `c1a3ba56`, rc 0, each changed file's `source_sha256` matching
    `source-head.json` (= `build/results.jsonl` of `ledoc-evidence.zip`).
  - `final-tree-check.txt`: 1211/1211 modules at `c1a3ba56`'s source and olean hashes
    (= `build/tree-check-head.txt` of `ledoc-evidence.zip`).
  - `axioms-head.txt`: the review's census summary (= `final-r1/landing/census-summary.txt`); LE-width and LE-doc change
    no code.
- **`worker-report.md`:** the worker's `REPORT.md`, at exchange `74f0ba5f`.
- **`pr.diff.txt`:** `git diff` from the base to the head (11 paths, 5364 insertions, 31 deletions).
- **`source-head.json`:** the head hashes, line counts and over-width counts of the 11 changed files.
- **`sources.zip`:** the source closure at the head of every changed module, 172 files.

## Findings delivery

Return `gate23-cca2-ett-findings.md` as a Markdown file in this chat. If you have several evidence files, return a
ZIP. The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish the frozen statement, or a change outside
  the owned file and helper directory.
- **major:** a changed frozen statement, a forbidden read in a touched declaration not covered by the rulings, an
  undisclosed copied private lemma, or necessary evidence that cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring or proof sketch.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.

## ===== briefs/pass-shelat-ch5-8/gates/23-cca2-ett/review.md =====

# cca2-ett · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS.** The landing edit **LE-width** is done. The landing edit **LE-doc**
(formula docstrings, proof sketches and module contents) has been written and waits for its rebuild.

## Delivery and landing branch

**The delivery**
- **Source:** Claude worker, exchange `74f0ba5ffcf82e33c6b3be5da7ba63087a1bca07` (`inbox/fills/cca2-ett/`). The
  checkpoints were `ad6b9ec3` and `60778ff1`.
- **Worker head:** `b66a81a1af45bc158fa2405cf8150058a4a805b4`, 8 commits on the issue base `eff2dcd0`. The commit
  hashes reproduce exactly.
- **Target:** `Composability.ccaScheme_cca2 (hF : PRF F) : (ccaScheme F E hE hFE).INDSecure .cca2`, [PS10,
  Theorem 170.4]: encrypt-then-tag is CCA2-secure. The brief is `../issued-r1/brief.md`.
- **Files:**
  - the owned file `PrivateKey/EncryptThenTag.lean`;
  - 10 new helpers under `PrivateKey/EncryptThenTag/`: `CPAHandler`, `CPAReduction`, `Forgery`, `Games`,
    `Handler`, `Lazy`, `Machines`, `Reduction`, `Tools` and `Transfer`.
- **Untouched:** no other file changes. In particular the frozen facades and `Games/Efficiency.lean` are untouched.

**The landing branch** is `land/pass-shelat-cca2-ett`.
- **Base:** the worker commits are rebased onto records tip `48cd45ab291695f07da6093b4756fea446a4296b`, which contains
  the #303 merge `d82e9a50`. The rebase had no conflict, and the unit's files are byte-identical before and after it.
- **Head:** `8c3e6496a8ce95c77e61067ad3067394081ed80b` (**LE-width**), tree `9ecb64f2cc73b51361bcf7d217b7a1422d8b14ab`.
  The commits are listed in `landing/commits.txt`.
- **LE-width:** it re-wraps 40 lines over 100 characters, in 9 files. It is whitespace only: every file's token
  sequence is unchanged (`landing/lewidth-wscheck.txt`).

**The evidence** is in `review-evidence.zip`.
- SHA-256 `766872ef1e358fe9fc56bbeb9de833870af95a8dd9097aaee02308f9ec58773f`, 446 entries.
- Its manifest is `evidence-SHA256SUMS`, and `unzip -Z1` lists exactly the manifest's paths.
- Extracts are in `landing/`, and the full provenance is in `landing/PROVENANCE.txt`.

## Checks

**Integrity**
- The issue package verifies 7/7, its `SOURCE-SHA256SUMS` 264/264, and `evidence/SHA256SUMS` 118/118. The delivered
  paths are exactly the manifest's.
- `git am` at the base gives rc 0. The 11 paths are byte-identical to `src/`.
- Every foreign name the delivery uses exists at the base. That includes `InteractiveHandler.rCnt_input` and
  `Games.expect_toCompOn_outLen`.

**Build**, on the full base tree `$SP/dl-oleans`
- All 11 unit modules and `PrivateKey`, `Encryption`, `Composability` and root `TCSlib` give rc 0, with 0 errors,
  0 warnings and 0 sorries. This holds both before and after LE-width.
- #303's modules were built as base-delta modules.
- The final whole-tree check passes: 1211 modules plus 31 PFR modules are at the head's source and olean hashes.
- No `audits/*/Checks` module imports the unit.
- **Restore:** the tree is byte-identical to the pre-review snapshot (`landing/tree-check-post.txt`).

**Statements** (against `eff2dcd0`)
- decls2 gives 249 ADDED, 0 CHANGED, 0 REMOVED.
- The target's header, and the other 24 pre-existing declarations of the owned file, are byte-identical.
- Only the target changed, in its body and its sketch.

**Axioms**
- All 551 stored constants use only `propext`, `Classical.choice` and `Quot.sound`. The target no longer uses
  `sorryAx`.
- There are no new `@[simp]` lemmas and no instances.
- The new abbreviations `St`, `tagOut`, `LEntry` and `LSt` each have an `_eq` reader.

**Rule 10**
- The whole-file seals A and B pass for all 11 files at the head and for the owned file at the base. Both the
  coe variant (canonical) and the strict variant were run. There are 0 failing declarations, and the two variants
  agree.
- Paired controls: 20 probes and 51 sealed negatives, ALL_OK.
- The explicit-unfold scan finds 0 foreign definitions (2290 items at the head, 88 at the base).

**Admissions:** 24 → 23. Only the target was removed (`landing/sorry-census-r2.txt`).

**Lint, sizes and widths**
- **Sizes:** the files have 218–835 lines.
- **Widths:** at most 100 characters after LE-width.
- **Cryptography-wide lint:** 216 → 235 FAIL. All 19 new FAILs belong to the facade-completeness class: the frozen
  `PrivateKey.lean` and `Encryption.lean` do not import the 10 helpers. See finding 4.
- **Brief-scoped lint** (PrivateKey, `--check8b`): 0 FAIL and 5 WARN, both at the base and at the head.

**Content.** The proof has four steps:
1. **PRF tag key.** The tag key is replaced by a random function, at the cost of a PRF advantage at `2n`.
2. **Fresh decryptions.** Rejecting fresh decryption queries costs at most `q/2^{2n}`. The argument is
   identical-until-bad plus a union bound.
3. **Lazy tags.** With lazy tags, the rejecting experiment is the CPA experiment of the §3.9 scheme.
4. **CPA bound.** That CPA experiment is bounded by two PRF advantages plus the collision term `Q²/2ⁿ`.

The case `n = 0` is covered by an eventually-zero correction. The proof's route differs from the brief's
suggestion: it uses `fImpl` and `exists_prfReduction` directly, instead of `prfFixedScheme_cpa` and `lazyImpl`. The
worker disclosed this, and the route is sound. The following edge cases are covered by whole-simulation
equalities: malformed words, a refused challenge, repeated challenges, nonce collisions and timeouts.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| 1 | low | 40 lines are over 100 characters, in 9 files. | **Fixed** by LE-width `8c3e6496`. |
| 2 | medium | 94 new public declarations have docstrings without a formula (`landing/docaudit-head-le.tsv`). `Forgery` and `Transfer` have no `## Main definitions` section. | **LE-doc**, docstrings only, following the ext-nosrc and nm-sim precedents. It is written; the rebuild is pending. |
| 3 | low | 15 proofs of 15 or more lines have no `**Proof sketch.**` (`landing/sketchaudit.tsv`). Six of them are public. | **LE-doc**, following the nm-sim LE-D2 precedent. |
| 4 | low | 19 new facade-completeness FAILs, from `PrivateKey.lean` and `Encryption.lean`. The same class is pre-existing: the base has 173 such FAILs, including `PrivateKey.lean` for `OracleFromPRF/*` and 48 in `Encryption.lean`. | **Accepted as recorded**, following the consolidation precedent (+4). A Cryptography-wide facade-completeness sweep is the clean fix, and is recorded as a follow-up. Changing frozen facades for this unit alone would be inconsistent with the `OracleFromPRF` precedent. |
| 5 | low | Undisclosed near-duplicate: `ETTGame.eval_toOracleAdversary_len` generalizes the public `PRFGame.eval_toOracleAdversary_width` (its case `ℓ = n`). | Ledger **DL-40**. |
| 6 | low | Disclosed duplicates. `ETTGame.zipWith_xor_cancel` has the same statement as four private `zipWith_xor_xor_self` copies: in `FromPRF`, `FromPRG` and `SpecialEncryption`, and the owned file's own copy. `ETTGame.prfAdv_eq_expect` re-derives the private `prfAdv_prfReduction`. | Ledger **DL-40**. |
| 7 | low | Generic or parallel restatements, none of them exact copies: `ETTGame.tapeImpl` with `simulate_tapeImpl_congr` and `expect_simulate_tapeImpl` (AdaptiveCPA); `recBits`; `ovr` (PRFGame); `expect_simulate_abs` (`Games.simulate_eq_of_abs_bounded`); and a private `abs_expect_sub_le_expect` (`ProbComp.abs_expect_sub_le`). | Ledger **DL-40**. The worker's promotion requests cover most of them. |
| 8 | info | The disclosed PRFGame overlaps (`rY_one`, `log_ne_nil`, the handler-field readers) and the disclosed route deviation (see Content). | Accepted. |
| 9 | info | The delivery has no top-level manifest. The brief requires only `evidence/SHA256SUMS`. | Recorded. |

## LE-doc · `c1a3ba56` (built)

- **Head:** `c1a3ba5623febf318a56a0f84be885f262e0f86e`, tree `a64aea92b6384058304ee8cb8f48f61d97d4ad71`.
- **Change:** 94 formula docstrings, 15 proof sketches, `## Main definitions` in `Forgery` and `Transfer`. Docstrings only:
  - every hunk lies inside a doc comment, and with doc comments blanked the files are byte-identical;
  - all headers are byte-identical, and decls2 against the previous head is empty;
  - every new public declaration now passes the docaudit, except the target, whose first line is prose.
- **Rebase:** The branch was rebased onto `a757b6a1`; the unit files are byte-identical, and LE-width is now `edcbb3c1`.
- **Build** on `$SP/dl-oleans`: 19 modules (the 11 unit modules, `PrivateKey`, `Encryption`, `Composability`, the #303 base-delta modules, root `TCSlib`) rc 0; full head check 1211 modules OK. The tree was restored to the base snapshot afterwards.
- **Lint (#305):** 92 FAIL / 102 WARN, with the same lines at the head as at the records tip.
- **Evidence:** `ledoc-evidence.zip`, SHA-256 `38505c81c18bfc28982d47e63c56c6b7f363024439e4d9210054d13920836416`, 116 entries. Its manifest is `ledoc-evidence-SHA256SUMS`, and extracts
  are in `landing-ledoc/`.
- **PR:** draft [PR #306](https://github.com/Shilun-Allan-Li/tcslib/pull/306).

## ===== briefs/pass-shelat-ch5-8/gates/23-cca2-ett/worker-report.md =====

# Fill cca2-ett — final

**Unit** `cca2-ett` · **Worker** Claude · **Issue base** `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`
(`cryptography/pass-shelat-ch2-4`, the merge of #299) · **Proof branch** `fill/cca2-ett` (local),
head `b66a81a1a` · **Lean** 4.25.0, Mathlib at the base's manifest.

**Target status: proved.** `Composability.ccaScheme_cca2` (PS10 Theorem 170.4) has a complete proof;
its statement is unchanged. `#print axioms ccaScheme_cca2`: `[propext, Classical.choice, Quot.sound]`.
The final sweep of the supplied order (with the ten helper modules inserted before the owned module)
has 0 errors, and the `sorry` census is `base-sorries.txt` minus `ccaScheme_cca2` (§5).

Commits on the proof branch (the patch series in `patches/`):
`9015e943d` checkpoint 1 (step 1), `9262d2ba6` checkpoint 2 (step 2), `3fc373bb6` step 3,
`af9fdc724` the combination, `731efd9ed` published readers only (seal fixes), docstrings, lint,
`c68fc02eb` the public width transport, `c5e21bc04` general one-entry log readers, `b66a81a1a`
`rCnt` read through its published reader (found by the explicit-unfold scan).

## 1. The proof

Fix a machine adversary `A`, a budget polynomial `q` and a bit `b`; `P_b = Pr[IND_b(A, q(n), n) = 1]`
for the CCA2 game of `π′`. Four steps, each an equality or a bound at every `n` (step 2 at `n > 0`):

1. **Tag key → random function** (checkpoint 1; `cca_tag_step`, from `ETTGame.exists_tagStep`):
   `|P_b − 𝔼_{k₁} 𝔼_R ettAcc(f_{k₁}, R, rej = false, b)| = prfAdv(F_{2n}, D_b^{q(2n)})` for a
   next-query machine `D_b` (T2 handler `dHandler` with `k₁` and nonce tapes in its seed, a budget
   cap, T4 at length `2n`, parameter halving; §7.2 below).
2. **Fresh decryption queries rejected** (checkpoint 2; `cca_rej_step`, from
   `ETTGame.abs_ettAcc_rej_sub_le`): for `n > 0`,
   `|𝔼_{k₁}𝔼_R ettAcc(…, rej = false, b) − 𝔼_{k₁}𝔼_R ettAcc(…, rej = true, b)| ≤ q(n) · 2^{-2n}`.
3. **The rejecting experiment is a CPA experiment of the §3.9 scheme** (new;
   `ETTGame.exists_cpaStep`): there is one machine `B` (independent of `b`) with, for every `b`,
   `n` and pad function `f`,
   `𝔼_R ettAcc(f, R, rej = true, b, A, q(n)) = 𝔼_{r_B} 𝔼[⟦B's output⟧₀ = 1 | simulate (PRFGame.fImpl … (atkOf false) b f) (B.toComp … (qRed q)(n) r_B) none]`.
   - *Lazy tags* (`Lazy.lean`, `expect_ettImpl_lazy`): averaged over `R`, the rejecting experiment
     is the experiment whose state is the challenge record and the table of `Enc′` answers
     `(r ‖ c₁, tag, m)`, newest first; a pair gets the table's tag, else the challenge's, else a
     fresh tape (`tagOf`); `Dec′` refuses the record and answers a well-formed word from the table
     (`lazyDec`). Proof: induction with `R` overridden by the table's tags (`ovr`, `tagTbl`); a new
     pair moves `R`'s value into the table (`expect_sample_ovr`); decryption answers agree because
     the entry's pair is `r ‖ (m ⊕ f(r))` with an `n`-bit `m` (`LInv`, `decAnsW_tagTbl`).
     With tapes in advance: `expect_ettLazyTape` (generic `expect_simulate_tapeImpl`).
   - *The handler* (`CPAHandler.lean`, `bHandler`): a `Games.InteractiveHandler` from the CCA2
     oracles (`ettDin`, `ettDout`) to the CPA oracles of the §3.9 scheme (`PRFGame.pkDin`,
     `pkDout`). Seed: `q(n)` tag tapes of `2n` bits. State: the table word (`GGMRed.tblEnc` of the
     entries, read with GGM's public `GGMRed.lookup`/`lookup_tblOf`, `lookup_tblW`), `1^j`, the
     record. `Enc′` asks the CPA encryption oracle, tags `⟨r, c₁⟩` as `tagOf` does with tape `j`,
     adds the entry; `Dec′` answers `lazyDec` with no outer query; a first challenge asks the CPA
     challenge oracle, tags and records; a repeated one repeats the record. Every word read from an
     outer answer is padded to its length (`EnsembleLemmas.padL`), so the round function is total
     and polynomial-time (`polyTimeComputable_bRun`), for every outer answer. Answer lemmas:
     `bHandler_impl_enc`, `_dec`, `_challenge_some`, `_challenge_none`.
   - *The reduction* (`CPAReduction.lean`): each call of the handler composed with
     `PRFGame.fImpl` has, from `bAbs ((o, L), j)` (handler state `bState j L o`, CPA record
     `o.map cpaRec`), the law of the call of `ettLazyTape` from `((o, L), j)` (`comp_bAbs`), under
     the invariant `bInv` (`|L| ≤ j`, `n`-bit messages; kept by `ettLazyTape_bInv`) and `j < q(n)`;
     `expect_simulate_abs_inv` (generic, `Tools.lean`) lifts this to whole runs of the adversary
     (at most `q(n)` queries). T2 (`exists_interactiveHandlerMachine`) for `bHandler`, the
     input-free companion of `A`, and `NUPPT.exists_comp` (pre `⟨[], ·⟩`) give `B` with budget
     `qRed q` (`= q·1 + 0`).
4. **The CPA experiment hides the bit** (owned file, `ccaScheme_cca2`): `PRFGame.exists_prfReduction B (qRed q) false b`
   gives `C_b` with `prfAdv(F_n, C_b^{qRed(qRed q)}) = |𝔼_k K_b(f_k) − 𝔼_R K_b(R)|`
   (`ETTGame.prfAdv_eq_expect`), and `PRFGame.abs_expect_fImpl_sub_le` (CPA: `decOpen_atkOf`;
   `ctP = 3n + 2`; `2n`-bit challenge queries) gives `|𝔼_R K_0(R) − 𝔼_R K_1(R)| ≤ Q(n)²/2ⁿ`,
   `Q = qRed q`.

**Combination.** For `n > 0`:
`|P₀ − P₁| ≤ adv(D₀) + adv(D₁) + 2 q(n)/2^{2n} + adv(C₀) + adv(C₁) + Q(n)²/2ⁿ` (linear arithmetic on
the two-sided forms of the seven facts). The witness is that sum plus `if n = 0 then 1 else 0`
(at `n = 0` the advantage is at most `1`, `advantage_le_one`; the other terms are nonnegative,
`prfAdv_nonneg`). Negligibility: `PRF.negligible_prfAdv` for `D_b` at budget `q` composed with
`n ↦ 2n` (`Negligible.comp_of_le`) and for `C_b` at budget `qRed (qRed q)`;
`2 q(n) 2^{-2n} ≤ 2 · q(n) (1/2)ⁿ` (`EnsembleLemmas.negligible_polyExpr_mul`,
`negligible_two_pow_neg`, `Negligible.const_mul`, `Negligible.mono`); `Q(n)²/2ⁿ = (Q·Q)(n) (1/2)ⁿ`;
the `n = 0` correction is eventually `0` (`negligible_zero.mono`); `Negligible.add`.

**Deviation from the route (documented; no statement changed).** The brief's step 3 cites
`prfFixedScheme_cpa` and, for the tags, `lazyImpl`. The proof uses instead PRFGame's public API
directly: the CPA adversary `B` is built against the oracles `PRFGame.fImpl` (the brief's "CPA
oracles"), and the CPA bound for `B` is assembled from `PRFGame.exists_prfReduction`,
`PRFGame.abs_expect_fImpl_sub_le` and `ETTGame.prfAdv_eq_expect`. Going through
`prfFixedScheme_cpa` would have required turning `B` into an adversary of the IND game of
`prfFixedScheme`, i.e. re-deriving the private readers of `OracleFromPRF.lean`
(`accept_prf_indGame`, `ofFn_prf_encryptAt`, …). `PRFGame.lazyImpl` is the §3.9 experiment's lazy
pad function (`n`-bit points, the §3.9 record); the tags need `2n`-bit points with the CCA2 table
and record, hence the ETT-specific `Lazy.lean` (on the generic `ovr`/`expect_sample_ovr` of
`Tools.lean`). Lazily sampled tags agree with `RF` on repeated pairs, so no tag-collision term
appears; the only collision term is PRFGame's `Q²/2ⁿ` (nonce collisions of the §3.9 scheme).

**Edge cases.**
- `n = 0`: steps 1, 3, 4 hold at every `n`; step 2 needs `n > 0`, and the witness adds `1` at
  `n = 0`. The transfer (step 1) matches every decryption answer, including the malformed four-bit
  words that decrypt at `n = 0` (same total projections `wR`, `wC`, `wT` and guards `validW`).
- Budget 0, no challenge, repeated challenges: all equalities are by induction on the adversary's
  computation (a returned value is the base case); repeated challenges answer the record in every
  experiment (`ettStep_challenge_some`, `lazyStep_challenge_some`, `bHandler_impl_challenge_some`).
- `Dec′` on the challenge: refused (`refW`) in every experiment; on the challenge with a changed
  tag or another word with the challenge's pair: rejected as a fresh pair in the rejecting
  experiment, and (step 2) a valid such query is the challenge itself for `n > 0` (canonical
  parsing, `eq_ctW_of_wfW`); malformed and over-long words: `wfW` fails, `⊥`; an earlier `Enc′`
  answer: the table's message (`decAnsW_tagTbl`).
- Nonce collisions: two `Enc′` answers with the same pair `r ‖ c₁` read the same tag (the table is
  read first, `tagOf`), as with a random function; the CPA bound carries the §3.9 collision term.
- Codecs' timeout outputs: each step is an equality of whole simulations of `A.toComp (bitCodec …)`
  (or of the machines from T2/T4, whose `toCompOn` equalities hold for every answer), so the
  timeout outputs are the same on both sides; the handlers read every outer answer, of every
  value, through padding.

## 2. Changed and new files

| File | Lines | Role |
|---|---|---|
| `PrivateKey/EncryptThenTag.lean` (owned) | 739 | readers of `ccaScheme`; steps 1, 2 (private); the proof of `ccaScheme_cca2` |
| `EncryptThenTag/Tools.lean` | 293 | generic: simulation through an abstraction in law (`expect_simulate_abs`, `_inv`), coins in advance, `ovr` |
| `EncryptThenTag/Machines.lean` | 352 | budget cap, parameter halving, width transport |
| `EncryptThenTag/Games.lean` | 437 | the CCA2 experiment with pad `f` and tag `g` |
| `EncryptThenTag/Handler.lean` | 833 | T2 handler of the tag-key PRF reduction |
| `EncryptThenTag/Reduction.lean` | 386 | step 1 |
| `EncryptThenTag/Transfer.lean` | 218 | the CCA2 game of a scheme as the experiment with `f`, `g` |
| `EncryptThenTag/Forgery.lean` | 528 | step 2 |
| `EncryptThenTag/Lazy.lean` | 585 | step 3: the experiment with lazily sampled tags |
| `EncryptThenTag/CPAHandler.lean` | 757 | step 3: the T2 handler of the CPA reduction |
| `EncryptThenTag/CPAReduction.lean` | 354 | step 3: the CPA reduction |

All below 1000 lines. Import graph (acyclic; the sweep checks it in order): Tools ← Machines;
Tools ← Games ← Handler ← Reduction (← Machines, ← `OracleFromPRF.Reduction`); Games ← Transfer;
Games ← Forgery; Games ← Lazy ← CPAHandler (← Handler, ← `OracleFromPRF.Handler`) ← CPAReduction
(← Reduction). The owned file imports all ten helpers (the lint's facade rule) and
`OracleFromPRF.Collision` (for `PRFGame.abs_expect_fImpl_sub_le`). No helper imports the owned
file; `OracleFromPRF` and its helpers do not import `EncryptThenTag`.

**Owned-file edits.** Title (dropped "(statement phase)"); `## Main results` (the theorem is
proved); new `## Contents` (the helper modules and what each provides); imports; the target's
docstring sketch rewritten to describe the delivered proof (four steps, the combination, the
`n = 0` correction, and the deviation above); the target's body. The statement, every other
declaration, the source notes and the `simps` attribute are unchanged.

## 3. New declarations

(All helpers in namespace `TCSlib.Cryptography.Composability.ETTGame`.) Checkpoint 1 and 2
declarations are listed in §7.4. New since checkpoint 2:
- Tools: `expect_simulate_abs_inv`.
- Games: `encW_eq_ctW` (replaces Forgery's private `encW_pairV`, now deleted).
- Lazy: public `LEntry`, `LEntry_eq`, `LSt`, `LSt_eq`, `keysL`, `keysL_eq`, `lookL`, `lookL_eq`, `tagOf`, `tagOf_eq`, `lazyDec`, `lazyDec_eq`, `tagTbl`, `tagTbl_eq`, `keysL_nil`, `tagTbl_none_nil`, `ovr_append`, `getD_idxOf_fst`, `ovr_tags_of_mem`, `keys_tagTbl`, `tagOf_eq_ovr`, `zipWith_xor_cancel`, `LInv`, `lInv_iff`, `lInv_nil`, `decAnsW_tagTbl`, `lazyStep`, `lazyStep_enc`, `lazyStep_dec`, `lazyStep_challenge_some`, `lazyStep_challenge_none`, `ettLazyK`, `ettLazyK_eq`, `ettLazy`, `ettLazy_eq`, `ettLazyTape`, `ettLazyTape_eq`, `expect_ettLazyTape`, `ettLazy_apply`, `expect_ettImpl_lazy`; private `tagTbl_cons`, `keysL_cons`, `ovr_cons_self`, `ovr_append_of_mem`, `ovr_append_of_not_mem`.
- CPAHandler: public `encE`, `encE_eq`, `tblW`, `tblW_eq`, `tblW_nil`, `tblW_cons`, `length_tblW`, `lookup_tblW`, `bStLen`, `bStLen_eval`, `bSeedLen`, `bSeedLen_eval`, `bState`, `bState_eq`, `bSeed`, `bSeed_eq`, `ofFn_bSeed`, `bTapeOf`, `bTapeOf_eq`, `bHandler`, `bHState`, `bHState_eq`, `ofFn_bHState`, `bHSeed`, `bHSeed_eq`, `ofFn_bHSeed`, `bHandler_init_hstate`, `bHandler_advInput`, `bHandler_finish`, `bKeyOf`, `bKeyOf_eq`, `bHandler_impl_enc`, `bHandler_impl_dec`, `bHandler_impl_challenge_some`, `bHandler_impl_challenge_none`; private `map_encE_eq_tblOf`, `fields_bState`, `bTbl`, `bJ`, `bFlag`, `bRec`, `bPad2`, `bTape`, `bKey`, `bLook`, `bChalKey`, `bChalTag`, `bTag`, `bCt`, `bNew`, `bDKey`, `bWF`, `bRef`, `bDecL`, `bDecAns`, `bRun`, `polyTimeComputable_bRun`, `bFin`, `polyTimeComputable_bFin`, `fields_input`, `rAns_one`, `log_ne_nil`, `bPad2_fields`, `bNew_fields`, `bTag_fields`, `bDecL_fields`, `recBits_fields`, `ofFn_padFin_msg`.
- CPAReduction: public `cpaRec`, `cpaRec_eq`, `bAbs`, `bAbs_eq`, `bInv`, `bInv_iff`, `bTapes`, `bTapes_eq`, `bTapes_of_lt`, `comp_bAbs`, `ettLazyTape_bInv`, `exists_cpaStep`; private `ofFn_ctOf`, `bKeyOf_ctOf`.
- Owned file: no new declaration since checkpoint 2 (the proof of `ccaScheme_cca2`).
- Handler: `rY_one`, `log_ne_nil` (private) generalized to any oracle-index word.

No `@[simp]` added. New public `abbrev`s: `LEntry`, `LSt` (with `LEntry_eq`, `LSt_eq`); earlier
`St`, `tagOut` (`St_eq`, `tagOut_eq`). Every public `def` has a lemma beside it (lint
check 8: no WARN for the new files).

## 4. Promotion requests, reader requests, PRFGame overlap

**Promotion list** (generic facts in the helpers; searches in `evidence/logs/checkpoint1-searches.log`
and `evidence/logs/final-searches.log`):
- Checkpoints 1–2 (unchanged): `expect_simulate_abs`; `freshImpl`, `tapeImpl`,
  `expect_simulate_tapeImpl`; `ovr`, `expect_sample_ovr`; `logCount`, `length_logCount_encodeLog`,
  `buildComp_cap`, `exists_capMachine`; `exists_halfMachine`; `eval_toOracleAdversary_len`;
  Forgery's private `abs_expect_sub_le_expect`.
- `expect_simulate_abs_inv` (Tools): `expect_simulate_abs` with an invariant kept by the calls
  (`Games.simulate_eq_of_abs_bounded` is the deterministic version, without invariant).
- `zipWith_xor_cancel` (Lazy): `(m ⊕ p) ⊕ p = m` for `|m| ≤ |p|`. Private copies:
  `zipWith_xor_xor_self` in `FromPRF.lean`, `FromPRG.lean`, `SecureComputation/SpecialEncryption.lean`
  and the owned file's `zipWith_xor_xor_self'` (base); the public
  `Foundations/BitLists.zipWith_xor_cancel_left` is the other orientation, `(a ⊕ c) ⊕ a = c` with
  `|a| = |c|`.
- `ovr_append` (Lazy): writing a concatenated table.

**Reader requests:** none (every foreign definition is read through a published lemma; see the
seals and the explicit-unfold scan, §5).

**PRFGame overlap** (private lemmas of `OracleFromPRF/` re-derived from published readers, in the
general form):
- `prfAdv_prfReduction` (private, `OracleFromPRF.lean`) → `ETTGame.prfAdv_eq_expect` (checkpoint 1):
  the PRF advantage of any oracle adversary as the gap of two expectations.
- `prf_advantage_le` (private, `OracleFromPRF.lean`): the CPA bound for an adversary of the §3.9
  scheme. Re-derived inline in `ccaScheme_cca2` for the machine `B` against the oracles `fImpl`
  (step 4), from `PRFGame.exists_prfReduction`, `ETTGame.prfAdv_eq_expect` and
  `PRFGame.abs_expect_fImpl_sub_le`.
- `rY_one`, `log_ne_nil` (private, `OracleFromPRF/Handler.lean`): the outer answer of a one-entry
  log and its non-emptiness. Re-derived as private lemmas of `Handler.lean` (`rY_one`,
  `log_ne_nil`) and `CPAHandler.lean` (`rAns_one`, `log_ne_nil`), for any oracle-index word `u`
  (PRFGame's are for `u = []`), from `InteractiveHandler.rAns_eq`, `pairFstD_pairEncode`,
  `pairSndD_pairEncode`, `pairEncode_ne_nil`.
- The handler-reading pattern of `OracleFromPRF/Handler.lean` (`fields_input`, `rNew_fields`,
  `recBits_fields`, private) recurs in `Handler.lean` and `CPAHandler.lean` (`fields_input`,
  `bNew_fields`, `recBits_fields`, …) for these files' own handlers and state encodings; the
  statements are about different definitions (not copies).

## 5. Checks (final)

All runs one Lean process at a time, each module through `scripts/lean_check_tree.sh` (via
`tools/check.sh`: start/end time, elapsed time and max RSS in the log). The post-sweep runs are
driven by `tools/final_pipeline.sh` (its step log: `logs/final-pipeline.log`).

- **Recheck and sweep** (`logs/final-sweep.log`, 06:31–06:52 UTC): the 274 modules of
  `logs/order-with-helpers.txt` (the 264 of `order.txt` with the ten helpers inserted before the
  owned module; otherwise identical to `order.txt`), each checked from scratch (stale olean
  removed first), in order: **274/274 status 0, no `error:` line**; the eleven files of this fill
  emit no warning at all. This is one uninterrupted run from the first module. Earlier final-sweep
  runs were stopped by me twice in the first 20 modules to make source changes (commits
  `c68fc02eb`, `c5e21bc04`), and one complete run (06:08, 274/274 status 0) was superseded by the
  `rCnt` fix (`b66a81a1a`, see the scan below); their logs were discarded, as noted in
  `logs/final-pipeline.log`. No restart of the host happened during the delivered runs.
- **Sorry census** (`logs/final-census.txt`, `logs/final-census-vs-base.diff`): 23 declarations in
  9 modules; the diff against `base-sorries.txt` is exactly the line
  `TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag: 1: ccaScheme_cca2` and the total
  (24 → 23).
- **Axioms** (`logs/final-axioms.log`, probe `probes/AxiomsFinal.lean`):
  `ccaScheme_cca2` depends on `[propext, Classical.choice, Quot.sound]`. The probe prints the axioms
  of every stored constant of the eleven files (all constants of the environment whose module is
  one of them, auxiliary constants included): **551 constants**, the union of their axioms is
  `{Classical.choice, Quot.sound, propext}`; no `sorryAx`. (The probe's first run failed on a
  syntax error of the probe itself, a shadowed mutable variable; it was fixed and rerun.)
- **Whole-file seals** (`seals/`; generator `tools/seal_gen.py`, runner `tools/seal_run.py`,
  `tools/seal_all.sh`). Each file is copied verbatim to a new module whose header makes every
  TCSlib definition of its whole import closure `irreducible` and removes it from instance
  unfolding (abbreviations excluded: structure projections, `casesOn`, `bitSpec`-style notation);
  the copy must elaborate. Variant **A** excludes `Complexity.PolyExpr.eval` as notation; variant
  **B** seals it too. Results (rows in `final-A.jsonl`, `final-B.jsonl`, `base-A.jsonl`,
  `base-B.jsonl`; raw output in the `.out` files; sealed copies in `seals/sources/`; each row
  carries the sha256 of the checked source and of the copy, which match the delivered `src/` and
  `seals/sources/` files):
  - final, A and B: **all eleven files elaborate sealed (0 errors, 0 failing declarations)**;
    about 1,500–1,640 definitions sealed per file (the counts are in each row);
  - base (the owned file is the only changed file that exists at the base; checked from
    `base/EncryptThenTagBase.lean`, sha256 equal to `SOURCE-SHA256SUMS`), A and B: 0 errors;
  - `seals/seals-compare.log`: no declaration fails at the final, so none is new.
  During development the first seal runs (variant A; not delivered) failed at eighteen places in
  seven files: `rfl` or `cases … <;> rfl` through `recBits`, `refW`, `keysL`, `LInv`,
  `padL`/`ettDout`, `InteractiveHandler.advInput`, `pairSndD`, an `intro` through `INDSecure`, and one
  `rw … at` whose result typechecked only by unfolding `pairW`. All were replaced by published
  readers (`recBits_none/some`, `refW_none/some`, the new `keysL_nil`, `lInv_nil` and
  `tagTbl_none_nil`, `EnsembleLemmas.ofFn_padFin_eq_padL`, `ettDout_zero/one/two`,
  `InteractiveHandler.advInput_eq`, `BinArith.iterate_pairSndD_nil`,
  `FixedLengthScheme.INDSecure_iff`, `pairW_eq`) in `731efd9ed`; the delivered runs above are on the
  final sources.
- **Paired controls** (`controls/`, `logs/controls-plain.log`, `seals/controls-A.jsonl`,
  `seals/controls-B.jsonl`):
  - `CtlUnfold` (`ETTGame.wR w = pairFstD w := rfl`, unfolding a helper's `def`): unsealed status 0;
    sealed A **1 error** (`ctl_unfold_wR`), sealed B **1 error**;
  - `CtlEval` (`(PolyExpr.const 1).eval 5 = 1 := rfl`): unsealed 0; sealed A 0 (eval excluded);
    sealed B **1 error** (`ctl_unfold_eval`);
  - `CtlReader` (the same two facts through `ETTGame.wR_eq`, `PolyExpr.eval_const`): unsealed 0,
    sealed A 0, sealed B 0.
  Each sealed negative fails exactly once, and the positive passes. (A first run of the controls
  was void: `pairFstD` was written unqualified and did not elaborate even unsealed; the sources
  were fixed and the controls rerun; the void logs were discarded.)
- **Explicit-unfold scan** (`scan/`; `tools/rwids.py`, `tools/rwids_run.sh`, `tools/cmp_scans.py`):
  every identifier in a `rw`/`rwa`/`nth_rw`/`simp`/`simp only`/`simpa`/`simp_rw`/`dsimp`/`unfold`/
  `delta` list of each file is resolved in the file's namespaces and `open`s by a scan module
  (`scan/sources/`), and classified. Final: 1,042 rows: 758 theorems, 13 definitions of the scanned
  file itself, 1 core simproc (`reduceIte`), 270 unresolved (local hypotheses, private
  declarations of the scanned file, projections of hypotheses, dot-notation theorem uses; listed in
  `scan/scan-unresolved.txt`), and **0 definitions of another TCSlib file**
  (`scan/scan-compare.log`: "NEW foreign explicit unfolds: 0"). Base: 42 rows, 0 foreign. The
  scan of the first complete run found one (`rw [rCnt, …]` in `Handler.fields_input`, the
  `InteractiveHandler.rCnt` of `Games/Efficiency.lean`); it now reads `InteractiveHandler.rCnt_input`
  (`b66a81a1a`).
- **Lint** (`logs/final-lint.log`): `python3 -I scripts/campaign_style_lint.py
  TCSlib/Cryptography/Encryption/PrivateKey --check8b`: **0 FAIL**, 5 WARN, all in files this fill
  does not touch (the same five as at checkpoints 1 and 2); none for the eleven files (the owned
  file imports every helper, the facade rule).
- **Searches** for the generic facts of step 3: `logs/final-searches.log` (ripgrep).

## 6. Evidence (`evidence/`, manifest `evidence/SHA256SUMS`)

`evidence/SHA256SUMS` lists exactly the files under `evidence/` (118), each delivered.
- `logs/`: environment and bootstrap (`preflight.log`, `mathlib-roots.txt`, `cache-store.log`,
  `source-sha256.log`, `cache-get.log`, `packages-check.log`, `cache-probe.log`, `order.txt`,
  `bootstrap.log`, `resume-1.log`, `resume-2.log`, `census-bootstrap.txt`,
  `census-bootstrap-vs-base.diff`); checkpoints (`checkpoint1-*`, `checkpoint2-*`); final
  (`order-with-helpers.txt`, `final-sweep.log`, `final-census.txt`, `final-census-vs-base.diff`,
  `final-axioms.log`, `final-lint.log`, `final-searches.log`, `final-pipeline.log`,
  `controls-plain.log`, `scan-final.ids.log`, `scan-final.raw.log`, `scan-base.ids.log`,
  `scan-base.raw.log`).
- `seals/`: `final-A.jsonl`/`.out`, `final-B.jsonl`/`.out`, `base-A.jsonl`/`.out`,
  `base-B.jsonl`/`.out`, `controls-A.jsonl`/`.out`, `controls-B.jsonl`/`.out`, `seals-compare.log`,
  and `sources/{finalA,finalB,baseA,baseB,ctlA,ctlB}/` (the sealed copies that were checked).
- `scan/`: `scan-final.tsv`, `scan-base.tsv`, `scan-compare.log`, `scan-unresolved.txt`,
  `sources/{final,base}/` (the scan modules).
- `controls/`: `CtlUnfold.lean`, `CtlEval.lean`, `CtlReader.lean`.
- `base/`: `EncryptThenTagBase.lean` (the owned file at the base, for the base seals and scan).
- `probes/`: `CacheProbe.lean`, `AxiomsCP1.lean`, `AxiomsCP2.lean`, `AxiomsFinal.lean`.
- `tools/`: `check.sh`, `dev.sh`, `mk.py`, `sweep_chunk.sh`, `census.py`, `cmpcensus.sh`,
  `pkgcheck.py`, `payload.sh`, `seal_gen.py`, `seal_run.py`, `seal_all.sh`, `rwids.py`,
  `rwids_run.sh`, `cmp_scans.py`, `final_pipeline.sh`, `finalize.sh`.

`patches/`: `git format-patch eff2dcd0a..b66a81a1a` (8 patches). `src/`: the eleven changed and new
files at `b66a81a1a`.

## 7. From the checkpoints

### 7.1 Environment (addendum v1)

- **Preflight** (`evidence/logs/preflight.log`): 4 CPUs; cgroup v1 limit unlimited, so the headroom is
  `MemAvailable` = 16442974208 B = 15.31 GiB; clone filesystem ext4 with 13927960576 B = 12.97 GiB
  free (floor 12 GiB): `PREFLIGHT PASS`. Two worktrees of finished jobs of this session
  (`/workspace/dlc-base`, `/workspace/base-wt`) were removed before the preflight to get above the
  floor; no dependency tree was copied or moved.
- **Cache**: the narrowed `lake exe cache get` for the 98 roots of `roots.txt`
  (`evidence/logs/mathlib-roots.txt` is the same list) printed "No files to download" and
  "Decompressing 2370" and exited 0 (`cache-get.log`). The cache tool's store
  (`~/.cache/mathlib`, `cache-store.log`) already held 2402 archives, left by this session's earlier
  fills on this host; none was downloaded for this fill. No zero-size olean; the probe importing
  `Mathlib.Algebra.BigOperators.Field` elaborates (`cache-probe.log`, `probes/CacheProbe.lean`).
- **Packages** (`packages-check.log`, last line): `RESULT: all present packages match the manifest`
  (`doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean` ABSENT; no module of the order imports them).
- **Bootstrap** (`bootstrap.log`, one module per `scripts/lean_check_tree.sh` call through
  `tools/check.sh`): 264/264 modules of `order.txt`, status 0. The host was restarted twice during
  the bootstrap (a VM restore: uptime 0, `dmesg` "virtual machine fork"); each restart terminated
  the background sweep mid-module (no Lean failure, no OOM event). Both are logged
  (`resume-1.log`, `resume-2.log`) and the sweep resumed at the interrupted module, which was
  re-checked from scratch. Sorry census of the bootstrap = `base-sorries.txt` (24 declarations in 10
  modules; `census-bootstrap.txt`, `census-bootstrap-vs-base.diff`).

### 7.2 Step 1 (checkpoint 1)

`ETTGame.exists_tagStep` (helper) and `cca_tag_step` (owned file): for a machine adversary `A` with
budget `q` and a bit `b` there is a next-query machine `D` with, at every `n`,

`|Pr[IND_b(A, q(n), n) = 1] − 𝔼_{k₁} 𝔼_R ettAcc(f_{k₁}, R, rej = false, b)| = prfAdv(F_{2n}, D^{q(2n)}_{2n})`,

where `R` ranges over all functions on `2n` bits. With `PRF.negligible_prfAdv` and
`Negligible.comp_of_le` (`φ n = 2n`) this is negligible in `n`; the final combination does that.

**The reduction** (`ETTGame.exists_tagReduction`): the handler `dHandler` holds `k₁` and `q(2n)`
nonce tapes in its seed and the query count and the challenge record in its state; `Enc′` and a
first challenge ask the oracle at `r ‖ c₁`, `Dec′` refuses the record, asks the oracle at the pair of
a well-formed word and compares with the tag. T2 is applied with the budget `q(2n)` to the
input-free companion of a **capped** adversary, then T4 at length `2n`, then the parameter is halved.

**Why the cap and the halving.** `PRF.negligible_prfAdv` bounds machines run at parameter `m` with
an `m`-bit oracle and budget `Q(m)` for a polynomial `Q`. The handler runs the adversary at `n` with
a `2n`-bit oracle. So the distinguisher at `m = 2n` must run T2's machine at `m / 2`
(`exists_halfMachine`, from `NUPPT.exists_reparam_advice`), and T2's budget must be a polynomial in
`2n`: `q(2n)`. The adversary's budget is `q(n)`; `exists_capMachine` gives a machine that, at every
budget `K ≥ q(n)`, computes what `A` computes with budget `q(n)` (after `q(n)` log entries a query
word becomes the empty word, which every bit codec reads as the timeout output). No statement is
weakened: the game is still `A` at budget `q(n)`.

**Transfer** (`ETTGame.accept_indGame_eq`, `accept_cca_indGame`): the real oracles have, call by
call, the laws of `ettImpl (F n k₁) (F (2n) k₂) false b`, through the record
(`expect_simulate_abs`). The readers of `ccaScheme` used: `ccaScheme_gen/enc/dec/ctLen`,
`runAt_ccaGen`, `runAt_ccaEnc`, `ccaDecFun_eq`, `ccaDecOK_eq` and the `NUPPT` run readers. Every
decryption answer is matched, including malformed words and, at `n = 0`, the malformed four-bit
words that decrypt to the empty message: the experiment parses with the same total projections
(`wR`, `wC`, `wT`) and guards (`validW`).

### 7.3 Step 2 (checkpoint 2)

New helper `EncryptThenTag/Forgery.lean` (536 lines) and, in the owned file, `cca_rej_step`: for
`n > 0`, a machine adversary `A` with budget `Q` and a bit `b`,

`|𝔼_{k₁} 𝔼_R ettAcc(f_{k₁}, R, rej = false, b) − 𝔼_{k₁} 𝔼_R ettAcc(f_{k₁}, R, rej = true, b)| ≤ Q / 2^{2n}`

(`ETTGame.abs_ettAcc_rej_sub_le`, averaged over `k₁`). The route of the brief: couple both
experiments with the same tapes and random function; they agree until the first fresh valid query.
- *Identical until bad* (`ettBad_agree`, `ettBad_stick`, `simulate_ettBad_fst`,
  `abs_prob_ettImpl_rej_sub_le`): `identical_until_bad` with the flag `hitW` (a decryption query
  that is not refused, is valid and whose pair is not the pair of an earlier `Enc′` answer), and
  `prob_eq_until_bad` to read the flag's probability in the rejecting experiment.
- *The flag's probability* (`expect_prob_bad_le`, an equal-until-bad argument through the union
  bound rather than `prob_bad_le`, because the per-query bound needs the average over `R`): by
  induction over the computation with `R` overridden on the revealed pairs (`ovr`, invariant
  `RevInv`). A new pair moves `R`'s value into the table (`expect_sample_ovr`); the rejecting
  experiment's decryption answers read the tag function only at listed pairs, so they do not
  depend on `R`; a fresh guess hits the unrevealed value with probability at most `2^{-2n}`
  (`expect_hitW_le`), "even if the pair was queried before" (each guess is bounded separately; no
  conditional probability after failed guesses is used). A valid query with the challenge's pair
  is the challenge itself for `n > 0` (`eq_of_pairV_eq`, `eq_ctW_of_wfW`: canonical parsing through
  `pairEncode` and the two length guards) and is refused, so it is not a hit.
- The bound is `Q / 2^{2n}`, the brief's `q(n) / 2^{2n}`.

New public declarations (Forgery): `ettBad_agree`, `ettBad_stick`, `simulate_ettBad_fst`,
`abs_prob_ettImpl_rej_sub_le`, `RevInv`, `revInv_iff`, `revInv_nil`, `expect_prob_bad_le`,
`abs_ettAcc_rej_sub_le`; private: `revInv_enc_old`, `revInv_enc_new`, `revInv_chal_old`,
`revInv_chal_new`, `validW_pairW`, `encW_pairV`, `expect_hitW_le`, `prob_bad_of_flag`,
`prob_simulate_ettBad_query`, `abs_expect_sub_le_expect` (generic: candidate for promotion,
`|𝔼 f − 𝔼 g| ≤ 𝔼 h` under a pointwise bound; `ProbComp.abs_expect_sub_le` has a constant bound).
Owned file: `cca_rej_step` (private).

Evidence added: `logs/checkpoint2-checks.log` (fresh checks of the seven helpers and the owned
module, status 0), `checkpoint2-census.txt`, `checkpoint2-axioms.log` (`propext`,
`Classical.choice`, `Quot.sound`), `checkpoint2-lint.log` (0 FAIL), `probes/AxiomsCP2.lean`;
`order-with-helpers.txt` now lists Forgery before the owned module.

### 7.4 Declarations of checkpoints 1 and 2

- Tools: `expect_simulate_abs`, `freshImpl`, `freshImpl_apply`, `tapeImpl`, `tapeImpl_apply`,
  `simulate_tapeImpl_congr`, `expect_simulate_tapeImpl`, `ovr`, `ovr_nil`, `ovr_cons`,
  `ovr_of_not_mem`, `ovr_of_mem`, `ovr_update`, `expect_sample_ovr`.
- Machines: `logCount`, `logCount_eq`, `polyTimeComputable_logCount`, `length_logCount_encodeLog`,
  `buildComp_cap`, `capRaw`, `capRaw_eq`, `polyTimeComputable_capRaw`, `exists_capMachine`,
  `exists_halfMachine`, `eval_toOracleAdversary_len`.
- Games: `pairV`, `tagL`, `ctW`, `maskL`, `encW`, `wR`, `wC`, `wT`, `wfW`, `validW`, `decL`, `pairW`
  (each with its `_eq`), `wR_ctW`, `wC_ctW`, `wT_ctW`, `length_maskL`, `length_encW`, `eq_ctW_of_wfW`,
  `wfW_encW`, `eq_of_pairV_eq`, `St` (abbrev, `St_eq`), `refW` (`refW_none`, `refW_some`),
  `decAnsW`, `hitW` (with `_eq`), `decAnsW_agree`, `ettStep` (`ettStep_enc`, `_dec`,
  `_challenge_some`, `_challenge_none`), `ettImpl` (`ettImpl_apply`, `ettImpl_eq_freshImpl`),
  `hitQ` (`hitQ_zero/one/two`), `ettBad` (`ettBad_apply`), `ettTape` (`ettTape_apply`),
  `expect_ettTape`, `expect_ettImpl_transport`, `ettAcc` (`ettAcc_eq`, `ettAcc_nonneg`,
  `ettAcc_le_one`).
- Handler: `ettCt`, `ettDin`, `ettDout`, `tagLen`, `tagOut` (abbrev, `tagOut_eq`), `dStLen`,
  `dSeedLen`, `recBits`, `dState`, `dSeed`, `dTape`, `dHandler` (simps fields), `dHState`, `dHSeed`
  (each with `_eq`/readers), `ofFn_dSeed`, `ofFn_dHSeed`, `ofFn_dHState`, `dHandler_init_hstate`,
  `dHandler_advInput`, `dHandler_finish`, `dHandler_impl_enc`, `dHandler_impl_dec_ref`,
  `dHandler_impl_dec_wf`, `dHandler_impl_dec_nwf`, `dHandler_impl_challenge_some`,
  `dHandler_impl_challenge_none`.
- Reduction: `gOuter` (`gOuter_apply`), `dAbs` (`dAbs_eq`), `dTapes` (`dTapes_eq`, `dTapes_of_lt`),
  `comp_dAbs`, `eval_subst_tagLen`, `expect_ettImpl_outLen`, `exists_tagReduction`,
  `prfAdv_eq_expect`, `exists_tagStep`.
- Transfer: `stRec` (`stRec_eq`), `expect_indImpl_ettImpl`, `accept_indGame_eq`.
- Owned file (all `private`): `cca_ctLen_eval`, `cca_inLens`, `cca_outLens`, `cca_gen_coins`,
  `cca_enc_coins`, `cca_gen_len`, `ccaKeyEq`, `ofFn_ccaKeyEq`, `cca_gen_runAt`, `ccaNonceEq`,
  `ofFn_ccaNonceEq`, `ofFn_cca_encryptAt`, `ofFn_cca_decAnswer`, `accept_cca_indGame`,
  `cca_tag_step`.

No `@[simp]` was added. The one new public `abbrev`s (`St`, `tagOut`) have `St_eq`, `tagOut_eq`.

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

## ===== briefs/pass-shelat-ch5-8/fills/cca2-ett/issued-r1/brief.md =====

# Claude fill · encrypt-then-tag is CCA2-secure (`ccaScheme_cca2`, Theorem 170.4)

**Issue base** `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9` on `cryptography/pass-shelat-ch2-4` (the merge of #299).
**Unit** `cca2-ett`. **Worker** Claude (standing ruling, 2026-11-11). **Lean** 4.25.0 and the Mathlib revision in that
commit's `lake-manifest.json`.

Prove the admitted theorem of [PS10, Theorem 170.4] in
`TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag.lean`. The theorem says that Algorithm 169.3 is CCA2-secure
when `F` is a pseudorandom function family. The scheme is the §3.9 scheme with its ciphertext `(r, c₁)` tagged by
`f_{k₂}(r ‖ c₁)`. The statement passed its Gate 06 audit (chapters 5–8 statements) and is frozen.

This fill starts after the duplication consolidation (#298) and its follow-up folds (#299), so the shared Games-layer
API is current. Seyoon ruled on 2026-11-13 that this job waits for those folds.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/cca2-ett` at the exact issue base, and record
  the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/cca2-ett/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `src/`: the changed and new files;
  - `evidence/`, with a `SHA256SUMS` manifest (see *Evidence completeness*).
- Commit as `fill cca2-ett: checkpoint N` and `fill cca2-ett: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land by
  a maintainer PR for Seyoon's approval.

## Target (frozen; quoted from the issue base)

```lean
theorem ccaScheme_cca2 (hF : PRF F) : (ccaScheme F E hE hFE).INDSecure .cca2 := by
  sorry
```

It lives in namespace `TCSlib.Cryptography.Composability`, with these variables:
- `F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)`;
- `E : List Bool → List Bool` and `hE : PolyTimeComputable E`;
- `hFE`, which says `E` agrees with `F` on `⟨s, x⟩` when `|s| = |x|`.

**The scheme `ccaScheme`** (all in the owned file):
- `Gen′` uses `3n` coins, split at `n` into the keys `k₁` (n bits) and `k₂` (2n bits), so the key is `⟨k₁, k₂⟩`.
- `Enc′` takes `n` coins `r` and outputs `⟨r, ⟨c₁, t⟩⟩`, where `c₁ = m ⊕ E⟨k₁, r⟩` and `t = E⟨k₂, r ++ c₁⟩`.
- `Dec′` checks the two length guards and the tag, and outputs `⊥` otherwise (`ccaDecOK`, `ccaDecFun`).
- Ciphertexts have `6n + 4` bits.
- The readers are `runAt_ccaGen`, `runAt_ccaEnc`, `runAt_ccaDec`, the `*_eq` lemmas and `length_eval_of_length`.

**The security notion `INDSecure .cca2`** (`INDSecure_iff`, `indGame_eq`, `indImpl_*` in
`PrivateKey/OracleSecurity.lean`): every adversary has negligible advantage between `indGame .cca2 A q false` and
`true`.

The module docstring's *source notes* record two points; read them:
- the tag covers `(r, c₁)`;
- at `n = 0` there is malformed-but-accepted behaviour, which changes no asymptotic claim.

The target's docstring sketch is the maintainer's route. You may edit it to describe the delivered proof.

## Published interfaces

| Interface | Provider |
|---|---|
| `ccaGenFun`, `ccaMaskFun`, `ccaEncFun`, `ccaDecOK`, `ccaDecFun` and their `_eq`; `polyTimeComputable_*`; `runAt_ccaGen/_ccaEnc/_ccaDec`; `length_eval_of_length`; `ccaScheme` and its `simps` fields | `PrivateKey/EncryptThenTag.lean` (owned) |
| `FixedLengthScheme` fields, `decAnswer`, `decOpen_*`, `indImpl`, `indImpl_dec`, `indCodec_*`, `indGame_eq`, `INDSecure_iff` | `PrivateKey/OracleSecurity.lean` |
| `prfFixedScheme`, `prfFixedScheme_cpa`, `prfFixedScheme_cca1` (Thm 168.2, proved, with the bound in its docstring) | `PrivateKey/OracleFromPRF.lean` |
| PRFGame's public API: `fImpl`, `eImpl` (`Games`); `pkHandler` (`Handler`); `exists_prfReduction` (`Reduction`); the `Transfer` readers; `lazyImpl`, `expect_lazyImpl` (`Lazy`); `abs_expect_fImpl_sub_le` (`Collision`) | `PrivateKey/OracleFromPRF/*.lean` (import them, do not copy) |
| `PRF`, `PRF.negligible_prfAdv`, `prfAdv_toOracleAdversary`; `prfAdv` | `Pseudorandom/Functions/Asymptotic/Defs.lean`, `Pseudorandom/Functions/Defs.lean` |
| T2 `exists_interactiveHandlerMachine`, T4 `exists_toOracleAdversary_of_bitCodec`, the `InteractiveHandler` readers (`rU`…`rL`, `rAns`, the `_input`/`_finInput` readers, `impl_of_ret`, `impl_of_query`, `finish_of_ret`) | `Games/Efficiency.lean` |
| `fwdHandler`, `fwdHandler_impl` | `Games/Forwarding.lean` |
| `prob_eq_until_bad`, `expect_eq_until_bad`, `prob_bad_le` (per-query potential bound), `expect_sample_mem_le`, `expect_simulate_eager`, `expect_congr_of_allOutputs` | `Games/Hopping.lean` |
| `simulate` equations, `simulate_eq_of_abs(_bounded)`, `castImpl` family, `buildComp_*`, `CostBoundedBy`, `bitCodec_*`, `padFin*`, `cntRead`/`ansRead`, `OracleComp` laws, `advantage_eq`, `accept_eq`, `ProbComp.expect_*` | `Games/*` |
| `NUPPT.exists_comp`, `exists_compParam`, `exists_withAdvice(On)`, `exists_seq`, `exists_reparam`; `NUPPT` run/coin readers; `Negligible` closure: `add`, `const_mul`, `mono`, `negligible_two_pow_neg`, and `comp_of_le`, which takes the PRF bound at parameter `2n` back to `n` | `Complexity/Randomized/Closure.lean`, `Asymptotic/*`, `Foundations/Negligible.lean` |
| `coinBlock`, `FunFamily.blocks`, `ofFn_blocks`, `Foundations/BitLists` | `Asymptotic/Adversary.lean`, `Foundations/BitLists.lean` |

## Proof route and checkpoints

Fix a CCA2 adversary `A`, with query budget `q` and challenge-bit games `b = false, true`.

1. **The tag key becomes a random function** (sketch step 1).
   - Build a PRF distinguisher at parameter `2n`. It samples `k₁` itself and runs `A`. It answers:
     - `Enc′` and the challenge with its oracle in place of `f_{k₂}`;
     - `Dec′` by recomputing the tag with its oracle.

     It is a T2 handler (`exists_interactiveHandlerMachine`) with `k₁` in its seed, made an oracle adversary with
     T4 at length `2n`.
   - For each `b`, the gap between the real game and the game with a random tag function is at most `prfAdv` at
     `2n`, which is negligible in `n` by `Negligible.comp_of_le` with `φ n = 2n`.

   Send checkpoint 1.
2. **Fresh decryption queries are rejected** (sketch step 2). For positive `n`, call a `Dec′` query `(r, c₁, t)`
   *fresh* if `(r, c₁)` is not the pair of an earlier `Enc′` or challenge answer.
   - Compare with the game that rejects every fresh query. Couple both with the same tapes and random function:
     they agree until the first fresh query with a valid tag.
   - Bound that event by `q(n)/2^{2n}` with `prob_bad_le`, or an equal-until-bad argument through
     `prob_eq_until_bad`/`expect_eq_until_bad`. In the always-reject game, a rejected guess reveals no value of the
     random function at an unanswered pair.
   - A *non-fresh* valid query is an earlier answer. Canonical parsing (`pairEncode` injectivity, the length guards)
     makes it either the refused challenge or an encryption of a chosen message.

   Send checkpoint 2.
3. **Reduction to the §3.9 scheme's CPA security** (sketch step 3).
   - The always-reject game is simulated by a CPA adversary against `prfFixedScheme` under `k₁`:
     - `Enc′` and challenge answers come from the CPA oracles, re-encoded from `⟨r, c₁⟩` (3n + 2 bits) to
       `⟨r, ⟨c₁, t⟩⟩`, with `t` from a lazily sampled random function (`lazyImpl`);
     - `Dec′` answers come from the table of earlier answers, or are `⊥`.
   - If you use fresh uniform tags instead of a lazily sampled function (the source's version), account for the
     nonce-collision term `q(n)²/2^n`.
   - Combine the terms: the PRF advantages at `2n`, the first-discrepancy term `q(n)/2^{2n}`, any collision term,
     and the CPA advantage (`prfFixedScheme_cpa`). The sum is negligible. Handle `n = 0` by `Negligible.mono`
     (eventual bounds).

   Send the final delivery.

Check the edge cases:
- `n = 0`, including the malformed `0000` that decrypts to the empty message;
- budget 0, no challenge, and repeated challenges;
- `A` querying `Dec′` on the challenge itself (refused), on the challenge with a changed tag, on malformed or
  over-long words, and on an earlier `Enc′` answer;
- nonce collisions;
- the codecs' timeout outputs, in every direction.

If the sketch is wrong, or the target is false as stated, stop and escalate with the exact obligation: a checkpoint
with the counterexample or the missing fact. Do not weaken the statement.

## Scope and proof discipline

- **Owned file.** You own `PrivateKey/EncryptThenTag.lean`:
  - replace the target's proof body and edit its sketch;
  - update the module title (drop "(statement phase)") and the `## Main results` status.
- **Helper modules.**
  - They are permitted under `TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/`.
  - The owned file imports them precisely and gets a `## Contents` list.
  - A helper may import `OracleFromPRF` and its helpers. They are not downstream of the owned file, so this creates
    no cycle; check it.
- **Size.** Keep every file below 1000 lines.
- **Frozen.** Do not edit any other file.
  - `Games/Efficiency.lean` is at 982 lines and must be split before it grows. Do not add to it.
  - If a lemma belongs in an existing file, put it in your helper module and list it as a promotion request.
  - If a reader of another file's definition is missing, escalate: record the exact obligation and the reader you
    need, and push a checkpoint.
- **Duplication (binding).**
  - **Public lemmas.** Do not copy them: import them, including PRFGame's public API above.
  - **Private lemmas** of `OracleFromPRF/` or `OracleFromPRF.lean`. Do not copy them. If you need one, re-derive it
    from published readers in your helper module, disclose it in `REPORT.md` as **"PRFGame overlap: <item>"**, and
    keep its statement in the general form.
  - **Other generic facts** (probability, simulation, machine or list) go on your promotion list. Grep first, and
    report the searches.
- **Statements.** Preserve the target statement, every other declaration, the statement prose and the global simp
  attributes.
- **Docstrings.** Public helpers get docstrings with their formulas, and proof sketches when nontrivial
  (policy §3). Add no `@[simp]`. A new public `abbrev` needs an `_eq`/`_iff` lemma.
- **Rule 10.**
  - Use only published readers for other files' definitions, including generated matchers and projections.
  - Your helper modules count as foreign to each other and to the owned file.
  - The owned file's definitions are foreign to your helpers. Read `ccaScheme` and its parts through
    `runAt_cca*`, the `_eq` lemmas and the `simps` fields.

## Checks and report

- **Bootstrap.** Bootstrap from `order.txt` (264 modules) and the narrow `roots.txt` (98), following the addendum.
  Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree. Insert helper
  modules before their consumers.
- **Sweep.**
  - Recheck the owned module, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (24 declarations in 10 modules). The only change must be
    the removal of `ccaScheme_cca2`.
- **Axioms.**
  - Print the axioms of `ccaScheme_cca2`. Expect only `propext`, `Classical.choice` and `Quot.sound`.
  - Print them for every stored constant of the changed and new files.
- **Rule 10 evidence.**
  - Run whole-file seals A and B of every changed or new file over its full TCSlib import closure, at base and
    final, and report every failing declaration.
  - Add paired controls that pass unsealed and fail sealed, each sealed negative failing exactly once.
  - Run the explicit-unfold scan.
  - Report the seals with `PolyExpr.eval` both excluded as notation and sealed.
- **Lint.** Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PrivateKey --check8b`. It
  must show no new FAIL.
- **Report.** Give:
  - the base and the target's status;
  - the changed files and the sketch edits;
  - the new declarations;
  - the promotion and reader requests;
  - every "PRFGame overlap" item;
  - the evidence.

### Evidence completeness

Gate 20 held a delivery for omitted raw evidence (G20-01).
- Every file that `evidence/SHA256SUMS` names must be delivered. That includes:
  - seal and control sources, manifests and request records;
  - every raw log and `results.jsonl`;
  - the probe sources and the tools used.
- If the evidence is too large for one commit, deliver it in several commits, or as numbered ZIP parts, each part
  with an entry list. Do not leave anything out for size.
- Check before delivery that the delivered paths are exactly the manifest's.

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
| DL-40 | cca2-ett fill (delivery review 2026-11-14): undisclosed `ETTGame.eval_toOracleAdversary_len` (`EncryptThenTag/Machines.lean`) generalizes public `PRFGame.eval_toOracleAdversary_width` (`OracleFromPRF/Reduction.lean`, its `ℓ = n` case); disclosed `ETTGame.zipWith_xor_cancel` = four private `zipWith_xor_xor_self` copies (`FromPRF`, `FromPRG`, `SpecialEncryption`, owned `zipWith_xor_xor_self'`; public relative `zipWith_xor_cancel_left`, other orientation); `ETTGame.prfAdv_eq_expect` re-derives private `prfAdv_prfReduction` (public relative `prfAdv_eq`, uprob form); generic forms `ETTGame.tapeImpl`/`simulate_tapeImpl_congr`/`expect_simulate_tapeImpl` (AdaptiveCPA), `recBits` family and `ovr` (PRFGame), `expect_simulate_abs` (`Games.simulate_eq_of_abs_bounded`), private `abs_expect_sub_le_expect` (`ProbComp.abs_expect_sub_le`). | `Foundations/BitLists`, `Pseudorandom/Functions`, `Games/*`, the general ETT forms | Open (deferred) | Promote the general forms (worker requested most) and re-derive the specialised copies from them; fold the private XOR copies. |
| DL-41 | dl-crh fill (delivery review 2026-11-14): **undisclosed** `FromDiscreteLog.inputWord_split` restates `ofFn_eq_init_append` (`Asymptotic/ReductionSupport.lean`, up to `Fin.init`); `ofFn_splitBits_fst/_snd` restate `ofFn_splitCoins_fst/_snd` (`CollectionsHelpers.lean`; `Authentication.splitBits` = `splitCoins`); disclosed re-derivations from public readers of private `dlb_expo_val`, `fac_listToNat_inj`, `ofFn_splitCoins_symm_cast`, `dla_statClose_expDec`; near relatives `residueFinEquiv` (Mathlib `ZMod.finEquiv`), `boundedInputEquiv` (`Fin.snocEquiv`), `expect_sample_eq_uexp` (`Games.Bridge.prob_sample_eq_uprob`). | `ofFn_eq_init_append`, `ofFn_splitCoins_*`, a `splitBits = splitCoins` bridge; worker promotion list `evidence/PROMOTION.md` (exchange `9ad236d1`) | Open (deferred) | Re-point and promote in a later job. |
| DL-42 | hash-sign fill (delivery review 2026-11-14): `HashSignForward.roundWord`/`handler` repeats the `Games/Forwarding` `fwdRun`/`fwdHandler` pattern with a hashed query and different widths (disclosed); `splitBits_pad_concat` is a corollary of `Games.padFin_append_split`; `expect_simulate_sample_once` near `Games.expect_simulate_eager`; `MachineCodec.ext_of_fields`, `forgerCodec_eq_bitCodec`, `eq_pure_of_cost_zero` overlap the parallel lamport delivery's `lamport_codec_ext`, `lamport_forgerCodec`, `exists_pure_of_cost_zero`. | `Games/Forwarding` (a query-map `fwdHandler`), `Games/BitCodec`, `Games/Hopping`, `Games/Machines` | Open (deferred) | Generalize `fwdHandler`; promote the codec/cost facts to `Games/Machines` (no attribute) and fold the lamport copies once both units have landed. |

## ===== briefs/pass-shelat-ch5-8/gates/23-cca2-ett/pr.diff.txt =====

diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag.lean b/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag.lean
index a8481262d..589088a4f 100644
--- a/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag.lean
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag.lean
@@ -6,6 +6,17 @@ import TCSlib.Complexity.Randomized.Repetition
 import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
 import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
 import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs
+import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Tools
+import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Machines
+import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Games
+import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Handler
+import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Reduction
+import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Transfer
+import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Forgery
+import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Lazy
+import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.CPAHandler
+import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.CPAReduction
+import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Collision
 import Mathlib.Tactic.Simps.Basic
 
 set_option maxHeartbeats 0
@@ -13,7 +24,7 @@ set_option relaxedAutoImplicit false
 set_option autoImplicit false
 
 /-!
-# A CCA2-secure private-key scheme (statement phase)
+# A CCA2-secure private-key scheme
 
 [PS10, Algorithm 169.3] and Theorem 170.4. For a PRF family `{f_k}`:
 - `Gen′(1^n)` samples keys `k₁ ← U_n` and `k₂ ← U_{2n}`;
@@ -59,7 +70,24 @@ followed by `k₂`. A ciphertext is `⟨r, ⟨c₁, t⟩⟩`, of `6n + 4` bits.
 
 ## Main results
 
-* `Composability.ccaScheme_cca2` (Thm 170.4, stated; a `sorry` under the source's sketch).
+* `Composability.ccaScheme_cca2`: Theorem 170.4, `π′` is CCA2-secure when `F` is a PRF.
+
+## Contents
+
+This file states the scheme and assembles the proof; the proof's games, handlers and reductions
+are in the helper modules under `EncryptThenTag/` (namespace `Composability.ETTGame`):
+- `Tools`: simulation through a state abstraction, coins in advance, functions overridden by a
+  table;
+- `Machines`: the budget cap and the parameter halving of machines;
+- `Games`: the CCA2 experiment with a pad function `f` and a tag function `g` (`ettImpl`);
+- `Handler`, `Reduction`: step 1, the tag-key PRF reduction at parameter `2n`
+  (`exists_tagStep`);
+- `Transfer`: the CCA2 experiment of `π′` as the experiment with `f_{k₁}` and `f_{k₂}`
+  (`accept_indGame_eq`);
+- `Forgery`: step 2, rejecting fresh decryption queries costs at most `q(n)/2^{2n}`
+  (`abs_ettAcc_rej_sub_le`);
+- `Lazy`, `CPAHandler`, `CPAReduction`: step 3, the rejecting experiment with lazily sampled tags
+  is a CPA experiment of the §3.9 scheme (`expect_ettImpl_lazy`, `exists_cpaStep`).
 
 ## References
 
@@ -365,38 +393,361 @@ noncomputable def ccaScheme : FixedLengthScheme where
 
 attribute [simps (config := { isSimp := false }) gen enc dec ctLen] ccaScheme
 
+/-! ### The proof of Theorem 170.4 -/
+
+section Proof
+
+open ETTGame ProbComp
+
+/-- The ciphertext length is `6n + 4` (`ccaScheme_ctLen`). -/
+private theorem cca_ctLen_eval (n : ℕ) : (ccaScheme F E hE hFE).ctLen.eval n = 6 * n + 4 := by
+  rw [ccaScheme_ctLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
+    PolyExpr.eval_const, PolyExpr.eval_var]
+
+/-- The scheme's query lengths are the reduction's: `inLens n = fun i => (ettDin i).eval n`. -/
+private theorem cca_inLens (n : ℕ) :
+    (ccaScheme F E hE hFE).inLens n = fun i => (ettDin i).eval n := by
+  funext i
+  match i with
+  | 0 => rw [FixedLengthScheme.inLens_zero, ettDin_zero, PolyExpr.eval_var]
+  | 1 => rw [FixedLengthScheme.inLens_one, ettDin_one, cca_ctLen_eval, ettCt_eval]
+  | 2 => rw [FixedLengthScheme.inLens_two, ettDin_two, PolyExpr.eval_add, PolyExpr.eval_var]
+
+/-- The scheme's answer lengths are the reduction's: `outLens n = fun i => (ettDout i).eval n`. -/
+private theorem cca_outLens (n : ℕ) :
+    (ccaScheme F E hE hFE).outLens n = fun i => (ettDout i).eval n := by
+  funext i
+  match i with
+  | 0 => rw [FixedLengthScheme.outLens_zero, ettDout_zero, cca_ctLen_eval, ettCt_eval]
+  | 1 =>
+    rw [FixedLengthScheme.outLens_one, ettDout_one, PolyExpr.eval_add, PolyExpr.eval_var,
+      PolyExpr.eval_const]
+  | 2 => rw [FixedLengthScheme.outLens_two, ettDout_two, cca_ctLen_eval, ettCt_eval]
+
+/-- `Gen′` has `3n` coins. -/
+private theorem cca_gen_coins : (ccaScheme F E hE hFE).gen.coins = .mul (.const 3) .var := by
+  rw [ccaScheme_gen, NUPPT.coins_ofPolyTimeUniform]
+
+/-- `Enc′` has `n` coins. -/
+private theorem cca_enc_coins : (ccaScheme F E hE hFE).enc.coins = .var := by
+  rw [ccaScheme_enc, NUPPT.coins_ofPolyTimeUniform]
+
+/-- `3n = n + 2n`, for the key coins. -/
+private theorem cca_gen_len (n : ℕ) : (PolyExpr.mul (.const 3) .var).eval n = n + 2 * n := by
+  rw [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
+  ring
+
+/-- The `3n` key coins as the keys `k₁` (`n` bits) and `k₂` (`2n` bits). -/
+private noncomputable def ccaKeyEq (n : ℕ) :
+    (ccaScheme F E hE hFE).gen.Coins n ≃ (Fin n → Bool) × (Fin (2 * n) → Bool) :=
+  (NUPPT.coinsEquivPoly (cca_gen_coins F E hE hFE) n).trans
+    (EnsembleLemmas.coinsEquiv (cca_gen_len n)).symm
+
+/-- `⟦rg⟧ = ⟦k₁⟧ ++ ⟦k₂⟧` for `(k₁, k₂) = ccaKeyEq rg`. -/
+private theorem ofFn_ccaKeyEq (n : ℕ) (rg : (ccaScheme F E hE hFE).gen.Coins n) :
+    List.ofFn rg = List.ofFn (ccaKeyEq F E hE hFE n rg).1 ++
+      List.ofFn (ccaKeyEq F E hE hFE n rg).2 := by
+  rw [← EnsembleLemmas.ofFn_coinsEquiv (cca_gen_len n), ccaKeyEq, Equiv.trans_apply,
+    Equiv.apply_symm_apply, NUPPT.coinsEquivPoly_ofFn]
+
+/-- **`Gen′` outputs the pair of the two keys:** `Gen′(1^n; rg) = ⟨⟦k₁⟧, ⟦k₂⟧⟩` for
+`(k₁, k₂) = ccaKeyEq rg` (`runAt_ccaGen`). -/
+private theorem cca_gen_runAt (n : ℕ) (rg : (ccaScheme F E hE hFE).gen.Coins n) :
+    (ccaScheme F E hE hFE).gen.runAt n [] rg =
+      pairEncode (List.ofFn (ccaKeyEq F E hE hFE n rg).1)
+        (List.ofFn (ccaKeyEq F E hE hFE n rg).2) := by
+  have h := ofFn_ccaKeyEq F E hE hFE n rg
+  generalize ccaKeyEq F E hE hFE n rg = kk at h
+  revert rg
+  rw [ccaScheme_gen]
+  intro rg h
+  rw [runAt_ccaGen, h, List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn]
+
+/-- The encryption coins as an `n`-bit nonce, keeping the string. -/
+private noncomputable def ccaNonceEq (n : ℕ) :
+    (ccaScheme F E hE hFE).enc.Coins n ≃ (Fin n → Bool) :=
+  (NUPPT.coinsEquivPoly (cca_enc_coins F E hE hFE) n).trans
+    (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool))
+
+/-- `⟦ccaNonceEq n re⟧ = ⟦re⟧`. -/
+private theorem ofFn_ccaNonceEq (n : ℕ) (re : (ccaScheme F E hE hFE).enc.Coins n) :
+    List.ofFn (ccaNonceEq F E hE hFE n re) = List.ofFn re := by
+  rw [ccaNonceEq, Equiv.trans_apply, ofFn_arrowCongr_finCongr, NUPPT.coinsEquivPoly_ofFn]
+
+/-- **`Enc′` with the keys `k₁`, `k₂` and the coins `re`** is `encW (F n k₁) (F (2n) k₂)` with the
+nonce `ccaNonceEq re` (`runAt_ccaEnc`, `hFE` at `n` and at `2n`). -/
+private theorem ofFn_cca_encryptAt (n : ℕ) (k₁ : Fin n → Bool) (k₂ : Fin (2 * n) → Bool)
+    (m : Fin n → Bool) (re : (ccaScheme F E hE hFE).enc.Coins n) :
+    List.ofFn ((ccaScheme F E hE hFE).encryptAt n (pairEncode (List.ofFn k₁) (List.ofFn k₂)) m re) =
+      encW (F n k₁) (F (2 * n) k₂) (ccaNonceEq F E hE hFE n re) (List.ofFn m) := by
+  have hx : List.ofFn re = List.ofFn (ccaNonceEq F E hE hFE n re) :=
+    (ofFn_ccaNonceEq F E hE hFE n re).symm
+  generalize ccaNonceEq F E hE hFE n re = r at hx
+  revert re
+  simp only [FixedLengthScheme.encryptAt_eq]
+  rw [ccaScheme_enc]
+  intro re hx
+  have hm : (List.ofFn m).length = n := List.length_ofFn
+  have hc := length_maskL (F n k₁) r hm
+  have hp : List.ofFn r ++ maskL (F n k₁) r (List.ofFn m) =
+      List.ofFn (pairV n (List.ofFn r) (maskL (F n k₁) r (List.ofFn m))) := by
+    rw [pairV_eq, ofFn_padFin_of_length (by rw [List.length_append, List.length_ofFn, hc]; omega)]
+  rw [runAt_ccaEnc, hx, hFE, ← maskL_eq, hp, hFE, ← tagL_eq, ← ctW_eq, ← encW_eq,
+    ofFn_padFin_of_length (by rw [length_encW _ _ _ hm, cca_ctLen_eval])]
+
+/-- **`Dec′` with the keys `k₁`, `k₂`** on a word `w`: `⟨1, wC w ⊕ ⟦F n k₁ (wR w)⟧⟩` if `w` is valid
+for the tag function `F (2n) k₂`, and `⊥` otherwise (`ccaDecFun_eq`, `ccaDecOK_eq`, `hFE`). The
+zero-parameter malformed words are read alike: their total projections are empty.
+
+**Proof sketch.** Unfold the decryption machine (`ccaScheme_dec`, `runAtL_ofPolyTimeUniform`,
+`ccaDecFun_eq`, `ccaDecOK_eq`). Its test is `|wR w| = n`, `|wC w| = n` and
+`E⟨⟦k₂⟧, wR w ++ wC w⟩ = wT w`; on `n`-bit fields `E⟨⟦k₂⟧, wR w ++ wC w⟩` is
+`tagL (F (2n) k₂) (wR w) (wC w)` (`hFE`, `pairV_eq`), so the test is `validW`. On a valid word
+the output `wC w ⊕ E⟨⟦k₁⟧, wR w⟩` has `n` bits and decodes, giving `decL (F n k₁) w` (`hFE`,
+`decodeFin_ofFn`, `decAnswer_some`); otherwise the output `true :: 1^n` has `n + 1` bits, decodes
+to nothing and is read as `0^{n+1}` (`decodeFin_eq`, `decAnswer_none`, `ofFn_zeroBits`). -/
+private theorem ofFn_cca_decAnswer (n : ℕ) (k₁ : Fin n → Bool) (k₂ : Fin (2 * n) → Bool)
+    (w : List Bool) (rd : (ccaScheme F E hE hFE).dec.Coins n) :
+    List.ofFn (FixedLengthScheme.decAnswer (decodeFin n ((ccaScheme F E hE hFE).dec.runAt n
+        (pairEncode (pairEncode (List.ofFn k₁) (List.ofFn k₂)) w) rd))) =
+      if validW (F (2 * n) k₂) w = true then decL (F n k₁) w
+      else List.replicate (n + 1) false := by
+  revert rd
+  rw [ccaScheme_dec]
+  intro rd
+  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform, ccaDecFun_eq, ccaDecOK_eq]
+  simp only [NUPPT.inArg_eq, NUPPT.inParam_eq, NUPPT.advInput_eq, pairFstD_pairEncode,
+    pairSndD_pairEncode, List.length_replicate]
+  have htag : ∀ (hr : (pairFstD w).length = n) (hc : (pairFstD (pairSndD w)).length = n),
+      E (pairEncode (List.ofFn k₂) (pairFstD w ++ pairFstD (pairSndD w))) =
+        tagL (F (2 * n) k₂) (wR w) (wC w) := by
+    intro hr hc
+    have he : pairFstD w ++ pairFstD (pairSndD w) =
+        List.ofFn (pairV n (pairFstD w) (pairFstD (pairSndD w))) := by
+      rw [pairV_eq, ofFn_padFin_of_length (by rw [List.length_append, hr, hc]; omega)]
+    rw [he, hFE, tagL_eq, wR_eq, wC_eq]
+  by_cases hv : validW (F (2 * n) k₂) w = true
+  · rw [if_pos hv]
+    have hv' := hv
+    rw [validW_eq, Bool.and_eq_true, wfW_eq, Bool.and_eq_true, decide_eq_true_eq,
+      decide_eq_true_eq, decide_eq_true_eq] at hv'
+    obtain ⟨⟨hr, hc⟩, ht⟩ := hv'
+    rw [wR_eq] at hr
+    rw [wC_eq] at hc
+    have hok : (decide ((pairFstD w).length = n) && decide ((pairFstD (pairSndD w)).length = n) &&
+        decide (E (pairEncode (List.ofFn k₂) (pairFstD w ++ pairFstD (pairSndD w))) =
+          pairSndD (pairSndD w))) = true := by
+      rw [htag hr hc, ← wT_eq, ← ht]
+      simp [hr, hc]
+    rw [if_pos hok]
+    have hk : pairFstD w = List.ofFn (padFin n (pairFstD w)) := (ofFn_padFin_of_length hr).symm
+    have hlen : (List.zipWith xor (pairFstD (pairSndD w))
+        (List.ofFn (F n k₁ (padFin n (pairFstD w))))).length = n := by
+      rw [List.length_zipWith, List.length_ofFn, hc, Nat.min_self]
+    have hdec : List.zipWith xor (pairFstD (pairSndD w))
+        (List.ofFn (F n k₁ (padFin n (pairFstD w)))) =
+        List.ofFn (padFin n (List.zipWith xor (pairFstD (pairSndD w))
+          (List.ofFn (F n k₁ (padFin n (pairFstD w)))))) := (ofFn_padFin_of_length hlen).symm
+    conv_lhs => rw [hk, hFE, hdec, decodeFin_ofFn, FixedLengthScheme.decAnswer_some]
+    rw [List.ofFn_succ, Fin.cons_zero]
+    simp only [Fin.cons_succ]
+    rw [← hdec, decL_eq, wC_eq, wR_eq]
+  · rw [if_neg hv]
+    have hnok : (decide ((pairFstD w).length = n) && decide ((pairFstD (pairSndD w)).length = n) &&
+        decide (E (pairEncode (List.ofFn k₂) (pairFstD w ++ pairFstD (pairSndD w))) =
+          pairSndD (pairSndD w))) = false := by
+      by_contra hc'
+      rw [Bool.not_eq_false, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
+        decide_eq_true_eq, decide_eq_true_eq] at hc'
+      obtain ⟨⟨hr, hc⟩, ht⟩ := hc'
+      apply hv
+      rw [validW_eq, wfW_eq, wR_eq, wC_eq, hr, hc, wT_eq, ← ht, htag hr hc, wR_eq, wC_eq]
+      simp
+    rw [if_neg (by rw [hnok]; exact Bool.false_ne_true), decodeFin_eq,
+      dif_neg (by rw [List.length_cons, List.length_replicate]; omega),
+      FixedLengthScheme.decAnswer_none, ofFn_zeroBits]
+
+/-- **The CCA2 experiment of `π′` is the experiment with `f_{k₁}` and `f_{k₂}`:**
+`Pr[IND_b = 1] = 𝔼_{k₁} 𝔼_{k₂} ettAcc (F n k₁) (F (2n) k₂) false b A Q`, on the reduction's lengths.
+
+**Proof sketch.** `ETTGame.accept_indGame_eq` with the key split (`ccaKeyEq`, `cca_gen_runAt`), the
+nonce (`ccaNonceEq`) and the readers `ofFn_cca_encryptAt`, `ofFn_cca_decAnswer`; the key coins are
+uniform pairs (`expect_sample_equiv`, `expect_sample_prod`), and the lengths are the reduction's
+(`cca_inLens`, `cca_outLens`, `cca_ctLen_eval`, `expect_ettImpl_transport`). -/
+private theorem accept_cca_indGame (A : NUPPT) (Q : ℕ) (b : Bool) (n : ℕ) :
+    accept ((ccaScheme F E hE hFE).indGame .cca2 A Q b n) =
+      expect (sample (Fin n → Bool)) fun k₁ => expect (sample (Fin (2 * n) → Bool)) fun k₂ =>
+        ettAcc (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
+          (F n k₁) (F (2 * n) k₂) false b A Q := by
+  rw [accept_indGame_eq (ccaScheme F E hE hFE) b n A Q (cca_ctLen_eval F E hE hFE n)
+      (fun rg => F n (ccaKeyEq F E hE hFE n rg).1)
+      (fun rg => F (2 * n) (ccaKeyEq F E hE hFE n rg).2) (ccaNonceEq F E hE hFE n)
+      (fun rg m re => by rw [cca_gen_runAt]; exact ofFn_cca_encryptAt F E hE hFE n _ _ m re)
+      (fun rg w rd => by rw [cca_gen_runAt]; exact ofFn_cca_decAnswer F E hE hFE n _ _ w rd),
+    ← expect_sample_equiv (ccaKeyEq F E hE hFE n).symm, ChallengeSim.expect_sample_prod]
+  refine congrArg _ (funext fun k₁ => congrArg _ (funext fun k₂ => ?_))
+  simp only [Equiv.apply_symm_apply]
+  rw [ettAcc_eq]
+  refine congrArg _ (funext fun r => ?_)
+  exact expect_ettImpl_transport n _ _ false b (cca_inLens F E hE hFE n)
+    (cca_outLens F E hE hFE n) (by rw [cca_ctLen_eval, ettCt_eval]) A Q r
+
+/-- **Step 1: the tag key becomes a random function** [PS10, Thm 170.4, proof]. For a machine
+adversary `A` with budget `q` and a bit `b`, there is a PRF distinguisher `D` such that at every
+`n`, `|Pr[IND_b = 1] − 𝔼_{k₁} 𝔼_R ettAcc (F n k₁) R false b A (q n)|` is the PRF advantage of `D`
+at parameter `2n` with budget `q(2n)`.
+
+**Proof sketch.** `accept_cca_indGame` and `ETTGame.exists_tagStep`. -/
+private theorem cca_tag_step (A : NUPPT) (q : PolyExpr) (b : Bool) :
+    ∃ D : NUPPT, ∀ n : ℕ,
+      |accept ((ccaScheme F E hE hFE).indGame .cca2 A (q.eval n) b n) -
+          expect (sample (Fin n → Bool)) (fun k₁ =>
+            expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))) fun R =>
+              ettAcc (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
+                (F n k₁) R false b A (q.eval n))| =
+        prfAdv (F (2 * n)) (D.toOracleAdversary (2 * n) (2 * n) (2 * n) (q.eval (2 * n))) := by
+  obtain ⟨D, hD⟩ := exists_tagStep F E hE hFE A q b
+  exact ⟨D, fun n => by rw [accept_cca_indGame, hD n]⟩
+
+/-- **Step 2: fresh decryption queries are rejected** [PS10, Thm 170.4, proof]. For `n > 0`, the
+experiments with a random tag function without and with the rejection of fresh pairs, averaged
+over the key `k₁`, differ by at most `q(n) / 2^{2n}`.
+
+**Proof sketch.** `ETTGame.abs_ettAcc_rej_sub_le` for each `k₁` (the ciphertexts have
+`6n + 4 = ettCt(n)` bits and the challenge queries `2n`), averaged over `k₁`
+(`abs_expect_sub_le`). -/
+private theorem cca_rej_step (A : NUPPT) (Q : ℕ) (b : Bool) (n : ℕ) (hn : 0 < n) :
+    |expect (sample (Fin n → Bool)) (fun k₁ =>
+          expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))) fun R =>
+            ettAcc (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
+              (F n k₁) R false b A Q) -
+        expect (sample (Fin n → Bool)) (fun k₁ =>
+          expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))) fun R =>
+            ettAcc (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
+              (F n k₁) R true b A Q)| ≤ Q * ((2 : ℝ) ^ (2 * n))⁻¹ :=
+  abs_expect_sub_le _ fun k₁ => abs_ettAcc_rej_sub_le _ _ _ n (F n k₁) b hn (ettCt_eval n)
+    (by show (ettDin 2).eval n = n + n; rw [ettDin_two, PolyExpr.eval_add, PolyExpr.eval_var])
+    A Q
+
+end Proof
+
 /-- **Theorem 170.4: `π′` is CCA2-secure** [PS10, Theorem 170.4] when `F` is a pseudorandom
 function family.
 
-**Proof sketch** (the source's, made explicit).
-1. Replace `f_{k₂}` by a random function `RF` on `2n` bits: by PRF security at parameter `2n`,
-   the advantage changes by a negligible amount. The reduction samples `k₁` itself and answers
-   `Enc′` and `Dec′` with its oracle in place of `f_{k₂}`. T2
-   (`Games.exists_interactiveHandlerMachine`) implements the forwarding handler with `k₁`
-   in its seed, the input-free companion supplies its machine input, and T4
-   (`Games.exists_toOracleAdversary_of_bitCodec`) provides the oracle adversary at length
-   `2n`.
-2. For positive `n`, call a `Dec′` query `(r, c₁, t)` *fresh* if `(r, c₁)` is not the
-   ciphertext part of an earlier `Enc′` or challenge answer. Compare with a game that always
-   rejects fresh-pair queries. Couple both games with the same tapes and `RF`: they agree until
-   the first fresh-pair query with a valid tag. In the always-reject game, prior rejected guesses
-   reveal no value of `RF` at such a pair. Each guess therefore hits that unrevealed uniform
-   `2n`-bit value with probability at most `2^{-2n}`, even if the pair was queried before. The union bound
-   gives a first-discrepancy probability at most `q(n)/2^{2n}` in each bit-game. This does not
-   assert the same conditional probability after failed guesses in the original game.
-   A nonfresh valid-tag query is an earlier answer itself: canonical parsing and the tag's
-   dependence on `(r, c₁)` make it the refused challenge or an encryption of a chosen message.
-3. The always-reject game is simulated by a CPA adversary against the §3.9 scheme under `k₁`:
-   `Enc′` answers come from the CPA encryption oracle, tagged by a lazily sampled `RF`; `Dec′`
-   answers come from the table of earlier answers, or are `⊥`. Up to fixed constant factors
-   when combining the two bit-games, the advantage is bounded by the CPA advantage
-   (`prfFixedScheme_cpa`), the first-discrepancy term `q(n)/2^{2n}`, and the PRF advantage.
-   Each is negligible; the zero-parameter behavior described above changes no asymptotic claim.
-
-The source's simulator tags with fresh uniform strings rather than a lazily sampled `RF`. The two
-differ only when two answers share `(r, c₁)`, a collision of the `n`-bit `r`, of probability at
-most `q(n)²/2^n`. -/
+**Proof sketch** (the source's, made explicit). Fix a machine adversary `A` with budget `q` and a
+bit `b`; write `P_b` for `Pr[IND_b = 1]`.
+1. **The tag key becomes a random function** (`cca_tag_step`, from `ETTGame.exists_tagStep`):
+   replacing `f_{k₂}` by a uniform random function `R` on `2n` bits moves `P_b` by the PRF
+   advantage, at parameter `2n`, of a next-query machine `D_b`: T2
+   (`Games.exists_interactiveHandlerMachine`) with `k₁` and the nonces in its seed, T4
+   (`Games.exists_toOracleAdversary_of_bitCodec`) at length `2n`, and the parameter halving.
+2. **Fresh decryption queries are rejected** (`cca_rej_step`, from
+   `ETTGame.abs_ettAcc_rej_sub_le`): for `n > 0`, the experiment that rejects every `Dec′` query
+   whose pair `(r, c₁)` is not that of an earlier `Enc′` answer differs by at most
+   `q(n)/2^{2n}`: the two agree until the first fresh pair with a valid tag, and each such guess
+   hits the unrevealed value of `R` with probability at most `2^{-2n}`.
+3. **The rejecting experiment is a CPA experiment of the §3.9 scheme** (`ETTGame.exists_cpaStep`):
+   averaged over `R` it is the experiment with lazily sampled tags (`ETTGame.expect_ettImpl_lazy`),
+   which a CPA adversary `B` against the §3.9 scheme with pad `f_{k₁}` simulates: `Enc′` and the
+   challenge come from the CPA oracles and are tagged from the table of earlier answers, the
+   challenge record, or a fresh tape; `Dec′` is answered from the table (`ETTGame.bHandler`, T2).
+4. **The CPA experiment hides the bit** (as in [PS10, Theorem 168.2]): replacing `f_{k₁}` by a
+   random function costs the PRF advantages of `PRFGame.exists_prfReduction`'s machines `C_b`
+   (`ETTGame.prfAdv_eq_expect`), and with a random function the two bits are `Q²/2^n` apart,
+   `Q = qRed q` (`PRFGame.abs_expect_fImpl_sub_le`).
+So for `n > 0`, `|P₀ − P₁| ≤ adv(D₀) + adv(D₁) + 2q(n)/2^{2n} + adv(C₀) + adv(C₁) + Q(n)²/2^n`,
+every term negligible (`PRF.negligible_prfAdv`, `Negligible.comp_of_le` at `2n`,
+`EnsembleLemmas.negligible_polyExpr_mul`, `negligible_two_pow_neg`); at `n = 0` the advantage is
+at most `1` (`advantage_le_one`), an eventually-zero correction.
+
+Step 4 re-derives the CPA bound for the §3.9 scheme from `PRFGame`'s public reduction and
+collision bound rather than citing `prfFixedScheme_cpa`, since the simulator's CPA adversary runs
+against the oracles `PRFGame.fImpl` directly. The simulator samples tags lazily, so two answers that
+share `(r, c₁)` share their tag, as with `RF`; the source's fresh uniform tags would differ from
+`RF` only on such a collision. -/
 theorem ccaScheme_cca2 (hF : PRF F) : (ccaScheme F E hE hFE).INDSecure .cca2 := by
-  sorry
+  refine (FixedLengthScheme.INDSecure_iff _ _).2 fun A q => ?_
+  obtain ⟨D₀, hD₀⟩ := cca_tag_step F E hE hFE A q false
+  obtain ⟨D₁, hD₁⟩ := cca_tag_step F E hE hFE A q true
+  obtain ⟨B, hB⟩ := ETTGame.exists_cpaStep A q
+  obtain ⟨C₀, hC₀⟩ := PRFGame.exists_prfReduction B (PRFGame.qRed q) false false
+  obtain ⟨C₁, hC₁⟩ := PRFGame.exists_prfReduction B (PRFGame.qRed q) false true
+  refine ⟨fun n =>
+      prfAdv (F (2 * n)) (D₀.toOracleAdversary (2 * n) (2 * n) (2 * n) (q.eval (2 * n))) +
+      prfAdv (F (2 * n)) (D₁.toOracleAdversary (2 * n) (2 * n) (2 * n) (q.eval (2 * n))) +
+      2 * ((q.eval n : ℝ) * ((2 : ℝ) ^ (2 * n))⁻¹) +
+      prfAdv (F n) (C₀.toOracleAdversary n n n ((PRFGame.qRed (PRFGame.qRed q)).eval n)) +
+      prfAdv (F n) (C₁.toOracleAdversary n n n ((PRFGame.qRed (PRFGame.qRed q)).eval n)) +
+      ((PRFGame.qRed q).eval n : ℝ) ^ 2 / 2 ^ n + (if n = 0 then 1 else 0), ?_, fun n => ?_⟩
+  · -- Each term is negligible.
+    have hT₀ := (hF.negligible_prfAdv D₀ q).comp_of_le (fun n => 2 * n)
+      fun N => by show N ≤ 2 * N; omega
+    have hT₁ := (hF.negligible_prfAdv D₁ q).comp_of_le (fun n => 2 * n)
+      fun N => by show N ≤ 2 * N; omega
+    have hR : Negligible fun n => 2 * ((q.eval n : ℝ) * ((2 : ℝ) ^ (2 * n))⁻¹) := by
+      refine ((EnsembleLemmas.negligible_polyExpr_mul q negligible_two_pow_neg).const_mul 2).mono
+        ⟨0, fun n _ => ?_⟩
+      have h₁ : ((2 : ℝ) ^ (2 * n))⁻¹ ≤ (2 : ℝ)⁻¹ ^ n := by
+        rw [inv_pow]
+        exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
+      have h₂ : (0 : ℝ) ≤ q.eval n := Nat.cast_nonneg _
+      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
+      gcongr
+    have hP₀ := hF.negligible_prfAdv C₀ (PRFGame.qRed (PRFGame.qRed q))
+    have hP₁ := hF.negligible_prfAdv C₁ (PRFGame.qRed (PRFGame.qRed q))
+    have hS : Negligible fun n => ((PRFGame.qRed q).eval n : ℝ) ^ 2 / 2 ^ n := by
+      refine (EnsembleLemmas.negligible_polyExpr_mul (.mul (PRFGame.qRed q) (PRFGame.qRed q))
+        negligible_two_pow_neg).mono ⟨0, fun n _ => le_of_eq ?_⟩
+      rw [PolyExpr.eval_mul, Nat.cast_mul, inv_pow, ← div_eq_mul_inv, sq]
+    have hZ : Negligible fun n : ℕ => if n = 0 then (1 : ℝ) else 0 :=
+      negligible_zero.mono ⟨1, fun n hn => by rw [if_neg (by omega)]⟩
+    exact (((((hT₀.add hT₁).add hR).add hP₀).add hP₁).add hS).add hZ
+  · have n₀ := prfAdv_nonneg (F (2 * n))
+      (D₀.toOracleAdversary (2 * n) (2 * n) (2 * n) (q.eval (2 * n)))
+    have n₁ := prfAdv_nonneg (F (2 * n))
+      (D₁.toOracleAdversary (2 * n) (2 * n) (2 * n) (q.eval (2 * n)))
+    have m₀ := prfAdv_nonneg (F n)
+      (C₀.toOracleAdversary n n n ((PRFGame.qRed (PRFGame.qRed q)).eval n))
+    have m₁ := prfAdv_nonneg (F n)
+      (C₁.toOracleAdversary n n n ((PRFGame.qRed (PRFGame.qRed q)).eval n))
+    have hc : (0 : ℝ) ≤ 2 * ((q.eval n : ℝ) * ((2 : ℝ) ^ (2 * n))⁻¹) := by positivity
+    have hs : (0 : ℝ) ≤ ((PRFGame.qRed q).eval n : ℝ) ^ 2 / 2 ^ n := by positivity
+    beta_reduce
+    rcases Nat.eq_zero_or_pos n with rfl | hn
+    · -- At `n = 0` the advantage is at most `1`.
+      have h1 := advantage_le_one ((ccaScheme F E hE hFE).indGame .cca2 A (q.eval 0) false 0)
+        ((ccaScheme F E hE hFE).indGame .cca2 A (q.eval 0) true 0)
+      rw [if_pos rfl]
+      linarith
+    · rw [if_neg (by omega : n ≠ 0), add_zero, advantage_eq]
+      -- Steps 1 and 2 for both bits.
+      have t₀ := hD₀ n
+      have t₁ := hD₁ n
+      have r₀ := cca_rej_step F A (q.eval n) false n hn
+      have r₁ := cca_rej_step F A (q.eval n) true n hn
+      -- Step 3: the rejecting experiments are CPA experiments of the §3.9 scheme.
+      simp only [hB false n, hB true n] at r₀ r₁
+      have p₀ := ETTGame.prfAdv_eq_expect (F n)
+        (C₀.toOracleAdversary n n n ((PRFGame.qRed (PRFGame.qRed q)).eval n))
+      have p₁ := ETTGame.prfAdv_eq_expect (F n)
+        (C₁.toOracleAdversary n n n ((PRFGame.qRed (PRFGame.qRed q)).eval n))
+      simp only [hC₀ n, hC₁ n] at p₀ p₁
+      have hcpa := PRFGame.abs_expect_fImpl_sub_le (fun i => (PRFGame.pkDin i).eval n)
+        (fun i => (PRFGame.pkDout i).eval n) (PRFGame.ctP.eval n) n (PRFGame.atkOf false)
+        (by rw [PRFGame.decOpen_atkOf]; rfl) (PRFGame.ctP_eval n)
+        (by show (PRFGame.pkDin 2).eval n = n + n
+            rw [PRFGame.pkDin_two, PolyExpr.eval_add, PolyExpr.eval_var])
+        (fun r : B.Coins n => B.toComp (bitCodec (fun i => (PRFGame.pkDin i).eval n)
+          (fun i => (PRFGame.pkDout i).eval n) 1) n ((PRFGame.qRed q).eval n) r)
+        (fun a => (List.ofFn a).headD false = true) ((PRFGame.qRed q).eval n)
+        (fun r => NUPPT.toComp_costBoundedBy _ _ _ _ _)
+      obtain ⟨a₀, b₀⟩ := abs_le.1 t₀.le
+      obtain ⟨a₁, b₁⟩ := abs_le.1 t₁.le
+      obtain ⟨c₀, d₀⟩ := abs_le.1 r₀
+      obtain ⟨c₁, d₁⟩ := abs_le.1 r₁
+      obtain ⟨e₀, f₀⟩ := abs_le.1 p₀.ge
+      obtain ⟨e₁, f₁⟩ := abs_le.1 p₁.ge
+      obtain ⟨g, h⟩ := abs_le.1 hcpa
+      refine abs_le.2 ⟨by linarith, by linarith⟩
 
 end TCSlib.Cryptography.Composability
diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/CPAHandler.lean b/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/CPAHandler.lean
new file mode 100644
index 000000000..fd76cdff9
--- /dev/null
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/CPAHandler.lean
@@ -0,0 +1,806 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Handler
+import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Lazy
+import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Handler
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The handler of the CPA reduction
+
+Step 3 of [PS10, Theorem 170.4]: the experiment that rejects fresh decryption queries is
+simulated by a CPA adversary against the §3.9 scheme. This file builds that adversary's handler
+(`bHandler`): a `Games.InteractiveHandler` from the CCA2 oracles of the encrypt-then-tag scheme
+(lengths `ettDin`, `ettDout`) to the CPA oracles of the §3.9 scheme (lengths `PRFGame.pkDin`,
+`PRFGame.pkDout`).
+
+The handler's seed is `q(n)` tag tapes of `2n` bits; its state is the table of its `Enc′` answers
+(`GGMRed.tblEnc` of the entries `(r ‖ c₁, t ‖ m)`, newest first), the query count and the
+challenge record (`bState`).
+- `Enc′` on `m`: ask the CPA encryption oracle, read its answer `⟨r, c₁⟩`, take the tag of
+  `r ‖ c₁` from the table, else from the record, else from the query's tape, answer
+  `⟨r, ⟨c₁, t⟩⟩` and add the entry.
+- `Dec′` on `w`: refuse the record; if `w` is well formed and the table holds its pair with its tag,
+  answer `⟨1, m⟩` with the table's message, else `⊥` (`lazyDec`). No outer query.
+- `Challenge`: the first time, ask the CPA challenge oracle on `⟨m₀, m₁⟩`, tag its answer as `Enc′`
+  does (without an entry) and record it; later repeat the record.
+Words read from the outer answer are padded to their lengths (`EnsembleLemmas.padL`), so every
+call is well formed for every outer answer. Lookups use GGM's table lookup (`GGMRed.lookup`,
+`GGMRed.lookup_tblOf`).
+
+## Main definitions
+
+* `ETTGame.encE`, `tblW`, `bStLen`, `bSeedLen`, `bState`, `bSeed`, `bTapeOf`.
+* `ETTGame.bHandler q hq b`: the handler.
+
+## Main results
+
+* `ETTGame.lookup_tblW`: the lookup on the table word is `lookL`.
+* `ETTGame.bHandler_impl_enc`, `_impl_dec`, `_impl_challenge_some`, `_impl_challenge_none`: its
+  answers on encoded states.
+* `ETTGame.bHandler_finish`, `bHandler_init_hstate`.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 170.4 (book pp. 170–171).
+-/
+
+namespace TCSlib.Cryptography.Composability.ETTGame
+
+open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
+open TCSlib.Cryptography.Games.InteractiveHandler (rU rW rS rI rX rL rAns)
+open TCSlib.Cryptography.Composability.PRFGame (pkDin pkDout ctP)
+
+/-! ### The table word -/
+
+section Table
+
+variable {n : ℕ}
+
+/-- The string entry of a lazy-table entry `(p, t, m)`: `encE (p, t, m) = (⟦p⟧, ⟦t⟧ ++ m)`. -/
+def encE (e : LEntry n) : List Bool × List Bool := (List.ofFn e.1, List.ofFn e.2.1 ++ e.2.2)
+
+/-- `encE e = (⟦e.1⟧, ⟦e.2.1⟧ ++ e.2.2)`. -/
+theorem encE_eq (e : LEntry n) : encE e = (List.ofFn e.1, List.ofFn e.2.1 ++ e.2.2) := rfl
+
+/-- **The table word** of a lazy table: the nested pairs of its string entries (`GGMRed.tblEnc`),
+`tblW L = GGMRed.tblEnc (L.map encE)`. -/
+def tblW (L : List (LEntry n)) : List Bool := GGMRed.tblEnc (L.map encE)
+
+/-- `tblW L = GGMRed.tblEnc (L.map encE)`. -/
+theorem tblW_eq (L : List (LEntry n)) : tblW L = GGMRed.tblEnc (L.map encE) := rfl
+
+/-- The table word of the empty table is empty: `tblW [] = []`. -/
+theorem tblW_nil : tblW ([] : List (LEntry n)) = [] := by
+  rw [tblW_eq, List.map_nil, GGMRed.tblEnc_nil]
+
+/-- A new entry is the first pair of the table word:
+`tblW (e :: L) = ⟨⟨⟦p⟧, ⟦t⟧ ++ m⟩, tblW L⟩`. -/
+theorem tblW_cons (e : LEntry n) (L : List (LEntry n)) :
+    tblW (e :: L) =
+      pairEncode (pairEncode (List.ofFn e.1) (List.ofFn e.2.1 ++ e.2.2)) (tblW L) := by
+  rw [tblW_eq, tblW_eq, List.map_cons, GGMRed.tblEnc_cons, encE_eq]
+
+/-- With `n`-bit messages, each entry adds `14n + 6` bits:
+`|tblW L| = |L| · (14n + 6)`. -/
+theorem length_tblW (L : List (LEntry n)) (hL : ∀ e ∈ L, e.2.2.length = n) :
+    (tblW L).length = L.length * (14 * n + 6) := by
+  induction L with
+  | nil => rw [tblW_nil, List.length_nil, List.length_nil, Nat.zero_mul]
+  | cons e L ih =>
+    rw [tblW_cons, length_pairEncode, length_pairEncode, List.length_append, List.length_ofFn,
+      List.length_ofFn, hL e (List.mem_cons_self ..),
+      ih fun e' he' => hL e' (List.mem_cons_of_mem _ he'), List.length_cons]
+    ring
+
+/-- The table of string entries is `GGMRed.tblOf` of the pairs, with the entries' values. -/
+private theorem map_encE_eq_tblOf (L : List (LEntry n)) :
+    L.map encE = GGMRed.tblOf (fun k => (encE (L.getD k default)).2) (keysL L) 0 := by
+  refine List.ext_getElem (by rw [List.length_map, GGMRed.length_tblOf, keysL_eq, List.length_map])
+    fun k h₁ h₂ => ?_
+  have hk : k < L.length := by rwa [List.length_map] at h₁
+  refine Prod.ext ?_ ?_
+  · rw [GGMRed.tblOf_getElem_fst, List.getElem_map, encE_eq]
+    simp only [keysL_eq, List.getElem_map]
+  · rw [GGMRed.tblOf_getElem_snd, List.getElem_map, Nat.zero_add, List.getD_eq_getElem _ _ hk]
+
+/-- **The lookup on the table word is `lookL`:**
+`lookup ⟨⟦p⟧, tblW L⟩ = ⟨[], ⟦t⟧ ++ m⟩` for the newest entry `(p, t, m)` at `p`, and `[]` if there
+is none (`GGMRed.lookup_tblOf`). -/
+theorem lookup_tblW (L : List (LEntry n)) (p : Fin (2 * n) → Bool) :
+    GGMRed.lookup (pairEncode (List.ofFn p) (tblW L)) =
+      match lookL L p with
+      | some e => pairEncode [] (List.ofFn e.2.1 ++ e.2.2)
+      | none => [] := by
+  rw [tblW_eq, map_encE_eq_tblOf, GGMRed.lookup_tblOf, lookL_eq]
+  by_cases hp : p ∈ keysL L
+  · rw [if_pos hp, if_pos hp, encE_eq]
+  · rw [if_neg hp, if_neg hp]
+
+end Table
+
+/-! ### Lengths, state and seed -/
+
+variable (q : PolyExpr)
+
+/-- The state length `2q(14n + 6) + 2q + 6n + 9`:
+`(bStLen q).eval n = 2 q(n) (14n + 6) + 2 q(n) + (6n + 9)`. -/
+def bStLen : PolyExpr :=
+  .add
+    (.add (.mul (.const 2) (.mul q (.add (.mul (.const 14) .var) (.const 6)))) (.mul (.const 2) q))
+    (.add (.mul (.const 6) .var) (.const 9))
+
+/-- `(bStLen q).eval n = 2 q(n) (14n + 6) + 2 q(n) + 6n + 9`. -/
+theorem bStLen_eval (n : ℕ) :
+    (bStLen q).eval n = 2 * (q.eval n * (14 * n + 6)) + 2 * q.eval n + (6 * n + 9) := by
+  simp only [bStLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
+
+/-- The seed length `q(n) · 2n`: one tag tape per query, `bSeedLen q = q · tagLen`, so
+`(bSeedLen q).eval n = q(n) · 2n`. -/
+def bSeedLen : PolyExpr := .mul q tagLen
+
+/-- `(bSeedLen q).eval n = q(n) · 2n`. -/
+theorem bSeedLen_eval (n : ℕ) : (bSeedLen q).eval n = q.eval n * (2 * n) := by
+  rw [bSeedLen, PolyExpr.eval_mul, tagLen_eval]
+
+/-- **The encoded state** with the table `L`, the query count `j` and the record `o`:
+`⟨tblW L, ⟨1^j, recBits o⟩⟩`, padded with `false` to the state length,
+`bState q n j L o = padFin _ ⟨tblW L, ⟨1^j, recBits n o⟩⟩`. -/
+def bState (n j : ℕ) (L : List (LEntry n)) (o : Option (Fin (ettCt.eval n) → Bool)) :
+    Fin ((bStLen q).eval n) → Bool :=
+  padFin _ (pairEncode (tblW L) (pairEncode (List.replicate j true) (recBits n o)))
+
+/-- `bState q n j L o = padFin _ ⟨tblW L, ⟨1^j, recBits n o⟩⟩`. -/
+theorem bState_eq (n j : ℕ) (L : List (LEntry n)) (o : Option (Fin (ettCt.eval n) → Bool)) :
+    bState q n j L o =
+      padFin _ (pairEncode (tblW L) (pairEncode (List.replicate j true) (recBits n o))) :=
+  rfl
+
+/-- **The seed** from the tape word: `⟦bSeed q n W⟧ = ⟦W⟧`. -/
+def bSeed (n : ℕ) : (Fin (q.eval n * (2 * n)) → Bool) ≃ (Fin ((bSeedLen q).eval n) → Bool) :=
+  Equiv.arrowCongr (finCongr (bSeedLen_eval q n).symm) (Equiv.refl Bool)
+
+/-- `bSeed q n = arrowCongr (finCongr _) (refl Bool)`. -/
+theorem bSeed_eq (n : ℕ) :
+    bSeed q n = Equiv.arrowCongr (finCongr (bSeedLen_eval q n).symm) (Equiv.refl Bool) := rfl
+
+/-- `⟦bSeed q n W⟧ = ⟦W⟧`. -/
+theorem ofFn_bSeed (n : ℕ) (W : Fin (q.eval n * (2 * n)) → Bool) :
+    List.ofFn (bSeed q n W) = List.ofFn W := by
+  rw [bSeed, ofFn_arrowCongr_finCongr]
+
+/-- The tag tape `j` of the tape word: block `j` of `W`,
+`bTapeOf q n W j hj = blocks (q n) (2n) W ⟨j, hj⟩`. -/
+def bTapeOf (n : ℕ) (W : Fin (q.eval n * (2 * n)) → Bool) (j : ℕ) (hj : j < q.eval n) :
+    Fin (2 * n) → Bool :=
+  EnsembleLemmas.blocks (q.eval n) (2 * n) W ⟨j, hj⟩
+
+/-- `bTapeOf q n W j hj = blocks (q n) (2n) W ⟨j, hj⟩`. -/
+theorem bTapeOf_eq (n : ℕ) (W : Fin (q.eval n * (2 * n)) → Bool) (j : ℕ) (hj : j < q.eval n) :
+    bTapeOf q n W j hj = EnsembleLemmas.blocks (q.eval n) (2 * n) W ⟨j, hj⟩ := rfl
+
+/-- The fields of an encoded state that fits: the table word, the count `1^j`, the flag and the
+record.
+
+**Proof sketch.** The encoded triple fits in the state length: `|tblW L| = |L| · (14n + 6)` with
+`|L| ≤ q(n)` (`length_tblW`) and `j ≤ q(n)` (`bStLen_eval`). So the padding only appends `false`s
+to the innermost component (`ofFn_padFin_of_le`, `pairEncode_append_right` twice), and the
+projections read `tblW L`, `1^j` and `recBits n o` followed by `false`s, whose head is the flag and
+whose next `ct(n)` bits are the record (by cases on `o`). -/
+private theorem fields_bState (n j : ℕ) (L : List (LEntry n))
+    (o : Option (Fin (ettCt.eval n) → Bool))
+    (hj : j ≤ q.eval n) (hL : L.length ≤ q.eval n) (hm : ∀ e ∈ L, e.2.2.length = n) :
+    pairFstD (List.ofFn (bState q n j L o)) = tblW L ∧
+      pairFstD (pairSndD (List.ofFn (bState q n j L o))) = List.replicate j true ∧
+      (pairSndD (pairSndD (List.ofFn (bState q n j L o)))).headD false = o.isSome ∧
+      ((pairSndD (pairSndD (List.ofFn (bState q n j L o)))).drop 1).take (ettCt.eval n) =
+        (recBits n o).drop 1 := by
+  have hlen : (pairEncode (tblW L) (pairEncode (List.replicate j true) (recBits n o))).length ≤
+      (bStLen q).eval n := by
+    rw [length_pairEncode, length_pairEncode, List.length_replicate, length_recBits,
+      length_tblW L hm, bStLen_eval, ettCt_eval]
+    have : L.length * (14 * n + 6) ≤ q.eval n * (14 * n + 6) := Nat.mul_le_mul_right _ hL
+    omega
+  rw [bState_eq, Collection.ofFn_padFin_of_le hlen, ← GGMRed.pairEncode_append_right,
+    pairFstD_pairEncode, pairSndD_pairEncode, ← GGMRed.pairEncode_append_right,
+    pairFstD_pairEncode, pairSndD_pairEncode]
+  refine ⟨rfl, rfl, ?_, ?_⟩
+  · cases o with
+    | none => rw [recBits_none, List.cons_append, List.headD_cons, Option.isSome_none]
+    | some c => rw [recBits_some, List.cons_append, List.headD_cons, Option.isSome_some]
+  · cases o with
+    | none =>
+      rw [recBits_none, List.cons_append, List.drop_succ_cons, List.drop_zero, List.drop_succ_cons,
+        List.drop_zero, List.take_left' List.length_replicate]
+    | some c =>
+      rw [recBits_some, List.cons_append, List.drop_succ_cons, List.drop_zero, List.drop_succ_cons,
+        List.drop_zero, List.take_left' List.length_ofFn]
+
+/-! ### The round function -/
+
+/-- The table word of the state. -/
+private def bTbl (w : List Bool) : List Bool := pairFstD (rS w)
+/-- The query count of the state. -/
+private def bJ (w : List Bool) : List Bool := pairFstD (pairSndD (rS w))
+/-- The challenge flag of the state. -/
+private def bFlag (w : List Bool) : Bool := (pairSndD (pairSndD (rS w))).headD false
+/-- The recorded challenge of the state. -/
+private def bRec (w : List Bool) : List Bool :=
+  ((pairSndD (pairSndD (rS w))).drop 1).take (ettCt.eval (rU w).length)
+/-- A word read at `2n` bits. -/
+private def bPad2 (w v : List Bool) : List Bool := EnsembleLemmas.padL (tagLen.eval (rU w).length) v
+/-- The tape of the query count. -/
+private def bTape (w : List Bool) : List Bool :=
+  ((rW w).drop ((bJ w).length * tagLen.eval (rU w).length)).take (tagLen.eval (rU w).length)
+/-- The pair `r ‖ c₁` of the outer answer `⟨r, c₁⟩`, at `2n` bits. -/
+private def bKey (w : List Bool) : List Bool := bPad2 w (pairFstD (rAns w) ++ pairSndD (rAns w))
+/-- The table lookup at a pair. -/
+private def bLook (w key : List Bool) : List Bool := GGMRed.lookup (pairEncode key (bTbl w))
+/-- The pair of the record, at `2n` bits. -/
+private def bChalKey (w : List Bool) : List Bool :=
+  bPad2 w (pairFstD (bRec w) ++ pairFstD (pairSndD (bRec w)))
+/-- The tag of the record, at `2n` bits. -/
+private def bChalTag (w : List Bool) : List Bool := bPad2 w (pairSndD (pairSndD (bRec w)))
+/-- The tag of the outer answer's pair: the table's, else the record's, else the tape. -/
+private def bTag (w : List Bool) : List Bool :=
+  if decide (bLook w (bKey w) = []) then
+    (if bFlag w && decide (bChalKey w = bKey w) then bChalTag w else bTape w)
+  else (pairSndD (bLook w (bKey w))).take (tagLen.eval (rU w).length)
+/-- The ciphertext `⟨r, ⟨c₁, t⟩⟩` of the outer answer and its tag, at `6n + 4` bits. -/
+private def bCt (w : List Bool) : List Bool :=
+  EnsembleLemmas.padL (ettCt.eval (rU w).length)
+    (pairEncode (pairFstD (rAns w)) (pairEncode (pairSndD (rAns w)) (bTag w)))
+/-- The new state: the table word `tbl`, count `j + 1`, record `t`. -/
+private def bNew (w tbl t : List Bool) : List Bool :=
+  EnsembleLemmas.padL ((bStLen q).eval (rU w).length) (pairEncode tbl (pairEncode (true :: bJ w) t))
+/-- The pair of the decryption query, at `2n` bits. -/
+private def bDKey (w : List Bool) : List Bool :=
+  bPad2 w (pairFstD (rX w) ++ pairFstD (pairSndD (rX w)))
+/-- Whether the decryption query is well formed. -/
+private def bWF (w : List Bool) : Bool :=
+  decide ((pairFstD (rX w)).length = (rU w).length) &&
+    decide ((pairFstD (pairSndD (rX w))).length = (rU w).length)
+/-- Whether the decryption query is the recorded challenge. -/
+private def bRef (w : List Bool) : Bool := bFlag w && decide (rX w = bRec w)
+/-- The lazy decryption answer (`lazyDec`) of the query, from the table. -/
+private def bDecL (w : List Bool) : List Bool :=
+  if (!bRef w && bWF w) = true then
+    if decide (bLook w (bDKey w) = []) then []
+    else if decide ((pairSndD (bLook w (bDKey w))).take (tagLen.eval (rU w).length) =
+        pairSndD (pairSndD (rX w))) then
+      true :: (pairSndD (bLook w (bDKey w))).drop (tagLen.eval (rU w).length)
+    else []
+  else []
+/-- The decryption answer at `n + 1` bits. -/
+private def bDecAns (w : List Bool) : List Bool :=
+  EnsembleLemmas.padL ((PolyExpr.add .var (.const 1)).eval (rU w).length) (bDecL w)
+
+/-- **One round of the handler** (see the module docstring). A first round of `Enc′` or of a first
+challenge asks the CPA oracle; the second round, with the answer in the log, returns the answer and
+the new state. Decryption and a repeated challenge answer at once. -/
+private def bRun (w : List Bool) : List Bool :=
+  if (rI w).headD false then
+    if ((rI w).drop 1).headD false then
+      if bFlag w then
+        pairEncode [true] (EnsembleLemmas.padL (ettCt.eval (rU w).length) (bRec w) ++
+          bNew q w (bTbl w) (true :: bRec w))
+      else if decide (rL w = []) then pairEncode [false] (pairEncode [true, true] (rX w))
+      else pairEncode [true] (bCt w ++ bNew q w (bTbl w) (true :: bCt w))
+    else pairEncode [true] (bDecAns w ++ bNew q w (bTbl w) (bFlag w :: bRec w))
+  else
+    if decide (rL w = []) then pairEncode [false] (pairEncode [] (rX w))
+    else pairEncode [true] (bCt w ++
+      bNew q w (pairEncode (pairEncode (bKey w) (bTag w ++ rX w)) (bTbl w)) (bFlag w :: bRec w))
+
+/-- The round function is polynomial-time: `PolyTimeComputable (bRun q)`.
+
+**Proof sketch.** Every reader of `bRun` is assembled from the generic input readers (`rU`, `rW`,
+`rS`, `rI`, `rX`, `rL`, `rAns`) and pair projections: the record by `pairTakePoly`; the tape by
+`unaryMulPair`, `dropPrefixByLength` and `pairTakePoly`; the table lookup by `GGMRed.lookup_poly`;
+padding by `EnsembleLemmas.polyTimeComputable_padL`; word tests by `pairEq`, `isNil` and
+`lenEq_poly`. The branches for the three oracles are combined with `polyTimeComputable_ite`. -/
+private theorem polyTimeComputable_bRun : PolyTimeComputable (bRun q) := by
+  have hF := polyTimeComputable_pairFstD
+  have hD := polyTimeComputable_pairSndD
+  have hU : PolyTimeComputable rU := InteractiveHandler.polyTimeComputable_rU
+  have hW : PolyTimeComputable rW := InteractiveHandler.polyTimeComputable_rW
+  have hS : PolyTimeComputable rS := InteractiveHandler.polyTimeComputable_rS
+  have hI : PolyTimeComputable rI := InteractiveHandler.polyTimeComputable_rI
+  have hX : PolyTimeComputable rX := InteractiveHandler.polyTimeComputable_rX
+  have hL : PolyTimeComputable rL := InteractiveHandler.polyTimeComputable_rL
+  have hY : PolyTimeComputable rAns := InteractiveHandler.polyTimeComputable_rAns
+  have hTbl : PolyTimeComputable bTbl := hF.comp hS
+  have hJ : PolyTimeComputable bJ := (hF.comp hD).comp hS
+  have hT : PolyTimeComputable fun w => pairSndD (pairSndD (rS w)) := (hD.comp hD).comp hS
+  have hFlag : PolyTimeComputable fun w => [bFlag w] := polyTimeComputable_headD.comp hT
+  have hRec : PolyTimeComputable bRec :=
+    ((polyTimeComputable_pairTakePoly ettCt).comp
+      (hU.pairEncode (polyTimeComputable_tail.comp hT))).congr fun w => by
+        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]; rfl
+  have hPad2 : ∀ {v : List Bool → List Bool}, PolyTimeComputable v →
+      PolyTimeComputable fun w => bPad2 w (v w) := fun hv =>
+    EnsembleLemmas.polyTimeComputable_padL tagLen hU hv
+  have hOff : PolyTimeComputable fun w =>
+      List.replicate ((bJ w).length * tagLen.eval (rU w).length) true :=
+    (OneWay.polyTimeComputable_unaryMulPair.comp (hJ.pairEncode
+      ((polyTimeComputable_unaryPoly tagLen).comp hU))).congr fun w => by
+        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
+          List.length_replicate]
+  have hDrop : PolyTimeComputable fun w =>
+      (rW w).drop ((bJ w).length * tagLen.eval (rU w).length) :=
+    (polyTimeComputable_dropPrefixByLength.comp (hOff.pairEncode hW)).congr fun w => by
+      simp only [Function.comp_apply, PrefixByLength.drop_def, pairFstD_pairEncode,
+        pairSndD_pairEncode, List.length_replicate]
+  have hTape : PolyTimeComputable bTape :=
+    ((polyTimeComputable_pairTakePoly tagLen).comp (hU.pairEncode hDrop)).congr fun w => by
+      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]; rfl
+  have hKey : PolyTimeComputable bKey := hPad2 ((hF.comp hY).append (hD.comp hY))
+  have hLook : ∀ {k : List Bool → List Bool}, PolyTimeComputable k →
+      PolyTimeComputable fun w => bLook w (k w) := fun hk =>
+    GGMRed.lookup_poly.comp (hk.pairEncode hTbl)
+  have hEq : ∀ {u v : List Bool → List Bool}, PolyTimeComputable u → PolyTimeComputable v →
+      PolyTimeComputable fun w => [decide (u w = v w)] := fun hu hv =>
+    (polyTimeComputable_pairEq.comp (hu.pairEncode hv)).congr fun w => by
+      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
+  have hNil : ∀ {u : List Bool → List Bool}, PolyTimeComputable u →
+      PolyTimeComputable fun w => [decide (u w = [])] := fun hu => polyTimeComputable_isNil.comp hu
+  have hTake2 : ∀ {u : List Bool → List Bool}, PolyTimeComputable u →
+      PolyTimeComputable fun w => (u w).take (tagLen.eval (rU w).length) := fun hu =>
+    ((polyTimeComputable_pairTakePoly tagLen).comp (hU.pairEncode hu)).congr fun w => by
+      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
+  have hDrop2 : ∀ {u : List Bool → List Bool}, PolyTimeComputable u →
+      PolyTimeComputable fun w => (u w).drop (tagLen.eval (rU w).length) := fun hu =>
+    ((polyTimeComputable_pairDropPoly tagLen).comp (hU.pairEncode hu)).congr fun w => by
+      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
+  have hChalKey : PolyTimeComputable bChalKey :=
+    hPad2 ((hF.comp hRec).append ((hF.comp hD).comp hRec))
+  have hChalTag : PolyTimeComputable bChalTag := hPad2 ((hD.comp hD).comp hRec)
+  have hTag : PolyTimeComputable bTag :=
+    polyTimeComputable_ite (hNil (hLook hKey))
+      (polyTimeComputable_ite (polyTimeComputable_and hFlag (hEq hChalKey hKey)) hChalTag hTape)
+      (hTake2 (hD.comp (hLook hKey)))
+  have hCt : PolyTimeComputable bCt :=
+    EnsembleLemmas.polyTimeComputable_padL ettCt hU
+      ((hF.comp hY).pairEncode ((hD.comp hY).pairEncode hTag))
+  have hNew : ∀ {tb t : List Bool → List Bool}, PolyTimeComputable tb → PolyTimeComputable t →
+      PolyTimeComputable fun w => bNew q w (tb w) (t w) := fun htb ht =>
+    EnsembleLemmas.polyTimeComputable_padL (bStLen q) hU
+      (htb.pairEncode (((polyTimeComputable_const [true]).append hJ).pairEncode ht))
+  have hDKey : PolyTimeComputable bDKey := hPad2 ((hF.comp hX).append ((hF.comp hD).comp hX))
+  have hWF : PolyTimeComputable fun w => [bWF w] :=
+    polyTimeComputable_and (EffFill.lenEq_poly (hF.comp hX) hU)
+      (EffFill.lenEq_poly ((hF.comp hD).comp hX) hU)
+  have hRef : PolyTimeComputable fun w => [bRef w] := polyTimeComputable_and hFlag (hEq hX hRec)
+  have hDecL : PolyTimeComputable bDecL :=
+    polyTimeComputable_ite (polyTimeComputable_and (polyTimeComputable_not hRef) hWF)
+      (polyTimeComputable_ite (hNil (hLook hDKey)) (polyTimeComputable_const [])
+        (polyTimeComputable_ite (hEq (hTake2 (hD.comp (hLook hDKey))) ((hD.comp hD).comp hX))
+          ((polyTimeComputable_const [true]).append (hDrop2 (hD.comp (hLook hDKey))))
+          (polyTimeComputable_const [])))
+      (polyTimeComputable_const [])
+  have hDecAns : PolyTimeComputable bDecAns :=
+    EnsembleLemmas.polyTimeComputable_padL (.add .var (.const 1)) hU hDecL
+  have hRet : ∀ {f : List Bool → List Bool}, PolyTimeComputable f →
+      PolyTimeComputable fun w => pairEncode [true] (f w) := fun hf =>
+    (polyTimeComputable_const [true]).pairEncode hf
+  have hKeep : PolyTimeComputable fun w => bFlag w :: bRec w :=
+    (hFlag.append hRec).congr fun _ => rfl
+  have cNil : PolyTimeComputable fun w => [decide (rL w = [])] := polyTimeComputable_isNil.comp hL
+  have hChal := polyTimeComputable_ite hFlag
+    (hRet ((EnsembleLemmas.polyTimeComputable_padL ettCt hU hRec).append
+      (hNew hTbl ((polyTimeComputable_const [true]).append hRec))))
+    (polyTimeComputable_ite cNil
+      ((polyTimeComputable_const [false]).pairEncode
+        ((polyTimeComputable_const [true, true]).pairEncode hX))
+      (hRet (hCt.append (hNew hTbl ((polyTimeComputable_const [true]).append hCt)))))
+  have hDec := hRet (hDecAns.append (hNew hTbl hKeep))
+  have hEnc := polyTimeComputable_ite cNil
+    ((polyTimeComputable_const [false]).pairEncode ((polyTimeComputable_const []).pairEncode hX))
+    (hRet (hCt.append (hNew ((hKey.pairEncode (hTag.append hX)).pairEncode hTbl) hKeep)))
+  exact polyTimeComputable_ite (polyTimeComputable_headD.comp hI)
+    (polyTimeComputable_ite (polyTimeComputable_headD.comp (polyTimeComputable_tail.comp hI))
+      hChal hDec) hEnc
+
+/-- The finalization's round: output `A`'s bit. -/
+private def bFin (w : List Bool) : List Bool := pairEncode [true] (pairFstD (pairSndD (pairSndD w)))
+
+/-- The finalization's round is polynomial-time. -/
+private theorem polyTimeComputable_bFin : PolyTimeComputable bFin :=
+  (polyTimeComputable_const [true]).pairEncode
+    (polyTimeComputable_pairFstD.comp
+      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
+
+/-! ### The handler -/
+
+/-- **The handler of the CPA reduction** for the budget `q`: state `bState` (initially the empty
+table, count `0`, no record), seed `q(n)` tag tapes, one outer call per inner query, the adversary
+run on the empty input, and the finalization outputting the adversary's bit:
+`stateLen = bStLen q`, `seedLen = bSeedLen q`, `init n = bState q n 0 [] none`, `run = bRun q`,
+`perCall = 1`, `advIn _ = []`, `outLen = 1`, `finCall = 0` and `finRun = bFin`. -/
+noncomputable def bHandler : InteractiveHandler 3 ettDin ettDout 3 pkDin pkDout where
+  stateLen := bStLen q
+  seedLen := bSeedLen q
+  perCall := .const 1
+  init n := bState q n 0 [] none
+  run := bRun q
+  poly := polyTimeComputable_bRun q
+  advIn _ := []
+  advIn_poly := polyTimeComputable_const []
+  outLen := .const 1
+  finCall := .const 0
+  finRun := bFin
+  finRun_poly := polyTimeComputable_bFin
+
+attribute [simps (config := { isSimp := false }) stateLen seedLen perCall outLen finCall] bHandler
+
+/-- The encoded state at the handler's state type: `bHState q n j L o = bState q n j L o`. -/
+def bHState (n j : ℕ) (L : List (LEntry n)) (o : Option (Fin (ettCt.eval n) → Bool)) :
+    Fin ((bHandler q).stateLen.eval n) → Bool :=
+  bState q n j L o
+
+/-- `bHState q n j L o = bState q n j L o`. -/
+theorem bHState_eq (n j : ℕ) (L : List (LEntry n)) (o : Option (Fin (ettCt.eval n) → Bool)) :
+    bHState q n j L o = bState q n j L o := rfl
+
+/-- `⟦bHState q n j L o⟧ = ⟦bState q n j L o⟧`. -/
+theorem ofFn_bHState (n j : ℕ) (L : List (LEntry n)) (o : Option (Fin (ettCt.eval n) → Bool)) :
+    List.ofFn (bHState q n j L o) = List.ofFn (bState q n j L o) := rfl
+
+/-- The seed at the handler's seed type: `bHSeed q n = bSeed q n`. -/
+def bHSeed (n : ℕ) :
+    (Fin (q.eval n * (2 * n)) → Bool) ≃ (Fin ((bHandler q).seedLen.eval n) → Bool) :=
+  bSeed q n
+
+/-- `bHSeed q n = bSeed q n`. -/
+theorem bHSeed_eq (n : ℕ) : bHSeed q n = bSeed q n := rfl
+
+/-- `⟦bHSeed q n W⟧ = ⟦W⟧`. -/
+theorem ofFn_bHSeed (n : ℕ) (W : Fin (q.eval n * (2 * n)) → Bool) :
+    List.ofFn (bHSeed q n W) = List.ofFn W :=
+  ofFn_bSeed q n W
+
+/-- The initial state is the empty table, count `0` and no record:
+`(bHandler q).init n = bHState q n 0 [] none`. -/
+theorem bHandler_init_hstate (n : ℕ) : (bHandler q).init n = bHState q n 0 [] none := rfl
+
+/-- The adversary's input is empty: `(bHandler q).advInput n z ω = []`. -/
+theorem bHandler_advInput (n : ℕ) (z : List Bool)
+    (ω : Fin ((bHandler q).seedLen.eval n) → Bool) : (bHandler q).advInput n z ω = [] := by
+  rw [InteractiveHandler.advInput_eq]
+  rfl
+
+/-- The finalization outputs the adversary's bit and asks nothing:
+`(bHandler q).finish n z ω s a = pure (padFin _ ⟦a⟧)`. -/
+theorem bHandler_finish (n : ℕ) (z : List Bool) (ω : Fin ((bHandler q).seedLen.eval n) → Bool)
+    (s : Fin ((bHandler q).stateLen.eval n) → Bool) (a : Fin ((PolyExpr.const 1).eval n) → Bool) :
+    (bHandler q).finish n z ω s a =
+      .pure (padFin ((bHandler q).outLen.eval n) (List.ofFn a)) := by
+  rw [InteractiveHandler.finish_eq]
+  have h0 : (bHandler q).finCall.eval n = 0 := by rw [bHandler_finCall, PolyExpr.eval_const]
+  rw [h0]
+  refine buildComp_zero_of_ret ?_
+  show decodeBitMove _ _ _ (bFin _) = _
+  rw [bFin, InteractiveHandler.finInput_eq, pairSndD_pairEncode, pairSndD_pairEncode,
+    pairFstD_pairEncode]
+  have hw : List.ofFn (padFin ((bHandler q).outLen.eval n) (List.ofFn a)) = List.ofFn a :=
+    ofFn_padFin_of_length (by rw [List.length_ofFn, bHandler_outLen])
+  exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).symm.trans
+    (decodeBitMove_ret _ _ _ _)
+
+/-! ### Answers of the handler -/
+
+/-- The pair of an outer answer `y = ⟨r, c₁⟩`, read at `2n` bits:
+`bKeyOf n y = padFin (2n) (pairFstD ⟦y⟧ ++ pairSndD ⟦y⟧)`. -/
+def bKeyOf (n : ℕ) {m : ℕ} (y : Fin m → Bool) : Fin (2 * n) → Bool :=
+  padFin (2 * n) (pairFstD (List.ofFn y) ++ pairSndD (List.ofFn y))
+
+/-- `bKeyOf n y = padFin (2n) (pairFstD ⟦y⟧ ++ pairSndD ⟦y⟧)`. -/
+theorem bKeyOf_eq (n : ℕ) {m : ℕ} (y : Fin m → Bool) :
+    bKeyOf n y = padFin (2 * n) (pairFstD (List.ofFn y) ++ pairSndD (List.ofFn y)) := rfl
+
+section Answers
+
+variable (n : ℕ) (z : List Bool) (W : Fin (q.eval n * (2 * n)) → Bool)
+
+/-- The round input of a call, field by field, on an encoded state that fits, with `j < q(n)`
+and the seed `bHSeed W`. -/
+private theorem fields_input {i : Fin 3} (x Lg : List Bool) (j : ℕ) (L : List (LEntry n))
+    (o : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n) (hL : L.length ≤ q.eval n)
+    (hm : ∀ e ∈ L, e.2.2.length = n) :
+    let w := InteractiveHandler.input n z (List.ofFn (bHSeed q n W))
+      (List.ofFn (bHState q n j L o)) i x Lg
+    rU w = List.replicate n true ∧ rI w = List.replicate i true ∧ rX w = x ∧ rL w = Lg ∧
+      bTbl w = tblW L ∧ bJ w = List.replicate j true ∧ bFlag w = o.isSome ∧
+      bRec w = (recBits n o).drop 1 ∧ bTape w = List.ofFn (bTapeOf q n W j hj) := by
+  obtain ⟨h₁, h₂, h₃, h₄⟩ := fields_bState q n j L o hj.le hL hm
+  have hS : rS (InteractiveHandler.input n z (List.ofFn (bHSeed q n W))
+      (List.ofFn (bHState q n j L o)) i x Lg) = List.ofFn (bState q n j L o) :=
+    (InteractiveHandler.rS_input ..).trans (ofFn_bHState q n j L o)
+  have hU := InteractiveHandler.rU_input (k := 3) n z (List.ofFn (bHSeed q n W))
+    (List.ofFn (bHState q n j L o)) i x Lg
+  have hJ : bJ (InteractiveHandler.input n z (List.ofFn (bHSeed q n W))
+      (List.ofFn (bHState q n j L o)) i x Lg) = List.replicate j true := by rw [bJ, hS, h₂]
+  refine ⟨hU, InteractiveHandler.rI_input .., InteractiveHandler.rX_input ..,
+    InteractiveHandler.rL_input .., by rw [bTbl, hS, h₁], hJ, by rw [bFlag, hS, h₃],
+    by rw [bRec, hS, hU, List.length_replicate, h₄], ?_⟩
+  rw [bTape, hJ, hU, InteractiveHandler.rW_input, ofFn_bHSeed, List.length_replicate,
+    List.length_replicate, tagLen_eval, bTapeOf_eq]
+  exact EnsembleLemmas.take_drop_ofFn_blocks W j hj
+
+/-- The outer answer recorded in a one-entry log. -/
+private theorem rAns_one (w : List Bool) (u x' y : List Bool)
+    (hL : rL w = pairEncode (pairEncode u (pairEncode x' y)) []) : rAns w = y := by
+  rw [InteractiveHandler.rAns_eq, hL, pairFstD_pairEncode, pairSndD_pairEncode,
+    pairSndD_pairEncode]
+
+/-- A one-entry log is not empty. -/
+private theorem log_ne_nil (u x' y : List Bool) :
+    decide (pairEncode (pairEncode u (pairEncode x' y)) [] = []) = false :=
+  decide_eq_false (pairEncode_ne_nil _ _)
+
+/-- A word read at `2n` bits is a `2n`-bit word. -/
+private theorem bPad2_fields (w v : List Bool) (hU : rU w = List.replicate n true) :
+    bPad2 w v = List.ofFn (padFin (2 * n) v) := by
+  rw [bPad2, hU, List.length_replicate, tagLen_eval, EnsembleLemmas.ofFn_padFin_eq_padL]
+
+/-- The new state with table word `tblW L'`, count `j + 1` and record `recBits o'`. -/
+private theorem bNew_fields (w : List Bool) (j : ℕ) (L' : List (LEntry n))
+    (o' : Option (Fin (ettCt.eval n) → Bool)) (hU : rU w = List.replicate n true)
+    (hJ : bJ w = List.replicate j true) :
+    bNew q w (tblW L') (recBits n o') = List.ofFn (bHState q n (j + 1) L' o') := by
+  rw [bNew, hU, hJ, List.length_replicate, ofFn_bHState, bState_eq,
+    EnsembleLemmas.ofFn_padFin_eq_padL, List.replicate_succ]
+
+/-- **The tag of a pair `p`:** the table's, else the record's, else the tape `t`.
+
+**Proof sketch.** The lookup on the table word is `lookL L p` (`lookup_tblW`). On an entry `e`
+the lookup is nonempty and its first `2n` bits are `⟦e.2.1⟧`. Without an entry, by cases on `o`:
+with no record the flag is false and the tape is taken; with the record `c`, its pair and tag
+read at `2n` bits are `pairW n ⟦c⟧` and `padFin (2n) (wT ⟦c⟧)` (`bPad2_fields`), and the test
+`pairW n ⟦c⟧ = p` selects the record's tag or the tape, as `tagOf` does. -/
+private theorem bTag_fields (w : List Bool) (L : List (LEntry n))
+    (o : Option (Fin (ettCt.eval n) → Bool)) (p t : Fin (2 * n) → Bool)
+    (hU : rU w = List.replicate n true) (hT : bTbl w = tblW L) (hF : bFlag w = o.isSome)
+    (hR : bRec w = (recBits n o).drop 1) (hTp : bTape w = List.ofFn t)
+    (hK : bKey w = List.ofFn p) :
+    bTag w = List.ofFn ((tagOf ((o, L) : LSt n (ettCt.eval n)) p).getD t) := by
+  rw [bTag, bLook, hK, hT, lookup_tblW, tagOf_eq]
+  cases h : lookL L p with
+  | some e =>
+    simp only [decide_eq_false (pairEncode_ne_nil _ _), Bool.false_eq_true, if_false,
+      pairSndD_pairEncode, Option.getD_some]
+    rw [hU, List.length_replicate, tagLen_eval, List.take_left' (by rw [List.length_ofFn])]
+  | none =>
+    simp only [decide_true, if_true]
+    cases o with
+    | none => simp only [hF, Option.isSome_none, Bool.false_and, Bool.false_eq_true, if_false,
+        hTp, Option.getD_none]
+    | some c =>
+      have hRc : bRec w = List.ofFn c := by
+        rw [hR, recBits_some, List.drop_succ_cons, List.drop_zero]
+      have hCK : bChalKey w = List.ofFn (pairW n (List.ofFn c)) := by
+        rw [bChalKey, hRc, bPad2_fields n w _ hU, pairW_eq, pairV_eq, wR_eq, wC_eq]
+      have hCT : bChalTag w = List.ofFn (padFin (2 * n) (wT (List.ofFn c))) := by
+        rw [bChalTag, hRc, bPad2_fields n w _ hU, wT_eq]
+      simp only [hF, Option.isSome_some, Bool.true_and, hCK, List.ofFn_inj]
+      by_cases hc : pairW n (List.ofFn c) = p
+      · simp only [hc, decide_true, if_true, hCT, Option.getD_some]
+      · simp only [hc, decide_false, Bool.false_eq_true, if_false, hTp, Option.getD_none]
+
+/-- **The lazy decryption answer of the query `⟦x⟧`:** `bDecL w = lazyDec (o, L) ⟦x⟧`.
+
+**Proof sketch.** The handler's tests are the lazy ones: `bRef w = refW o x` (by cases on `o`,
+reading the record `c` from `recBits`), `bWF w = wfW n x`, and the decryption key read at `2n`
+bits is `pairW n x` (`bPad2_fields`). The lookup on the table word is `lookL L (pairW n x)`
+(`lookup_tblW`); on an entry `e` its first `2n` bits are `⟦e.2.1⟧` and the rest is `e.2.2`, so the
+tag test and the answer `true :: e.2.2` are those of `lazyDec`. -/
+private theorem bDecL_fields (w x : List Bool) (L : List (LEntry n))
+    (o : Option (Fin (ettCt.eval n) → Bool))
+    (hU : rU w = List.replicate n true) (hX : rX w = x) (hT : bTbl w = tblW L)
+    (hF : bFlag w = o.isSome) (hR : bRec w = (recBits n o).drop 1) :
+    bDecL w = lazyDec ((o, L) : LSt n (ettCt.eval n)) x := by
+  have hRef : bRef w = refW o x := by
+    rw [bRef, hF, hR, hX]
+    cases o with
+    | none => rw [Option.isSome_none, Bool.false_and, refW_none]
+    | some c =>
+      rw [recBits_some, List.drop_succ_cons, List.drop_zero, Option.isSome_some, Bool.true_and,
+        refW_some]
+      exact decide_eq_decide.2 eq_comm
+  have hWF : bWF w = wfW n x := by
+    rw [bWF, hU, hX, List.length_replicate, wfW_eq, wR_eq, wC_eq]
+  have hDK : bDKey w = List.ofFn (pairW n x) := by
+    rw [bDKey, hX, bPad2_fields n w _ hU, pairW_eq, pairV_eq, wR_eq, wC_eq]
+  rw [bDecL, lazyDec_eq, hRef, hWF]
+  simp only
+  by_cases hc : (!refW o x && wfW n x) = true
+  · rw [if_pos hc, if_pos hc, bLook, hDK, hT, lookup_tblW]
+    cases h : lookL L (pairW n x) with
+    | none => simp only [decide_true, if_true]
+    | some e =>
+      simp only [decide_eq_false (pairEncode_ne_nil _ _), Bool.false_eq_true, if_false,
+        pairSndD_pairEncode]
+      rw [hU, List.length_replicate, tagLen_eval, List.take_left' (by rw [List.length_ofFn]),
+        List.drop_left' (by rw [List.length_ofFn]), hX, wT_eq]
+      by_cases ht : List.ofFn e.2.1 = pairSndD (pairSndD x)
+      · rw [if_pos (decide_eq_true ht), if_pos ht]
+      · rw [if_neg (by rw [decide_eq_true_eq]; exact ht), if_neg ht]
+  · rw [if_neg hc, if_neg hc]
+
+/-- The flag and the record rebuild the record bits:
+`o.isSome :: (recBits o).drop 1 = recBits o`. -/
+private theorem recBits_fields (o : Option (Fin (ettCt.eval n) → Bool)) :
+    o.isSome :: (recBits n o).drop 1 = recBits n o := by
+  cases o with
+  | none => rw [recBits_none, List.drop_succ_cons, List.drop_zero, Option.isSome_none]
+  | some c => rw [recBits_some, List.drop_succ_cons, List.drop_zero, Option.isSome_some]
+
+/-- The inner query word read at the outer length: `⟦padFin _ ⟦x⟧⟧ = ⟦x⟧` for an `n`-bit `x`. -/
+private theorem ofFn_padFin_msg {m : ℕ} (x : Fin m → Bool) (hm : m = n) :
+    List.ofFn (padFin ((pkDin 0).eval n) (List.ofFn x)) = List.ofFn x :=
+  ofFn_padFin_of_length (by rw [List.length_ofFn, PRFGame.pkDin_zero, PolyExpr.eval_var, hm])
+
+/-- **Encryption:** from `bState j L o` with `j < q(n)`, the query `m = ⟦x⟧` asks the CPA
+encryption oracle at `m`; its answer `y` gives the ciphertext `⟨pairFstD y, ⟨pairSndD y, t⟩⟩`
+with the tag `t` of the pair `bKeyOf n y` (`tagOf`, else the tape `j`), and the state
+`bState (j + 1) ((bKeyOf n y, t, m) :: L) o`.
+
+**Proof sketch.** Read the round input field by field (`fields_input`); the first round, with an
+empty log, asks `m`; the second, with the answer in the log (`rAns_one`), computes the tag
+(`bTag_fields`, from `lookup_tblW`), the ciphertext and the new state (`bNew_fields`, `tblW_cons`);
+`InteractiveHandler.impl_of_query` assembles the two rounds. -/
+theorem bHandler_impl_enc (x : Fin ((ettDin 0).eval n) → Bool) (j : ℕ) (L : List (LEntry n))
+    (o : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n) (hL : L.length ≤ q.eval n)
+    (hm : ∀ e ∈ L, e.2.2.length = n) :
+    (bHandler q).impl n z (bHSeed q n W) 0 x (bHState q n j L o) =
+      .query 0 (padFin _ (List.ofFn x)) fun y =>
+        .pure (padFin _ (ctW (pairFstD (List.ofFn y)) (pairSndD (List.ofFn y))
+            (List.ofFn ((tagOf ((o, L) : LSt n (ettCt.eval n)) (bKeyOf n y)).getD
+              (bTapeOf q n W j hj)))),
+          bHState q n (j + 1) ((bKeyOf n y, (tagOf ((o, L) : LSt n (ettCt.eval n))
+            (bKeyOf n y)).getD (bTapeOf q n W j hj), List.ofFn x) :: L) o) := by
+  have hx := ofFn_padFin_msg n x (by rw [ettDin_zero, PolyExpr.eval_var])
+  refine InteractiveHandler.impl_of_query _ n z _ x _ 0 _ _ _
+    (by rw [bHandler_perCall, PolyExpr.eval_const]) ?_ ?_
+  · show bRun q _ = _
+    obtain ⟨-, hI, hX, hL', -⟩ := fields_input q n z W (i := 0) (List.ofFn x) [] j L o hj hL hm
+    rw [bRun, hI, Fin.val_zero, List.replicate_zero, List.headD_nil, if_neg Bool.false_ne_true,
+      hL', if_pos (decide_eq_true rfl), hX, hx]
+  · intro y
+    show bRun q _ = _
+    simp only [Fin.val_zero, List.replicate_zero]
+    obtain ⟨hU, hI, hX, hL', hT, hJ, hF, hR, hTp⟩ := fields_input q n z W (i := 0) (List.ofFn x)
+      (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((pkDin 0).eval n)
+        (List.ofFn x))) (List.ofFn y))) []) j L o hj hL hm
+    have hY := rAns_one _ _ _ _ hL'
+    have hK : bKey (InteractiveHandler.input n z (List.ofFn (bHSeed q n W))
+        (List.ofFn (bHState q n j L o)) (0 : Fin 3) (List.ofFn x)
+        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((pkDin 0).eval n)
+          (List.ofFn x))) (List.ofFn y))) [])) = List.ofFn (bKeyOf n y) := by
+      rw [bKey, hY, bPad2_fields n _ _ hU, bKeyOf_eq]
+    have hTag := bTag_fields n _ L o (bKeyOf n y) (bTapeOf q n W j hj) hU hT hF hR hTp hK
+    rw [bRun, hI, Fin.val_zero, List.replicate_zero, List.headD_nil, if_neg Bool.false_ne_true,
+      hL', log_ne_nil, if_neg Bool.false_ne_true, bCt, hY, hTag, hU, List.length_replicate, hK,
+      hX, hT, hF, hR, recBits_fields,
+      ← tblW_cons (bKeyOf n y, (tagOf ((o, L) : LSt n (ettCt.eval n))
+        (bKeyOf n y)).getD (bTapeOf q n W j hj), List.ofFn x) L,
+      bNew_fields q n _ j _ o hU hJ, ← ctW_eq]
+    rw [EnsembleLemmas.ofFn_padFin_eq_padL, ettDout_zero]
+
+/-- **Decryption:** from `bState j L o` with `j < q(n)`, the query `⟦x⟧` is answered by
+`lazyDec (o, L) ⟦x⟧` without an outer query, and the state is `bState (j + 1) L o`
+(`bDecL_fields`). -/
+theorem bHandler_impl_dec (x : Fin ((ettDin 1).eval n) → Bool) (j : ℕ) (L : List (LEntry n))
+    (o : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n) (hL : L.length ≤ q.eval n)
+    (hm : ∀ e ∈ L, e.2.2.length = n) :
+    (bHandler q).impl n z (bHSeed q n W) 1 x (bHState q n j L o) =
+      .pure (padFin _ (lazyDec ((o, L) : LSt n (ettCt.eval n)) (List.ofFn x)),
+        bHState q n (j + 1) L o) := by
+  refine InteractiveHandler.impl_of_ret _ n z _ x _ _ _ ?_
+  show bRun q _ = _
+  obtain ⟨hU, hI, hX, -, hT, hJ, hF, hR, -⟩ :=
+    fields_input q n z W (i := 1) (List.ofFn x) [] j L o hj hL hm
+  rw [bRun, hI, Fin.val_one, List.replicate_one, List.headD_cons, if_pos rfl, List.drop_succ_cons,
+    List.drop_zero, List.headD_nil, if_neg Bool.false_ne_true, bDecAns,
+    bDecL_fields n _ _ L o hU hX hT hF hR, hU, List.length_replicate, hT, hF, hR, recBits_fields,
+    bNew_fields q n _ j L o hU hJ]
+  beta_reduce
+  rw [EnsembleLemmas.ofFn_padFin_eq_padL, ettDout_one]
+
+/-- **A recorded challenge is repeated:** from `bState j L (some c)`, a challenge is answered `c`
+and the state is `bState (j + 1) L (some c)`: for `j < q(n)`, `|L| ≤ q(n)` and `n`-bit messages
+in `L`, `(bHandler q).impl n z (bHSeed q n W) 2 x (bHState q n j L (some c)) =
+pure (padFin _ ⟦c⟧, bHState q n (j + 1) L (some c))`. -/
+theorem bHandler_impl_challenge_some (x : Fin ((ettDin 2).eval n) → Bool) (j : ℕ)
+    (L : List (LEntry n)) (c : Fin (ettCt.eval n) → Bool) (hj : j < q.eval n)
+    (hL : L.length ≤ q.eval n) (hm : ∀ e ∈ L, e.2.2.length = n) :
+    (bHandler q).impl n z (bHSeed q n W) 2 x (bHState q n j L (some c)) =
+      .pure (padFin _ (List.ofFn c), bHState q n (j + 1) L (some c)) := by
+  refine InteractiveHandler.impl_of_ret _ n z _ x _ _ _ ?_
+  show bRun q _ = _
+  obtain ⟨hU, hI, -, -, hT, hJ, hF, hR, -⟩ :=
+    fields_input q n z W (i := 2) (List.ofFn x) [] j L (some c) hj hL hm
+  have hRc : (recBits n (some c)).drop 1 = List.ofFn c := by
+    rw [recBits_some, List.drop_succ_cons, List.drop_zero]
+  have hrec : true :: List.ofFn c = recBits n (some c) := (recBits_some n c).symm
+  rw [bRun, hI, hF, hR, hRc]
+  simp only [show List.replicate ((2 : Fin 3) : ℕ) true = [true, true] from rfl, List.headD_cons,
+    List.drop_succ_cons, List.drop_zero, if_true, Option.isSome_some]
+  rw [hT, hrec, bNew_fields q n _ j L (some c) hU hJ, hU, List.length_replicate]
+  rw [EnsembleLemmas.ofFn_padFin_eq_padL, ettDout_two]
+
+/-- **The first challenge:** from `bState j L none` with `j < q(n)`, the challenge `⟦x⟧` asks the
+CPA challenge oracle at `⟦x⟧`; its answer `y` gives the ciphertext
+`c = ⟨pairFstD y, ⟨pairSndD y, t⟩⟩` with the tag `t` of `bKeyOf n y` (`tagOf (none, L)`, else the
+tape `j`), recorded in the state `bState (j + 1) L (some c)`.
+
+**Proof sketch.** As for `bHandler_impl_enc`: read the round input field by field
+(`fields_input`); the first round, with no record (flag false) and an empty log, asks the CPA
+challenge oracle (oracle `2`) at `⟦x⟧`; the second, with the answer `y` in the log (`rAns_one`),
+takes the tag of `bKeyOf n y` (`bTag_fields` with no record), returns the ciphertext `c`, and
+writes the record bits `true :: ⟦c⟧ = recBits n (some c)` with the table unchanged
+(`bNew_fields`); `InteractiveHandler.impl_of_query` assembles the two rounds. -/
+theorem bHandler_impl_challenge_none (x : Fin ((ettDin 2).eval n) → Bool) (j : ℕ)
+    (L : List (LEntry n)) (hj : j < q.eval n) (hL : L.length ≤ q.eval n)
+    (hm : ∀ e ∈ L, e.2.2.length = n) :
+    (bHandler q).impl n z (bHSeed q n W) 2 x (bHState q n j L none) =
+      .query 2 (padFin _ (List.ofFn x)) fun y =>
+        .pure (padFin _ (ctW (pairFstD (List.ofFn y)) (pairSndD (List.ofFn y))
+            (List.ofFn ((tagOf ((none, L) : LSt n (ettCt.eval n)) (bKeyOf n y)).getD
+              (bTapeOf q n W j hj)))),
+          bHState q n (j + 1) L (some (padFin (ettCt.eval n) (ctW (pairFstD (List.ofFn y))
+            (pairSndD (List.ofFn y)) (List.ofFn ((tagOf ((none, L) : LSt n (ettCt.eval n))
+              (bKeyOf n y)).getD (bTapeOf q n W j hj))))))) := by
+  have hx : List.ofFn (padFin ((pkDin 2).eval n) (List.ofFn x)) = List.ofFn x :=
+    ofFn_padFin_of_length (by rw [List.length_ofFn, PRFGame.pkDin_two, ettDin_two])
+  refine InteractiveHandler.impl_of_query _ n z _ x _ 2 _ _ _
+    (by rw [bHandler_perCall, PolyExpr.eval_const]) ?_ ?_
+  · show bRun q _ = _
+    obtain ⟨-, hI, hX, hL', -, -, hF, -⟩ :=
+      fields_input q n z W (i := 2) (List.ofFn x) [] j L none hj hL hm
+    rw [bRun, hI, hF, hL']
+    simp only [show List.replicate ((2 : Fin 3) : ℕ) true = [true, true] from rfl, List.headD_cons,
+      List.drop_succ_cons, List.drop_zero, if_true, Option.isSome_none, Bool.false_eq_true,
+      if_false, decide_true]
+    rw [hX, hx]
+  · intro y
+    show bRun q _ = _
+    simp only [show List.replicate ((2 : Fin 3) : ℕ) true = [true, true] from rfl]
+    obtain ⟨hU, hI, hX, hL', hT, hJ, hF, hR, hTp⟩ := fields_input q n z W (i := 2) (List.ofFn x)
+      (pairEncode (pairEncode [true, true]
+        (pairEncode (List.ofFn (padFin ((pkDin 2).eval n) (List.ofFn x))) (List.ofFn y))) [])
+      j L none hj hL hm
+    have hY := rAns_one _ _ _ _ hL'
+    have hK : bKey (InteractiveHandler.input n z (List.ofFn (bHSeed q n W))
+        (List.ofFn (bHState q n j L none)) (2 : Fin 3) (List.ofFn x)
+        (pairEncode (pairEncode [true, true]
+          (pairEncode (List.ofFn (padFin ((pkDin 2).eval n) (List.ofFn x))) (List.ofFn y))) [])) =
+        List.ofFn (bKeyOf n y) := by
+      rw [bKey, hY, bPad2_fields n _ _ hU, bKeyOf_eq]
+    have hTag := bTag_fields n _ L none (bKeyOf n y) (bTapeOf q n W j hj) hU hT hF hR hTp hK
+    have hrec : true :: bCt (InteractiveHandler.input n z (List.ofFn (bHSeed q n W))
+        (List.ofFn (bHState q n j L none)) (2 : Fin 3) (List.ofFn x)
+        (pairEncode (pairEncode [true, true]
+          (pairEncode (List.ofFn (padFin ((pkDin 2).eval n) (List.ofFn x))) (List.ofFn y))) [])) =
+        recBits n (some (padFin (ettCt.eval n) (ctW (pairFstD (List.ofFn y))
+            (pairSndD (List.ofFn y)) (List.ofFn ((tagOf ((none, L) : LSt n (ettCt.eval n))
+              (bKeyOf n y)).getD (bTapeOf q n W j hj)))))) := by
+      rw [recBits_some, bCt, hY, hTag, hU, List.length_replicate, ← ctW_eq,
+        EnsembleLemmas.ofFn_padFin_eq_padL]
+    rw [bRun, hI, hF, hL']
+    simp only [show List.replicate ((2 : Fin 3) : ℕ) true = [true, true] from rfl, List.headD_cons,
+      List.drop_succ_cons, List.drop_zero, if_true, Option.isSome_none, Bool.false_eq_true,
+      if_false]
+    rw [log_ne_nil, if_neg Bool.false_ne_true, hrec, hT, bNew_fields q n _ j L _ hU hJ, bCt, hY,
+      hTag, hU, List.length_replicate, ← ctW_eq]
+    rw [EnsembleLemmas.ofFn_padFin_eq_padL, ettDout_two]
+
+end Answers
+
+end TCSlib.Cryptography.Composability.ETTGame
diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/CPAReduction.lean b/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/CPAReduction.lean
new file mode 100644
index 000000000..ed69f35b4
--- /dev/null
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/CPAReduction.lean
@@ -0,0 +1,370 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.CPAHandler
+import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Reduction
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The CPA reduction for the encrypt-then-tag scheme
+
+Step 3 of [PS10, Theorem 170.4]: the experiment that rejects fresh decryption queries, with a
+uniform random tag function, is the CPA experiment of the §3.9 scheme against a machine adversary
+`B` (`exists_cpaStep`). `B` is T2 (`Games.exists_interactiveHandlerMachine`) applied to the handler
+`bHandler` (through the input-free companion `Games.exists_toCompOn_of_toComp`), run on the empty
+input (`NUPPT.exists_comp`).
+
+The proof composes the handler with the CPA oracles `PRFGame.fImpl` (`QueryImpl.comp`). Each
+composed call, from the encoded state `bState j L o` and the CPA record of `o`, has the law of the
+call of the lazy experiment with the tapes in advance (`ettLazyTape`) from `((o, L), j)`
+(`comp_bAbs`), as long as `j` is below the number `q(n)` of tapes and the table has at most `j`
+entries of `n`-bit messages (`bInv`, kept by every call, `ettLazyTape_bInv`); the adversary asks
+at most `q(n)` queries, so this holds along every run (`expect_simulate_abs_inv`). Drawing the
+seed uniformly gives fresh tapes (`expect_ettLazyTape`), and the lazy experiment is the rejecting
+experiment with a uniform random tag function (`expect_ettImpl_lazy`).
+
+## Main definitions
+
+* `ETTGame.cpaRec`: the CPA record `⟨r, c₁⟩` of a CCA2 record `⟨r, ⟨c₁, t⟩⟩`.
+* `ETTGame.bAbs`, `bInv`, `bTapes`: the abstraction, the invariant and the tapes.
+
+## Main results
+
+* `ETTGame.comp_bAbs`: one composed call has the law of a call of `ettLazyTape`.
+* `ETTGame.ettLazyTape_bInv`: the calls of `ettLazyTape` keep the invariant.
+* `ETTGame.exists_cpaStep`: step 3, the rejecting experiment with a random tag function is a CPA
+  experiment of the §3.9 scheme.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 170.4 (book pp. 170–171).
+-/
+
+namespace TCSlib.Cryptography.Composability.ETTGame
+
+open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp
+open TCSlib.Cryptography.Composability.PRFGame (pkDin pkDout ctP fImpl atkOf qRed ctOf)
+
+/-! ### The abstraction -/
+
+/-- **The CPA record** of a CCA2 record `c = ⟨r, ⟨c₁, t⟩⟩`: the pair `⟨r, c₁⟩` at `3n + 2` bits. -/
+def cpaRec (n : ℕ) (c : Fin (ettCt.eval n) → Bool) : Fin (ctP.eval n) → Bool :=
+  padFin _ (pairEncode (wR (List.ofFn c)) (wC (List.ofFn c)))
+
+/-- `cpaRec n c = padFin _ ⟨wR ⟦c⟧, wC ⟦c⟧⟩`. -/
+theorem cpaRec_eq (n : ℕ) (c : Fin (ettCt.eval n) → Bool) :
+    cpaRec n c = padFin _ (pairEncode (wR (List.ofFn c)) (wC (List.ofFn c))) := rfl
+
+/-- **The abstraction:** the handler's state `bState j L o` and the CPA record of `o`, as functions
+of the lazy experiment's state `(o, L)` with the counter `j`,
+`bAbs q n ((o, L), j) = (bHState q n j L o, o.map (cpaRec n))`. -/
+def bAbs (q : PolyExpr) (n : ℕ) (s : LSt n (ettCt.eval n) × ℕ) :
+    (Fin ((bHandler q).stateLen.eval n) → Bool) × Option (Fin (ctP.eval n) → Bool) :=
+  (bHState q n s.2 s.1.2 s.1.1, s.1.1.map (cpaRec n))
+
+/-- `bAbs q n ((o, L), j) = (bHState q n j L o, o.map (cpaRec n))`. -/
+theorem bAbs_eq (q : PolyExpr) (n : ℕ) (s : LSt n (ettCt.eval n) × ℕ) :
+    bAbs q n s = (bHState q n s.2 s.1.2 s.1.1, s.1.1.map (cpaRec n)) := rfl
+
+/-- **The invariant:** the table has at most one entry per query, each with an `n`-bit message,
+`bInv n ((o, L), j) ↔ |L| ≤ j ∧ ∀ e ∈ L, |e.2.2| = n`. -/
+def bInv (n : ℕ) (s : LSt n (ettCt.eval n) × ℕ) : Prop :=
+  s.1.2.length ≤ s.2 ∧ ∀ e ∈ s.1.2, e.2.2.length = n
+
+/-- `bInv n ((o, L), j) ↔ |L| ≤ j ∧ every message of `L` has `n` bits`. -/
+theorem bInv_iff (n : ℕ) (s : LSt n (ettCt.eval n) × ℕ) :
+    bInv n s ↔ s.1.2.length ≤ s.2 ∧ ∀ e ∈ s.1.2, e.2.2.length = n := Iff.rfl
+
+section Composed
+
+variable (q : PolyExpr) (b : Bool) (n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)) (z : List Bool)
+  (W : Fin (q.eval n * (2 * n)) → Bool)
+
+/-- The tag tapes of the tape word, extended to every index (`AdaptiveCPA.extTape`):
+`bTapes q n W = extTape (blocks (q n) (2n) W)`. -/
+noncomputable def bTapes : ℕ → Fin (2 * n) → Bool :=
+  AdaptiveCPA.extTape (EnsembleLemmas.blocks (q.eval n) (2 * n) W)
+
+/-- `bTapes q n W = extTape (blocks (q n) (2n) W)`. -/
+theorem bTapes_eq :
+    bTapes q n W = AdaptiveCPA.extTape (EnsembleLemmas.blocks (q.eval n) (2 * n) W) :=
+  rfl
+
+/-- Below `q(n)`, the extended tapes are the tapes: `bTapes q n W j = bTapeOf q n W j hj`. -/
+theorem bTapes_of_lt (j : ℕ) (hj : j < q.eval n) : bTapes q n W j = bTapeOf q n W j hj := by
+  rw [bTapes_eq, AdaptiveCPA.extTape_of_lt _ hj, bTapeOf_eq]
+
+/-- The CPA ciphertext of an `n`-bit message as a list:
+`⟦padFin _ (ctOf r m (f r))⟧ = ⟨r, m ⊕ f(r)⟩`. -/
+private theorem ofFn_ctOf {k : ℕ} (hk : k = ctP.eval n) (r : Fin n → Bool) {m : List Bool}
+    (hm : m.length = n) :
+    List.ofFn (padFin k (ctOf r m (f r))) = pairEncode (List.ofFn r) (maskL f r m) := by
+  rw [ofFn_padFin_of_length (by rw [PRFGame.length_ctOf r hm, hk, PRFGame.ctP_eval]),
+    PRFGame.ctOf_eq, maskL_eq]
+
+/-- The pair read from a CPA ciphertext is the pair of the encryption:
+`bKeyOf n (padFin _ (ctOf r m (f r))) = pairV n ⟦r⟧ (maskL f r m)`. -/
+private theorem bKeyOf_ctOf {k : ℕ} (hk : k = ctP.eval n) (r : Fin n → Bool) {m : List Bool}
+    (hm : m.length = n) :
+    bKeyOf n (padFin k (ctOf r m (f r))) = pairV n (List.ofFn r) (maskL f r m) := by
+  rw [bKeyOf_eq, ofFn_ctOf n f hk r hm, pairFstD_pairEncode, pairSndD_pairEncode, pairV_eq]
+
+/-- **One composed call has the law of a call of the lazy experiment with tapes in advance:** from
+`bAbs ((o, L), j)` with the invariant and `j < q(n)`, the handler composed with the CPA oracles
+with pad function `f` gives every function `g` of the answer and the state the expectation that
+the call of `ettLazyTape` with the tapes `bTapes W` from `((o, L), j)` gives it, with the new state
+abstracted.
+
+**Proof sketch.** By the oracle and the record: encryption and a first challenge ask the CPA
+oracle, which draws `r` and answers `⟨r, m ⊕ f(r)⟩` (`PRFGame.fImpl_enc`,
+`PRFGame.fImpl_challenge_none`); the handler reads the pair `r ‖ (m ⊕ f(r))` (`bKeyOf_ctOf`) and
+tags it as `lazyStep` does (`bHandler_impl_enc`, `bHandler_impl_challenge_none`), and the recorded
+CPA challenge is the CPA record of the CCA2 record. Decryption and a repeated challenge answer
+directly in both (`bHandler_impl_dec`, `bHandler_impl_challenge_some`), and the lazy experiment's
+nonce is not read (`expect_const`). -/
+theorem comp_bAbs (i : Fin 3) (x : (bitSpecAt ettDin ettDout n).dom i)
+    (s : LSt n (ettCt.eval n) × ℕ) (hP : bInv n s) (hs : s.2 < q.eval n)
+    (g : (bitSpecAt ettDin ettDout n).rng i ×
+      ((Fin ((bHandler q).stateLen.eval n) → Bool) × Option (Fin (ctP.eval n) → Bool)) → ℝ) :
+    expect ((fImpl (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) (ctP.eval n) n
+        (atkOf false) b f).comp ((bHandler q).impl n z (bHSeed q n W)) i x (bAbs q n s)) g =
+      expect (ettLazyTape (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
+        (ettCt.eval n) n f b (bTapes q n W) i x s) fun p => g (p.1, bAbs q n p.2) := by
+  obtain ⟨⟨o, L⟩, j⟩ := s
+  obtain ⟨hL, hm⟩ := hP
+  have hj : j < q.eval n := hs
+  have hLq : L.length ≤ q.eval n := le_trans hL hj.le
+  rw [QueryImpl.comp_apply, bAbs_eq, ettLazyTape_eq, tapeImpl_apply, ettLazyK_eq,
+    bTapes_of_lt q n W j hj]
+  simp only [OracleComp.bind_assoc, OracleComp.pure_bind, expect_bind, expect_pure]
+  match i, x with
+  | 0, x =>
+    have hx : (List.ofFn x).length = n := by
+      rw [List.length_ofFn]
+      show (ettDin 0).eval n = n
+      rw [ettDin_zero, PolyExpr.eval_var]
+    have hx' : List.ofFn (padFin ((pkDin 0).eval n) (List.ofFn x)) = List.ofFn x :=
+      ofFn_padFin_of_length (by rw [hx, PRFGame.pkDin_zero, PolyExpr.eval_var])
+    rw [bHandler_impl_enc q n z W x j L o hj hLq hm, simulate_query, PRFGame.fImpl_enc]
+    simp only [OracleComp.bind_assoc, OracleComp.pure_bind, simulate_pure, expect_bind, expect_pure]
+    refine congrArg _ (funext fun r => ?_)
+    have hk : (fun i => (pkDout i).eval n) 0 = ctP.eval n := by
+      show (pkDout 0).eval n = ctP.eval n
+      rw [PRFGame.pkDout_zero]
+    rw [lazyStep_enc, bAbs_eq, hx', ofFn_ctOf n f hk r hx, bKeyOf_ctOf n f hk r hx,
+      pairFstD_pairEncode, pairSndD_pairEncode]
+  | 1, x =>
+    rw [bHandler_impl_dec q n z W x j L o hj hLq hm, simulate_pure]
+    simp only [expect_pure, lazyStep_dec, bAbs_eq, expect_const]
+  | 2, x =>
+    cases o with
+    | some c =>
+      rw [bHandler_impl_challenge_some q n z W x j L c hj hLq hm, simulate_pure]
+      simp only [expect_pure, lazyStep_challenge_some, bAbs_eq, expect_const]
+    | none =>
+      have hxx : (List.ofFn x).length = n + n := by
+        rw [List.length_ofFn]
+        show (ettDin 2).eval n = n + n
+        rw [ettDin_two, PolyExpr.eval_add, PolyExpr.eval_var]
+      have hx' : List.ofFn (padFin ((pkDin 2).eval n) (List.ofFn x)) = List.ofFn x :=
+        ofFn_padFin_of_length (by rw [hxx, PRFGame.pkDin_two, PolyExpr.eval_add, PolyExpr.eval_var])
+      have hmsg : (AdaptiveCPA.msgOf n b (List.ofFn x)).length = n := by
+        rw [AdaptiveCPA.msgOf_eq]
+        cases b <;> simp [hxx]
+      rw [bHandler_impl_challenge_none q n z W x j L hj hLq hm, simulate_query, Option.map_none,
+        PRFGame.fImpl_challenge_none]
+      simp only [OracleComp.bind_assoc, OracleComp.pure_bind, simulate_pure, expect_bind,
+        expect_pure]
+      refine congrArg _ (funext fun r => ?_)
+      have hk : (fun i => (pkDout i).eval n) 2 = ctP.eval n := by
+        show (pkDout 2).eval n = ctP.eval n
+        rw [PRFGame.pkDout_two]
+      have hlen : (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn x)))
+          (List.ofFn ((tagOf ((none, L) : LSt n (ettCt.eval n)) (pairV n (List.ofFn r)
+            (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn x))))).getD
+              (bTapeOf q n W j hj)))).length =
+          ettCt.eval n := by
+        rw [ctW_eq, length_pairEncode, length_pairEncode, List.length_ofFn,
+          length_maskL f r hmsg, List.length_ofFn, ettCt_eval]
+        omega
+      have hrec : cpaRec n (padFin (ettCt.eval n) (ctW (List.ofFn r)
+          (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn x)))
+          (List.ofFn ((tagOf ((none, L) : LSt n (ettCt.eval n)) (pairV n (List.ofFn r)
+            (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn x))))).getD (bTapeOf q n W j hj))))) =
+          padFin (ctP.eval n) (ctOf r (AdaptiveCPA.msgOf n b (List.ofFn x)) (f r)) := by
+        rw [cpaRec_eq, ofFn_padFin_of_length hlen, wR_ctW, wC_ctW, PRFGame.ctOf_eq, maskL_eq]
+      rw [lazyStep_challenge_none, bAbs_eq, hx', ofFn_ctOf n f hk r hmsg, bKeyOf_ctOf n f hk r hmsg,
+        pairFstD_pairEncode, pairSndD_pairEncode]
+      simp only [Option.map_some, hrec]
+
+/-- **The calls of the lazy experiment keep the invariant** and raise the counter by one: an
+encryption adds one entry with the `n`-bit message; the other calls keep the table,
+`bInv n s → (ettLazyTape … T i x s).AllOutputs fun p => bInv n p.2 ∧ p.2.2 ≤ s.2 + 1`.
+
+**Proof sketch.** Unfold one call (`ettLazyTape_eq`, `tapeImpl_apply`, `ettLazyK_eq`): for every
+nonce it is a pure step to the counter `j + 1`, so the counter bound holds by `le_rfl`. By the
+oracle: an encryption adds the entry with the message `⟦x⟧` of `n` bits (`lazyStep_enc`), so
+`|L| ≤ j` becomes `|L| + 1 ≤ j + 1`; decryption and both challenge cases keep the table
+(`lazyStep_dec`, `lazyStep_challenge_some`, `lazyStep_challenge_none`), and `|L| ≤ j ≤ j + 1`. -/
+theorem ettLazyTape_bInv (T : ℕ → Fin (2 * n) → Bool) (i : Fin 3)
+    (x : (bitSpecAt ettDin ettDout n).dom i) (s : LSt n (ettCt.eval n) × ℕ) (hP : bInv n s) :
+    (ettLazyTape (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n f b T
+      i x s).AllOutputs fun p => bInv n p.2 ∧ p.2.2 ≤ s.2 + 1 := by
+  obtain ⟨⟨o, L⟩, j⟩ := s
+  obtain ⟨hL, hm⟩ := hP
+  rw [ettLazyTape_eq, tapeImpl_apply, ettLazyK_eq, OracleComp.bind_assoc]
+  refine OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun r _ => ?_
+  rw [OracleComp.pure_bind]
+  refine OracleComp.allOutputs_pure.2 ⟨?_, le_rfl⟩
+  match i, x with
+  | 0, x =>
+    have hx : (List.ofFn x).length = n := by
+      rw [List.length_ofFn]
+      show (ettDin 0).eval n = n
+      rw [ettDin_zero, PolyExpr.eval_var]
+    rw [lazyStep_enc, bInv_iff]
+    refine ⟨by simp only [List.length_cons]; exact Nat.succ_le_succ hL, fun e he => ?_⟩
+    rcases List.mem_cons.1 he with rfl | he
+    · exact hx
+    · exact hm e he
+  | 1, x =>
+    rw [lazyStep_dec]
+    exact ⟨Nat.le_succ_of_le hL, hm⟩
+  | 2, x =>
+    cases o with
+    | some c =>
+      rw [lazyStep_challenge_some]
+      exact ⟨Nat.le_succ_of_le hL, hm⟩
+    | none =>
+      rw [lazyStep_challenge_none]
+      exact ⟨Nat.le_succ_of_le hL, hm⟩
+
+end Composed
+
+/-! ### The reduction -/
+
+/-- **Step 3 of [PS10, Thm 170.4]: the rejecting experiment with a random tag function is a CPA
+experiment of the §3.9 scheme**,
+`∃ B, ∀ b n f, 𝔼_R ettAcc … f R true b A (q n) =
+𝔼_r 𝔼[⟦output⟧₀ = 1 | simulate (fImpl … (atkOf false) b f) (B.toComp … (qRed q n) r) none]`.
+For a machine adversary `A` with budget `q` there is a machine
+`B` such that, for every challenge bit `b`, every `n` and every pad function `f` on `n` bits, the
+average over a uniform random tag function `R` of `A`'s acceptance probability in the experiment
+that rejects fresh decryption queries is `B`'s acceptance probability in the CPA experiment with
+pad function `f` (the oracles `PRFGame.fImpl`, on the lengths `pkDin`, `pkDout`) with budget
+`qRed q`.
+
+**Proof sketch.** `B` runs T2's machine for `bHandler` and the input-free companion of `A` on the
+empty input (`NUPPT.exists_comp` with `pre = ⟨[], ·⟩`). Its coins are, through the bijections of
+the companion, T2 and the seed, the tapes `W` and `A`'s coins `r` (`expect_sample_equiv`,
+`ChallengeSim.expect_sample_prod`, `expect_sample_comm`). For fixed `W` and `r`, T2 turns `B`'s run
+against the CPA oracles into the handler's simulation of `A` composed with them (`simulate_bind`,
+`simulate_comp`, `bHandler_finish`); along `A`'s run (at most `q(n)` queries) it has the law of
+`ettLazyTape` with the tapes of `W` (`expect_simulate_abs_inv`, `comp_bAbs`, `ettLazyTape_bInv`).
+Drawing `W` gives fresh tapes (`expect_ettLazyTape`), and the lazy experiment from the empty state
+is the rejecting experiment averaged over `R` (`expect_ettImpl_lazy`; the empty tag table writes
+nothing). Widths are transported by `Games.expect_toCompOn_outLen` and `expect_ettImpl_outLen`. -/
+theorem exists_cpaStep (A : NUPPT) (q : PolyExpr) :
+    ∃ B : NUPPT, ∀ (b : Bool) (n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)),
+      expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))) (fun R =>
+          ettAcc (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n f R
+            true b A (q.eval n)) =
+        expect (sample (B.Coins n)) fun r =>
+          expect (simulate (fImpl (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
+              (ctP.eval n) n (atkOf false) b f)
+              (B.toComp (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) 1) n
+                ((qRed q).eval n) r) none)
+            (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
+  obtain ⟨A₂, -, hA₂⟩ := exists_toCompOn_of_toComp A
+  obtain ⟨B, hB⟩ := exists_interactiveHandlerMachine A₂ q ettDin ettDout pkDin pkDout (.const 1)
+    (bHandler q)
+  obtain ⟨B', hc, -, -, hB'⟩ := NUPPT.exists_comp B
+    (pre := fun y => pairEncode [] y) (post := id)
+    ((polyTimeComputable_const []).pairEncode polyTimeComputable_id) polyTimeComputable_id
+  refine ⟨B', fun b n f => ?_⟩
+  obtain ⟨φ₀, hφ₀⟩ := hA₂ n
+  obtain ⟨φ₂, hφ₂⟩ := hB n
+  have hQ : q.eval n * (bHandler q).perCall.eval n + (bHandler q).finCall.eval n =
+      (qRed q).eval n := by
+    rw [bHandler_perCall, bHandler_finCall, PRFGame.qRed_eval]
+  have hout : (bHandler q).outLen.eval n = 1 := by rw [bHandler_outLen, PolyExpr.eval_const]
+  -- `B'` on the empty input history is `B` on the input `[]`.
+  have hB'B : ∀ r : B.Coins n,
+      B'.toComp (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) 1) n
+          ((qRed q).eval n) (NUPPT.coinsCongr hc.symm n r) =
+        B.toCompOn (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) 1) n
+          ((qRed q).eval n) [] r := by
+    intro r
+    rw [NUPPT.toComp_eq, NUPPT.toCompOn_eq]
+    congr 1
+    funext hist
+    rw [NUPPT.runAt_coinsCongr, hB', id_eq, ← NUPPT.runAt_eq]
+  -- `B'`'s coins are a tape word and `A`'s coins.
+  rw [← expect_sample_equiv (NUPPT.coinsCongr hc.symm n)]
+  simp only [hB'B]
+  rw [← expect_sample_equiv φ₂, ChallengeSim.expect_sample_prod,
+    ← expect_sample_equiv (bHSeed q n)]
+  conv_rhs => rw [expect_sample_comm]
+  rw [← expect_sample_equiv φ₀]
+  simp only [ettAcc_eq]
+  rw [expect_sample_comm]
+  refine congrArg _ (funext fun r => ?_)
+  -- One run of `B'` is the handler's simulation of `A`, composed with the CPA oracles.
+  have hrun : ∀ W : Fin (q.eval n * (2 * n)) → Bool,
+      expect (simulate (fImpl (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
+          (ctP.eval n) n (atkOf false) b f)
+          (B.toCompOn (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) 1) n
+            ((qRed q).eval n) [] (φ₂ (bHSeed q n W, φ₀ r))) none)
+          (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) =
+        expect (simulate (ettLazyTape (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
+            (ettCt.eval n) n f b (bTapes q n W))
+            (A₂.toCompOn (bitCodec (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
+              ((PolyExpr.const 1).eval n)) n (q.eval n) [] (φ₀ r)) ((none, []), 0))
+          (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
+    intro W
+    rw [expect_toCompOn_outLen _ B n _ [] _ none hout.symm
+        (fun p => if p.1.headD false = true then (1 : ℝ) else 0), ← hQ,
+      ← hφ₂ [] (bHSeed q n W) (φ₀ r), bHandler_advInput, simulate_bind, simulate_comp,
+      OracleComp.bind_assoc, expect_bind]
+    simp only [OracleComp.pure_bind, bHandler_finish, simulate_pure, expect_pure]
+    rw [bHandler_init_hstate, show ((bHState q n 0 [] none, none) :
+        (Fin ((bHandler q).stateLen.eval n) → Bool) × Option (Fin (ctP.eval n) → Bool)) =
+        bAbs q n ((none, []), 0) from rfl,
+      expect_simulate_abs_inv _ _ (bAbs q n) (bInv n) (fun s => s.2) (q.eval n)
+        (fun i x s hP hs g => comp_bAbs q b n f [] W i x s hP hs g)
+        (fun i x s hP _ => ettLazyTape_bInv b n f _ i x s hP) _ (q.eval n)
+        (A₂.toCompOn_costBoundedBy _ n _ _ _) ((none, []), 0)
+        ⟨le_rfl, fun e he => absurd he List.not_mem_nil⟩ (Nat.zero_add _).le]
+    refine congrArg _ (funext fun p => ?_)
+    rw [ofFn_padFin_of_length (by rw [List.length_ofFn, bHandler_outLen])]
+  simp only [hrun, bTapes_eq]
+  have hi0 : (fun i => (ettDin i).eval n) 0 = n := by
+    show (ettDin 0).eval n = n
+    rw [ettDin_zero, PolyExpr.eval_var]
+  have hi2 : (fun i => (ettDin i).eval n) 2 = n + n := by
+    show (ettDin 2).eval n = n + n
+    rw [ettDin_two, PolyExpr.eval_add, PolyExpr.eval_var]
+  rw [expect_sample_equiv (EnsembleLemmas.blocks (q.eval n) (2 * n)) (fun T =>
+      expect (simulate (ettLazyTape (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
+          (ettCt.eval n) n f b (AdaptiveCPA.extTape T))
+          (A₂.toCompOn (bitCodec (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
+            ((PolyExpr.const 1).eval n)) n (q.eval n) [] (φ₀ r)) ((none, []), 0))
+        (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0)),
+    expect_ettLazyTape _ _ _ _ _ _ (q.eval n)
+      (fun a => if (List.ofFn a).headD false = true then (1 : ℝ) else 0) _
+      (q.eval n) (A₂.toCompOn_costBoundedBy _ n _ _ _) (none, []) 0 (by omega),
+    ← expect_ettImpl_lazy _ _ _ n f b (ettCt_eval n) hi0 hi2
+      (fun a => if (List.ofFn a).headD false = true then (1 : ℝ) else 0) _ (none, [])
+      (lInv_nil n f none)]
+  refine congrArg _ (funext fun R => ?_)
+  have htbl : ovr (tagTbl ((none, []) : LSt n (ettCt.eval n))) R = R := by
+    rw [tagTbl_none_nil, ovr_nil]
+  rw [htbl, hφ₀, keysL_nil]
+  exact expect_ettImpl_outLen (PolyExpr.eval_const 1 n).symm _ _ _ _ A _ r
+
+end TCSlib.Cryptography.Composability.ETTGame
diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Forgery.lean b/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Forgery.lean
new file mode 100644
index 000000000..22595430e
--- /dev/null
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Forgery.lean
@@ -0,0 +1,559 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Games
+import TCSlib.Cryptography.Games.Hopping
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Fresh decryption queries are rejected
+
+Step 2 of [PS10, Theorem 170.4]: with a random tag function `R` on `2n` bits, the experiment that
+answers every valid decryption query (`rej = false`) and the experiment that rejects the valid
+queries whose pair `r ‖ c₁` is not the pair of an earlier `Enc′` answer (`rej = true`) differ by at
+most `q / 2^{2n}` for an adversary making at most `q` queries.
+
+* *Identical until bad.* The two experiments draw the same nonces and agree until the first
+  decryption query that is not refused, is valid and has a fresh pair (`hitW`); the flag of
+  `ettBad` records it (`ettBad_agree`, `ettBad_stick`), and forgetting the flag gives `ettImpl`
+  (`simulate_ettBad_fst`).
+* *The bad probability.* In the rejecting experiment the answers never read `R` outside the
+  revealed pairs (the pairs of the `Enc′` answers and of the challenge). Averaging over `R`, write
+  `R` overridden on the revealed pairs by a table `M` (`ovr`): an encryption at a new pair moves
+  the value `R p` into the table (`expect_sample_ovr`), and a decryption query with a fresh pair
+  guesses the unrevealed `R p`, with probability at most `2^{-2n}`. A valid query with the
+  challenge's pair is the challenge itself, for `n > 0` (canonical parsing, `eq_ctW_of_wfW`), and is
+  refused. The union bound over the queries gives `q / 2^{2n}` (`expect_prob_bad_le`).
+
+## Main definitions
+
+* `ETTGame.RevInv M s`: the invariant of the revealed pairs, with `keys M = M.map Prod.fst`,
+  `keys M ⊆ s.2 ∪ {pairW n ⟦c⟧ | s.1 = some c}`, `s.2 ⊆ keys M`, and a record `s.1 = some c` with
+  `⟦c⟧ = ctW ⟦r⟧ c₁ ⟦y⟧`, `|c₁| = n`, `pairV n ⟦r⟧ c₁ ∈ keys M` and `ovr M R (pairV n ⟦r⟧ c₁) = y`.
+
+## Main results
+
+* `ETTGame.ettBad_agree`, `ettBad_stick`, `simulate_ettBad_fst`.
+* `ETTGame.abs_prob_ettImpl_rej_sub_le`: identical until bad.
+* `ETTGame.expect_prob_bad_le`: the bad probability with a random tag function.
+* `ETTGame.abs_ettAcc_rej_sub_le`: step 2, for machine adversaries.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 170.4 (book pp. 170–171).
+* [BR06] M. Bellare, P. Rogaway, *The Security of Triple Encryption and a Framework for
+  Code-Based Game-Playing Proofs*, EUROCRYPT 2006 (identical until bad).
+-/
+
+namespace TCSlib.Cryptography.Composability.ETTGame
+
+open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp
+
+/-! ### Identical until bad -/
+
+section Agree
+
+variable (ins outs : Fin 3 → ℕ) (d n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool))
+  (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (b : Bool)
+
+/-- **From a good state the two experiments agree on good successors:** for every function `G`
+vanishing on flagged states, the calls of `ettBad … false` and `ettBad … true` have the same
+expectation of `G`: for `s.2 ≠ true` and `G̃ ys = if ys.2.2 = true then 0 else G ys`,
+`𝔼[G̃ | ettBad … false b i x s] = 𝔼[G̃ | ettBad … true b i x s]`.
+
+**Proof sketch.** Both draw the same nonce and raise the flag by the same `hitQ`; only a
+decryption answer reads `rej`, and off the flag the two answers agree (`decAnsW_agree`). -/
+theorem ettBad_agree (i : Fin 3) (x : (bitSpec ins outs).dom i) (s : St n d × Bool)
+    (hs : ¬ s.2 = true) (G : (bitSpec ins outs).rng i × (St n d × Bool) → ℝ) :
+    expect (ettBad ins outs d n f g false b i x s) (fun ys => if ys.2.2 = true then 0 else G ys) =
+      expect (ettBad ins outs d n f g true b i x s)
+        (fun ys => if ys.2.2 = true then 0 else G ys) := by
+  obtain ⟨s, β⟩ := s
+  have hβ : β = false := Bool.eq_false_iff.2 hs
+  subst hβ
+  rw [ettBad_apply, ettBad_apply, ettImpl_apply, ettImpl_apply]
+  simp only [OracleComp.bind_assoc, OracleComp.pure_bind, expect_bind, expect_pure,
+    Bool.false_or]
+  refine congrArg _ (funext fun r => ?_)
+  match i, x with
+  | 0, m => rw [ettStep_enc, ettStep_enc]
+  | 1, w =>
+    rw [hitQ_one, ettStep_dec, ettStep_dec]
+    by_cases h : hitW g s (List.ofFn w) = true
+    · rw [if_pos h, if_pos h]
+    · rw [Bool.not_eq_true] at h
+      rw [decAnsW_agree f g s _ h]
+  | 2, mm =>
+    obtain ⟨o, T⟩ := s
+    cases o with
+    | some c => rw [ettStep_challenge_some, ettStep_challenge_some]
+    | none => rw [ettStep_challenge_none, ettStep_challenge_none]
+
+/-- **The flag is sticky:** from a flagged state every successor is flagged,
+`s.2 = true → (ettBad … rej b i x s).AllOutputs fun ys => ys.2.2 = true`. -/
+theorem ettBad_stick (rej : Bool) (i : Fin 3) (x : (bitSpec ins outs).dom i) (s : St n d × Bool)
+    (hs : s.2 = true) :
+    (ettBad ins outs d n f g rej b i x s).AllOutputs fun ys => ys.2.2 = true := by
+  rw [ettBad_apply, ettImpl_apply, OracleComp.bind_assoc]
+  refine OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun r _ => ?_
+  rw [OracleComp.pure_bind]
+  exact OracleComp.allOutputs_pure.2 (by rw [hs, Bool.true_or])
+
+/-- **The flag is a ghost:** forgetting it, the simulation of `ettBad` is the simulation of
+`ettImpl`, from every flag (`simulate_eq_of_abs` with the projection):
+`(simulate (ettBad … rej b) c (s, β)).bind (fun p => pure (p.1, p.2.1)) =
+simulate (ettImpl … rej b) c s`. -/
+theorem simulate_ettBad_fst (rej : Bool) {α : Type} (c : OracleComp (bitSpec ins outs) α)
+    (s : St n d) (β : Bool) :
+    (simulate (ettBad ins outs d n f g rej b) c (s, β)).bind (fun p => .pure (p.1, p.2.1)) =
+      simulate (ettImpl ins outs d n f g rej b) c s := by
+  refine (simulate_eq_of_abs (ettImpl ins outs d n f g rej b) (ettBad ins outs d n f g rej b)
+    Prod.fst (fun i x s => ?_) c (s, β)).symm
+  rw [ettBad_apply, OracleComp.bind_assoc]
+  simp only [OracleComp.pure_bind]
+  exact (OracleComp.bind_pure _).symm
+
+/-- **Identical until bad** [BR06]: for every event `P` on the output, the probabilities under the
+experiments with `rej = false` and `rej = true` differ by at most the probability that the
+rejecting experiment raises the flag.
+
+**Proof sketch.** `identical_until_bad` on `ettBad` (`ettBad_agree`, `ettBad_stick`), with the bad
+probability moved to `rej = true` (`prob_eq_until_bad`) and the flag forgotten
+(`simulate_ettBad_fst`). -/
+theorem abs_prob_ettImpl_rej_sub_le {α : Type} (c : OracleComp (bitSpec ins outs) α)
+    (P : α → Prop) (s : St n d) :
+    |prob (simulate (ettImpl ins outs d n f g false b) c s) (fun p => P p.1) -
+        prob (simulate (ettImpl ins outs d n f g true b) c s) (fun p => P p.1)| ≤
+      prob (simulate (ettBad ins outs d n f g true b) c (s, false)) (fun p => p.2.2 = true) := by
+  classical
+  have hfst : ∀ rej : Bool, prob (simulate (ettImpl ins outs d n f g rej b) c s)
+      (fun p => P p.1) =
+      prob (simulate (ettBad ins outs d n f g rej b) c (s, false)) (fun p => P p.1) := by
+    intro rej
+    rw [← simulate_ettBad_fst ins outs d n f g b rej c s false, prob_bind]
+    simp only [prob_pure]
+    rw [prob_eq_expect]
+  rw [hfst false, hfst true]
+  refine (identical_until_bad (fun st : St n d × Bool => st.2 = true)
+    (fun i x st hst G => ettBad_agree ins outs d n f g b i x st hst G)
+    (fun i x st hst => ettBad_stick ins outs d n f g b false i x st hst)
+    (fun i x st hst => ettBad_stick ins outs d n f g b true i x st hst) c P
+    (s := (s, false)) Bool.false_ne_true).trans (le_of_eq ?_)
+  exact (prob_eq_until_bad (fun st : St n d × Bool => st.2 = true)
+    (fun i x st hst G => ettBad_agree ins outs d n f g b i x st hst G)
+    (fun i x st hst => ettBad_stick ins outs d n f g b false i x st hst)
+    (fun i x st hst => ettBad_stick ins outs d n f g b true i x st hst) c P
+    (s := (s, false)) Bool.false_ne_true).2
+
+end Agree
+
+/-! ### The bad probability with a random tag function -/
+
+section Bound
+
+variable {d n : ℕ}
+
+/-- **The invariant of the revealed pairs** for a table `M` and a state `s`: every key of `M` is a
+listed pair or the challenge's pair; every listed pair is a key; and the recorded challenge is the
+word `⟨r, ⟨c₁, y⟩⟩` of a nonce, an `n`-bit mask and the table's value `y` at their pair: with
+`keys M = M.map Prod.fst`,
+`RevInv M s ↔ (∀ p ∈ keys M, p ∈ s.2 ∨ ∃ c, s.1 = some c ∧ p = pairW n ⟦c⟧) ∧
+(∀ p ∈ s.2, p ∈ keys M) ∧ (∀ c, s.1 = some c → ∃ r c₁ y, ⟦c⟧ = ctW ⟦r⟧ c₁ ⟦y⟧ ∧ |c₁| = n ∧
+pairV n ⟦r⟧ c₁ ∈ keys M ∧ ∀ R, ovr M R (pairV n ⟦r⟧ c₁) = y)`. -/
+def RevInv (M : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))) (s : St n d) : Prop :=
+  (∀ p ∈ M.map Prod.fst, p ∈ s.2 ∨ ∃ c, s.1 = some c ∧ p = pairW n (List.ofFn c)) ∧
+  (∀ p ∈ s.2, p ∈ M.map Prod.fst) ∧
+  (∀ c, s.1 = some c → ∃ (r : Fin n → Bool) (c₁ : List Bool) (y : Fin (2 * n) → Bool),
+    List.ofFn c = ctW (List.ofFn r) c₁ (List.ofFn y) ∧ c₁.length = n ∧
+    pairV n (List.ofFn r) c₁ ∈ M.map Prod.fst ∧ ∀ R, ovr M R (pairV n (List.ofFn r) c₁) = y)
+
+/-- `RevInv M s` unfolded, with `keys M = M.map Prod.fst`:
+`RevInv M s ↔ (∀ p ∈ keys M, p ∈ s.2 ∨ ∃ c, s.1 = some c ∧ p = pairW n ⟦c⟧) ∧
+(∀ p ∈ s.2, p ∈ keys M) ∧ (∀ c, s.1 = some c → ∃ r c₁ y, ⟦c⟧ = ctW ⟦r⟧ c₁ ⟦y⟧ ∧ |c₁| = n ∧
+pairV n ⟦r⟧ c₁ ∈ keys M ∧ ∀ R, ovr M R (pairV n ⟦r⟧ c₁) = y)`. -/
+theorem revInv_iff (M : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))) (s : St n d) :
+    RevInv M s ↔
+      (∀ p ∈ M.map Prod.fst, p ∈ s.2 ∨ ∃ c, s.1 = some c ∧ p = pairW n (List.ofFn c)) ∧
+      (∀ p ∈ s.2, p ∈ M.map Prod.fst) ∧
+      (∀ c, s.1 = some c → ∃ (r : Fin n → Bool) (c₁ : List Bool) (y : Fin (2 * n) → Bool),
+        List.ofFn c = ctW (List.ofFn r) c₁ (List.ofFn y) ∧ c₁.length = n ∧
+        pairV n (List.ofFn r) c₁ ∈ M.map Prod.fst ∧
+        ∀ R, ovr M R (pairV n (List.ofFn r) c₁) = y) :=
+  Iff.rfl
+
+/-- The empty table and the initial state satisfy the invariant: `RevInv [] (none, [])`, since its
+clauses quantify over `p ∈ []`, over `p ∈ []` and over `none = some c`. -/
+theorem revInv_nil : RevInv (d := d) (n := n) [] (none, []) :=
+  ⟨fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => by cases h⟩
+
+/-- An encryption at a pair already in the table keeps the invariant. -/
+private theorem revInv_enc_old {M : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))}
+    {s : St n d} (h : RevInv M s) {p : Fin (2 * n) → Bool} (hp : p ∈ M.map Prod.fst) :
+    RevInv M (s.1, p :: s.2) := by
+  obtain ⟨h₁, h₂, h₃⟩ := h
+  refine ⟨fun p' hp' => ?_, fun p' hp' => ?_, h₃⟩
+  · rcases h₁ p' hp' with h | h
+    · exact Or.inl (List.mem_cons_of_mem _ h)
+    · exact Or.inr h
+  · rcases List.mem_cons.1 hp' with rfl | h
+    · exact hp
+    · exact h₂ p' h
+
+/-- An encryption at a new pair `p` with the value `t` keeps the invariant of the extended table.
+
+**Proof sketch.** Clause by clause. A key of `(p, t) :: M` is `p`, now listed, or a key of `M`,
+listed or the challenge's pair as before. A listed pair of `p :: s.2` is `p`, now a key, or a key
+of `M`. The challenge's witnesses `r, c₁, y` are kept: their pair is still a key, and it differs
+from the new `p ∉ keys M`, so `ovr ((p, t) :: M) R` still gives `y` there (`ovr_cons`,
+`Function.update_of_ne`). -/
+private theorem revInv_enc_new {M : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))}
+    {s : St n d} (h : RevInv M s) {p : Fin (2 * n) → Bool} (hp : p ∉ M.map Prod.fst)
+    (t : Fin (2 * n) → Bool) : RevInv ((p, t) :: M) (s.1, p :: s.2) := by
+  obtain ⟨h₁, h₂, h₃⟩ := h
+  refine ⟨fun p' hp' => ?_, fun p' hp' => ?_, fun c hc => ?_⟩
+  · simp only [List.map_cons, List.mem_cons] at hp'
+    rcases hp' with rfl | hp'
+    · exact Or.inl (List.mem_cons_self ..)
+    · rcases h₁ p' hp' with h | h
+      · exact Or.inl (List.mem_cons_of_mem _ h)
+      · exact Or.inr h
+  · simp only [List.map_cons, List.mem_cons]
+    rcases List.mem_cons.1 hp' with rfl | h
+    · exact Or.inl rfl
+    · exact Or.inr (h₂ p' h)
+  · obtain ⟨r, c₁, y, hw, hl, hk, hy⟩ := h₃ c hc
+    have hne : pairV n (List.ofFn r) c₁ ≠ p := fun h => hp (h ▸ hk)
+    refine ⟨r, c₁, y, hw, hl, ?_, fun R => ?_⟩
+    · simp only [List.map_cons, List.mem_cons]
+      exact Or.inr hk
+    · rw [ovr_cons, Function.update_of_ne hne, hy]
+
+/-- Recording a challenge whose pair is already in the table keeps the invariant. -/
+private theorem revInv_chal_old {M : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))}
+    {T : List (Fin (2 * n) → Bool)} (h : RevInv (d := d) M (none, T)) (r : Fin n → Bool)
+    {c₁ : List Bool}
+    (hl : c₁.length = n) (hk : pairV n (List.ofFn r) c₁ ∈ M.map Prod.fst)
+    (y : Fin (2 * n) → Bool) (hy : ∀ R, ovr M R (pairV n (List.ofFn r) c₁) = y) (c : Fin d → Bool)
+    (hc : List.ofFn c = ctW (List.ofFn r) c₁ (List.ofFn y)) : RevInv M (some c, T) := by
+  obtain ⟨h₁, h₂, -⟩ := h
+  refine ⟨fun p hp => ?_, h₂, fun c' hc' => ?_⟩
+  · rcases h₁ p hp with h | ⟨c'', hc'', -⟩
+    · exact Or.inl h
+    · cases hc''
+  · cases hc'
+    exact ⟨r, c₁, y, hc, hl, hk, hy⟩
+
+/-- Recording a challenge at a new pair with the value `t` keeps the invariant of the extended
+table.
+
+**Proof sketch.** Clause by clause. The new key `pairV n ⟦r⟧ c₁` is the pair of the recorded `c`
+(`pairW_eq`, `wR_ctW`, `wC_ctW` on `⟦c⟧ = ctW ⟦r⟧ c₁ ⟦t⟧`); the old keys are listed, since the
+state had no record. The list is unchanged and its pairs are still keys. The record's witnesses
+are `r, c₁, t`: the new key is a key, and `ovr` of the extended table gives `t` there (`ovr_cons`,
+`Function.update_self`). -/
+private theorem revInv_chal_new {M : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))}
+    {T : List (Fin (2 * n) → Bool)} (h : RevInv (d := d) M (none, T)) (r : Fin n → Bool)
+    {c₁ : List Bool}
+    (hl : c₁.length = n) (t : Fin (2 * n) → Bool) (c : Fin d → Bool)
+    (hc : List.ofFn c = ctW (List.ofFn r) c₁ (List.ofFn t)) :
+    RevInv ((pairV n (List.ofFn r) c₁, t) :: M) (some c, T) := by
+  obtain ⟨h₁, h₂, -⟩ := h
+  refine ⟨fun p hp' => ?_, fun p hp' => ?_, fun c' hc' => ?_⟩
+  · simp only [List.map_cons, List.mem_cons] at hp'
+    rcases hp' with rfl | hp'
+    · refine Or.inr ⟨c, rfl, ?_⟩
+      rw [pairW_eq, hc, wR_ctW, wC_ctW]
+    · rcases h₁ p hp' with h | ⟨c'', hc'', -⟩
+      · exact Or.inl h
+      · cases hc''
+  · simp only [List.map_cons, List.mem_cons]
+    exact Or.inr (h₂ p hp')
+  · cases hc'
+    refine ⟨r, c₁, t, hc, hl, ?_, fun R => ?_⟩
+    · simp only [List.map_cons, List.mem_cons, true_or]
+    · rw [ovr_cons, Function.update_self]
+
+/-- The tag of a word read through the pair:
+`validW g w = (wfW n w && decide (wT w = ⟦g (pairW n w)⟧))`. -/
+private theorem validW_pairW (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (w : List Bool) :
+    validW g w = (wfW n w && decide (wT w = List.ofFn (g (pairW n w)))) := by
+  rw [validW_eq, tagL_eq, pairW_eq]
+
+/-- **A fresh guess hits the random tag with probability at most `2^{-2n}`:** under the
+invariant, `𝔼_R [hitW (ovr M R) s w] ≤ 2^{-2n}` for `n > 0`.
+
+**Proof sketch.** A hit needs a pair outside the list. A key of the table outside the list is the
+challenge's pair; there a valid word has the challenge's fields (`eq_of_pairV_eq`), so it is the
+challenge (`eq_ctW_of_wfW`) and is refused. Outside the keys the tag is `R` at the pair
+(`ovr_of_not_mem`), uniform (`expect_sample_coord`, `expect_sample_mem_le`). -/
+private theorem expect_hitW_le (hn : 0 < n) {M : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))}
+    {s : St n d} (hM : RevInv M s) (w : List Bool) :
+    expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)))
+        (fun R => if hitW (ovr M R) s w = true then (1 : ℝ) else 0) ≤ ((2 : ℝ) ^ (2 * n))⁻¹ := by
+  have hδ : (0 : ℝ) ≤ ((2 : ℝ) ^ (2 * n))⁻¹ := by positivity
+  by_cases hk : pairW n w ∈ M.map Prod.fst
+  · -- a key: the list or the challenge, and then no hit
+    have h0 : ∀ R, hitW (ovr M R) s w = false := by
+      intro R
+      rw [hitW_eq]
+      obtain ⟨h₁, -, h₃⟩ := hM
+      rcases h₁ _ hk with hl | ⟨c, hc, hp⟩
+      · simp [hl]
+      · obtain ⟨r, c₁, y, hw, hl, -, hy⟩ := h₃ c hc
+        by_cases hv : validW (ovr M R) w = true
+        · have hv' := hv
+          rw [validW_pairW, Bool.and_eq_true, decide_eq_true_eq] at hv'
+          obtain ⟨hwf, ht⟩ := hv'
+          have hwf' := hwf
+          rw [wfW_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hwf'
+          have hpc : pairW n (List.ofFn c) = pairV n (List.ofFn r) c₁ := by
+            rw [pairW_eq, hw, wR_ctW, wC_ctW]
+          rw [hp, hpc, hy] at ht
+          rw [pairW_eq, hpc] at hp
+          obtain ⟨hr, hcc⟩ := eq_of_pairV_eq hwf'.1 hwf'.2 List.length_ofFn hl hp
+          have hweq : w = List.ofFn c := by
+            rw [hw, eq_ctW_of_wfW hn hwf, hr, hcc, ht]
+          rw [hc, refW_some, hweq]
+          simp
+        · rw [Bool.not_eq_true] at hv
+          simp [hv]
+    simp only [h0, Bool.false_eq_true, if_false, expect_const]
+    exact hδ
+  · -- not a key: the tag is `R` at the pair
+    have hle : ∀ R, (if hitW (ovr M R) s w = true then (1 : ℝ) else 0) ≤
+        if R (pairW n w) ∈ [padFin (2 * n) (wT w)] then 1 else 0 := by
+      intro R
+      by_cases h : hitW (ovr M R) s w = true
+      · rw [if_pos h]
+        rw [hitW_eq, Bool.and_eq_true, Bool.and_eq_true, validW_pairW, Bool.and_eq_true,
+          decide_eq_true_eq, ovr_of_not_mem hk] at h
+        rw [if_pos (by rw [List.mem_singleton, h.1.2.2, padFin_ofFn])]
+      · rw [if_neg h]
+        split <;> norm_num
+    refine (expect_mono _ hle).trans ?_
+    rw [expect_sample_coord (pairW n w) (fun t (_ : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) =>
+      if t ∈ [padFin (2 * n) (wT w)] then (1 : ℝ) else 0) (fun _ _ _ => rfl)]
+    simp only [expect_const]
+    refine (expect_sample_mem_le _).trans (le_of_eq ?_)
+    rw [List.length_singleton, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
+    push_cast
+    rw [one_div]
+
+end Bound
+
+section Induction
+
+variable (ins outs : Fin 3 → ℕ) (d n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)) (b : Bool)
+
+/-- From a flagged state the simulation ends flagged: its bad probability is `1`. -/
+private theorem prob_bad_of_flag (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) {α : Type}
+    (c : OracleComp (bitSpec ins outs) α) (s : St n d) :
+    prob (simulate (ettBad ins outs d n f g true b) c (s, true)) (fun p => p.2.2 = true) = 1 :=
+  prob_eq_one_of_allOutputs (simulate_allOutputs_bad (fun st : St n d × Bool => st.2 = true)
+    (fun i x st hst => ettBad_stick ins outs d n f g b true i x st hst) c rfl)
+
+/-- One query of the flagged simulation: draw the nonce, take the step, raise the flag by
+`hitQ`, continue. -/
+private theorem prob_simulate_ettBad_query (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))
+    {α : Type} (i : Fin 3) (x : (bitSpec ins outs).dom i)
+    (k : (bitSpec ins outs).rng i → OracleComp (bitSpec ins outs) α) (s : St n d) :
+    prob (simulate (ettBad ins outs d n f g true b) (.query i x k) (s, false))
+        (fun p => p.2.2 = true) =
+      expect (sample (Fin n → Bool)) fun r =>
+        prob (simulate (ettBad ins outs d n f g true b)
+          (k (ettStep ins outs d n f g true b r i x s).1)
+          ((ettStep ins outs d n f g true b r i x s).2, hitQ ins d n g i x s))
+          (fun p => p.2.2 = true) := by
+  rw [simulate_query, prob_bind, ettBad_apply, ettImpl_apply, OracleComp.bind_assoc, expect_bind]
+  simp only [OracleComp.pure_bind, expect_pure, Bool.false_or]
+
+/-- **The bad probability with a random tag function** [PS10, Thm 170.4, proof]: for `n > 0`,
+`(6n + 4)`-bit records and `2n`-bit challenge queries, from a state and a table with the invariant
+`RevInv`, a computation making at most `m` queries raises the flag of the rejecting experiment
+with probability at most `m / 2^{2n}`, averaged over `R` with the table written over it:
+`𝔼_R Pr[bad | simulate (ettBad … (ovr M R) true b) c (s, false)] ≤ m · 2^{-2n}`.
+
+**Proof sketch.** Induction on `c`. An encryption, or a first challenge, at a pair already in the
+table reads the table only; at a new pair it reads `R` there, which `expect_sample_ovr` moves into
+the table (the invariant follows, `revInv_enc_new`, `revInv_chal_new`). A decryption answer of the
+rejecting experiment reads the tag function only at listed pairs, which are keys, so it does not
+depend on `R`; it raises the flag with probability at most `2^{-2n}` (`expect_hitW_le`), and the
+union bound adds it to the continuation's bound. A repeated challenge reads nothing. -/
+theorem expect_prob_bad_le (hn : 0 < n) (hd : d = 6 * n + 4) (hi2 : ins 2 = n + n) {α : Type}
+    (c : OracleComp (bitSpec ins outs) α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m)
+    (M : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))) (s : St n d) (hM : RevInv M s) :
+    expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)))
+        (fun R => prob (simulate (ettBad ins outs d n f (ovr M R) true b) c (s, false))
+          (fun p => p.2.2 = true)) ≤ m * ((2 : ℝ) ^ (2 * n))⁻¹ := by
+  have hδ : (0 : ℝ) ≤ ((2 : ℝ) ^ (2 * n))⁻¹ := by positivity
+  induction c generalizing m M s with
+  | pure a =>
+    simp only [simulate_pure, prob_pure, Bool.false_eq_true, if_false, expect_const]
+    positivity
+  | query i x k ih =>
+    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
+    have hm1 : 1 ≤ m := hm
+    have IH : ∀ y (M' : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))) (s' : St n d),
+        RevInv M' s' →
+        expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)))
+          (fun R => prob (simulate (ettBad ins outs d n f (ovr M' R) true b) (k y) (s', false))
+            (fun p => p.2.2 = true)) ≤ ((m - 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (2 * n))⁻¹ :=
+      fun y M' s' h => ih y (m - 1) (hk y) M' s' h
+    have hm' : ((m - 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (2 * n))⁻¹ + ((2 : ℝ) ^ (2 * n))⁻¹ =
+        (m : ℝ) * ((2 : ℝ) ^ (2 * n))⁻¹ := by
+      rw [Nat.cast_sub hm1]
+      ring
+    have hle : ((m - 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (2 * n))⁻¹ ≤ (m : ℝ) * ((2 : ℝ) ^ (2 * n))⁻¹ := by
+      linarith
+    simp only [prob_simulate_ettBad_query]
+    -- a step that reads the tag function at the pair `p` of a fresh nonce
+    have fresh : ∀ (p : (Fin n → Bool) → Fin (2 * n) → Bool)
+        (Y : (Fin n → Bool) → (Fin (2 * n) → Bool) → (bitSpec ins outs).rng i)
+        (S : (Fin n → Bool) → (Fin (2 * n) → Bool) → St n d),
+        (∀ r, p r ∈ M.map Prod.fst → ∀ t, (∀ R, ovr M R (p r) = t) → RevInv M (S r t)) →
+        (∀ r, p r ∉ M.map Prod.fst → ∀ t, RevInv ((p r, t) :: M) (S r t)) →
+        expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))) (fun R =>
+          expect (sample (Fin n → Bool)) fun r =>
+            prob (simulate (ettBad ins outs d n f (ovr M R) true b)
+              (k (Y r (ovr M R (p r)))) (S r (ovr M R (p r)), false))
+              (fun q => q.2.2 = true)) ≤ (m : ℝ) * ((2 : ℝ) ^ (2 * n))⁻¹ := by
+      intro p Y S hold hnew
+      rw [expect_sample_comm]
+      refine (expect_mono _ fun r => ?_).trans ((le_of_eq (expect_const _ _)).trans hle)
+      by_cases hp : p r ∈ M.map Prod.fst
+      · have hc : ∀ R, ovr M R (p r) = ovr M (fun _ => p r) (p r) :=
+          fun R => ovr_of_mem hp R _
+        simp only [hc]
+        exact IH _ M _ (hold r hp _ hc)
+      · have e : ∀ R, ovr M R (p r) = R (p r) := fun R => ovr_of_not_mem hp R
+        simp only [e]
+        rw [expect_sample_ovr M hp (fun t g => prob (simulate (ettBad ins outs d n f g true b)
+            (k (Y r t)) (S r t, false)) (fun q => q.2.2 = true))]
+        refine (expect_mono _ fun t => IH _ _ _ (hnew r hp t)).trans (le_of_eq ?_)
+        exact expect_const _ _
+    match i, x, k, ih, IH, fresh with
+    | 0, x, k, ih, IH, fresh =>
+      simp only [ettStep_enc, hitQ_zero, encW_eq_ctW]
+      exact fresh (fun r => pairV n (List.ofFn r) (maskL f r (List.ofFn x)))
+        (fun r t => padFin _ (ctW (List.ofFn r) (maskL f r (List.ofFn x)) (List.ofFn t)))
+        (fun r _ => (s.1, pairV n (List.ofFn r) (maskL f r (List.ofFn x)) :: s.2))
+        (fun r hp _ _ => revInv_enc_old hM hp) (fun r hp t => revInv_enc_new hM hp t)
+    | 1, w, k, ih, IH, fresh =>
+      simp only [ettStep_dec, hitQ_one, expect_const]
+      -- the answer does not read `R`
+      have hans : ∀ R, decAnsW f (ovr M R) true s (List.ofFn w) =
+          decAnsW f (ovr M (fun _ => pairW n (List.ofFn w))) true s (List.ofFn w) := by
+        intro R
+        rw [decAnsW_eq, decAnsW_eq]
+        by_cases hl : pairW n (List.ofFn w) ∈ s.2
+        · have hkey := hM.2.1 _ hl
+          rw [validW_pairW, validW_pairW, ovr_of_mem hkey R]
+        · simp [hl]
+      simp only [hans]
+      have hsplit : ∀ R, prob (simulate (ettBad ins outs d n f (ovr M R) true b)
+          (k (padFin _ (decAnsW f (ovr M (fun _ => pairW n (List.ofFn w))) true s (List.ofFn w))))
+          (s, hitW (ovr M R) s (List.ofFn w))) (fun q => q.2.2 = true) ≤
+          (if hitW (ovr M R) s (List.ofFn w) = true then (1 : ℝ) else 0) +
+            prob (simulate (ettBad ins outs d n f (ovr M R) true b)
+              (k (padFin _ (decAnsW f (ovr M (fun _ => pairW n (List.ofFn w))) true s
+                (List.ofFn w)))) (s, false)) (fun q => q.2.2 = true) := by
+        intro R
+        by_cases h : hitW (ovr M R) s (List.ofFn w) = true
+        · rw [h, prob_bad_of_flag, if_pos rfl]
+          linarith [prob_nonneg (simulate (ettBad ins outs d n f (ovr M R) true b)
+            (k (padFin _ (decAnsW f (ovr M (fun _ => pairW n (List.ofFn w))) true s
+              (List.ofFn w)))) (s, false)) (fun q => q.2.2 = true)]
+        · rw [Bool.not_eq_true] at h
+          rw [h]
+          simp
+      refine (expect_mono _ hsplit).trans ?_
+      rw [expect_add]
+      have h1 := expect_hitW_le hn hM (List.ofFn w)
+      have h2 := IH (padFin _ (decAnsW f (ovr M (fun _ => pairW n (List.ofFn w))) true s
+        (List.ofFn w))) M s hM
+      linarith
+    | 2, mm, k, ih, IH, fresh =>
+      obtain ⟨o, T⟩ := s
+      cases o with
+      | some c =>
+        simp only [ettStep_challenge_some, hitQ_two, expect_const]
+        exact (IH _ M _ hM).trans hle
+      | none =>
+        have hmsg : (AdaptiveCPA.msgOf n b (List.ofFn mm)).length = n := by
+          have : (List.ofFn mm).length = n + n := by rw [List.length_ofFn, hi2]
+          rw [AdaptiveCPA.msgOf_eq]
+          cases b <;> simp [this]
+        have hl : ∀ r : Fin n → Bool,
+            (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))).length = n :=
+          fun r => length_maskL f r hmsg
+        have hrec : ∀ (r : Fin n → Bool) (t : Fin (2 * n) → Bool),
+            List.ofFn (padFin d (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b
+              (List.ofFn mm))) (List.ofFn t))) =
+            ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))) (List.ofFn t) := by
+          intro r t
+          refine ofFn_padFin_of_length ?_
+          rw [ctW_eq, length_pairEncode, length_pairEncode, List.length_ofFn, hl r,
+            List.length_ofFn, hd]
+          omega
+        simp only [ettStep_challenge_none, hitQ_two, encW_eq_ctW]
+        exact fresh (fun r => pairV n (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b
+            (List.ofFn mm))))
+          (fun r t => padFin _ (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b
+            (List.ofFn mm))) (List.ofFn t)))
+          (fun r t => (some (padFin d (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b
+            (List.ofFn mm))) (List.ofFn t))), T))
+          (fun r hp t ht => revInv_chal_old hM r (hl r) hp t ht _ (hrec r t))
+          (fun r _ t => revInv_chal_new hM r (hl r) t _ (hrec r t))
+
+/-- Expectations of functions within a pointwise bound of each other:
+`(∀ x, |f x - g x| ≤ h x) → |𝔼 f - 𝔼 g| ≤ 𝔼 h`. -/
+private theorem abs_expect_sub_le_expect {β : Type} (c : ProbComp β) {f g h : β → ℝ}
+    (hb : ∀ x, |f x - g x| ≤ h x) : |expect c f - expect c g| ≤ expect c h := by
+  rw [← expect_sub, abs_le]
+  constructor
+  · have := expect_mono c fun x => (neg_le_of_abs_le (hb x))
+    rw [show (fun x => -h x) = fun x => (-1) * h x from funext fun x => by ring,
+      expect_const_mul] at this
+    linarith
+  · exact expect_mono c fun x => le_of_abs_le (hb x)
+
+/-- **Step 2 of [PS10, Thm 170.4]: fresh decryption queries are rejected.** For `n > 0`,
+`(6n + 4)`-bit records and `2n`-bit challenge queries, and a machine adversary `A` with budget `Q`,
+the acceptance probabilities in the experiments with and without the rejection of fresh pairs,
+averaged over a uniform random tag function `R`, differ by at most `Q / 2^{2n}`.
+
+**Proof sketch.** For each of `A`'s coins and each `R`, identical until bad
+(`abs_prob_ettImpl_rej_sub_le`); average over `R` (`abs_expect_sub_le_expect`) and bound the bad
+probability from the empty table (`expect_prob_bad_le`, `revInv_nil`, `ovr_nil`); average over the
+coins (`abs_expect_sub_le`). -/
+theorem abs_ettAcc_rej_sub_le (hn : 0 < n) (hd : d = 6 * n + 4) (hi2 : ins 2 = n + n)
+    (A : NUPPT) (Q : ℕ) :
+    |expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)))
+          (fun R => ettAcc ins outs d n f R false b A Q) -
+        expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)))
+          (fun R => ettAcc ins outs d n f R true b A Q)| ≤ Q * ((2 : ℝ) ^ (2 * n))⁻¹ := by
+  classical
+  simp only [ettAcc_eq]
+  rw [expect_sample_comm (α := (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (β := A.Coins n),
+    expect_sample_comm (α := (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (β := A.Coins n)]
+  refine abs_expect_sub_le _ fun r => ?_
+  refine (abs_expect_sub_le_expect (h := fun R => prob (simulate (ettBad ins outs d n f R true b)
+      (A.toComp (bitCodec ins outs 1) n Q r) ((none, []), false)) (fun p => p.2.2 = true)) _
+      fun R => ?_).trans ?_
+  · have h := abs_prob_ettImpl_rej_sub_le ins outs d n f R b (A.toComp (bitCodec ins outs 1) n Q r)
+      (fun a => (List.ofFn a).headD false = true) (none, [])
+    rw [prob_eq_expect, prob_eq_expect] at h
+    exact h
+  · have h := expect_prob_bad_le ins outs d n f b hn hd hi2 (A.toComp (bitCodec ins outs 1) n Q r)
+      Q (A.toComp_costBoundedBy _ n Q r) [] (none, []) revInv_nil
+    simp only [ovr_nil] at h
+    exact h
+
+end Induction
+
+end TCSlib.Cryptography.Composability.ETTGame
diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Games.lean b/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Games.lean
new file mode 100644
index 000000000..ffb6451a0
--- /dev/null
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Games.lean
@@ -0,0 +1,460 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Tools
+import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler
+import TCSlib.Cryptography.Foundations.BitLists
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The CCA2 games of the encrypt-then-tag scheme with a pad and a tag function
+
+The scheme of [PS10, Algorithm 169.3] encrypts `m` as `⟨r, ⟨c₁, t⟩⟩` with a fresh `n`-bit nonce
+`r`, the mask `c₁ = m ⊕ f(r)` and the tag `t = g(r ‖ c₁)`, where `f = f_{k₁}` and `g = f_{k₂}` are
+the keyed functions at parameters `n` and `2n`. The proof of [PS10, Theorem 170.4] replaces them by
+other functions; this file states the CCA2 experiment's oracles with `f` and `g` arbitrary, on
+bit-string oracles of arbitrary lengths (`bitSpec ins outs`; oracle `0` is `Enc`, `1` is `Dec`,
+`2` is `Challenge`), with the challenge recorded at width `d`.
+
+**The state** (`St n d`) is the recorded challenge and the list of pairs `r ‖ c₁` of the earlier
+`Enc` answers. **Every query draws one nonce** `r`, used by `Enc` and by a first challenge only
+(`ettImpl`); the answer is then a deterministic function of the nonce (`ettStep`).
+
+* `Enc` on `m` answers `⟨r, ⟨c₁, g(r ‖ c₁)⟩⟩` and adds the pair `r ‖ c₁` to the list.
+* `Dec` on `w` refuses the recorded challenge; otherwise it parses `w = ⟨r, ⟨c₁, t⟩⟩` with the total
+  projections (`wR`, `wC`, `wT`), and answers `⟨1, c₁ ⊕ f(r)⟩` when `r` and `c₁` have `n` bits and
+  `t = g(r ‖ c₁)` (`validW`), else `⊥`. With `rej = true` it also rejects a pair that is not in
+  the list (**fresh pairs are rejected**).
+* `Challenge` on `⟨m₀, m₁⟩` encrypts `m_b` once and records it; later it repeats the record.
+
+The bad flag of the comparison between `rej = false` and `rej = true` (`ettBad`) records a `Dec`
+query that is not refused, has a valid tag and a fresh pair (`hitW`). The nonces drawn in advance
+from tapes give `ettTape`, the experiment run by the PRF reduction.
+
+## Main definitions
+
+* `ETTGame.encW`, `wR`, `wC`, `wT`, `validW`, `decL`, `pairW`: ciphertext words.
+* `ETTGame.St`, `ettStep`, `ettImpl`, `ettBad`, `ettTape`: the experiments.
+* `ETTGame.ettAcc`: a machine's acceptance probability in the experiment.
+
+## Main results
+
+* `ETTGame.ettStep_enc`, `_dec`, `_challenge_some`, `_challenge_none`: the answers.
+* `ETTGame.encW_eq_ctW`: an encryption reads the tag function at its pair only.
+* `ETTGame.length_encW`, `ETTGame.eq_ctW_of_wfW`: ciphertext lengths and canonical parsing.
+* `ETTGame.expect_ettTape`: nonces in advance have the law of fresh nonces.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Algorithm 169.3 and Theorem 170.4 (book pp. 169–171).
+-/
+
+namespace TCSlib.Cryptography.Composability.ETTGame
+
+open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp
+
+/-! ### Ciphertext words -/
+
+section Words
+
+variable {n : ℕ}
+
+/-- The pair `r ‖ c₁` read as a `2n`-bit vector: `pairV n r c = padFin (2n) (r ++ c)`. -/
+def pairV (n : ℕ) (r c : List Bool) : Fin (2 * n) → Bool := padFin (2 * n) (r ++ c)
+
+/-- `pairV n r c = padFin (2n) (r ++ c)`. -/
+theorem pairV_eq (n : ℕ) (r c : List Bool) : pairV n r c = padFin (2 * n) (r ++ c) := rfl
+
+/-- The tag `⟦g (r ‖ c₁)⟧`: `tagL g r c = ⟦g (pairV n r c)⟧`. -/
+def tagL (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (r c : List Bool) : List Bool :=
+  List.ofFn (g (pairV n r c))
+
+/-- `tagL g r c = ⟦g (pairV n r c)⟧`. -/
+theorem tagL_eq (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (r c : List Bool) :
+    tagL g r c = List.ofFn (g (pairV n r c)) := rfl
+
+/-- The ciphertext word `⟨r, ⟨c₁, t⟩⟩`: `ctW r c t = pairEncode r (pairEncode c t)`. -/
+def ctW (r c t : List Bool) : List Bool := pairEncode r (pairEncode c t)
+
+/-- `ctW r c t = ⟨r, ⟨c, t⟩⟩`. -/
+theorem ctW_eq (r c t : List Bool) : ctW r c t = pairEncode r (pairEncode c t) := rfl
+
+/-- The mask `c₁ = m ⊕ ⟦f r⟧`. -/
+def maskL (f : (Fin n → Bool) → (Fin n → Bool)) (r : Fin n → Bool) (m : List Bool) : List Bool :=
+  List.zipWith xor m (List.ofFn (f r))
+
+/-- `maskL f r m = m ⊕ ⟦f r⟧`. -/
+theorem maskL_eq (f : (Fin n → Bool) → (Fin n → Bool)) (r : Fin n → Bool) (m : List Bool) :
+    maskL f r m = List.zipWith xor m (List.ofFn (f r)) := rfl
+
+/-- **The encryption** of the message list `m` with the nonce `r`:
+`⟨r, ⟨c₁, ⟦g (r ‖ c₁)⟧⟩⟩` with `c₁ = maskL f r m`. -/
+def encW (f : (Fin n → Bool) → (Fin n → Bool)) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))
+    (r : Fin n → Bool) (m : List Bool) : List Bool :=
+  ctW (List.ofFn r) (maskL f r m) (tagL g (List.ofFn r) (maskL f r m))
+
+/-- `encW f g r m = ctW ⟦r⟧ c₁ (tagL g ⟦r⟧ c₁)` with `c₁ = maskL f r m`. -/
+theorem encW_eq (f : (Fin n → Bool) → (Fin n → Bool))
+    (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (r : Fin n → Bool) (m : List Bool) :
+    encW f g r m = ctW (List.ofFn r) (maskL f r m) (tagL g (List.ofFn r) (maskL f r m)) := rfl
+
+/-- **An encryption reads the tag function at its pair only:**
+`encW f g r m = ctW ⟦r⟧ c₁ ⟦g (pairV n ⟦r⟧ c₁)⟧` with `c₁ = maskL f r m`. -/
+theorem encW_eq_ctW (f : (Fin n → Bool) → (Fin n → Bool))
+    (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (r : Fin n → Bool) (m : List Bool) :
+    encW f g r m = ctW (List.ofFn r) (maskL f r m)
+      (List.ofFn (g (pairV n (List.ofFn r) (maskL f r m)))) := by
+  rw [encW_eq, tagL_eq]
+
+/-- The nonce field of a word: `wR w = pairFstD w`. -/
+def wR (w : List Bool) : List Bool := pairFstD w
+
+/-- The mask field of a word: `wC w = pairFstD (pairSndD w)`. -/
+def wC (w : List Bool) : List Bool := pairFstD (pairSndD w)
+
+/-- The tag field of a word: `wT w = pairSndD (pairSndD w)`. -/
+def wT (w : List Bool) : List Bool := pairSndD (pairSndD w)
+
+/-- `wR w = pairFstD w`. -/
+theorem wR_eq (w : List Bool) : wR w = pairFstD w := rfl
+
+/-- `wC w = pairFstD (pairSndD w)`. -/
+theorem wC_eq (w : List Bool) : wC w = pairFstD (pairSndD w) := rfl
+
+/-- `wT w = pairSndD (pairSndD w)`. -/
+theorem wT_eq (w : List Bool) : wT w = pairSndD (pairSndD w) := rfl
+
+/-- The fields of a ciphertext word: `wR (ctW r c t) = r`. -/
+theorem wR_ctW (r c t : List Bool) : wR (ctW r c t) = r := by
+  rw [wR_eq, ctW_eq, pairFstD_pairEncode]
+
+/-- The fields of a ciphertext word: `wC (ctW r c t) = c`. -/
+theorem wC_ctW (r c t : List Bool) : wC (ctW r c t) = c := by
+  rw [wC_eq, ctW_eq, pairSndD_pairEncode, pairFstD_pairEncode]
+
+/-- The fields of a ciphertext word: `wT (ctW r c t) = t`. -/
+theorem wT_ctW (r c t : List Bool) : wT (ctW r c t) = t := by
+  rw [wT_eq, ctW_eq, pairSndD_pairEncode, pairSndD_pairEncode]
+
+/-- **Well-formedness:** the nonce and the mask fields have `n` bits,
+`wfW n w = (|wR w| = n && |wC w| = n)`. -/
+def wfW (n : ℕ) (w : List Bool) : Bool :=
+  decide ((wR w).length = n) && decide ((wC w).length = n)
+
+/-- `wfW n w = (decide (|wR w| = n) && decide (|wC w| = n))`. -/
+theorem wfW_eq (n : ℕ) (w : List Bool) :
+    wfW n w = (decide ((wR w).length = n) && decide ((wC w).length = n)) := rfl
+
+/-- **A valid word:** well formed, with the tag `wT w = tagL g (wR w) (wC w)`. -/
+def validW (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (w : List Bool) : Bool :=
+  wfW n w && decide (wT w = tagL g (wR w) (wC w))
+
+/-- `validW g w = (wfW n w && decide (wT w = tagL g (wR w) (wC w)))`. -/
+theorem validW_eq (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (w : List Bool) :
+    validW g w = (wfW n w && decide (wT w = tagL g (wR w) (wC w))) := rfl
+
+/-- **The decryption** of a word, `⟨1, wC w ⊕ ⟦f (wR w)⟧⟩`:
+`decL f w = true :: (wC w ⊕ ⟦f (padFin n (wR w))⟧)`. -/
+def decL (f : (Fin n → Bool) → (Fin n → Bool)) (w : List Bool) : List Bool :=
+  true :: List.zipWith xor (wC w) (List.ofFn (f (padFin n (wR w))))
+
+/-- `decL f w = true :: (wC w ⊕ ⟦f (padFin n (wR w))⟧)`. -/
+theorem decL_eq (f : (Fin n → Bool) → (Fin n → Bool)) (w : List Bool) :
+    decL f w = true :: List.zipWith xor (wC w) (List.ofFn (f (padFin n (wR w)))) := rfl
+
+/-- The pair of a word, as a `2n`-bit vector: `pairW n w = pairV n (wR w) (wC w)`. -/
+def pairW (n : ℕ) (w : List Bool) : Fin (2 * n) → Bool := pairV n (wR w) (wC w)
+
+/-- `pairW n w = pairV n (wR w) (wC w)`. -/
+theorem pairW_eq (n : ℕ) (w : List Bool) : pairW n w = pairV n (wR w) (wC w) := rfl
+
+/-- The mask of an `n`-bit message has `n` bits: `|m| = n → |maskL f r m| = n`. -/
+theorem length_maskL (f : (Fin n → Bool) → (Fin n → Bool)) (r : Fin n → Bool) {m : List Bool}
+    (hm : m.length = n) : (maskL f r m).length = n := by
+  rw [maskL_eq, List.length_zipWith, List.length_ofFn, hm, Nat.min_self]
+
+/-- **The ciphertext length:** an encryption of an `n`-bit message has `6n + 4` bits:
+`|m| = n → |encW f g r m| = 6n + 4`. -/
+theorem length_encW (f : (Fin n → Bool) → (Fin n → Bool))
+    (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (r : Fin n → Bool) {m : List Bool}
+    (hm : m.length = n) : (encW f g r m).length = 6 * n + 4 := by
+  rw [encW_eq, ctW_eq, length_pairEncode, length_pairEncode, List.length_ofFn,
+    length_maskL f r hm, tagL_eq, List.length_ofFn]
+  omega
+
+/-- **Canonical parsing:** for `n > 0`, a well-formed word is the ciphertext word of its fields,
+`w = ctW (wR w) (wC w) (wT w)` (`eq_pairEncode_of_pairFstD_ne`, the nonempty fields). -/
+theorem eq_ctW_of_wfW {w : List Bool} (hn : 0 < n) (hw : wfW n w = true) :
+    w = ctW (wR w) (wC w) (wT w) := by
+  rw [wfW_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hw
+  have h₁ : pairFstD w ≠ [] := by
+    intro h
+    have := hw.1
+    rw [wR_eq, h, List.length_nil] at this
+    omega
+  have h₂ : pairFstD (pairSndD w) ≠ [] := by
+    intro h
+    have := hw.2
+    rw [wC_eq, h, List.length_nil] at this
+    omega
+  rw [ctW_eq, wR_eq, wC_eq, wT_eq, ← eq_pairEncode_of_pairFstD_ne h₂]
+  exact eq_pairEncode_of_pairFstD_ne h₁
+
+/-- An encryption of an `n`-bit message is well formed:
+`|m| = n → wfW n (encW f g r m) = true`. -/
+theorem wfW_encW (f : (Fin n → Bool) → (Fin n → Bool))
+    (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (r : Fin n → Bool) {m : List Bool}
+    (hm : m.length = n) : wfW n (encW f g r m) = true := by
+  rw [wfW_eq, encW_eq, wR_ctW, wC_ctW, List.length_ofFn, length_maskL f r hm]
+  simp
+
+/-- **Pairs of `n`-bit fields determine the fields:** if `|r| = |c| = |r'| = |c'| = n` and
+`pairV n r c = pairV n r' c'`, then `r = r'` and `c = c'`. -/
+theorem eq_of_pairV_eq {r c r' c' : List Bool} (hr : r.length = n) (hc : c.length = n)
+    (hr' : r'.length = n) (hc' : c'.length = n) (h : pairV n r c = pairV n r' c') :
+    r = r' ∧ c = c' := by
+  have h1 : r ++ c = r' ++ c' := by
+    have e : List.ofFn (pairV n r c) = List.ofFn (pairV n r' c') := by rw [h]
+    rw [pairV_eq, pairV_eq, ofFn_padFin_of_length (by rw [List.length_append, hr, hc]; omega),
+      ofFn_padFin_of_length (by rw [List.length_append, hr', hc']; omega)] at e
+    exact e
+  exact List.append_inj h1 (hr.trans hr'.symm)
+
+end Words
+
+/-! ### The state and the decryption answer -/
+
+section State
+
+variable {n d : ℕ}
+
+/-- **The state of the experiment:** the recorded challenge and the pairs of the `Enc` answers,
+`St n d = Option (Fin d → Bool) × List (Fin (2n) → Bool)`. -/
+abbrev St (n d : ℕ) : Type := Option (Fin d → Bool) × List (Fin (2 * n) → Bool)
+
+/-- `St n d = Option (Fin d → Bool) × List (Fin (2n) → Bool)`. -/
+theorem St_eq (n d : ℕ) : St n d = (Option (Fin d → Bool) × List (Fin (2 * n) → Bool)) := rfl
+
+/-- **The refusal test:** the word `w` is the recorded challenge,
+`refW (some c) w = (⟦c⟧ = w)`, `refW none w = false`. -/
+def refW (o : Option (Fin d → Bool)) (w : List Bool) : Bool :=
+  match o with
+  | some c => decide (List.ofFn c = w)
+  | none => false
+
+/-- `refW none w = false`. -/
+theorem refW_none (w : List Bool) : refW (none : Option (Fin d → Bool)) w = false := rfl
+
+/-- `refW (some c) w = decide (⟦c⟧ = w)`. -/
+theorem refW_some (c : Fin d → Bool) (w : List Bool) : refW (some c) w = decide (List.ofFn c = w) :=
+  rfl
+
+/-- **The decryption answer** in state `s`, with fresh pairs rejected when `rej` holds:
+`decAnsW f g rej s w = if !refW s.1 w && validW g w && (!rej || pairW n w ∈ s.2) then decL f w
+else []`, that is, `decL f w` if `w` is not refused, valid, and (when `rej`) its pair is in the
+list; else `[]` (read as `⊥`). -/
+def decAnsW (f : (Fin n → Bool) → (Fin n → Bool)) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))
+    (rej : Bool) (s : St n d) (w : List Bool) : List Bool :=
+  if (!refW s.1 w && validW g w && (!rej || decide (pairW n w ∈ s.2))) = true then decL f w else []
+
+/-- `decAnsW f g rej s w = if !refW s.1 w && validW g w && (!rej || pairW n w ∈ s.2) then decL f w
+else []`. -/
+theorem decAnsW_eq (f : (Fin n → Bool) → (Fin n → Bool))
+    (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (rej : Bool) (s : St n d) (w : List Bool) :
+    decAnsW f g rej s w =
+      if (!refW s.1 w && validW g w && (!rej || decide (pairW n w ∈ s.2))) = true then decL f w
+      else [] := rfl
+
+/-- **The bad event of a decryption query:** not refused, valid, and a fresh pair,
+`hitW g s w = (!refW s.1 w && validW g w && !decide (pairW n w ∈ s.2))`. -/
+def hitW (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (s : St n d) (w : List Bool) : Bool :=
+  !refW s.1 w && validW g w && !decide (pairW n w ∈ s.2)
+
+/-- `hitW g s w = (!refW s.1 w && validW g w && !decide (pairW n w ∈ s.2))`. -/
+theorem hitW_eq (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (s : St n d) (w : List Bool) :
+    hitW g s w = (!refW s.1 w && validW g w && !decide (pairW n w ∈ s.2)) := rfl
+
+/-- **Off the bad event the two decryption answers agree:** `hitW g s w = false →
+decAnsW f g false s w = decAnsW f g true s w`. -/
+theorem decAnsW_agree (f : (Fin n → Bool) → (Fin n → Bool))
+    (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (s : St n d) (w : List Bool)
+    (h : hitW g s w = false) : decAnsW f g false s w = decAnsW f g true s w := by
+  rw [decAnsW_eq, decAnsW_eq]
+  rw [hitW_eq] at h
+  cases hr : refW s.1 w <;> cases hv : validW g w <;>
+    cases hm : decide (pairW n w ∈ s.2) <;> simp_all
+
+end State
+
+/-! ### The experiments -/
+
+section Experiments
+
+variable (ins outs : Fin 3 → ℕ) (d n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool))
+  (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (rej b : Bool)
+
+/-- **One step of the experiment with the nonce `r`** (see the module docstring), with inputs read
+by `⟦·⟧` and answers and records written by `padFin`:
+`ettStep … r 0 m s = (encW f g r m, (s.1, pairV n ⟦r⟧ (maskL f r m) :: s.2))`,
+`ettStep … r 1 w s = (decAnsW f g rej s w, s)`,
+`ettStep … r 2 mm (some c, T) = (⟦c⟧, (some c, T))` and
+`ettStep … r 2 mm (none, T) = (e, (some e, T))` with `e = encW f g r (msgOf n b mm)`. -/
+def ettStep (r : Fin n → Bool) :
+    ∀ i : Fin 3, (Fin (ins i) → Bool) → St n d → (Fin (outs i) → Bool) × St n d
+  | 0, m, s => (padFin _ (encW f g r (List.ofFn m)),
+      (s.1, pairV n (List.ofFn r) (maskL f r (List.ofFn m)) :: s.2))
+  | 1, w, s => (padFin _ (decAnsW f g rej s (List.ofFn w)), s)
+  | 2, _, (some c, T) => (padFin _ (List.ofFn c), (some c, T))
+  | 2, mm, (none, T) => (padFin _ (encW f g r (AdaptiveCPA.msgOf n b (List.ofFn mm))),
+      (some (padFin d (encW f g r (AdaptiveCPA.msgOf n b (List.ofFn mm)))), T))
+
+/-- `Enc` on `m` answers `encW f g r m` and adds the pair `r ‖ maskL f r m` to the list:
+`ettStep … r 0 m s = (padFin _ (encW f g r ⟦m⟧), (s.1, pairV n ⟦r⟧ (maskL f r ⟦m⟧) :: s.2))`. -/
+theorem ettStep_enc (r : Fin n → Bool) (m : Fin (ins 0) → Bool) (s : St n d) :
+    ettStep ins outs d n f g rej b r 0 m s =
+      (padFin _ (encW f g r (List.ofFn m)),
+        (s.1, pairV n (List.ofFn r) (maskL f r (List.ofFn m)) :: s.2)) := rfl
+
+/-- `Dec` on `w` answers `decAnsW f g rej s w` and keeps the state:
+`ettStep … r 1 w s = (padFin _ (decAnsW f g rej s ⟦w⟧), s)`. -/
+theorem ettStep_dec (r : Fin n → Bool) (w : Fin (ins 1) → Bool) (s : St n d) :
+    ettStep ins outs d n f g rej b r 1 w s = (padFin _ (decAnsW f g rej s (List.ofFn w)), s) := rfl
+
+/-- A later challenge repeats the record and keeps the state:
+`ettStep … r 2 mm (some c, T) = (padFin _ ⟦c⟧, (some c, T))`. -/
+theorem ettStep_challenge_some (r : Fin n → Bool) (mm : Fin (ins 2) → Bool) (c : Fin d → Bool)
+    (T : List (Fin (2 * n) → Bool)) :
+    ettStep ins outs d n f g rej b r 2 mm (some c, T) = (padFin _ (List.ofFn c), (some c, T)) := rfl
+
+/-- The first challenge encrypts `m_b` with the nonce `r` and records it:
+`ettStep … r 2 mm (none, T) = (padFin _ e, (some (padFin d e), T))` with
+`e = encW f g r (msgOf n b ⟦mm⟧)`. -/
+theorem ettStep_challenge_none (r : Fin n → Bool) (mm : Fin (ins 2) → Bool)
+    (T : List (Fin (2 * n) → Bool)) :
+    ettStep ins outs d n f g rej b r 2 mm (none, T) =
+      (padFin _ (encW f g r (AdaptiveCPA.msgOf n b (List.ofFn mm))),
+        (some (padFin d (encW f g r (AdaptiveCPA.msgOf n b (List.ofFn mm)))), T)) := rfl
+
+/-- **The experiment with pad function `f` and tag function `g`:** every query draws a nonce `r`
+and takes one `ettStep`,
+`ettImpl … i x s = (sample (Fin n → Bool)).bind fun r => pure (ettStep … r i x s)`. -/
+noncomputable def ettImpl : QueryImpl (bitSpec ins outs) (St n d) unifSpec :=
+  fun i x s => (sample (Fin n → Bool)).bind fun r => .pure (ettStep ins outs d n f g rej b r i x s)
+
+/-- `ettImpl … i x s = (sample (Fin n → Bool)).bind fun r => pure (ettStep … r i x s)`. -/
+theorem ettImpl_apply (i : Fin 3) (x : Fin (ins i) → Bool) (s : St n d) :
+    ettImpl ins outs d n f g rej b i x s =
+      (sample (Fin n → Bool)).bind fun r => .pure (ettStep ins outs d n f g rej b r i x s) := rfl
+
+/-- The experiment draws one coin per query (`freshImpl`):
+`ettImpl … = freshImpl fun i x s r => pure (ettStep … r i x s)`. -/
+theorem ettImpl_eq_freshImpl :
+    ettImpl ins outs d n f g rej b =
+      freshImpl fun i x s r => .pure (ettStep ins outs d n f g rej b r i x s) := by
+  funext i x s
+  rw [ettImpl_apply, freshImpl_apply]
+
+/-- The bad event of a query: a decryption query with `hitW`, `hitQ … 1 w s = hitW g s ⟦w⟧`,
+and `hitQ … 0 m s = hitQ … 2 mm s = false`. -/
+def hitQ : ∀ i : Fin 3, (Fin (ins i) → Bool) → St n d → Bool
+  | 0, _, _ => false
+  | 1, w, s => hitW g s (List.ofFn w)
+  | 2, _, _ => false
+
+/-- An encryption query never raises the bad flag: `hitQ … 0 m s = false`. -/
+theorem hitQ_zero (m : Fin (ins 0) → Bool) (s : St n d) : hitQ ins d n g 0 m s = false := rfl
+
+/-- A decryption query raises the bad flag by `hitW`: `hitQ … 1 w s = hitW g s ⟦w⟧`. -/
+theorem hitQ_one (w : Fin (ins 1) → Bool) (s : St n d) :
+    hitQ ins d n g 1 w s = hitW g s (List.ofFn w) := rfl
+
+/-- A challenge query never raises the bad flag: `hitQ … 2 mm s = false`. -/
+theorem hitQ_two (mm : Fin (ins 2) → Bool) (s : St n d) : hitQ ins d n g 2 mm s = false := rfl
+
+/-- **The experiment with the bad flag:** `ettImpl`, and the flag raised by `hitQ`,
+`ettBad … i x s = (ettImpl … i x s.1).bind fun p =>
+pure (p.1, (p.2, s.2 || hitQ … i x s.1))`. -/
+noncomputable def ettBad : QueryImpl (bitSpec ins outs) (St n d × Bool) unifSpec :=
+  fun i x s => (ettImpl ins outs d n f g rej b i x s.1).bind fun p =>
+    .pure (p.1, (p.2, s.2 || hitQ ins d n g i x s.1))
+
+/-- `ettBad … i x s =
+(ettImpl … i x s.1).bind fun p => pure (p.1, (p.2, s.2 || hitQ … i x s.1))`. -/
+theorem ettBad_apply (i : Fin 3) (x : Fin (ins i) → Bool) (s : St n d × Bool) :
+    ettBad ins outs d n f g rej b i x s =
+      (ettImpl ins outs d n f g rej b i x s.1).bind fun p =>
+        .pure (p.1, (p.2, s.2 || hitQ ins d n g i x s.1)) := rfl
+
+/-- **The experiment with nonces in advance** (`rej = false`): the `j`-th query uses the nonce
+`T j` (`tapeImpl`). -/
+def ettTape (T : ℕ → Fin n → Bool) : QueryImpl (bitSpec ins outs) (St n d × ℕ) unifSpec :=
+  tapeImpl (fun i x s r => .pure (ettStep ins outs d n f g false b r i x s)) T
+
+/-- `ettTape … T i x (s, j) = pure (ettStep … false b (T j) i x s)` with the counter advanced. -/
+theorem ettTape_apply (T : ℕ → Fin n → Bool) (i : Fin 3) (x : Fin (ins i) → Bool) (s : St n d)
+    (j : ℕ) :
+    ettTape ins outs d n f g b T i x (s, j) =
+      .pure ((ettStep ins outs d n f g false b (T j) i x s).1,
+        ((ettStep ins outs d n f g false b (T j) i x s).2, j + 1)) := by
+  rw [ettTape, tapeImpl_apply, OracleComp.pure_bind]
+
+/-- **Nonces in advance have the law of fresh nonces:** for a computation with at most `m`
+queries and `j + m ≤ κ`,
+`𝔼_{T ← ({0,1}^n)^κ} 𝔼[G (simulate (ettTape (extTape T)) c (s, j))] =
+𝔼[G (simulate (ettImpl … false b) c s)]` (`expect_simulate_tapeImpl`). -/
+theorem expect_ettTape (κ : ℕ) {α : Type} (G : α → ℝ) (c : OracleComp (bitSpec ins outs) α)
+    (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : St n d) (j : ℕ) (hj : j + m ≤ κ) :
+    expect (sample (Fin κ → Fin n → Bool))
+        (fun T => expect (simulate (ettTape ins outs d n f g b (AdaptiveCPA.extTape T)) c (s, j))
+          fun p => G p.1) =
+      expect (simulate (ettImpl ins outs d n f g false b) c s) fun p => G p.1 := by
+  rw [ettImpl_eq_freshImpl]
+  exact expect_simulate_tapeImpl _ κ G c m hc s j hj
+
+/-- **The experiment along equal lengths:** for `ins = ins'`, `outs = outs'` and `d = d'`, the
+expected first output bit of a machine's run against `ettImpl` agrees. -/
+theorem expect_ettImpl_transport {ins ins' outs outs' : Fin 3 → ℕ} {d d' : ℕ} (hi : ins = ins')
+    (ho : outs = outs') (hd : d = d') (A : NUPPT) (Q : ℕ) (r : A.Coins n) :
+    expect (simulate (ettImpl ins outs d n f g rej b) (A.toComp (bitCodec ins outs 1) n Q r)
+        (none, [])) (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) =
+      expect (simulate (ettImpl ins' outs' d' n f g rej b) (A.toComp (bitCodec ins' outs' 1) n Q r)
+        (none, [])) (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
+  subst hi ho hd
+  rfl
+
+/-- **The acceptance probability of a machine** in the experiment with `f` and `g`, averaged over
+its coins: `𝔼_r 𝔼[⟦A's output⟧₀ = 1 | simulate (ettImpl … f g rej b) (A.toComp … r) (none, [])]`. -/
+noncomputable def ettAcc (A : NUPPT) (Q : ℕ) : ℝ :=
+  expect (sample (A.Coins n)) fun r =>
+    expect (simulate (ettImpl ins outs d n f g rej b) (A.toComp (bitCodec ins outs 1) n Q r)
+      (none, [])) (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0)
+
+/-- `ettAcc … A Q = 𝔼_r 𝔼[⟦output⟧₀ = 1 | simulate (ettImpl …) (A.toComp … r) (none, [])]`. -/
+theorem ettAcc_eq (A : NUPPT) (Q : ℕ) :
+    ettAcc ins outs d n f g rej b A Q =
+      expect (sample (A.Coins n)) fun r =>
+        expect (simulate (ettImpl ins outs d n f g rej b) (A.toComp (bitCodec ins outs 1) n Q r)
+          (none, [])) (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) :=
+  rfl
+
+/-- The acceptance probability lies in `[0, 1]`; the lower bound: `0 ≤ ettAcc … A Q`. -/
+theorem ettAcc_nonneg (A : NUPPT) (Q : ℕ) : 0 ≤ ettAcc ins outs d n f g rej b A Q := by
+  rw [ettAcc_eq]
+  refine expect_nonneg _ fun r => expect_nonneg _ fun p => ?_
+  split <;> norm_num
+
+/-- The acceptance probability lies in `[0, 1]`; the upper bound: `ettAcc … A Q ≤ 1`. -/
+theorem ettAcc_le_one (A : NUPPT) (Q : ℕ) : ettAcc ins outs d n f g rej b A Q ≤ 1 := by
+  rw [ettAcc_eq]
+  refine (expect_mono _ fun r => ?_).trans (le_of_eq (expect_const _ 1))
+  refine (expect_mono _ fun p => ?_).trans (le_of_eq (expect_const _ 1))
+  split <;> norm_num
+
+end Experiments
+
+end TCSlib.Cryptography.Composability.ETTGame
diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Handler.lean b/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Handler.lean
new file mode 100644
index 000000000..9f54d4dd7
--- /dev/null
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Handler.lean
@@ -0,0 +1,886 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Games
+import TCSlib.Cryptography.Games.Efficiency
+import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
+import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
+import TCSlib.Cryptography.Asymptotic.OneWayLemmas
+import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Reduction
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The handler of the tag-key PRF reduction
+
+Step 1 of [PS10, Theorem 170.4] replaces the tag function `f_{k₂}` by a random function: a
+reduction with oracle access to a function `g` on `2n` bits samples `k₁` itself, runs the CCA2
+adversary and answers its queries with `g` in place of `f_{k₂}`. This file builds that reduction as
+a `Games.InteractiveHandler` (`dHandler`) with one outer oracle (the function), so that T2
+(`Games.exists_interactiveHandlerMachine`) and T4 (`Games.exists_toOracleAdversary_of_bitCodec`)
+make it a next-query machine.
+
+The handler's seed is the key `k₁` followed by `q(n)` nonce tapes of `n` bits (`dSeed`); its state
+counts the queries and records the challenge (`dState`). The mask `c₁ = m ⊕ f_{k₁}(r)` is computed
+with the evaluator `E`.
+- `Enc` on `m`: with the next tape `r`, ask `g` at `r ‖ c₁` and answer `⟨r, ⟨c₁, g(r ‖ c₁)⟩⟩`.
+- `Dec` on `w`: refuse the recorded challenge; if `w = ⟨r, ⟨c₁, t⟩⟩` has `n`-bit `r` and `c₁`, ask
+  `g` at `r ‖ c₁` and answer `⟨1, c₁ ⊕ f_{k₁}(r)⟩` if the answer is `t`; otherwise answer `⊥`.
+- `Challenge` on `⟨m₀, m₁⟩`: the first time, encrypt `m_b` as `Enc` does and record it; later
+  repeat the record.
+Every query advances the counter. The finalization asks nothing and outputs the adversary's bit.
+
+## Main definitions
+
+* `ETTGame.ettCt`, `ettDin`, `ettDout`, `tagLen`, `tagOut`, `dStLen`, `dSeedLen`: the lengths.
+* `ETTGame.recBits`, `dState`, `dSeed`: the encoded state and seed.
+* `ETTGame.dHandler E hE q b`: the handler.
+
+## Main results
+
+* `ETTGame.dHandler_impl_enc`, `_impl_dec_ref`, `_impl_dec_wf`, `_impl_dec_nwf`,
+  `_impl_challenge_some`, `_impl_challenge_none`: its answers on encoded states.
+* `ETTGame.dHandler_finish`, `dHandler_init_hstate`: the finalization and the initial state.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Algorithm 169.3 and Theorem 170.4 (book pp. 169–171).
+-/
+
+namespace TCSlib.Cryptography.Composability.ETTGame
+
+open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
+open TCSlib.Cryptography.Games.InteractiveHandler (rU rW rS rI rX rL rCnt rAns)
+
+/-! ### Lengths -/
+
+/-- The ciphertext length `6n + 4`: `ettCt = 6 · var + 4`, so `ettCt.eval n = 6n + 4`. -/
+def ettCt : PolyExpr := .add (.mul (.const 6) .var) (.const 4)
+
+/-- `ettCt.eval n = 6n + 4`. -/
+theorem ettCt_eval (n : ℕ) : ettCt.eval n = 6 * n + 4 := by
+  rw [ettCt, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_const,
+    PolyExpr.eval_var]
+
+/-- The query lengths: `n`-bit messages to `Enc`, `(6n + 4)`-bit ciphertexts to `Dec`, `2n`-bit
+challenge queries: `ettDin 0 = var`, `ettDin 1 = ettCt` and `ettDin 2 = var + var`. -/
+def ettDin : Fin 3 → PolyExpr
+  | 0 => .var
+  | 1 => ettCt
+  | 2 => .add .var .var
+
+/-- `ettDin 0 = var`. -/
+theorem ettDin_zero : ettDin 0 = .var := rfl
+
+/-- `ettDin 1 = ettCt`. -/
+theorem ettDin_one : ettDin 1 = ettCt := rfl
+
+/-- `ettDin 2 = var + var`. -/
+theorem ettDin_two : ettDin 2 = .add .var .var := rfl
+
+/-- The answer lengths: ciphertexts, `(n + 1)`-bit decryption answers, ciphertexts:
+`ettDout 0 = ettCt`, `ettDout 1 = var + 1` and `ettDout 2 = ettCt`. -/
+def ettDout : Fin 3 → PolyExpr
+  | 0 => ettCt
+  | 1 => .add .var (.const 1)
+  | 2 => ettCt
+
+/-- `ettDout 0 = ettCt`. -/
+theorem ettDout_zero : ettDout 0 = ettCt := rfl
+
+/-- `ettDout 1 = var + 1`. -/
+theorem ettDout_one : ettDout 1 = .add .var (.const 1) := rfl
+
+/-- `ettDout 2 = ettCt`. -/
+theorem ettDout_two : ettDout 2 = ettCt := rfl
+
+/-- The tag length `2n`: `tagLen = 2 · var`, so `tagLen.eval n = 2n`. -/
+def tagLen : PolyExpr := .mul (.const 2) .var
+
+/-- `tagLen.eval n = 2n`. -/
+theorem tagLen_eval (n : ℕ) : tagLen.eval n = 2 * n := by
+  rw [tagLen, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
+
+/-- The outer oracle: `2n`-bit queries and answers, `tagOut j = tagLen` for `j : Fin 1`. -/
+abbrev tagOut : Fin 1 → PolyExpr := fun _ => tagLen
+
+/-- `tagOut j = tagLen`. -/
+theorem tagOut_eq (j : Fin 1) : tagOut j = tagLen := rfl
+
+variable (q : PolyExpr)
+
+/-- The state length `2q + 3 + (6n + 4)`: `dStLen q = 2 · q + 3 + ettCt`, so
+`(dStLen q).eval n = 2 q(n) + 3 + (6n + 4)`. -/
+def dStLen : PolyExpr := .add (.add (.mul (.const 2) q) (.const 3)) ettCt
+
+/-- `dStLen q = 2q + 3 + ettCt`. -/
+theorem dStLen_eq : dStLen q = .add (.add (.mul (.const 2) q) (.const 3)) ettCt := rfl
+
+/-- The seed length `n + q(n) · n`: the key and the tapes, `dSeedLen q = var + q · var`, so
+`(dSeedLen q).eval n = n + q(n) · n`. -/
+def dSeedLen : PolyExpr := .add .var (.mul q .var)
+
+/-- `(dSeedLen q).eval n = n + q(n) · n`. -/
+theorem dSeedLen_eval (n : ℕ) : (dSeedLen q).eval n = n + q.eval n * n := by
+  rw [dSeedLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_var]
+
+/-- The record of the challenge: `1 :: c` once recorded, `0^{1 + ct(n)}` before,
+`recBits n (some c) = true :: ⟦c⟧` and
+`recBits n none = false :: List.replicate (ettCt.eval n) false`. -/
+def recBits (n : ℕ) : Option (Fin (ettCt.eval n) → Bool) → List Bool
+  | none => false :: List.replicate (ettCt.eval n) false
+  | some c => true :: List.ofFn c
+
+/-- `recBits n none = 0^{1 + ct(n)}`. -/
+theorem recBits_none (n : ℕ) : recBits n none = false :: List.replicate (ettCt.eval n) false :=
+  rfl
+
+/-- `recBits n (some c) = 1 :: ⟦c⟧`. -/
+theorem recBits_some (n : ℕ) (c : Fin (ettCt.eval n) → Bool) :
+    recBits n (some c) = true :: List.ofFn c := rfl
+
+/-- The record has `1 + ct(n)` bits: `|recBits n o| = ettCt.eval n + 1`. -/
+theorem length_recBits (n : ℕ) (o : Option (Fin (ettCt.eval n) → Bool)) :
+    (recBits n o).length = ettCt.eval n + 1 := by
+  cases o with
+  | none => rw [recBits_none, List.length_cons, List.length_replicate]
+  | some c => rw [recBits_some, List.length_cons, List.length_ofFn]
+
+/-- **The encoded state** after `j` queries, with the challenge record `o`:
+`⟨1^j, recBits o⟩`, padded with `false` to the state length,
+`dState q n j o = padFin _ (pairEncode (List.replicate j true) (recBits n o))`. -/
+def dState (n j : ℕ) (o : Option (Fin (ettCt.eval n) → Bool)) :
+    Fin ((dStLen q).eval n) → Bool :=
+  padFin _ (pairEncode (List.replicate j true) (recBits n o))
+
+/-- `dState q n j o = padFin _ ⟨1^j, recBits n o⟩`. -/
+theorem dState_eq (n j : ℕ) (o : Option (Fin (ettCt.eval n) → Bool)) :
+    dState q n j o = padFin _ (pairEncode (List.replicate j true) (recBits n o)) := rfl
+
+/-- **The seed** from the key `k₁` and the tape word: `⟦dSeed q n (k, W)⟧ = ⟦k⟧ ++ ⟦W⟧`. -/
+def dSeed (n : ℕ) :
+    (Fin n → Bool) × (Fin (q.eval n * n) → Bool) ≃ (Fin ((dSeedLen q).eval n) → Bool) :=
+  EnsembleLemmas.coinsEquiv (dSeedLen_eval q n)
+
+/-- `dSeed q n = coinsEquiv (dSeedLen_eval q n)`. -/
+theorem dSeed_eq (n : ℕ) : dSeed q n = EnsembleLemmas.coinsEquiv (dSeedLen_eval q n) := rfl
+
+/-- `⟦dSeed q n (k, W)⟧ = ⟦k⟧ ++ ⟦W⟧`. -/
+theorem ofFn_dSeed (n : ℕ) (kW : (Fin n → Bool) × (Fin (q.eval n * n) → Bool)) :
+    List.ofFn (dSeed q n kW) = List.ofFn kW.1 ++ List.ofFn kW.2 :=
+  EnsembleLemmas.ofFn_coinsEquiv _ _
+
+/-- The tape `j` of the tape word: block `j` of `W` (`EnsembleLemmas.blocks`),
+`dTape q n W j hj = blocks (q n) n W ⟨j, hj⟩`. -/
+def dTape (n : ℕ) (W : Fin (q.eval n * n) → Bool) (j : ℕ) (hj : j < q.eval n) : Fin n → Bool :=
+  EnsembleLemmas.blocks (q.eval n) n W ⟨j, hj⟩
+
+/-- `dTape q n W j hj = blocks (q n) n W ⟨j, hj⟩`. -/
+theorem dTape_eq (n : ℕ) (W : Fin (q.eval n * n) → Bool) (j : ℕ) (hj : j < q.eval n) :
+    dTape q n W j hj = EnsembleLemmas.blocks (q.eval n) n W ⟨j, hj⟩ := rfl
+
+/-! ### Strings -/
+
+/-- The fields of an encoded state with `j ≤ q(n)`: the count `1^j`, the flag and the record.
+
+**Proof sketch.** The pair `⟨1^j, recBits n o⟩` fits in the state length (`length_pairEncode`,
+`length_recBits`, `j ≤ q(n)`), so the padding only appends `false`s to its second component
+(`ofFn_padFin_of_le`, `pairEncode_append_right`). The projections then read `1^j` and
+`recBits n o` followed by `false`s; its head is the flag and its next `ct(n)` bits are the record
+(by cases on `o`, `recBits_none`, `recBits_some`). -/
+private theorem fields_dState (n j : ℕ) (o : Option (Fin (ettCt.eval n) → Bool))
+    (hj : j ≤ q.eval n) :
+    pairFstD (List.ofFn (dState q n j o)) = List.replicate j true ∧
+      (pairSndD (List.ofFn (dState q n j o))).headD false = o.isSome ∧
+      ((pairSndD (List.ofFn (dState q n j o))).drop 1).take (ettCt.eval n) =
+        (recBits n o).drop 1 := by
+  have hlen : (pairEncode (List.replicate j true) (recBits n o)).length ≤ (dStLen q).eval n := by
+    rw [length_pairEncode, List.length_replicate, length_recBits, dStLen_eq, PolyExpr.eval_add,
+      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_const]
+    omega
+  rw [dState_eq, Collection.ofFn_padFin_of_le hlen, ← GGMRed.pairEncode_append_right]
+  rw [pairFstD_pairEncode, pairSndD_pairEncode]
+  refine ⟨rfl, ?_, ?_⟩
+  · cases o <;> rfl
+  · cases o with
+    | none =>
+      rw [recBits_none, List.cons_append, List.drop_succ_cons, List.drop_zero, List.drop_succ_cons,
+        List.drop_zero, List.take_left' List.length_replicate]
+    | some c =>
+      rw [recBits_some, List.cons_append, List.drop_succ_cons, List.drop_zero, List.drop_succ_cons,
+        List.drop_zero, List.take_left' List.length_ofFn]
+
+/-! ### The round function -/
+
+/-- The challenge flag of the state. -/
+private def rFlag (w : List Bool) : Bool := (pairSndD (rS w)).headD false
+/-- The recorded challenge of the state. -/
+private def rRec (w : List Bool) : List Bool :=
+  ((pairSndD (rS w)).drop 1).take (ettCt.eval (rU w).length)
+/-- The key `k₁` of the seed. -/
+private def rKey (w : List Bool) : List Bool := (rW w).take (rU w).length
+/-- Tape `j` of the seed, `j` the query count. -/
+private def rNonce (w : List Bool) : List Bool :=
+  ((rW w).drop ((rU w).length + (rCnt w).length * (rU w).length)).take (rU w).length
+/-- The mask `m ⊕ E⟨k₁, r⟩` with the tape `r`. -/
+private def rMask (E : List Bool → List Bool) (w m : List Bool) : List Bool :=
+  List.zipWith xor m (E (pairEncode (rKey w) (rNonce w)))
+/-- The ciphertext `⟨r, ⟨c₁, y⟩⟩` with the tape `r` and the outer answer `y`. -/
+private def rCt (E : List Bool → List Bool) (w m : List Bool) : List Bool :=
+  pairEncode (rNonce w) (pairEncode (rMask E w m) (rAns w))
+/-- The selected challenge message `m_b`. -/
+private def rMsg (b : Bool) (w : List Bool) : List Bool :=
+  if b then (rX w).drop (rU w).length else (rX w).take (rU w).length
+/-- Whether the decryption query `⟨r, ⟨c₁, t⟩⟩` has `n`-bit `r` and `c₁`. -/
+private def rWF (w : List Bool) : Bool :=
+  decide ((pairFstD (rX w)).length = (rU w).length) &&
+    decide ((pairFstD (pairSndD (rX w))).length = (rU w).length)
+/-- Whether the decryption query is the recorded challenge. -/
+private def rRef (w : List Bool) : Bool := rFlag w && decide (rX w = rRec w)
+/-- The decryption `⟨1, c₁ ⊕ E⟨k₁, r⟩⟩` of the query. -/
+private def rDec (E : List Bool → List Bool) (w : List Bool) : List Bool :=
+  true :: List.zipWith xor (pairFstD (pairSndD (rX w))) (E (pairEncode (rKey w) (pairFstD (rX w))))
+/-- Whether the outer answer is the tag of the query. -/
+private def rOK (w : List Bool) : Bool := decide (rAns w = pairSndD (pairSndD (rX w)))
+/-- The all-`false` decryption answer `⊥`. -/
+private def rZero (w : List Bool) : List Bool :=
+  List.replicate ((PolyExpr.add .var (.const 1)).eval (rU w).length) false
+/-- The new state after a query: count `j + 1`, record `t`. -/
+private def rNew (w t : List Bool) : List Bool :=
+  EnsembleLemmas.padL ((dStLen q).eval (rU w).length) (pairEncode (true :: rCnt w) t)
+
+/-- **One round of the handler** (see the module docstring), for the challenge bit `b`. A first
+round of `Enc`, of a first challenge or of a well-formed decryption asks the outer oracle; the
+second round, with the answer `y` in the log, returns the answer and the new state. -/
+private def dRun (E : List Bool → List Bool) (b : Bool) (w : List Bool) : List Bool :=
+  if (rI w).headD false then
+    if ((rI w).drop 1).headD false then
+      if rFlag w then pairEncode [true] (rRec w ++ rNew q w (true :: rRec w))
+      else if decide (rL w = []) then
+        pairEncode [false] (pairEncode [] (rNonce w ++ rMask E w (rMsg b w)))
+      else pairEncode [true] (rCt E w (rMsg b w) ++ rNew q w (true :: rCt E w (rMsg b w)))
+    else
+      if rRef w then pairEncode [true] (rZero w ++ rNew q w (rFlag w :: rRec w))
+      else if rWF w then
+        if decide (rL w = []) then
+          pairEncode [false] (pairEncode [] (pairFstD (rX w) ++ pairFstD (pairSndD (rX w))))
+        else pairEncode [true]
+          ((if rOK w then rDec E w else rZero w) ++ rNew q w (rFlag w :: rRec w))
+      else pairEncode [true] (rZero w ++ rNew q w (rFlag w :: rRec w))
+  else
+    if decide (rL w = []) then pairEncode [false] (pairEncode [] (rNonce w ++ rMask E w (rX w)))
+    else pairEncode [true] (rCt E w (rX w) ++ rNew q w (rFlag w :: rRec w))
+
+/-- The round function is polynomial-time.
+
+**Proof sketch.** Pair projections; the key and the tape by `pairTakePoly`, `unaryMulPair` and
+`dropPrefixByLength`; the mask and the decryption by the evaluator `E` and `pairXor`; the tests
+by `lenEq_poly` and `pairEq`; the padded new state by `padL`; and `polyTimeComputable_ite` for
+the cases. -/
+private theorem polyTimeComputable_dRun {E : List Bool → List Bool} (hE : PolyTimeComputable E)
+    (b : Bool) : PolyTimeComputable (dRun q E b) := by
+  have hF := polyTimeComputable_pairFstD
+  have hD := polyTimeComputable_pairSndD
+  have hU : PolyTimeComputable rU := InteractiveHandler.polyTimeComputable_rU
+  have hW : PolyTimeComputable rW := InteractiveHandler.polyTimeComputable_rW
+  have hS : PolyTimeComputable rS := InteractiveHandler.polyTimeComputable_rS
+  have hI : PolyTimeComputable rI := InteractiveHandler.polyTimeComputable_rI
+  have hX : PolyTimeComputable rX := InteractiveHandler.polyTimeComputable_rX
+  have hL : PolyTimeComputable rL := InteractiveHandler.polyTimeComputable_rL
+  have hCnt : PolyTimeComputable rCnt := InteractiveHandler.polyTimeComputable_rCnt
+  have hY : PolyTimeComputable rAns := InteractiveHandler.polyTimeComputable_rAns
+  have hT : PolyTimeComputable fun w => pairSndD (rS w) := hD.comp hS
+  have hFlag : PolyTimeComputable fun w => [rFlag w] := polyTimeComputable_headD.comp hT
+  have hRec : PolyTimeComputable rRec :=
+    ((polyTimeComputable_pairTakePoly ettCt).comp
+      (hU.pairEncode (polyTimeComputable_tail.comp hT))).congr fun w => by
+        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]; rfl
+  have hKey : PolyTimeComputable rKey :=
+    ((polyTimeComputable_pairTakePoly .var).comp (hU.pairEncode hW)).congr fun w => by
+      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
+        PolyExpr.eval_var]; rfl
+  have hU1 : PolyTimeComputable fun w => List.replicate (rU w).length true :=
+    ((polyTimeComputable_unaryPoly .var).comp hU).congr fun w => by
+      simp only [Function.comp_apply, PolyExpr.eval_var]
+  have hOff : PolyTimeComputable fun w =>
+      List.replicate ((rU w).length + (rCnt w).length * (rU w).length) true :=
+    (hU1.append (OneWay.polyTimeComputable_unaryMulPair.comp (hCnt.pairEncode hU))).congr
+      fun w => by
+        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
+          List.replicate_add]
+  have hDrop : PolyTimeComputable fun w =>
+      (rW w).drop ((rU w).length + (rCnt w).length * (rU w).length) :=
+    (polyTimeComputable_dropPrefixByLength.comp (hOff.pairEncode hW)).congr fun w => by
+      simp only [Function.comp_apply, PrefixByLength.drop_def, pairFstD_pairEncode,
+        pairSndD_pairEncode, List.length_replicate]
+  have hNonce : PolyTimeComputable rNonce :=
+    ((polyTimeComputable_pairTakePoly .var).comp (hU.pairEncode hDrop)).congr fun w => by
+      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
+        PolyExpr.eval_var]; rfl
+  have hXor : ∀ {m p : List Bool → List Bool}, PolyTimeComputable m → PolyTimeComputable p →
+      PolyTimeComputable fun w => List.zipWith xor (m w) (p w) := fun hm hp =>
+    (polyTimeComputable_pairXor.comp (hm.pairEncode hp)).congr fun w => by
+      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
+  have hMask : ∀ {m : List Bool → List Bool}, PolyTimeComputable m →
+      PolyTimeComputable fun w => rMask E w (m w) := fun hm =>
+    hXor hm (hE.comp (hKey.pairEncode hNonce))
+  have hCt : ∀ {m : List Bool → List Bool}, PolyTimeComputable m →
+      PolyTimeComputable fun w => rCt E w (m w) := fun hm =>
+    hNonce.pairEncode ((hMask hm).pairEncode hY)
+  have hMsg : PolyTimeComputable (rMsg b) :=
+    polyTimeComputable_ite (polyTimeComputable_const [b])
+      (((polyTimeComputable_pairDropPoly .var).comp (hU.pairEncode hX)).congr fun w => by
+        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
+          PolyExpr.eval_var])
+      (((polyTimeComputable_pairTakePoly .var).comp (hU.pairEncode hX)).congr fun w => by
+        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
+          PolyExpr.eval_var])
+  have hR : PolyTimeComputable fun w => pairFstD (rX w) := hF.comp hX
+  have hC : PolyTimeComputable fun w => pairFstD (pairSndD (rX w)) := (hF.comp hD).comp hX
+  have hTg : PolyTimeComputable fun w => pairSndD (pairSndD (rX w)) := (hD.comp hD).comp hX
+  have hWF : PolyTimeComputable fun w => [rWF w] :=
+    polyTimeComputable_and (EffFill.lenEq_poly hR hU) (EffFill.lenEq_poly hC hU)
+  have hEq : ∀ {u v : List Bool → List Bool}, PolyTimeComputable u → PolyTimeComputable v →
+      PolyTimeComputable fun w => [decide (u w = v w)] := fun hu hv =>
+    (polyTimeComputable_pairEq.comp (hu.pairEncode hv)).congr fun w => by
+      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
+  have hRef : PolyTimeComputable fun w => [rRef w] := polyTimeComputable_and hFlag (hEq hX hRec)
+  have hOK : PolyTimeComputable fun w => [rOK w] := hEq hY hTg
+  have hDec : PolyTimeComputable (rDec E) :=
+    (polyTimeComputable_const [true]).append (hXor hC (hE.comp (hKey.pairEncode hR)))
+  have hZero : PolyTimeComputable rZero := EnsembleLemmas.polyTimeComputable_zeros _ hU
+  have hNew : ∀ {t : List Bool → List Bool}, PolyTimeComputable t →
+      PolyTimeComputable fun w => rNew q w (t w) := fun ht =>
+    EnsembleLemmas.polyTimeComputable_padL (dStLen q) hU
+      (((polyTimeComputable_const [true]).append hCnt).pairEncode ht)
+  have hRet : ∀ {f : List Bool → List Bool}, PolyTimeComputable f →
+      PolyTimeComputable fun w => pairEncode [true] (f w) := fun hf =>
+    (polyTimeComputable_const [true]).pairEncode hf
+  have hQry : ∀ {f : List Bool → List Bool}, PolyTimeComputable f →
+      PolyTimeComputable fun w => pairEncode [false] (pairEncode [] (f w)) := fun hf =>
+    (polyTimeComputable_const [false]).pairEncode ((polyTimeComputable_const []).pairEncode hf)
+  have cNil : PolyTimeComputable fun w => [decide (rL w = [])] := polyTimeComputable_isNil.comp hL
+  have hKeep : PolyTimeComputable fun w => rFlag w :: rRec w :=
+    (hFlag.append hRec).congr fun _ => rfl
+  have hTrueRec : PolyTimeComputable fun w => true :: rRec w :=
+    (polyTimeComputable_const [true]).append hRec
+  have hChal := polyTimeComputable_ite hFlag (hRet (hRec.append (hNew hTrueRec)))
+    (polyTimeComputable_ite cNil (hQry (hNonce.append (hMask hMsg)))
+      (hRet ((hCt hMsg).append (hNew ((polyTimeComputable_const [true]).append (hCt hMsg))))))
+  have hDecR := polyTimeComputable_ite hRef (hRet (hZero.append (hNew hKeep)))
+    (polyTimeComputable_ite hWF
+      (polyTimeComputable_ite cNil (hQry (hR.append hC))
+        (hRet ((polyTimeComputable_ite hOK hDec hZero).append (hNew hKeep))))
+      (hRet (hZero.append (hNew hKeep))))
+  have hEnc := polyTimeComputable_ite cNil (hQry (hNonce.append (hMask hX)))
+    (hRet ((hCt hX).append (hNew hKeep)))
+  exact polyTimeComputable_ite (polyTimeComputable_headD.comp hI)
+    (polyTimeComputable_ite (polyTimeComputable_headD.comp (polyTimeComputable_tail.comp hI))
+      hChal hDecR) hEnc
+
+/-- The finalization's round: output `A`'s bit, `⟨[true], a⟩` on `⟨ctx, ⟨s, ⟨a, L⟩⟩⟩`. -/
+private def dFin (w : List Bool) : List Bool :=
+  pairEncode [true] (pairFstD (pairSndD (pairSndD w)))
+
+/-- The finalization's round is polynomial-time. -/
+private theorem polyTimeComputable_dFin : PolyTimeComputable dFin :=
+  (polyTimeComputable_const [true]).pairEncode
+    (polyTimeComputable_pairFstD.comp
+      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
+
+/-! ### The handler -/
+
+/-- **The handler of the tag-key PRF reduction** for the evaluator `E`, the budget `q` and the
+challenge bit `b`: state `dState j o` (initially `j = 0` and no record), seed `dSeed` (the key and
+`q(n)` tapes), one outer call per inner query, the adversary run on the empty input, and the
+finalization outputting the adversary's bit. -/
+noncomputable def dHandler (E : List Bool → List Bool) (hE : PolyTimeComputable E) (b : Bool) :
+    InteractiveHandler 3 ettDin ettDout 1 tagOut tagOut where
+  stateLen := dStLen q
+  seedLen := dSeedLen q
+  perCall := .const 1
+  init n := dState q n 0 none
+  run := dRun q E b
+  poly := polyTimeComputable_dRun q hE b
+  advIn _ := []
+  advIn_poly := polyTimeComputable_const []
+  outLen := .const 1
+  finCall := .const 0
+  finRun := dFin
+  finRun_poly := polyTimeComputable_dFin
+
+attribute [simps (config := { isSimp := false }) stateLen seedLen perCall outLen finCall]
+  dHandler
+
+variable (E : List Bool → List Bool) (hE : PolyTimeComputable E) (b : Bool)
+
+/-- The encoded state at the handler's state type: `dHState … n j o = dState q n j o`. -/
+def dHState (n j : ℕ) (o : Option (Fin (ettCt.eval n) → Bool)) :
+    Fin ((dHandler q E hE b).stateLen.eval n) → Bool :=
+  dState q n j o
+
+/-- `dHState q E hE b n j o = dState q n j o`. -/
+theorem dHState_eq (n j : ℕ) (o : Option (Fin (ettCt.eval n) → Bool)) :
+    dHState q E hE b n j o = dState q n j o := rfl
+
+/-- The seed at the handler's seed type: `dHSeed … n = dSeed q n`. -/
+def dHSeed (n : ℕ) :
+    (Fin n → Bool) × (Fin (q.eval n * n) → Bool) ≃
+      (Fin ((dHandler q E hE b).seedLen.eval n) → Bool) :=
+  dSeed q n
+
+/-- `dHSeed q E hE b n = dSeed q n`. -/
+theorem dHSeed_eq (n : ℕ) : dHSeed q E hE b n = dSeed q n := rfl
+
+/-- The initial state is the encoded `(0, none)`:
+`(dHandler q E hE b).init n = dHState q E hE b n 0 none`. -/
+theorem dHandler_init_hstate (n : ℕ) : (dHandler q E hE b).init n = dHState q E hE b n 0 none :=
+  rfl
+
+/-- The adversary's input is empty: `(dHandler q E hE b).advInput n z ω = []`. -/
+theorem dHandler_advInput (n : ℕ) (z : List Bool)
+    (ω : Fin ((dHandler q E hE b).seedLen.eval n) → Bool) :
+    (dHandler q E hE b).advInput n z ω = [] := by
+  rw [InteractiveHandler.advInput_eq]
+  rfl
+
+/-- The finalization outputs the adversary's bit and asks nothing:
+`(dHandler q E hE b).finish n z ω s a = pure (padFin _ ⟦a⟧)`. -/
+theorem dHandler_finish (n : ℕ) (z : List Bool)
+    (ω : Fin ((dHandler q E hE b).seedLen.eval n) → Bool)
+    (s : Fin ((dHandler q E hE b).stateLen.eval n) → Bool)
+    (a : Fin ((PolyExpr.const 1).eval n) → Bool) :
+    (dHandler q E hE b).finish n z ω s a =
+      .pure (padFin ((dHandler q E hE b).outLen.eval n) (List.ofFn a)) := by
+  rw [InteractiveHandler.finish_eq]
+  have h0 : (dHandler q E hE b).finCall.eval n = 0 := by
+    rw [dHandler_finCall, PolyExpr.eval_const]
+  rw [h0]
+  refine buildComp_zero_of_ret ?_
+  show decodeBitMove _ _ _ (dFin _) = _
+  rw [dFin, InteractiveHandler.finInput_eq, pairSndD_pairEncode, pairSndD_pairEncode,
+    pairFstD_pairEncode]
+  have hw : List.ofFn (padFin ((dHandler q E hE b).outLen.eval n) (List.ofFn a)) =
+      List.ofFn a :=
+    ofFn_padFin_of_length (by rw [List.length_ofFn, dHandler_outLen])
+  exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).symm.trans
+    (decodeBitMove_ret _ _ _ _)
+
+/-! ### Answers of the handler -/
+
+/-- `⟦dHSeed … n (k, W)⟧ = ⟦k⟧ ++ ⟦W⟧`. -/
+theorem ofFn_dHSeed (n : ℕ) (kW : (Fin n → Bool) × (Fin (q.eval n * n) → Bool)) :
+    List.ofFn (dHSeed q E hE b n kW) = List.ofFn kW.1 ++ List.ofFn kW.2 :=
+  ofFn_dSeed q n kW
+
+/-- `⟦dHState … n j o⟧ = ⟦dState q n j o⟧`. -/
+theorem ofFn_dHState (n j : ℕ) (o : Option (Fin (ettCt.eval n) → Bool)) :
+    List.ofFn (dHState q E hE b n j o) = List.ofFn (dState q n j o) :=
+  rfl
+
+section Answers
+
+variable (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
+  (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
+    List.ofFn (F n s x))
+  (n : ℕ) (z : List Bool) (k : Fin n → Bool) (W : Fin (q.eval n * n) → Bool)
+
+/-- The round input of a call, field by field, on an encoded state with `j < q(n)` and the seed
+`dHSeed (k, W)`.
+
+**Proof sketch.** The generic readers of the round input (`rU_input`, `rS_input`, `rI_input`,
+`rX_input`, `rL_input`, `rW_input`, `rCnt_input`) give the parameter, state, oracle index, query,
+log, seed word `⟦k⟧ ++ ⟦W⟧` (`ofFn_dHSeed`) and count; `fields_dState` gives the count `1^j`, the
+flag and the record. The key is then the first `n` bits of the seed word, and the nonce is the
+`n` bits after the offset `n + j · n`, which is block `j` of `W` (`take_drop_ofFn_blocks`). -/
+private theorem fields_input {i : Fin 3} (x L : List Bool) (j : ℕ)
+    (o : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n) :
+    let w := InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
+      (List.ofFn (dHState q E hE b n j o)) i x L
+    rU w = List.replicate n true ∧ rS w = List.ofFn (dHState q E hE b n j o) ∧
+      rI w = List.replicate i true ∧ rX w = x ∧ rL w = L ∧ rCnt w = List.replicate j true ∧
+      rFlag w = o.isSome ∧ rRec w = (recBits n o).drop 1 ∧ rKey w = List.ofFn k ∧
+      rNonce w = List.ofFn (dTape q n W j hj) := by
+  obtain ⟨h₁, h₂, h₃⟩ := fields_dState q n j o hj.le
+  have hW : rW (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
+      (List.ofFn (dHState q E hE b n j o)) i x L) = List.ofFn k ++ List.ofFn W := by
+    rw [InteractiveHandler.rW_input, ofFn_dHSeed]
+  have hS : rS (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
+      (List.ofFn (dHState q E hE b n j o)) i x L) = List.ofFn (dState q n j o) :=
+    (InteractiveHandler.rS_input ..).trans (ofFn_dHState q E hE b n j o)
+  have hcnt : rCnt (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
+      (List.ofFn (dHState q E hE b n j o)) i x L) = List.replicate j true := by
+    rw [InteractiveHandler.rCnt_input, ofFn_dHState, h₁]
+  have hU := InteractiveHandler.rU_input (k := 3) n z (List.ofFn (dHSeed q E hE b n (k, W)))
+    (List.ofFn (dHState q E hE b n j o)) i x L
+  refine ⟨hU, InteractiveHandler.rS_input .., InteractiveHandler.rI_input ..,
+    InteractiveHandler.rX_input .., InteractiveHandler.rL_input .., hcnt, ?_, ?_, ?_, ?_⟩
+  · rw [rFlag, hS, h₂]
+  · rw [rRec, hS, hU, List.length_replicate, h₃]
+  · rw [rKey, hW, hU, List.length_replicate, List.take_left' List.length_ofFn]
+  · rw [rNonce, hW, hU, hcnt, List.length_replicate, List.length_replicate, List.drop_append,
+      List.drop_eq_nil_of_le (by rw [List.length_ofFn]; omega), List.nil_append, List.length_ofFn,
+      Nat.add_sub_cancel_left, dTape_eq]
+    exact EnsembleLemmas.take_drop_ofFn_blocks W j hj
+
+/-- The new state after a query from `dState j o`, with record `t`. -/
+private theorem rNew_fields {i : Fin 3} (x L : List Bool) (j : ℕ)
+    (o o' : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n) :
+    rNew q (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
+        (List.ofFn (dHState q E hE b n j o)) i x L) (recBits n o') =
+      List.ofFn (dHState q E hE b n (j + 1) o') := by
+  obtain ⟨hU, -, -, -, -, hCnt, -, -, -, -⟩ := fields_input q E hE b n z k W (i := i) x L j o hj
+  rw [rNew, hU, hCnt, List.length_replicate, ofFn_dHState, dState_eq,
+    EnsembleLemmas.ofFn_padFin_eq_padL, List.replicate_succ]
+
+/-- The flag and the record rebuild the record bits: `rFlag :: rRec = recBits o`. -/
+private theorem recBits_fields (o : Option (Fin (ettCt.eval n) → Bool)) :
+    o.isSome :: (recBits n o).drop 1 = recBits n o := by
+  cases o <;> rfl
+
+/-- The outer answer recorded in a one-entry log (any oracle index word `u`). -/
+private theorem rY_one (w : List Bool) (u x' y : List Bool)
+    (hL : rL w = pairEncode (pairEncode u (pairEncode x' y)) []) : rAns w = y := by
+  rw [InteractiveHandler.rAns_eq, hL, pairFstD_pairEncode, pairSndD_pairEncode,
+    pairSndD_pairEncode]
+
+/-- A one-entry log is not empty. -/
+private theorem log_ne_nil (u x' y : List Bool) :
+    decide (pairEncode (pairEncode u (pairEncode x' y)) [] = []) = false :=
+  decide_eq_false (pairEncode_ne_nil _ _)
+
+include hFE in
+/-- The mask computed with the evaluator: `m ⊕ E⟨⟦k⟧, ⟦r⟧⟩ = maskL (F n k) r m`. -/
+private theorem mask_eval (r : Fin n → Bool) (m : List Bool) :
+    List.zipWith xor m (E (pairEncode (List.ofFn k) (List.ofFn r))) = maskL (F n k) r m := by
+  rw [hFE, maskL_eq]
+
+/-- The outer query word of a pair `r ‖ c₁` with `|r| = |c₁| = n`, read at `2n` bits. -/
+private theorem ofFn_padFin_pair {r c : List Bool} (hr : r.length = n) (hc : c.length = n) :
+    List.ofFn (padFin ((tagOut 0).eval n) (r ++ c)) = r ++ c :=
+  ofFn_padFin_of_length (by rw [List.length_append, hr, hc, tagOut_eq, tagLen_eval]; omega)
+
+/-- The all-`false` decryption answer as a list. -/
+private theorem rZero_fields (w : List Bool) (hU : rU w = List.replicate n true) :
+    rZero w = List.ofFn (padFin ((ettDout 1).eval n) ([] : List Bool)) := by
+  rw [rZero, hU, List.length_replicate, padFin_nil, ofFn_zeroBits, ettDout_one]
+
+/-- The ciphertext of a nonce and an `n`-bit mask with a `2n`-bit tag has `6n + 4` bits. -/
+private theorem length_ctW_tag {r c t : List Bool} (hr : r.length = n) (hc : c.length = n)
+    (ht : t.length = 2 * n) : (ctW r c t).length = ettCt.eval n := by
+  rw [ctW_eq, length_pairEncode, length_pairEncode, hr, hc, ht, ettCt_eval]
+  omega
+
+include hFE in
+/-- **Encryption with the next tape:** from `dState j o` with `j < q(n)`, the query `m` asks the
+outer oracle at `r ‖ c₁` with the tape `r` and `c₁ = maskL f_k r m`; its answer `y` gives the
+ciphertext `⟨r, ⟨c₁, y⟩⟩` and the state `dState (j + 1) o`.
+
+**Proof sketch.** Read the round input field by field (`fields_input`); the first round, with an
+empty log, asks `r ‖ c₁` (`mask_eval`); the second, with the answer `y` in the log (`rY_one`),
+returns `⟨r, ⟨c₁, y⟩⟩` and the state with count `j + 1` (`rNew_fields`);
+`InteractiveHandler.impl_of_query` assembles the two rounds. -/
+theorem dHandler_impl_enc (x : Fin ((ettDin 0).eval n) → Bool) (j : ℕ)
+    (o : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n) :
+    (dHandler q E hE b).impl n z (dHSeed q E hE b n (k, W)) 0 x (dHState q E hE b n j o) =
+      .query 0 (padFin _ (List.ofFn (dTape q n W j hj) ++
+          maskL (F n k) (dTape q n W j hj) (List.ofFn x))) fun y =>
+        .pure (padFin _ (ctW (List.ofFn (dTape q n W j hj))
+          (maskL (F n k) (dTape q n W j hj) (List.ofFn x)) (List.ofFn y)),
+          dHState q E hE b n (j + 1) o) := by
+  have hx : (List.ofFn x).length = n := by rw [List.length_ofFn, ettDin_zero, PolyExpr.eval_var]
+  have hm := length_maskL (F n k) (dTape q n W j hj) hx
+  refine InteractiveHandler.impl_of_query _ n z _ x _ 0 _ _ _
+    (by rw [dHandler_perCall, PolyExpr.eval_const]) ?_ ?_
+  · show dRun q E b _ = _
+    obtain ⟨-, -, hI, hX, hL, -, -, -, hK, hN⟩ :=
+      fields_input q E hE b n z k W (i := 0) (List.ofFn x) [] j o hj
+    rw [dRun, hI, Fin.val_zero, List.replicate_zero, List.headD_nil, if_neg Bool.false_ne_true,
+      hL, if_pos (decide_eq_true rfl), rMask, hK, hN, hX, mask_eval E F hFE n k,
+      ofFn_padFin_pair n List.length_ofFn hm]
+    rfl
+  · intro y
+    show dRun q E b _ = _
+    simp only [Fin.val_zero, List.replicate_zero]
+    obtain ⟨-, -, hI, hX, hL, -, hFlag, hRec, hK, hN⟩ :=
+      fields_input q E hE b n z k W (i := 0) (List.ofFn x)
+        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((tagOut 0).eval n)
+          (List.ofFn (dTape q n W j hj) ++ maskL (F n k) (dTape q n W j hj) (List.ofFn x))))
+          (List.ofFn y))) []) j o hj
+    have hY := rY_one _ _ _ _ hL
+    have hct : List.ofFn (padFin ((ettDout 0).eval n) (ctW (List.ofFn (dTape q n W j hj))
+        (maskL (F n k) (dTape q n W j hj) (List.ofFn x)) (List.ofFn y))) =
+        ctW (List.ofFn (dTape q n W j hj)) (maskL (F n k) (dTape q n W j hj) (List.ofFn x))
+          (List.ofFn y) :=
+      ofFn_padFin_of_length (by
+        rw [length_ctW_tag n List.length_ofFn hm (by rw [List.length_ofFn, tagOut_eq, tagLen_eval]),
+          ettDout_zero])
+    rw [dRun, hI, Fin.val_zero, List.replicate_zero, List.headD_nil, if_neg Bool.false_ne_true, hL,
+      log_ne_nil,
+      if_neg Bool.false_ne_true, hct, rCt, rMask, hK, hN, hX, hY, mask_eval E F hFE n k, hFlag,
+      hRec, recBits_fields, rNew_fields q E hE b n z k W (i := 0) _ _ j o o hj, ctW_eq]
+
+/-- **A refused decryption:** from `dState j o` with the query the recorded challenge, the answer
+is `⊥` and the state is `dState (j + 1) o`: for `j < q(n)` and `refW o ⟦x⟧ = true`,
+`(dHandler …).impl n z (dHSeed … (k, W)) 1 x (dHState … j o) =
+pure (padFin _ [], dHState … (j + 1) o)`.
+
+**Proof sketch.** The handler answers in one round (`impl_of_ret`). Reading the round input
+(`fields_input`), `href` makes the refusal test true (`rRef`, by cases on `o`: with the record `c`,
+`⟦x⟧ = ⟦c⟧`), so `dRun` takes the refusal branch: the answer `rZero = ⊥` (`rZero_fields`) and the
+new state with count `j + 1` and the same record bits (`recBits_fields`, `rNew_fields`). -/
+theorem dHandler_impl_dec_ref (x : Fin ((ettDin 1).eval n) → Bool) (j : ℕ)
+    (o : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n)
+    (href : refW o (List.ofFn x) = true) :
+    (dHandler q E hE b).impl n z (dHSeed q E hE b n (k, W)) 1 x (dHState q E hE b n j o) =
+      .pure (padFin _ [], dHState q E hE b n (j + 1) o) := by
+  refine InteractiveHandler.impl_of_ret _ n z _ x _ _ _ ?_
+  show dRun q E b _ = _
+  obtain ⟨hU, -, hI, hX, -, -, hFlag, hRec, -, -⟩ :=
+    fields_input q E hE b n z k W (i := 1) (List.ofFn x) [] j o hj
+  have hRef : rRef (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
+      (List.ofFn (dHState q E hE b n j o)) (1 : Fin 3) (List.ofFn x) []) = true := by
+    rw [rRef, hFlag, hRec, hX]
+    cases o with
+    | none => rw [refW_none] at href; cases href
+    | some c =>
+      rw [refW_some, decide_eq_true_eq] at href
+      rw [recBits_some, List.drop_succ_cons, List.drop_zero, href]
+      simp
+  rw [dRun, hI, Fin.val_one, List.replicate_one, List.headD_cons, if_pos rfl, List.drop_succ_cons,
+    List.drop_zero, List.headD_nil, if_neg Bool.false_ne_true, hRef, if_pos rfl,
+    rZero_fields n _ hU, hFlag, hRec, recBits_fields,
+    rNew_fields q E hE b n z k W (i := 1) _ _ j o o hj]
+
+include hFE in
+/-- **A well-formed decryption:** from `dState j o` with a query `w = ⟦x⟧` that is not refused and
+has `n`-bit `wR w` and `wC w`, the query asks the outer oracle at `wR w ‖ wC w`; its answer `y`
+gives `decL f_k w` if `⟦y⟧ = wT w` and `⊥` otherwise; the state is `dState (j + 1) o`.
+
+**Proof sketch.** On every log the refusal test is false (`href`, by cases on `o`) and the
+well-formedness test is true (`hwf`), by `fields_input`. With `impl_of_query`: the first round,
+with an empty log, asks `wR w ++ wC w` (`ofFn_padFin_pair`); the second, with the answer `y` in
+the log (`rY_one`), compares `⟦y⟧` with `wT w` (`rOK`) and answers `rDec`, which is `decL f_k w` by
+`hFE` on the `n`-bit nonce, or `rZero = ⊥` (`rZero_fields`); the new state is `dState (j + 1) o`
+(`recBits_fields`, `rNew_fields`). -/
+theorem dHandler_impl_dec_wf (x : Fin ((ettDin 1).eval n) → Bool) (j : ℕ)
+    (o : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n)
+    (href : refW o (List.ofFn x) = false) (hwf : wfW n (List.ofFn x) = true) :
+    (dHandler q E hE b).impl n z (dHSeed q E hE b n (k, W)) 1 x (dHState q E hE b n j o) =
+      .query 0 (padFin _ (wR (List.ofFn x) ++ wC (List.ofFn x))) fun y =>
+        .pure (padFin _ (if List.ofFn y = wT (List.ofFn x) then decL (F n k) (List.ofFn x)
+          else []), dHState q E hE b n (j + 1) o) := by
+  have hwf' := hwf
+  rw [wfW_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hwf'
+  have hRef : ∀ L, rRef (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
+      (List.ofFn (dHState q E hE b n j o)) (1 : Fin 3) (List.ofFn x) L) = false := by
+    intro L
+    obtain ⟨-, -, -, hX, -, -, hFlag, hRec, -, -⟩ :=
+      fields_input q E hE b n z k W (i := 1) (List.ofFn x) L j o hj
+    rw [rRef, hFlag, hRec, hX]
+    cases o with
+    | none => rfl
+    | some c =>
+      rw [refW_some, decide_eq_false_iff_not] at href
+      rw [recBits_some, List.drop_succ_cons, List.drop_zero, Option.isSome_some, Bool.true_and,
+        decide_eq_false_iff_not]
+      exact fun h => href h.symm
+  have hWF : ∀ L, rWF (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
+      (List.ofFn (dHState q E hE b n j o)) (1 : Fin 3) (List.ofFn x) L) = true := by
+    intro L
+    obtain ⟨hU, -, -, hX, -, -, -, -, -, -⟩ :=
+      fields_input q E hE b n z k W (i := 1) (List.ofFn x) L j o hj
+    rw [rWF, hU, hX, List.length_replicate, ← wC_eq, ← wR_eq, hwf'.1, hwf'.2]
+    simp
+  refine InteractiveHandler.impl_of_query _ n z _ x _ 0 _ _ _
+    (by rw [dHandler_perCall, PolyExpr.eval_const]) ?_ ?_
+  · show dRun q E b _ = _
+    obtain ⟨-, -, hI, hX, hL, -, -, -, -, -⟩ :=
+      fields_input q E hE b n z k W (i := 1) (List.ofFn x) [] j o hj
+    rw [dRun, hI, Fin.val_one, List.replicate_one, List.headD_cons, if_pos rfl,
+      List.drop_succ_cons, List.drop_zero, List.headD_nil, if_neg Bool.false_ne_true, hRef,
+      if_neg Bool.false_ne_true, hWF, if_pos rfl, hL, if_pos (decide_eq_true rfl), hX,
+      ← wC_eq, ← wR_eq, ofFn_padFin_pair n hwf'.1 hwf'.2]
+    rfl
+  · intro y
+    show dRun q E b _ = _
+    simp only [Fin.val_zero, List.replicate_zero]
+    obtain ⟨hU, -, hI, hX, hL, -, hFlag, hRec, hK, -⟩ :=
+      fields_input q E hE b n z k W (i := 1) (List.ofFn x)
+        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((tagOut 0).eval n)
+          (wR (List.ofFn x) ++ wC (List.ofFn x)))) (List.ofFn y))) []) j o hj
+    have hY := rY_one _ _ _ _ hL
+    have hans : (if rOK (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
+        (List.ofFn (dHState q E hE b n j o)) (1 : Fin 3) (List.ofFn x)
+        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((tagOut 0).eval n)
+          (wR (List.ofFn x) ++ wC (List.ofFn x)))) (List.ofFn y))) [])) = true then
+        rDec E (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
+          (List.ofFn (dHState q E hE b n j o)) (1 : Fin 3) (List.ofFn x)
+          (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((tagOut 0).eval n)
+            (wR (List.ofFn x) ++ wC (List.ofFn x)))) (List.ofFn y))) []))
+        else rZero (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
+          (List.ofFn (dHState q E hE b n j o)) (1 : Fin 3) (List.ofFn x)
+          (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((tagOut 0).eval n)
+            (wR (List.ofFn x) ++ wC (List.ofFn x)))) (List.ofFn y))) []))) =
+        List.ofFn (padFin ((ettDout 1).eval n) (if List.ofFn y = wT (List.ofFn x) then
+          decL (F n k) (List.ofFn x) else [])) := by
+      rw [rOK, hY, hX, ← wT_eq]
+      by_cases ht : List.ofFn y = wT (List.ofFn x)
+      · rw [if_pos (decide_eq_true ht), if_pos ht, rDec, hK, hX, ← wC_eq, ← wR_eq]
+        have hr : wR (List.ofFn x) = List.ofFn (padFin n (wR (List.ofFn x))) :=
+          (ofFn_padFin_of_length hwf'.1).symm
+        rw [hr, hFE, ← decL_eq, ofFn_padFin_of_length]
+        rw [decL_eq, List.length_cons, List.length_zipWith, List.length_ofFn, hwf'.2, Nat.min_self,
+          ettDout_one, PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]
+      · rw [if_neg (by rw [decide_eq_true_eq]; exact ht), if_neg ht, rZero_fields n _ hU]
+    rw [dRun, hI, Fin.val_one, List.replicate_one, List.headD_cons, if_pos rfl,
+      List.drop_succ_cons, List.drop_zero, List.headD_nil, if_neg Bool.false_ne_true, hRef,
+      if_neg Bool.false_ne_true, hWF, if_pos rfl, hL, log_ne_nil, if_neg Bool.false_ne_true, hans,
+      hFlag, hRec, recBits_fields, rNew_fields q E hE b n z k W (i := 1) _ _ j o o hj]
+
+/-- **A malformed decryption:** from `dState j o` with a query that is not refused and not well
+formed, the answer is `⊥` and the state is `dState (j + 1) o`: for `j < q(n)`,
+`refW o ⟦x⟧ = false` and `wfW n ⟦x⟧ = false`,
+`(dHandler …).impl n z (dHSeed … (k, W)) 1 x (dHState … j o) =
+pure (padFin _ [], dHState … (j + 1) o)`.
+
+**Proof sketch.** As for `dHandler_impl_dec_ref`, the handler answers in one round
+(`impl_of_ret`); now the refusal test is false (`href`, by cases on `o`) and the well-formedness
+test is false (`hwf`, through `wfW_eq`), so `dRun` takes the malformed branch: the answer
+`rZero = ⊥` and the state `dState (j + 1) o` (`rZero_fields`, `recBits_fields`, `rNew_fields`). -/
+theorem dHandler_impl_dec_nwf (x : Fin ((ettDin 1).eval n) → Bool) (j : ℕ)
+    (o : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n)
+    (href : refW o (List.ofFn x) = false) (hwf : wfW n (List.ofFn x) = false) :
+    (dHandler q E hE b).impl n z (dHSeed q E hE b n (k, W)) 1 x (dHState q E hE b n j o) =
+      .pure (padFin _ [], dHState q E hE b n (j + 1) o) := by
+  refine InteractiveHandler.impl_of_ret _ n z _ x _ _ _ ?_
+  show dRun q E b _ = _
+  obtain ⟨hU, -, hI, hX, -, -, hFlag, hRec, -, -⟩ :=
+    fields_input q E hE b n z k W (i := 1) (List.ofFn x) [] j o hj
+  have hRef : rRef (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
+      (List.ofFn (dHState q E hE b n j o)) (1 : Fin 3) (List.ofFn x) []) = false := by
+    rw [rRef, hFlag, hRec, hX]
+    cases o with
+    | none => rfl
+    | some c =>
+      rw [refW_some, decide_eq_false_iff_not] at href
+      rw [recBits_some, List.drop_succ_cons, List.drop_zero, Option.isSome_some, Bool.true_and,
+        decide_eq_false_iff_not]
+      exact fun h => href h.symm
+  have hWF : rWF (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
+      (List.ofFn (dHState q E hE b n j o)) (1 : Fin 3) (List.ofFn x) []) = false := by
+    rw [rWF, hU, hX, List.length_replicate, ← wC_eq, ← wR_eq, ← wfW_eq, hwf]
+  rw [dRun, hI, Fin.val_one, List.replicate_one, List.headD_cons, if_pos rfl, List.drop_succ_cons,
+    List.drop_zero, List.headD_nil, if_neg Bool.false_ne_true, hRef, if_neg Bool.false_ne_true,
+    hWF, if_neg Bool.false_ne_true, rZero_fields n _ hU, hFlag, hRec, recBits_fields,
+    rNew_fields q E hE b n z k W (i := 1) _ _ j o o hj]
+
+/-- **A recorded challenge is repeated:** from `dState j (some c)`, a challenge is answered `c`
+and the state is `dState (j + 1) (some c)`: for `j < q(n)`,
+`(dHandler …).impl n z (dHSeed … (k, W)) 2 x (dHState … j (some c)) =
+pure (padFin _ ⟦c⟧, dHState … (j + 1) (some c))`. -/
+theorem dHandler_impl_challenge_some (x : Fin ((ettDin 2).eval n) → Bool) (j : ℕ)
+    (c : Fin (ettCt.eval n) → Bool) (hj : j < q.eval n) :
+    (dHandler q E hE b).impl n z (dHSeed q E hE b n (k, W)) 2 x (dHState q E hE b n j (some c)) =
+      .pure (padFin _ (List.ofFn c), dHState q E hE b n (j + 1) (some c)) := by
+  refine InteractiveHandler.impl_of_ret _ n z _ x _ _ _ ?_
+  show dRun q E b _ = _
+  obtain ⟨-, -, hI, -, -, -, hFlag, hRec, -, -⟩ :=
+    fields_input q E hE b n z k W (i := 2) (List.ofFn x) [] j (some c) hj
+  have hc : List.ofFn (padFin ((ettDout 2).eval n) (List.ofFn c)) = List.ofFn c :=
+    ofFn_padFin_of_length (by rw [List.length_ofFn, ettDout_two])
+  have hrec : true :: (recBits n (some c)).drop 1 = recBits n (some c) := rfl
+  rw [dRun, hI, hFlag, hRec]
+  simp only [show List.replicate ((2 : Fin 3) : ℕ) true = [true, true] from rfl, List.headD_cons,
+    List.drop_succ_cons, List.drop_zero, if_true, Option.isSome_some]
+  rw [hrec, rNew_fields q E hE b n z k W (i := 2) _ _ j (some c) (some c) hj, hc, recBits_some,
+    List.drop_succ_cons, List.drop_zero]
+
+include hFE in
+/-- **The first challenge with the next tape:** from `dState j none` with `j < q(n)`, the
+challenge `⟨m₀, m₁⟩` asks the outer oracle at `r ‖ c₁` with the tape `r` and
+`c₁ = maskL f_k r m_b`; its answer `y` gives the ciphertext `c = ⟨r, ⟨c₁, y⟩⟩`, recorded in the
+state `dState (j + 1) (some c)`.
+
+**Proof sketch.** The selected message read from the round input is `msgOf n b ⟦x⟧` (`rMsg`,
+`fields_input`), of `n` bits. With `impl_of_query`: the first round, with no record (flag false)
+and an empty log, asks `r ‖ c₁` with the tape `r` (`mask_eval`, `ofFn_padFin_pair`); the second,
+with `y` in the log (`rY_one`), returns `c = ⟨r, ⟨c₁, y⟩⟩` (`ctW_eq`, of `6n + 4` bits by
+`length_ctW_tag`) and the new state with count `j + 1` and the record bits
+`true :: ⟦c⟧ = recBits n (some c)` (`rNew_fields`). -/
+theorem dHandler_impl_challenge_none (x : Fin ((ettDin 2).eval n) → Bool) (j : ℕ)
+    (hj : j < q.eval n) :
+    (dHandler q E hE b).impl n z (dHSeed q E hE b n (k, W)) 2 x (dHState q E hE b n j none) =
+      .query 0 (padFin _ (List.ofFn (dTape q n W j hj) ++
+          maskL (F n k) (dTape q n W j hj) (AdaptiveCPA.msgOf n b (List.ofFn x)))) fun y =>
+        .pure (padFin _ (ctW (List.ofFn (dTape q n W j hj))
+            (maskL (F n k) (dTape q n W j hj) (AdaptiveCPA.msgOf n b (List.ofFn x)))
+            (List.ofFn y)),
+          dHState q E hE b n (j + 1) (some (padFin (ettCt.eval n)
+            (ctW (List.ofFn (dTape q n W j hj))
+              (maskL (F n k) (dTape q n W j hj) (AdaptiveCPA.msgOf n b (List.ofFn x)))
+              (List.ofFn y))))) := by
+  have hmsg : (AdaptiveCPA.msgOf n b (List.ofFn x)).length = n := by
+    have hx : (List.ofFn x).length = n + n := by
+      rw [List.length_ofFn, ettDin_two, PolyExpr.eval_add, PolyExpr.eval_var]
+    rw [AdaptiveCPA.msgOf_eq]
+    cases b <;> simp [hx]
+  have hm := length_maskL (F n k) (dTape q n W j hj) hmsg
+  have hMsg : ∀ L, rMsg b (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
+      (List.ofFn (dHState q E hE b n j none)) (2 : Fin 3) (List.ofFn x) L) =
+      AdaptiveCPA.msgOf n b (List.ofFn x) := by
+    intro L
+    obtain ⟨hU, -, -, hX, -, -, -, -, -, -⟩ :=
+      fields_input q E hE b n z k W (i := 2) (List.ofFn x) L j none hj
+    rw [rMsg, hU, hX, List.length_replicate, AdaptiveCPA.msgOf_eq]
+  refine InteractiveHandler.impl_of_query _ n z _ x _ 0 _ _ _
+    (by rw [dHandler_perCall, PolyExpr.eval_const]) ?_ ?_
+  · show dRun q E b _ = _
+    obtain ⟨-, -, hI, -, hL, -, hFlag, -, hK, hN⟩ :=
+      fields_input q E hE b n z k W (i := 2) (List.ofFn x) [] j none hj
+    rw [dRun, hI, hFlag, hL]
+    simp only [show List.replicate ((2 : Fin 3) : ℕ) true = [true, true] from rfl, List.headD_cons,
+      List.drop_succ_cons, List.drop_zero, if_true, Option.isSome_none, Bool.false_eq_true,
+      if_false, decide_true]
+    rw [hMsg, rMask, hK, hN, mask_eval E F hFE n k, ofFn_padFin_pair n List.length_ofFn hm]
+    rfl
+  · intro y
+    show dRun q E b _ = _
+    simp only [Fin.val_zero, List.replicate_zero]
+    obtain ⟨-, -, hI, -, hL, -, hFlag, -, hK, hN⟩ :=
+      fields_input q E hE b n z k W (i := 2) (List.ofFn x)
+        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((tagOut 0).eval n)
+          (List.ofFn (dTape q n W j hj) ++
+            maskL (F n k) (dTape q n W j hj) (AdaptiveCPA.msgOf n b (List.ofFn x)))))
+          (List.ofFn y))) []) j none hj
+    have hY := rY_one _ _ _ _ hL
+    have hlen := length_ctW_tag n (List.length_ofFn (f := dTape q n W j hj)) hm
+      (by rw [List.length_ofFn, tagOut_eq, tagLen_eval] : (List.ofFn y).length = 2 * n)
+    have hct : List.ofFn (padFin ((ettDout 2).eval n) (ctW (List.ofFn (dTape q n W j hj))
+        (maskL (F n k) (dTape q n W j hj) (AdaptiveCPA.msgOf n b (List.ofFn x)))
+        (List.ofFn y))) =
+        ctW (List.ofFn (dTape q n W j hj))
+          (maskL (F n k) (dTape q n W j hj) (AdaptiveCPA.msgOf n b (List.ofFn x)))
+          (List.ofFn y) :=
+      ofFn_padFin_of_length (by rw [hlen, ettDout_two])
+    have hrec : true :: ctW (List.ofFn (dTape q n W j hj))
+        (maskL (F n k) (dTape q n W j hj) (AdaptiveCPA.msgOf n b (List.ofFn x))) (List.ofFn y) =
+        recBits n (some (padFin (ettCt.eval n) (ctW (List.ofFn (dTape q n W j hj))
+          (maskL (F n k) (dTape q n W j hj) (AdaptiveCPA.msgOf n b (List.ofFn x)))
+          (List.ofFn y)))) := by
+      rw [recBits_some, ofFn_padFin_of_length hlen]
+    rw [dRun, hI, hFlag, hL]
+    simp only [show List.replicate ((2 : Fin 3) : ℕ) true = [true, true] from rfl, List.headD_cons,
+      List.drop_succ_cons, List.drop_zero, if_true, Option.isSome_none, Bool.false_eq_true,
+      if_false]
+    rw [log_ne_nil, if_neg Bool.false_ne_true, hMsg, hct, rCt, rMask, hK, hN, hY,
+      mask_eval E F hFE n k, ← ctW_eq, hrec,
+      rNew_fields q E hE b n z k W (i := 2) _ _ j none _ hj]
+
+end Answers
+
+end TCSlib.Cryptography.Composability.ETTGame
diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Lazy.lean b/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Lazy.lean
new file mode 100644
index 000000000..2e7251a01
--- /dev/null
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Lazy.lean
@@ -0,0 +1,630 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Games
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The rejecting experiment with lazily sampled tags
+
+Step 3 of [PS10, Theorem 170.4] simulates the experiment that rejects fresh decryption queries by
+a CPA adversary against the §3.9 scheme. That adversary cannot hold a random function on `2n`
+bits; it samples the tags lazily, one tape per query, and answers decryption queries from the table
+of its earlier answers. This file states that lazy experiment (`ettLazy`, with tapes in advance
+`ettLazyTape`) and proves that it has the law of the rejecting experiment with a uniform random
+tag function (`expect_ettImpl_lazy`).
+
+**The lazy state** (`LSt n d`) is the recorded challenge and the table of the `Enc′` answers, newest
+first: each entry is the pair `r ‖ c₁`, its tag and the encrypted message.
+- `Enc′` on `m` with the nonce `r`: the tag of the pair `p = r ‖ c₁` is the table's tag at `p` if
+  `p` is in the table, else the challenge's tag if `p` is the challenge's pair, else the query's
+  tape (`tagOf`); the entry `(p, tag, m)` is added.
+- `Dec′` on `w` refuses the record; a well-formed `w` whose pair is in the table and whose tag is
+  the table's tag gets `⟨1, m⟩` with the table's message, every other word `⊥` (`lazyDec`).
+- `Challenge` on `⟨m₀, m₁⟩`: the first time, as `Enc′` on `m_b` (without an entry), recorded.
+
+**The law** (`expect_ettImpl_lazy`). Average the rejecting experiment over `R` with the table's tags
+written over it (`tagTbl`, `ovr`). A new pair moves `R`'s value into the table
+(`expect_sample_ovr`); a pair in the table has its tag; a decryption with a listed pair reads the
+table's tag, and its answer `⟨1, c₁ ⊕ f(r)⟩` is the table's message, because the entry's pair is
+`r ‖ (m ⊕ f(r))` with an `n`-bit `m` (`LInv`).
+
+## Main definitions
+
+* `ETTGame.LEntry`, `LSt`, `keysL`, `lookL`, `tagOf`, `lazyDec`, `tagTbl`, `LInv`.
+* `ETTGame.lazyStep`, `ettLazyK`, `ettLazy`, `ettLazyTape`.
+
+## Main results
+
+* `ETTGame.expect_ettImpl_lazy`: the rejecting experiment with a random tag function is the lazy
+  experiment.
+* `ETTGame.expect_ettLazyTape`: the lazy experiment with tapes in advance.
+* `ETTGame.tagTbl_none_nil`, `ETTGame.lInv_nil`: the empty lazy state.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 170.4 (book pp. 170–171).
+-/
+
+namespace TCSlib.Cryptography.Composability.ETTGame
+
+open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp
+
+/-! ### Tables -/
+
+section Tables
+
+variable {n d : ℕ}
+
+/-- An entry of the lazy table: a pair, its tag and the message of the encryption,
+`LEntry n = (Fin (2n) → Bool) × (Fin (2n) → Bool) × List Bool`. -/
+abbrev LEntry (n : ℕ) : Type := (Fin (2 * n) → Bool) × (Fin (2 * n) → Bool) × List Bool
+
+/-- `LEntry n = pair × tag × message`. -/
+theorem LEntry_eq (n : ℕ) :
+    LEntry n = ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool) × List Bool) := rfl
+
+/-- The lazy state: the recorded challenge and the table, newest entry first,
+`LSt n d = Option (Fin d → Bool) × List (LEntry n)`. -/
+abbrev LSt (n d : ℕ) : Type := Option (Fin d → Bool) × List (LEntry n)
+
+/-- `LSt n d = Option (Fin d → Bool) × List (LEntry n)`. -/
+theorem LSt_eq (n d : ℕ) : LSt n d = (Option (Fin d → Bool) × List (LEntry n)) := rfl
+
+/-- The pairs of the table: `keysL L = L.map Prod.fst`. -/
+def keysL (L : List (LEntry n)) : List (Fin (2 * n) → Bool) := L.map Prod.fst
+
+/-- `keysL L = L.map Prod.fst`. -/
+theorem keysL_eq (L : List (LEntry n)) : keysL L = L.map Prod.fst := rfl
+
+/-- **The table's entry at a pair:** the first (newest) entry with the pair `p`, if any,
+`lookL L p = if p ∈ keysL L then some (L.getD ((keysL L).idxOf p) default) else none`. -/
+def lookL (L : List (LEntry n)) (p : Fin (2 * n) → Bool) : Option (LEntry n) :=
+  if p ∈ keysL L then some (L.getD ((keysL L).idxOf p) default) else none
+
+/-- `lookL L p = if p ∈ keysL L then some (L.getD ((keysL L).idxOf p) default) else none`. -/
+theorem lookL_eq (L : List (LEntry n)) (p : Fin (2 * n) → Bool) :
+    lookL L p = if p ∈ keysL L then some (L.getD ((keysL L).idxOf p) default) else none := rfl
+
+/-- **The tag of a pair:** the table's, else the challenge's at its pair, else none:
+`tagOf s p = some e.2.1` if `lookL s.2 p = some e`; else
+`tagOf s p = some (padFin (2n) (wT ⟦c⟧))` if `s.1 = some c` and `pairW n ⟦c⟧ = p`; else
+`tagOf s p = none`. -/
+def tagOf (s : LSt n d) (p : Fin (2 * n) → Bool) : Option (Fin (2 * n) → Bool) :=
+  match lookL s.2 p with
+  | some e => some e.2.1
+  | none =>
+    match s.1 with
+    | some c => if pairW n (List.ofFn c) = p then some (padFin (2 * n) (wT (List.ofFn c))) else none
+    | none => none
+
+/-- `tagOf s p` unfolded: the table's tag, else the challenge's at its pair,
+`tagOf s p = some e.2.1` if `lookL s.2 p = some e`; else
+`tagOf s p = some (padFin (2n) (wT ⟦c⟧))` if `s.1 = some c` and `pairW n ⟦c⟧ = p`; else
+`tagOf s p = none`. -/
+theorem tagOf_eq (s : LSt n d) (p : Fin (2 * n) → Bool) :
+    tagOf s p = match lookL s.2 p with
+      | some e => some e.2.1
+      | none =>
+        match s.1 with
+        | some c =>
+          if pairW n (List.ofFn c) = p then some (padFin (2 * n) (wT (List.ofFn c))) else none
+        | none => none := rfl
+
+/-- **The lazy decryption answer:** `⊥` on the record; on a well-formed word whose pair is in the
+table with the word's tag, `⟨1, m⟩` with the table's message; `⊥` otherwise:
+`lazyDec s w = true :: e.2.2` if `refW s.1 w = false`, `wfW n w = true`,
+`lookL s.2 (pairW n w) = some e` and `⟦e.2.1⟧ = wT w`; else `lazyDec s w = []`. -/
+def lazyDec (s : LSt n d) (w : List Bool) : List Bool :=
+  if (!refW s.1 w && wfW n w) = true then
+    match lookL s.2 (pairW n w) with
+    | some e => if List.ofFn e.2.1 = wT w then true :: e.2.2 else []
+    | none => []
+  else []
+
+/-- `lazyDec s w` unfolded: `lazyDec s w = true :: e.2.2` if `refW s.1 w = false`,
+`wfW n w = true`, `lookL s.2 (pairW n w) = some e` and `⟦e.2.1⟧ = wT w`; else
+`lazyDec s w = []`. -/
+theorem lazyDec_eq (s : LSt n d) (w : List Bool) :
+    lazyDec s w = if (!refW s.1 w && wfW n w) = true then
+      match lookL s.2 (pairW n w) with
+      | some e => if List.ofFn e.2.1 = wT w then true :: e.2.2 else []
+      | none => []
+    else [] := rfl
+
+/-- **The tag table of a lazy state:** the entries' tags, newest first, then the challenge's,
+`tagTbl s = s.2.map (fun e => (e.1, e.2.1)) ++ [(pairW n ⟦c⟧, padFin (2n) (wT ⟦c⟧))]` for
+`s.1 = some c`, and `tagTbl s = s.2.map (fun e => (e.1, e.2.1))` for `s.1 = none`. -/
+def tagTbl (s : LSt n d) : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool)) :=
+  s.2.map (fun e => (e.1, e.2.1)) ++
+    match s.1 with
+    | some c => [(pairW n (List.ofFn c), padFin (2 * n) (wT (List.ofFn c)))]
+    | none => []
+
+/-- `tagTbl s` unfolded:
+`tagTbl s = s.2.map (fun e => (e.1, e.2.1)) ++ [(pairW n ⟦c⟧, padFin (2n) (wT ⟦c⟧))]` for
+`s.1 = some c`, and `tagTbl s = s.2.map (fun e => (e.1, e.2.1)) ++ []` for `s.1 = none`. -/
+theorem tagTbl_eq (s : LSt n d) :
+    tagTbl s = s.2.map (fun e => (e.1, e.2.1)) ++
+      match s.1 with
+      | some c => [(pairW n (List.ofFn c), padFin (2 * n) (wT (List.ofFn c)))]
+      | none => [] := rfl
+
+/-- The empty table has no pairs: `keysL [] = []`. -/
+theorem keysL_nil : keysL ([] : List (LEntry n)) = [] := by
+  rw [keysL_eq, List.map_nil]
+
+/-- The empty lazy state has the empty tag table: `tagTbl (none, []) = []`. -/
+theorem tagTbl_none_nil : tagTbl ((none, []) : LSt n d) = [] := by
+  rw [tagTbl_eq, List.map_nil, List.nil_append]
+
+end Tables
+
+/-! ### Tags as a table written over a function -/
+
+section Ovr
+
+variable {n d : ℕ}
+
+/-- Writing a concatenation is writing its parts: `ovr (A ++ B) R = ovr A (ovr B R)`. -/
+theorem ovr_append (A B : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool)))
+    (R : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) : ovr (A ++ B) R = ovr A (ovr B R) := by
+  induction A with
+  | nil => rw [List.nil_append, ovr_nil]
+  | cons e A ih =>
+    obtain ⟨p, y⟩ := e
+    rw [List.cons_append, ovr_cons, ovr_cons, ih]
+
+/-- The entry at a listed pair has that pair:
+`p ∈ keysL L → (L.getD ((keysL L).idxOf p) _).1 = p`. -/
+theorem getD_idxOf_fst {L : List (LEntry n)} {p : Fin (2 * n) → Bool} (hp : p ∈ keysL L) :
+    (L.getD ((keysL L).idxOf p) default).1 = p := by
+  induction L with
+  | nil => simp [keysL_eq] at hp
+  | cons e L ih =>
+    rw [keysL_eq, List.map_cons, List.idxOf_cons]
+    by_cases h : e.1 = p
+    · simp [h]
+    · have hp' : p ∈ keysL L := by
+        rw [keysL_eq, List.map_cons, List.mem_cons] at hp
+        exact hp.resolve_left (Ne.symm h)
+      simp only [show (e.1 == p) = false from beq_false_of_ne h, cond_false, List.getD_cons_succ]
+      exact ih hp'
+
+/-- **On a listed pair the tag table gives the newest entry's tag:**
+`p ∈ keysL L → ovr (L-tags ++ X) R p = (L.getD ((keysL L).idxOf p) _).2.1`. -/
+theorem ovr_tags_of_mem (L : List (LEntry n))
+    (X : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool)))
+    (R : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) {p : Fin (2 * n) → Bool}
+    (hp : p ∈ keysL L) :
+    ovr (L.map (fun e => (e.1, e.2.1)) ++ X) R p = (L.getD ((keysL L).idxOf p) default).2.1 := by
+  induction L with
+  | nil => simp [keysL_eq] at hp
+  | cons e L ih =>
+    rw [List.map_cons, List.cons_append, ovr_cons, keysL_eq, List.map_cons, List.idxOf_cons]
+    by_cases h : e.1 = p
+    · subst h
+      simp
+    · have hp' : p ∈ keysL L := by
+        rw [keysL_eq, List.map_cons, List.mem_cons] at hp
+        exact hp.resolve_left (Ne.symm h)
+      rw [Function.update_of_ne (Ne.symm h)]
+      simp only [show (e.1 == p) = false from beq_false_of_ne h, cond_false, List.getD_cons_succ]
+      exact ih hp'
+
+/-- The keys of the tag table: the listed pairs, then the challenge's pair,
+`(tagTbl s).map Prod.fst = keysL s.2 ++ [pairW n ⟦c⟧]` for `s.1 = some c`, and
+`(tagTbl s).map Prod.fst = keysL s.2 ++ []` for `s.1 = none`. -/
+theorem keys_tagTbl (s : LSt n d) :
+    (tagTbl s).map Prod.fst = keysL s.2 ++
+      match s.1 with
+      | some c => [pairW n (List.ofFn c)]
+      | none => [] := by
+  rw [tagTbl_eq, List.map_append, List.map_map, keysL_eq]
+  congr 1
+  cases s.1 <;> rfl
+
+/-- **`tagOf` reads the tag table:** for every `R`, `tagOf s p` is `ovr (tagTbl s) R p` on the keys
+of the tag table, and none elsewhere,
+`tagOf s p = if p ∈ (tagTbl s).map Prod.fst then some (ovr (tagTbl s) R p) else none`. -/
+theorem tagOf_eq_ovr (s : LSt n d) (p : Fin (2 * n) → Bool)
+    (R : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) :
+    tagOf s p = if p ∈ (tagTbl s).map Prod.fst then some (ovr (tagTbl s) R p) else none := by
+  rw [tagOf_eq, keys_tagTbl, tagTbl_eq]
+  by_cases hp : p ∈ keysL s.2
+  · rw [lookL_eq, if_pos hp, if_pos (List.mem_append_left _ hp), ovr_tags_of_mem _ _ _ hp]
+  · rw [lookL_eq, if_neg hp, ovr_append, ovr_of_not_mem (by rwa [List.map_map]) _]
+    obtain ⟨o, L⟩ := s
+    cases o with
+    | none => simp [hp]
+    | some c =>
+      simp only
+      by_cases hc : pairW n (List.ofFn c) = p
+      · subst hc
+        simp [ovr_cons, ovr_nil]
+      · simp only [if_neg hc, List.mem_append, hp, List.mem_singleton, false_or]
+        rw [if_neg (Ne.symm hc)]
+
+/-- The tag table after an entry: `tagTbl (o, (p, t, m) :: L) = (p, t) :: tagTbl (o, L)`. -/
+private theorem tagTbl_cons (o : Option (Fin d → Bool)) (p t : Fin (2 * n) → Bool) (m : List Bool)
+    (L : List (LEntry n)) : tagTbl (o, (p, t, m) :: L) = (p, t) :: tagTbl (o, L) := by
+  rw [tagTbl_eq, tagTbl_eq, List.map_cons, List.cons_append]
+
+/-- The pairs after an entry: `keysL ((p, t, m) :: L) = p :: keysL L`. -/
+private theorem keysL_cons (p t : Fin (2 * n) → Bool) (m : List Bool) (L : List (LEntry n)) :
+    keysL ((p, t, m) :: L) = p :: keysL L := by
+  rw [keysL_eq, keysL_eq, List.map_cons]
+
+/-- Writing a value the table already gives changes nothing:
+`ovr M R p = y → ovr ((p, y) :: M) R = ovr M R`. -/
+private theorem ovr_cons_self {M : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))}
+    {R : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)} {p y : Fin (2 * n) → Bool}
+    (h : ovr M R p = y) : ovr ((p, y) :: M) R = ovr M R := by
+  rw [ovr_cons, ← h, Function.update_eq_self]
+
+/-- Appending a value at a key changes nothing: `p ∈ keys M → ovr (M ++ [(p, y)]) R = ovr M R`. -/
+private theorem ovr_append_of_mem {M : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))}
+    {p : Fin (2 * n) → Bool} (hp : p ∈ M.map Prod.fst) (y : Fin (2 * n) → Bool)
+    (R : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) : ovr (M ++ [(p, y)]) R = ovr M R := by
+  rw [ovr_append, ovr_cons, ovr_nil]
+  funext x
+  by_cases hx : x ∈ M.map Prod.fst
+  · exact ovr_of_mem hx _ _
+  · rw [ovr_of_not_mem hx, ovr_of_not_mem hx,
+      Function.update_of_ne (fun h => hx (by rw [h]; exact hp))]
+
+/-- Appending a value at a new key is writing it first:
+`p ∉ keys M → ovr (M ++ [(p, y)]) R = ovr ((p, y) :: M) R`. -/
+private theorem ovr_append_of_not_mem {M : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))}
+    {p : Fin (2 * n) → Bool} (hp : p ∉ M.map Prod.fst) (y : Fin (2 * n) → Bool)
+    (R : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) :
+    ovr (M ++ [(p, y)]) R = ovr ((p, y) :: M) R := by
+  rw [ovr_append, ovr_cons, ovr_nil, ovr_cons, ovr_update hp]
+
+end Ovr
+
+/-! ### The lazy experiment -/
+
+/-- **XOR twice with the same pad is the identity** (generic; several modules keep a private
+copy): `(m ⊕ p) ⊕ p = m` when `|m| ≤ |p|`. -/
+theorem zipWith_xor_cancel : ∀ (m p : List Bool), m.length ≤ p.length →
+    List.zipWith xor (List.zipWith xor m p) p = m
+  | [], _, _ => by simp
+  | _ :: _, [], h => by simp at h
+  | a :: m, c :: p, h => by
+    simp only [List.zipWith_cons_cons, List.cons.injEq]
+    exact ⟨by cases a <;> cases c <;> rfl, zipWith_xor_cancel m p (by simpa using h)⟩
+
+section Lazy
+
+variable (ins outs : Fin 3 → ℕ) (d n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)) (b : Bool)
+
+/-- **The invariant of the lazy table:** every entry `(p, t, m)` has an `n`-bit message `m` and the
+pair `p = r ‖ (m ⊕ f(r))` of some nonce `r`. -/
+def LInv {d : ℕ} (s : LSt n d) : Prop :=
+  ∀ e ∈ s.2, ∃ r : Fin n → Bool, e.1 = pairV n (List.ofFn r) (maskL f r e.2.2) ∧ e.2.2.length = n
+
+/-- `LInv f s` unfolded:
+`LInv n f s ↔ ∀ e ∈ s.2, ∃ r, e.1 = pairV n ⟦r⟧ (maskL f r e.2.2) ∧ |e.2.2| = n`. -/
+theorem lInv_iff {d : ℕ} (s : LSt n d) :
+    LInv n f s ↔ ∀ e ∈ s.2,
+      ∃ r : Fin n → Bool, e.1 = pairV n (List.ofFn r) (maskL f r e.2.2) ∧ e.2.2.length = n :=
+  Iff.rfl
+
+/-- The empty table has the invariant: `LInv n f (o, [])`, vacuously, since `LInv n f s`
+quantifies over `e ∈ s.2` and here `s.2 = []`. -/
+theorem lInv_nil {d : ℕ} (o : Option (Fin d → Bool)) : LInv n f ((o, []) : LSt n d) :=
+  fun _ he => absurd he List.not_mem_nil
+
+/-- **The rejecting decryption answer with the table's tags is the lazy answer:** under the
+invariant, `decAnsW f (ovr (tagTbl s) R) true (s.1, keysL s.2) w = lazyDec s w`.
+
+**Proof sketch.** A refused or malformed word gets `⊥` in both. A well-formed word with a listed
+pair reads the newest entry `(p, t, m)` at it (`ovr_tags_of_mem`, `getD_idxOf_fst`); its fields are
+`r` and `m ⊕ f(r)` (`eq_of_pairV_eq`), so `decL f w = ⟨1, m⟩` (`zipWith_xor_cancel`). A fresh pair
+is rejected by both. -/
+theorem decAnsW_tagTbl {d : ℕ} (s : LSt n d) (hs : LInv n f s)
+    (R : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (w : List Bool) :
+    decAnsW f (ovr (tagTbl s) R) true (s.1, keysL s.2) w = lazyDec s w := by
+  rw [decAnsW_eq, lazyDec_eq, validW_eq]
+  simp only [Bool.not_true, Bool.false_or]
+  by_cases hr : refW s.1 w = true
+  · simp [hr]
+  · rw [Bool.not_eq_true] at hr
+    simp only [hr, Bool.not_false, Bool.true_and]
+    by_cases hw : wfW n w = true
+    · simp only [hw, Bool.true_and]
+      have hw' := hw
+      rw [wfW_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hw'
+      by_cases hk : pairW n w ∈ keysL s.2
+      · rw [lookL_eq, if_pos hk, tagL_eq, ← pairW_eq, tagTbl_eq, ovr_tags_of_mem _ _ _ hk]
+        simp only [decide_eq_true hk, Bool.and_true, decide_eq_true_eq, ↓reduceIte]
+        have hfst := getD_idxOf_fst hk
+        have hlt : (keysL s.2).idxOf (pairW n w) < s.2.length := by
+          have := List.idxOf_lt_length_of_mem hk
+          rwa [keysL_eq, List.length_map] at this
+        obtain ⟨r, hp, hl⟩ := hs (s.2.getD ((keysL s.2).idxOf (pairW n w)) default) (by
+          rw [List.getD_eq_getElem _ _ hlt]
+          exact List.getElem_mem hlt)
+        by_cases ht : wT w = List.ofFn (s.2.getD ((keysL s.2).idxOf (pairW n w)) default).2.1
+        · rw [if_pos ht, if_pos ht.symm, decL_eq]
+          obtain ⟨h₁, h₂⟩ := eq_of_pairV_eq hw'.1 hw'.2 List.length_ofFn
+            (length_maskL f r hl) ((pairW_eq n w).symm.trans (hfst.symm.trans hp))
+          rw [h₁, h₂, padFin_ofFn, maskL_eq, zipWith_xor_cancel _ _ (by
+            rw [List.length_ofFn, hl])]
+        · rw [if_neg ht, if_neg (Ne.symm ht)]
+      · rw [lookL_eq, if_neg hk]
+        simp [hk]
+    · rw [Bool.not_eq_true] at hw
+      simp [hw]
+
+/-- **One step of the lazy experiment** with the nonce `r` and the tape `t` (see the module
+docstring), with inputs read by `⟦·⟧` and answers and records written by `padFin`: for
+`c₁ = maskL f r m`, `p = pairV n ⟦r⟧ c₁` and `τ = (tagOf s p).getD t`,
+`lazyStep … r t 0 m s = (ctW ⟦r⟧ c₁ ⟦τ⟧, (s.1, (p, τ, m) :: s.2))`,
+`lazyStep … r t 1 w s = (lazyDec s w, s)`,
+`lazyStep … r t 2 mm (some c, L) = (⟦c⟧, (some c, L))` and
+`lazyStep … r t 2 mm (none, L) = (e, (some e, L))` with `e = ctW ⟦r⟧ c₁ ⟦τ⟧`, where here
+`m = msgOf n b mm` and `s = (none, L)`. -/
+def lazyStep (r : Fin n → Bool) (t : Fin (2 * n) → Bool) :
+    ∀ i : Fin 3, (Fin (ins i) → Bool) → LSt n d → (Fin (outs i) → Bool) × LSt n d
+  | 0, m, s => (padFin _ (ctW (List.ofFn r) (maskL f r (List.ofFn m))
+        (List.ofFn ((tagOf s (pairV n (List.ofFn r) (maskL f r (List.ofFn m)))).getD t))),
+      (s.1, (pairV n (List.ofFn r) (maskL f r (List.ofFn m)),
+        (tagOf s (pairV n (List.ofFn r) (maskL f r (List.ofFn m)))).getD t, List.ofFn m) :: s.2))
+  | 1, w, s => (padFin _ (lazyDec s (List.ofFn w)), s)
+  | 2, _, (some c, L) => (padFin _ (List.ofFn c), (some c, L))
+  | 2, mm, (none, L) =>
+    (padFin _ (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))
+        (List.ofFn ((tagOf ((none, L) : LSt n d) (pairV n (List.ofFn r)
+          (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))))).getD t))),
+      (some (padFin d (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))
+        (List.ofFn ((tagOf ((none, L) : LSt n d) (pairV n (List.ofFn r)
+          (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))))).getD t)))), L))
+
+/-- `Enc′` in the lazy experiment: the tag `tagOf s p` or the tape, and a new entry,
+`lazyStep … r t 0 m s = (padFin _ (ctW ⟦r⟧ c₁ ⟦τ⟧), (s.1, (p, τ, ⟦m⟧) :: s.2))` with
+`c₁ = maskL f r ⟦m⟧`, `p = pairV n ⟦r⟧ c₁` and `τ = (tagOf s p).getD t`. -/
+theorem lazyStep_enc (r : Fin n → Bool) (t : Fin (2 * n) → Bool) (m : Fin (ins 0) → Bool)
+    (s : LSt n d) :
+    lazyStep ins outs d n f b r t 0 m s =
+      (padFin _ (ctW (List.ofFn r) (maskL f r (List.ofFn m))
+          (List.ofFn ((tagOf s (pairV n (List.ofFn r) (maskL f r (List.ofFn m)))).getD t))),
+        (s.1, (pairV n (List.ofFn r) (maskL f r (List.ofFn m)),
+          (tagOf s (pairV n (List.ofFn r) (maskL f r (List.ofFn m)))).getD t,
+          List.ofFn m) :: s.2)) := rfl
+
+/-- `Dec′` in the lazy experiment answers `lazyDec`:
+`lazyStep … r t 1 w s = (padFin _ (lazyDec s ⟦w⟧), s)`. -/
+theorem lazyStep_dec (r : Fin n → Bool) (t : Fin (2 * n) → Bool) (w : Fin (ins 1) → Bool)
+    (s : LSt n d) :
+    lazyStep ins outs d n f b r t 1 w s = (padFin _ (lazyDec s (List.ofFn w)), s) := rfl
+
+/-- A repeated challenge in the lazy experiment:
+`lazyStep … r t 2 mm (some c, L) = (padFin _ ⟦c⟧, (some c, L))`. -/
+theorem lazyStep_challenge_some (r : Fin n → Bool) (t : Fin (2 * n) → Bool)
+    (mm : Fin (ins 2) → Bool) (c : Fin d → Bool) (L : List (LEntry n)) :
+    lazyStep ins outs d n f b r t 2 mm (some c, L) = (padFin _ (List.ofFn c), (some c, L)) := rfl
+
+/-- The first challenge in the lazy experiment:
+`lazyStep … r t 2 mm (none, L) = (padFin _ e, (some (padFin d e), L))` with
+`e = ctW ⟦r⟧ c₁ ⟦(tagOf (none, L) (pairV n ⟦r⟧ c₁)).getD t⟧` and
+`c₁ = maskL f r (msgOf n b ⟦mm⟧)`. -/
+theorem lazyStep_challenge_none (r : Fin n → Bool) (t : Fin (2 * n) → Bool)
+    (mm : Fin (ins 2) → Bool) (L : List (LEntry n)) :
+    lazyStep ins outs d n f b r t 2 mm (none, L) =
+      (padFin _ (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))
+          (List.ofFn ((tagOf ((none, L) : LSt n d) (pairV n (List.ofFn r)
+            (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))))).getD t))),
+        (some (padFin d (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))
+          (List.ofFn ((tagOf ((none, L) : LSt n d) (pairV n (List.ofFn r)
+            (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))))).getD t)))), L)) := rfl
+
+/-- One call of the lazy experiment with the tape `t`: draw the nonce and take `lazyStep`,
+`ettLazyK … i x s t = (sample (Fin n → Bool)).bind fun r => pure (lazyStep … r t i x s)`. -/
+noncomputable def ettLazyK (i : Fin 3) (x : Fin (ins i) → Bool) (s : LSt n d)
+    (t : Fin (2 * n) → Bool) : ProbComp ((Fin (outs i) → Bool) × LSt n d) :=
+  (sample (Fin n → Bool)).bind fun r => .pure (lazyStep ins outs d n f b r t i x s)
+
+/-- `ettLazyK … i x s t = (sample (Fin n → Bool)).bind fun r => pure (lazyStep … r t i x s)`. -/
+theorem ettLazyK_eq (i : Fin 3) (x : Fin (ins i) → Bool) (s : LSt n d) (t : Fin (2 * n) → Bool) :
+    ettLazyK ins outs d n f b i x s t =
+      (sample (Fin n → Bool)).bind fun r => .pure (lazyStep ins outs d n f b r t i x s) := rfl
+
+/-- **The lazy experiment:** one fresh tape per query (`freshImpl`):
+`ettLazy … = freshImpl (ettLazyK …)`. -/
+noncomputable def ettLazy : QueryImpl (bitSpec ins outs) (LSt n d) unifSpec :=
+  freshImpl (ettLazyK ins outs d n f b)
+
+/-- `ettLazy … = freshImpl (ettLazyK …)`. -/
+theorem ettLazy_eq : ettLazy ins outs d n f b = freshImpl (ettLazyK ins outs d n f b) := rfl
+
+/-- **The lazy experiment with tapes in advance** (`tapeImpl`):
+`ettLazyTape … T = tapeImpl (ettLazyK …) T`. -/
+noncomputable def ettLazyTape (T : ℕ → Fin (2 * n) → Bool) :
+    QueryImpl (bitSpec ins outs) (LSt n d × ℕ) unifSpec :=
+  tapeImpl (ettLazyK ins outs d n f b) T
+
+/-- `ettLazyTape … T = tapeImpl (ettLazyK …) T`. -/
+theorem ettLazyTape_eq (T : ℕ → Fin (2 * n) → Bool) :
+    ettLazyTape ins outs d n f b T = tapeImpl (ettLazyK ins outs d n f b) T := rfl
+
+/-- **Tapes in advance have the law of fresh tapes** (`expect_simulate_tapeImpl`): for a
+computation with at most `m` queries and `j + m ≤ κ`,
+`𝔼_{T ← ({0,1}^{2n})^κ} 𝔼[G (simulate (ettLazyTape … (extTape T)) c (s, j))] =
+𝔼[G (simulate (ettLazy …) c s)]`. -/
+theorem expect_ettLazyTape (κ : ℕ) {α : Type} (G : α → ℝ) (c : OracleComp (bitSpec ins outs) α)
+    (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : LSt n d) (j : ℕ) (hj : j + m ≤ κ) :
+    expect (sample (Fin κ → Fin (2 * n) → Bool))
+        (fun T => expect (simulate (ettLazyTape ins outs d n f b (AdaptiveCPA.extTape T)) c (s, j))
+          fun p => G p.1) =
+      expect (simulate (ettLazy ins outs d n f b) c s) fun p => G p.1 :=
+  expect_simulate_tapeImpl _ κ G c m hc s j hj
+
+end Lazy
+
+/-! ### The law of the lazy experiment -/
+
+section LazyLaw
+
+variable (ins outs : Fin 3 → ℕ) (d n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)) (b : Bool)
+
+/-- One call of the lazy experiment: draw the tape, then the nonce, and take `lazyStep`,
+`ettLazy … i x s = (sample (Fin (2n) → Bool)).bind fun t =>
+(sample (Fin n → Bool)).bind fun r => pure (lazyStep … r t i x s)`. -/
+theorem ettLazy_apply (i : Fin 3) (x : Fin (ins i) → Bool) (s : LSt n d) :
+    ettLazy ins outs d n f b i x s =
+      (sample (Fin (2 * n) → Bool)).bind fun t =>
+        (sample (Fin n → Bool)).bind fun r => .pure (lazyStep ins outs d n f b r t i x s) := by
+  rw [ettLazy_eq, freshImpl_apply]
+  rfl
+
+/-- **The rejecting experiment with a uniform random tag function is the lazy experiment**
+[PS10, Thm 170.4, proof]: for `(6n + 4)`-bit records, `n`-bit messages and `2n`-bit challenge
+queries, from a lazy state with the invariant `LInv`, averaging over `R` with the table's tags
+written over it, `𝔼_R 𝔼[G (simulate (ettImpl … (ovr (tagTbl s) R) true b) c (s.1, keysL s.2))] =
+𝔼[G (simulate (ettLazy …) c s)]`.
+
+**Proof sketch.** Induction on `c`; both sides draw a nonce per query (exchanged with the
+average, `expect_sample_comm`). An encryption or a first challenge at a pair of the tag table reads
+the table (`tagOf_eq_ovr`, `ovr_of_mem`), and the new entry repeats it (`ovr_cons_self`,
+`ovr_append_of_mem`); at a new pair it reads `R` there, moved into the table by
+`expect_sample_ovr` and matched by the lazy tape (`ovr_append_of_not_mem`). Decryption answers agree
+(`decAnsW_tagTbl`). A repeated challenge reads nothing. -/
+theorem expect_ettImpl_lazy (hd : d = 6 * n + 4) (hi0 : ins 0 = n) (hi2 : ins 2 = n + n)
+    {α : Type} (G : α → ℝ) (c : OracleComp (bitSpec ins outs) α) (s : LSt n d)
+    (hs : LInv n f s) :
+    expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)))
+        (fun R => expect (simulate (ettImpl ins outs d n f (ovr (tagTbl s) R) true b) c
+          (s.1, keysL s.2)) fun p => G p.1) =
+      expect (simulate (ettLazy ins outs d n f b) c s) fun p => G p.1 := by
+  induction c generalizing s with
+  | pure a =>
+    simp only [simulate_pure, expect_pure]
+    exact expect_const _ _
+  | query i x k ih =>
+    rw [simulate_query, ettLazy_apply]
+    simp only [simulate_query, ettImpl_apply, OracleComp.bind_assoc, OracleComp.pure_bind,
+      expect_bind]
+    rw [expect_sample_comm (α := (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)),
+      expect_sample_comm (α := Fin (2 * n) → Bool)]
+    refine congrArg _ (funext fun r => ?_)
+    match i, x, k, ih with
+    | 0, m, k, ih =>
+      have hm : (List.ofFn m).length = n := by rw [List.length_ofFn, hi0]
+      simp only [ettStep_enc, lazyStep_enc, encW_eq_ctW]
+      by_cases hp : pairV n (List.ofFn r) (maskL f r (List.ofFn m)) ∈ (tagTbl s).map Prod.fst
+      · -- the pair has a tag already
+        have hy : ∀ R, ovr (tagTbl s) R (pairV n (List.ofFn r) (maskL f r (List.ofFn m))) =
+            ovr (tagTbl s) (fun _ => pairV n (List.ofFn r) (maskL f r (List.ofFn m)))
+              (pairV n (List.ofFn r) (maskL f r (List.ofFn m))) := fun R => ovr_of_mem hp R _
+        rw [tagOf_eq_ovr s _ (fun _ => pairV n (List.ofFn r) (maskL f r (List.ofFn m))),
+          if_pos hp]
+        simp only [Option.getD_some, hy, expect_const]
+        have hs' : LInv n f (s.1, (pairV n (List.ofFn r) (maskL f r (List.ofFn m)),
+            ovr (tagTbl s) (fun _ => pairV n (List.ofFn r) (maskL f r (List.ofFn m)))
+              (pairV n (List.ofFn r) (maskL f r (List.ofFn m))), List.ofFn m) :: s.2) := by
+          intro e he
+          rcases List.mem_cons.1 he with rfl | he
+          · exact ⟨r, rfl, hm⟩
+          · exact hs e he
+        rw [← ih _ _ hs', tagTbl_cons, keysL_cons, Prod.mk.eta]
+        refine congrArg _ (funext fun R => ?_)
+        rw [ovr_cons_self (hy R)]
+      · -- a new pair: its tag is the tape
+        rw [tagOf_eq_ovr s _ (fun _ => pairV n (List.ofFn r) (maskL f r (List.ofFn m))),
+          if_neg hp]
+        simp only [Option.getD_none]
+        have e : ∀ R, ovr (tagTbl s) R (pairV n (List.ofFn r) (maskL f r (List.ofFn m))) =
+            R (pairV n (List.ofFn r) (maskL f r (List.ofFn m))) := fun R => ovr_of_not_mem hp R
+        simp only [e]
+        rw [expect_sample_ovr (tagTbl s) hp (fun t g => expect (simulate
+          (ettImpl ins outs d n f g true b) (k (padFin _ (ctW (List.ofFn r)
+            (maskL f r (List.ofFn m)) (List.ofFn t))))
+          (s.1, pairV n (List.ofFn r) (maskL f r (List.ofFn m)) :: keysL s.2)) fun p => G p.1)]
+        refine congrArg _ (funext fun t => ?_)
+        have hs' : LInv n f (s.1, (pairV n (List.ofFn r) (maskL f r (List.ofFn m)), t,
+            List.ofFn m) :: s.2) := by
+          intro e he
+          rcases List.mem_cons.1 he with rfl | he
+          · exact ⟨r, rfl, hm⟩
+          · exact hs e he
+        rw [← ih _ _ hs', tagTbl_cons, keysL_cons, Prod.mk.eta]
+    | 1, w, k, ih =>
+      simp only [ettStep_dec, lazyStep_dec, decAnsW_tagTbl n f s hs, expect_const]
+      exact ih _ s hs
+    | 2, mm, k, ih =>
+      obtain ⟨o, L⟩ := s
+      cases o with
+      | some c =>
+        simp only [ettStep_challenge_some, lazyStep_challenge_some, expect_const]
+        exact ih _ (some c, L) hs
+      | none =>
+        have hmsg : (AdaptiveCPA.msgOf n b (List.ofFn mm)).length = n := by
+          have : (List.ofFn mm).length = n + n := by rw [List.length_ofFn, hi2]
+          rw [AdaptiveCPA.msgOf_eq]
+          cases b <;> simp [this]
+        have hl := length_maskL f r hmsg
+        have hrec : ∀ t : Fin (2 * n) → Bool,
+            List.ofFn (padFin d (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b
+              (List.ofFn mm))) (List.ofFn t))) =
+            ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))) (List.ofFn t) := by
+          intro t
+          refine ofFn_padFin_of_length ?_
+          rw [ctW_eq, length_pairEncode, length_pairEncode, List.length_ofFn, hl, List.length_ofFn,
+            hd]
+          omega
+        have htbl : ∀ t : Fin (2 * n) → Bool,
+            tagTbl ((some (padFin d (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b
+              (List.ofFn mm))) (List.ofFn t))), L) : LSt n d) =
+            tagTbl ((none, L) : LSt n d) ++ [(pairV n (List.ofFn r)
+              (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))), t)] := by
+          intro t
+          rw [tagTbl_eq, tagTbl_eq, List.append_nil]
+          simp only
+          rw [hrec, pairW_eq, wR_ctW, wC_ctW, wT_ctW, padFin_ofFn]
+        simp only [ettStep_challenge_none, lazyStep_challenge_none, encW_eq_ctW]
+        by_cases hp : pairV n (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))) ∈
+            (tagTbl ((none, L) : LSt n d)).map Prod.fst
+        · have hy : ∀ R, ovr (tagTbl ((none, L) : LSt n d)) R (pairV n (List.ofFn r)
+              (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))) =
+              ovr (tagTbl ((none, L) : LSt n d)) (fun _ => pairV n (List.ofFn r)
+                (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))) (pairV n (List.ofFn r)
+                (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))) := fun R => ovr_of_mem hp R _
+          rw [tagOf_eq_ovr _ _ (fun _ => pairV n (List.ofFn r)
+            (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))), if_pos hp]
+          simp only [Option.getD_some, hy, expect_const]
+          rw [← ih _ (some (padFin d (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b
+            (List.ofFn mm))) (List.ofFn (ovr (tagTbl ((none, L) : LSt n d)) (fun _ => pairV n
+              (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))))
+              (pairV n (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))))))), L) hs,
+            htbl]
+          refine congrArg _ (funext fun R => ?_)
+          rw [ovr_append_of_mem hp]
+        · rw [tagOf_eq_ovr _ _ (fun _ => pairV n (List.ofFn r)
+            (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))), if_neg hp]
+          simp only [Option.getD_none]
+          have e : ∀ R, ovr (tagTbl ((none, L) : LSt n d)) R (pairV n (List.ofFn r)
+              (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))) =
+              R (pairV n (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))) :=
+            fun R => ovr_of_not_mem hp R
+          simp only [e]
+          rw [expect_sample_ovr (tagTbl ((none, L) : LSt n d)) hp (fun t g => expect (simulate
+            (ettImpl ins outs d n f g true b) (k (padFin _ (ctW (List.ofFn r)
+              (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))) (List.ofFn t))))
+            (some (padFin d (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))
+              (List.ofFn t))), keysL L)) fun p => G p.1)]
+          refine congrArg _ (funext fun t => ?_)
+          rw [← ih _ (some (padFin d (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b
+            (List.ofFn mm))) (List.ofFn t))), L) hs, htbl]
+          refine congrArg _ (funext fun R => ?_)
+          rw [ovr_append_of_not_mem hp]
+
+end LazyLaw
+
+end TCSlib.Cryptography.Composability.ETTGame
diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Machines.lean b/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Machines.lean
new file mode 100644
index 000000000..666b94f7c
--- /dev/null
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Machines.lean
@@ -0,0 +1,359 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Games.BitCodec
+import TCSlib.Cryptography.Games.Efficiency.Strings
+import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs
+import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.ChallengeSim
+import TCSlib.Complexity.Randomized.Repetition
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Machine constructions for the encrypt-then-tag proof
+
+Two generic constructions on machines used by the proof of [PS10, Theorem 170.4]
+(`Composability.ccaScheme_cca2`); both are candidates for promotion.
+
+* **A budget cap** (`exists_capMachine`): for a machine `A` and a polynomial `q` there is a machine
+  `A'` that behaves as `A` with budget `q(n)` at every budget `K ≥ q(n)`: once its log holds `q(n)`
+  entries, a query of `A` is replaced by the empty word, which every bit codec reads as the
+  all-`false` output, the timeout of the bit codec. The PRF reduction of the encrypt-then-tag proof
+  runs at parameter `2n` with budget `q(2n)` an adversary whose budget is `q(n)`.
+* **Halving the parameter** (`exists_halfMachine`): for a next-query machine `B` there is a machine
+  `D` whose oracle adversary at parameter `2n` accepts any oracle with the probability that `B`'s
+  accepts it at parameter `n` (`NUPPT.exists_reparam_advice` with `φ m = m / 2`; the coins `D` does
+  not read are an independent uniform factor).
+
+## Main definitions
+
+* `ETTGame.logCount`: the number of entries of a nested-pair log, in unary.
+
+## Main results
+
+* `ETTGame.length_logCount_encodeLog`: `logCount` counts the entries of an encoded log.
+* `ETTGame.buildComp_cap`: a next-move function capped after `q` entries computes, at every budget
+  `K ≥ q`, what the original computes with budget `q`.
+* `ETTGame.exists_capMachine`, `ETTGame.exists_halfMachine`, `ETTGame.eval_toOracleAdversary_len`.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §2.1 (non-uniform machines) and Theorem 170.4 (book p. 170).
+-/
+
+namespace TCSlib.Cryptography.Composability.ETTGame
+
+open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp
+
+/-! ### Counting the entries of a log -/
+
+/-- **The number of entries of a nested-pair log `⟨e₁, ⟨e₂, …⟩⟩`, in unary:** one `true` for every
+nonempty suffix `pairSndD^[i] L`, `i ≤ |L|` (`cntRead`). -/
+def logCount (L : List Bool) : List Bool :=
+  (List.range (PolyExpr.var.eval L.length + 1)).flatMap fun i => cntRead (pairSndD^[i] L)
+
+/-- `logCount L = ⋃_{i ≤ |L|} cntRead (pairSndD^[i] L)`. -/
+theorem logCount_eq (L : List Bool) :
+    logCount L =
+      (List.range (PolyExpr.var.eval L.length + 1)).flatMap fun i => cntRead (pairSndD^[i] L) :=
+  rfl
+
+/-- The entry count is polynomial-time, `PolyTimeComputable logCount`, i.e.
+`∃ M C c, M.ComputesFunInTime logCount (fun n => C * (n + 1)^c)`: an iterated emission
+(`polyTimeComputable_iterateEmit`) along `pairSndD`, which does not lengthen its argument
+(`length_pairSndD_le`). -/
+theorem polyTimeComputable_logCount : PolyTimeComputable logCount := by
+  have horb : ∀ (x : List Bool) (i : ℕ), (pairSndD^[i] x).length ≤ x.length := by
+    intro x i
+    induction i with
+    | zero => exact le_rfl
+    | succ i ih =>
+      rw [Function.iterate_succ_apply']
+      exact (length_pairSndD_le _).trans ih
+  exact polyTimeComputable_iterateEmit polyTimeComputable_pairSndD polyTimeComputable_cntRead
+    .var .var fun x i _ => by rw [PolyExpr.eval_var]; exact horb x i
+
+/-- `#{i < N : i < L} = min N L`, as the length of an emission of `[true]` below `L`. -/
+private theorem length_flatMap_range_lt (N L : ℕ) :
+    ((List.range N).flatMap fun i => if i < L then [true] else []).length = min N L := by
+  induction N with
+  | zero => simp
+  | succ N ih =>
+    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
+    by_cases h : N < L
+    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, if_pos h,
+        List.length_singleton]
+      omega
+    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, if_neg h, List.length_nil]
+      omega
+
+/-- An encoded log has at least as many bits as entries. -/
+private theorem length_le_length_encodeLog {ι α : Type} {spec : OracleSpec ι}
+    (codec : MachineCodec spec α) (h : QueryLog spec) : h.length ≤ (codec.encodeLog h).length := by
+  induction h with
+  | nil => simp
+  | cons e h ih =>
+    rw [MachineCodec.encodeLog_cons, length_pairEncode, List.length_cons]
+    omega
+
+/-- **`logCount` counts the entries of an encoded log:** `|logCount (codec.encodeLog h)| = |h|`.
+
+**Proof sketch.** The `i`-th suffix of `encodeLog h` is `encodeLog (h.drop i)`
+(`MachineCodec.encodeLog_cons`, `pairSndD_pairEncode`), nonempty exactly for `i < |h|`
+(`pairEncode_ne_nil`); every entry adds at least two bits (`length_pairEncode`), so the range
+`i ≤ |encodeLog h|` covers all of them (`length_flatMap_range_lt`). -/
+theorem length_logCount_encodeLog {ι α : Type} {spec : OracleSpec ι} (codec : MachineCodec spec α)
+    (h : QueryLog spec) : (logCount (codec.encodeLog h)).length = h.length := by
+  have hsuf : ∀ (i : ℕ) (h : QueryLog spec),
+      pairSndD^[i] (codec.encodeLog h) = codec.encodeLog (h.drop i) := by
+    intro i
+    induction i with
+    | zero => intro h; rfl
+    | succ i ih =>
+      intro h
+      cases h with
+      | nil =>
+        rw [List.drop_nil, Function.iterate_succ_apply, MachineCodec.encodeLog_nil]
+        have : pairSndD ([] : List Bool) = [] := by
+          have h1 := Complexity.BinArith.iterate_pairSndD_nil 1
+          rwa [Function.iterate_one] at h1
+        rw [this]
+        have hn := ih []
+        rwa [List.drop_nil, MachineCodec.encodeLog_nil] at hn
+      | cons e h =>
+        rw [Function.iterate_succ_apply, MachineCodec.encodeLog_cons, pairSndD_pairEncode, ih,
+          List.drop_succ_cons]
+  have hcnt : ∀ i : ℕ, cntRead (pairSndD^[i] (codec.encodeLog h)) =
+      if i < h.length then [true] else [] := by
+    intro i
+    rw [hsuf, cntRead_eq]
+    by_cases hi : i < h.length
+    · rw [if_pos hi]
+      obtain ⟨e, t, ht⟩ : ∃ e t, h.drop i = e :: t := by
+        cases hd : h.drop i with
+        | nil => rw [List.drop_eq_nil_iff] at hd; omega
+        | cons e t => exact ⟨e, t, rfl⟩
+      rw [ht, MachineCodec.encodeLog_cons, decide_eq_false (pairEncode_ne_nil _ _)]
+      rfl
+    · rw [if_neg hi, List.drop_eq_nil_of_le (by omega), MachineCodec.encodeLog_nil]
+      rfl
+  have hlen := length_le_length_encodeLog codec h
+  rw [logCount_eq]
+  simp only [hcnt]
+  rw [length_flatMap_range_lt, PolyExpr.eval_var]
+  omega
+
+/-! ### Capping a next-move function -/
+
+/-- **Budget cap for `buildComp`.** Let `next'` agree with `next` on logs shorter than `q`, and on
+logs of length `q` return `next`'s output, or the timeout `t` in place of a query. Then from a log
+of length `|hist| = q - j`, at every budget `K ≥ j`, the computation of `next'` is the computation
+of `next` at budget `j`: `buildComp next' t K hist = buildComp next t j hist`.
+
+**Proof sketch.** Induction on `j`. At `j = 0` the log has length `q`, and `next'` returns
+(`buildComp_of_ret`) what `buildComp next t 0` returns: the output, or `t` for a query. Below `q`
+the moves agree; a query is asked at budgets `K = K' + 1` and `j' + 1` and both continue from the
+log extended by the answer. -/
+theorem buildComp_cap {ι α : Type} {spec : OracleSpec ι} (next next' : QueryLog spec → Move spec α)
+    (t : α) (q : ℕ) (h₁ : ∀ hist : QueryLog spec, hist.length < q → next' hist = next hist)
+    (h₂ : ∀ hist : QueryLog spec, hist.length = q →
+      (∀ a, next hist = .ret a → next' hist = .ret a) ∧
+        (∀ i x, next hist = .query i x → next' hist = .ret t)) :
+    ∀ (j K : ℕ) (hist : QueryLog spec), hist.length + j = q → j ≤ K →
+      buildComp next' t K hist = buildComp next t j hist := by
+  intro j
+  induction j with
+  | zero =>
+    intro K hist hq _
+    obtain ⟨hr, hqy⟩ := h₂ hist (by omega)
+    cases h : next hist with
+    | ret a => rw [buildComp_of_ret (hr a h), buildComp_zero_of_ret h]
+    | query i x => rw [buildComp_of_ret (hqy i x h), buildComp_zero_of_query h]
+  | succ j ih =>
+    intro K hist hq hK
+    obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
+    have hn := h₁ hist (by omega)
+    cases h : next hist with
+    | ret a =>
+      rw [buildComp_succ_of_ret (hn.trans h), buildComp_succ_of_ret h]
+    | query i x =>
+      rw [buildComp_succ_of_query (hn.trans h), buildComp_succ_of_query h]
+      congr 1
+      funext y
+      exact ih K _ (by rw [List.length_append, List.length_singleton]; omega) (by omega)
+
+/-- A word with first component `[false]` decodes as a query or as the default output:
+`pairFstD w = [false] → decodeBitMove din dout dα w = ret a → a = zeroBits dα`.
+
+**Proof sketch.** Such a word is not a canonical output word, whose first component is `[true]`
+(`pairFstD_pairEncode`); if it is not a canonical query word either, it decodes to the default
+(`decodeBitMove_of_not_canonical`); a canonical query word decodes as a query
+(`decodeBitMove_query`). -/
+private theorem eq_zeroBits_of_pairFstD_false {k : ℕ} {din dout : Fin k → ℕ} {dα : ℕ}
+    {w : List Bool} (hw : pairFstD w = [false]) {a : Fin dα → Bool}
+    (ha : decodeBitMove din dout dα w = .ret a) : a = zeroBits dα := by
+  by_cases hq : ∃ (i : Fin k) (x : Fin (din i) → Bool),
+      w = pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x))
+  · obtain ⟨i, x, rfl⟩ := hq
+    rw [decodeBitMove_query] at ha
+    cases ha
+  · push_neg at hq
+    have hr : ∀ a' : Fin dα → Bool, w ≠ pairEncode [true] (List.ofFn a') := by
+      intro a' h
+      rw [h, pairFstD_pairEncode] at hw
+      cases hw
+    rw [decodeBitMove_of_not_canonical hq hr] at ha
+    cases ha
+    rfl
+
+/-- The empty word decodes to the default output: `decodeBitMove din dout dα [] = ret 0^{dα}`. -/
+private theorem decodeBitMove_nil {k : ℕ} (din dout : Fin k → ℕ) (dα : ℕ) :
+    decodeBitMove din dout dα [] = .ret (zeroBits dα) :=
+  decodeBitMove_of_not_canonical (fun _ _ h => pairEncode_ne_nil _ _ h.symm)
+    (fun _ h => pairEncode_ne_nil _ _ h.symm)
+
+/-- A query word has first component `[false]`:
+`decodeBitMove din dout dα w = query i x → pairFstD w = [false]`. -/
+private theorem pairFstD_of_query {k : ℕ} {din dout : Fin k → ℕ} {dα : ℕ} {w : List Bool}
+    {i : Fin k} {x : Fin (din i) → Bool} (h : decodeBitMove din dout dα w = .query i x) :
+    pairFstD w = [false] := by
+  rw [decodeBitMove_eq_query_iff.1 h, pairFstD_pairEncode]
+
+/-- The raw function of the capped machine: `A`'s output, except that once the argument (the
+encoded log) has `q(n)` entries, an output with first component `[false]` (a query word) becomes
+the empty word: `capRaw A q z = if |logCount (inArg z)| = q(|inParam z|) ∧
+pairFstD (A.output z) = [false] then [] else A.output z`. -/
+noncomputable def capRaw (A : NUPPT) (q : PolyExpr) (z : List Bool) : List Bool :=
+  if decide ((logCount (NUPPT.inArg z)).length = q.eval (NUPPT.inParam z).length) &&
+      decide (pairFstD (A.output z) = [false]) then [] else A.output z
+
+/-- `capRaw A q z = if |logCount (inArg z)| = q(|inParam z|) ∧ pairFstD (A.output z) = [false]
+then [] else A.output z`. -/
+theorem capRaw_eq (A : NUPPT) (q : PolyExpr) (z : List Bool) :
+    capRaw A q z =
+      if decide ((logCount (NUPPT.inArg z)).length = q.eval (NUPPT.inParam z).length) &&
+          decide (pairFstD (A.output z) = [false]) then [] else A.output z :=
+  rfl
+
+/-- The capped raw function is polynomial-time, `PolyTimeComputable (capRaw A q)`, i.e.
+`∃ M C c, M.ComputesFunInTime (capRaw A q) (fun n => C * (n + 1)^c)`: the entry count
+(`polyTimeComputable_logCount`), a length comparison with `1^{q(n)}` (`EffFill.lenEq_poly`,
+`polyTimeComputable_unaryPoly`), a word comparison (`polyTimeComputable_pairEq`) and `A`'s output.
+-/
+theorem polyTimeComputable_capRaw (A : NUPPT) (q : PolyExpr) :
+    PolyTimeComputable (capRaw A q) := by
+  have hc := EffFill.lenEq_poly (polyTimeComputable_logCount.comp NUPPT.polyTimeComputable_inArg)
+    ((polyTimeComputable_unaryPoly q).comp NUPPT.polyTimeComputable_inParam)
+  have he : PolyTimeComputable fun z => [decide (pairFstD (A.output z) = [false])] :=
+    (polyTimeComputable_pairEq.comp ((polyTimeComputable_pairFstD.comp
+      A.polyTimeComputable_output).pairEncode (polyTimeComputable_const [false]))).congr fun z => by
+        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
+  refine (polyTimeComputable_ite (polyTimeComputable_and hc he) (polyTimeComputable_const [])
+    A.polyTimeComputable_output).congr fun z => ?_
+  simp only [Function.comp_apply, List.length_replicate, capRaw_eq]
+
+/-- **A budget cap** (generic; candidate for promotion). For a machine `A` and a polynomial `q`
+there is a machine `A'` with `A`'s coins whose computation through any bit codec, at any budget
+`K ≥ q(n)`, is `A`'s computation at budget `q(n)`:
+`A'.toComp (bitCodec ins outs dα) n K (coinsCongr h n r) =
+A.toComp (bitCodec ins outs dα) n (q n) r`.
+
+**Proof sketch.** `A' := NUPPT.ofPolyTime` of `capRaw A q` with `A`'s coins and advice
+(`runAtL_ofPolyTime`). On the encoded log of `hist` the entry count is `|hist|`
+(`length_logCount_encodeLog`). Below `q(n)` entries the move is `A`'s; at `q(n)` entries a query
+word becomes the empty word, which decodes to the all-`false` output (`decodeBitMove_nil`, the
+codec's timeout), and an output word with first component `[false]` already decoded to it
+(`eq_zeroBits_of_pairFstD_false`); `buildComp_cap` concludes. -/
+theorem exists_capMachine (A : NUPPT) (q : PolyExpr) :
+    ∃ (A' : NUPPT) (h : A.coins = A'.coins), ∀ (n : ℕ) {k : ℕ} (ins outs : Fin k → ℕ)
+      (dα K : ℕ) (r : A.Coins n), q.eval n ≤ K →
+      A'.toComp (bitCodec ins outs dα) n K (NUPPT.coinsCongr h n r) =
+        A.toComp (bitCodec ins outs dα) n (q.eval n) r := by
+  refine ⟨NUPPT.ofPolyTime (polyTimeComputable_capRaw A q) A.coins A.adv A.advice
+    A.advice_length, (NUPPT.coins_ofPolyTime _ _ _ _ _).symm, fun n k ins outs dα K r hK => ?_⟩
+  have hrun : ∀ y, (NUPPT.ofPolyTime (polyTimeComputable_capRaw A q) A.coins A.adv A.advice
+      A.advice_length).runAt n y (NUPPT.coinsCongr (NUPPT.coins_ofPolyTime _ _ _ _ _).symm n r) =
+      if decide ((logCount y).length = q.eval n) && decide (pairFstD (A.runAt n y r) = [false])
+      then [] else A.runAt n y r := by
+    intro y
+    rw [NUPPT.runAt_coinsCongr, NUPPT.runAtL_ofPolyTime, capRaw_eq, NUPPT.runAt_eq A,
+      NUPPT.runAtL_eq A, NUPPT.inArg_eq, NUPPT.inParam_eq, NUPPT.advInput_eq]
+    simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
+  rw [NUPPT.toComp_eq, NUPPT.toComp_eq, bitCodec_timeout]
+  refine buildComp_cap _ _ _ (q.eval n) (fun hist hl => ?_) (fun hist hl => ⟨?_, ?_⟩) (q.eval n)
+    K [] (by simp) hK
+  · rw [bitCodec_decodeMove, bitCodec_decodeMove, hrun, length_logCount_encodeLog,
+      decide_eq_false (Nat.ne_of_lt hl), Bool.false_and, if_neg Bool.false_ne_true]
+  · intro a ha
+    rw [bitCodec_decodeMove] at ha ⊢
+    rw [hrun, length_logCount_encodeLog, decide_eq_true hl, Bool.true_and]
+    by_cases hw : pairFstD (A.runAt n ((bitCodec ins outs dα).encodeLog hist) r) = [false]
+    · rw [decide_eq_true hw, if_pos rfl, decodeBitMove_nil, eq_zeroBits_of_pairFstD_false hw ha]
+    · rw [decide_eq_false hw, if_neg Bool.false_ne_true, ha]
+  · intro i x hx
+    rw [bitCodec_decodeMove] at hx ⊢
+    rw [hrun, length_logCount_encodeLog, decide_eq_true hl, Bool.true_and,
+      decide_eq_true (pairFstD_of_query hx), if_pos rfl, decodeBitMove_nil]
+
+/-! ### Halving the parameter of a next-query machine -/
+
+/-- **Halving the parameter** (generic; candidate for promotion). For a next-query machine `B`
+there is a machine `D` whose oracle adversary at parameter `2n` accepts every oracle `h` with the
+probability that `B`'s accepts it at parameter `n`, for all oracle lengths and budgets:
+`𝔼_c [D^h(2n; c)] = 𝔼_c [B^h(n; c)]`.
+
+**Proof sketch.** `D := NUPPT.exists_reparam_advice B (· / 2) var`: at parameter `2n` it runs
+`B` at `2n / 2 = n` on the first `B.coinLen n` of its `B.coinLen (2n)` coins
+(`PolyExpr.eval_subst`, `PolyExpr.eval_mono`). Split `D`'s coins as `B`'s coins and the rest
+(`EnsembleLemmas.coinsEquiv`, `take_ofFn_coinsEquiv`); the trees agree (`toOracleAdversary_eq`)
+and the unread coins average out (`expect_sample_prod`, `expect_const`). -/
+theorem exists_halfMachine (B : NUPPT) :
+    ∃ D : NUPPT, ∀ (n ℓ₁ ℓ₂ K : ℕ) (h : (Fin ℓ₁ → Bool) → (Fin ℓ₂ → Bool)),
+      expect (sample (D.Coins (2 * n)))
+          (fun c => if (D.toOracleAdversary (2 * n) ℓ₁ ℓ₂ K c).eval h = true then (1 : ℝ) else 0) =
+        expect (sample (B.Coins n))
+          (fun c => if (B.toOracleAdversary n ℓ₁ ℓ₂ K c).eval h = true then (1 : ℝ) else 0) := by
+  obtain ⟨D, hDc, hD⟩ := B.exists_reparam_advice (fun m => m / 2) .var
+    (fun m => by rw [PolyExpr.eval_var]; exact Nat.div_le_self m 2)
+  refine ⟨D, fun n ℓ₁ ℓ₂ K h => ?_⟩
+  have h2 : 2 * n / 2 = n := by omega
+  have hle : B.coinLen n ≤ B.coinLen (2 * n) := by
+    rw [NUPPT.coinLen_eq, NUPPT.coinLen_eq]
+    exact B.coins.eval_mono (by omega)
+  have hlen : D.coinLen (2 * n) = B.coinLen n + (B.coinLen (2 * n) - B.coinLen n) := by
+    rw [NUPPT.coinLen_eq, hDc, PolyExpr.eval_subst, PolyExpr.eval_var, ← NUPPT.coinLen_eq]
+    omega
+  rw [← expect_sample_equiv (EnsembleLemmas.coinsEquiv hlen), ChallengeSim.expect_sample_prod]
+  refine congrArg _ (funext fun c₁ => ?_)
+  refine (congrArg _ (funext fun c₂ => ?_)).trans (expect_const _ _)
+  have hrun :
+      ∀ y, D.runAt (2 * n) y (EnsembleLemmas.coinsEquiv hlen (c₁, c₂)) = B.runAt n y c₁ := by
+    intro y
+    rw [NUPPT.runAt_eq D, hD, NUPPT.runAt_eq B]
+    simp only [h2]
+    rw [EnsembleLemmas.take_ofFn_coinsEquiv]
+  rw [NUPPT.toOracleAdversary_eq, NUPPT.toOracleAdversary_eq]
+  simp only [hrun]
+
+/-- **An oracle adversary read at equal widths** (generic; the width-changing form of
+`PRFGame.eval_toOracleAdversary_width`, which fixes the widths to the parameter): for `ℓ = ℓ'`,
+running `D.toOracleAdversary n ℓ ℓ K c` against `f` is running `D.toOracleAdversary n ℓ' ℓ' K c`
+against `f` with its inputs and outputs read at width `ℓ'`.
+
+**Proof sketch.** Substitute `ℓ' = ℓ`; the readings are identities (`padFin_ofFn`). -/
+theorem eval_toOracleAdversary_len (D : NUPPT) (n K : ℕ) (c : D.Coins n) {ℓ ℓ' : ℕ}
+    (h : ℓ' = ℓ) (f : (Fin ℓ → Bool) → (Fin ℓ → Bool)) :
+    (D.toOracleAdversary n ℓ ℓ K c).eval f =
+      (D.toOracleAdversary n ℓ' ℓ' K c).eval
+        (fun x => padFin ℓ' (List.ofFn (f (padFin ℓ (List.ofFn x))))) := by
+  subst h
+  have e : (fun x => padFin ℓ' (List.ofFn (f (padFin ℓ' (List.ofFn x))))) = f := by
+    funext x
+    rw [padFin_ofFn, padFin_ofFn]
+  rw [e]
+
+end TCSlib.Cryptography.Composability.ETTGame
diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Reduction.lean b/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Reduction.lean
new file mode 100644
index 000000000..600c0f4a6
--- /dev/null
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Reduction.lean
@@ -0,0 +1,395 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Handler
+import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Machines
+import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Reduction
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The tag-key PRF reduction for the encrypt-then-tag scheme
+
+The reduction of [PS10, Theorem 170.4], step 1, as a next-query oracle machine at parameter `2n`:
+the budget cap of the adversary (`exists_capMachine`), the input-free companion
+(`Games.exists_toCompOn_of_toComp`), T2 (`Games.exists_interactiveHandlerMachine`) applied to the
+handler `dHandler` with the budget `q(2n)`, T4 (`Games.exists_toOracleAdversary_of_bitCodec`) at
+the length `2n`, and the parameter halving (`exists_halfMachine`). Its acceptance probability at
+parameter `2n` against any function `g` on `2n` bits is the acceptance probability of the CCA2
+experiment with `f_{k₁}` and `g` (`exists_tagReduction`).
+
+The proof answers the handler's outer queries by `g` (`gOuter`) and composes the two
+implementations (`QueryImpl.comp`). Each composed call, from the encoded state `dState j o`, is the
+call of `ettTape` from `((o, T), j)` with the handler's tapes in advance (`comp_dAbs`), as long as
+`j` is below the number `q(2n)` of tapes; the capped adversary asks at most `q(n) ≤ q(2n)` queries,
+so this holds along every run (`Games.simulate_eq_of_abs_bounded`). Drawing the seed uniformly
+gives the key and fresh nonces (`expect_ettTape`).
+
+## Main definitions
+
+* `ETTGame.gOuter`: the outer oracle answering with `g`.
+* `ETTGame.dAbs`: the handler's state as a function of `ettTape`'s state.
+
+## Main results
+
+* `ETTGame.comp_dAbs`: one composed call is a call of `ettTape`.
+* `ETTGame.exists_tagReduction`: the reduction.
+* `ETTGame.prfAdv_eq_expect`: the PRF advantage as expectations.
+* `ETTGame.exists_tagStep`: step 1, the gap to the random tag function is a PRF advantage at `2n`.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 170.4 (book p. 170).
+-/
+
+namespace TCSlib.Cryptography.Composability.ETTGame
+
+open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp
+
+/-! ### The outer oracle and the composed calls -/
+
+/-- **The outer oracle answering with `g`:** a query `x` is answered `g x`, lengths adjusted,
+`gOuter n g i x s = pure (padFin _ ⟦g (padFin (2n) ⟦x⟧)⟧, s)`. -/
+noncomputable def gOuter (n : ℕ) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) :
+    QueryImpl (bitSpecAt tagOut tagOut n) Unit unifSpec :=
+  QueryImpl.ofComp fun _ x => .pure (padFin _ (List.ofFn (g (padFin (2 * n) (List.ofFn x)))))
+
+/-- `gOuter n g i x s = pure (padFin _ ⟦g (padFin (2n) ⟦x⟧)⟧, s)`. -/
+theorem gOuter_apply (n : ℕ) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (i : Fin 1)
+    (x : (bitSpecAt tagOut tagOut n).dom i) (s : Unit) :
+    gOuter n g i x s = .pure (padFin _ (List.ofFn (g (padFin (2 * n) (List.ofFn x)))), s) := by
+  rw [gOuter, QueryImpl.ofComp_apply, OracleComp.pure_bind]
+
+section Composed
+
+variable (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
+  (E : List Bool → List Bool) (hE : PolyTimeComputable E)
+  (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
+    List.ofFn (F n s x))
+  (q : PolyExpr) (b : Bool) (n : ℕ) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))
+  (z : List Bool) (k : Fin n → Bool) (W : Fin (q.eval n * n) → Bool)
+
+/-- The handler's state and the (trivial) outer state, as functions of `ettTape`'s state:
+`dAbs … (σ, j) = (dHState q E hE b n j σ.1, ())`. -/
+def dAbs (s : St n (ettCt.eval n) × ℕ) :
+    (Fin ((dHandler q E hE b).stateLen.eval n) → Bool) × Unit :=
+  (dHState q E hE b n s.2 s.1.1, ())
+
+/-- `dAbs q E hE b n s = (dHState q E hE b n s.2 s.1.1, ())`. -/
+theorem dAbs_eq (s : St n (ettCt.eval n) × ℕ) :
+    dAbs E hE q b n s = (dHState q E hE b n s.2 s.1.1, ()) :=
+  rfl
+
+/-- The tapes of the tape word, extended to every index (`AdaptiveCPA.extTape`):
+`dTapes q n W = extTape (blocks (q n) n W)`. -/
+noncomputable def dTapes : ℕ → Fin n → Bool :=
+  AdaptiveCPA.extTape (EnsembleLemmas.blocks (q.eval n) n W)
+
+/-- `dTapes q n W = extTape (blocks (q n) n W)`. -/
+theorem dTapes_eq : dTapes q n W = AdaptiveCPA.extTape (EnsembleLemmas.blocks (q.eval n) n W) :=
+  rfl
+
+/-- Below `q(n)`, the extended tapes are the tapes: `dTapes q n W j = dTape q n W j hj`. -/
+theorem dTapes_of_lt (j : ℕ) (hj : j < q.eval n) : dTapes q n W j = dTape q n W j hj := by
+  rw [dTapes_eq, AdaptiveCPA.extTape_of_lt _ hj, dTape_eq]
+
+/-- Reading the answer of `g` to a pair `r ‖ c₁` with `|r| = |c₁| = n` through the outer oracle:
+`⟦padFin _ ⟦g (padFin (2n) ⟦padFin _ (r ++ c₁)⟧)⟧⟧ = tagL g r c₁`. -/
+private theorem gOuter_pair {r c : List Bool} (hr : r.length = n) (hc : c.length = n) :
+    List.ofFn (padFin ((tagOut 0).eval n) (List.ofFn (g (padFin (2 * n)
+      (List.ofFn (padFin ((tagOut 0).eval n) (r ++ c))))))) = tagL g r c := by
+  have h2 : (tagOut 0).eval n = 2 * n := by rw [tagOut_eq, tagLen_eval]
+  have e1 : List.ofFn (padFin ((tagOut 0).eval n) (r ++ c)) = r ++ c :=
+    ofFn_padFin_of_length (by rw [List.length_append, hr, hc, h2]; omega)
+  rw [e1, ofFn_padFin_of_length (by rw [List.length_ofFn, h2]), tagL_eq, pairV_eq]
+
+include hFE in
+/-- **One composed call is a call of `ettTape` with the tapes in advance:** from the encoded state
+`dState j o` with `j < q(n)`, the handler composed with `gOuter g` answers as `ettTape` with pad
+function `f_k` and tag function `g` and the tapes `dTapes W` from `((o, T), j)`, both
+deterministic, with the new state abstracted; the counter grows by one.
+
+**Proof sketch.** By the oracle, the record, the refusal test and well-formedness: encryption and a
+first challenge ask `g` at `r ‖ c₁` (`dHandler_impl_enc`, `dHandler_impl_challenge_none`); a
+well-formed decryption that is not refused asks `g` at its pair (`dHandler_impl_dec_wf`); the
+other calls answer directly. The outer oracle answers `g` (`gOuter_apply`, `gOuter_pair`), and the
+answers are `ettStep`'s (`ettStep_enc`, …, `decAnsW_eq`). -/
+theorem comp_dAbs (i : Fin 3) (x : (bitSpecAt ettDin ettDout n).dom i)
+    (s : St n (ettCt.eval n) × ℕ) (hs : s.2 < q.eval n) :
+    ∃ (y : (bitSpecAt ettDin ettDout n).rng i) (s' : St n (ettCt.eval n) × ℕ),
+      ettTape (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n (F n k)
+          g b (dTapes q n W) i x s = .pure (y, s') ∧ s'.2 ≤ s.2 + 1 ∧
+      (gOuter n g).comp ((dHandler q E hE b).impl n z (dHSeed q E hE b n (k, W))) i x
+          (dAbs E hE q b n s) = .pure (y, dAbs E hE q b n s') := by
+  obtain ⟨⟨o, T⟩, j⟩ := s
+  have hj : j < q.eval n := hs
+  refine ⟨(ettStep (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
+      (F n k) g false b (dTapes q n W j) i x (o, T)).1,
+    ((ettStep (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
+      (F n k) g false b (dTapes q n W j) i x (o, T)).2, j + 1),
+    ettTape_apply (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
+      (F n k) g b (dTapes q n W) i x (o, T) j, le_rfl, ?_⟩
+  rw [dTapes_of_lt q n W j hj, QueryImpl.comp_apply, dAbs_eq]
+  simp only
+  match i, x with
+  | 0, x =>
+    have hx : (List.ofFn x).length = n := by
+      rw [List.length_ofFn]
+      show (ettDin 0).eval n = n
+      rw [ettDin_zero, PolyExpr.eval_var]
+    rw [dHandler_impl_enc q E hE b F hFE n z k W x j o hj, simulate_query, gOuter_apply,
+      OracleComp.pure_bind, simulate_pure, OracleComp.pure_bind, ettStep_enc, dAbs_eq,
+      gOuter_pair n g List.length_ofFn (length_maskL (F n k) _ hx), ← encW_eq]
+  | 1, x =>
+    rw [ettStep_dec, decAnsW_eq]
+    by_cases href : refW o (List.ofFn x) = true
+    · rw [dHandler_impl_dec_ref q E hE b n z k W x j o hj href, simulate_pure,
+        OracleComp.pure_bind, dAbs_eq]
+      simp only [href, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false]
+    · rw [Bool.not_eq_true] at href
+      by_cases hwf : wfW n (List.ofFn x) = true
+      · have hwf' := hwf
+        rw [wfW_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hwf'
+        rw [dHandler_impl_dec_wf q E hE b F hFE n z k W x j o hj href hwf, simulate_query,
+          gOuter_apply, OracleComp.pure_bind, simulate_pure, OracleComp.pure_bind, dAbs_eq,
+          gOuter_pair n g hwf'.1 hwf'.2, validW_eq, hwf, href]
+        simp only [Bool.not_false, Bool.true_and, Bool.true_or, Bool.and_true, decide_eq_true_eq]
+        by_cases ht : tagL g (wR (List.ofFn x)) (wC (List.ofFn x)) = wT (List.ofFn x)
+        · rw [if_pos ht, if_pos ht.symm]
+        · rw [if_neg ht, if_neg (Ne.symm ht)]
+      · rw [Bool.not_eq_true] at hwf
+        rw [dHandler_impl_dec_nwf q E hE b n z k W x j o hj href hwf, simulate_pure,
+          OracleComp.pure_bind, dAbs_eq, validW_eq, hwf]
+        simp only [Bool.false_and, Bool.and_false, Bool.false_eq_true, if_false]
+  | 2, x =>
+    cases o with
+    | some c =>
+      rw [dHandler_impl_challenge_some q E hE b n z k W x j c hj, simulate_pure,
+        OracleComp.pure_bind, ettStep_challenge_some, dAbs_eq]
+    | none =>
+      have hmsg : (AdaptiveCPA.msgOf n b (List.ofFn x)).length = n := by
+        have hx : (List.ofFn x).length = n + n := by
+          rw [List.length_ofFn]
+          show (ettDin 2).eval n = n + n
+          rw [ettDin_two, PolyExpr.eval_add, PolyExpr.eval_var]
+        rw [AdaptiveCPA.msgOf_eq]
+        cases b <;> simp [hx]
+      rw [dHandler_impl_challenge_none q E hE b F hFE n z k W x j hj, simulate_query,
+        gOuter_apply, OracleComp.pure_bind, simulate_pure, OracleComp.pure_bind,
+        ettStep_challenge_none, dAbs_eq,
+        gOuter_pair n g List.length_ofFn (length_maskL (F n k) _ hmsg), ← encW_eq]
+
+end Composed
+
+/-! ### The reduction -/
+
+/-- The budget `q(2n)` of the handler's adversary: `(q.subst tagLen).eval n = q(2n)`. -/
+theorem eval_subst_tagLen (q : PolyExpr) (n : ℕ) : (q.subst tagLen).eval n = q.eval (2 * n) := by
+  rw [PolyExpr.eval_subst, tagLen_eval]
+
+/-- **The experiment does not see the output width:** for `d = d'`, the expected first output bit
+of the run through `bitCodec ins outs d` and through `bitCodec ins outs d'` agree.
+
+**Proof sketch.** Substitute `d = d'`. -/
+theorem expect_ettImpl_outLen {ins outs : Fin 3 → ℕ} {c n : ℕ} {d d' : ℕ} (hd : d = d')
+    (f : (Fin n → Bool) → (Fin n → Bool)) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))
+    (rej b : Bool) (A : NUPPT) (Q : ℕ) (r : A.Coins n) :
+    expect (simulate (ettImpl ins outs c n f g rej b) (A.toComp (bitCodec ins outs d) n Q r)
+        (none, [])) (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) =
+      expect (simulate (ettImpl ins outs c n f g rej b) (A.toComp (bitCodec ins outs d') n Q r)
+        (none, [])) (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
+  subst hd
+  rfl
+
+section Reduction
+
+variable (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
+  (E : List Bool → List Bool) (hE : PolyTimeComputable E)
+  (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
+    List.ofFn (F n s x))
+
+include hE hFE in
+/-- **The tag-key PRF reduction** [PS10, Theorem 170.4, step 1]: for a machine adversary `A` with
+budget `q` and a challenge bit `b`, there is a next-query machine `D` such that, at every `n` and
+for every function `g` on `2n` bits, `D` at parameter `2n` with budget `q(2n)` accepts against `g`
+with the probability that `A` outputs `1` in the CCA2 experiment with `f_k` (`k` a uniform `n`-bit
+key) and `g` in place of `f_{k₂}` (the oracles `ettImpl … false b`, on the lengths `ettDin`,
+`ettDout`):
+`𝔼_c [D^g(2n; c) = 1] = 𝔼_k 𝔼_r 𝔼[⟦A's output⟧₀ = 1 | simulate (ettImpl … f_k g false b) (A …) ∅]`.
+
+**Proof sketch.** `D` is the halving (`exists_halfMachine`) of T4 at length `2n` applied to T2's
+machine `B` for `dHandler` with budget `q(2n)` and the input-free companion of the capped adversary
+(`exists_capMachine`). Its coins at `2n` are, through the halving and the bijections of T4, T2, the
+companion and the cap, a seed `(k, W)` and `A`'s coins `r` (`expect_sample_equiv`,
+`ChallengeSim.expect_sample_prod`, `expect_sample_comm`). For fixed seed and coins, T4 and T2 turn
+`D`'s run against `g` into the evaluation, with `g`, of the reduction; evaluation is simulation
+with `gOuter g` (`simulate_ofComp_pure`), which composes with the handler (`simulate_bind`,
+`simulate_comp`, `dHandler_finish`); along the adversary's run (at most `q(2n)` queries) the
+composite is `ettTape` with the tapes of `W` (`simulate_eq_of_abs_bounded`, `comp_dAbs`). Drawing
+`W` uniformly gives fresh nonces (`expect_ettTape`), and the capped adversary at budget `q(2n)` is
+`A` at budget `q(n)` (`exists_capMachine`). Widths are transported by
+`eval_toOracleAdversary_len`, `PRFGame.ofFn_evalFn_toCompOn` and `expect_ettImpl_outLen`. -/
+theorem exists_tagReduction (A : NUPPT) (q : PolyExpr) (b : Bool) :
+    ∃ D : NUPPT, ∀ (n : ℕ) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)),
+      expect (sample (D.Coins (2 * n)))
+          (fun c =>
+            if (D.toOracleAdversary (2 * n) (2 * n) (2 * n) (q.eval (2 * n)) c).eval g = true
+            then (1 : ℝ) else 0) =
+        expect (sample (Fin n → Bool)) fun k => expect (sample (A.Coins n)) fun r =>
+          expect (simulate (ettImpl (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
+              (ettCt.eval n) n (F n k) g false b)
+              (A.toComp (bitCodec (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) 1) n
+                (q.eval n) r) (none, []))
+            (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
+  obtain ⟨A₁, hA₁c, hA₁⟩ := exists_capMachine A q
+  obtain ⟨A₂, -, hA₂⟩ := exists_toCompOn_of_toComp A₁
+  obtain ⟨B, hB⟩ := exists_interactiveHandlerMachine A₂ (q.subst tagLen) ettDin ettDout tagOut
+    tagOut (.const 1) (dHandler (q.subst tagLen) E hE b)
+  obtain ⟨B', -, hB'⟩ := exists_toOracleAdversary_of_bitCodec B tagLen tagLen
+  obtain ⟨D, hD⟩ := exists_halfMachine B'
+  refine ⟨D, fun n g => ?_⟩
+  obtain ⟨φ₀, hφ₀⟩ := hA₂ n
+  obtain ⟨φ₂, hφ₂⟩ := hB n
+  obtain ⟨φ₄, hφ₄⟩ := hB' n
+  have hq₂ : (q.subst tagLen).eval n = q.eval (2 * n) := eval_subst_tagLen q n
+  have hQ : (q.subst tagLen).eval n * (dHandler (q.subst tagLen) E hE b).perCall.eval n +
+      (dHandler (q.subst tagLen) E hE b).finCall.eval n = q.eval (2 * n) := by
+    rw [dHandler_perCall, dHandler_finCall, PolyExpr.eval_const, PolyExpr.eval_const, hq₂]
+    ring
+  have hout : (dHandler (q.subst tagLen) E hE b).outLen.eval n = 1 := by
+    rw [dHandler_outLen, PolyExpr.eval_const]
+  have hle : q.eval n ≤ (q.subst tagLen).eval n := by
+    rw [hq₂]
+    exact q.eval_mono (by omega)
+  -- `D`'s coins at `2n` are `B'`'s at `n`, then a seed and `A`'s coins.
+  rw [hD n (2 * n) (2 * n) (q.eval (2 * n)) g, ← expect_sample_equiv φ₄, ← expect_sample_equiv φ₂,
+    ChallengeSim.expect_sample_prod, expect_sample_comm, ← expect_sample_equiv φ₀,
+    ← expect_sample_equiv (NUPPT.coinsCongr hA₁c n)]
+  conv_rhs => rw [expect_sample_comm]
+  refine congrArg _ (funext fun r => ?_)
+  rw [← expect_sample_equiv (dHSeed (q.subst tagLen) E hE b n), ChallengeSim.expect_sample_prod]
+  refine congrArg _ (funext fun k => ?_)
+  -- One run of `D` is the reduction evaluated with `g`.
+  have hrun : ∀ W : Fin ((q.subst tagLen).eval n * n) → Bool,
+      (if (B'.toOracleAdversary n (2 * n) (2 * n) (q.eval (2 * n))
+          (φ₄ (φ₂ (dHSeed (q.subst tagLen) E hE b n (k, W),
+            φ₀ (NUPPT.coinsCongr hA₁c n r))))).eval g = true then (1 : ℝ) else 0) =
+      expect (simulate (ettTape (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
+          (ettCt.eval n) n (F n k) g b (dTapes (q.subst tagLen) n W))
+          (A₂.toCompOn (bitCodec (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
+            ((PolyExpr.const 1).eval n)) n ((q.subst tagLen).eval n) []
+            (φ₀ (NUPPT.coinsCongr hA₁c n r))) ((none, []), 0))
+        (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
+    intro W
+    have key : ∀ v : Fin 1 → Bool, (if v 0 = true then (1 : ℝ) else 0) =
+        if (List.ofFn v).headD false = true then 1 else 0 := fun v => by
+      rw [headD_ofFn_one]
+    have h2 : _ = B.toCompOn (bitCodec (fun _ : Fin 1 => tagLen.eval n)
+        (fun _ => tagLen.eval n) ((dHandler (q.subst tagLen) E hE b).outLen.eval n)) n
+        ((q.subst tagLen).eval n * (dHandler (q.subst tagLen) E hE b).perCall.eval n +
+          (dHandler (q.subst tagLen) E hE b).finCall.eval n)
+        [] (φ₂ (dHSeed (q.subst tagLen) E hE b n (k, W), φ₀ (NUPPT.coinsCongr hA₁c n r))) :=
+      hφ₂ [] (dHSeed (q.subst tagLen) E hE b n (k, W)) (φ₀ (NUPPT.coinsCongr hA₁c n r))
+    rw [eval_toOracleAdversary_len B' n _ _ (tagLen_eval n), hφ₄, ← hQ, key,
+      PRFGame.ofFn_evalFn_toCompOn hout.symm B n _ [] _, ← h2, dHandler_advInput]
+    have hev : simulate (gOuter n g) ((simulate ((dHandler (q.subst tagLen) E hE b).impl n []
+        (dHSeed (q.subst tagLen) E hE b n (k, W)))
+        (A₂.toCompOn (bitCodec (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
+          ((PolyExpr.const 1).eval n)) n ((q.subst tagLen).eval n) []
+          (φ₀ (NUPPT.coinsCongr hA₁c n r)))
+        ((dHandler (q.subst tagLen) E hE b).init n)).bind
+        (fun res => (dHandler (q.subst tagLen) E hE b).finish n []
+          (dHSeed (q.subst tagLen) E hE b n (k, W)) res.2 res.1)) () = _ :=
+      simulate_ofComp_pure _ _ _
+    have h1 := congrArg (fun c => expect c
+      (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0)) hev
+    simp only [expect_pure] at h1
+    refine h1.symm.trans ?_
+    rw [simulate_bind, simulate_comp, OracleComp.bind_assoc, expect_bind]
+    simp only [OracleComp.pure_bind, dHandler_finish, simulate_pure, expect_pure]
+    rw [dHandler_init_hstate, show (dHState (q.subst tagLen) E hE b n 0 none, ()) =
+        dAbs E hE (q.subst tagLen) b n ((none, []), 0) from
+          (dAbs_eq E hE (q.subst tagLen) b n ((none, []), 0)).symm,
+      simulate_eq_of_abs_bounded _ _ (dAbs E hE (q.subst tagLen) b n) (fun s => s.2)
+        ((q.subst tagLen).eval n)
+        (fun i x s hs => comp_dAbs F E hE hFE (q.subst tagLen) b n g [] k W i x s hs) _
+        ((q.subst tagLen).eval n) (A₂.toCompOn_costBoundedBy _ n _ _ _) ((none, []), 0)
+        (Nat.zero_add _).le,
+      expect_bind]
+    simp only [expect_pure]
+    refine congrArg _ (funext fun p => ?_)
+    rw [ofFn_padFin_of_length (by rw [List.length_ofFn, dHandler_outLen])]
+  simp only [hrun, dTapes_eq]
+  rw [expect_sample_equiv (EnsembleLemmas.blocks ((q.subst tagLen).eval n) n) (fun T =>
+      expect (simulate (ettTape (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
+          (ettCt.eval n) n (F n k) g b (AdaptiveCPA.extTape T))
+          (A₂.toCompOn (bitCodec (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
+            ((PolyExpr.const 1).eval n)) n ((q.subst tagLen).eval n) []
+            (φ₀ (NUPPT.coinsCongr hA₁c n r))) ((none, []), 0))
+        (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0)),
+    expect_ettTape _ _ _ _ _ _ _ ((q.subst tagLen).eval n)
+      (fun a => if (List.ofFn a).headD false = true then (1 : ℝ) else 0) _
+      ((q.subst tagLen).eval n) (A₂.toCompOn_costBoundedBy _ n _ _ _) (none, []) 0 (by omega),
+    hφ₀, hA₁ n _ _ _ _ _ hle]
+  exact expect_ettImpl_outLen (PolyExpr.eval_const 1 n) _ _ _ _ A _ r
+
+/-- **The PRF advantage as expectations** (PRFGame overlap: `prfAdv_prfReduction`, re-derived here
+in general form from the published readers): for an oracle adversary `A'` on `m`-bit strings,
+`prfAdv F A' = |𝔼_k 𝔼_c [A'(c)^{F k} = 1] − 𝔼_R 𝔼_c [A'(c)^R = 1]|`.
+
+**Proof sketch.** `prfAdv_def`, `distAdv_def`; each acceptance probability is an average over the
+key (resp. the function table) and the coins (`Bridge.acceptProb_eq`, `accept_eq`,
+`Bridge.acceptGame_eq`, `prob_bind`, `oracleDist_apply`, `randomFunction_apply`). -/
+theorem prfAdv_eq_expect {m : ℕ} (Fm : (Fin m → Bool) → (Fin m → Bool) → (Fin m → Bool))
+    {ρ : Type} [Fintype ρ] [Nonempty ρ] (A' : OracleAdversary ρ (Fin m → Bool) (Fin m → Bool)) :
+    prfAdv Fm A' =
+      |expect (sample (Fin m → Bool))
+          (fun k => expect (sample ρ) fun c => if (A' c).eval (Fm k) = true then (1 : ℝ) else 0) -
+        expect (sample ((Fin m → Bool) → (Fin m → Bool)))
+          (fun R => expect (sample ρ) fun c => if (A' c).eval R = true then (1 : ℝ) else 0)| := by
+  rw [prfAdv_def, distAdv_def, Bridge.acceptProb_eq, Bridge.acceptProb_eq, accept_eq, accept_eq,
+    Bridge.acceptGame_eq, Bridge.acceptGame_eq, prob_bind, prob_bind]
+  congr 2
+  · refine congrArg _ (funext fun k => ?_)
+    simp only [prob_bind, prob_pure, oracleDist_apply]
+  · refine congrArg _ (funext fun R => ?_)
+    simp only [prob_bind, prob_pure, oracleDist_apply, randomFunction_apply]
+
+include hE hFE in
+/-- **Step 1 of [PS10, Thm 170.4]: the tag key becomes a random function**,
+`∃ D, ∀ n, |𝔼_{k₁} 𝔼_{k₂} ettAcc … (F n k₁) (F (2n) k₂) false b A (q n) -
+𝔼_{k₁} 𝔼_R ettAcc … (F n k₁) R false b A (q n)| =
+prfAdv (F (2n)) (D.toOracleAdversary (2n) (2n) (2n) (q (2n)))`.
+For a machine adversary `A` with budget `q` and a challenge bit `b` there is a next-query machine
+`D` such that at
+every `n` the gap between the experiments with the tag functions `f_{k₂}` (`k₂` a uniform `2n`-bit
+key) and a uniform random function on `2n` bits, the pad function being `f_{k₁}`, is the PRF
+advantage of `D` at parameter `2n` with budget `q(2n)`.
+
+**Proof sketch.** `exists_tagReduction` gives `D` and its acceptance probability against every `g`;
+`prfAdv_eq_expect` writes the advantage as the gap between the averages over `k₂` and over the
+function table; exchange the averages with the key `k₁` (`expect_sample_comm`). -/
+theorem exists_tagStep (A : NUPPT) (q : PolyExpr) (b : Bool) :
+    ∃ D : NUPPT, ∀ n : ℕ,
+      |(expect (sample (Fin n → Bool)) fun k => expect (sample (Fin (2 * n) → Bool)) fun k₂ =>
+          ettAcc (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
+            (F n k) (F (2 * n) k₂) false b A (q.eval n)) -
+        (expect (sample (Fin n → Bool)) fun k =>
+          expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))) fun R =>
+            ettAcc (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
+              (F n k) R false b A (q.eval n))| =
+        prfAdv (F (2 * n)) (D.toOracleAdversary (2 * n) (2 * n) (2 * n) (q.eval (2 * n))) := by
+  obtain ⟨D, hD⟩ := exists_tagReduction F E hE hFE A q b
+  refine ⟨D, fun n => ?_⟩
+  rw [prfAdv_eq_expect]
+  simp only [hD n, ettAcc_eq]
+  rw [expect_sample_comm (α := Fin n → Bool) (β := Fin (2 * n) → Bool),
+    expect_sample_comm (α := Fin n → Bool) (β := (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))]
+
+end Reduction
+
+end TCSlib.Cryptography.Composability.ETTGame
diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Tools.lean b/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Tools.lean
new file mode 100644
index 000000000..e1d041898
--- /dev/null
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Tools.lean
@@ -0,0 +1,295 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Games.Hopping
+import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Hybrid
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Simulation tools for the encrypt-then-tag proof
+
+Generic facts on simulations of oracle computations used by the proof of [PS10, Theorem 170.4]
+(`Composability.ccaScheme_cca2`). They are stated for arbitrary oracle specifications and are
+candidates for promotion to the `Games` layer.
+
+* **Simulation through a state abstraction, in law** (`expect_simulate_abs`): if every call of
+  `impl₁` from the abstract image `f s` has the law of the call of `impl₂` from `s` with its new
+  state abstracted, so do whole simulations, along runs within a query budget.
+* **Coins in advance** (`expect_simulate_tapeImpl`): an implementation that draws one fresh coin
+  `t` per query (`freshImpl`) has the law of the implementation that reads the `j`-th query's coin
+  from a tape `T j` drawn in advance (`tapeImpl`), for computations with at most `κ` queries.
+* **Functions overridden by a table** (`ovr`): `ovr M R` is `R` with the values of the table `M`
+  written over it; resampling `R` at a point outside the table moves into the table
+  (`expect_sample_ovr`).
+
+## Main definitions
+
+* `ETTGame.freshImpl`, `ETTGame.tapeImpl`: per-query coins drawn fresh, and read from tapes.
+* `ETTGame.ovr`: a function overridden by a finite table.
+
+## Main results
+
+* `ETTGame.expect_simulate_abs`, `ETTGame.expect_simulate_abs_inv`,
+  `ETTGame.expect_simulate_tapeImpl`, `ETTGame.expect_sample_ovr`.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 170.4 (book p. 170).
+-/
+
+namespace TCSlib.Cryptography.Composability.ETTGame
+
+open TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp
+
+/-! ### Simulation through a state abstraction, in law -/
+
+section Abs
+
+variable {ι : Type} {spec : OracleSpec ι} {σ₁ σ₂ α : Type}
+
+/-- **Simulation through a state abstraction, in law, along runs with a query budget.** Let every
+call of `impl₂` from a state `s` with `cnt s < κ` raise `cnt` by at most one, and give every
+function `g` of the answer and the abstracted new state the expectation that the call of `impl₁`
+from `f s` gives it. Then for a computation `c` with at most `m` queries and `cnt s + m ≤ κ`,
+`𝔼[G] (simulate impl₁ c (f s)) = 𝔼[fun p => G (p.1, f p.2)] (simulate impl₂ c s)`.
+
+**Proof sketch.** Induction on `c`. A query costs one unit, so it is asked from a state with
+`cnt s < κ`: rewrite the call of `impl₁` by the hypothesis, and on each possible outcome of the
+call of `impl₂` (where `cnt` grew by at most one) apply the induction hypothesis
+(`expect_congr_of_allOutputs`). -/
+theorem expect_simulate_abs (impl₁ : QueryImpl spec σ₁ unifSpec)
+    (impl₂ : QueryImpl spec σ₂ unifSpec) (f : σ₂ → σ₁) (cnt : σ₂ → ℕ) (κ : ℕ)
+    (h : ∀ i x s, cnt s < κ → ∀ g : spec.rng i × σ₁ → ℝ,
+      expect (impl₁ i x (f s)) g = expect (impl₂ i x s) fun p => g (p.1, f p.2))
+    (hcnt : ∀ i x s, cnt s < κ → (impl₂ i x s).AllOutputs fun p => cnt p.2 ≤ cnt s + 1)
+    (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ₂)
+    (hs : cnt s + m ≤ κ) (G : α × σ₁ → ℝ) :
+    expect (simulate impl₁ c (f s)) G = expect (simulate impl₂ c s) fun p => G (p.1, f p.2) := by
+  induction c generalizing m s with
+  | pure a => simp only [simulate_pure, expect_pure]
+  | query i x k ih =>
+    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
+    have hm1 : 1 ≤ m := hm
+    rw [simulate_query, simulate_query, expect_bind, expect_bind, h i x s (by omega)]
+    refine expect_congr_of_allOutputs (hcnt i x s (by omega)) fun p hp => ?_
+    exact ih p.1 (m - 1) (hk p.1) p.2 (by omega)
+
+/-- **Simulation through a state abstraction, in law, along runs with a query budget and an
+invariant:** as `expect_simulate_abs`, with the hypotheses only on the states satisfying an
+invariant `P` that every call of `impl₂` keeps: for `c` with at most `m` queries, `P s` and
+`cnt s + m ≤ κ`, `𝔼[G | simulate impl₁ c (f s)] = 𝔼[fun p => G (p.1, f p.2) | simulate impl₂ c s]`.
+
+**Proof sketch.** As `expect_simulate_abs`, carrying `P` through the possible outcomes. -/
+theorem expect_simulate_abs_inv (impl₁ : QueryImpl spec σ₁ unifSpec)
+    (impl₂ : QueryImpl spec σ₂ unifSpec) (f : σ₂ → σ₁) (P : σ₂ → Prop) (cnt : σ₂ → ℕ) (κ : ℕ)
+    (h : ∀ i x s, P s → cnt s < κ → ∀ g : spec.rng i × σ₁ → ℝ,
+      expect (impl₁ i x (f s)) g = expect (impl₂ i x s) fun p => g (p.1, f p.2))
+    (hcnt : ∀ i x s, P s → cnt s < κ →
+      (impl₂ i x s).AllOutputs fun p => P p.2 ∧ cnt p.2 ≤ cnt s + 1)
+    (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ₂) (hP : P s)
+    (hs : cnt s + m ≤ κ) (G : α × σ₁ → ℝ) :
+    expect (simulate impl₁ c (f s)) G = expect (simulate impl₂ c s) fun p => G (p.1, f p.2) := by
+  induction c generalizing m s with
+  | pure a => simp only [simulate_pure, expect_pure]
+  | query i x k ih =>
+    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
+    have hm1 : 1 ≤ m := hm
+    rw [simulate_query, simulate_query, expect_bind, expect_bind, h i x s hP (by omega)]
+    refine expect_congr_of_allOutputs (hcnt i x s hP (by omega)) fun p hp => ?_
+    exact ih p.1 (m - 1) (hk p.1) p.2 hp.1 (by omega)
+
+end Abs
+
+/-! ### Coins drawn fresh and coins in advance -/
+
+section Tapes
+
+variable {ι : Type} {spec : OracleSpec ι} {σ τ α : Type}
+
+/-- **One fresh coin per query:** the query `x` to oracle `i` in state `s` draws a uniform
+`t ∈ τ`, then runs `K i x s t`. -/
+noncomputable def freshImpl [Fintype τ] [Nonempty τ]
+    (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ)) :
+    QueryImpl spec σ unifSpec :=
+  fun i x s => (sample τ).bind (K i x s)
+
+/-- `freshImpl K i x s = (sample τ).bind (K i x s)`. -/
+theorem freshImpl_apply [Fintype τ] [Nonempty τ]
+    (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ)) (i : ι)
+    (x : spec.dom i) (s : σ) : freshImpl K i x s = (sample τ).bind (K i x s) :=
+  rfl
+
+/-- **One coin per query, from tapes in advance:** the query `x` to oracle `i` in state `(s, j)`
+runs `K i x s (T j)` and advances the query counter `j`,
+`tapeImpl K T i x (s, j) = (K i x s (T j)).bind fun p => pure (p.1, (p.2, j + 1))`. -/
+def tapeImpl (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ)) (T : ℕ → τ) :
+    QueryImpl spec (σ × ℕ) unifSpec :=
+  fun i x s => (K i x s.1 (T s.2)).bind fun p => .pure (p.1, (p.2, s.2 + 1))
+
+/-- `tapeImpl K T i x (s, j) = (K i x s (T j)).bind fun p => pure (p.1, (p.2, j + 1))`. -/
+theorem tapeImpl_apply (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ)) (T : ℕ → τ)
+    (i : ι) (x : spec.dom i) (s : σ) (j : ℕ) :
+    tapeImpl K T i x (s, j) = (K i x s (T j)).bind fun p => .pure (p.1, (p.2, j + 1)) :=
+  rfl
+
+/-- **The run from the counter `j` ignores the tapes below `j`:** if `T m = T' m` for every
+`m ≥ j`, the runs of `tapeImpl K T` and `tapeImpl K T'` from `(s, j)` agree.
+
+**Proof sketch.** Induction on the computation: a query at counter `j' ≥ j` reads `T j'` and
+moves to `j' + 1`. -/
+theorem simulate_tapeImpl_congr (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ))
+    (T T' : ℕ → τ) (c : OracleComp spec α) (s : σ) (j : ℕ) (hT : ∀ m, j ≤ m → T m = T' m) :
+    simulate (tapeImpl K T) c (s, j) = simulate (tapeImpl K T') c (s, j) := by
+  induction c generalizing s j with
+  | pure a => rw [simulate_pure, simulate_pure]
+  | query i x k ih =>
+    rw [simulate_query, simulate_query, tapeImpl_apply, tapeImpl_apply, hT j le_rfl,
+      OracleComp.bind_assoc, OracleComp.bind_assoc]
+    congr 1
+    funext p
+    rw [OracleComp.pure_bind, OracleComp.pure_bind]
+    exact ih p.1 p.2 (j + 1) fun m hm => hT m (by omega)
+
+/-- **Coins in advance have the law of fresh coins:** for a computation with at most `m` queries,
+a counter `j` with `j + m ≤ κ`, and every function `G` of the output,
+`𝔼_{T ← τ^κ} 𝔼[G (simulate (tapeImpl K (extTape T)) c (s, j))] = 𝔼[G (simulate (freshImpl K) c s)]`.
+
+**Proof sketch.** Induction on `c`, generalizing the counter, the state and the budget. A query
+costs one unit, so it reads the tape `T j` with `j < κ`; the continuation runs from `j + 1`, so it
+ignores `T j` (`simulate_tapeImpl_congr`, `AdaptiveCPA.extTape_update`), and
+`ProbComp.expect_sample_coord` replaces `T j` by the fresh coin of `freshImpl`
+(`expect_expect_sample` exchanges the tape with the call). -/
+theorem expect_simulate_tapeImpl [Fintype τ] [Nonempty τ]
+    (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ))
+    (κ : ℕ) (G : α → ℝ) (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m)
+    (s : σ) (j : ℕ) (hj : j + m ≤ κ) :
+    expect (sample (Fin κ → τ))
+        (fun T => expect (simulate (tapeImpl K (AdaptiveCPA.extTape T)) c (s, j))
+          fun p => G p.1) =
+      expect (simulate (freshImpl K) c s) fun p => G p.1 := by
+  induction c generalizing m s j with
+  | pure a =>
+    simp only [simulate_pure, expect_pure]
+    exact expect_const _ _
+  | query i x k ih =>
+    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
+    have hm1 : 1 ≤ m := hm
+    have hjk : j < κ := by omega
+    let jj : Fin κ := ⟨j, hjk⟩
+    have hT : ∀ T : Fin κ → τ, AdaptiveCPA.extTape T j = T jj :=
+      fun T => AdaptiveCPA.extTape_of_lt T hjk
+    simp only [simulate_query, tapeImpl_apply, freshImpl_apply, OracleComp.bind_assoc,
+      OracleComp.pure_bind, expect_bind, hT]
+    refine (expect_sample_coord jj (fun t T => expect (K i x s t) fun p =>
+      expect (simulate (tapeImpl K (AdaptiveCPA.extTape T)) (k p.1) (p.2, j + 1))
+        fun q => G q.1) ?_).trans ?_
+    · intro t t' T
+      show expect (K i x s t) (fun p => expect (simulate (tapeImpl K
+          (AdaptiveCPA.extTape (Function.update T jj t'))) (k p.1) (p.2, j + 1)) fun q => G q.1) =
+        expect (K i x s t) fun p => expect (simulate (tapeImpl K (AdaptiveCPA.extTape T)) (k p.1)
+          (p.2, j + 1)) fun q => G q.1
+      refine congrArg _ (funext fun p => ?_)
+      refine congrArg (fun c => expect c fun q => G q.1)
+        (simulate_tapeImpl_congr K _ _ _ _ _ fun m' hm' => ?_)
+      exact AdaptiveCPA.extTape_update T jj t' (by
+        intro h
+        have : m' = j := h
+        omega)
+    · refine congrArg _ (funext fun t => ?_)
+      rw [← expect_expect_sample]
+      refine congrArg _ (funext fun p => ?_)
+      exact ih p.1 (m - 1) (hk p.1) p.2 (j + 1) (by omega)
+
+end Tapes
+
+/-! ### Functions overridden by a table -/
+
+section Override
+
+variable {κ β : Type} [DecidableEq κ]
+
+/-- **A function overridden by a table:** `ovr M R` is `R` with the entries `(p, y)` of `M`
+written over it, the first entry of a key winning: `ovr [] R = R`,
+`ovr ((p, y) :: M) R = update (ovr M R) p y`. -/
+def ovr : List (κ × β) → (κ → β) → κ → β
+  | [], R => R
+  | e :: M, R => Function.update (ovr M R) e.1 e.2
+
+/-- `ovr [] R = R`. -/
+theorem ovr_nil (R : κ → β) : ovr ([] : List (κ × β)) R = R :=
+  rfl
+
+/-- `ovr ((p, y) :: M) R = update (ovr M R) p y`. -/
+theorem ovr_cons (p : κ) (y : β) (M : List (κ × β)) (R : κ → β) :
+    ovr ((p, y) :: M) R = Function.update (ovr M R) p y :=
+  rfl
+
+/-- Outside the keys of the table, the overridden function is `R`:
+`p ∉ M.map Prod.fst → ovr M R p = R p`. -/
+theorem ovr_of_not_mem {M : List (κ × β)} {p : κ} (hp : p ∉ M.map Prod.fst) (R : κ → β) :
+    ovr M R p = R p := by
+  induction M with
+  | nil => rfl
+  | cons e M ih =>
+    obtain ⟨q, y⟩ := e
+    simp only [List.map_cons, List.mem_cons, not_or] at hp
+    rw [ovr_cons, Function.update_of_ne hp.1]
+    exact ih hp.2
+
+/-- On the keys of the table, the overridden function does not read `R`:
+`p ∈ M.map Prod.fst → ovr M R p = ovr M R' p`. -/
+theorem ovr_of_mem {M : List (κ × β)} {p : κ} (hp : p ∈ M.map Prod.fst) (R R' : κ → β) :
+    ovr M R p = ovr M R' p := by
+  induction M with
+  | nil => simp at hp
+  | cons e M ih =>
+    obtain ⟨q, y⟩ := e
+    rw [ovr_cons, ovr_cons]
+    by_cases hpq : p = q
+    · subst hpq
+      rw [Function.update_self, Function.update_self]
+    · rw [Function.update_of_ne hpq, Function.update_of_ne hpq]
+      simp only [List.map_cons, List.mem_cons] at hp
+      exact ih (hp.resolve_left hpq)
+
+/-- Changing `R` at a point outside the table changes the overridden function there only:
+`p ∉ M.map Prod.fst → ovr M (update R p y) = update (ovr M R) p y`. -/
+theorem ovr_update {M : List (κ × β)} {p : κ} (hp : p ∉ M.map Prod.fst) (R : κ → β) (y : β) :
+    ovr M (Function.update R p y) = Function.update (ovr M R) p y := by
+  induction M with
+  | nil => rfl
+  | cons e M ih =>
+    obtain ⟨q, z⟩ := e
+    simp only [List.map_cons, List.mem_cons, not_or] at hp
+    rw [ovr_cons, ovr_cons, ih hp.2]
+    exact Function.update_comm hp.1 _ _ _
+
+variable [Fintype κ] [Fintype β] [Nonempty β]
+
+/-- **Resampling a point outside the table moves it into the table:** for `p` not a key of `M`,
+`𝔼_R F (R p) (ovr M R) = 𝔼_y 𝔼_R F y (ovr ((p, y) :: M) R)`.
+
+**Proof sketch.** `ProbComp.expect_sample_coord` at the coordinate `p` with
+`F' y R = F y (ovr ((p, y) :: M) R)`, which does not read `R p` (`ovr_update`,
+`Function.update_idem`); at `y = R p` the new entry repeats `ovr M R p = R p`
+(`ovr_of_not_mem`, `Function.update_eq_self`). -/
+theorem expect_sample_ovr (M : List (κ × β)) {p : κ} (hp : p ∉ M.map Prod.fst)
+    (F : β → (κ → β) → ℝ) :
+    expect (sample (κ → β)) (fun R => F (R p) (ovr M R)) =
+      expect (sample β) fun y => expect (sample (κ → β)) fun R => F y (ovr ((p, y) :: M) R) := by
+  have h := expect_sample_coord p (fun y R => F y (ovr ((p, y) :: M) R)) fun y y' R => by
+    show F y (ovr ((p, y) :: M) (Function.update R p y')) = F y (ovr ((p, y) :: M) R)
+    rw [ovr_cons, ovr_cons, ovr_update hp, Function.update_idem]
+  refine Eq.trans ?_ h
+  refine congrArg _ (funext fun R => ?_)
+  show F (R p) (ovr M R) = F (R p) (ovr ((p, R p) :: M) R)
+  rw [ovr_cons, ← ovr_of_not_mem hp R, Function.update_eq_self]
+
+end Override
+
+end TCSlib.Cryptography.Composability.ETTGame
diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Transfer.lean b/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Transfer.lean
new file mode 100644
index 000000000..4918c8edd
--- /dev/null
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Transfer.lean
@@ -0,0 +1,222 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Games
+import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
+import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.ChallengeSim
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# From the CCA2 experiment to the experiment with a pad and a tag function
+
+Generic transfer lemmas for step 1 of [PS10, Theorem 170.4]: a fixed-length private-key scheme
+whose encryption with a key is `⟨r, ⟨c₁, g(r ‖ c₁)⟩⟩` with `c₁ = m ⊕ f(r)` and a uniform nonce `r`,
+and whose decryption answers `⟨1, c₁ ⊕ f(r)⟩` on valid words (`validW g`) and `⊥` otherwise, has,
+call by call, the oracles `ettImpl … f g false b` of the CCA2 experiment
+(`expect_indImpl_ettImpl`); so the experiment `IND_b` is the experiment with `f` and `g`, averaged
+over the key (`accept_indGame_eq`).
+
+## Main definitions
+
+* `ETTGame.stRec`: the challenge record of the experiment's state, `stRec s = s.1`.
+
+## Main results
+
+* `ETTGame.expect_indImpl_ettImpl`: one call of `IND_b` has the law of `ettImpl`.
+* `ETTGame.accept_indGame_eq`: the CCA2 experiment as the experiment with a pad and a tag
+  function.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Algorithm 169.3 and Theorem 170.4 (book pp. 169–171).
+-/
+
+namespace TCSlib.Cryptography.Composability.ETTGame
+
+open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp
+
+/-- The challenge record of the experiment's state: `stRec s = s.1`. -/
+def stRec {n d : ℕ} (s : St n d) : Option (Fin d → Bool) := s.1
+
+/-- `stRec s = s.1`. -/
+theorem stRec_eq {n d : ℕ} (s : St n d) : stRec s = s.1 := rfl
+
+section Transfer
+
+variable (S : FixedLengthScheme) (b : Bool) (n : ℕ) (key : List Bool)
+  (f : (Fin n → Bool) → (Fin n → Bool)) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))
+
+/-- **One call of `IND_b` under CCA2 with the key `key` has the law of `ettImpl` with `f` and `g`**,
+for every function `G` of the answer and the record, for a scheme `S` whose encryption with `key`
+is `encW f g` with the nonce `ν re` of a bijection `ν` (`henc`), whose decryption is `decL f` on
+valid words and `⊥` otherwise (`hdec`), with `(6n + 4)`-bit ciphertexts:
+`𝔼[G] (S.indImpl .cca2 b n key i x (stRec s)) = 𝔼[G ∘ (id × stRec)] (ettImpl … f g false b i x s)`.
+
+**Proof sketch.** By the oracle (the `_onSpec` readers). Encryption and the first challenge
+sample the coins of `Enc`, which are the nonce (`expect_sample_equiv ν`), and encrypt as `encW`;
+the selected half is `msgOf` (`ofFn_splitHalf_fst`, `_snd`). Decryption refuses the record
+(`refW`) and otherwise answers `decAnsW`; its coins and the experiment's nonce are unused
+(`expect_const`). A repeated challenge returns the record. -/
+theorem expect_indImpl_ettImpl (hct : S.ctLen.eval n = 6 * n + 4)
+    (ν : S.enc.Coins n ≃ (Fin n → Bool))
+    (henc : ∀ (m : Fin n → Bool) (re : S.enc.Coins n),
+      List.ofFn (S.encryptAt n key m re) = encW f g (ν re) (List.ofFn m))
+    (hdec : ∀ (w : List Bool) (rd : S.dec.Coins n),
+      List.ofFn (FixedLengthScheme.decAnswer (decodeFin n
+          (S.dec.runAt n (pairEncode key w) rd))) =
+        if validW g w = true then decL f w else List.replicate (n + 1) false)
+    (i : Fin 3) (x : (S.indSpec n).dom i) (s : St n (S.ctLen.eval n))
+    (G : (S.indSpec n).rng i × Option (Fin (S.ctLen.eval n) → Bool) → ℝ) :
+    expect (S.indImpl .cca2 b n key i x (stRec s)) G =
+      expect (ettImpl (S.inLens n) (S.outLens n) (S.ctLen.eval n) n f g false b i x s)
+        (fun p => G (p.1, stRec p.2)) := by
+  have hlenEnc : ∀ (r : Fin n → Bool) {m : List Bool}, m.length = n →
+      (encW f g r m).length = S.ctLen.eval n := fun r m hm => by rw [length_encW f g r hm, hct]
+  rw [ettImpl_apply, expect_bind]
+  match i, x with
+  | 0, m =>
+    rw [S.indImpl_enc_onSpec, expect_bind, ← expect_sample_equiv ν]
+    refine congrArg _ (funext fun re => ?_)
+    rw [expect_pure, expect_pure, ettStep_enc, stRec_eq, stRec_eq]
+    have hm : List.ofFn (cast (S.indSpec_encDom n) m) = List.ofFn m :=
+      ofFn_cast (S.inLens_zero n) _ m
+    have hm' : cast (S.indSpec_encDom n) m = padFin n (List.ofFn m) :=
+      List.ofFn_injective (by rw [hm, ofFn_padFin_of_length (by
+        rw [List.length_ofFn, S.inLens_zero])])
+    have hmn : (List.ofFn m).length = n := by rw [List.length_ofFn, S.inLens_zero]
+    congr 2
+    refine List.ofFn_injective ?_
+    rw [ofFn_cast (S.outLens_zero n).symm _ _, hm', henc, ofFn_padFin_of_length hmn,
+      ofFn_padFin_of_length (by rw [hlenEnc _ hmn, S.outLens_zero])]
+  | 1, c =>
+    rw [S.indImpl_dec_onSpec, FixedLengthScheme.decOpen_cca2, Bool.true_and]
+    have hc : List.ofFn (cast (S.indSpec_decDom n) c) = List.ofFn c :=
+      ofFn_cast (S.inLens_one n) _ c
+    have href : (!decide (s.1 = some (cast (S.indSpec_decDom n) c))) =
+        !refW s.1 (List.ofFn c) := by
+      obtain ⟨o, T⟩ := s
+      cases o with
+      | none => simp [refW_none]
+      | some c' =>
+        rw [refW_some]
+        simp only [Option.some.injEq]
+        congr 1
+        exact decide_eq_decide.2 ⟨fun h => by rw [h, hc],
+          fun h => List.ofFn_injective (h.trans hc.symm)⟩
+    simp only [expect_pure, ettStep_dec, stRec_eq]
+    rw [expect_const]
+    by_cases hr : refW s.1 (List.ofFn c) = true
+    · rw [if_neg (by rw [href, hr]; exact Bool.false_ne_true), expect_pure, decAnsW_eq,
+        if_neg (by rw [hr]; simp), padFin_nil]
+    · rw [Bool.not_eq_true] at hr
+      rw [if_pos (by rw [href, hr]; rfl), expect_bind]
+      refine (congrArg _ (funext fun rd => ?_)).trans (expect_const _ _)
+      rw [expect_pure]
+      congr 2
+      refine List.ofFn_injective ?_
+      rw [ofFn_cast (S.outLens_one n).symm _ _, hc, hdec, decAnsW_eq, hr]
+      simp only [Bool.not_false, Bool.true_and, Bool.true_or, Bool.and_true]
+      by_cases hv : validW g (List.ofFn c) = true
+      · rw [if_pos hv, if_pos hv]
+        have hlen : (decL f (List.ofFn c)).length = S.outLens n 1 := by
+          rw [validW_eq, Bool.and_eq_true, wfW_eq, Bool.and_eq_true, decide_eq_true_eq,
+            decide_eq_true_eq] at hv
+          rw [decL_eq, List.length_cons, List.length_zipWith, List.length_ofFn, hv.1.2,
+            Nat.min_self, S.outLens_one]
+        rw [ofFn_padFin_of_length hlen]
+      · rw [if_neg hv, if_neg hv, padFin_nil, ofFn_zeroBits, S.outLens_one]
+  | 2, mm =>
+    have hmm : List.ofFn (cast (S.indSpec_challengeDom n) mm) = List.ofFn mm :=
+      ofFn_cast (S.inLens_two n) _ mm
+    have hmsg : (AdaptiveCPA.msgOf n b (List.ofFn mm)).length = n := by
+      have : (List.ofFn mm).length = n + n := by rw [List.length_ofFn, S.inLens_two]
+      rw [AdaptiveCPA.msgOf_eq]
+      cases b <;> simp [this]
+    have hsel : (if b then (FixedLengthScheme.splitHalf
+        (cast (S.indSpec_challengeDom n) mm)).2 else (FixedLengthScheme.splitHalf
+        (cast (S.indSpec_challengeDom n) mm)).1) =
+        padFin n (AdaptiveCPA.msgOf n b (List.ofFn mm)) := by
+      refine List.ofFn_injective ?_
+      rw [ofFn_padFin_of_length hmsg, AdaptiveCPA.msgOf_eq, ← hmm]
+      cases b
+      · exact FixedLengthScheme.ofFn_splitHalf_fst _
+      · exact FixedLengthScheme.ofFn_splitHalf_snd _
+    obtain ⟨o, T⟩ := s
+    cases o with
+    | some c =>
+      rw [stRec_eq, S.indImpl_challenge_repeat_onSpec, expect_pure]
+      simp only [expect_pure, ettStep_challenge_some, stRec_eq]
+      rw [expect_const]
+      congr 2
+      refine List.ofFn_injective ?_
+      rw [ofFn_cast (S.outLens_two n).symm _ _,
+        ofFn_padFin_of_length (by rw [List.length_ofFn, S.outLens_two])]
+    | none =>
+      rw [stRec_eq, S.indImpl_challenge_none_onSpec, expect_bind, ← expect_sample_equiv ν]
+      refine congrArg _ (funext fun re => ?_)
+      simp only [expect_pure, ettStep_challenge_none, stRec_eq]
+      have henc' : List.ofFn (S.encryptAt n key (if b then (FixedLengthScheme.splitHalf
+          (cast (S.indSpec_challengeDom n) mm)).2 else (FixedLengthScheme.splitHalf
+          (cast (S.indSpec_challengeDom n) mm)).1) re) =
+          encW f g (ν re) (AdaptiveCPA.msgOf n b (List.ofFn mm)) := by
+        rw [hsel, henc, ofFn_padFin_of_length hmsg]
+      congr 2
+      · refine List.ofFn_injective ?_
+        rw [ofFn_cast (S.outLens_two n).symm _ _, henc',
+          ofFn_padFin_of_length (by rw [hlenEnc _ hmsg, S.outLens_two])]
+      · congr 1
+        refine List.ofFn_injective ?_
+        rw [henc', ofFn_padFin_of_length (hlenEnc _ hmsg)]
+
+/-- **The CCA2 experiment is the experiment with a pad and a tag function** (step 1 of
+[PS10, Thm 170.4], transfer): for a scheme `S` whose encryption with the key generated from the
+coins `rg` is `encW (fk rg) (gk rg)` with nonces `ν re`, and whose decryption is `decL (fk rg)` on
+valid words for `gk rg` and `⊥` otherwise, with `(6n + 4)`-bit ciphertexts,
+`Pr[IND_b = 1] = 𝔼_{rg} 𝔼_r 𝔼[⟦A's output⟧₀ = 1 | simulate (ettImpl … (fk rg) (gk rg) false b) …]`.
+
+**Proof sketch.** `FixedLengthScheme.indGame_eq` and `accept_eq`; for each key and coins, the
+oracles of `IND_b` have the laws of `ettImpl` through the record (`expect_indImpl_ettImpl`,
+`expect_simulate_abs` with a constant counter); the game's codec is a bit codec
+(`FixedLengthScheme.indCodec_eq_bitCodec`) and its bit is the head of the output
+(`headD_ofFn_one`). -/
+theorem accept_indGame_eq (A : NUPPT) (Q : ℕ) (hct : S.ctLen.eval n = 6 * n + 4)
+    (fk : S.gen.Coins n → (Fin n → Bool) → (Fin n → Bool))
+    (gk : S.gen.Coins n → (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))
+    (ν : S.enc.Coins n ≃ (Fin n → Bool))
+    (henc : ∀ (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.enc.Coins n),
+      List.ofFn (S.encryptAt n (S.gen.runAt n [] rg) m re) =
+        encW (fk rg) (gk rg) (ν re) (List.ofFn m))
+    (hdec : ∀ (rg : S.gen.Coins n) (w : List Bool) (rd : S.dec.Coins n),
+      List.ofFn (FixedLengthScheme.decAnswer (decodeFin n
+          (S.dec.runAt n (pairEncode (S.gen.runAt n [] rg) w) rd))) =
+        if validW (gk rg) w = true then decL (fk rg) w else List.replicate (n + 1) false) :
+    accept (S.indGame .cca2 A Q b n) =
+      expect (sample (S.gen.Coins n)) fun rg => expect (sample (A.Coins n)) fun r =>
+        expect (simulate (ettImpl (S.inLens n) (S.outLens n) (S.ctLen.eval n) n (fk rg) (gk rg)
+            false b) (A.toComp (bitCodec (S.inLens n) (S.outLens n) 1) n Q r) (none, []))
+          (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
+  rw [accept_eq, FixedLengthScheme.indGame_eq, prob_bind]
+  refine congrArg _ (funext fun rg => ?_)
+  rw [prob_bind]
+  refine congrArg _ (funext fun r => ?_)
+  rw [prob_bind, FixedLengthScheme.indCodec_eq_bitCodec]
+  have h1 : (fun res : (Fin 1 → Bool) × Option (Fin (S.ctLen.eval n) → Bool) =>
+      ProbComp.prob (.pure (res.1 0)) (· = true)) =
+      fun res => if (List.ofFn res.1).headD false = true then (1 : ℝ) else 0 := by
+    funext res
+    rw [prob_pure, headD_ofFn_one]
+  rw [h1]
+  exact expect_simulate_abs _ _ stRec (fun _ => 0) (Q + 1)
+    (fun i x s _ G => expect_indImpl_ettImpl S b n _ (fk rg) (gk rg) hct ν (henc rg) (hdec rg)
+      i x s G)
+    (fun i x s _ => (OracleComp.allOutputs_true _).mono fun _ _ => Nat.zero_le _)
+    _ Q (A.toComp_costBoundedBy _ n Q r) (none, []) (by simp) _
+
+end Transfer
+
+end TCSlib.Cryptography.Composability.ETTGame

## ===== TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Tools
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Machines
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Games
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Handler
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Reduction
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Transfer
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Forgery
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Lazy
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.CPAHandler
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.CPAReduction
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Collision
import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A CCA2-secure private-key scheme

[PS10, Algorithm 169.3] and Theorem 170.4. For a PRF family `{f_k}`:
- `Gen′(1^n)` samples keys `k₁ ← U_n` and `k₂ ← U_{2n}`;
- `Enc′_{k₁,k₂}(m)` samples `r ← U_n`, sets `c₁ = m ⊕ f_{k₁}(r)`, and outputs
  `(r, c₁, f_{k₂}(r ‖ c₁))`;
- `Dec′_{k₁,k₂}(r, c₁, t)` outputs `⊥` unless `f_{k₂}(r ‖ c₁) = t`, and `c₁ ⊕ f_{k₁}(r)` otherwise.

It is the §3.9 scheme with its whole ciphertext `(r, c₁)` tagged under a second key: encrypt, then
authenticate. The tag defeats the mauling attack on the §3.9 scheme (Claim 169.a).

**Source notes: what the tag covers.**
- The algorithm box outputs `(r, c₁, f_{k₂}(c))`, with `c` undefined, while `Dec′` tests
  `f_{k₂}(c₁)`. The proof tags `c₁ ← Enc_{s₁}(m)`, which there names the whole §3.9 ciphertext.
  So the tag covers `(r, c₁)`.
- **Tagging `c₁` alone would not be CCA2-secure.** For positive `n`, choose challenge messages
  `0^n` and `1^n`, obtain `(r*, c₁*, t*)`, and obtain an encryption
  `(r₁, f_{k₁}(r₁), t₁)` of `0^n`. In this short-tag variant the query
  `(r*, f_{k₁}(r₁), t₁)` has a valid tag. If it equals the challenge, do not query it and count
  that branch as attack failure; otherwise its answer `f_{k₁}(r₁) ⊕ f_{k₁}(r*)` reveals the pad
  `f_{k₁}(r*)` and hence `m_b`. Equality can occur, in particular when `r₁ = r*` and `m_b = 0^n`.
  In the random-pad hybrid, nonce equality and accidental masked-message equality have total
  probability at most `2 / 2^n`; the real PRF setting adds a negligible reduction error.
  The attack is therefore overwhelmingly successful, rather than unconditionally query-distinct.
- The input `r ‖ c₁` has `2n` bits. The source's families are length-preserving on `|s|`-bit
  keys, so the tag key `k₂` has `2n` bits and the tag `2n` bits. One family `F` serves both keys,
  at parameters `n` and `2n` (the source names two families, `f` and `g`).
- `Dec′` is specified on well-formed triples. Here total pair projections and the two length
  guards enforce malformed rejection for generated keys when `n > 0`: both ciphertext pair layers
  must parse, and evaluator agreement then forces the valid tag to have `2n` bits. The evaluator
  `E` agrees with `F` only on `⟨s, x⟩` with `|s| = |x|`. At `n = 0`, failed projections can all be
  empty: the malformed four-bit word `0000`, for example, decrypts to the valid empty message.
  This finite-prefix behavior is retained; the malformed-rejection claim is only for positive
  parameters. There is only one plaintext at zero, so this does not change the security statement.

**The encoding.** The key is `⟨k₁, k₂⟩`; `Gen′` reads its `3n` coins as `k₁` (the first `n`)
followed by `k₂`. A ciphertext is `⟨r, ⟨c₁, t⟩⟩`, of `6n + 4` bits.

## Main definitions

* `Composability.ccaGenFun`, `ccaEncFun`, `ccaDecFun`: the three algorithms as string functions.
* `Composability.ccaScheme`: Algorithm 169.3 as a `FixedLengthScheme`, with correctness and the
  ciphertext length proved.

## Main results

* `Composability.ccaScheme_cca2`: Theorem 170.4, `π′` is CCA2-secure when `F` is a PRF.

## Contents

This file states the scheme and assembles the proof; the proof's games, handlers and reductions
are in the helper modules under `EncryptThenTag/` (namespace `Composability.ETTGame`):
- `Tools`: simulation through a state abstraction, coins in advance, functions overridden by a
  table;
- `Machines`: the budget cap and the parameter halving of machines;
- `Games`: the CCA2 experiment with a pad function `f` and a tag function `g` (`ettImpl`);
- `Handler`, `Reduction`: step 1, the tag-key PRF reduction at parameter `2n`
  (`exists_tagStep`);
- `Transfer`: the CCA2 experiment of `π′` as the experiment with `f_{k₁}` and `f_{k₂}`
  (`accept_indGame_eq`);
- `Forgery`: step 2, rejecting fresh decryption queries costs at most `q(n)/2^{2n}`
  (`abs_ettAcc_rej_sub_le`);
- `Lazy`, `CPAHandler`, `CPAReduction`: step 3, the rejecting experiment with lazily sampled tags
  is a CPA experiment of the §3.9 scheme (`expect_ettImpl_lazy`, `exists_cpaStep`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.3, Algorithm 169.3 and Theorem 170.4 (book pp. 169–171).
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! ### The algorithms as string functions -/

/-- `Gen′` on the layout `⟨⟨⟨1^n, y⟩, α⟩, ρ⟩` with `3n` coins `ρ`: the key `⟨k₁, k₂⟩`, where
`k₁` is the first `n` coins and `k₂` the rest. -/
def ccaGenFun (z : List Bool) : List Bool :=
  pairEncode ((NUPPT.inCoins z).take (NUPPT.inParam z).length)
    ((NUPPT.inCoins z).drop (NUPPT.inParam z).length)

/-- The raw generator pairs the input coins before and after the parameter length:
`⟨ρ.take n, ρ.drop n⟩`. -/
theorem ccaGenFun_eq (z : List Bool) :
    ccaGenFun z =
      pairEncode ((NUPPT.inCoins z).take (NUPPT.inParam z).length)
        ((NUPPT.inCoins z).drop (NUPPT.inParam z).length) := rfl

/-- The first ciphertext part `c₁ = m ⊕ E(⟨k₁, r⟩)` of `Enc′`, on the layout
`⟨⟨⟨1^n, ⟨⟨k₁, k₂⟩, m⟩⟩, α⟩, r⟩`. -/
def ccaMaskFun (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  List.zipWith xor (pairSndD (NUPPT.inArg z))
    (E (pairEncode (pairFstD (pairFstD (NUPPT.inArg z))) (NUPPT.inCoins z)))

/-- The raw ciphertext mask is the decoded message XOR the evaluator's output on the first
key and the input coins [PS10, Algorithm 169.3]. -/
theorem ccaMaskFun_eq (E : List Bool → List Bool) (z : List Bool) :
    ccaMaskFun E z =
      List.zipWith xor (pairSndD (NUPPT.inArg z))
        (E (pairEncode (pairFstD (pairFstD (NUPPT.inArg z))) (NUPPT.inCoins z))) := rfl

/-- `Enc′` on the layout `⟨⟨⟨1^n, ⟨⟨k₁, k₂⟩, m⟩⟩, α⟩, r⟩`: the ciphertext
`⟨r, ⟨c₁, E(⟨k₂, r ++ c₁⟩)⟩⟩` with `c₁ = m ⊕ E(⟨k₁, r⟩)`. -/
def ccaEncFun (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  pairEncode (NUPPT.inCoins z)
    (pairEncode (ccaMaskFun E z)
      (E (pairEncode (pairSndD (pairFstD (NUPPT.inArg z)))
        (NUPPT.inCoins z ++ ccaMaskFun E z))))

/-- Raw encryption returns the nonce, the masked message, and the tag of their concatenation
under the second key [PS10, Algorithm 169.3]. -/
theorem ccaEncFun_eq (E : List Bool → List Bool) (z : List Bool) :
    ccaEncFun E z =
      pairEncode (NUPPT.inCoins z)
        (pairEncode (ccaMaskFun E z)
          (E (pairEncode (pairSndD (pairFstD (NUPPT.inArg z)))
            (NUPPT.inCoins z ++ ccaMaskFun E z)))) := rfl

/-- The test of `Dec′` on the layout `⟨⟨⟨1^n, ⟨⟨k₁, k₂⟩, ⟨r, ⟨c₁, t⟩⟩⟩⟩, α⟩, r'⟩`: `r` and `c₁`
have `n` bits, and the tag is valid, `E(⟨k₂, r ++ c₁⟩) = t`. -/
def ccaDecOK (E : List Bool → List Bool) (z : List Bool) : Bool :=
  decide ((pairFstD (pairSndD (NUPPT.inArg z))).length = (NUPPT.inParam z).length) &&
    decide ((pairFstD (pairSndD (pairSndD (NUPPT.inArg z)))).length =
      (NUPPT.inParam z).length) &&
    decide (E (pairEncode (pairSndD (pairFstD (NUPPT.inArg z)))
        (pairFstD (pairSndD (NUPPT.inArg z)) ++ pairFstD (pairSndD (pairSndD (NUPPT.inArg z))))) =
      pairSndD (pairSndD (pairSndD (NUPPT.inArg z))))

/-- The raw decryption guard conjoins the two parameter-length checks with equality of the
computed and supplied tags [PS10, Algorithm 169.3]. -/
theorem ccaDecOK_eq (E : List Bool → List Bool) (z : List Bool) :
    ccaDecOK E z = (
      decide ((pairFstD (pairSndD (NUPPT.inArg z))).length = (NUPPT.inParam z).length) &&
        decide ((pairFstD (pairSndD (pairSndD (NUPPT.inArg z)))).length =
          (NUPPT.inParam z).length) &&
        decide (E (pairEncode (pairSndD (pairFstD (NUPPT.inArg z)))
            (pairFstD (pairSndD (NUPPT.inArg z)) ++
              pairFstD (pairSndD (pairSndD (NUPPT.inArg z))))) =
          pairSndD (pairSndD (pairSndD (NUPPT.inArg z))))) := rfl

/-- `Dec′` on the layout `⟨⟨⟨1^n, ⟨⟨k₁, k₂⟩, ⟨r, ⟨c₁, t⟩⟩⟩⟩, α⟩, r'⟩`: `c₁ ⊕ E(⟨k₁, r⟩)` when
the test passes, and otherwise `⊥`, here `1^{n+1}`, which decodes to no `n`-bit message. -/
def ccaDecFun (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  if ccaDecOK E z then
    List.zipWith xor (pairFstD (pairSndD (pairSndD (NUPPT.inArg z))))
      (E (pairEncode (pairFstD (pairFstD (NUPPT.inArg z))) (pairFstD (pairSndD (NUPPT.inArg z)))))
  else true :: NUPPT.inParam z

/-- Raw decryption XORs the first ciphertext component with the first-key pad when
`ccaDecOK` holds, and returns `true :: NUPPT.inParam z` otherwise [PS10, Algorithm 169.3]. -/
theorem ccaDecFun_eq (E : List Bool → List Bool) (z : List Bool) :
    ccaDecFun E z =
      if ccaDecOK E z then
        List.zipWith xor (pairFstD (pairSndD (pairSndD (NUPPT.inArg z))))
          (E (pairEncode (pairFstD (pairFstD (NUPPT.inArg z)))
            (pairFstD (pairSndD (NUPPT.inArg z)))))
      else true :: NUPPT.inParam z := rfl

/-! ### Efficiency -/

/-- `Gen′` is polynomial-time: a split of the coins at `n` (`polyTimeComputable_pairTakePoly`). -/
theorem polyTimeComputable_ccaGenFun : PolyTimeComputable ccaGenFun := by
  have hp := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins
  convert ((polyTimeComputable_pairTakePoly .var).comp hp).pairEncode
    ((polyTimeComputable_pairDropPoly .var).comp hp) using 1
  funext z
  simp [ccaGenFun, Function.comp_apply]

/-- The mask `c₁` is polynomial-time when `E` is. -/
theorem polyTimeComputable_ccaMaskFun {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (ccaMaskFun E) := by
  have h := polyTimeComputable_pairXor.comp
    ((polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg).pairEncode
      (hE.comp (((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).comp
        NUPPT.polyTimeComputable_inArg).pairEncode NUPPT.polyTimeComputable_inCoins)))
  convert h using 1
  funext z
  simp [ccaMaskFun, Function.comp_apply]

/-- `Enc′` is polynomial-time when `E` is. -/
theorem polyTimeComputable_ccaEncFun {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (ccaEncFun E) := by
  have hm := polyTimeComputable_ccaMaskFun hE
  have h := NUPPT.polyTimeComputable_inCoins.pairEncode (hm.pairEncode
    (hE.comp (((polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD).comp
      NUPPT.polyTimeComputable_inArg).pairEncode (NUPPT.polyTimeComputable_inCoins.append hm))))
  convert h using 1

/-- The test of `Dec′` is polynomial-time when `E` is: two length comparisons and one equality
(`polyTimeComputable_lenEq`, `polyTimeComputable_pairEq`).

**Proof sketch.** Project the nonce, encrypted message, tag and second key from the layout.
Two polynomial-time length comparisons check that the nonce and encrypted message each have
`n` bits. Append these two words and evaluate the tag under the second key, using composition
with the polynomial-time evaluator. A word-equality test compares this result with the supplied
tag; Boolean conjunction combines that test with the two length checks. -/
theorem polyTimeComputable_ccaDecOK {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (fun z => [ccaDecOK E z]) := by
  have hl : ∀ g : List Bool → List Bool, PolyTimeComputable g →
      PolyTimeComputable (fun z => [decide ((g z).length = (NUPPT.inParam z).length)]) := by
    intro g hg
    convert polyTimeComputable_lenEq.comp (hg.pairEncode NUPPT.polyTimeComputable_inParam)
      using 1
    funext z
    simp [Function.comp_apply]
  have hArg := NUPPT.polyTimeComputable_inArg
  have hc₁ : PolyTimeComputable fun z => pairFstD (pairSndD (pairSndD (NUPPT.inArg z))) :=
    ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp
      polyTimeComputable_pairSndD).comp hArg
  have hc₂ : PolyTimeComputable fun z => pairSndD (pairSndD (pairSndD (NUPPT.inArg z))) :=
    ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).comp
      polyTimeComputable_pairSndD).comp hArg
  have hr : PolyTimeComputable fun z => pairFstD (pairSndD (NUPPT.inArg z)) :=
    (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp hArg
  have htag : PolyTimeComputable fun z =>
      [decide (E (pairEncode (pairSndD (pairFstD (NUPPT.inArg z)))
          (pairFstD (pairSndD (NUPPT.inArg z)) ++
            pairFstD (pairSndD (pairSndD (NUPPT.inArg z))))) =
        pairSndD (pairSndD (pairSndD (NUPPT.inArg z))))] := by
    convert polyTimeComputable_pairEq.comp ((hE.comp
      (((polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD).comp hArg).pairEncode
        (hr.append hc₁))).pairEncode hc₂) using 1
    funext z
    simp [Function.comp_apply]
  exact polyTimeComputable_and (polyTimeComputable_and (hl _ hr) (hl _ hc₁)) htag

/-- `Dec′` is polynomial-time when `E` is. -/
theorem polyTimeComputable_ccaDecFun {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (ccaDecFun E) := by
  refine polyTimeComputable_ite (polyTimeComputable_ccaDecOK hE) ?_
    ((polyTimeComputable_const [true]).append NUPPT.polyTimeComputable_inParam)
  have hArg := NUPPT.polyTimeComputable_inArg
  have h := polyTimeComputable_pairXor.comp
    ((((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp
      polyTimeComputable_pairSndD).comp hArg).pairEncode
      (hE.comp (((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).comp
        hArg).pairEncode ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp
          hArg))))
  convert h using 1
  funext z
  simp [Function.comp_apply]

/-! ### The machines -/

section Machines

variable {E : List Bool → List Bool} (hE : PolyTimeComputable E)

/-- The machine `Gen′`, with `3n` coins. -/
noncomputable abbrev ccaGen : NUPPT :=
  NUPPT.ofPolyTimeUniform polyTimeComputable_ccaGenFun (.mul (.const 3) .var)

/-- The machine `Enc′`, with `n` coins. -/
noncomputable abbrev ccaEnc : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_ccaEncFun hE) .var

/-- The machine `Dec′`, deterministic. -/
noncomputable abbrev ccaDec : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_ccaDecFun hE) (.const 0)

/-- `Gen′` splits its `3n` coins at `n`. -/
theorem runAt_ccaGen (n : ℕ) (ρ : ccaGen.Coins n) :
    ccaGen.runAt n [] ρ = pairEncode ((List.ofFn ρ).take n) ((List.ofFn ρ).drop n) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [ccaGenFun, NUPPT.inCoins_eq, NUPPT.inParam_eq, NUPPT.advInput_eq]

/-- `Enc′` on `⟨⟨k₁, k₂⟩, m⟩` with coins `r` is `⟨r, ⟨c₁, E(⟨k₂, r ++ c₁⟩)⟩⟩`,
`c₁ = m ⊕ E(⟨k₁, r⟩)`. -/
theorem runAt_ccaEnc (n : ℕ) (k₁ k₂ m : List Bool) (r : (ccaEnc hE).Coins n) :
    (ccaEnc hE).runAt n (pairEncode (pairEncode k₁ k₂) m) r =
      pairEncode (List.ofFn r)
        (pairEncode (List.zipWith xor m (E (pairEncode k₁ (List.ofFn r))))
          (E (pairEncode k₂
            (List.ofFn r ++ List.zipWith xor m (E (pairEncode k₁ (List.ofFn r))))))) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [ccaEncFun, ccaMaskFun, NUPPT.inArg_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq]

/-- `Dec′` on `⟨⟨k₁, k₂⟩, ⟨r, ⟨c₁, t⟩⟩⟩` with `n`-bit `r` and `c₁` and a valid tag is
`c₁ ⊕ E(⟨k₁, r⟩)`. -/
theorem runAt_ccaDec (n : ℕ) (k₁ k₂ r c₁ t : List Bool) (hr : r.length = n)
    (hc₁ : c₁.length = n) (htag : E (pairEncode k₂ (r ++ c₁)) = t) (r' : (ccaDec hE).Coins n) :
    (ccaDec hE).runAt n (pairEncode (pairEncode k₁ k₂) (pairEncode r (pairEncode c₁ t))) r' =
      List.zipWith xor c₁ (E (pairEncode k₁ r)) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [ccaDecFun, ccaDecOK, NUPPT.inArg_eq, NUPPT.inParam_eq, NUPPT.advInput_eq,
    hr, hc₁, htag]

end Machines

/-! ### The scheme -/

variable (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
  (E : List Bool → List Bool) (hE : PolyTimeComputable E)
  (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (F n s x))

include hFE in
/-- On two `n`-bit strings, `E` returns `n` bits (it agrees with `F`). -/
theorem length_eval_of_length {n : ℕ} {a b : List Bool} (ha : a.length = n)
    (hb : b.length = n) : (E (pairEncode a b)).length = n := by
  have hA : List.ofFn (padFin n a) = a := by
    simpa only [ha, Nat.sub_self, List.replicate_zero, List.append_nil] using
      (Collection.ofFn_padFin_of_le (ℓ := n) ha.le)
  have hB : List.ofFn (padFin n b) = b := by
    simpa only [hb, Nat.sub_self, List.replicate_zero, List.append_nil] using
      (Collection.ofFn_padFin_of_le (ℓ := n) hb.le)
  rw [← hA, ← hB, hFE, List.length_ofFn]

/-- XOR-ing twice with the same pad, at least as long as the message, is the identity. -/
private theorem zipWith_xor_xor_self' : ∀ (m p : List Bool), m.length ≤ p.length →
    List.zipWith xor (List.zipWith xor m p) p = m
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | a :: m, b :: p, h => by
    simp only [List.zipWith_cons_cons, List.cons.injEq]
    exact ⟨by cases a <;> cases b <;> rfl, zipWith_xor_xor_self' m p (by simpa using h)⟩

/-- **`π′`** [PS10, Algorithm 169.3], for a family `F` with evaluator `E`: the §3.9 scheme under
the `n`-bit key `k₁`, its ciphertext `(r, c₁)` tagged with `f_{k₂}(r ‖ c₁)` under the `2n`-bit key
`k₂`. Ciphertexts have `6n + 4` bits. -/
noncomputable def ccaScheme : FixedLengthScheme where
  gen := ccaGen
  enc := ccaEnc hE
  dec := ccaDec hE
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  enc_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  dec_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  correct := by
    intro n m rg re rd
    have hρ : (List.ofFn rg).length = 3 * n := by
      rw [List.length_ofFn, NUPPT.coinLen_eq, NUPPT.coins_ofPolyTimeUniform,
        PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    have hk₁ : ((List.ofFn rg).take n).length = n := by simp [hρ]; omega
    have hr : (List.ofFn re).length = n := by
      rw [List.length_ofFn, NUPPT.coinLen_eq, NUPPT.coins_ofPolyTimeUniform,
        PolyExpr.eval_var]
    have hp := length_eval_of_length F E hFE hk₁ hr
    have hc₁ : (List.zipWith xor (List.ofFn m) (E (pairEncode ((List.ofFn rg).take n)
        (List.ofFn re)))).length = n := by simp [hp]
    rw [runAt_ccaGen, runAt_ccaEnc, runAt_ccaDec hE n _ _ _ _ _ hr hc₁ rfl,
      zipWith_xor_xor_self' _ _ (by simp [hp]), decodeFin_ofFn]
  ctLen := .add (.mul (.const 6) .var) (.const 4)
  enc_length := by
    intro n rg m r
    show ((ccaEnc hE).runAt n (pairEncode (ccaGen.runAt n [] rg) (List.ofFn m)) r).length = _
    have hρ : (List.ofFn rg).length = 3 * n := by
      rw [List.length_ofFn, NUPPT.coinLen_eq, NUPPT.coins_ofPolyTimeUniform,
        PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    have hk₁ : ((List.ofFn rg).take n).length = n := by simp [hρ]; omega
    have hk₂ : ((List.ofFn rg).drop n).length = 2 * n := by simp [hρ]; omega
    have hr : (List.ofFn r).length = n := by
      rw [List.length_ofFn, NUPPT.coinLen_eq, NUPPT.coins_ofPolyTimeUniform,
        PolyExpr.eval_var]
    have hp := length_eval_of_length F E hFE hk₁ hr
    have hc₁ : (List.zipWith xor (List.ofFn m) (E (pairEncode ((List.ofFn rg).take n)
        (List.ofFn r)))).length = n := by simp [hp]
    have hrc : (List.ofFn r ++ List.zipWith xor (List.ofFn m) (E (pairEncode
        ((List.ofFn rg).take n) (List.ofFn r)))).length = 2 * n := by
      rw [List.length_append, hr, hc₁]; ring
    have ht := length_eval_of_length F E hFE hk₂ hrc
    rw [runAt_ccaGen, runAt_ccaEnc]
    simp only [length_pairEncode, hr, hc₁, ht, PolyExpr.eval_add, PolyExpr.eval_mul,
      PolyExpr.eval_const, PolyExpr.eval_var]
    omega

attribute [simps (config := { isSimp := false }) gen enc dec ctLen] ccaScheme

/-! ### The proof of Theorem 170.4 -/

section Proof

open ETTGame ProbComp

/-- The ciphertext length is `6n + 4` (`ccaScheme_ctLen`). -/
private theorem cca_ctLen_eval (n : ℕ) : (ccaScheme F E hE hFE).ctLen.eval n = 6 * n + 4 := by
  rw [ccaScheme_ctLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
    PolyExpr.eval_const, PolyExpr.eval_var]

/-- The scheme's query lengths are the reduction's: `inLens n = fun i => (ettDin i).eval n`. -/
private theorem cca_inLens (n : ℕ) :
    (ccaScheme F E hE hFE).inLens n = fun i => (ettDin i).eval n := by
  funext i
  match i with
  | 0 => rw [FixedLengthScheme.inLens_zero, ettDin_zero, PolyExpr.eval_var]
  | 1 => rw [FixedLengthScheme.inLens_one, ettDin_one, cca_ctLen_eval, ettCt_eval]
  | 2 => rw [FixedLengthScheme.inLens_two, ettDin_two, PolyExpr.eval_add, PolyExpr.eval_var]

/-- The scheme's answer lengths are the reduction's: `outLens n = fun i => (ettDout i).eval n`. -/
private theorem cca_outLens (n : ℕ) :
    (ccaScheme F E hE hFE).outLens n = fun i => (ettDout i).eval n := by
  funext i
  match i with
  | 0 => rw [FixedLengthScheme.outLens_zero, ettDout_zero, cca_ctLen_eval, ettCt_eval]
  | 1 =>
    rw [FixedLengthScheme.outLens_one, ettDout_one, PolyExpr.eval_add, PolyExpr.eval_var,
      PolyExpr.eval_const]
  | 2 => rw [FixedLengthScheme.outLens_two, ettDout_two, cca_ctLen_eval, ettCt_eval]

/-- `Gen′` has `3n` coins. -/
private theorem cca_gen_coins : (ccaScheme F E hE hFE).gen.coins = .mul (.const 3) .var := by
  rw [ccaScheme_gen, NUPPT.coins_ofPolyTimeUniform]

/-- `Enc′` has `n` coins. -/
private theorem cca_enc_coins : (ccaScheme F E hE hFE).enc.coins = .var := by
  rw [ccaScheme_enc, NUPPT.coins_ofPolyTimeUniform]

/-- `3n = n + 2n`, for the key coins. -/
private theorem cca_gen_len (n : ℕ) : (PolyExpr.mul (.const 3) .var).eval n = n + 2 * n := by
  rw [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  ring

/-- The `3n` key coins as the keys `k₁` (`n` bits) and `k₂` (`2n` bits). -/
private noncomputable def ccaKeyEq (n : ℕ) :
    (ccaScheme F E hE hFE).gen.Coins n ≃ (Fin n → Bool) × (Fin (2 * n) → Bool) :=
  (NUPPT.coinsEquivPoly (cca_gen_coins F E hE hFE) n).trans
    (EnsembleLemmas.coinsEquiv (cca_gen_len n)).symm

/-- `⟦rg⟧ = ⟦k₁⟧ ++ ⟦k₂⟧` for `(k₁, k₂) = ccaKeyEq rg`. -/
private theorem ofFn_ccaKeyEq (n : ℕ) (rg : (ccaScheme F E hE hFE).gen.Coins n) :
    List.ofFn rg = List.ofFn (ccaKeyEq F E hE hFE n rg).1 ++
      List.ofFn (ccaKeyEq F E hE hFE n rg).2 := by
  rw [← EnsembleLemmas.ofFn_coinsEquiv (cca_gen_len n), ccaKeyEq, Equiv.trans_apply,
    Equiv.apply_symm_apply, NUPPT.coinsEquivPoly_ofFn]

/-- **`Gen′` outputs the pair of the two keys:** `Gen′(1^n; rg) = ⟨⟦k₁⟧, ⟦k₂⟧⟩` for
`(k₁, k₂) = ccaKeyEq rg` (`runAt_ccaGen`). -/
private theorem cca_gen_runAt (n : ℕ) (rg : (ccaScheme F E hE hFE).gen.Coins n) :
    (ccaScheme F E hE hFE).gen.runAt n [] rg =
      pairEncode (List.ofFn (ccaKeyEq F E hE hFE n rg).1)
        (List.ofFn (ccaKeyEq F E hE hFE n rg).2) := by
  have h := ofFn_ccaKeyEq F E hE hFE n rg
  generalize ccaKeyEq F E hE hFE n rg = kk at h
  revert rg
  rw [ccaScheme_gen]
  intro rg h
  rw [runAt_ccaGen, h, List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn]

/-- The encryption coins as an `n`-bit nonce, keeping the string. -/
private noncomputable def ccaNonceEq (n : ℕ) :
    (ccaScheme F E hE hFE).enc.Coins n ≃ (Fin n → Bool) :=
  (NUPPT.coinsEquivPoly (cca_enc_coins F E hE hFE) n).trans
    (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool))

/-- `⟦ccaNonceEq n re⟧ = ⟦re⟧`. -/
private theorem ofFn_ccaNonceEq (n : ℕ) (re : (ccaScheme F E hE hFE).enc.Coins n) :
    List.ofFn (ccaNonceEq F E hE hFE n re) = List.ofFn re := by
  rw [ccaNonceEq, Equiv.trans_apply, ofFn_arrowCongr_finCongr, NUPPT.coinsEquivPoly_ofFn]

/-- **`Enc′` with the keys `k₁`, `k₂` and the coins `re`** is `encW (F n k₁) (F (2n) k₂)` with the
nonce `ccaNonceEq re` (`runAt_ccaEnc`, `hFE` at `n` and at `2n`). -/
private theorem ofFn_cca_encryptAt (n : ℕ) (k₁ : Fin n → Bool) (k₂ : Fin (2 * n) → Bool)
    (m : Fin n → Bool) (re : (ccaScheme F E hE hFE).enc.Coins n) :
    List.ofFn ((ccaScheme F E hE hFE).encryptAt n (pairEncode (List.ofFn k₁) (List.ofFn k₂)) m re) =
      encW (F n k₁) (F (2 * n) k₂) (ccaNonceEq F E hE hFE n re) (List.ofFn m) := by
  have hx : List.ofFn re = List.ofFn (ccaNonceEq F E hE hFE n re) :=
    (ofFn_ccaNonceEq F E hE hFE n re).symm
  generalize ccaNonceEq F E hE hFE n re = r at hx
  revert re
  simp only [FixedLengthScheme.encryptAt_eq]
  rw [ccaScheme_enc]
  intro re hx
  have hm : (List.ofFn m).length = n := List.length_ofFn
  have hc := length_maskL (F n k₁) r hm
  have hp : List.ofFn r ++ maskL (F n k₁) r (List.ofFn m) =
      List.ofFn (pairV n (List.ofFn r) (maskL (F n k₁) r (List.ofFn m))) := by
    rw [pairV_eq, ofFn_padFin_of_length (by rw [List.length_append, List.length_ofFn, hc]; omega)]
  rw [runAt_ccaEnc, hx, hFE, ← maskL_eq, hp, hFE, ← tagL_eq, ← ctW_eq, ← encW_eq,
    ofFn_padFin_of_length (by rw [length_encW _ _ _ hm, cca_ctLen_eval])]

/-- **`Dec′` with the keys `k₁`, `k₂`** on a word `w`: `⟨1, wC w ⊕ ⟦F n k₁ (wR w)⟧⟩` if `w` is valid
for the tag function `F (2n) k₂`, and `⊥` otherwise (`ccaDecFun_eq`, `ccaDecOK_eq`, `hFE`). The
zero-parameter malformed words are read alike: their total projections are empty.

**Proof sketch.** Unfold the decryption machine (`ccaScheme_dec`, `runAtL_ofPolyTimeUniform`,
`ccaDecFun_eq`, `ccaDecOK_eq`). Its test is `|wR w| = n`, `|wC w| = n` and
`E⟨⟦k₂⟧, wR w ++ wC w⟩ = wT w`; on `n`-bit fields `E⟨⟦k₂⟧, wR w ++ wC w⟩` is
`tagL (F (2n) k₂) (wR w) (wC w)` (`hFE`, `pairV_eq`), so the test is `validW`. On a valid word
the output `wC w ⊕ E⟨⟦k₁⟧, wR w⟩` has `n` bits and decodes, giving `decL (F n k₁) w` (`hFE`,
`decodeFin_ofFn`, `decAnswer_some`); otherwise the output `true :: 1^n` has `n + 1` bits, decodes
to nothing and is read as `0^{n+1}` (`decodeFin_eq`, `decAnswer_none`, `ofFn_zeroBits`). -/
private theorem ofFn_cca_decAnswer (n : ℕ) (k₁ : Fin n → Bool) (k₂ : Fin (2 * n) → Bool)
    (w : List Bool) (rd : (ccaScheme F E hE hFE).dec.Coins n) :
    List.ofFn (FixedLengthScheme.decAnswer (decodeFin n ((ccaScheme F E hE hFE).dec.runAt n
        (pairEncode (pairEncode (List.ofFn k₁) (List.ofFn k₂)) w) rd))) =
      if validW (F (2 * n) k₂) w = true then decL (F n k₁) w
      else List.replicate (n + 1) false := by
  revert rd
  rw [ccaScheme_dec]
  intro rd
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform, ccaDecFun_eq, ccaDecOK_eq]
  simp only [NUPPT.inArg_eq, NUPPT.inParam_eq, NUPPT.advInput_eq, pairFstD_pairEncode,
    pairSndD_pairEncode, List.length_replicate]
  have htag : ∀ (hr : (pairFstD w).length = n) (hc : (pairFstD (pairSndD w)).length = n),
      E (pairEncode (List.ofFn k₂) (pairFstD w ++ pairFstD (pairSndD w))) =
        tagL (F (2 * n) k₂) (wR w) (wC w) := by
    intro hr hc
    have he : pairFstD w ++ pairFstD (pairSndD w) =
        List.ofFn (pairV n (pairFstD w) (pairFstD (pairSndD w))) := by
      rw [pairV_eq, ofFn_padFin_of_length (by rw [List.length_append, hr, hc]; omega)]
    rw [he, hFE, tagL_eq, wR_eq, wC_eq]
  by_cases hv : validW (F (2 * n) k₂) w = true
  · rw [if_pos hv]
    have hv' := hv
    rw [validW_eq, Bool.and_eq_true, wfW_eq, Bool.and_eq_true, decide_eq_true_eq,
      decide_eq_true_eq, decide_eq_true_eq] at hv'
    obtain ⟨⟨hr, hc⟩, ht⟩ := hv'
    rw [wR_eq] at hr
    rw [wC_eq] at hc
    have hok : (decide ((pairFstD w).length = n) && decide ((pairFstD (pairSndD w)).length = n) &&
        decide (E (pairEncode (List.ofFn k₂) (pairFstD w ++ pairFstD (pairSndD w))) =
          pairSndD (pairSndD w))) = true := by
      rw [htag hr hc, ← wT_eq, ← ht]
      simp [hr, hc]
    rw [if_pos hok]
    have hk : pairFstD w = List.ofFn (padFin n (pairFstD w)) := (ofFn_padFin_of_length hr).symm
    have hlen : (List.zipWith xor (pairFstD (pairSndD w))
        (List.ofFn (F n k₁ (padFin n (pairFstD w))))).length = n := by
      rw [List.length_zipWith, List.length_ofFn, hc, Nat.min_self]
    have hdec : List.zipWith xor (pairFstD (pairSndD w))
        (List.ofFn (F n k₁ (padFin n (pairFstD w)))) =
        List.ofFn (padFin n (List.zipWith xor (pairFstD (pairSndD w))
          (List.ofFn (F n k₁ (padFin n (pairFstD w)))))) := (ofFn_padFin_of_length hlen).symm
    conv_lhs => rw [hk, hFE, hdec, decodeFin_ofFn, FixedLengthScheme.decAnswer_some]
    rw [List.ofFn_succ, Fin.cons_zero]
    simp only [Fin.cons_succ]
    rw [← hdec, decL_eq, wC_eq, wR_eq]
  · rw [if_neg hv]
    have hnok : (decide ((pairFstD w).length = n) && decide ((pairFstD (pairSndD w)).length = n) &&
        decide (E (pairEncode (List.ofFn k₂) (pairFstD w ++ pairFstD (pairSndD w))) =
          pairSndD (pairSndD w))) = false := by
      by_contra hc'
      rw [Bool.not_eq_false, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        decide_eq_true_eq, decide_eq_true_eq] at hc'
      obtain ⟨⟨hr, hc⟩, ht⟩ := hc'
      apply hv
      rw [validW_eq, wfW_eq, wR_eq, wC_eq, hr, hc, wT_eq, ← ht, htag hr hc, wR_eq, wC_eq]
      simp
    rw [if_neg (by rw [hnok]; exact Bool.false_ne_true), decodeFin_eq,
      dif_neg (by rw [List.length_cons, List.length_replicate]; omega),
      FixedLengthScheme.decAnswer_none, ofFn_zeroBits]

/-- **The CCA2 experiment of `π′` is the experiment with `f_{k₁}` and `f_{k₂}`:**
`Pr[IND_b = 1] = 𝔼_{k₁} 𝔼_{k₂} ettAcc (F n k₁) (F (2n) k₂) false b A Q`, on the reduction's lengths.

**Proof sketch.** `ETTGame.accept_indGame_eq` with the key split (`ccaKeyEq`, `cca_gen_runAt`), the
nonce (`ccaNonceEq`) and the readers `ofFn_cca_encryptAt`, `ofFn_cca_decAnswer`; the key coins are
uniform pairs (`expect_sample_equiv`, `expect_sample_prod`), and the lengths are the reduction's
(`cca_inLens`, `cca_outLens`, `cca_ctLen_eval`, `expect_ettImpl_transport`). -/
private theorem accept_cca_indGame (A : NUPPT) (Q : ℕ) (b : Bool) (n : ℕ) :
    accept ((ccaScheme F E hE hFE).indGame .cca2 A Q b n) =
      expect (sample (Fin n → Bool)) fun k₁ => expect (sample (Fin (2 * n) → Bool)) fun k₂ =>
        ettAcc (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
          (F n k₁) (F (2 * n) k₂) false b A Q := by
  rw [accept_indGame_eq (ccaScheme F E hE hFE) b n A Q (cca_ctLen_eval F E hE hFE n)
      (fun rg => F n (ccaKeyEq F E hE hFE n rg).1)
      (fun rg => F (2 * n) (ccaKeyEq F E hE hFE n rg).2) (ccaNonceEq F E hE hFE n)
      (fun rg m re => by rw [cca_gen_runAt]; exact ofFn_cca_encryptAt F E hE hFE n _ _ m re)
      (fun rg w rd => by rw [cca_gen_runAt]; exact ofFn_cca_decAnswer F E hE hFE n _ _ w rd),
    ← expect_sample_equiv (ccaKeyEq F E hE hFE n).symm, ChallengeSim.expect_sample_prod]
  refine congrArg _ (funext fun k₁ => congrArg _ (funext fun k₂ => ?_))
  simp only [Equiv.apply_symm_apply]
  rw [ettAcc_eq]
  refine congrArg _ (funext fun r => ?_)
  exact expect_ettImpl_transport n _ _ false b (cca_inLens F E hE hFE n)
    (cca_outLens F E hE hFE n) (by rw [cca_ctLen_eval, ettCt_eval]) A Q r

/-- **Step 1: the tag key becomes a random function** [PS10, Thm 170.4, proof]. For a machine
adversary `A` with budget `q` and a bit `b`, there is a PRF distinguisher `D` such that at every
`n`, `|Pr[IND_b = 1] − 𝔼_{k₁} 𝔼_R ettAcc (F n k₁) R false b A (q n)|` is the PRF advantage of `D`
at parameter `2n` with budget `q(2n)`.

**Proof sketch.** `accept_cca_indGame` and `ETTGame.exists_tagStep`. -/
private theorem cca_tag_step (A : NUPPT) (q : PolyExpr) (b : Bool) :
    ∃ D : NUPPT, ∀ n : ℕ,
      |accept ((ccaScheme F E hE hFE).indGame .cca2 A (q.eval n) b n) -
          expect (sample (Fin n → Bool)) (fun k₁ =>
            expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))) fun R =>
              ettAcc (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
                (F n k₁) R false b A (q.eval n))| =
        prfAdv (F (2 * n)) (D.toOracleAdversary (2 * n) (2 * n) (2 * n) (q.eval (2 * n))) := by
  obtain ⟨D, hD⟩ := exists_tagStep F E hE hFE A q b
  exact ⟨D, fun n => by rw [accept_cca_indGame, hD n]⟩

/-- **Step 2: fresh decryption queries are rejected** [PS10, Thm 170.4, proof]. For `n > 0`, the
experiments with a random tag function without and with the rejection of fresh pairs, averaged
over the key `k₁`, differ by at most `q(n) / 2^{2n}`.

**Proof sketch.** `ETTGame.abs_ettAcc_rej_sub_le` for each `k₁` (the ciphertexts have
`6n + 4 = ettCt(n)` bits and the challenge queries `2n`), averaged over `k₁`
(`abs_expect_sub_le`). -/
private theorem cca_rej_step (A : NUPPT) (Q : ℕ) (b : Bool) (n : ℕ) (hn : 0 < n) :
    |expect (sample (Fin n → Bool)) (fun k₁ =>
          expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))) fun R =>
            ettAcc (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
              (F n k₁) R false b A Q) -
        expect (sample (Fin n → Bool)) (fun k₁ =>
          expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))) fun R =>
            ettAcc (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
              (F n k₁) R true b A Q)| ≤ Q * ((2 : ℝ) ^ (2 * n))⁻¹ :=
  abs_expect_sub_le _ fun k₁ => abs_ettAcc_rej_sub_le _ _ _ n (F n k₁) b hn (ettCt_eval n)
    (by show (ettDin 2).eval n = n + n; rw [ettDin_two, PolyExpr.eval_add, PolyExpr.eval_var])
    A Q

end Proof

/-- **Theorem 170.4: `π′` is CCA2-secure** [PS10, Theorem 170.4] when `F` is a pseudorandom
function family.

**Proof sketch** (the source's, made explicit). Fix a machine adversary `A` with budget `q` and a
bit `b`; write `P_b` for `Pr[IND_b = 1]`.
1. **The tag key becomes a random function** (`cca_tag_step`, from `ETTGame.exists_tagStep`):
   replacing `f_{k₂}` by a uniform random function `R` on `2n` bits moves `P_b` by the PRF
   advantage, at parameter `2n`, of a next-query machine `D_b`: T2
   (`Games.exists_interactiveHandlerMachine`) with `k₁` and the nonces in its seed, T4
   (`Games.exists_toOracleAdversary_of_bitCodec`) at length `2n`, and the parameter halving.
2. **Fresh decryption queries are rejected** (`cca_rej_step`, from
   `ETTGame.abs_ettAcc_rej_sub_le`): for `n > 0`, the experiment that rejects every `Dec′` query
   whose pair `(r, c₁)` is not that of an earlier `Enc′` answer differs by at most
   `q(n)/2^{2n}`: the two agree until the first fresh pair with a valid tag, and each such guess
   hits the unrevealed value of `R` with probability at most `2^{-2n}`.
3. **The rejecting experiment is a CPA experiment of the §3.9 scheme** (`ETTGame.exists_cpaStep`):
   averaged over `R` it is the experiment with lazily sampled tags (`ETTGame.expect_ettImpl_lazy`),
   which a CPA adversary `B` against the §3.9 scheme with pad `f_{k₁}` simulates: `Enc′` and the
   challenge come from the CPA oracles and are tagged from the table of earlier answers, the
   challenge record, or a fresh tape; `Dec′` is answered from the table (`ETTGame.bHandler`, T2).
4. **The CPA experiment hides the bit** (as in [PS10, Theorem 168.2]): replacing `f_{k₁}` by a
   random function costs the PRF advantages of `PRFGame.exists_prfReduction`'s machines `C_b`
   (`ETTGame.prfAdv_eq_expect`), and with a random function the two bits are `Q²/2^n` apart,
   `Q = qRed q` (`PRFGame.abs_expect_fImpl_sub_le`).
So for `n > 0`, `|P₀ − P₁| ≤ adv(D₀) + adv(D₁) + 2q(n)/2^{2n} + adv(C₀) + adv(C₁) + Q(n)²/2^n`,
every term negligible (`PRF.negligible_prfAdv`, `Negligible.comp_of_le` at `2n`,
`EnsembleLemmas.negligible_polyExpr_mul`, `negligible_two_pow_neg`); at `n = 0` the advantage is
at most `1` (`advantage_le_one`), an eventually-zero correction.

Step 4 re-derives the CPA bound for the §3.9 scheme from `PRFGame`'s public reduction and
collision bound rather than citing `prfFixedScheme_cpa`, since the simulator's CPA adversary runs
against the oracles `PRFGame.fImpl` directly. The simulator samples tags lazily, so two answers that
share `(r, c₁)` share their tag, as with `RF`; the source's fresh uniform tags would differ from
`RF` only on such a collision. -/
theorem ccaScheme_cca2 (hF : PRF F) : (ccaScheme F E hE hFE).INDSecure .cca2 := by
  refine (FixedLengthScheme.INDSecure_iff _ _).2 fun A q => ?_
  obtain ⟨D₀, hD₀⟩ := cca_tag_step F E hE hFE A q false
  obtain ⟨D₁, hD₁⟩ := cca_tag_step F E hE hFE A q true
  obtain ⟨B, hB⟩ := ETTGame.exists_cpaStep A q
  obtain ⟨C₀, hC₀⟩ := PRFGame.exists_prfReduction B (PRFGame.qRed q) false false
  obtain ⟨C₁, hC₁⟩ := PRFGame.exists_prfReduction B (PRFGame.qRed q) false true
  refine ⟨fun n =>
      prfAdv (F (2 * n)) (D₀.toOracleAdversary (2 * n) (2 * n) (2 * n) (q.eval (2 * n))) +
      prfAdv (F (2 * n)) (D₁.toOracleAdversary (2 * n) (2 * n) (2 * n) (q.eval (2 * n))) +
      2 * ((q.eval n : ℝ) * ((2 : ℝ) ^ (2 * n))⁻¹) +
      prfAdv (F n) (C₀.toOracleAdversary n n n ((PRFGame.qRed (PRFGame.qRed q)).eval n)) +
      prfAdv (F n) (C₁.toOracleAdversary n n n ((PRFGame.qRed (PRFGame.qRed q)).eval n)) +
      ((PRFGame.qRed q).eval n : ℝ) ^ 2 / 2 ^ n + (if n = 0 then 1 else 0), ?_, fun n => ?_⟩
  · -- Each term is negligible.
    have hT₀ := (hF.negligible_prfAdv D₀ q).comp_of_le (fun n => 2 * n)
      fun N => by show N ≤ 2 * N; omega
    have hT₁ := (hF.negligible_prfAdv D₁ q).comp_of_le (fun n => 2 * n)
      fun N => by show N ≤ 2 * N; omega
    have hR : Negligible fun n => 2 * ((q.eval n : ℝ) * ((2 : ℝ) ^ (2 * n))⁻¹) := by
      refine ((EnsembleLemmas.negligible_polyExpr_mul q negligible_two_pow_neg).const_mul 2).mono
        ⟨0, fun n _ => ?_⟩
      have h₁ : ((2 : ℝ) ^ (2 * n))⁻¹ ≤ (2 : ℝ)⁻¹ ^ n := by
        rw [inv_pow]
        exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
      have h₂ : (0 : ℝ) ≤ q.eval n := Nat.cast_nonneg _
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      gcongr
    have hP₀ := hF.negligible_prfAdv C₀ (PRFGame.qRed (PRFGame.qRed q))
    have hP₁ := hF.negligible_prfAdv C₁ (PRFGame.qRed (PRFGame.qRed q))
    have hS : Negligible fun n => ((PRFGame.qRed q).eval n : ℝ) ^ 2 / 2 ^ n := by
      refine (EnsembleLemmas.negligible_polyExpr_mul (.mul (PRFGame.qRed q) (PRFGame.qRed q))
        negligible_two_pow_neg).mono ⟨0, fun n _ => le_of_eq ?_⟩
      rw [PolyExpr.eval_mul, Nat.cast_mul, inv_pow, ← div_eq_mul_inv, sq]
    have hZ : Negligible fun n : ℕ => if n = 0 then (1 : ℝ) else 0 :=
      negligible_zero.mono ⟨1, fun n hn => by rw [if_neg (by omega)]⟩
    exact (((((hT₀.add hT₁).add hR).add hP₀).add hP₁).add hS).add hZ
  · have n₀ := prfAdv_nonneg (F (2 * n))
      (D₀.toOracleAdversary (2 * n) (2 * n) (2 * n) (q.eval (2 * n)))
    have n₁ := prfAdv_nonneg (F (2 * n))
      (D₁.toOracleAdversary (2 * n) (2 * n) (2 * n) (q.eval (2 * n)))
    have m₀ := prfAdv_nonneg (F n)
      (C₀.toOracleAdversary n n n ((PRFGame.qRed (PRFGame.qRed q)).eval n))
    have m₁ := prfAdv_nonneg (F n)
      (C₁.toOracleAdversary n n n ((PRFGame.qRed (PRFGame.qRed q)).eval n))
    have hc : (0 : ℝ) ≤ 2 * ((q.eval n : ℝ) * ((2 : ℝ) ^ (2 * n))⁻¹) := by positivity
    have hs : (0 : ℝ) ≤ ((PRFGame.qRed q).eval n : ℝ) ^ 2 / 2 ^ n := by positivity
    beta_reduce
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- At `n = 0` the advantage is at most `1`.
      have h1 := advantage_le_one ((ccaScheme F E hE hFE).indGame .cca2 A (q.eval 0) false 0)
        ((ccaScheme F E hE hFE).indGame .cca2 A (q.eval 0) true 0)
      rw [if_pos rfl]
      linarith
    · rw [if_neg (by omega : n ≠ 0), add_zero, advantage_eq]
      -- Steps 1 and 2 for both bits.
      have t₀ := hD₀ n
      have t₁ := hD₁ n
      have r₀ := cca_rej_step F A (q.eval n) false n hn
      have r₁ := cca_rej_step F A (q.eval n) true n hn
      -- Step 3: the rejecting experiments are CPA experiments of the §3.9 scheme.
      simp only [hB false n, hB true n] at r₀ r₁
      have p₀ := ETTGame.prfAdv_eq_expect (F n)
        (C₀.toOracleAdversary n n n ((PRFGame.qRed (PRFGame.qRed q)).eval n))
      have p₁ := ETTGame.prfAdv_eq_expect (F n)
        (C₁.toOracleAdversary n n n ((PRFGame.qRed (PRFGame.qRed q)).eval n))
      simp only [hC₀ n, hC₁ n] at p₀ p₁
      have hcpa := PRFGame.abs_expect_fImpl_sub_le (fun i => (PRFGame.pkDin i).eval n)
        (fun i => (PRFGame.pkDout i).eval n) (PRFGame.ctP.eval n) n (PRFGame.atkOf false)
        (by rw [PRFGame.decOpen_atkOf]; rfl) (PRFGame.ctP_eval n)
        (by show (PRFGame.pkDin 2).eval n = n + n
            rw [PRFGame.pkDin_two, PolyExpr.eval_add, PolyExpr.eval_var])
        (fun r : B.Coins n => B.toComp (bitCodec (fun i => (PRFGame.pkDin i).eval n)
          (fun i => (PRFGame.pkDout i).eval n) 1) n ((PRFGame.qRed q).eval n) r)
        (fun a => (List.ofFn a).headD false = true) ((PRFGame.qRed q).eval n)
        (fun r => NUPPT.toComp_costBoundedBy _ _ _ _ _)
      obtain ⟨a₀, b₀⟩ := abs_le.1 t₀.le
      obtain ⟨a₁, b₁⟩ := abs_le.1 t₁.le
      obtain ⟨c₀, d₀⟩ := abs_le.1 r₀
      obtain ⟨c₁, d₁⟩ := abs_le.1 r₁
      obtain ⟨e₀, f₀⟩ := abs_le.1 p₀.ge
      obtain ⟨e₁, f₁⟩ := abs_le.1 p₁.ge
      obtain ⟨g, h⟩ := abs_le.1 hcpa
      refine abs_le.2 ⟨by linarith, by linarith⟩

end TCSlib.Cryptography.Composability

## ===== TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/CPAHandler.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Handler
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Lazy
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Handler

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The handler of the CPA reduction

Step 3 of [PS10, Theorem 170.4]: the experiment that rejects fresh decryption queries is
simulated by a CPA adversary against the §3.9 scheme. This file builds that adversary's handler
(`bHandler`): a `Games.InteractiveHandler` from the CCA2 oracles of the encrypt-then-tag scheme
(lengths `ettDin`, `ettDout`) to the CPA oracles of the §3.9 scheme (lengths `PRFGame.pkDin`,
`PRFGame.pkDout`).

The handler's seed is `q(n)` tag tapes of `2n` bits; its state is the table of its `Enc′` answers
(`GGMRed.tblEnc` of the entries `(r ‖ c₁, t ‖ m)`, newest first), the query count and the
challenge record (`bState`).
- `Enc′` on `m`: ask the CPA encryption oracle, read its answer `⟨r, c₁⟩`, take the tag of
  `r ‖ c₁` from the table, else from the record, else from the query's tape, answer
  `⟨r, ⟨c₁, t⟩⟩` and add the entry.
- `Dec′` on `w`: refuse the record; if `w` is well formed and the table holds its pair with its tag,
  answer `⟨1, m⟩` with the table's message, else `⊥` (`lazyDec`). No outer query.
- `Challenge`: the first time, ask the CPA challenge oracle on `⟨m₀, m₁⟩`, tag its answer as `Enc′`
  does (without an entry) and record it; later repeat the record.
Words read from the outer answer are padded to their lengths (`EnsembleLemmas.padL`), so every
call is well formed for every outer answer. Lookups use GGM's table lookup (`GGMRed.lookup`,
`GGMRed.lookup_tblOf`).

## Main definitions

* `ETTGame.encE`, `tblW`, `bStLen`, `bSeedLen`, `bState`, `bSeed`, `bTapeOf`.
* `ETTGame.bHandler q hq b`: the handler.

## Main results

* `ETTGame.lookup_tblW`: the lookup on the table word is `lookL`.
* `ETTGame.bHandler_impl_enc`, `_impl_dec`, `_impl_challenge_some`, `_impl_challenge_none`: its
  answers on encoded states.
* `ETTGame.bHandler_finish`, `bHandler_init_hstate`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 170.4 (book pp. 170–171).
-/

namespace TCSlib.Cryptography.Composability.ETTGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Games.InteractiveHandler (rU rW rS rI rX rL rAns)
open TCSlib.Cryptography.Composability.PRFGame (pkDin pkDout ctP)

/-! ### The table word -/

section Table

variable {n : ℕ}

/-- The string entry of a lazy-table entry `(p, t, m)`: `encE (p, t, m) = (⟦p⟧, ⟦t⟧ ++ m)`. -/
def encE (e : LEntry n) : List Bool × List Bool := (List.ofFn e.1, List.ofFn e.2.1 ++ e.2.2)

/-- `encE e = (⟦e.1⟧, ⟦e.2.1⟧ ++ e.2.2)`. -/
theorem encE_eq (e : LEntry n) : encE e = (List.ofFn e.1, List.ofFn e.2.1 ++ e.2.2) := rfl

/-- **The table word** of a lazy table: the nested pairs of its string entries (`GGMRed.tblEnc`),
`tblW L = GGMRed.tblEnc (L.map encE)`. -/
def tblW (L : List (LEntry n)) : List Bool := GGMRed.tblEnc (L.map encE)

/-- `tblW L = GGMRed.tblEnc (L.map encE)`. -/
theorem tblW_eq (L : List (LEntry n)) : tblW L = GGMRed.tblEnc (L.map encE) := rfl

/-- The table word of the empty table is empty: `tblW [] = []`. -/
theorem tblW_nil : tblW ([] : List (LEntry n)) = [] := by
  rw [tblW_eq, List.map_nil, GGMRed.tblEnc_nil]

/-- A new entry is the first pair of the table word:
`tblW (e :: L) = ⟨⟨⟦p⟧, ⟦t⟧ ++ m⟩, tblW L⟩`. -/
theorem tblW_cons (e : LEntry n) (L : List (LEntry n)) :
    tblW (e :: L) =
      pairEncode (pairEncode (List.ofFn e.1) (List.ofFn e.2.1 ++ e.2.2)) (tblW L) := by
  rw [tblW_eq, tblW_eq, List.map_cons, GGMRed.tblEnc_cons, encE_eq]

/-- With `n`-bit messages, each entry adds `14n + 6` bits:
`|tblW L| = |L| · (14n + 6)`. -/
theorem length_tblW (L : List (LEntry n)) (hL : ∀ e ∈ L, e.2.2.length = n) :
    (tblW L).length = L.length * (14 * n + 6) := by
  induction L with
  | nil => rw [tblW_nil, List.length_nil, List.length_nil, Nat.zero_mul]
  | cons e L ih =>
    rw [tblW_cons, length_pairEncode, length_pairEncode, List.length_append, List.length_ofFn,
      List.length_ofFn, hL e (List.mem_cons_self ..),
      ih fun e' he' => hL e' (List.mem_cons_of_mem _ he'), List.length_cons]
    ring

/-- The table of string entries is `GGMRed.tblOf` of the pairs, with the entries' values. -/
private theorem map_encE_eq_tblOf (L : List (LEntry n)) :
    L.map encE = GGMRed.tblOf (fun k => (encE (L.getD k default)).2) (keysL L) 0 := by
  refine List.ext_getElem (by rw [List.length_map, GGMRed.length_tblOf, keysL_eq, List.length_map])
    fun k h₁ h₂ => ?_
  have hk : k < L.length := by rwa [List.length_map] at h₁
  refine Prod.ext ?_ ?_
  · rw [GGMRed.tblOf_getElem_fst, List.getElem_map, encE_eq]
    simp only [keysL_eq, List.getElem_map]
  · rw [GGMRed.tblOf_getElem_snd, List.getElem_map, Nat.zero_add, List.getD_eq_getElem _ _ hk]

/-- **The lookup on the table word is `lookL`:**
`lookup ⟨⟦p⟧, tblW L⟩ = ⟨[], ⟦t⟧ ++ m⟩` for the newest entry `(p, t, m)` at `p`, and `[]` if there
is none (`GGMRed.lookup_tblOf`). -/
theorem lookup_tblW (L : List (LEntry n)) (p : Fin (2 * n) → Bool) :
    GGMRed.lookup (pairEncode (List.ofFn p) (tblW L)) =
      match lookL L p with
      | some e => pairEncode [] (List.ofFn e.2.1 ++ e.2.2)
      | none => [] := by
  rw [tblW_eq, map_encE_eq_tblOf, GGMRed.lookup_tblOf, lookL_eq]
  by_cases hp : p ∈ keysL L
  · rw [if_pos hp, if_pos hp, encE_eq]
  · rw [if_neg hp, if_neg hp]

end Table

/-! ### Lengths, state and seed -/

variable (q : PolyExpr)

/-- The state length `2q(14n + 6) + 2q + 6n + 9`:
`(bStLen q).eval n = 2 q(n) (14n + 6) + 2 q(n) + (6n + 9)`. -/
def bStLen : PolyExpr :=
  .add
    (.add (.mul (.const 2) (.mul q (.add (.mul (.const 14) .var) (.const 6)))) (.mul (.const 2) q))
    (.add (.mul (.const 6) .var) (.const 9))

/-- `(bStLen q).eval n = 2 q(n) (14n + 6) + 2 q(n) + 6n + 9`. -/
theorem bStLen_eval (n : ℕ) :
    (bStLen q).eval n = 2 * (q.eval n * (14 * n + 6)) + 2 * q.eval n + (6 * n + 9) := by
  simp only [bStLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]

/-- The seed length `q(n) · 2n`: one tag tape per query, `bSeedLen q = q · tagLen`, so
`(bSeedLen q).eval n = q(n) · 2n`. -/
def bSeedLen : PolyExpr := .mul q tagLen

/-- `(bSeedLen q).eval n = q(n) · 2n`. -/
theorem bSeedLen_eval (n : ℕ) : (bSeedLen q).eval n = q.eval n * (2 * n) := by
  rw [bSeedLen, PolyExpr.eval_mul, tagLen_eval]

/-- **The encoded state** with the table `L`, the query count `j` and the record `o`:
`⟨tblW L, ⟨1^j, recBits o⟩⟩`, padded with `false` to the state length,
`bState q n j L o = padFin _ ⟨tblW L, ⟨1^j, recBits n o⟩⟩`. -/
def bState (n j : ℕ) (L : List (LEntry n)) (o : Option (Fin (ettCt.eval n) → Bool)) :
    Fin ((bStLen q).eval n) → Bool :=
  padFin _ (pairEncode (tblW L) (pairEncode (List.replicate j true) (recBits n o)))

/-- `bState q n j L o = padFin _ ⟨tblW L, ⟨1^j, recBits n o⟩⟩`. -/
theorem bState_eq (n j : ℕ) (L : List (LEntry n)) (o : Option (Fin (ettCt.eval n) → Bool)) :
    bState q n j L o =
      padFin _ (pairEncode (tblW L) (pairEncode (List.replicate j true) (recBits n o))) :=
  rfl

/-- **The seed** from the tape word: `⟦bSeed q n W⟧ = ⟦W⟧`. -/
def bSeed (n : ℕ) : (Fin (q.eval n * (2 * n)) → Bool) ≃ (Fin ((bSeedLen q).eval n) → Bool) :=
  Equiv.arrowCongr (finCongr (bSeedLen_eval q n).symm) (Equiv.refl Bool)

/-- `bSeed q n = arrowCongr (finCongr _) (refl Bool)`. -/
theorem bSeed_eq (n : ℕ) :
    bSeed q n = Equiv.arrowCongr (finCongr (bSeedLen_eval q n).symm) (Equiv.refl Bool) := rfl

/-- `⟦bSeed q n W⟧ = ⟦W⟧`. -/
theorem ofFn_bSeed (n : ℕ) (W : Fin (q.eval n * (2 * n)) → Bool) :
    List.ofFn (bSeed q n W) = List.ofFn W := by
  rw [bSeed, ofFn_arrowCongr_finCongr]

/-- The tag tape `j` of the tape word: block `j` of `W`,
`bTapeOf q n W j hj = blocks (q n) (2n) W ⟨j, hj⟩`. -/
def bTapeOf (n : ℕ) (W : Fin (q.eval n * (2 * n)) → Bool) (j : ℕ) (hj : j < q.eval n) :
    Fin (2 * n) → Bool :=
  EnsembleLemmas.blocks (q.eval n) (2 * n) W ⟨j, hj⟩

/-- `bTapeOf q n W j hj = blocks (q n) (2n) W ⟨j, hj⟩`. -/
theorem bTapeOf_eq (n : ℕ) (W : Fin (q.eval n * (2 * n)) → Bool) (j : ℕ) (hj : j < q.eval n) :
    bTapeOf q n W j hj = EnsembleLemmas.blocks (q.eval n) (2 * n) W ⟨j, hj⟩ := rfl

/-- The fields of an encoded state that fits: the table word, the count `1^j`, the flag and the
record.

**Proof sketch.** The encoded triple fits in the state length: `|tblW L| = |L| · (14n + 6)` with
`|L| ≤ q(n)` (`length_tblW`) and `j ≤ q(n)` (`bStLen_eval`). So the padding only appends `false`s
to the innermost component (`ofFn_padFin_of_le`, `pairEncode_append_right` twice), and the
projections read `tblW L`, `1^j` and `recBits n o` followed by `false`s, whose head is the flag and
whose next `ct(n)` bits are the record (by cases on `o`). -/
private theorem fields_bState (n j : ℕ) (L : List (LEntry n))
    (o : Option (Fin (ettCt.eval n) → Bool))
    (hj : j ≤ q.eval n) (hL : L.length ≤ q.eval n) (hm : ∀ e ∈ L, e.2.2.length = n) :
    pairFstD (List.ofFn (bState q n j L o)) = tblW L ∧
      pairFstD (pairSndD (List.ofFn (bState q n j L o))) = List.replicate j true ∧
      (pairSndD (pairSndD (List.ofFn (bState q n j L o)))).headD false = o.isSome ∧
      ((pairSndD (pairSndD (List.ofFn (bState q n j L o)))).drop 1).take (ettCt.eval n) =
        (recBits n o).drop 1 := by
  have hlen : (pairEncode (tblW L) (pairEncode (List.replicate j true) (recBits n o))).length ≤
      (bStLen q).eval n := by
    rw [length_pairEncode, length_pairEncode, List.length_replicate, length_recBits,
      length_tblW L hm, bStLen_eval, ettCt_eval]
    have : L.length * (14 * n + 6) ≤ q.eval n * (14 * n + 6) := Nat.mul_le_mul_right _ hL
    omega
  rw [bState_eq, Collection.ofFn_padFin_of_le hlen, ← GGMRed.pairEncode_append_right,
    pairFstD_pairEncode, pairSndD_pairEncode, ← GGMRed.pairEncode_append_right,
    pairFstD_pairEncode, pairSndD_pairEncode]
  refine ⟨rfl, rfl, ?_, ?_⟩
  · cases o with
    | none => rw [recBits_none, List.cons_append, List.headD_cons, Option.isSome_none]
    | some c => rw [recBits_some, List.cons_append, List.headD_cons, Option.isSome_some]
  · cases o with
    | none =>
      rw [recBits_none, List.cons_append, List.drop_succ_cons, List.drop_zero, List.drop_succ_cons,
        List.drop_zero, List.take_left' List.length_replicate]
    | some c =>
      rw [recBits_some, List.cons_append, List.drop_succ_cons, List.drop_zero, List.drop_succ_cons,
        List.drop_zero, List.take_left' List.length_ofFn]

/-! ### The round function -/

/-- The table word of the state. -/
private def bTbl (w : List Bool) : List Bool := pairFstD (rS w)
/-- The query count of the state. -/
private def bJ (w : List Bool) : List Bool := pairFstD (pairSndD (rS w))
/-- The challenge flag of the state. -/
private def bFlag (w : List Bool) : Bool := (pairSndD (pairSndD (rS w))).headD false
/-- The recorded challenge of the state. -/
private def bRec (w : List Bool) : List Bool :=
  ((pairSndD (pairSndD (rS w))).drop 1).take (ettCt.eval (rU w).length)
/-- A word read at `2n` bits. -/
private def bPad2 (w v : List Bool) : List Bool := EnsembleLemmas.padL (tagLen.eval (rU w).length) v
/-- The tape of the query count. -/
private def bTape (w : List Bool) : List Bool :=
  ((rW w).drop ((bJ w).length * tagLen.eval (rU w).length)).take (tagLen.eval (rU w).length)
/-- The pair `r ‖ c₁` of the outer answer `⟨r, c₁⟩`, at `2n` bits. -/
private def bKey (w : List Bool) : List Bool := bPad2 w (pairFstD (rAns w) ++ pairSndD (rAns w))
/-- The table lookup at a pair. -/
private def bLook (w key : List Bool) : List Bool := GGMRed.lookup (pairEncode key (bTbl w))
/-- The pair of the record, at `2n` bits. -/
private def bChalKey (w : List Bool) : List Bool :=
  bPad2 w (pairFstD (bRec w) ++ pairFstD (pairSndD (bRec w)))
/-- The tag of the record, at `2n` bits. -/
private def bChalTag (w : List Bool) : List Bool := bPad2 w (pairSndD (pairSndD (bRec w)))
/-- The tag of the outer answer's pair: the table's, else the record's, else the tape. -/
private def bTag (w : List Bool) : List Bool :=
  if decide (bLook w (bKey w) = []) then
    (if bFlag w && decide (bChalKey w = bKey w) then bChalTag w else bTape w)
  else (pairSndD (bLook w (bKey w))).take (tagLen.eval (rU w).length)
/-- The ciphertext `⟨r, ⟨c₁, t⟩⟩` of the outer answer and its tag, at `6n + 4` bits. -/
private def bCt (w : List Bool) : List Bool :=
  EnsembleLemmas.padL (ettCt.eval (rU w).length)
    (pairEncode (pairFstD (rAns w)) (pairEncode (pairSndD (rAns w)) (bTag w)))
/-- The new state: the table word `tbl`, count `j + 1`, record `t`. -/
private def bNew (w tbl t : List Bool) : List Bool :=
  EnsembleLemmas.padL ((bStLen q).eval (rU w).length) (pairEncode tbl (pairEncode (true :: bJ w) t))
/-- The pair of the decryption query, at `2n` bits. -/
private def bDKey (w : List Bool) : List Bool :=
  bPad2 w (pairFstD (rX w) ++ pairFstD (pairSndD (rX w)))
/-- Whether the decryption query is well formed. -/
private def bWF (w : List Bool) : Bool :=
  decide ((pairFstD (rX w)).length = (rU w).length) &&
    decide ((pairFstD (pairSndD (rX w))).length = (rU w).length)
/-- Whether the decryption query is the recorded challenge. -/
private def bRef (w : List Bool) : Bool := bFlag w && decide (rX w = bRec w)
/-- The lazy decryption answer (`lazyDec`) of the query, from the table. -/
private def bDecL (w : List Bool) : List Bool :=
  if (!bRef w && bWF w) = true then
    if decide (bLook w (bDKey w) = []) then []
    else if decide ((pairSndD (bLook w (bDKey w))).take (tagLen.eval (rU w).length) =
        pairSndD (pairSndD (rX w))) then
      true :: (pairSndD (bLook w (bDKey w))).drop (tagLen.eval (rU w).length)
    else []
  else []
/-- The decryption answer at `n + 1` bits. -/
private def bDecAns (w : List Bool) : List Bool :=
  EnsembleLemmas.padL ((PolyExpr.add .var (.const 1)).eval (rU w).length) (bDecL w)

/-- **One round of the handler** (see the module docstring). A first round of `Enc′` or of a first
challenge asks the CPA oracle; the second round, with the answer in the log, returns the answer and
the new state. Decryption and a repeated challenge answer at once. -/
private def bRun (w : List Bool) : List Bool :=
  if (rI w).headD false then
    if ((rI w).drop 1).headD false then
      if bFlag w then
        pairEncode [true] (EnsembleLemmas.padL (ettCt.eval (rU w).length) (bRec w) ++
          bNew q w (bTbl w) (true :: bRec w))
      else if decide (rL w = []) then pairEncode [false] (pairEncode [true, true] (rX w))
      else pairEncode [true] (bCt w ++ bNew q w (bTbl w) (true :: bCt w))
    else pairEncode [true] (bDecAns w ++ bNew q w (bTbl w) (bFlag w :: bRec w))
  else
    if decide (rL w = []) then pairEncode [false] (pairEncode [] (rX w))
    else pairEncode [true] (bCt w ++
      bNew q w (pairEncode (pairEncode (bKey w) (bTag w ++ rX w)) (bTbl w)) (bFlag w :: bRec w))

/-- The round function is polynomial-time: `PolyTimeComputable (bRun q)`.

**Proof sketch.** Every reader of `bRun` is assembled from the generic input readers (`rU`, `rW`,
`rS`, `rI`, `rX`, `rL`, `rAns`) and pair projections: the record by `pairTakePoly`; the tape by
`unaryMulPair`, `dropPrefixByLength` and `pairTakePoly`; the table lookup by `GGMRed.lookup_poly`;
padding by `EnsembleLemmas.polyTimeComputable_padL`; word tests by `pairEq`, `isNil` and
`lenEq_poly`. The branches for the three oracles are combined with `polyTimeComputable_ite`. -/
private theorem polyTimeComputable_bRun : PolyTimeComputable (bRun q) := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hU : PolyTimeComputable rU := InteractiveHandler.polyTimeComputable_rU
  have hW : PolyTimeComputable rW := InteractiveHandler.polyTimeComputable_rW
  have hS : PolyTimeComputable rS := InteractiveHandler.polyTimeComputable_rS
  have hI : PolyTimeComputable rI := InteractiveHandler.polyTimeComputable_rI
  have hX : PolyTimeComputable rX := InteractiveHandler.polyTimeComputable_rX
  have hL : PolyTimeComputable rL := InteractiveHandler.polyTimeComputable_rL
  have hY : PolyTimeComputable rAns := InteractiveHandler.polyTimeComputable_rAns
  have hTbl : PolyTimeComputable bTbl := hF.comp hS
  have hJ : PolyTimeComputable bJ := (hF.comp hD).comp hS
  have hT : PolyTimeComputable fun w => pairSndD (pairSndD (rS w)) := (hD.comp hD).comp hS
  have hFlag : PolyTimeComputable fun w => [bFlag w] := polyTimeComputable_headD.comp hT
  have hRec : PolyTimeComputable bRec :=
    ((polyTimeComputable_pairTakePoly ettCt).comp
      (hU.pairEncode (polyTimeComputable_tail.comp hT))).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]; rfl
  have hPad2 : ∀ {v : List Bool → List Bool}, PolyTimeComputable v →
      PolyTimeComputable fun w => bPad2 w (v w) := fun hv =>
    EnsembleLemmas.polyTimeComputable_padL tagLen hU hv
  have hOff : PolyTimeComputable fun w =>
      List.replicate ((bJ w).length * tagLen.eval (rU w).length) true :=
    (OneWay.polyTimeComputable_unaryMulPair.comp (hJ.pairEncode
      ((polyTimeComputable_unaryPoly tagLen).comp hU))).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
          List.length_replicate]
  have hDrop : PolyTimeComputable fun w =>
      (rW w).drop ((bJ w).length * tagLen.eval (rU w).length) :=
    (polyTimeComputable_dropPrefixByLength.comp (hOff.pairEncode hW)).congr fun w => by
      simp only [Function.comp_apply, PrefixByLength.drop_def, pairFstD_pairEncode,
        pairSndD_pairEncode, List.length_replicate]
  have hTape : PolyTimeComputable bTape :=
    ((polyTimeComputable_pairTakePoly tagLen).comp (hU.pairEncode hDrop)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]; rfl
  have hKey : PolyTimeComputable bKey := hPad2 ((hF.comp hY).append (hD.comp hY))
  have hLook : ∀ {k : List Bool → List Bool}, PolyTimeComputable k →
      PolyTimeComputable fun w => bLook w (k w) := fun hk =>
    GGMRed.lookup_poly.comp (hk.pairEncode hTbl)
  have hEq : ∀ {u v : List Bool → List Bool}, PolyTimeComputable u → PolyTimeComputable v →
      PolyTimeComputable fun w => [decide (u w = v w)] := fun hu hv =>
    (polyTimeComputable_pairEq.comp (hu.pairEncode hv)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hNil : ∀ {u : List Bool → List Bool}, PolyTimeComputable u →
      PolyTimeComputable fun w => [decide (u w = [])] := fun hu => polyTimeComputable_isNil.comp hu
  have hTake2 : ∀ {u : List Bool → List Bool}, PolyTimeComputable u →
      PolyTimeComputable fun w => (u w).take (tagLen.eval (rU w).length) := fun hu =>
    ((polyTimeComputable_pairTakePoly tagLen).comp (hU.pairEncode hu)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hDrop2 : ∀ {u : List Bool → List Bool}, PolyTimeComputable u →
      PolyTimeComputable fun w => (u w).drop (tagLen.eval (rU w).length) := fun hu =>
    ((polyTimeComputable_pairDropPoly tagLen).comp (hU.pairEncode hu)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hChalKey : PolyTimeComputable bChalKey :=
    hPad2 ((hF.comp hRec).append ((hF.comp hD).comp hRec))
  have hChalTag : PolyTimeComputable bChalTag := hPad2 ((hD.comp hD).comp hRec)
  have hTag : PolyTimeComputable bTag :=
    polyTimeComputable_ite (hNil (hLook hKey))
      (polyTimeComputable_ite (polyTimeComputable_and hFlag (hEq hChalKey hKey)) hChalTag hTape)
      (hTake2 (hD.comp (hLook hKey)))
  have hCt : PolyTimeComputable bCt :=
    EnsembleLemmas.polyTimeComputable_padL ettCt hU
      ((hF.comp hY).pairEncode ((hD.comp hY).pairEncode hTag))
  have hNew : ∀ {tb t : List Bool → List Bool}, PolyTimeComputable tb → PolyTimeComputable t →
      PolyTimeComputable fun w => bNew q w (tb w) (t w) := fun htb ht =>
    EnsembleLemmas.polyTimeComputable_padL (bStLen q) hU
      (htb.pairEncode (((polyTimeComputable_const [true]).append hJ).pairEncode ht))
  have hDKey : PolyTimeComputable bDKey := hPad2 ((hF.comp hX).append ((hF.comp hD).comp hX))
  have hWF : PolyTimeComputable fun w => [bWF w] :=
    polyTimeComputable_and (EffFill.lenEq_poly (hF.comp hX) hU)
      (EffFill.lenEq_poly ((hF.comp hD).comp hX) hU)
  have hRef : PolyTimeComputable fun w => [bRef w] := polyTimeComputable_and hFlag (hEq hX hRec)
  have hDecL : PolyTimeComputable bDecL :=
    polyTimeComputable_ite (polyTimeComputable_and (polyTimeComputable_not hRef) hWF)
      (polyTimeComputable_ite (hNil (hLook hDKey)) (polyTimeComputable_const [])
        (polyTimeComputable_ite (hEq (hTake2 (hD.comp (hLook hDKey))) ((hD.comp hD).comp hX))
          ((polyTimeComputable_const [true]).append (hDrop2 (hD.comp (hLook hDKey))))
          (polyTimeComputable_const [])))
      (polyTimeComputable_const [])
  have hDecAns : PolyTimeComputable bDecAns :=
    EnsembleLemmas.polyTimeComputable_padL (.add .var (.const 1)) hU hDecL
  have hRet : ∀ {f : List Bool → List Bool}, PolyTimeComputable f →
      PolyTimeComputable fun w => pairEncode [true] (f w) := fun hf =>
    (polyTimeComputable_const [true]).pairEncode hf
  have hKeep : PolyTimeComputable fun w => bFlag w :: bRec w :=
    (hFlag.append hRec).congr fun _ => rfl
  have cNil : PolyTimeComputable fun w => [decide (rL w = [])] := polyTimeComputable_isNil.comp hL
  have hChal := polyTimeComputable_ite hFlag
    (hRet ((EnsembleLemmas.polyTimeComputable_padL ettCt hU hRec).append
      (hNew hTbl ((polyTimeComputable_const [true]).append hRec))))
    (polyTimeComputable_ite cNil
      ((polyTimeComputable_const [false]).pairEncode
        ((polyTimeComputable_const [true, true]).pairEncode hX))
      (hRet (hCt.append (hNew hTbl ((polyTimeComputable_const [true]).append hCt)))))
  have hDec := hRet (hDecAns.append (hNew hTbl hKeep))
  have hEnc := polyTimeComputable_ite cNil
    ((polyTimeComputable_const [false]).pairEncode ((polyTimeComputable_const []).pairEncode hX))
    (hRet (hCt.append (hNew ((hKey.pairEncode (hTag.append hX)).pairEncode hTbl) hKeep)))
  exact polyTimeComputable_ite (polyTimeComputable_headD.comp hI)
    (polyTimeComputable_ite (polyTimeComputable_headD.comp (polyTimeComputable_tail.comp hI))
      hChal hDec) hEnc

/-- The finalization's round: output `A`'s bit. -/
private def bFin (w : List Bool) : List Bool := pairEncode [true] (pairFstD (pairSndD (pairSndD w)))

/-- The finalization's round is polynomial-time. -/
private theorem polyTimeComputable_bFin : PolyTimeComputable bFin :=
  (polyTimeComputable_const [true]).pairEncode
    (polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))

/-! ### The handler -/

/-- **The handler of the CPA reduction** for the budget `q`: state `bState` (initially the empty
table, count `0`, no record), seed `q(n)` tag tapes, one outer call per inner query, the adversary
run on the empty input, and the finalization outputting the adversary's bit:
`stateLen = bStLen q`, `seedLen = bSeedLen q`, `init n = bState q n 0 [] none`, `run = bRun q`,
`perCall = 1`, `advIn _ = []`, `outLen = 1`, `finCall = 0` and `finRun = bFin`. -/
noncomputable def bHandler : InteractiveHandler 3 ettDin ettDout 3 pkDin pkDout where
  stateLen := bStLen q
  seedLen := bSeedLen q
  perCall := .const 1
  init n := bState q n 0 [] none
  run := bRun q
  poly := polyTimeComputable_bRun q
  advIn _ := []
  advIn_poly := polyTimeComputable_const []
  outLen := .const 1
  finCall := .const 0
  finRun := bFin
  finRun_poly := polyTimeComputable_bFin

attribute [simps (config := { isSimp := false }) stateLen seedLen perCall outLen finCall] bHandler

/-- The encoded state at the handler's state type: `bHState q n j L o = bState q n j L o`. -/
def bHState (n j : ℕ) (L : List (LEntry n)) (o : Option (Fin (ettCt.eval n) → Bool)) :
    Fin ((bHandler q).stateLen.eval n) → Bool :=
  bState q n j L o

/-- `bHState q n j L o = bState q n j L o`. -/
theorem bHState_eq (n j : ℕ) (L : List (LEntry n)) (o : Option (Fin (ettCt.eval n) → Bool)) :
    bHState q n j L o = bState q n j L o := rfl

/-- `⟦bHState q n j L o⟧ = ⟦bState q n j L o⟧`. -/
theorem ofFn_bHState (n j : ℕ) (L : List (LEntry n)) (o : Option (Fin (ettCt.eval n) → Bool)) :
    List.ofFn (bHState q n j L o) = List.ofFn (bState q n j L o) := rfl

/-- The seed at the handler's seed type: `bHSeed q n = bSeed q n`. -/
def bHSeed (n : ℕ) :
    (Fin (q.eval n * (2 * n)) → Bool) ≃ (Fin ((bHandler q).seedLen.eval n) → Bool) :=
  bSeed q n

/-- `bHSeed q n = bSeed q n`. -/
theorem bHSeed_eq (n : ℕ) : bHSeed q n = bSeed q n := rfl

/-- `⟦bHSeed q n W⟧ = ⟦W⟧`. -/
theorem ofFn_bHSeed (n : ℕ) (W : Fin (q.eval n * (2 * n)) → Bool) :
    List.ofFn (bHSeed q n W) = List.ofFn W :=
  ofFn_bSeed q n W

/-- The initial state is the empty table, count `0` and no record:
`(bHandler q).init n = bHState q n 0 [] none`. -/
theorem bHandler_init_hstate (n : ℕ) : (bHandler q).init n = bHState q n 0 [] none := rfl

/-- The adversary's input is empty: `(bHandler q).advInput n z ω = []`. -/
theorem bHandler_advInput (n : ℕ) (z : List Bool)
    (ω : Fin ((bHandler q).seedLen.eval n) → Bool) : (bHandler q).advInput n z ω = [] := by
  rw [InteractiveHandler.advInput_eq]
  rfl

/-- The finalization outputs the adversary's bit and asks nothing:
`(bHandler q).finish n z ω s a = pure (padFin _ ⟦a⟧)`. -/
theorem bHandler_finish (n : ℕ) (z : List Bool) (ω : Fin ((bHandler q).seedLen.eval n) → Bool)
    (s : Fin ((bHandler q).stateLen.eval n) → Bool) (a : Fin ((PolyExpr.const 1).eval n) → Bool) :
    (bHandler q).finish n z ω s a =
      .pure (padFin ((bHandler q).outLen.eval n) (List.ofFn a)) := by
  rw [InteractiveHandler.finish_eq]
  have h0 : (bHandler q).finCall.eval n = 0 := by rw [bHandler_finCall, PolyExpr.eval_const]
  rw [h0]
  refine buildComp_zero_of_ret ?_
  show decodeBitMove _ _ _ (bFin _) = _
  rw [bFin, InteractiveHandler.finInput_eq, pairSndD_pairEncode, pairSndD_pairEncode,
    pairFstD_pairEncode]
  have hw : List.ofFn (padFin ((bHandler q).outLen.eval n) (List.ofFn a)) = List.ofFn a :=
    ofFn_padFin_of_length (by rw [List.length_ofFn, bHandler_outLen])
  exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).symm.trans
    (decodeBitMove_ret _ _ _ _)

/-! ### Answers of the handler -/

/-- The pair of an outer answer `y = ⟨r, c₁⟩`, read at `2n` bits:
`bKeyOf n y = padFin (2n) (pairFstD ⟦y⟧ ++ pairSndD ⟦y⟧)`. -/
def bKeyOf (n : ℕ) {m : ℕ} (y : Fin m → Bool) : Fin (2 * n) → Bool :=
  padFin (2 * n) (pairFstD (List.ofFn y) ++ pairSndD (List.ofFn y))

/-- `bKeyOf n y = padFin (2n) (pairFstD ⟦y⟧ ++ pairSndD ⟦y⟧)`. -/
theorem bKeyOf_eq (n : ℕ) {m : ℕ} (y : Fin m → Bool) :
    bKeyOf n y = padFin (2 * n) (pairFstD (List.ofFn y) ++ pairSndD (List.ofFn y)) := rfl

section Answers

variable (n : ℕ) (z : List Bool) (W : Fin (q.eval n * (2 * n)) → Bool)

/-- The round input of a call, field by field, on an encoded state that fits, with `j < q(n)`
and the seed `bHSeed W`. -/
private theorem fields_input {i : Fin 3} (x Lg : List Bool) (j : ℕ) (L : List (LEntry n))
    (o : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n) (hL : L.length ≤ q.eval n)
    (hm : ∀ e ∈ L, e.2.2.length = n) :
    let w := InteractiveHandler.input n z (List.ofFn (bHSeed q n W))
      (List.ofFn (bHState q n j L o)) i x Lg
    rU w = List.replicate n true ∧ rI w = List.replicate i true ∧ rX w = x ∧ rL w = Lg ∧
      bTbl w = tblW L ∧ bJ w = List.replicate j true ∧ bFlag w = o.isSome ∧
      bRec w = (recBits n o).drop 1 ∧ bTape w = List.ofFn (bTapeOf q n W j hj) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := fields_bState q n j L o hj.le hL hm
  have hS : rS (InteractiveHandler.input n z (List.ofFn (bHSeed q n W))
      (List.ofFn (bHState q n j L o)) i x Lg) = List.ofFn (bState q n j L o) :=
    (InteractiveHandler.rS_input ..).trans (ofFn_bHState q n j L o)
  have hU := InteractiveHandler.rU_input (k := 3) n z (List.ofFn (bHSeed q n W))
    (List.ofFn (bHState q n j L o)) i x Lg
  have hJ : bJ (InteractiveHandler.input n z (List.ofFn (bHSeed q n W))
      (List.ofFn (bHState q n j L o)) i x Lg) = List.replicate j true := by rw [bJ, hS, h₂]
  refine ⟨hU, InteractiveHandler.rI_input .., InteractiveHandler.rX_input ..,
    InteractiveHandler.rL_input .., by rw [bTbl, hS, h₁], hJ, by rw [bFlag, hS, h₃],
    by rw [bRec, hS, hU, List.length_replicate, h₄], ?_⟩
  rw [bTape, hJ, hU, InteractiveHandler.rW_input, ofFn_bHSeed, List.length_replicate,
    List.length_replicate, tagLen_eval, bTapeOf_eq]
  exact EnsembleLemmas.take_drop_ofFn_blocks W j hj

/-- The outer answer recorded in a one-entry log. -/
private theorem rAns_one (w : List Bool) (u x' y : List Bool)
    (hL : rL w = pairEncode (pairEncode u (pairEncode x' y)) []) : rAns w = y := by
  rw [InteractiveHandler.rAns_eq, hL, pairFstD_pairEncode, pairSndD_pairEncode,
    pairSndD_pairEncode]

/-- A one-entry log is not empty. -/
private theorem log_ne_nil (u x' y : List Bool) :
    decide (pairEncode (pairEncode u (pairEncode x' y)) [] = []) = false :=
  decide_eq_false (pairEncode_ne_nil _ _)

/-- A word read at `2n` bits is a `2n`-bit word. -/
private theorem bPad2_fields (w v : List Bool) (hU : rU w = List.replicate n true) :
    bPad2 w v = List.ofFn (padFin (2 * n) v) := by
  rw [bPad2, hU, List.length_replicate, tagLen_eval, EnsembleLemmas.ofFn_padFin_eq_padL]

/-- The new state with table word `tblW L'`, count `j + 1` and record `recBits o'`. -/
private theorem bNew_fields (w : List Bool) (j : ℕ) (L' : List (LEntry n))
    (o' : Option (Fin (ettCt.eval n) → Bool)) (hU : rU w = List.replicate n true)
    (hJ : bJ w = List.replicate j true) :
    bNew q w (tblW L') (recBits n o') = List.ofFn (bHState q n (j + 1) L' o') := by
  rw [bNew, hU, hJ, List.length_replicate, ofFn_bHState, bState_eq,
    EnsembleLemmas.ofFn_padFin_eq_padL, List.replicate_succ]

/-- **The tag of a pair `p`:** the table's, else the record's, else the tape `t`.

**Proof sketch.** The lookup on the table word is `lookL L p` (`lookup_tblW`). On an entry `e`
the lookup is nonempty and its first `2n` bits are `⟦e.2.1⟧`. Without an entry, by cases on `o`:
with no record the flag is false and the tape is taken; with the record `c`, its pair and tag
read at `2n` bits are `pairW n ⟦c⟧` and `padFin (2n) (wT ⟦c⟧)` (`bPad2_fields`), and the test
`pairW n ⟦c⟧ = p` selects the record's tag or the tape, as `tagOf` does. -/
private theorem bTag_fields (w : List Bool) (L : List (LEntry n))
    (o : Option (Fin (ettCt.eval n) → Bool)) (p t : Fin (2 * n) → Bool)
    (hU : rU w = List.replicate n true) (hT : bTbl w = tblW L) (hF : bFlag w = o.isSome)
    (hR : bRec w = (recBits n o).drop 1) (hTp : bTape w = List.ofFn t)
    (hK : bKey w = List.ofFn p) :
    bTag w = List.ofFn ((tagOf ((o, L) : LSt n (ettCt.eval n)) p).getD t) := by
  rw [bTag, bLook, hK, hT, lookup_tblW, tagOf_eq]
  cases h : lookL L p with
  | some e =>
    simp only [decide_eq_false (pairEncode_ne_nil _ _), Bool.false_eq_true, if_false,
      pairSndD_pairEncode, Option.getD_some]
    rw [hU, List.length_replicate, tagLen_eval, List.take_left' (by rw [List.length_ofFn])]
  | none =>
    simp only [decide_true, if_true]
    cases o with
    | none => simp only [hF, Option.isSome_none, Bool.false_and, Bool.false_eq_true, if_false,
        hTp, Option.getD_none]
    | some c =>
      have hRc : bRec w = List.ofFn c := by
        rw [hR, recBits_some, List.drop_succ_cons, List.drop_zero]
      have hCK : bChalKey w = List.ofFn (pairW n (List.ofFn c)) := by
        rw [bChalKey, hRc, bPad2_fields n w _ hU, pairW_eq, pairV_eq, wR_eq, wC_eq]
      have hCT : bChalTag w = List.ofFn (padFin (2 * n) (wT (List.ofFn c))) := by
        rw [bChalTag, hRc, bPad2_fields n w _ hU, wT_eq]
      simp only [hF, Option.isSome_some, Bool.true_and, hCK, List.ofFn_inj]
      by_cases hc : pairW n (List.ofFn c) = p
      · simp only [hc, decide_true, if_true, hCT, Option.getD_some]
      · simp only [hc, decide_false, Bool.false_eq_true, if_false, hTp, Option.getD_none]

/-- **The lazy decryption answer of the query `⟦x⟧`:** `bDecL w = lazyDec (o, L) ⟦x⟧`.

**Proof sketch.** The handler's tests are the lazy ones: `bRef w = refW o x` (by cases on `o`,
reading the record `c` from `recBits`), `bWF w = wfW n x`, and the decryption key read at `2n`
bits is `pairW n x` (`bPad2_fields`). The lookup on the table word is `lookL L (pairW n x)`
(`lookup_tblW`); on an entry `e` its first `2n` bits are `⟦e.2.1⟧` and the rest is `e.2.2`, so the
tag test and the answer `true :: e.2.2` are those of `lazyDec`. -/
private theorem bDecL_fields (w x : List Bool) (L : List (LEntry n))
    (o : Option (Fin (ettCt.eval n) → Bool))
    (hU : rU w = List.replicate n true) (hX : rX w = x) (hT : bTbl w = tblW L)
    (hF : bFlag w = o.isSome) (hR : bRec w = (recBits n o).drop 1) :
    bDecL w = lazyDec ((o, L) : LSt n (ettCt.eval n)) x := by
  have hRef : bRef w = refW o x := by
    rw [bRef, hF, hR, hX]
    cases o with
    | none => rw [Option.isSome_none, Bool.false_and, refW_none]
    | some c =>
      rw [recBits_some, List.drop_succ_cons, List.drop_zero, Option.isSome_some, Bool.true_and,
        refW_some]
      exact decide_eq_decide.2 eq_comm
  have hWF : bWF w = wfW n x := by
    rw [bWF, hU, hX, List.length_replicate, wfW_eq, wR_eq, wC_eq]
  have hDK : bDKey w = List.ofFn (pairW n x) := by
    rw [bDKey, hX, bPad2_fields n w _ hU, pairW_eq, pairV_eq, wR_eq, wC_eq]
  rw [bDecL, lazyDec_eq, hRef, hWF]
  simp only
  by_cases hc : (!refW o x && wfW n x) = true
  · rw [if_pos hc, if_pos hc, bLook, hDK, hT, lookup_tblW]
    cases h : lookL L (pairW n x) with
    | none => simp only [decide_true, if_true]
    | some e =>
      simp only [decide_eq_false (pairEncode_ne_nil _ _), Bool.false_eq_true, if_false,
        pairSndD_pairEncode]
      rw [hU, List.length_replicate, tagLen_eval, List.take_left' (by rw [List.length_ofFn]),
        List.drop_left' (by rw [List.length_ofFn]), hX, wT_eq]
      by_cases ht : List.ofFn e.2.1 = pairSndD (pairSndD x)
      · rw [if_pos (decide_eq_true ht), if_pos ht]
      · rw [if_neg (by rw [decide_eq_true_eq]; exact ht), if_neg ht]
  · rw [if_neg hc, if_neg hc]

/-- The flag and the record rebuild the record bits:
`o.isSome :: (recBits o).drop 1 = recBits o`. -/
private theorem recBits_fields (o : Option (Fin (ettCt.eval n) → Bool)) :
    o.isSome :: (recBits n o).drop 1 = recBits n o := by
  cases o with
  | none => rw [recBits_none, List.drop_succ_cons, List.drop_zero, Option.isSome_none]
  | some c => rw [recBits_some, List.drop_succ_cons, List.drop_zero, Option.isSome_some]

/-- The inner query word read at the outer length: `⟦padFin _ ⟦x⟧⟧ = ⟦x⟧` for an `n`-bit `x`. -/
private theorem ofFn_padFin_msg {m : ℕ} (x : Fin m → Bool) (hm : m = n) :
    List.ofFn (padFin ((pkDin 0).eval n) (List.ofFn x)) = List.ofFn x :=
  ofFn_padFin_of_length (by rw [List.length_ofFn, PRFGame.pkDin_zero, PolyExpr.eval_var, hm])

/-- **Encryption:** from `bState j L o` with `j < q(n)`, the query `m = ⟦x⟧` asks the CPA
encryption oracle at `m`; its answer `y` gives the ciphertext `⟨pairFstD y, ⟨pairSndD y, t⟩⟩`
with the tag `t` of the pair `bKeyOf n y` (`tagOf`, else the tape `j`), and the state
`bState (j + 1) ((bKeyOf n y, t, m) :: L) o`.

**Proof sketch.** Read the round input field by field (`fields_input`); the first round, with an
empty log, asks `m`; the second, with the answer in the log (`rAns_one`), computes the tag
(`bTag_fields`, from `lookup_tblW`), the ciphertext and the new state (`bNew_fields`, `tblW_cons`);
`InteractiveHandler.impl_of_query` assembles the two rounds. -/
theorem bHandler_impl_enc (x : Fin ((ettDin 0).eval n) → Bool) (j : ℕ) (L : List (LEntry n))
    (o : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n) (hL : L.length ≤ q.eval n)
    (hm : ∀ e ∈ L, e.2.2.length = n) :
    (bHandler q).impl n z (bHSeed q n W) 0 x (bHState q n j L o) =
      .query 0 (padFin _ (List.ofFn x)) fun y =>
        .pure (padFin _ (ctW (pairFstD (List.ofFn y)) (pairSndD (List.ofFn y))
            (List.ofFn ((tagOf ((o, L) : LSt n (ettCt.eval n)) (bKeyOf n y)).getD
              (bTapeOf q n W j hj)))),
          bHState q n (j + 1) ((bKeyOf n y, (tagOf ((o, L) : LSt n (ettCt.eval n))
            (bKeyOf n y)).getD (bTapeOf q n W j hj), List.ofFn x) :: L) o) := by
  have hx := ofFn_padFin_msg n x (by rw [ettDin_zero, PolyExpr.eval_var])
  refine InteractiveHandler.impl_of_query _ n z _ x _ 0 _ _ _
    (by rw [bHandler_perCall, PolyExpr.eval_const]) ?_ ?_
  · show bRun q _ = _
    obtain ⟨-, hI, hX, hL', -⟩ := fields_input q n z W (i := 0) (List.ofFn x) [] j L o hj hL hm
    rw [bRun, hI, Fin.val_zero, List.replicate_zero, List.headD_nil, if_neg Bool.false_ne_true,
      hL', if_pos (decide_eq_true rfl), hX, hx]
  · intro y
    show bRun q _ = _
    simp only [Fin.val_zero, List.replicate_zero]
    obtain ⟨hU, hI, hX, hL', hT, hJ, hF, hR, hTp⟩ := fields_input q n z W (i := 0) (List.ofFn x)
      (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((pkDin 0).eval n)
        (List.ofFn x))) (List.ofFn y))) []) j L o hj hL hm
    have hY := rAns_one _ _ _ _ hL'
    have hK : bKey (InteractiveHandler.input n z (List.ofFn (bHSeed q n W))
        (List.ofFn (bHState q n j L o)) (0 : Fin 3) (List.ofFn x)
        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((pkDin 0).eval n)
          (List.ofFn x))) (List.ofFn y))) [])) = List.ofFn (bKeyOf n y) := by
      rw [bKey, hY, bPad2_fields n _ _ hU, bKeyOf_eq]
    have hTag := bTag_fields n _ L o (bKeyOf n y) (bTapeOf q n W j hj) hU hT hF hR hTp hK
    rw [bRun, hI, Fin.val_zero, List.replicate_zero, List.headD_nil, if_neg Bool.false_ne_true,
      hL', log_ne_nil, if_neg Bool.false_ne_true, bCt, hY, hTag, hU, List.length_replicate, hK,
      hX, hT, hF, hR, recBits_fields,
      ← tblW_cons (bKeyOf n y, (tagOf ((o, L) : LSt n (ettCt.eval n))
        (bKeyOf n y)).getD (bTapeOf q n W j hj), List.ofFn x) L,
      bNew_fields q n _ j _ o hU hJ, ← ctW_eq]
    rw [EnsembleLemmas.ofFn_padFin_eq_padL, ettDout_zero]

/-- **Decryption:** from `bState j L o` with `j < q(n)`, the query `⟦x⟧` is answered by
`lazyDec (o, L) ⟦x⟧` without an outer query, and the state is `bState (j + 1) L o`
(`bDecL_fields`). -/
theorem bHandler_impl_dec (x : Fin ((ettDin 1).eval n) → Bool) (j : ℕ) (L : List (LEntry n))
    (o : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n) (hL : L.length ≤ q.eval n)
    (hm : ∀ e ∈ L, e.2.2.length = n) :
    (bHandler q).impl n z (bHSeed q n W) 1 x (bHState q n j L o) =
      .pure (padFin _ (lazyDec ((o, L) : LSt n (ettCt.eval n)) (List.ofFn x)),
        bHState q n (j + 1) L o) := by
  refine InteractiveHandler.impl_of_ret _ n z _ x _ _ _ ?_
  show bRun q _ = _
  obtain ⟨hU, hI, hX, -, hT, hJ, hF, hR, -⟩ :=
    fields_input q n z W (i := 1) (List.ofFn x) [] j L o hj hL hm
  rw [bRun, hI, Fin.val_one, List.replicate_one, List.headD_cons, if_pos rfl, List.drop_succ_cons,
    List.drop_zero, List.headD_nil, if_neg Bool.false_ne_true, bDecAns,
    bDecL_fields n _ _ L o hU hX hT hF hR, hU, List.length_replicate, hT, hF, hR, recBits_fields,
    bNew_fields q n _ j L o hU hJ]
  beta_reduce
  rw [EnsembleLemmas.ofFn_padFin_eq_padL, ettDout_one]

/-- **A recorded challenge is repeated:** from `bState j L (some c)`, a challenge is answered `c`
and the state is `bState (j + 1) L (some c)`: for `j < q(n)`, `|L| ≤ q(n)` and `n`-bit messages
in `L`, `(bHandler q).impl n z (bHSeed q n W) 2 x (bHState q n j L (some c)) =
pure (padFin _ ⟦c⟧, bHState q n (j + 1) L (some c))`. -/
theorem bHandler_impl_challenge_some (x : Fin ((ettDin 2).eval n) → Bool) (j : ℕ)
    (L : List (LEntry n)) (c : Fin (ettCt.eval n) → Bool) (hj : j < q.eval n)
    (hL : L.length ≤ q.eval n) (hm : ∀ e ∈ L, e.2.2.length = n) :
    (bHandler q).impl n z (bHSeed q n W) 2 x (bHState q n j L (some c)) =
      .pure (padFin _ (List.ofFn c), bHState q n (j + 1) L (some c)) := by
  refine InteractiveHandler.impl_of_ret _ n z _ x _ _ _ ?_
  show bRun q _ = _
  obtain ⟨hU, hI, -, -, hT, hJ, hF, hR, -⟩ :=
    fields_input q n z W (i := 2) (List.ofFn x) [] j L (some c) hj hL hm
  have hRc : (recBits n (some c)).drop 1 = List.ofFn c := by
    rw [recBits_some, List.drop_succ_cons, List.drop_zero]
  have hrec : true :: List.ofFn c = recBits n (some c) := (recBits_some n c).symm
  rw [bRun, hI, hF, hR, hRc]
  simp only [show List.replicate ((2 : Fin 3) : ℕ) true = [true, true] from rfl, List.headD_cons,
    List.drop_succ_cons, List.drop_zero, if_true, Option.isSome_some]
  rw [hT, hrec, bNew_fields q n _ j L (some c) hU hJ, hU, List.length_replicate]
  rw [EnsembleLemmas.ofFn_padFin_eq_padL, ettDout_two]

/-- **The first challenge:** from `bState j L none` with `j < q(n)`, the challenge `⟦x⟧` asks the
CPA challenge oracle at `⟦x⟧`; its answer `y` gives the ciphertext
`c = ⟨pairFstD y, ⟨pairSndD y, t⟩⟩` with the tag `t` of `bKeyOf n y` (`tagOf (none, L)`, else the
tape `j`), recorded in the state `bState (j + 1) L (some c)`.

**Proof sketch.** As for `bHandler_impl_enc`: read the round input field by field
(`fields_input`); the first round, with no record (flag false) and an empty log, asks the CPA
challenge oracle (oracle `2`) at `⟦x⟧`; the second, with the answer `y` in the log (`rAns_one`),
takes the tag of `bKeyOf n y` (`bTag_fields` with no record), returns the ciphertext `c`, and
writes the record bits `true :: ⟦c⟧ = recBits n (some c)` with the table unchanged
(`bNew_fields`); `InteractiveHandler.impl_of_query` assembles the two rounds. -/
theorem bHandler_impl_challenge_none (x : Fin ((ettDin 2).eval n) → Bool) (j : ℕ)
    (L : List (LEntry n)) (hj : j < q.eval n) (hL : L.length ≤ q.eval n)
    (hm : ∀ e ∈ L, e.2.2.length = n) :
    (bHandler q).impl n z (bHSeed q n W) 2 x (bHState q n j L none) =
      .query 2 (padFin _ (List.ofFn x)) fun y =>
        .pure (padFin _ (ctW (pairFstD (List.ofFn y)) (pairSndD (List.ofFn y))
            (List.ofFn ((tagOf ((none, L) : LSt n (ettCt.eval n)) (bKeyOf n y)).getD
              (bTapeOf q n W j hj)))),
          bHState q n (j + 1) L (some (padFin (ettCt.eval n) (ctW (pairFstD (List.ofFn y))
            (pairSndD (List.ofFn y)) (List.ofFn ((tagOf ((none, L) : LSt n (ettCt.eval n))
              (bKeyOf n y)).getD (bTapeOf q n W j hj))))))) := by
  have hx : List.ofFn (padFin ((pkDin 2).eval n) (List.ofFn x)) = List.ofFn x :=
    ofFn_padFin_of_length (by rw [List.length_ofFn, PRFGame.pkDin_two, ettDin_two])
  refine InteractiveHandler.impl_of_query _ n z _ x _ 2 _ _ _
    (by rw [bHandler_perCall, PolyExpr.eval_const]) ?_ ?_
  · show bRun q _ = _
    obtain ⟨-, hI, hX, hL', -, -, hF, -⟩ :=
      fields_input q n z W (i := 2) (List.ofFn x) [] j L none hj hL hm
    rw [bRun, hI, hF, hL']
    simp only [show List.replicate ((2 : Fin 3) : ℕ) true = [true, true] from rfl, List.headD_cons,
      List.drop_succ_cons, List.drop_zero, if_true, Option.isSome_none, Bool.false_eq_true,
      if_false, decide_true]
    rw [hX, hx]
  · intro y
    show bRun q _ = _
    simp only [show List.replicate ((2 : Fin 3) : ℕ) true = [true, true] from rfl]
    obtain ⟨hU, hI, hX, hL', hT, hJ, hF, hR, hTp⟩ := fields_input q n z W (i := 2) (List.ofFn x)
      (pairEncode (pairEncode [true, true]
        (pairEncode (List.ofFn (padFin ((pkDin 2).eval n) (List.ofFn x))) (List.ofFn y))) [])
      j L none hj hL hm
    have hY := rAns_one _ _ _ _ hL'
    have hK : bKey (InteractiveHandler.input n z (List.ofFn (bHSeed q n W))
        (List.ofFn (bHState q n j L none)) (2 : Fin 3) (List.ofFn x)
        (pairEncode (pairEncode [true, true]
          (pairEncode (List.ofFn (padFin ((pkDin 2).eval n) (List.ofFn x))) (List.ofFn y))) [])) =
        List.ofFn (bKeyOf n y) := by
      rw [bKey, hY, bPad2_fields n _ _ hU, bKeyOf_eq]
    have hTag := bTag_fields n _ L none (bKeyOf n y) (bTapeOf q n W j hj) hU hT hF hR hTp hK
    have hrec : true :: bCt (InteractiveHandler.input n z (List.ofFn (bHSeed q n W))
        (List.ofFn (bHState q n j L none)) (2 : Fin 3) (List.ofFn x)
        (pairEncode (pairEncode [true, true]
          (pairEncode (List.ofFn (padFin ((pkDin 2).eval n) (List.ofFn x))) (List.ofFn y))) [])) =
        recBits n (some (padFin (ettCt.eval n) (ctW (pairFstD (List.ofFn y))
            (pairSndD (List.ofFn y)) (List.ofFn ((tagOf ((none, L) : LSt n (ettCt.eval n))
              (bKeyOf n y)).getD (bTapeOf q n W j hj)))))) := by
      rw [recBits_some, bCt, hY, hTag, hU, List.length_replicate, ← ctW_eq,
        EnsembleLemmas.ofFn_padFin_eq_padL]
    rw [bRun, hI, hF, hL']
    simp only [show List.replicate ((2 : Fin 3) : ℕ) true = [true, true] from rfl, List.headD_cons,
      List.drop_succ_cons, List.drop_zero, if_true, Option.isSome_none, Bool.false_eq_true,
      if_false]
    rw [log_ne_nil, if_neg Bool.false_ne_true, hrec, hT, bNew_fields q n _ j L _ hU hJ, bCt, hY,
      hTag, hU, List.length_replicate, ← ctW_eq]
    rw [EnsembleLemmas.ofFn_padFin_eq_padL, ettDout_two]

end Answers

end TCSlib.Cryptography.Composability.ETTGame

## ===== TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/CPAReduction.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.CPAHandler
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Reduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The CPA reduction for the encrypt-then-tag scheme

Step 3 of [PS10, Theorem 170.4]: the experiment that rejects fresh decryption queries, with a
uniform random tag function, is the CPA experiment of the §3.9 scheme against a machine adversary
`B` (`exists_cpaStep`). `B` is T2 (`Games.exists_interactiveHandlerMachine`) applied to the handler
`bHandler` (through the input-free companion `Games.exists_toCompOn_of_toComp`), run on the empty
input (`NUPPT.exists_comp`).

The proof composes the handler with the CPA oracles `PRFGame.fImpl` (`QueryImpl.comp`). Each
composed call, from the encoded state `bState j L o` and the CPA record of `o`, has the law of the
call of the lazy experiment with the tapes in advance (`ettLazyTape`) from `((o, L), j)`
(`comp_bAbs`), as long as `j` is below the number `q(n)` of tapes and the table has at most `j`
entries of `n`-bit messages (`bInv`, kept by every call, `ettLazyTape_bInv`); the adversary asks
at most `q(n)` queries, so this holds along every run (`expect_simulate_abs_inv`). Drawing the
seed uniformly gives fresh tapes (`expect_ettLazyTape`), and the lazy experiment is the rejecting
experiment with a uniform random tag function (`expect_ettImpl_lazy`).

## Main definitions

* `ETTGame.cpaRec`: the CPA record `⟨r, c₁⟩` of a CCA2 record `⟨r, ⟨c₁, t⟩⟩`.
* `ETTGame.bAbs`, `bInv`, `bTapes`: the abstraction, the invariant and the tapes.

## Main results

* `ETTGame.comp_bAbs`: one composed call has the law of a call of `ettLazyTape`.
* `ETTGame.ettLazyTape_bInv`: the calls of `ettLazyTape` keep the invariant.
* `ETTGame.exists_cpaStep`: step 3, the rejecting experiment with a random tag function is a CPA
  experiment of the §3.9 scheme.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 170.4 (book pp. 170–171).
-/

namespace TCSlib.Cryptography.Composability.ETTGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp
open TCSlib.Cryptography.Composability.PRFGame (pkDin pkDout ctP fImpl atkOf qRed ctOf)

/-! ### The abstraction -/

/-- **The CPA record** of a CCA2 record `c = ⟨r, ⟨c₁, t⟩⟩`: the pair `⟨r, c₁⟩` at `3n + 2` bits. -/
def cpaRec (n : ℕ) (c : Fin (ettCt.eval n) → Bool) : Fin (ctP.eval n) → Bool :=
  padFin _ (pairEncode (wR (List.ofFn c)) (wC (List.ofFn c)))

/-- `cpaRec n c = padFin _ ⟨wR ⟦c⟧, wC ⟦c⟧⟩`. -/
theorem cpaRec_eq (n : ℕ) (c : Fin (ettCt.eval n) → Bool) :
    cpaRec n c = padFin _ (pairEncode (wR (List.ofFn c)) (wC (List.ofFn c))) := rfl

/-- **The abstraction:** the handler's state `bState j L o` and the CPA record of `o`, as functions
of the lazy experiment's state `(o, L)` with the counter `j`,
`bAbs q n ((o, L), j) = (bHState q n j L o, o.map (cpaRec n))`. -/
def bAbs (q : PolyExpr) (n : ℕ) (s : LSt n (ettCt.eval n) × ℕ) :
    (Fin ((bHandler q).stateLen.eval n) → Bool) × Option (Fin (ctP.eval n) → Bool) :=
  (bHState q n s.2 s.1.2 s.1.1, s.1.1.map (cpaRec n))

/-- `bAbs q n ((o, L), j) = (bHState q n j L o, o.map (cpaRec n))`. -/
theorem bAbs_eq (q : PolyExpr) (n : ℕ) (s : LSt n (ettCt.eval n) × ℕ) :
    bAbs q n s = (bHState q n s.2 s.1.2 s.1.1, s.1.1.map (cpaRec n)) := rfl

/-- **The invariant:** the table has at most one entry per query, each with an `n`-bit message,
`bInv n ((o, L), j) ↔ |L| ≤ j ∧ ∀ e ∈ L, |e.2.2| = n`. -/
def bInv (n : ℕ) (s : LSt n (ettCt.eval n) × ℕ) : Prop :=
  s.1.2.length ≤ s.2 ∧ ∀ e ∈ s.1.2, e.2.2.length = n

/-- `bInv n ((o, L), j) ↔ |L| ≤ j ∧ every message of `L` has `n` bits`. -/
theorem bInv_iff (n : ℕ) (s : LSt n (ettCt.eval n) × ℕ) :
    bInv n s ↔ s.1.2.length ≤ s.2 ∧ ∀ e ∈ s.1.2, e.2.2.length = n := Iff.rfl

section Composed

variable (q : PolyExpr) (b : Bool) (n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)) (z : List Bool)
  (W : Fin (q.eval n * (2 * n)) → Bool)

/-- The tag tapes of the tape word, extended to every index (`AdaptiveCPA.extTape`):
`bTapes q n W = extTape (blocks (q n) (2n) W)`. -/
noncomputable def bTapes : ℕ → Fin (2 * n) → Bool :=
  AdaptiveCPA.extTape (EnsembleLemmas.blocks (q.eval n) (2 * n) W)

/-- `bTapes q n W = extTape (blocks (q n) (2n) W)`. -/
theorem bTapes_eq :
    bTapes q n W = AdaptiveCPA.extTape (EnsembleLemmas.blocks (q.eval n) (2 * n) W) :=
  rfl

/-- Below `q(n)`, the extended tapes are the tapes: `bTapes q n W j = bTapeOf q n W j hj`. -/
theorem bTapes_of_lt (j : ℕ) (hj : j < q.eval n) : bTapes q n W j = bTapeOf q n W j hj := by
  rw [bTapes_eq, AdaptiveCPA.extTape_of_lt _ hj, bTapeOf_eq]

/-- The CPA ciphertext of an `n`-bit message as a list:
`⟦padFin _ (ctOf r m (f r))⟧ = ⟨r, m ⊕ f(r)⟩`. -/
private theorem ofFn_ctOf {k : ℕ} (hk : k = ctP.eval n) (r : Fin n → Bool) {m : List Bool}
    (hm : m.length = n) :
    List.ofFn (padFin k (ctOf r m (f r))) = pairEncode (List.ofFn r) (maskL f r m) := by
  rw [ofFn_padFin_of_length (by rw [PRFGame.length_ctOf r hm, hk, PRFGame.ctP_eval]),
    PRFGame.ctOf_eq, maskL_eq]

/-- The pair read from a CPA ciphertext is the pair of the encryption:
`bKeyOf n (padFin _ (ctOf r m (f r))) = pairV n ⟦r⟧ (maskL f r m)`. -/
private theorem bKeyOf_ctOf {k : ℕ} (hk : k = ctP.eval n) (r : Fin n → Bool) {m : List Bool}
    (hm : m.length = n) :
    bKeyOf n (padFin k (ctOf r m (f r))) = pairV n (List.ofFn r) (maskL f r m) := by
  rw [bKeyOf_eq, ofFn_ctOf n f hk r hm, pairFstD_pairEncode, pairSndD_pairEncode, pairV_eq]

/-- **One composed call has the law of a call of the lazy experiment with tapes in advance:** from
`bAbs ((o, L), j)` with the invariant and `j < q(n)`, the handler composed with the CPA oracles
with pad function `f` gives every function `g` of the answer and the state the expectation that
the call of `ettLazyTape` with the tapes `bTapes W` from `((o, L), j)` gives it, with the new state
abstracted.

**Proof sketch.** By the oracle and the record: encryption and a first challenge ask the CPA
oracle, which draws `r` and answers `⟨r, m ⊕ f(r)⟩` (`PRFGame.fImpl_enc`,
`PRFGame.fImpl_challenge_none`); the handler reads the pair `r ‖ (m ⊕ f(r))` (`bKeyOf_ctOf`) and
tags it as `lazyStep` does (`bHandler_impl_enc`, `bHandler_impl_challenge_none`), and the recorded
CPA challenge is the CPA record of the CCA2 record. Decryption and a repeated challenge answer
directly in both (`bHandler_impl_dec`, `bHandler_impl_challenge_some`), and the lazy experiment's
nonce is not read (`expect_const`). -/
theorem comp_bAbs (i : Fin 3) (x : (bitSpecAt ettDin ettDout n).dom i)
    (s : LSt n (ettCt.eval n) × ℕ) (hP : bInv n s) (hs : s.2 < q.eval n)
    (g : (bitSpecAt ettDin ettDout n).rng i ×
      ((Fin ((bHandler q).stateLen.eval n) → Bool) × Option (Fin (ctP.eval n) → Bool)) → ℝ) :
    expect ((fImpl (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) (ctP.eval n) n
        (atkOf false) b f).comp ((bHandler q).impl n z (bHSeed q n W)) i x (bAbs q n s)) g =
      expect (ettLazyTape (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
        (ettCt.eval n) n f b (bTapes q n W) i x s) fun p => g (p.1, bAbs q n p.2) := by
  obtain ⟨⟨o, L⟩, j⟩ := s
  obtain ⟨hL, hm⟩ := hP
  have hj : j < q.eval n := hs
  have hLq : L.length ≤ q.eval n := le_trans hL hj.le
  rw [QueryImpl.comp_apply, bAbs_eq, ettLazyTape_eq, tapeImpl_apply, ettLazyK_eq,
    bTapes_of_lt q n W j hj]
  simp only [OracleComp.bind_assoc, OracleComp.pure_bind, expect_bind, expect_pure]
  match i, x with
  | 0, x =>
    have hx : (List.ofFn x).length = n := by
      rw [List.length_ofFn]
      show (ettDin 0).eval n = n
      rw [ettDin_zero, PolyExpr.eval_var]
    have hx' : List.ofFn (padFin ((pkDin 0).eval n) (List.ofFn x)) = List.ofFn x :=
      ofFn_padFin_of_length (by rw [hx, PRFGame.pkDin_zero, PolyExpr.eval_var])
    rw [bHandler_impl_enc q n z W x j L o hj hLq hm, simulate_query, PRFGame.fImpl_enc]
    simp only [OracleComp.bind_assoc, OracleComp.pure_bind, simulate_pure, expect_bind, expect_pure]
    refine congrArg _ (funext fun r => ?_)
    have hk : (fun i => (pkDout i).eval n) 0 = ctP.eval n := by
      show (pkDout 0).eval n = ctP.eval n
      rw [PRFGame.pkDout_zero]
    rw [lazyStep_enc, bAbs_eq, hx', ofFn_ctOf n f hk r hx, bKeyOf_ctOf n f hk r hx,
      pairFstD_pairEncode, pairSndD_pairEncode]
  | 1, x =>
    rw [bHandler_impl_dec q n z W x j L o hj hLq hm, simulate_pure]
    simp only [expect_pure, lazyStep_dec, bAbs_eq, expect_const]
  | 2, x =>
    cases o with
    | some c =>
      rw [bHandler_impl_challenge_some q n z W x j L c hj hLq hm, simulate_pure]
      simp only [expect_pure, lazyStep_challenge_some, bAbs_eq, expect_const]
    | none =>
      have hxx : (List.ofFn x).length = n + n := by
        rw [List.length_ofFn]
        show (ettDin 2).eval n = n + n
        rw [ettDin_two, PolyExpr.eval_add, PolyExpr.eval_var]
      have hx' : List.ofFn (padFin ((pkDin 2).eval n) (List.ofFn x)) = List.ofFn x :=
        ofFn_padFin_of_length (by rw [hxx, PRFGame.pkDin_two, PolyExpr.eval_add, PolyExpr.eval_var])
      have hmsg : (AdaptiveCPA.msgOf n b (List.ofFn x)).length = n := by
        rw [AdaptiveCPA.msgOf_eq]
        cases b <;> simp [hxx]
      rw [bHandler_impl_challenge_none q n z W x j L hj hLq hm, simulate_query, Option.map_none,
        PRFGame.fImpl_challenge_none]
      simp only [OracleComp.bind_assoc, OracleComp.pure_bind, simulate_pure, expect_bind,
        expect_pure]
      refine congrArg _ (funext fun r => ?_)
      have hk : (fun i => (pkDout i).eval n) 2 = ctP.eval n := by
        show (pkDout 2).eval n = ctP.eval n
        rw [PRFGame.pkDout_two]
      have hlen : (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn x)))
          (List.ofFn ((tagOf ((none, L) : LSt n (ettCt.eval n)) (pairV n (List.ofFn r)
            (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn x))))).getD
              (bTapeOf q n W j hj)))).length =
          ettCt.eval n := by
        rw [ctW_eq, length_pairEncode, length_pairEncode, List.length_ofFn,
          length_maskL f r hmsg, List.length_ofFn, ettCt_eval]
        omega
      have hrec : cpaRec n (padFin (ettCt.eval n) (ctW (List.ofFn r)
          (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn x)))
          (List.ofFn ((tagOf ((none, L) : LSt n (ettCt.eval n)) (pairV n (List.ofFn r)
            (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn x))))).getD (bTapeOf q n W j hj))))) =
          padFin (ctP.eval n) (ctOf r (AdaptiveCPA.msgOf n b (List.ofFn x)) (f r)) := by
        rw [cpaRec_eq, ofFn_padFin_of_length hlen, wR_ctW, wC_ctW, PRFGame.ctOf_eq, maskL_eq]
      rw [lazyStep_challenge_none, bAbs_eq, hx', ofFn_ctOf n f hk r hmsg, bKeyOf_ctOf n f hk r hmsg,
        pairFstD_pairEncode, pairSndD_pairEncode]
      simp only [Option.map_some, hrec]

/-- **The calls of the lazy experiment keep the invariant** and raise the counter by one: an
encryption adds one entry with the `n`-bit message; the other calls keep the table,
`bInv n s → (ettLazyTape … T i x s).AllOutputs fun p => bInv n p.2 ∧ p.2.2 ≤ s.2 + 1`.

**Proof sketch.** Unfold one call (`ettLazyTape_eq`, `tapeImpl_apply`, `ettLazyK_eq`): for every
nonce it is a pure step to the counter `j + 1`, so the counter bound holds by `le_rfl`. By the
oracle: an encryption adds the entry with the message `⟦x⟧` of `n` bits (`lazyStep_enc`), so
`|L| ≤ j` becomes `|L| + 1 ≤ j + 1`; decryption and both challenge cases keep the table
(`lazyStep_dec`, `lazyStep_challenge_some`, `lazyStep_challenge_none`), and `|L| ≤ j ≤ j + 1`. -/
theorem ettLazyTape_bInv (T : ℕ → Fin (2 * n) → Bool) (i : Fin 3)
    (x : (bitSpecAt ettDin ettDout n).dom i) (s : LSt n (ettCt.eval n) × ℕ) (hP : bInv n s) :
    (ettLazyTape (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n f b T
      i x s).AllOutputs fun p => bInv n p.2 ∧ p.2.2 ≤ s.2 + 1 := by
  obtain ⟨⟨o, L⟩, j⟩ := s
  obtain ⟨hL, hm⟩ := hP
  rw [ettLazyTape_eq, tapeImpl_apply, ettLazyK_eq, OracleComp.bind_assoc]
  refine OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun r _ => ?_
  rw [OracleComp.pure_bind]
  refine OracleComp.allOutputs_pure.2 ⟨?_, le_rfl⟩
  match i, x with
  | 0, x =>
    have hx : (List.ofFn x).length = n := by
      rw [List.length_ofFn]
      show (ettDin 0).eval n = n
      rw [ettDin_zero, PolyExpr.eval_var]
    rw [lazyStep_enc, bInv_iff]
    refine ⟨by simp only [List.length_cons]; exact Nat.succ_le_succ hL, fun e he => ?_⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact hx
    · exact hm e he
  | 1, x =>
    rw [lazyStep_dec]
    exact ⟨Nat.le_succ_of_le hL, hm⟩
  | 2, x =>
    cases o with
    | some c =>
      rw [lazyStep_challenge_some]
      exact ⟨Nat.le_succ_of_le hL, hm⟩
    | none =>
      rw [lazyStep_challenge_none]
      exact ⟨Nat.le_succ_of_le hL, hm⟩

end Composed

/-! ### The reduction -/

/-- **Step 3 of [PS10, Thm 170.4]: the rejecting experiment with a random tag function is a CPA
experiment of the §3.9 scheme**,
`∃ B, ∀ b n f, 𝔼_R ettAcc … f R true b A (q n) =
𝔼_r 𝔼[⟦output⟧₀ = 1 | simulate (fImpl … (atkOf false) b f) (B.toComp … (qRed q n) r) none]`.
For a machine adversary `A` with budget `q` there is a machine
`B` such that, for every challenge bit `b`, every `n` and every pad function `f` on `n` bits, the
average over a uniform random tag function `R` of `A`'s acceptance probability in the experiment
that rejects fresh decryption queries is `B`'s acceptance probability in the CPA experiment with
pad function `f` (the oracles `PRFGame.fImpl`, on the lengths `pkDin`, `pkDout`) with budget
`qRed q`.

**Proof sketch.** `B` runs T2's machine for `bHandler` and the input-free companion of `A` on the
empty input (`NUPPT.exists_comp` with `pre = ⟨[], ·⟩`). Its coins are, through the bijections of
the companion, T2 and the seed, the tapes `W` and `A`'s coins `r` (`expect_sample_equiv`,
`ChallengeSim.expect_sample_prod`, `expect_sample_comm`). For fixed `W` and `r`, T2 turns `B`'s run
against the CPA oracles into the handler's simulation of `A` composed with them (`simulate_bind`,
`simulate_comp`, `bHandler_finish`); along `A`'s run (at most `q(n)` queries) it has the law of
`ettLazyTape` with the tapes of `W` (`expect_simulate_abs_inv`, `comp_bAbs`, `ettLazyTape_bInv`).
Drawing `W` gives fresh tapes (`expect_ettLazyTape`), and the lazy experiment from the empty state
is the rejecting experiment averaged over `R` (`expect_ettImpl_lazy`; the empty tag table writes
nothing). Widths are transported by `Games.expect_toCompOn_outLen` and `expect_ettImpl_outLen`. -/
theorem exists_cpaStep (A : NUPPT) (q : PolyExpr) :
    ∃ B : NUPPT, ∀ (b : Bool) (n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)),
      expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))) (fun R =>
          ettAcc (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n f R
            true b A (q.eval n)) =
        expect (sample (B.Coins n)) fun r =>
          expect (simulate (fImpl (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
              (ctP.eval n) n (atkOf false) b f)
              (B.toComp (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) 1) n
                ((qRed q).eval n) r) none)
            (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
  obtain ⟨A₂, -, hA₂⟩ := exists_toCompOn_of_toComp A
  obtain ⟨B, hB⟩ := exists_interactiveHandlerMachine A₂ q ettDin ettDout pkDin pkDout (.const 1)
    (bHandler q)
  obtain ⟨B', hc, -, -, hB'⟩ := NUPPT.exists_comp B
    (pre := fun y => pairEncode [] y) (post := id)
    ((polyTimeComputable_const []).pairEncode polyTimeComputable_id) polyTimeComputable_id
  refine ⟨B', fun b n f => ?_⟩
  obtain ⟨φ₀, hφ₀⟩ := hA₂ n
  obtain ⟨φ₂, hφ₂⟩ := hB n
  have hQ : q.eval n * (bHandler q).perCall.eval n + (bHandler q).finCall.eval n =
      (qRed q).eval n := by
    rw [bHandler_perCall, bHandler_finCall, PRFGame.qRed_eval]
  have hout : (bHandler q).outLen.eval n = 1 := by rw [bHandler_outLen, PolyExpr.eval_const]
  -- `B'` on the empty input history is `B` on the input `[]`.
  have hB'B : ∀ r : B.Coins n,
      B'.toComp (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) 1) n
          ((qRed q).eval n) (NUPPT.coinsCongr hc.symm n r) =
        B.toCompOn (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) 1) n
          ((qRed q).eval n) [] r := by
    intro r
    rw [NUPPT.toComp_eq, NUPPT.toCompOn_eq]
    congr 1
    funext hist
    rw [NUPPT.runAt_coinsCongr, hB', id_eq, ← NUPPT.runAt_eq]
  -- `B'`'s coins are a tape word and `A`'s coins.
  rw [← expect_sample_equiv (NUPPT.coinsCongr hc.symm n)]
  simp only [hB'B]
  rw [← expect_sample_equiv φ₂, ChallengeSim.expect_sample_prod,
    ← expect_sample_equiv (bHSeed q n)]
  conv_rhs => rw [expect_sample_comm]
  rw [← expect_sample_equiv φ₀]
  simp only [ettAcc_eq]
  rw [expect_sample_comm]
  refine congrArg _ (funext fun r => ?_)
  -- One run of `B'` is the handler's simulation of `A`, composed with the CPA oracles.
  have hrun : ∀ W : Fin (q.eval n * (2 * n)) → Bool,
      expect (simulate (fImpl (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
          (ctP.eval n) n (atkOf false) b f)
          (B.toCompOn (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) 1) n
            ((qRed q).eval n) [] (φ₂ (bHSeed q n W, φ₀ r))) none)
          (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) =
        expect (simulate (ettLazyTape (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
            (ettCt.eval n) n f b (bTapes q n W))
            (A₂.toCompOn (bitCodec (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
              ((PolyExpr.const 1).eval n)) n (q.eval n) [] (φ₀ r)) ((none, []), 0))
          (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
    intro W
    rw [expect_toCompOn_outLen _ B n _ [] _ none hout.symm
        (fun p => if p.1.headD false = true then (1 : ℝ) else 0), ← hQ,
      ← hφ₂ [] (bHSeed q n W) (φ₀ r), bHandler_advInput, simulate_bind, simulate_comp,
      OracleComp.bind_assoc, expect_bind]
    simp only [OracleComp.pure_bind, bHandler_finish, simulate_pure, expect_pure]
    rw [bHandler_init_hstate, show ((bHState q n 0 [] none, none) :
        (Fin ((bHandler q).stateLen.eval n) → Bool) × Option (Fin (ctP.eval n) → Bool)) =
        bAbs q n ((none, []), 0) from rfl,
      expect_simulate_abs_inv _ _ (bAbs q n) (bInv n) (fun s => s.2) (q.eval n)
        (fun i x s hP hs g => comp_bAbs q b n f [] W i x s hP hs g)
        (fun i x s hP _ => ettLazyTape_bInv b n f _ i x s hP) _ (q.eval n)
        (A₂.toCompOn_costBoundedBy _ n _ _ _) ((none, []), 0)
        ⟨le_rfl, fun e he => absurd he List.not_mem_nil⟩ (Nat.zero_add _).le]
    refine congrArg _ (funext fun p => ?_)
    rw [ofFn_padFin_of_length (by rw [List.length_ofFn, bHandler_outLen])]
  simp only [hrun, bTapes_eq]
  have hi0 : (fun i => (ettDin i).eval n) 0 = n := by
    show (ettDin 0).eval n = n
    rw [ettDin_zero, PolyExpr.eval_var]
  have hi2 : (fun i => (ettDin i).eval n) 2 = n + n := by
    show (ettDin 2).eval n = n + n
    rw [ettDin_two, PolyExpr.eval_add, PolyExpr.eval_var]
  rw [expect_sample_equiv (EnsembleLemmas.blocks (q.eval n) (2 * n)) (fun T =>
      expect (simulate (ettLazyTape (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
          (ettCt.eval n) n f b (AdaptiveCPA.extTape T))
          (A₂.toCompOn (bitCodec (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
            ((PolyExpr.const 1).eval n)) n (q.eval n) [] (φ₀ r)) ((none, []), 0))
        (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0)),
    expect_ettLazyTape _ _ _ _ _ _ (q.eval n)
      (fun a => if (List.ofFn a).headD false = true then (1 : ℝ) else 0) _
      (q.eval n) (A₂.toCompOn_costBoundedBy _ n _ _ _) (none, []) 0 (by omega),
    ← expect_ettImpl_lazy _ _ _ n f b (ettCt_eval n) hi0 hi2
      (fun a => if (List.ofFn a).headD false = true then (1 : ℝ) else 0) _ (none, [])
      (lInv_nil n f none)]
  refine congrArg _ (funext fun R => ?_)
  have htbl : ovr (tagTbl ((none, []) : LSt n (ettCt.eval n))) R = R := by
    rw [tagTbl_none_nil, ovr_nil]
  rw [htbl, hφ₀, keysL_nil]
  exact expect_ettImpl_outLen (PolyExpr.eval_const 1 n).symm _ _ _ _ A _ r

end TCSlib.Cryptography.Composability.ETTGame

## ===== TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Forgery.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Games
import TCSlib.Cryptography.Games.Hopping

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fresh decryption queries are rejected

Step 2 of [PS10, Theorem 170.4]: with a random tag function `R` on `2n` bits, the experiment that
answers every valid decryption query (`rej = false`) and the experiment that rejects the valid
queries whose pair `r ‖ c₁` is not the pair of an earlier `Enc′` answer (`rej = true`) differ by at
most `q / 2^{2n}` for an adversary making at most `q` queries.

* *Identical until bad.* The two experiments draw the same nonces and agree until the first
  decryption query that is not refused, is valid and has a fresh pair (`hitW`); the flag of
  `ettBad` records it (`ettBad_agree`, `ettBad_stick`), and forgetting the flag gives `ettImpl`
  (`simulate_ettBad_fst`).
* *The bad probability.* In the rejecting experiment the answers never read `R` outside the
  revealed pairs (the pairs of the `Enc′` answers and of the challenge). Averaging over `R`, write
  `R` overridden on the revealed pairs by a table `M` (`ovr`): an encryption at a new pair moves
  the value `R p` into the table (`expect_sample_ovr`), and a decryption query with a fresh pair
  guesses the unrevealed `R p`, with probability at most `2^{-2n}`. A valid query with the
  challenge's pair is the challenge itself, for `n > 0` (canonical parsing, `eq_ctW_of_wfW`), and is
  refused. The union bound over the queries gives `q / 2^{2n}` (`expect_prob_bad_le`).

## Main definitions

* `ETTGame.RevInv M s`: the invariant of the revealed pairs, with `keys M = M.map Prod.fst`,
  `keys M ⊆ s.2 ∪ {pairW n ⟦c⟧ | s.1 = some c}`, `s.2 ⊆ keys M`, and a record `s.1 = some c` with
  `⟦c⟧ = ctW ⟦r⟧ c₁ ⟦y⟧`, `|c₁| = n`, `pairV n ⟦r⟧ c₁ ∈ keys M` and `ovr M R (pairV n ⟦r⟧ c₁) = y`.

## Main results

* `ETTGame.ettBad_agree`, `ettBad_stick`, `simulate_ettBad_fst`.
* `ETTGame.abs_prob_ettImpl_rej_sub_le`: identical until bad.
* `ETTGame.expect_prob_bad_le`: the bad probability with a random tag function.
* `ETTGame.abs_ettAcc_rej_sub_le`: step 2, for machine adversaries.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 170.4 (book pp. 170–171).
* [BR06] M. Bellare, P. Rogaway, *The Security of Triple Encryption and a Framework for
  Code-Based Game-Playing Proofs*, EUROCRYPT 2006 (identical until bad).
-/

namespace TCSlib.Cryptography.Composability.ETTGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

/-! ### Identical until bad -/

section Agree

variable (ins outs : Fin 3 → ℕ) (d n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool))
  (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (b : Bool)

/-- **From a good state the two experiments agree on good successors:** for every function `G`
vanishing on flagged states, the calls of `ettBad … false` and `ettBad … true` have the same
expectation of `G`: for `s.2 ≠ true` and `G̃ ys = if ys.2.2 = true then 0 else G ys`,
`𝔼[G̃ | ettBad … false b i x s] = 𝔼[G̃ | ettBad … true b i x s]`.

**Proof sketch.** Both draw the same nonce and raise the flag by the same `hitQ`; only a
decryption answer reads `rej`, and off the flag the two answers agree (`decAnsW_agree`). -/
theorem ettBad_agree (i : Fin 3) (x : (bitSpec ins outs).dom i) (s : St n d × Bool)
    (hs : ¬ s.2 = true) (G : (bitSpec ins outs).rng i × (St n d × Bool) → ℝ) :
    expect (ettBad ins outs d n f g false b i x s) (fun ys => if ys.2.2 = true then 0 else G ys) =
      expect (ettBad ins outs d n f g true b i x s)
        (fun ys => if ys.2.2 = true then 0 else G ys) := by
  obtain ⟨s, β⟩ := s
  have hβ : β = false := Bool.eq_false_iff.2 hs
  subst hβ
  rw [ettBad_apply, ettBad_apply, ettImpl_apply, ettImpl_apply]
  simp only [OracleComp.bind_assoc, OracleComp.pure_bind, expect_bind, expect_pure,
    Bool.false_or]
  refine congrArg _ (funext fun r => ?_)
  match i, x with
  | 0, m => rw [ettStep_enc, ettStep_enc]
  | 1, w =>
    rw [hitQ_one, ettStep_dec, ettStep_dec]
    by_cases h : hitW g s (List.ofFn w) = true
    · rw [if_pos h, if_pos h]
    · rw [Bool.not_eq_true] at h
      rw [decAnsW_agree f g s _ h]
  | 2, mm =>
    obtain ⟨o, T⟩ := s
    cases o with
    | some c => rw [ettStep_challenge_some, ettStep_challenge_some]
    | none => rw [ettStep_challenge_none, ettStep_challenge_none]

/-- **The flag is sticky:** from a flagged state every successor is flagged,
`s.2 = true → (ettBad … rej b i x s).AllOutputs fun ys => ys.2.2 = true`. -/
theorem ettBad_stick (rej : Bool) (i : Fin 3) (x : (bitSpec ins outs).dom i) (s : St n d × Bool)
    (hs : s.2 = true) :
    (ettBad ins outs d n f g rej b i x s).AllOutputs fun ys => ys.2.2 = true := by
  rw [ettBad_apply, ettImpl_apply, OracleComp.bind_assoc]
  refine OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun r _ => ?_
  rw [OracleComp.pure_bind]
  exact OracleComp.allOutputs_pure.2 (by rw [hs, Bool.true_or])

/-- **The flag is a ghost:** forgetting it, the simulation of `ettBad` is the simulation of
`ettImpl`, from every flag (`simulate_eq_of_abs` with the projection):
`(simulate (ettBad … rej b) c (s, β)).bind (fun p => pure (p.1, p.2.1)) =
simulate (ettImpl … rej b) c s`. -/
theorem simulate_ettBad_fst (rej : Bool) {α : Type} (c : OracleComp (bitSpec ins outs) α)
    (s : St n d) (β : Bool) :
    (simulate (ettBad ins outs d n f g rej b) c (s, β)).bind (fun p => .pure (p.1, p.2.1)) =
      simulate (ettImpl ins outs d n f g rej b) c s := by
  refine (simulate_eq_of_abs (ettImpl ins outs d n f g rej b) (ettBad ins outs d n f g rej b)
    Prod.fst (fun i x s => ?_) c (s, β)).symm
  rw [ettBad_apply, OracleComp.bind_assoc]
  simp only [OracleComp.pure_bind]
  exact (OracleComp.bind_pure _).symm

/-- **Identical until bad** [BR06]: for every event `P` on the output, the probabilities under the
experiments with `rej = false` and `rej = true` differ by at most the probability that the
rejecting experiment raises the flag.

**Proof sketch.** `identical_until_bad` on `ettBad` (`ettBad_agree`, `ettBad_stick`), with the bad
probability moved to `rej = true` (`prob_eq_until_bad`) and the flag forgotten
(`simulate_ettBad_fst`). -/
theorem abs_prob_ettImpl_rej_sub_le {α : Type} (c : OracleComp (bitSpec ins outs) α)
    (P : α → Prop) (s : St n d) :
    |prob (simulate (ettImpl ins outs d n f g false b) c s) (fun p => P p.1) -
        prob (simulate (ettImpl ins outs d n f g true b) c s) (fun p => P p.1)| ≤
      prob (simulate (ettBad ins outs d n f g true b) c (s, false)) (fun p => p.2.2 = true) := by
  classical
  have hfst : ∀ rej : Bool, prob (simulate (ettImpl ins outs d n f g rej b) c s)
      (fun p => P p.1) =
      prob (simulate (ettBad ins outs d n f g rej b) c (s, false)) (fun p => P p.1) := by
    intro rej
    rw [← simulate_ettBad_fst ins outs d n f g b rej c s false, prob_bind]
    simp only [prob_pure]
    rw [prob_eq_expect]
  rw [hfst false, hfst true]
  refine (identical_until_bad (fun st : St n d × Bool => st.2 = true)
    (fun i x st hst G => ettBad_agree ins outs d n f g b i x st hst G)
    (fun i x st hst => ettBad_stick ins outs d n f g b false i x st hst)
    (fun i x st hst => ettBad_stick ins outs d n f g b true i x st hst) c P
    (s := (s, false)) Bool.false_ne_true).trans (le_of_eq ?_)
  exact (prob_eq_until_bad (fun st : St n d × Bool => st.2 = true)
    (fun i x st hst G => ettBad_agree ins outs d n f g b i x st hst G)
    (fun i x st hst => ettBad_stick ins outs d n f g b false i x st hst)
    (fun i x st hst => ettBad_stick ins outs d n f g b true i x st hst) c P
    (s := (s, false)) Bool.false_ne_true).2

end Agree

/-! ### The bad probability with a random tag function -/

section Bound

variable {d n : ℕ}

/-- **The invariant of the revealed pairs** for a table `M` and a state `s`: every key of `M` is a
listed pair or the challenge's pair; every listed pair is a key; and the recorded challenge is the
word `⟨r, ⟨c₁, y⟩⟩` of a nonce, an `n`-bit mask and the table's value `y` at their pair: with
`keys M = M.map Prod.fst`,
`RevInv M s ↔ (∀ p ∈ keys M, p ∈ s.2 ∨ ∃ c, s.1 = some c ∧ p = pairW n ⟦c⟧) ∧
(∀ p ∈ s.2, p ∈ keys M) ∧ (∀ c, s.1 = some c → ∃ r c₁ y, ⟦c⟧ = ctW ⟦r⟧ c₁ ⟦y⟧ ∧ |c₁| = n ∧
pairV n ⟦r⟧ c₁ ∈ keys M ∧ ∀ R, ovr M R (pairV n ⟦r⟧ c₁) = y)`. -/
def RevInv (M : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))) (s : St n d) : Prop :=
  (∀ p ∈ M.map Prod.fst, p ∈ s.2 ∨ ∃ c, s.1 = some c ∧ p = pairW n (List.ofFn c)) ∧
  (∀ p ∈ s.2, p ∈ M.map Prod.fst) ∧
  (∀ c, s.1 = some c → ∃ (r : Fin n → Bool) (c₁ : List Bool) (y : Fin (2 * n) → Bool),
    List.ofFn c = ctW (List.ofFn r) c₁ (List.ofFn y) ∧ c₁.length = n ∧
    pairV n (List.ofFn r) c₁ ∈ M.map Prod.fst ∧ ∀ R, ovr M R (pairV n (List.ofFn r) c₁) = y)

/-- `RevInv M s` unfolded, with `keys M = M.map Prod.fst`:
`RevInv M s ↔ (∀ p ∈ keys M, p ∈ s.2 ∨ ∃ c, s.1 = some c ∧ p = pairW n ⟦c⟧) ∧
(∀ p ∈ s.2, p ∈ keys M) ∧ (∀ c, s.1 = some c → ∃ r c₁ y, ⟦c⟧ = ctW ⟦r⟧ c₁ ⟦y⟧ ∧ |c₁| = n ∧
pairV n ⟦r⟧ c₁ ∈ keys M ∧ ∀ R, ovr M R (pairV n ⟦r⟧ c₁) = y)`. -/
theorem revInv_iff (M : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))) (s : St n d) :
    RevInv M s ↔
      (∀ p ∈ M.map Prod.fst, p ∈ s.2 ∨ ∃ c, s.1 = some c ∧ p = pairW n (List.ofFn c)) ∧
      (∀ p ∈ s.2, p ∈ M.map Prod.fst) ∧
      (∀ c, s.1 = some c → ∃ (r : Fin n → Bool) (c₁ : List Bool) (y : Fin (2 * n) → Bool),
        List.ofFn c = ctW (List.ofFn r) c₁ (List.ofFn y) ∧ c₁.length = n ∧
        pairV n (List.ofFn r) c₁ ∈ M.map Prod.fst ∧
        ∀ R, ovr M R (pairV n (List.ofFn r) c₁) = y) :=
  Iff.rfl

/-- The empty table and the initial state satisfy the invariant: `RevInv [] (none, [])`, since its
clauses quantify over `p ∈ []`, over `p ∈ []` and over `none = some c`. -/
theorem revInv_nil : RevInv (d := d) (n := n) [] (none, []) :=
  ⟨fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => by cases h⟩

/-- An encryption at a pair already in the table keeps the invariant. -/
private theorem revInv_enc_old {M : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))}
    {s : St n d} (h : RevInv M s) {p : Fin (2 * n) → Bool} (hp : p ∈ M.map Prod.fst) :
    RevInv M (s.1, p :: s.2) := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨fun p' hp' => ?_, fun p' hp' => ?_, h₃⟩
  · rcases h₁ p' hp' with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · exact Or.inr h
  · rcases List.mem_cons.1 hp' with rfl | h
    · exact hp
    · exact h₂ p' h

/-- An encryption at a new pair `p` with the value `t` keeps the invariant of the extended table.

**Proof sketch.** Clause by clause. A key of `(p, t) :: M` is `p`, now listed, or a key of `M`,
listed or the challenge's pair as before. A listed pair of `p :: s.2` is `p`, now a key, or a key
of `M`. The challenge's witnesses `r, c₁, y` are kept: their pair is still a key, and it differs
from the new `p ∉ keys M`, so `ovr ((p, t) :: M) R` still gives `y` there (`ovr_cons`,
`Function.update_of_ne`). -/
private theorem revInv_enc_new {M : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))}
    {s : St n d} (h : RevInv M s) {p : Fin (2 * n) → Bool} (hp : p ∉ M.map Prod.fst)
    (t : Fin (2 * n) → Bool) : RevInv ((p, t) :: M) (s.1, p :: s.2) := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨fun p' hp' => ?_, fun p' hp' => ?_, fun c hc => ?_⟩
  · simp only [List.map_cons, List.mem_cons] at hp'
    rcases hp' with rfl | hp'
    · exact Or.inl (List.mem_cons_self ..)
    · rcases h₁ p' hp' with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h
  · simp only [List.map_cons, List.mem_cons]
    rcases List.mem_cons.1 hp' with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (h₂ p' h)
  · obtain ⟨r, c₁, y, hw, hl, hk, hy⟩ := h₃ c hc
    have hne : pairV n (List.ofFn r) c₁ ≠ p := fun h => hp (h ▸ hk)
    refine ⟨r, c₁, y, hw, hl, ?_, fun R => ?_⟩
    · simp only [List.map_cons, List.mem_cons]
      exact Or.inr hk
    · rw [ovr_cons, Function.update_of_ne hne, hy]

/-- Recording a challenge whose pair is already in the table keeps the invariant. -/
private theorem revInv_chal_old {M : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))}
    {T : List (Fin (2 * n) → Bool)} (h : RevInv (d := d) M (none, T)) (r : Fin n → Bool)
    {c₁ : List Bool}
    (hl : c₁.length = n) (hk : pairV n (List.ofFn r) c₁ ∈ M.map Prod.fst)
    (y : Fin (2 * n) → Bool) (hy : ∀ R, ovr M R (pairV n (List.ofFn r) c₁) = y) (c : Fin d → Bool)
    (hc : List.ofFn c = ctW (List.ofFn r) c₁ (List.ofFn y)) : RevInv M (some c, T) := by
  obtain ⟨h₁, h₂, -⟩ := h
  refine ⟨fun p hp => ?_, h₂, fun c' hc' => ?_⟩
  · rcases h₁ p hp with h | ⟨c'', hc'', -⟩
    · exact Or.inl h
    · cases hc''
  · cases hc'
    exact ⟨r, c₁, y, hc, hl, hk, hy⟩

/-- Recording a challenge at a new pair with the value `t` keeps the invariant of the extended
table.

**Proof sketch.** Clause by clause. The new key `pairV n ⟦r⟧ c₁` is the pair of the recorded `c`
(`pairW_eq`, `wR_ctW`, `wC_ctW` on `⟦c⟧ = ctW ⟦r⟧ c₁ ⟦t⟧`); the old keys are listed, since the
state had no record. The list is unchanged and its pairs are still keys. The record's witnesses
are `r, c₁, t`: the new key is a key, and `ovr` of the extended table gives `t` there (`ovr_cons`,
`Function.update_self`). -/
private theorem revInv_chal_new {M : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))}
    {T : List (Fin (2 * n) → Bool)} (h : RevInv (d := d) M (none, T)) (r : Fin n → Bool)
    {c₁ : List Bool}
    (hl : c₁.length = n) (t : Fin (2 * n) → Bool) (c : Fin d → Bool)
    (hc : List.ofFn c = ctW (List.ofFn r) c₁ (List.ofFn t)) :
    RevInv ((pairV n (List.ofFn r) c₁, t) :: M) (some c, T) := by
  obtain ⟨h₁, h₂, -⟩ := h
  refine ⟨fun p hp' => ?_, fun p hp' => ?_, fun c' hc' => ?_⟩
  · simp only [List.map_cons, List.mem_cons] at hp'
    rcases hp' with rfl | hp'
    · refine Or.inr ⟨c, rfl, ?_⟩
      rw [pairW_eq, hc, wR_ctW, wC_ctW]
    · rcases h₁ p hp' with h | ⟨c'', hc'', -⟩
      · exact Or.inl h
      · cases hc''
  · simp only [List.map_cons, List.mem_cons]
    exact Or.inr (h₂ p hp')
  · cases hc'
    refine ⟨r, c₁, t, hc, hl, ?_, fun R => ?_⟩
    · simp only [List.map_cons, List.mem_cons, true_or]
    · rw [ovr_cons, Function.update_self]

/-- The tag of a word read through the pair:
`validW g w = (wfW n w && decide (wT w = ⟦g (pairW n w)⟧))`. -/
private theorem validW_pairW (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (w : List Bool) :
    validW g w = (wfW n w && decide (wT w = List.ofFn (g (pairW n w)))) := by
  rw [validW_eq, tagL_eq, pairW_eq]

/-- **A fresh guess hits the random tag with probability at most `2^{-2n}`:** under the
invariant, `𝔼_R [hitW (ovr M R) s w] ≤ 2^{-2n}` for `n > 0`.

**Proof sketch.** A hit needs a pair outside the list. A key of the table outside the list is the
challenge's pair; there a valid word has the challenge's fields (`eq_of_pairV_eq`), so it is the
challenge (`eq_ctW_of_wfW`) and is refused. Outside the keys the tag is `R` at the pair
(`ovr_of_not_mem`), uniform (`expect_sample_coord`, `expect_sample_mem_le`). -/
private theorem expect_hitW_le (hn : 0 < n) {M : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))}
    {s : St n d} (hM : RevInv M s) (w : List Bool) :
    expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)))
        (fun R => if hitW (ovr M R) s w = true then (1 : ℝ) else 0) ≤ ((2 : ℝ) ^ (2 * n))⁻¹ := by
  have hδ : (0 : ℝ) ≤ ((2 : ℝ) ^ (2 * n))⁻¹ := by positivity
  by_cases hk : pairW n w ∈ M.map Prod.fst
  · -- a key: the list or the challenge, and then no hit
    have h0 : ∀ R, hitW (ovr M R) s w = false := by
      intro R
      rw [hitW_eq]
      obtain ⟨h₁, -, h₃⟩ := hM
      rcases h₁ _ hk with hl | ⟨c, hc, hp⟩
      · simp [hl]
      · obtain ⟨r, c₁, y, hw, hl, -, hy⟩ := h₃ c hc
        by_cases hv : validW (ovr M R) w = true
        · have hv' := hv
          rw [validW_pairW, Bool.and_eq_true, decide_eq_true_eq] at hv'
          obtain ⟨hwf, ht⟩ := hv'
          have hwf' := hwf
          rw [wfW_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hwf'
          have hpc : pairW n (List.ofFn c) = pairV n (List.ofFn r) c₁ := by
            rw [pairW_eq, hw, wR_ctW, wC_ctW]
          rw [hp, hpc, hy] at ht
          rw [pairW_eq, hpc] at hp
          obtain ⟨hr, hcc⟩ := eq_of_pairV_eq hwf'.1 hwf'.2 List.length_ofFn hl hp
          have hweq : w = List.ofFn c := by
            rw [hw, eq_ctW_of_wfW hn hwf, hr, hcc, ht]
          rw [hc, refW_some, hweq]
          simp
        · rw [Bool.not_eq_true] at hv
          simp [hv]
    simp only [h0, Bool.false_eq_true, if_false, expect_const]
    exact hδ
  · -- not a key: the tag is `R` at the pair
    have hle : ∀ R, (if hitW (ovr M R) s w = true then (1 : ℝ) else 0) ≤
        if R (pairW n w) ∈ [padFin (2 * n) (wT w)] then 1 else 0 := by
      intro R
      by_cases h : hitW (ovr M R) s w = true
      · rw [if_pos h]
        rw [hitW_eq, Bool.and_eq_true, Bool.and_eq_true, validW_pairW, Bool.and_eq_true,
          decide_eq_true_eq, ovr_of_not_mem hk] at h
        rw [if_pos (by rw [List.mem_singleton, h.1.2.2, padFin_ofFn])]
      · rw [if_neg h]
        split <;> norm_num
    refine (expect_mono _ hle).trans ?_
    rw [expect_sample_coord (pairW n w) (fun t (_ : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) =>
      if t ∈ [padFin (2 * n) (wT w)] then (1 : ℝ) else 0) (fun _ _ _ => rfl)]
    simp only [expect_const]
    refine (expect_sample_mem_le _).trans (le_of_eq ?_)
    rw [List.length_singleton, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    push_cast
    rw [one_div]

end Bound

section Induction

variable (ins outs : Fin 3 → ℕ) (d n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)) (b : Bool)

/-- From a flagged state the simulation ends flagged: its bad probability is `1`. -/
private theorem prob_bad_of_flag (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) {α : Type}
    (c : OracleComp (bitSpec ins outs) α) (s : St n d) :
    prob (simulate (ettBad ins outs d n f g true b) c (s, true)) (fun p => p.2.2 = true) = 1 :=
  prob_eq_one_of_allOutputs (simulate_allOutputs_bad (fun st : St n d × Bool => st.2 = true)
    (fun i x st hst => ettBad_stick ins outs d n f g b true i x st hst) c rfl)

/-- One query of the flagged simulation: draw the nonce, take the step, raise the flag by
`hitQ`, continue. -/
private theorem prob_simulate_ettBad_query (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))
    {α : Type} (i : Fin 3) (x : (bitSpec ins outs).dom i)
    (k : (bitSpec ins outs).rng i → OracleComp (bitSpec ins outs) α) (s : St n d) :
    prob (simulate (ettBad ins outs d n f g true b) (.query i x k) (s, false))
        (fun p => p.2.2 = true) =
      expect (sample (Fin n → Bool)) fun r =>
        prob (simulate (ettBad ins outs d n f g true b)
          (k (ettStep ins outs d n f g true b r i x s).1)
          ((ettStep ins outs d n f g true b r i x s).2, hitQ ins d n g i x s))
          (fun p => p.2.2 = true) := by
  rw [simulate_query, prob_bind, ettBad_apply, ettImpl_apply, OracleComp.bind_assoc, expect_bind]
  simp only [OracleComp.pure_bind, expect_pure, Bool.false_or]

/-- **The bad probability with a random tag function** [PS10, Thm 170.4, proof]: for `n > 0`,
`(6n + 4)`-bit records and `2n`-bit challenge queries, from a state and a table with the invariant
`RevInv`, a computation making at most `m` queries raises the flag of the rejecting experiment
with probability at most `m / 2^{2n}`, averaged over `R` with the table written over it:
`𝔼_R Pr[bad | simulate (ettBad … (ovr M R) true b) c (s, false)] ≤ m · 2^{-2n}`.

**Proof sketch.** Induction on `c`. An encryption, or a first challenge, at a pair already in the
table reads the table only; at a new pair it reads `R` there, which `expect_sample_ovr` moves into
the table (the invariant follows, `revInv_enc_new`, `revInv_chal_new`). A decryption answer of the
rejecting experiment reads the tag function only at listed pairs, which are keys, so it does not
depend on `R`; it raises the flag with probability at most `2^{-2n}` (`expect_hitW_le`), and the
union bound adds it to the continuation's bound. A repeated challenge reads nothing. -/
theorem expect_prob_bad_le (hn : 0 < n) (hd : d = 6 * n + 4) (hi2 : ins 2 = n + n) {α : Type}
    (c : OracleComp (bitSpec ins outs) α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m)
    (M : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))) (s : St n d) (hM : RevInv M s) :
    expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)))
        (fun R => prob (simulate (ettBad ins outs d n f (ovr M R) true b) c (s, false))
          (fun p => p.2.2 = true)) ≤ m * ((2 : ℝ) ^ (2 * n))⁻¹ := by
  have hδ : (0 : ℝ) ≤ ((2 : ℝ) ^ (2 * n))⁻¹ := by positivity
  induction c generalizing m M s with
  | pure a =>
    simp only [simulate_pure, prob_pure, Bool.false_eq_true, if_false, expect_const]
    positivity
  | query i x k ih =>
    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
    have hm1 : 1 ≤ m := hm
    have IH : ∀ y (M' : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))) (s' : St n d),
        RevInv M' s' →
        expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)))
          (fun R => prob (simulate (ettBad ins outs d n f (ovr M' R) true b) (k y) (s', false))
            (fun p => p.2.2 = true)) ≤ ((m - 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (2 * n))⁻¹ :=
      fun y M' s' h => ih y (m - 1) (hk y) M' s' h
    have hm' : ((m - 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (2 * n))⁻¹ + ((2 : ℝ) ^ (2 * n))⁻¹ =
        (m : ℝ) * ((2 : ℝ) ^ (2 * n))⁻¹ := by
      rw [Nat.cast_sub hm1]
      ring
    have hle : ((m - 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (2 * n))⁻¹ ≤ (m : ℝ) * ((2 : ℝ) ^ (2 * n))⁻¹ := by
      linarith
    simp only [prob_simulate_ettBad_query]
    -- a step that reads the tag function at the pair `p` of a fresh nonce
    have fresh : ∀ (p : (Fin n → Bool) → Fin (2 * n) → Bool)
        (Y : (Fin n → Bool) → (Fin (2 * n) → Bool) → (bitSpec ins outs).rng i)
        (S : (Fin n → Bool) → (Fin (2 * n) → Bool) → St n d),
        (∀ r, p r ∈ M.map Prod.fst → ∀ t, (∀ R, ovr M R (p r) = t) → RevInv M (S r t)) →
        (∀ r, p r ∉ M.map Prod.fst → ∀ t, RevInv ((p r, t) :: M) (S r t)) →
        expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))) (fun R =>
          expect (sample (Fin n → Bool)) fun r =>
            prob (simulate (ettBad ins outs d n f (ovr M R) true b)
              (k (Y r (ovr M R (p r)))) (S r (ovr M R (p r)), false))
              (fun q => q.2.2 = true)) ≤ (m : ℝ) * ((2 : ℝ) ^ (2 * n))⁻¹ := by
      intro p Y S hold hnew
      rw [expect_sample_comm]
      refine (expect_mono _ fun r => ?_).trans ((le_of_eq (expect_const _ _)).trans hle)
      by_cases hp : p r ∈ M.map Prod.fst
      · have hc : ∀ R, ovr M R (p r) = ovr M (fun _ => p r) (p r) :=
          fun R => ovr_of_mem hp R _
        simp only [hc]
        exact IH _ M _ (hold r hp _ hc)
      · have e : ∀ R, ovr M R (p r) = R (p r) := fun R => ovr_of_not_mem hp R
        simp only [e]
        rw [expect_sample_ovr M hp (fun t g => prob (simulate (ettBad ins outs d n f g true b)
            (k (Y r t)) (S r t, false)) (fun q => q.2.2 = true))]
        refine (expect_mono _ fun t => IH _ _ _ (hnew r hp t)).trans (le_of_eq ?_)
        exact expect_const _ _
    match i, x, k, ih, IH, fresh with
    | 0, x, k, ih, IH, fresh =>
      simp only [ettStep_enc, hitQ_zero, encW_eq_ctW]
      exact fresh (fun r => pairV n (List.ofFn r) (maskL f r (List.ofFn x)))
        (fun r t => padFin _ (ctW (List.ofFn r) (maskL f r (List.ofFn x)) (List.ofFn t)))
        (fun r _ => (s.1, pairV n (List.ofFn r) (maskL f r (List.ofFn x)) :: s.2))
        (fun r hp _ _ => revInv_enc_old hM hp) (fun r hp t => revInv_enc_new hM hp t)
    | 1, w, k, ih, IH, fresh =>
      simp only [ettStep_dec, hitQ_one, expect_const]
      -- the answer does not read `R`
      have hans : ∀ R, decAnsW f (ovr M R) true s (List.ofFn w) =
          decAnsW f (ovr M (fun _ => pairW n (List.ofFn w))) true s (List.ofFn w) := by
        intro R
        rw [decAnsW_eq, decAnsW_eq]
        by_cases hl : pairW n (List.ofFn w) ∈ s.2
        · have hkey := hM.2.1 _ hl
          rw [validW_pairW, validW_pairW, ovr_of_mem hkey R]
        · simp [hl]
      simp only [hans]
      have hsplit : ∀ R, prob (simulate (ettBad ins outs d n f (ovr M R) true b)
          (k (padFin _ (decAnsW f (ovr M (fun _ => pairW n (List.ofFn w))) true s (List.ofFn w))))
          (s, hitW (ovr M R) s (List.ofFn w))) (fun q => q.2.2 = true) ≤
          (if hitW (ovr M R) s (List.ofFn w) = true then (1 : ℝ) else 0) +
            prob (simulate (ettBad ins outs d n f (ovr M R) true b)
              (k (padFin _ (decAnsW f (ovr M (fun _ => pairW n (List.ofFn w))) true s
                (List.ofFn w)))) (s, false)) (fun q => q.2.2 = true) := by
        intro R
        by_cases h : hitW (ovr M R) s (List.ofFn w) = true
        · rw [h, prob_bad_of_flag, if_pos rfl]
          linarith [prob_nonneg (simulate (ettBad ins outs d n f (ovr M R) true b)
            (k (padFin _ (decAnsW f (ovr M (fun _ => pairW n (List.ofFn w))) true s
              (List.ofFn w)))) (s, false)) (fun q => q.2.2 = true)]
        · rw [Bool.not_eq_true] at h
          rw [h]
          simp
      refine (expect_mono _ hsplit).trans ?_
      rw [expect_add]
      have h1 := expect_hitW_le hn hM (List.ofFn w)
      have h2 := IH (padFin _ (decAnsW f (ovr M (fun _ => pairW n (List.ofFn w))) true s
        (List.ofFn w))) M s hM
      linarith
    | 2, mm, k, ih, IH, fresh =>
      obtain ⟨o, T⟩ := s
      cases o with
      | some c =>
        simp only [ettStep_challenge_some, hitQ_two, expect_const]
        exact (IH _ M _ hM).trans hle
      | none =>
        have hmsg : (AdaptiveCPA.msgOf n b (List.ofFn mm)).length = n := by
          have : (List.ofFn mm).length = n + n := by rw [List.length_ofFn, hi2]
          rw [AdaptiveCPA.msgOf_eq]
          cases b <;> simp [this]
        have hl : ∀ r : Fin n → Bool,
            (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))).length = n :=
          fun r => length_maskL f r hmsg
        have hrec : ∀ (r : Fin n → Bool) (t : Fin (2 * n) → Bool),
            List.ofFn (padFin d (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b
              (List.ofFn mm))) (List.ofFn t))) =
            ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))) (List.ofFn t) := by
          intro r t
          refine ofFn_padFin_of_length ?_
          rw [ctW_eq, length_pairEncode, length_pairEncode, List.length_ofFn, hl r,
            List.length_ofFn, hd]
          omega
        simp only [ettStep_challenge_none, hitQ_two, encW_eq_ctW]
        exact fresh (fun r => pairV n (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b
            (List.ofFn mm))))
          (fun r t => padFin _ (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b
            (List.ofFn mm))) (List.ofFn t)))
          (fun r t => (some (padFin d (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b
            (List.ofFn mm))) (List.ofFn t))), T))
          (fun r hp t ht => revInv_chal_old hM r (hl r) hp t ht _ (hrec r t))
          (fun r _ t => revInv_chal_new hM r (hl r) t _ (hrec r t))

/-- Expectations of functions within a pointwise bound of each other:
`(∀ x, |f x - g x| ≤ h x) → |𝔼 f - 𝔼 g| ≤ 𝔼 h`. -/
private theorem abs_expect_sub_le_expect {β : Type} (c : ProbComp β) {f g h : β → ℝ}
    (hb : ∀ x, |f x - g x| ≤ h x) : |expect c f - expect c g| ≤ expect c h := by
  rw [← expect_sub, abs_le]
  constructor
  · have := expect_mono c fun x => (neg_le_of_abs_le (hb x))
    rw [show (fun x => -h x) = fun x => (-1) * h x from funext fun x => by ring,
      expect_const_mul] at this
    linarith
  · exact expect_mono c fun x => le_of_abs_le (hb x)

/-- **Step 2 of [PS10, Thm 170.4]: fresh decryption queries are rejected.** For `n > 0`,
`(6n + 4)`-bit records and `2n`-bit challenge queries, and a machine adversary `A` with budget `Q`,
the acceptance probabilities in the experiments with and without the rejection of fresh pairs,
averaged over a uniform random tag function `R`, differ by at most `Q / 2^{2n}`.

**Proof sketch.** For each of `A`'s coins and each `R`, identical until bad
(`abs_prob_ettImpl_rej_sub_le`); average over `R` (`abs_expect_sub_le_expect`) and bound the bad
probability from the empty table (`expect_prob_bad_le`, `revInv_nil`, `ovr_nil`); average over the
coins (`abs_expect_sub_le`). -/
theorem abs_ettAcc_rej_sub_le (hn : 0 < n) (hd : d = 6 * n + 4) (hi2 : ins 2 = n + n)
    (A : NUPPT) (Q : ℕ) :
    |expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)))
          (fun R => ettAcc ins outs d n f R false b A Q) -
        expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)))
          (fun R => ettAcc ins outs d n f R true b A Q)| ≤ Q * ((2 : ℝ) ^ (2 * n))⁻¹ := by
  classical
  simp only [ettAcc_eq]
  rw [expect_sample_comm (α := (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (β := A.Coins n),
    expect_sample_comm (α := (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (β := A.Coins n)]
  refine abs_expect_sub_le _ fun r => ?_
  refine (abs_expect_sub_le_expect (h := fun R => prob (simulate (ettBad ins outs d n f R true b)
      (A.toComp (bitCodec ins outs 1) n Q r) ((none, []), false)) (fun p => p.2.2 = true)) _
      fun R => ?_).trans ?_
  · have h := abs_prob_ettImpl_rej_sub_le ins outs d n f R b (A.toComp (bitCodec ins outs 1) n Q r)
      (fun a => (List.ofFn a).headD false = true) (none, [])
    rw [prob_eq_expect, prob_eq_expect] at h
    exact h
  · have h := expect_prob_bad_le ins outs d n f b hn hd hi2 (A.toComp (bitCodec ins outs 1) n Q r)
      Q (A.toComp_costBoundedBy _ n Q r) [] (none, []) revInv_nil
    simp only [ovr_nil] at h
    exact h

end Induction

end TCSlib.Cryptography.Composability.ETTGame

## ===== TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Games.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Tools
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler
import TCSlib.Cryptography.Foundations.BitLists

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The CCA2 games of the encrypt-then-tag scheme with a pad and a tag function

The scheme of [PS10, Algorithm 169.3] encrypts `m` as `⟨r, ⟨c₁, t⟩⟩` with a fresh `n`-bit nonce
`r`, the mask `c₁ = m ⊕ f(r)` and the tag `t = g(r ‖ c₁)`, where `f = f_{k₁}` and `g = f_{k₂}` are
the keyed functions at parameters `n` and `2n`. The proof of [PS10, Theorem 170.4] replaces them by
other functions; this file states the CCA2 experiment's oracles with `f` and `g` arbitrary, on
bit-string oracles of arbitrary lengths (`bitSpec ins outs`; oracle `0` is `Enc`, `1` is `Dec`,
`2` is `Challenge`), with the challenge recorded at width `d`.

**The state** (`St n d`) is the recorded challenge and the list of pairs `r ‖ c₁` of the earlier
`Enc` answers. **Every query draws one nonce** `r`, used by `Enc` and by a first challenge only
(`ettImpl`); the answer is then a deterministic function of the nonce (`ettStep`).

* `Enc` on `m` answers `⟨r, ⟨c₁, g(r ‖ c₁)⟩⟩` and adds the pair `r ‖ c₁` to the list.
* `Dec` on `w` refuses the recorded challenge; otherwise it parses `w = ⟨r, ⟨c₁, t⟩⟩` with the total
  projections (`wR`, `wC`, `wT`), and answers `⟨1, c₁ ⊕ f(r)⟩` when `r` and `c₁` have `n` bits and
  `t = g(r ‖ c₁)` (`validW`), else `⊥`. With `rej = true` it also rejects a pair that is not in
  the list (**fresh pairs are rejected**).
* `Challenge` on `⟨m₀, m₁⟩` encrypts `m_b` once and records it; later it repeats the record.

The bad flag of the comparison between `rej = false` and `rej = true` (`ettBad`) records a `Dec`
query that is not refused, has a valid tag and a fresh pair (`hitW`). The nonces drawn in advance
from tapes give `ettTape`, the experiment run by the PRF reduction.

## Main definitions

* `ETTGame.encW`, `wR`, `wC`, `wT`, `validW`, `decL`, `pairW`: ciphertext words.
* `ETTGame.St`, `ettStep`, `ettImpl`, `ettBad`, `ettTape`: the experiments.
* `ETTGame.ettAcc`: a machine's acceptance probability in the experiment.

## Main results

* `ETTGame.ettStep_enc`, `_dec`, `_challenge_some`, `_challenge_none`: the answers.
* `ETTGame.encW_eq_ctW`: an encryption reads the tag function at its pair only.
* `ETTGame.length_encW`, `ETTGame.eq_ctW_of_wfW`: ciphertext lengths and canonical parsing.
* `ETTGame.expect_ettTape`: nonces in advance have the law of fresh nonces.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Algorithm 169.3 and Theorem 170.4 (book pp. 169–171).
-/

namespace TCSlib.Cryptography.Composability.ETTGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

/-! ### Ciphertext words -/

section Words

variable {n : ℕ}

/-- The pair `r ‖ c₁` read as a `2n`-bit vector: `pairV n r c = padFin (2n) (r ++ c)`. -/
def pairV (n : ℕ) (r c : List Bool) : Fin (2 * n) → Bool := padFin (2 * n) (r ++ c)

/-- `pairV n r c = padFin (2n) (r ++ c)`. -/
theorem pairV_eq (n : ℕ) (r c : List Bool) : pairV n r c = padFin (2 * n) (r ++ c) := rfl

/-- The tag `⟦g (r ‖ c₁)⟧`: `tagL g r c = ⟦g (pairV n r c)⟧`. -/
def tagL (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (r c : List Bool) : List Bool :=
  List.ofFn (g (pairV n r c))

/-- `tagL g r c = ⟦g (pairV n r c)⟧`. -/
theorem tagL_eq (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (r c : List Bool) :
    tagL g r c = List.ofFn (g (pairV n r c)) := rfl

/-- The ciphertext word `⟨r, ⟨c₁, t⟩⟩`: `ctW r c t = pairEncode r (pairEncode c t)`. -/
def ctW (r c t : List Bool) : List Bool := pairEncode r (pairEncode c t)

/-- `ctW r c t = ⟨r, ⟨c, t⟩⟩`. -/
theorem ctW_eq (r c t : List Bool) : ctW r c t = pairEncode r (pairEncode c t) := rfl

/-- The mask `c₁ = m ⊕ ⟦f r⟧`. -/
def maskL (f : (Fin n → Bool) → (Fin n → Bool)) (r : Fin n → Bool) (m : List Bool) : List Bool :=
  List.zipWith xor m (List.ofFn (f r))

/-- `maskL f r m = m ⊕ ⟦f r⟧`. -/
theorem maskL_eq (f : (Fin n → Bool) → (Fin n → Bool)) (r : Fin n → Bool) (m : List Bool) :
    maskL f r m = List.zipWith xor m (List.ofFn (f r)) := rfl

/-- **The encryption** of the message list `m` with the nonce `r`:
`⟨r, ⟨c₁, ⟦g (r ‖ c₁)⟧⟩⟩` with `c₁ = maskL f r m`. -/
def encW (f : (Fin n → Bool) → (Fin n → Bool)) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))
    (r : Fin n → Bool) (m : List Bool) : List Bool :=
  ctW (List.ofFn r) (maskL f r m) (tagL g (List.ofFn r) (maskL f r m))

/-- `encW f g r m = ctW ⟦r⟧ c₁ (tagL g ⟦r⟧ c₁)` with `c₁ = maskL f r m`. -/
theorem encW_eq (f : (Fin n → Bool) → (Fin n → Bool))
    (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (r : Fin n → Bool) (m : List Bool) :
    encW f g r m = ctW (List.ofFn r) (maskL f r m) (tagL g (List.ofFn r) (maskL f r m)) := rfl

/-- **An encryption reads the tag function at its pair only:**
`encW f g r m = ctW ⟦r⟧ c₁ ⟦g (pairV n ⟦r⟧ c₁)⟧` with `c₁ = maskL f r m`. -/
theorem encW_eq_ctW (f : (Fin n → Bool) → (Fin n → Bool))
    (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (r : Fin n → Bool) (m : List Bool) :
    encW f g r m = ctW (List.ofFn r) (maskL f r m)
      (List.ofFn (g (pairV n (List.ofFn r) (maskL f r m)))) := by
  rw [encW_eq, tagL_eq]

/-- The nonce field of a word: `wR w = pairFstD w`. -/
def wR (w : List Bool) : List Bool := pairFstD w

/-- The mask field of a word: `wC w = pairFstD (pairSndD w)`. -/
def wC (w : List Bool) : List Bool := pairFstD (pairSndD w)

/-- The tag field of a word: `wT w = pairSndD (pairSndD w)`. -/
def wT (w : List Bool) : List Bool := pairSndD (pairSndD w)

/-- `wR w = pairFstD w`. -/
theorem wR_eq (w : List Bool) : wR w = pairFstD w := rfl

/-- `wC w = pairFstD (pairSndD w)`. -/
theorem wC_eq (w : List Bool) : wC w = pairFstD (pairSndD w) := rfl

/-- `wT w = pairSndD (pairSndD w)`. -/
theorem wT_eq (w : List Bool) : wT w = pairSndD (pairSndD w) := rfl

/-- The fields of a ciphertext word: `wR (ctW r c t) = r`. -/
theorem wR_ctW (r c t : List Bool) : wR (ctW r c t) = r := by
  rw [wR_eq, ctW_eq, pairFstD_pairEncode]

/-- The fields of a ciphertext word: `wC (ctW r c t) = c`. -/
theorem wC_ctW (r c t : List Bool) : wC (ctW r c t) = c := by
  rw [wC_eq, ctW_eq, pairSndD_pairEncode, pairFstD_pairEncode]

/-- The fields of a ciphertext word: `wT (ctW r c t) = t`. -/
theorem wT_ctW (r c t : List Bool) : wT (ctW r c t) = t := by
  rw [wT_eq, ctW_eq, pairSndD_pairEncode, pairSndD_pairEncode]

/-- **Well-formedness:** the nonce and the mask fields have `n` bits,
`wfW n w = (|wR w| = n && |wC w| = n)`. -/
def wfW (n : ℕ) (w : List Bool) : Bool :=
  decide ((wR w).length = n) && decide ((wC w).length = n)

/-- `wfW n w = (decide (|wR w| = n) && decide (|wC w| = n))`. -/
theorem wfW_eq (n : ℕ) (w : List Bool) :
    wfW n w = (decide ((wR w).length = n) && decide ((wC w).length = n)) := rfl

/-- **A valid word:** well formed, with the tag `wT w = tagL g (wR w) (wC w)`. -/
def validW (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (w : List Bool) : Bool :=
  wfW n w && decide (wT w = tagL g (wR w) (wC w))

/-- `validW g w = (wfW n w && decide (wT w = tagL g (wR w) (wC w)))`. -/
theorem validW_eq (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (w : List Bool) :
    validW g w = (wfW n w && decide (wT w = tagL g (wR w) (wC w))) := rfl

/-- **The decryption** of a word, `⟨1, wC w ⊕ ⟦f (wR w)⟧⟩`:
`decL f w = true :: (wC w ⊕ ⟦f (padFin n (wR w))⟧)`. -/
def decL (f : (Fin n → Bool) → (Fin n → Bool)) (w : List Bool) : List Bool :=
  true :: List.zipWith xor (wC w) (List.ofFn (f (padFin n (wR w))))

/-- `decL f w = true :: (wC w ⊕ ⟦f (padFin n (wR w))⟧)`. -/
theorem decL_eq (f : (Fin n → Bool) → (Fin n → Bool)) (w : List Bool) :
    decL f w = true :: List.zipWith xor (wC w) (List.ofFn (f (padFin n (wR w)))) := rfl

/-- The pair of a word, as a `2n`-bit vector: `pairW n w = pairV n (wR w) (wC w)`. -/
def pairW (n : ℕ) (w : List Bool) : Fin (2 * n) → Bool := pairV n (wR w) (wC w)

/-- `pairW n w = pairV n (wR w) (wC w)`. -/
theorem pairW_eq (n : ℕ) (w : List Bool) : pairW n w = pairV n (wR w) (wC w) := rfl

/-- The mask of an `n`-bit message has `n` bits: `|m| = n → |maskL f r m| = n`. -/
theorem length_maskL (f : (Fin n → Bool) → (Fin n → Bool)) (r : Fin n → Bool) {m : List Bool}
    (hm : m.length = n) : (maskL f r m).length = n := by
  rw [maskL_eq, List.length_zipWith, List.length_ofFn, hm, Nat.min_self]

/-- **The ciphertext length:** an encryption of an `n`-bit message has `6n + 4` bits:
`|m| = n → |encW f g r m| = 6n + 4`. -/
theorem length_encW (f : (Fin n → Bool) → (Fin n → Bool))
    (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (r : Fin n → Bool) {m : List Bool}
    (hm : m.length = n) : (encW f g r m).length = 6 * n + 4 := by
  rw [encW_eq, ctW_eq, length_pairEncode, length_pairEncode, List.length_ofFn,
    length_maskL f r hm, tagL_eq, List.length_ofFn]
  omega

/-- **Canonical parsing:** for `n > 0`, a well-formed word is the ciphertext word of its fields,
`w = ctW (wR w) (wC w) (wT w)` (`eq_pairEncode_of_pairFstD_ne`, the nonempty fields). -/
theorem eq_ctW_of_wfW {w : List Bool} (hn : 0 < n) (hw : wfW n w = true) :
    w = ctW (wR w) (wC w) (wT w) := by
  rw [wfW_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hw
  have h₁ : pairFstD w ≠ [] := by
    intro h
    have := hw.1
    rw [wR_eq, h, List.length_nil] at this
    omega
  have h₂ : pairFstD (pairSndD w) ≠ [] := by
    intro h
    have := hw.2
    rw [wC_eq, h, List.length_nil] at this
    omega
  rw [ctW_eq, wR_eq, wC_eq, wT_eq, ← eq_pairEncode_of_pairFstD_ne h₂]
  exact eq_pairEncode_of_pairFstD_ne h₁

/-- An encryption of an `n`-bit message is well formed:
`|m| = n → wfW n (encW f g r m) = true`. -/
theorem wfW_encW (f : (Fin n → Bool) → (Fin n → Bool))
    (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (r : Fin n → Bool) {m : List Bool}
    (hm : m.length = n) : wfW n (encW f g r m) = true := by
  rw [wfW_eq, encW_eq, wR_ctW, wC_ctW, List.length_ofFn, length_maskL f r hm]
  simp

/-- **Pairs of `n`-bit fields determine the fields:** if `|r| = |c| = |r'| = |c'| = n` and
`pairV n r c = pairV n r' c'`, then `r = r'` and `c = c'`. -/
theorem eq_of_pairV_eq {r c r' c' : List Bool} (hr : r.length = n) (hc : c.length = n)
    (hr' : r'.length = n) (hc' : c'.length = n) (h : pairV n r c = pairV n r' c') :
    r = r' ∧ c = c' := by
  have h1 : r ++ c = r' ++ c' := by
    have e : List.ofFn (pairV n r c) = List.ofFn (pairV n r' c') := by rw [h]
    rw [pairV_eq, pairV_eq, ofFn_padFin_of_length (by rw [List.length_append, hr, hc]; omega),
      ofFn_padFin_of_length (by rw [List.length_append, hr', hc']; omega)] at e
    exact e
  exact List.append_inj h1 (hr.trans hr'.symm)

end Words

/-! ### The state and the decryption answer -/

section State

variable {n d : ℕ}

/-- **The state of the experiment:** the recorded challenge and the pairs of the `Enc` answers,
`St n d = Option (Fin d → Bool) × List (Fin (2n) → Bool)`. -/
abbrev St (n d : ℕ) : Type := Option (Fin d → Bool) × List (Fin (2 * n) → Bool)

/-- `St n d = Option (Fin d → Bool) × List (Fin (2n) → Bool)`. -/
theorem St_eq (n d : ℕ) : St n d = (Option (Fin d → Bool) × List (Fin (2 * n) → Bool)) := rfl

/-- **The refusal test:** the word `w` is the recorded challenge,
`refW (some c) w = (⟦c⟧ = w)`, `refW none w = false`. -/
def refW (o : Option (Fin d → Bool)) (w : List Bool) : Bool :=
  match o with
  | some c => decide (List.ofFn c = w)
  | none => false

/-- `refW none w = false`. -/
theorem refW_none (w : List Bool) : refW (none : Option (Fin d → Bool)) w = false := rfl

/-- `refW (some c) w = decide (⟦c⟧ = w)`. -/
theorem refW_some (c : Fin d → Bool) (w : List Bool) : refW (some c) w = decide (List.ofFn c = w) :=
  rfl

/-- **The decryption answer** in state `s`, with fresh pairs rejected when `rej` holds:
`decAnsW f g rej s w = if !refW s.1 w && validW g w && (!rej || pairW n w ∈ s.2) then decL f w
else []`, that is, `decL f w` if `w` is not refused, valid, and (when `rej`) its pair is in the
list; else `[]` (read as `⊥`). -/
def decAnsW (f : (Fin n → Bool) → (Fin n → Bool)) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))
    (rej : Bool) (s : St n d) (w : List Bool) : List Bool :=
  if (!refW s.1 w && validW g w && (!rej || decide (pairW n w ∈ s.2))) = true then decL f w else []

/-- `decAnsW f g rej s w = if !refW s.1 w && validW g w && (!rej || pairW n w ∈ s.2) then decL f w
else []`. -/
theorem decAnsW_eq (f : (Fin n → Bool) → (Fin n → Bool))
    (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (rej : Bool) (s : St n d) (w : List Bool) :
    decAnsW f g rej s w =
      if (!refW s.1 w && validW g w && (!rej || decide (pairW n w ∈ s.2))) = true then decL f w
      else [] := rfl

/-- **The bad event of a decryption query:** not refused, valid, and a fresh pair,
`hitW g s w = (!refW s.1 w && validW g w && !decide (pairW n w ∈ s.2))`. -/
def hitW (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (s : St n d) (w : List Bool) : Bool :=
  !refW s.1 w && validW g w && !decide (pairW n w ∈ s.2)

/-- `hitW g s w = (!refW s.1 w && validW g w && !decide (pairW n w ∈ s.2))`. -/
theorem hitW_eq (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (s : St n d) (w : List Bool) :
    hitW g s w = (!refW s.1 w && validW g w && !decide (pairW n w ∈ s.2)) := rfl

/-- **Off the bad event the two decryption answers agree:** `hitW g s w = false →
decAnsW f g false s w = decAnsW f g true s w`. -/
theorem decAnsW_agree (f : (Fin n → Bool) → (Fin n → Bool))
    (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (s : St n d) (w : List Bool)
    (h : hitW g s w = false) : decAnsW f g false s w = decAnsW f g true s w := by
  rw [decAnsW_eq, decAnsW_eq]
  rw [hitW_eq] at h
  cases hr : refW s.1 w <;> cases hv : validW g w <;>
    cases hm : decide (pairW n w ∈ s.2) <;> simp_all

end State

/-! ### The experiments -/

section Experiments

variable (ins outs : Fin 3 → ℕ) (d n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool))
  (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (rej b : Bool)

/-- **One step of the experiment with the nonce `r`** (see the module docstring), with inputs read
by `⟦·⟧` and answers and records written by `padFin`:
`ettStep … r 0 m s = (encW f g r m, (s.1, pairV n ⟦r⟧ (maskL f r m) :: s.2))`,
`ettStep … r 1 w s = (decAnsW f g rej s w, s)`,
`ettStep … r 2 mm (some c, T) = (⟦c⟧, (some c, T))` and
`ettStep … r 2 mm (none, T) = (e, (some e, T))` with `e = encW f g r (msgOf n b mm)`. -/
def ettStep (r : Fin n → Bool) :
    ∀ i : Fin 3, (Fin (ins i) → Bool) → St n d → (Fin (outs i) → Bool) × St n d
  | 0, m, s => (padFin _ (encW f g r (List.ofFn m)),
      (s.1, pairV n (List.ofFn r) (maskL f r (List.ofFn m)) :: s.2))
  | 1, w, s => (padFin _ (decAnsW f g rej s (List.ofFn w)), s)
  | 2, _, (some c, T) => (padFin _ (List.ofFn c), (some c, T))
  | 2, mm, (none, T) => (padFin _ (encW f g r (AdaptiveCPA.msgOf n b (List.ofFn mm))),
      (some (padFin d (encW f g r (AdaptiveCPA.msgOf n b (List.ofFn mm)))), T))

/-- `Enc` on `m` answers `encW f g r m` and adds the pair `r ‖ maskL f r m` to the list:
`ettStep … r 0 m s = (padFin _ (encW f g r ⟦m⟧), (s.1, pairV n ⟦r⟧ (maskL f r ⟦m⟧) :: s.2))`. -/
theorem ettStep_enc (r : Fin n → Bool) (m : Fin (ins 0) → Bool) (s : St n d) :
    ettStep ins outs d n f g rej b r 0 m s =
      (padFin _ (encW f g r (List.ofFn m)),
        (s.1, pairV n (List.ofFn r) (maskL f r (List.ofFn m)) :: s.2)) := rfl

/-- `Dec` on `w` answers `decAnsW f g rej s w` and keeps the state:
`ettStep … r 1 w s = (padFin _ (decAnsW f g rej s ⟦w⟧), s)`. -/
theorem ettStep_dec (r : Fin n → Bool) (w : Fin (ins 1) → Bool) (s : St n d) :
    ettStep ins outs d n f g rej b r 1 w s = (padFin _ (decAnsW f g rej s (List.ofFn w)), s) := rfl

/-- A later challenge repeats the record and keeps the state:
`ettStep … r 2 mm (some c, T) = (padFin _ ⟦c⟧, (some c, T))`. -/
theorem ettStep_challenge_some (r : Fin n → Bool) (mm : Fin (ins 2) → Bool) (c : Fin d → Bool)
    (T : List (Fin (2 * n) → Bool)) :
    ettStep ins outs d n f g rej b r 2 mm (some c, T) = (padFin _ (List.ofFn c), (some c, T)) := rfl

/-- The first challenge encrypts `m_b` with the nonce `r` and records it:
`ettStep … r 2 mm (none, T) = (padFin _ e, (some (padFin d e), T))` with
`e = encW f g r (msgOf n b ⟦mm⟧)`. -/
theorem ettStep_challenge_none (r : Fin n → Bool) (mm : Fin (ins 2) → Bool)
    (T : List (Fin (2 * n) → Bool)) :
    ettStep ins outs d n f g rej b r 2 mm (none, T) =
      (padFin _ (encW f g r (AdaptiveCPA.msgOf n b (List.ofFn mm))),
        (some (padFin d (encW f g r (AdaptiveCPA.msgOf n b (List.ofFn mm)))), T)) := rfl

/-- **The experiment with pad function `f` and tag function `g`:** every query draws a nonce `r`
and takes one `ettStep`,
`ettImpl … i x s = (sample (Fin n → Bool)).bind fun r => pure (ettStep … r i x s)`. -/
noncomputable def ettImpl : QueryImpl (bitSpec ins outs) (St n d) unifSpec :=
  fun i x s => (sample (Fin n → Bool)).bind fun r => .pure (ettStep ins outs d n f g rej b r i x s)

/-- `ettImpl … i x s = (sample (Fin n → Bool)).bind fun r => pure (ettStep … r i x s)`. -/
theorem ettImpl_apply (i : Fin 3) (x : Fin (ins i) → Bool) (s : St n d) :
    ettImpl ins outs d n f g rej b i x s =
      (sample (Fin n → Bool)).bind fun r => .pure (ettStep ins outs d n f g rej b r i x s) := rfl

/-- The experiment draws one coin per query (`freshImpl`):
`ettImpl … = freshImpl fun i x s r => pure (ettStep … r i x s)`. -/
theorem ettImpl_eq_freshImpl :
    ettImpl ins outs d n f g rej b =
      freshImpl fun i x s r => .pure (ettStep ins outs d n f g rej b r i x s) := by
  funext i x s
  rw [ettImpl_apply, freshImpl_apply]

/-- The bad event of a query: a decryption query with `hitW`, `hitQ … 1 w s = hitW g s ⟦w⟧`,
and `hitQ … 0 m s = hitQ … 2 mm s = false`. -/
def hitQ : ∀ i : Fin 3, (Fin (ins i) → Bool) → St n d → Bool
  | 0, _, _ => false
  | 1, w, s => hitW g s (List.ofFn w)
  | 2, _, _ => false

/-- An encryption query never raises the bad flag: `hitQ … 0 m s = false`. -/
theorem hitQ_zero (m : Fin (ins 0) → Bool) (s : St n d) : hitQ ins d n g 0 m s = false := rfl

/-- A decryption query raises the bad flag by `hitW`: `hitQ … 1 w s = hitW g s ⟦w⟧`. -/
theorem hitQ_one (w : Fin (ins 1) → Bool) (s : St n d) :
    hitQ ins d n g 1 w s = hitW g s (List.ofFn w) := rfl

/-- A challenge query never raises the bad flag: `hitQ … 2 mm s = false`. -/
theorem hitQ_two (mm : Fin (ins 2) → Bool) (s : St n d) : hitQ ins d n g 2 mm s = false := rfl

/-- **The experiment with the bad flag:** `ettImpl`, and the flag raised by `hitQ`,
`ettBad … i x s = (ettImpl … i x s.1).bind fun p =>
pure (p.1, (p.2, s.2 || hitQ … i x s.1))`. -/
noncomputable def ettBad : QueryImpl (bitSpec ins outs) (St n d × Bool) unifSpec :=
  fun i x s => (ettImpl ins outs d n f g rej b i x s.1).bind fun p =>
    .pure (p.1, (p.2, s.2 || hitQ ins d n g i x s.1))

/-- `ettBad … i x s =
(ettImpl … i x s.1).bind fun p => pure (p.1, (p.2, s.2 || hitQ … i x s.1))`. -/
theorem ettBad_apply (i : Fin 3) (x : Fin (ins i) → Bool) (s : St n d × Bool) :
    ettBad ins outs d n f g rej b i x s =
      (ettImpl ins outs d n f g rej b i x s.1).bind fun p =>
        .pure (p.1, (p.2, s.2 || hitQ ins d n g i x s.1)) := rfl

/-- **The experiment with nonces in advance** (`rej = false`): the `j`-th query uses the nonce
`T j` (`tapeImpl`). -/
def ettTape (T : ℕ → Fin n → Bool) : QueryImpl (bitSpec ins outs) (St n d × ℕ) unifSpec :=
  tapeImpl (fun i x s r => .pure (ettStep ins outs d n f g false b r i x s)) T

/-- `ettTape … T i x (s, j) = pure (ettStep … false b (T j) i x s)` with the counter advanced. -/
theorem ettTape_apply (T : ℕ → Fin n → Bool) (i : Fin 3) (x : Fin (ins i) → Bool) (s : St n d)
    (j : ℕ) :
    ettTape ins outs d n f g b T i x (s, j) =
      .pure ((ettStep ins outs d n f g false b (T j) i x s).1,
        ((ettStep ins outs d n f g false b (T j) i x s).2, j + 1)) := by
  rw [ettTape, tapeImpl_apply, OracleComp.pure_bind]

/-- **Nonces in advance have the law of fresh nonces:** for a computation with at most `m`
queries and `j + m ≤ κ`,
`𝔼_{T ← ({0,1}^n)^κ} 𝔼[G (simulate (ettTape (extTape T)) c (s, j))] =
𝔼[G (simulate (ettImpl … false b) c s)]` (`expect_simulate_tapeImpl`). -/
theorem expect_ettTape (κ : ℕ) {α : Type} (G : α → ℝ) (c : OracleComp (bitSpec ins outs) α)
    (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : St n d) (j : ℕ) (hj : j + m ≤ κ) :
    expect (sample (Fin κ → Fin n → Bool))
        (fun T => expect (simulate (ettTape ins outs d n f g b (AdaptiveCPA.extTape T)) c (s, j))
          fun p => G p.1) =
      expect (simulate (ettImpl ins outs d n f g false b) c s) fun p => G p.1 := by
  rw [ettImpl_eq_freshImpl]
  exact expect_simulate_tapeImpl _ κ G c m hc s j hj

/-- **The experiment along equal lengths:** for `ins = ins'`, `outs = outs'` and `d = d'`, the
expected first output bit of a machine's run against `ettImpl` agrees. -/
theorem expect_ettImpl_transport {ins ins' outs outs' : Fin 3 → ℕ} {d d' : ℕ} (hi : ins = ins')
    (ho : outs = outs') (hd : d = d') (A : NUPPT) (Q : ℕ) (r : A.Coins n) :
    expect (simulate (ettImpl ins outs d n f g rej b) (A.toComp (bitCodec ins outs 1) n Q r)
        (none, [])) (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) =
      expect (simulate (ettImpl ins' outs' d' n f g rej b) (A.toComp (bitCodec ins' outs' 1) n Q r)
        (none, [])) (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
  subst hi ho hd
  rfl

/-- **The acceptance probability of a machine** in the experiment with `f` and `g`, averaged over
its coins: `𝔼_r 𝔼[⟦A's output⟧₀ = 1 | simulate (ettImpl … f g rej b) (A.toComp … r) (none, [])]`. -/
noncomputable def ettAcc (A : NUPPT) (Q : ℕ) : ℝ :=
  expect (sample (A.Coins n)) fun r =>
    expect (simulate (ettImpl ins outs d n f g rej b) (A.toComp (bitCodec ins outs 1) n Q r)
      (none, [])) (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0)

/-- `ettAcc … A Q = 𝔼_r 𝔼[⟦output⟧₀ = 1 | simulate (ettImpl …) (A.toComp … r) (none, [])]`. -/
theorem ettAcc_eq (A : NUPPT) (Q : ℕ) :
    ettAcc ins outs d n f g rej b A Q =
      expect (sample (A.Coins n)) fun r =>
        expect (simulate (ettImpl ins outs d n f g rej b) (A.toComp (bitCodec ins outs 1) n Q r)
          (none, [])) (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) :=
  rfl

/-- The acceptance probability lies in `[0, 1]`; the lower bound: `0 ≤ ettAcc … A Q`. -/
theorem ettAcc_nonneg (A : NUPPT) (Q : ℕ) : 0 ≤ ettAcc ins outs d n f g rej b A Q := by
  rw [ettAcc_eq]
  refine expect_nonneg _ fun r => expect_nonneg _ fun p => ?_
  split <;> norm_num

/-- The acceptance probability lies in `[0, 1]`; the upper bound: `ettAcc … A Q ≤ 1`. -/
theorem ettAcc_le_one (A : NUPPT) (Q : ℕ) : ettAcc ins outs d n f g rej b A Q ≤ 1 := by
  rw [ettAcc_eq]
  refine (expect_mono _ fun r => ?_).trans (le_of_eq (expect_const _ 1))
  refine (expect_mono _ fun p => ?_).trans (le_of_eq (expect_const _ 1))
  split <;> norm_num

end Experiments

end TCSlib.Cryptography.Composability.ETTGame

## ===== TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Handler.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Games
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
import TCSlib.Cryptography.Asymptotic.OneWayLemmas
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Reduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The handler of the tag-key PRF reduction

Step 1 of [PS10, Theorem 170.4] replaces the tag function `f_{k₂}` by a random function: a
reduction with oracle access to a function `g` on `2n` bits samples `k₁` itself, runs the CCA2
adversary and answers its queries with `g` in place of `f_{k₂}`. This file builds that reduction as
a `Games.InteractiveHandler` (`dHandler`) with one outer oracle (the function), so that T2
(`Games.exists_interactiveHandlerMachine`) and T4 (`Games.exists_toOracleAdversary_of_bitCodec`)
make it a next-query machine.

The handler's seed is the key `k₁` followed by `q(n)` nonce tapes of `n` bits (`dSeed`); its state
counts the queries and records the challenge (`dState`). The mask `c₁ = m ⊕ f_{k₁}(r)` is computed
with the evaluator `E`.
- `Enc` on `m`: with the next tape `r`, ask `g` at `r ‖ c₁` and answer `⟨r, ⟨c₁, g(r ‖ c₁)⟩⟩`.
- `Dec` on `w`: refuse the recorded challenge; if `w = ⟨r, ⟨c₁, t⟩⟩` has `n`-bit `r` and `c₁`, ask
  `g` at `r ‖ c₁` and answer `⟨1, c₁ ⊕ f_{k₁}(r)⟩` if the answer is `t`; otherwise answer `⊥`.
- `Challenge` on `⟨m₀, m₁⟩`: the first time, encrypt `m_b` as `Enc` does and record it; later
  repeat the record.
Every query advances the counter. The finalization asks nothing and outputs the adversary's bit.

## Main definitions

* `ETTGame.ettCt`, `ettDin`, `ettDout`, `tagLen`, `tagOut`, `dStLen`, `dSeedLen`: the lengths.
* `ETTGame.recBits`, `dState`, `dSeed`: the encoded state and seed.
* `ETTGame.dHandler E hE q b`: the handler.

## Main results

* `ETTGame.dHandler_impl_enc`, `_impl_dec_ref`, `_impl_dec_wf`, `_impl_dec_nwf`,
  `_impl_challenge_some`, `_impl_challenge_none`: its answers on encoded states.
* `ETTGame.dHandler_finish`, `dHandler_init_hstate`: the finalization and the initial state.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Algorithm 169.3 and Theorem 170.4 (book pp. 169–171).
-/

namespace TCSlib.Cryptography.Composability.ETTGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Games.InteractiveHandler (rU rW rS rI rX rL rCnt rAns)

/-! ### Lengths -/

/-- The ciphertext length `6n + 4`: `ettCt = 6 · var + 4`, so `ettCt.eval n = 6n + 4`. -/
def ettCt : PolyExpr := .add (.mul (.const 6) .var) (.const 4)

/-- `ettCt.eval n = 6n + 4`. -/
theorem ettCt_eval (n : ℕ) : ettCt.eval n = 6 * n + 4 := by
  rw [ettCt, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_const,
    PolyExpr.eval_var]

/-- The query lengths: `n`-bit messages to `Enc`, `(6n + 4)`-bit ciphertexts to `Dec`, `2n`-bit
challenge queries: `ettDin 0 = var`, `ettDin 1 = ettCt` and `ettDin 2 = var + var`. -/
def ettDin : Fin 3 → PolyExpr
  | 0 => .var
  | 1 => ettCt
  | 2 => .add .var .var

/-- `ettDin 0 = var`. -/
theorem ettDin_zero : ettDin 0 = .var := rfl

/-- `ettDin 1 = ettCt`. -/
theorem ettDin_one : ettDin 1 = ettCt := rfl

/-- `ettDin 2 = var + var`. -/
theorem ettDin_two : ettDin 2 = .add .var .var := rfl

/-- The answer lengths: ciphertexts, `(n + 1)`-bit decryption answers, ciphertexts:
`ettDout 0 = ettCt`, `ettDout 1 = var + 1` and `ettDout 2 = ettCt`. -/
def ettDout : Fin 3 → PolyExpr
  | 0 => ettCt
  | 1 => .add .var (.const 1)
  | 2 => ettCt

/-- `ettDout 0 = ettCt`. -/
theorem ettDout_zero : ettDout 0 = ettCt := rfl

/-- `ettDout 1 = var + 1`. -/
theorem ettDout_one : ettDout 1 = .add .var (.const 1) := rfl

/-- `ettDout 2 = ettCt`. -/
theorem ettDout_two : ettDout 2 = ettCt := rfl

/-- The tag length `2n`: `tagLen = 2 · var`, so `tagLen.eval n = 2n`. -/
def tagLen : PolyExpr := .mul (.const 2) .var

/-- `tagLen.eval n = 2n`. -/
theorem tagLen_eval (n : ℕ) : tagLen.eval n = 2 * n := by
  rw [tagLen, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]

/-- The outer oracle: `2n`-bit queries and answers, `tagOut j = tagLen` for `j : Fin 1`. -/
abbrev tagOut : Fin 1 → PolyExpr := fun _ => tagLen

/-- `tagOut j = tagLen`. -/
theorem tagOut_eq (j : Fin 1) : tagOut j = tagLen := rfl

variable (q : PolyExpr)

/-- The state length `2q + 3 + (6n + 4)`: `dStLen q = 2 · q + 3 + ettCt`, so
`(dStLen q).eval n = 2 q(n) + 3 + (6n + 4)`. -/
def dStLen : PolyExpr := .add (.add (.mul (.const 2) q) (.const 3)) ettCt

/-- `dStLen q = 2q + 3 + ettCt`. -/
theorem dStLen_eq : dStLen q = .add (.add (.mul (.const 2) q) (.const 3)) ettCt := rfl

/-- The seed length `n + q(n) · n`: the key and the tapes, `dSeedLen q = var + q · var`, so
`(dSeedLen q).eval n = n + q(n) · n`. -/
def dSeedLen : PolyExpr := .add .var (.mul q .var)

/-- `(dSeedLen q).eval n = n + q(n) · n`. -/
theorem dSeedLen_eval (n : ℕ) : (dSeedLen q).eval n = n + q.eval n * n := by
  rw [dSeedLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_var]

/-- The record of the challenge: `1 :: c` once recorded, `0^{1 + ct(n)}` before,
`recBits n (some c) = true :: ⟦c⟧` and
`recBits n none = false :: List.replicate (ettCt.eval n) false`. -/
def recBits (n : ℕ) : Option (Fin (ettCt.eval n) → Bool) → List Bool
  | none => false :: List.replicate (ettCt.eval n) false
  | some c => true :: List.ofFn c

/-- `recBits n none = 0^{1 + ct(n)}`. -/
theorem recBits_none (n : ℕ) : recBits n none = false :: List.replicate (ettCt.eval n) false :=
  rfl

/-- `recBits n (some c) = 1 :: ⟦c⟧`. -/
theorem recBits_some (n : ℕ) (c : Fin (ettCt.eval n) → Bool) :
    recBits n (some c) = true :: List.ofFn c := rfl

/-- The record has `1 + ct(n)` bits: `|recBits n o| = ettCt.eval n + 1`. -/
theorem length_recBits (n : ℕ) (o : Option (Fin (ettCt.eval n) → Bool)) :
    (recBits n o).length = ettCt.eval n + 1 := by
  cases o with
  | none => rw [recBits_none, List.length_cons, List.length_replicate]
  | some c => rw [recBits_some, List.length_cons, List.length_ofFn]

/-- **The encoded state** after `j` queries, with the challenge record `o`:
`⟨1^j, recBits o⟩`, padded with `false` to the state length,
`dState q n j o = padFin _ (pairEncode (List.replicate j true) (recBits n o))`. -/
def dState (n j : ℕ) (o : Option (Fin (ettCt.eval n) → Bool)) :
    Fin ((dStLen q).eval n) → Bool :=
  padFin _ (pairEncode (List.replicate j true) (recBits n o))

/-- `dState q n j o = padFin _ ⟨1^j, recBits n o⟩`. -/
theorem dState_eq (n j : ℕ) (o : Option (Fin (ettCt.eval n) → Bool)) :
    dState q n j o = padFin _ (pairEncode (List.replicate j true) (recBits n o)) := rfl

/-- **The seed** from the key `k₁` and the tape word: `⟦dSeed q n (k, W)⟧ = ⟦k⟧ ++ ⟦W⟧`. -/
def dSeed (n : ℕ) :
    (Fin n → Bool) × (Fin (q.eval n * n) → Bool) ≃ (Fin ((dSeedLen q).eval n) → Bool) :=
  EnsembleLemmas.coinsEquiv (dSeedLen_eval q n)

/-- `dSeed q n = coinsEquiv (dSeedLen_eval q n)`. -/
theorem dSeed_eq (n : ℕ) : dSeed q n = EnsembleLemmas.coinsEquiv (dSeedLen_eval q n) := rfl

/-- `⟦dSeed q n (k, W)⟧ = ⟦k⟧ ++ ⟦W⟧`. -/
theorem ofFn_dSeed (n : ℕ) (kW : (Fin n → Bool) × (Fin (q.eval n * n) → Bool)) :
    List.ofFn (dSeed q n kW) = List.ofFn kW.1 ++ List.ofFn kW.2 :=
  EnsembleLemmas.ofFn_coinsEquiv _ _

/-- The tape `j` of the tape word: block `j` of `W` (`EnsembleLemmas.blocks`),
`dTape q n W j hj = blocks (q n) n W ⟨j, hj⟩`. -/
def dTape (n : ℕ) (W : Fin (q.eval n * n) → Bool) (j : ℕ) (hj : j < q.eval n) : Fin n → Bool :=
  EnsembleLemmas.blocks (q.eval n) n W ⟨j, hj⟩

/-- `dTape q n W j hj = blocks (q n) n W ⟨j, hj⟩`. -/
theorem dTape_eq (n : ℕ) (W : Fin (q.eval n * n) → Bool) (j : ℕ) (hj : j < q.eval n) :
    dTape q n W j hj = EnsembleLemmas.blocks (q.eval n) n W ⟨j, hj⟩ := rfl

/-! ### Strings -/

/-- The fields of an encoded state with `j ≤ q(n)`: the count `1^j`, the flag and the record.

**Proof sketch.** The pair `⟨1^j, recBits n o⟩` fits in the state length (`length_pairEncode`,
`length_recBits`, `j ≤ q(n)`), so the padding only appends `false`s to its second component
(`ofFn_padFin_of_le`, `pairEncode_append_right`). The projections then read `1^j` and
`recBits n o` followed by `false`s; its head is the flag and its next `ct(n)` bits are the record
(by cases on `o`, `recBits_none`, `recBits_some`). -/
private theorem fields_dState (n j : ℕ) (o : Option (Fin (ettCt.eval n) → Bool))
    (hj : j ≤ q.eval n) :
    pairFstD (List.ofFn (dState q n j o)) = List.replicate j true ∧
      (pairSndD (List.ofFn (dState q n j o))).headD false = o.isSome ∧
      ((pairSndD (List.ofFn (dState q n j o))).drop 1).take (ettCt.eval n) =
        (recBits n o).drop 1 := by
  have hlen : (pairEncode (List.replicate j true) (recBits n o)).length ≤ (dStLen q).eval n := by
    rw [length_pairEncode, List.length_replicate, length_recBits, dStLen_eq, PolyExpr.eval_add,
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_const]
    omega
  rw [dState_eq, Collection.ofFn_padFin_of_le hlen, ← GGMRed.pairEncode_append_right]
  rw [pairFstD_pairEncode, pairSndD_pairEncode]
  refine ⟨rfl, ?_, ?_⟩
  · cases o <;> rfl
  · cases o with
    | none =>
      rw [recBits_none, List.cons_append, List.drop_succ_cons, List.drop_zero, List.drop_succ_cons,
        List.drop_zero, List.take_left' List.length_replicate]
    | some c =>
      rw [recBits_some, List.cons_append, List.drop_succ_cons, List.drop_zero, List.drop_succ_cons,
        List.drop_zero, List.take_left' List.length_ofFn]

/-! ### The round function -/

/-- The challenge flag of the state. -/
private def rFlag (w : List Bool) : Bool := (pairSndD (rS w)).headD false
/-- The recorded challenge of the state. -/
private def rRec (w : List Bool) : List Bool :=
  ((pairSndD (rS w)).drop 1).take (ettCt.eval (rU w).length)
/-- The key `k₁` of the seed. -/
private def rKey (w : List Bool) : List Bool := (rW w).take (rU w).length
/-- Tape `j` of the seed, `j` the query count. -/
private def rNonce (w : List Bool) : List Bool :=
  ((rW w).drop ((rU w).length + (rCnt w).length * (rU w).length)).take (rU w).length
/-- The mask `m ⊕ E⟨k₁, r⟩` with the tape `r`. -/
private def rMask (E : List Bool → List Bool) (w m : List Bool) : List Bool :=
  List.zipWith xor m (E (pairEncode (rKey w) (rNonce w)))
/-- The ciphertext `⟨r, ⟨c₁, y⟩⟩` with the tape `r` and the outer answer `y`. -/
private def rCt (E : List Bool → List Bool) (w m : List Bool) : List Bool :=
  pairEncode (rNonce w) (pairEncode (rMask E w m) (rAns w))
/-- The selected challenge message `m_b`. -/
private def rMsg (b : Bool) (w : List Bool) : List Bool :=
  if b then (rX w).drop (rU w).length else (rX w).take (rU w).length
/-- Whether the decryption query `⟨r, ⟨c₁, t⟩⟩` has `n`-bit `r` and `c₁`. -/
private def rWF (w : List Bool) : Bool :=
  decide ((pairFstD (rX w)).length = (rU w).length) &&
    decide ((pairFstD (pairSndD (rX w))).length = (rU w).length)
/-- Whether the decryption query is the recorded challenge. -/
private def rRef (w : List Bool) : Bool := rFlag w && decide (rX w = rRec w)
/-- The decryption `⟨1, c₁ ⊕ E⟨k₁, r⟩⟩` of the query. -/
private def rDec (E : List Bool → List Bool) (w : List Bool) : List Bool :=
  true :: List.zipWith xor (pairFstD (pairSndD (rX w))) (E (pairEncode (rKey w) (pairFstD (rX w))))
/-- Whether the outer answer is the tag of the query. -/
private def rOK (w : List Bool) : Bool := decide (rAns w = pairSndD (pairSndD (rX w)))
/-- The all-`false` decryption answer `⊥`. -/
private def rZero (w : List Bool) : List Bool :=
  List.replicate ((PolyExpr.add .var (.const 1)).eval (rU w).length) false
/-- The new state after a query: count `j + 1`, record `t`. -/
private def rNew (w t : List Bool) : List Bool :=
  EnsembleLemmas.padL ((dStLen q).eval (rU w).length) (pairEncode (true :: rCnt w) t)

/-- **One round of the handler** (see the module docstring), for the challenge bit `b`. A first
round of `Enc`, of a first challenge or of a well-formed decryption asks the outer oracle; the
second round, with the answer `y` in the log, returns the answer and the new state. -/
private def dRun (E : List Bool → List Bool) (b : Bool) (w : List Bool) : List Bool :=
  if (rI w).headD false then
    if ((rI w).drop 1).headD false then
      if rFlag w then pairEncode [true] (rRec w ++ rNew q w (true :: rRec w))
      else if decide (rL w = []) then
        pairEncode [false] (pairEncode [] (rNonce w ++ rMask E w (rMsg b w)))
      else pairEncode [true] (rCt E w (rMsg b w) ++ rNew q w (true :: rCt E w (rMsg b w)))
    else
      if rRef w then pairEncode [true] (rZero w ++ rNew q w (rFlag w :: rRec w))
      else if rWF w then
        if decide (rL w = []) then
          pairEncode [false] (pairEncode [] (pairFstD (rX w) ++ pairFstD (pairSndD (rX w))))
        else pairEncode [true]
          ((if rOK w then rDec E w else rZero w) ++ rNew q w (rFlag w :: rRec w))
      else pairEncode [true] (rZero w ++ rNew q w (rFlag w :: rRec w))
  else
    if decide (rL w = []) then pairEncode [false] (pairEncode [] (rNonce w ++ rMask E w (rX w)))
    else pairEncode [true] (rCt E w (rX w) ++ rNew q w (rFlag w :: rRec w))

/-- The round function is polynomial-time.

**Proof sketch.** Pair projections; the key and the tape by `pairTakePoly`, `unaryMulPair` and
`dropPrefixByLength`; the mask and the decryption by the evaluator `E` and `pairXor`; the tests
by `lenEq_poly` and `pairEq`; the padded new state by `padL`; and `polyTimeComputable_ite` for
the cases. -/
private theorem polyTimeComputable_dRun {E : List Bool → List Bool} (hE : PolyTimeComputable E)
    (b : Bool) : PolyTimeComputable (dRun q E b) := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hU : PolyTimeComputable rU := InteractiveHandler.polyTimeComputable_rU
  have hW : PolyTimeComputable rW := InteractiveHandler.polyTimeComputable_rW
  have hS : PolyTimeComputable rS := InteractiveHandler.polyTimeComputable_rS
  have hI : PolyTimeComputable rI := InteractiveHandler.polyTimeComputable_rI
  have hX : PolyTimeComputable rX := InteractiveHandler.polyTimeComputable_rX
  have hL : PolyTimeComputable rL := InteractiveHandler.polyTimeComputable_rL
  have hCnt : PolyTimeComputable rCnt := InteractiveHandler.polyTimeComputable_rCnt
  have hY : PolyTimeComputable rAns := InteractiveHandler.polyTimeComputable_rAns
  have hT : PolyTimeComputable fun w => pairSndD (rS w) := hD.comp hS
  have hFlag : PolyTimeComputable fun w => [rFlag w] := polyTimeComputable_headD.comp hT
  have hRec : PolyTimeComputable rRec :=
    ((polyTimeComputable_pairTakePoly ettCt).comp
      (hU.pairEncode (polyTimeComputable_tail.comp hT))).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]; rfl
  have hKey : PolyTimeComputable rKey :=
    ((polyTimeComputable_pairTakePoly .var).comp (hU.pairEncode hW)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
        PolyExpr.eval_var]; rfl
  have hU1 : PolyTimeComputable fun w => List.replicate (rU w).length true :=
    ((polyTimeComputable_unaryPoly .var).comp hU).congr fun w => by
      simp only [Function.comp_apply, PolyExpr.eval_var]
  have hOff : PolyTimeComputable fun w =>
      List.replicate ((rU w).length + (rCnt w).length * (rU w).length) true :=
    (hU1.append (OneWay.polyTimeComputable_unaryMulPair.comp (hCnt.pairEncode hU))).congr
      fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
          List.replicate_add]
  have hDrop : PolyTimeComputable fun w =>
      (rW w).drop ((rU w).length + (rCnt w).length * (rU w).length) :=
    (polyTimeComputable_dropPrefixByLength.comp (hOff.pairEncode hW)).congr fun w => by
      simp only [Function.comp_apply, PrefixByLength.drop_def, pairFstD_pairEncode,
        pairSndD_pairEncode, List.length_replicate]
  have hNonce : PolyTimeComputable rNonce :=
    ((polyTimeComputable_pairTakePoly .var).comp (hU.pairEncode hDrop)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
        PolyExpr.eval_var]; rfl
  have hXor : ∀ {m p : List Bool → List Bool}, PolyTimeComputable m → PolyTimeComputable p →
      PolyTimeComputable fun w => List.zipWith xor (m w) (p w) := fun hm hp =>
    (polyTimeComputable_pairXor.comp (hm.pairEncode hp)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hMask : ∀ {m : List Bool → List Bool}, PolyTimeComputable m →
      PolyTimeComputable fun w => rMask E w (m w) := fun hm =>
    hXor hm (hE.comp (hKey.pairEncode hNonce))
  have hCt : ∀ {m : List Bool → List Bool}, PolyTimeComputable m →
      PolyTimeComputable fun w => rCt E w (m w) := fun hm =>
    hNonce.pairEncode ((hMask hm).pairEncode hY)
  have hMsg : PolyTimeComputable (rMsg b) :=
    polyTimeComputable_ite (polyTimeComputable_const [b])
      (((polyTimeComputable_pairDropPoly .var).comp (hU.pairEncode hX)).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
          PolyExpr.eval_var])
      (((polyTimeComputable_pairTakePoly .var).comp (hU.pairEncode hX)).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
          PolyExpr.eval_var])
  have hR : PolyTimeComputable fun w => pairFstD (rX w) := hF.comp hX
  have hC : PolyTimeComputable fun w => pairFstD (pairSndD (rX w)) := (hF.comp hD).comp hX
  have hTg : PolyTimeComputable fun w => pairSndD (pairSndD (rX w)) := (hD.comp hD).comp hX
  have hWF : PolyTimeComputable fun w => [rWF w] :=
    polyTimeComputable_and (EffFill.lenEq_poly hR hU) (EffFill.lenEq_poly hC hU)
  have hEq : ∀ {u v : List Bool → List Bool}, PolyTimeComputable u → PolyTimeComputable v →
      PolyTimeComputable fun w => [decide (u w = v w)] := fun hu hv =>
    (polyTimeComputable_pairEq.comp (hu.pairEncode hv)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hRef : PolyTimeComputable fun w => [rRef w] := polyTimeComputable_and hFlag (hEq hX hRec)
  have hOK : PolyTimeComputable fun w => [rOK w] := hEq hY hTg
  have hDec : PolyTimeComputable (rDec E) :=
    (polyTimeComputable_const [true]).append (hXor hC (hE.comp (hKey.pairEncode hR)))
  have hZero : PolyTimeComputable rZero := EnsembleLemmas.polyTimeComputable_zeros _ hU
  have hNew : ∀ {t : List Bool → List Bool}, PolyTimeComputable t →
      PolyTimeComputable fun w => rNew q w (t w) := fun ht =>
    EnsembleLemmas.polyTimeComputable_padL (dStLen q) hU
      (((polyTimeComputable_const [true]).append hCnt).pairEncode ht)
  have hRet : ∀ {f : List Bool → List Bool}, PolyTimeComputable f →
      PolyTimeComputable fun w => pairEncode [true] (f w) := fun hf =>
    (polyTimeComputable_const [true]).pairEncode hf
  have hQry : ∀ {f : List Bool → List Bool}, PolyTimeComputable f →
      PolyTimeComputable fun w => pairEncode [false] (pairEncode [] (f w)) := fun hf =>
    (polyTimeComputable_const [false]).pairEncode ((polyTimeComputable_const []).pairEncode hf)
  have cNil : PolyTimeComputable fun w => [decide (rL w = [])] := polyTimeComputable_isNil.comp hL
  have hKeep : PolyTimeComputable fun w => rFlag w :: rRec w :=
    (hFlag.append hRec).congr fun _ => rfl
  have hTrueRec : PolyTimeComputable fun w => true :: rRec w :=
    (polyTimeComputable_const [true]).append hRec
  have hChal := polyTimeComputable_ite hFlag (hRet (hRec.append (hNew hTrueRec)))
    (polyTimeComputable_ite cNil (hQry (hNonce.append (hMask hMsg)))
      (hRet ((hCt hMsg).append (hNew ((polyTimeComputable_const [true]).append (hCt hMsg))))))
  have hDecR := polyTimeComputable_ite hRef (hRet (hZero.append (hNew hKeep)))
    (polyTimeComputable_ite hWF
      (polyTimeComputable_ite cNil (hQry (hR.append hC))
        (hRet ((polyTimeComputable_ite hOK hDec hZero).append (hNew hKeep))))
      (hRet (hZero.append (hNew hKeep))))
  have hEnc := polyTimeComputable_ite cNil (hQry (hNonce.append (hMask hX)))
    (hRet ((hCt hX).append (hNew hKeep)))
  exact polyTimeComputable_ite (polyTimeComputable_headD.comp hI)
    (polyTimeComputable_ite (polyTimeComputable_headD.comp (polyTimeComputable_tail.comp hI))
      hChal hDecR) hEnc

/-- The finalization's round: output `A`'s bit, `⟨[true], a⟩` on `⟨ctx, ⟨s, ⟨a, L⟩⟩⟩`. -/
private def dFin (w : List Bool) : List Bool :=
  pairEncode [true] (pairFstD (pairSndD (pairSndD w)))

/-- The finalization's round is polynomial-time. -/
private theorem polyTimeComputable_dFin : PolyTimeComputable dFin :=
  (polyTimeComputable_const [true]).pairEncode
    (polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))

/-! ### The handler -/

/-- **The handler of the tag-key PRF reduction** for the evaluator `E`, the budget `q` and the
challenge bit `b`: state `dState j o` (initially `j = 0` and no record), seed `dSeed` (the key and
`q(n)` tapes), one outer call per inner query, the adversary run on the empty input, and the
finalization outputting the adversary's bit. -/
noncomputable def dHandler (E : List Bool → List Bool) (hE : PolyTimeComputable E) (b : Bool) :
    InteractiveHandler 3 ettDin ettDout 1 tagOut tagOut where
  stateLen := dStLen q
  seedLen := dSeedLen q
  perCall := .const 1
  init n := dState q n 0 none
  run := dRun q E b
  poly := polyTimeComputable_dRun q hE b
  advIn _ := []
  advIn_poly := polyTimeComputable_const []
  outLen := .const 1
  finCall := .const 0
  finRun := dFin
  finRun_poly := polyTimeComputable_dFin

attribute [simps (config := { isSimp := false }) stateLen seedLen perCall outLen finCall]
  dHandler

variable (E : List Bool → List Bool) (hE : PolyTimeComputable E) (b : Bool)

/-- The encoded state at the handler's state type: `dHState … n j o = dState q n j o`. -/
def dHState (n j : ℕ) (o : Option (Fin (ettCt.eval n) → Bool)) :
    Fin ((dHandler q E hE b).stateLen.eval n) → Bool :=
  dState q n j o

/-- `dHState q E hE b n j o = dState q n j o`. -/
theorem dHState_eq (n j : ℕ) (o : Option (Fin (ettCt.eval n) → Bool)) :
    dHState q E hE b n j o = dState q n j o := rfl

/-- The seed at the handler's seed type: `dHSeed … n = dSeed q n`. -/
def dHSeed (n : ℕ) :
    (Fin n → Bool) × (Fin (q.eval n * n) → Bool) ≃
      (Fin ((dHandler q E hE b).seedLen.eval n) → Bool) :=
  dSeed q n

/-- `dHSeed q E hE b n = dSeed q n`. -/
theorem dHSeed_eq (n : ℕ) : dHSeed q E hE b n = dSeed q n := rfl

/-- The initial state is the encoded `(0, none)`:
`(dHandler q E hE b).init n = dHState q E hE b n 0 none`. -/
theorem dHandler_init_hstate (n : ℕ) : (dHandler q E hE b).init n = dHState q E hE b n 0 none :=
  rfl

/-- The adversary's input is empty: `(dHandler q E hE b).advInput n z ω = []`. -/
theorem dHandler_advInput (n : ℕ) (z : List Bool)
    (ω : Fin ((dHandler q E hE b).seedLen.eval n) → Bool) :
    (dHandler q E hE b).advInput n z ω = [] := by
  rw [InteractiveHandler.advInput_eq]
  rfl

/-- The finalization outputs the adversary's bit and asks nothing:
`(dHandler q E hE b).finish n z ω s a = pure (padFin _ ⟦a⟧)`. -/
theorem dHandler_finish (n : ℕ) (z : List Bool)
    (ω : Fin ((dHandler q E hE b).seedLen.eval n) → Bool)
    (s : Fin ((dHandler q E hE b).stateLen.eval n) → Bool)
    (a : Fin ((PolyExpr.const 1).eval n) → Bool) :
    (dHandler q E hE b).finish n z ω s a =
      .pure (padFin ((dHandler q E hE b).outLen.eval n) (List.ofFn a)) := by
  rw [InteractiveHandler.finish_eq]
  have h0 : (dHandler q E hE b).finCall.eval n = 0 := by
    rw [dHandler_finCall, PolyExpr.eval_const]
  rw [h0]
  refine buildComp_zero_of_ret ?_
  show decodeBitMove _ _ _ (dFin _) = _
  rw [dFin, InteractiveHandler.finInput_eq, pairSndD_pairEncode, pairSndD_pairEncode,
    pairFstD_pairEncode]
  have hw : List.ofFn (padFin ((dHandler q E hE b).outLen.eval n) (List.ofFn a)) =
      List.ofFn a :=
    ofFn_padFin_of_length (by rw [List.length_ofFn, dHandler_outLen])
  exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).symm.trans
    (decodeBitMove_ret _ _ _ _)

/-! ### Answers of the handler -/

/-- `⟦dHSeed … n (k, W)⟧ = ⟦k⟧ ++ ⟦W⟧`. -/
theorem ofFn_dHSeed (n : ℕ) (kW : (Fin n → Bool) × (Fin (q.eval n * n) → Bool)) :
    List.ofFn (dHSeed q E hE b n kW) = List.ofFn kW.1 ++ List.ofFn kW.2 :=
  ofFn_dSeed q n kW

/-- `⟦dHState … n j o⟧ = ⟦dState q n j o⟧`. -/
theorem ofFn_dHState (n j : ℕ) (o : Option (Fin (ettCt.eval n) → Bool)) :
    List.ofFn (dHState q E hE b n j o) = List.ofFn (dState q n j o) :=
  rfl

section Answers

variable (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
  (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (F n s x))
  (n : ℕ) (z : List Bool) (k : Fin n → Bool) (W : Fin (q.eval n * n) → Bool)

/-- The round input of a call, field by field, on an encoded state with `j < q(n)` and the seed
`dHSeed (k, W)`.

**Proof sketch.** The generic readers of the round input (`rU_input`, `rS_input`, `rI_input`,
`rX_input`, `rL_input`, `rW_input`, `rCnt_input`) give the parameter, state, oracle index, query,
log, seed word `⟦k⟧ ++ ⟦W⟧` (`ofFn_dHSeed`) and count; `fields_dState` gives the count `1^j`, the
flag and the record. The key is then the first `n` bits of the seed word, and the nonce is the
`n` bits after the offset `n + j · n`, which is block `j` of `W` (`take_drop_ofFn_blocks`). -/
private theorem fields_input {i : Fin 3} (x L : List Bool) (j : ℕ)
    (o : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n) :
    let w := InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
      (List.ofFn (dHState q E hE b n j o)) i x L
    rU w = List.replicate n true ∧ rS w = List.ofFn (dHState q E hE b n j o) ∧
      rI w = List.replicate i true ∧ rX w = x ∧ rL w = L ∧ rCnt w = List.replicate j true ∧
      rFlag w = o.isSome ∧ rRec w = (recBits n o).drop 1 ∧ rKey w = List.ofFn k ∧
      rNonce w = List.ofFn (dTape q n W j hj) := by
  obtain ⟨h₁, h₂, h₃⟩ := fields_dState q n j o hj.le
  have hW : rW (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
      (List.ofFn (dHState q E hE b n j o)) i x L) = List.ofFn k ++ List.ofFn W := by
    rw [InteractiveHandler.rW_input, ofFn_dHSeed]
  have hS : rS (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
      (List.ofFn (dHState q E hE b n j o)) i x L) = List.ofFn (dState q n j o) :=
    (InteractiveHandler.rS_input ..).trans (ofFn_dHState q E hE b n j o)
  have hcnt : rCnt (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
      (List.ofFn (dHState q E hE b n j o)) i x L) = List.replicate j true := by
    rw [InteractiveHandler.rCnt_input, ofFn_dHState, h₁]
  have hU := InteractiveHandler.rU_input (k := 3) n z (List.ofFn (dHSeed q E hE b n (k, W)))
    (List.ofFn (dHState q E hE b n j o)) i x L
  refine ⟨hU, InteractiveHandler.rS_input .., InteractiveHandler.rI_input ..,
    InteractiveHandler.rX_input .., InteractiveHandler.rL_input .., hcnt, ?_, ?_, ?_, ?_⟩
  · rw [rFlag, hS, h₂]
  · rw [rRec, hS, hU, List.length_replicate, h₃]
  · rw [rKey, hW, hU, List.length_replicate, List.take_left' List.length_ofFn]
  · rw [rNonce, hW, hU, hcnt, List.length_replicate, List.length_replicate, List.drop_append,
      List.drop_eq_nil_of_le (by rw [List.length_ofFn]; omega), List.nil_append, List.length_ofFn,
      Nat.add_sub_cancel_left, dTape_eq]
    exact EnsembleLemmas.take_drop_ofFn_blocks W j hj

/-- The new state after a query from `dState j o`, with record `t`. -/
private theorem rNew_fields {i : Fin 3} (x L : List Bool) (j : ℕ)
    (o o' : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n) :
    rNew q (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
        (List.ofFn (dHState q E hE b n j o)) i x L) (recBits n o') =
      List.ofFn (dHState q E hE b n (j + 1) o') := by
  obtain ⟨hU, -, -, -, -, hCnt, -, -, -, -⟩ := fields_input q E hE b n z k W (i := i) x L j o hj
  rw [rNew, hU, hCnt, List.length_replicate, ofFn_dHState, dState_eq,
    EnsembleLemmas.ofFn_padFin_eq_padL, List.replicate_succ]

/-- The flag and the record rebuild the record bits: `rFlag :: rRec = recBits o`. -/
private theorem recBits_fields (o : Option (Fin (ettCt.eval n) → Bool)) :
    o.isSome :: (recBits n o).drop 1 = recBits n o := by
  cases o <;> rfl

/-- The outer answer recorded in a one-entry log (any oracle index word `u`). -/
private theorem rY_one (w : List Bool) (u x' y : List Bool)
    (hL : rL w = pairEncode (pairEncode u (pairEncode x' y)) []) : rAns w = y := by
  rw [InteractiveHandler.rAns_eq, hL, pairFstD_pairEncode, pairSndD_pairEncode,
    pairSndD_pairEncode]

/-- A one-entry log is not empty. -/
private theorem log_ne_nil (u x' y : List Bool) :
    decide (pairEncode (pairEncode u (pairEncode x' y)) [] = []) = false :=
  decide_eq_false (pairEncode_ne_nil _ _)

include hFE in
/-- The mask computed with the evaluator: `m ⊕ E⟨⟦k⟧, ⟦r⟧⟩ = maskL (F n k) r m`. -/
private theorem mask_eval (r : Fin n → Bool) (m : List Bool) :
    List.zipWith xor m (E (pairEncode (List.ofFn k) (List.ofFn r))) = maskL (F n k) r m := by
  rw [hFE, maskL_eq]

/-- The outer query word of a pair `r ‖ c₁` with `|r| = |c₁| = n`, read at `2n` bits. -/
private theorem ofFn_padFin_pair {r c : List Bool} (hr : r.length = n) (hc : c.length = n) :
    List.ofFn (padFin ((tagOut 0).eval n) (r ++ c)) = r ++ c :=
  ofFn_padFin_of_length (by rw [List.length_append, hr, hc, tagOut_eq, tagLen_eval]; omega)

/-- The all-`false` decryption answer as a list. -/
private theorem rZero_fields (w : List Bool) (hU : rU w = List.replicate n true) :
    rZero w = List.ofFn (padFin ((ettDout 1).eval n) ([] : List Bool)) := by
  rw [rZero, hU, List.length_replicate, padFin_nil, ofFn_zeroBits, ettDout_one]

/-- The ciphertext of a nonce and an `n`-bit mask with a `2n`-bit tag has `6n + 4` bits. -/
private theorem length_ctW_tag {r c t : List Bool} (hr : r.length = n) (hc : c.length = n)
    (ht : t.length = 2 * n) : (ctW r c t).length = ettCt.eval n := by
  rw [ctW_eq, length_pairEncode, length_pairEncode, hr, hc, ht, ettCt_eval]
  omega

include hFE in
/-- **Encryption with the next tape:** from `dState j o` with `j < q(n)`, the query `m` asks the
outer oracle at `r ‖ c₁` with the tape `r` and `c₁ = maskL f_k r m`; its answer `y` gives the
ciphertext `⟨r, ⟨c₁, y⟩⟩` and the state `dState (j + 1) o`.

**Proof sketch.** Read the round input field by field (`fields_input`); the first round, with an
empty log, asks `r ‖ c₁` (`mask_eval`); the second, with the answer `y` in the log (`rY_one`),
returns `⟨r, ⟨c₁, y⟩⟩` and the state with count `j + 1` (`rNew_fields`);
`InteractiveHandler.impl_of_query` assembles the two rounds. -/
theorem dHandler_impl_enc (x : Fin ((ettDin 0).eval n) → Bool) (j : ℕ)
    (o : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n) :
    (dHandler q E hE b).impl n z (dHSeed q E hE b n (k, W)) 0 x (dHState q E hE b n j o) =
      .query 0 (padFin _ (List.ofFn (dTape q n W j hj) ++
          maskL (F n k) (dTape q n W j hj) (List.ofFn x))) fun y =>
        .pure (padFin _ (ctW (List.ofFn (dTape q n W j hj))
          (maskL (F n k) (dTape q n W j hj) (List.ofFn x)) (List.ofFn y)),
          dHState q E hE b n (j + 1) o) := by
  have hx : (List.ofFn x).length = n := by rw [List.length_ofFn, ettDin_zero, PolyExpr.eval_var]
  have hm := length_maskL (F n k) (dTape q n W j hj) hx
  refine InteractiveHandler.impl_of_query _ n z _ x _ 0 _ _ _
    (by rw [dHandler_perCall, PolyExpr.eval_const]) ?_ ?_
  · show dRun q E b _ = _
    obtain ⟨-, -, hI, hX, hL, -, -, -, hK, hN⟩ :=
      fields_input q E hE b n z k W (i := 0) (List.ofFn x) [] j o hj
    rw [dRun, hI, Fin.val_zero, List.replicate_zero, List.headD_nil, if_neg Bool.false_ne_true,
      hL, if_pos (decide_eq_true rfl), rMask, hK, hN, hX, mask_eval E F hFE n k,
      ofFn_padFin_pair n List.length_ofFn hm]
    rfl
  · intro y
    show dRun q E b _ = _
    simp only [Fin.val_zero, List.replicate_zero]
    obtain ⟨-, -, hI, hX, hL, -, hFlag, hRec, hK, hN⟩ :=
      fields_input q E hE b n z k W (i := 0) (List.ofFn x)
        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((tagOut 0).eval n)
          (List.ofFn (dTape q n W j hj) ++ maskL (F n k) (dTape q n W j hj) (List.ofFn x))))
          (List.ofFn y))) []) j o hj
    have hY := rY_one _ _ _ _ hL
    have hct : List.ofFn (padFin ((ettDout 0).eval n) (ctW (List.ofFn (dTape q n W j hj))
        (maskL (F n k) (dTape q n W j hj) (List.ofFn x)) (List.ofFn y))) =
        ctW (List.ofFn (dTape q n W j hj)) (maskL (F n k) (dTape q n W j hj) (List.ofFn x))
          (List.ofFn y) :=
      ofFn_padFin_of_length (by
        rw [length_ctW_tag n List.length_ofFn hm (by rw [List.length_ofFn, tagOut_eq, tagLen_eval]),
          ettDout_zero])
    rw [dRun, hI, Fin.val_zero, List.replicate_zero, List.headD_nil, if_neg Bool.false_ne_true, hL,
      log_ne_nil,
      if_neg Bool.false_ne_true, hct, rCt, rMask, hK, hN, hX, hY, mask_eval E F hFE n k, hFlag,
      hRec, recBits_fields, rNew_fields q E hE b n z k W (i := 0) _ _ j o o hj, ctW_eq]

/-- **A refused decryption:** from `dState j o` with the query the recorded challenge, the answer
is `⊥` and the state is `dState (j + 1) o`: for `j < q(n)` and `refW o ⟦x⟧ = true`,
`(dHandler …).impl n z (dHSeed … (k, W)) 1 x (dHState … j o) =
pure (padFin _ [], dHState … (j + 1) o)`.

**Proof sketch.** The handler answers in one round (`impl_of_ret`). Reading the round input
(`fields_input`), `href` makes the refusal test true (`rRef`, by cases on `o`: with the record `c`,
`⟦x⟧ = ⟦c⟧`), so `dRun` takes the refusal branch: the answer `rZero = ⊥` (`rZero_fields`) and the
new state with count `j + 1` and the same record bits (`recBits_fields`, `rNew_fields`). -/
theorem dHandler_impl_dec_ref (x : Fin ((ettDin 1).eval n) → Bool) (j : ℕ)
    (o : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n)
    (href : refW o (List.ofFn x) = true) :
    (dHandler q E hE b).impl n z (dHSeed q E hE b n (k, W)) 1 x (dHState q E hE b n j o) =
      .pure (padFin _ [], dHState q E hE b n (j + 1) o) := by
  refine InteractiveHandler.impl_of_ret _ n z _ x _ _ _ ?_
  show dRun q E b _ = _
  obtain ⟨hU, -, hI, hX, -, -, hFlag, hRec, -, -⟩ :=
    fields_input q E hE b n z k W (i := 1) (List.ofFn x) [] j o hj
  have hRef : rRef (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
      (List.ofFn (dHState q E hE b n j o)) (1 : Fin 3) (List.ofFn x) []) = true := by
    rw [rRef, hFlag, hRec, hX]
    cases o with
    | none => rw [refW_none] at href; cases href
    | some c =>
      rw [refW_some, decide_eq_true_eq] at href
      rw [recBits_some, List.drop_succ_cons, List.drop_zero, href]
      simp
  rw [dRun, hI, Fin.val_one, List.replicate_one, List.headD_cons, if_pos rfl, List.drop_succ_cons,
    List.drop_zero, List.headD_nil, if_neg Bool.false_ne_true, hRef, if_pos rfl,
    rZero_fields n _ hU, hFlag, hRec, recBits_fields,
    rNew_fields q E hE b n z k W (i := 1) _ _ j o o hj]

include hFE in
/-- **A well-formed decryption:** from `dState j o` with a query `w = ⟦x⟧` that is not refused and
has `n`-bit `wR w` and `wC w`, the query asks the outer oracle at `wR w ‖ wC w`; its answer `y`
gives `decL f_k w` if `⟦y⟧ = wT w` and `⊥` otherwise; the state is `dState (j + 1) o`.

**Proof sketch.** On every log the refusal test is false (`href`, by cases on `o`) and the
well-formedness test is true (`hwf`), by `fields_input`. With `impl_of_query`: the first round,
with an empty log, asks `wR w ++ wC w` (`ofFn_padFin_pair`); the second, with the answer `y` in
the log (`rY_one`), compares `⟦y⟧` with `wT w` (`rOK`) and answers `rDec`, which is `decL f_k w` by
`hFE` on the `n`-bit nonce, or `rZero = ⊥` (`rZero_fields`); the new state is `dState (j + 1) o`
(`recBits_fields`, `rNew_fields`). -/
theorem dHandler_impl_dec_wf (x : Fin ((ettDin 1).eval n) → Bool) (j : ℕ)
    (o : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n)
    (href : refW o (List.ofFn x) = false) (hwf : wfW n (List.ofFn x) = true) :
    (dHandler q E hE b).impl n z (dHSeed q E hE b n (k, W)) 1 x (dHState q E hE b n j o) =
      .query 0 (padFin _ (wR (List.ofFn x) ++ wC (List.ofFn x))) fun y =>
        .pure (padFin _ (if List.ofFn y = wT (List.ofFn x) then decL (F n k) (List.ofFn x)
          else []), dHState q E hE b n (j + 1) o) := by
  have hwf' := hwf
  rw [wfW_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hwf'
  have hRef : ∀ L, rRef (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
      (List.ofFn (dHState q E hE b n j o)) (1 : Fin 3) (List.ofFn x) L) = false := by
    intro L
    obtain ⟨-, -, -, hX, -, -, hFlag, hRec, -, -⟩ :=
      fields_input q E hE b n z k W (i := 1) (List.ofFn x) L j o hj
    rw [rRef, hFlag, hRec, hX]
    cases o with
    | none => rfl
    | some c =>
      rw [refW_some, decide_eq_false_iff_not] at href
      rw [recBits_some, List.drop_succ_cons, List.drop_zero, Option.isSome_some, Bool.true_and,
        decide_eq_false_iff_not]
      exact fun h => href h.symm
  have hWF : ∀ L, rWF (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
      (List.ofFn (dHState q E hE b n j o)) (1 : Fin 3) (List.ofFn x) L) = true := by
    intro L
    obtain ⟨hU, -, -, hX, -, -, -, -, -, -⟩ :=
      fields_input q E hE b n z k W (i := 1) (List.ofFn x) L j o hj
    rw [rWF, hU, hX, List.length_replicate, ← wC_eq, ← wR_eq, hwf'.1, hwf'.2]
    simp
  refine InteractiveHandler.impl_of_query _ n z _ x _ 0 _ _ _
    (by rw [dHandler_perCall, PolyExpr.eval_const]) ?_ ?_
  · show dRun q E b _ = _
    obtain ⟨-, -, hI, hX, hL, -, -, -, -, -⟩ :=
      fields_input q E hE b n z k W (i := 1) (List.ofFn x) [] j o hj
    rw [dRun, hI, Fin.val_one, List.replicate_one, List.headD_cons, if_pos rfl,
      List.drop_succ_cons, List.drop_zero, List.headD_nil, if_neg Bool.false_ne_true, hRef,
      if_neg Bool.false_ne_true, hWF, if_pos rfl, hL, if_pos (decide_eq_true rfl), hX,
      ← wC_eq, ← wR_eq, ofFn_padFin_pair n hwf'.1 hwf'.2]
    rfl
  · intro y
    show dRun q E b _ = _
    simp only [Fin.val_zero, List.replicate_zero]
    obtain ⟨hU, -, hI, hX, hL, -, hFlag, hRec, hK, -⟩ :=
      fields_input q E hE b n z k W (i := 1) (List.ofFn x)
        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((tagOut 0).eval n)
          (wR (List.ofFn x) ++ wC (List.ofFn x)))) (List.ofFn y))) []) j o hj
    have hY := rY_one _ _ _ _ hL
    have hans : (if rOK (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
        (List.ofFn (dHState q E hE b n j o)) (1 : Fin 3) (List.ofFn x)
        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((tagOut 0).eval n)
          (wR (List.ofFn x) ++ wC (List.ofFn x)))) (List.ofFn y))) [])) = true then
        rDec E (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
          (List.ofFn (dHState q E hE b n j o)) (1 : Fin 3) (List.ofFn x)
          (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((tagOut 0).eval n)
            (wR (List.ofFn x) ++ wC (List.ofFn x)))) (List.ofFn y))) []))
        else rZero (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
          (List.ofFn (dHState q E hE b n j o)) (1 : Fin 3) (List.ofFn x)
          (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((tagOut 0).eval n)
            (wR (List.ofFn x) ++ wC (List.ofFn x)))) (List.ofFn y))) []))) =
        List.ofFn (padFin ((ettDout 1).eval n) (if List.ofFn y = wT (List.ofFn x) then
          decL (F n k) (List.ofFn x) else [])) := by
      rw [rOK, hY, hX, ← wT_eq]
      by_cases ht : List.ofFn y = wT (List.ofFn x)
      · rw [if_pos (decide_eq_true ht), if_pos ht, rDec, hK, hX, ← wC_eq, ← wR_eq]
        have hr : wR (List.ofFn x) = List.ofFn (padFin n (wR (List.ofFn x))) :=
          (ofFn_padFin_of_length hwf'.1).symm
        rw [hr, hFE, ← decL_eq, ofFn_padFin_of_length]
        rw [decL_eq, List.length_cons, List.length_zipWith, List.length_ofFn, hwf'.2, Nat.min_self,
          ettDout_one, PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]
      · rw [if_neg (by rw [decide_eq_true_eq]; exact ht), if_neg ht, rZero_fields n _ hU]
    rw [dRun, hI, Fin.val_one, List.replicate_one, List.headD_cons, if_pos rfl,
      List.drop_succ_cons, List.drop_zero, List.headD_nil, if_neg Bool.false_ne_true, hRef,
      if_neg Bool.false_ne_true, hWF, if_pos rfl, hL, log_ne_nil, if_neg Bool.false_ne_true, hans,
      hFlag, hRec, recBits_fields, rNew_fields q E hE b n z k W (i := 1) _ _ j o o hj]

/-- **A malformed decryption:** from `dState j o` with a query that is not refused and not well
formed, the answer is `⊥` and the state is `dState (j + 1) o`: for `j < q(n)`,
`refW o ⟦x⟧ = false` and `wfW n ⟦x⟧ = false`,
`(dHandler …).impl n z (dHSeed … (k, W)) 1 x (dHState … j o) =
pure (padFin _ [], dHState … (j + 1) o)`.

**Proof sketch.** As for `dHandler_impl_dec_ref`, the handler answers in one round
(`impl_of_ret`); now the refusal test is false (`href`, by cases on `o`) and the well-formedness
test is false (`hwf`, through `wfW_eq`), so `dRun` takes the malformed branch: the answer
`rZero = ⊥` and the state `dState (j + 1) o` (`rZero_fields`, `recBits_fields`, `rNew_fields`). -/
theorem dHandler_impl_dec_nwf (x : Fin ((ettDin 1).eval n) → Bool) (j : ℕ)
    (o : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n)
    (href : refW o (List.ofFn x) = false) (hwf : wfW n (List.ofFn x) = false) :
    (dHandler q E hE b).impl n z (dHSeed q E hE b n (k, W)) 1 x (dHState q E hE b n j o) =
      .pure (padFin _ [], dHState q E hE b n (j + 1) o) := by
  refine InteractiveHandler.impl_of_ret _ n z _ x _ _ _ ?_
  show dRun q E b _ = _
  obtain ⟨hU, -, hI, hX, -, -, hFlag, hRec, -, -⟩ :=
    fields_input q E hE b n z k W (i := 1) (List.ofFn x) [] j o hj
  have hRef : rRef (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
      (List.ofFn (dHState q E hE b n j o)) (1 : Fin 3) (List.ofFn x) []) = false := by
    rw [rRef, hFlag, hRec, hX]
    cases o with
    | none => rfl
    | some c =>
      rw [refW_some, decide_eq_false_iff_not] at href
      rw [recBits_some, List.drop_succ_cons, List.drop_zero, Option.isSome_some, Bool.true_and,
        decide_eq_false_iff_not]
      exact fun h => href h.symm
  have hWF : rWF (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
      (List.ofFn (dHState q E hE b n j o)) (1 : Fin 3) (List.ofFn x) []) = false := by
    rw [rWF, hU, hX, List.length_replicate, ← wC_eq, ← wR_eq, ← wfW_eq, hwf]
  rw [dRun, hI, Fin.val_one, List.replicate_one, List.headD_cons, if_pos rfl, List.drop_succ_cons,
    List.drop_zero, List.headD_nil, if_neg Bool.false_ne_true, hRef, if_neg Bool.false_ne_true,
    hWF, if_neg Bool.false_ne_true, rZero_fields n _ hU, hFlag, hRec, recBits_fields,
    rNew_fields q E hE b n z k W (i := 1) _ _ j o o hj]

/-- **A recorded challenge is repeated:** from `dState j (some c)`, a challenge is answered `c`
and the state is `dState (j + 1) (some c)`: for `j < q(n)`,
`(dHandler …).impl n z (dHSeed … (k, W)) 2 x (dHState … j (some c)) =
pure (padFin _ ⟦c⟧, dHState … (j + 1) (some c))`. -/
theorem dHandler_impl_challenge_some (x : Fin ((ettDin 2).eval n) → Bool) (j : ℕ)
    (c : Fin (ettCt.eval n) → Bool) (hj : j < q.eval n) :
    (dHandler q E hE b).impl n z (dHSeed q E hE b n (k, W)) 2 x (dHState q E hE b n j (some c)) =
      .pure (padFin _ (List.ofFn c), dHState q E hE b n (j + 1) (some c)) := by
  refine InteractiveHandler.impl_of_ret _ n z _ x _ _ _ ?_
  show dRun q E b _ = _
  obtain ⟨-, -, hI, -, -, -, hFlag, hRec, -, -⟩ :=
    fields_input q E hE b n z k W (i := 2) (List.ofFn x) [] j (some c) hj
  have hc : List.ofFn (padFin ((ettDout 2).eval n) (List.ofFn c)) = List.ofFn c :=
    ofFn_padFin_of_length (by rw [List.length_ofFn, ettDout_two])
  have hrec : true :: (recBits n (some c)).drop 1 = recBits n (some c) := rfl
  rw [dRun, hI, hFlag, hRec]
  simp only [show List.replicate ((2 : Fin 3) : ℕ) true = [true, true] from rfl, List.headD_cons,
    List.drop_succ_cons, List.drop_zero, if_true, Option.isSome_some]
  rw [hrec, rNew_fields q E hE b n z k W (i := 2) _ _ j (some c) (some c) hj, hc, recBits_some,
    List.drop_succ_cons, List.drop_zero]

include hFE in
/-- **The first challenge with the next tape:** from `dState j none` with `j < q(n)`, the
challenge `⟨m₀, m₁⟩` asks the outer oracle at `r ‖ c₁` with the tape `r` and
`c₁ = maskL f_k r m_b`; its answer `y` gives the ciphertext `c = ⟨r, ⟨c₁, y⟩⟩`, recorded in the
state `dState (j + 1) (some c)`.

**Proof sketch.** The selected message read from the round input is `msgOf n b ⟦x⟧` (`rMsg`,
`fields_input`), of `n` bits. With `impl_of_query`: the first round, with no record (flag false)
and an empty log, asks `r ‖ c₁` with the tape `r` (`mask_eval`, `ofFn_padFin_pair`); the second,
with `y` in the log (`rY_one`), returns `c = ⟨r, ⟨c₁, y⟩⟩` (`ctW_eq`, of `6n + 4` bits by
`length_ctW_tag`) and the new state with count `j + 1` and the record bits
`true :: ⟦c⟧ = recBits n (some c)` (`rNew_fields`). -/
theorem dHandler_impl_challenge_none (x : Fin ((ettDin 2).eval n) → Bool) (j : ℕ)
    (hj : j < q.eval n) :
    (dHandler q E hE b).impl n z (dHSeed q E hE b n (k, W)) 2 x (dHState q E hE b n j none) =
      .query 0 (padFin _ (List.ofFn (dTape q n W j hj) ++
          maskL (F n k) (dTape q n W j hj) (AdaptiveCPA.msgOf n b (List.ofFn x)))) fun y =>
        .pure (padFin _ (ctW (List.ofFn (dTape q n W j hj))
            (maskL (F n k) (dTape q n W j hj) (AdaptiveCPA.msgOf n b (List.ofFn x)))
            (List.ofFn y)),
          dHState q E hE b n (j + 1) (some (padFin (ettCt.eval n)
            (ctW (List.ofFn (dTape q n W j hj))
              (maskL (F n k) (dTape q n W j hj) (AdaptiveCPA.msgOf n b (List.ofFn x)))
              (List.ofFn y))))) := by
  have hmsg : (AdaptiveCPA.msgOf n b (List.ofFn x)).length = n := by
    have hx : (List.ofFn x).length = n + n := by
      rw [List.length_ofFn, ettDin_two, PolyExpr.eval_add, PolyExpr.eval_var]
    rw [AdaptiveCPA.msgOf_eq]
    cases b <;> simp [hx]
  have hm := length_maskL (F n k) (dTape q n W j hj) hmsg
  have hMsg : ∀ L, rMsg b (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
      (List.ofFn (dHState q E hE b n j none)) (2 : Fin 3) (List.ofFn x) L) =
      AdaptiveCPA.msgOf n b (List.ofFn x) := by
    intro L
    obtain ⟨hU, -, -, hX, -, -, -, -, -, -⟩ :=
      fields_input q E hE b n z k W (i := 2) (List.ofFn x) L j none hj
    rw [rMsg, hU, hX, List.length_replicate, AdaptiveCPA.msgOf_eq]
  refine InteractiveHandler.impl_of_query _ n z _ x _ 0 _ _ _
    (by rw [dHandler_perCall, PolyExpr.eval_const]) ?_ ?_
  · show dRun q E b _ = _
    obtain ⟨-, -, hI, -, hL, -, hFlag, -, hK, hN⟩ :=
      fields_input q E hE b n z k W (i := 2) (List.ofFn x) [] j none hj
    rw [dRun, hI, hFlag, hL]
    simp only [show List.replicate ((2 : Fin 3) : ℕ) true = [true, true] from rfl, List.headD_cons,
      List.drop_succ_cons, List.drop_zero, if_true, Option.isSome_none, Bool.false_eq_true,
      if_false, decide_true]
    rw [hMsg, rMask, hK, hN, mask_eval E F hFE n k, ofFn_padFin_pair n List.length_ofFn hm]
    rfl
  · intro y
    show dRun q E b _ = _
    simp only [Fin.val_zero, List.replicate_zero]
    obtain ⟨-, -, hI, -, hL, -, hFlag, -, hK, hN⟩ :=
      fields_input q E hE b n z k W (i := 2) (List.ofFn x)
        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((tagOut 0).eval n)
          (List.ofFn (dTape q n W j hj) ++
            maskL (F n k) (dTape q n W j hj) (AdaptiveCPA.msgOf n b (List.ofFn x)))))
          (List.ofFn y))) []) j none hj
    have hY := rY_one _ _ _ _ hL
    have hlen := length_ctW_tag n (List.length_ofFn (f := dTape q n W j hj)) hm
      (by rw [List.length_ofFn, tagOut_eq, tagLen_eval] : (List.ofFn y).length = 2 * n)
    have hct : List.ofFn (padFin ((ettDout 2).eval n) (ctW (List.ofFn (dTape q n W j hj))
        (maskL (F n k) (dTape q n W j hj) (AdaptiveCPA.msgOf n b (List.ofFn x)))
        (List.ofFn y))) =
        ctW (List.ofFn (dTape q n W j hj))
          (maskL (F n k) (dTape q n W j hj) (AdaptiveCPA.msgOf n b (List.ofFn x)))
          (List.ofFn y) :=
      ofFn_padFin_of_length (by rw [hlen, ettDout_two])
    have hrec : true :: ctW (List.ofFn (dTape q n W j hj))
        (maskL (F n k) (dTape q n W j hj) (AdaptiveCPA.msgOf n b (List.ofFn x))) (List.ofFn y) =
        recBits n (some (padFin (ettCt.eval n) (ctW (List.ofFn (dTape q n W j hj))
          (maskL (F n k) (dTape q n W j hj) (AdaptiveCPA.msgOf n b (List.ofFn x)))
          (List.ofFn y)))) := by
      rw [recBits_some, ofFn_padFin_of_length hlen]
    rw [dRun, hI, hFlag, hL]
    simp only [show List.replicate ((2 : Fin 3) : ℕ) true = [true, true] from rfl, List.headD_cons,
      List.drop_succ_cons, List.drop_zero, if_true, Option.isSome_none, Bool.false_eq_true,
      if_false]
    rw [log_ne_nil, if_neg Bool.false_ne_true, hMsg, hct, rCt, rMask, hK, hN, hY,
      mask_eval E F hFE n k, ← ctW_eq, hrec,
      rNew_fields q E hE b n z k W (i := 2) _ _ j none _ hj]

end Answers

end TCSlib.Cryptography.Composability.ETTGame

## ===== TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Lazy.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Games

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The rejecting experiment with lazily sampled tags

Step 3 of [PS10, Theorem 170.4] simulates the experiment that rejects fresh decryption queries by
a CPA adversary against the §3.9 scheme. That adversary cannot hold a random function on `2n`
bits; it samples the tags lazily, one tape per query, and answers decryption queries from the table
of its earlier answers. This file states that lazy experiment (`ettLazy`, with tapes in advance
`ettLazyTape`) and proves that it has the law of the rejecting experiment with a uniform random
tag function (`expect_ettImpl_lazy`).

**The lazy state** (`LSt n d`) is the recorded challenge and the table of the `Enc′` answers, newest
first: each entry is the pair `r ‖ c₁`, its tag and the encrypted message.
- `Enc′` on `m` with the nonce `r`: the tag of the pair `p = r ‖ c₁` is the table's tag at `p` if
  `p` is in the table, else the challenge's tag if `p` is the challenge's pair, else the query's
  tape (`tagOf`); the entry `(p, tag, m)` is added.
- `Dec′` on `w` refuses the record; a well-formed `w` whose pair is in the table and whose tag is
  the table's tag gets `⟨1, m⟩` with the table's message, every other word `⊥` (`lazyDec`).
- `Challenge` on `⟨m₀, m₁⟩`: the first time, as `Enc′` on `m_b` (without an entry), recorded.

**The law** (`expect_ettImpl_lazy`). Average the rejecting experiment over `R` with the table's tags
written over it (`tagTbl`, `ovr`). A new pair moves `R`'s value into the table
(`expect_sample_ovr`); a pair in the table has its tag; a decryption with a listed pair reads the
table's tag, and its answer `⟨1, c₁ ⊕ f(r)⟩` is the table's message, because the entry's pair is
`r ‖ (m ⊕ f(r))` with an `n`-bit `m` (`LInv`).

## Main definitions

* `ETTGame.LEntry`, `LSt`, `keysL`, `lookL`, `tagOf`, `lazyDec`, `tagTbl`, `LInv`.
* `ETTGame.lazyStep`, `ettLazyK`, `ettLazy`, `ettLazyTape`.

## Main results

* `ETTGame.expect_ettImpl_lazy`: the rejecting experiment with a random tag function is the lazy
  experiment.
* `ETTGame.expect_ettLazyTape`: the lazy experiment with tapes in advance.
* `ETTGame.tagTbl_none_nil`, `ETTGame.lInv_nil`: the empty lazy state.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 170.4 (book pp. 170–171).
-/

namespace TCSlib.Cryptography.Composability.ETTGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

/-! ### Tables -/

section Tables

variable {n d : ℕ}

/-- An entry of the lazy table: a pair, its tag and the message of the encryption,
`LEntry n = (Fin (2n) → Bool) × (Fin (2n) → Bool) × List Bool`. -/
abbrev LEntry (n : ℕ) : Type := (Fin (2 * n) → Bool) × (Fin (2 * n) → Bool) × List Bool

/-- `LEntry n = pair × tag × message`. -/
theorem LEntry_eq (n : ℕ) :
    LEntry n = ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool) × List Bool) := rfl

/-- The lazy state: the recorded challenge and the table, newest entry first,
`LSt n d = Option (Fin d → Bool) × List (LEntry n)`. -/
abbrev LSt (n d : ℕ) : Type := Option (Fin d → Bool) × List (LEntry n)

/-- `LSt n d = Option (Fin d → Bool) × List (LEntry n)`. -/
theorem LSt_eq (n d : ℕ) : LSt n d = (Option (Fin d → Bool) × List (LEntry n)) := rfl

/-- The pairs of the table: `keysL L = L.map Prod.fst`. -/
def keysL (L : List (LEntry n)) : List (Fin (2 * n) → Bool) := L.map Prod.fst

/-- `keysL L = L.map Prod.fst`. -/
theorem keysL_eq (L : List (LEntry n)) : keysL L = L.map Prod.fst := rfl

/-- **The table's entry at a pair:** the first (newest) entry with the pair `p`, if any,
`lookL L p = if p ∈ keysL L then some (L.getD ((keysL L).idxOf p) default) else none`. -/
def lookL (L : List (LEntry n)) (p : Fin (2 * n) → Bool) : Option (LEntry n) :=
  if p ∈ keysL L then some (L.getD ((keysL L).idxOf p) default) else none

/-- `lookL L p = if p ∈ keysL L then some (L.getD ((keysL L).idxOf p) default) else none`. -/
theorem lookL_eq (L : List (LEntry n)) (p : Fin (2 * n) → Bool) :
    lookL L p = if p ∈ keysL L then some (L.getD ((keysL L).idxOf p) default) else none := rfl

/-- **The tag of a pair:** the table's, else the challenge's at its pair, else none:
`tagOf s p = some e.2.1` if `lookL s.2 p = some e`; else
`tagOf s p = some (padFin (2n) (wT ⟦c⟧))` if `s.1 = some c` and `pairW n ⟦c⟧ = p`; else
`tagOf s p = none`. -/
def tagOf (s : LSt n d) (p : Fin (2 * n) → Bool) : Option (Fin (2 * n) → Bool) :=
  match lookL s.2 p with
  | some e => some e.2.1
  | none =>
    match s.1 with
    | some c => if pairW n (List.ofFn c) = p then some (padFin (2 * n) (wT (List.ofFn c))) else none
    | none => none

/-- `tagOf s p` unfolded: the table's tag, else the challenge's at its pair,
`tagOf s p = some e.2.1` if `lookL s.2 p = some e`; else
`tagOf s p = some (padFin (2n) (wT ⟦c⟧))` if `s.1 = some c` and `pairW n ⟦c⟧ = p`; else
`tagOf s p = none`. -/
theorem tagOf_eq (s : LSt n d) (p : Fin (2 * n) → Bool) :
    tagOf s p = match lookL s.2 p with
      | some e => some e.2.1
      | none =>
        match s.1 with
        | some c =>
          if pairW n (List.ofFn c) = p then some (padFin (2 * n) (wT (List.ofFn c))) else none
        | none => none := rfl

/-- **The lazy decryption answer:** `⊥` on the record; on a well-formed word whose pair is in the
table with the word's tag, `⟨1, m⟩` with the table's message; `⊥` otherwise:
`lazyDec s w = true :: e.2.2` if `refW s.1 w = false`, `wfW n w = true`,
`lookL s.2 (pairW n w) = some e` and `⟦e.2.1⟧ = wT w`; else `lazyDec s w = []`. -/
def lazyDec (s : LSt n d) (w : List Bool) : List Bool :=
  if (!refW s.1 w && wfW n w) = true then
    match lookL s.2 (pairW n w) with
    | some e => if List.ofFn e.2.1 = wT w then true :: e.2.2 else []
    | none => []
  else []

/-- `lazyDec s w` unfolded: `lazyDec s w = true :: e.2.2` if `refW s.1 w = false`,
`wfW n w = true`, `lookL s.2 (pairW n w) = some e` and `⟦e.2.1⟧ = wT w`; else
`lazyDec s w = []`. -/
theorem lazyDec_eq (s : LSt n d) (w : List Bool) :
    lazyDec s w = if (!refW s.1 w && wfW n w) = true then
      match lookL s.2 (pairW n w) with
      | some e => if List.ofFn e.2.1 = wT w then true :: e.2.2 else []
      | none => []
    else [] := rfl

/-- **The tag table of a lazy state:** the entries' tags, newest first, then the challenge's,
`tagTbl s = s.2.map (fun e => (e.1, e.2.1)) ++ [(pairW n ⟦c⟧, padFin (2n) (wT ⟦c⟧))]` for
`s.1 = some c`, and `tagTbl s = s.2.map (fun e => (e.1, e.2.1))` for `s.1 = none`. -/
def tagTbl (s : LSt n d) : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool)) :=
  s.2.map (fun e => (e.1, e.2.1)) ++
    match s.1 with
    | some c => [(pairW n (List.ofFn c), padFin (2 * n) (wT (List.ofFn c)))]
    | none => []

/-- `tagTbl s` unfolded:
`tagTbl s = s.2.map (fun e => (e.1, e.2.1)) ++ [(pairW n ⟦c⟧, padFin (2n) (wT ⟦c⟧))]` for
`s.1 = some c`, and `tagTbl s = s.2.map (fun e => (e.1, e.2.1)) ++ []` for `s.1 = none`. -/
theorem tagTbl_eq (s : LSt n d) :
    tagTbl s = s.2.map (fun e => (e.1, e.2.1)) ++
      match s.1 with
      | some c => [(pairW n (List.ofFn c), padFin (2 * n) (wT (List.ofFn c)))]
      | none => [] := rfl

/-- The empty table has no pairs: `keysL [] = []`. -/
theorem keysL_nil : keysL ([] : List (LEntry n)) = [] := by
  rw [keysL_eq, List.map_nil]

/-- The empty lazy state has the empty tag table: `tagTbl (none, []) = []`. -/
theorem tagTbl_none_nil : tagTbl ((none, []) : LSt n d) = [] := by
  rw [tagTbl_eq, List.map_nil, List.nil_append]

end Tables

/-! ### Tags as a table written over a function -/

section Ovr

variable {n d : ℕ}

/-- Writing a concatenation is writing its parts: `ovr (A ++ B) R = ovr A (ovr B R)`. -/
theorem ovr_append (A B : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool)))
    (R : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) : ovr (A ++ B) R = ovr A (ovr B R) := by
  induction A with
  | nil => rw [List.nil_append, ovr_nil]
  | cons e A ih =>
    obtain ⟨p, y⟩ := e
    rw [List.cons_append, ovr_cons, ovr_cons, ih]

/-- The entry at a listed pair has that pair:
`p ∈ keysL L → (L.getD ((keysL L).idxOf p) _).1 = p`. -/
theorem getD_idxOf_fst {L : List (LEntry n)} {p : Fin (2 * n) → Bool} (hp : p ∈ keysL L) :
    (L.getD ((keysL L).idxOf p) default).1 = p := by
  induction L with
  | nil => simp [keysL_eq] at hp
  | cons e L ih =>
    rw [keysL_eq, List.map_cons, List.idxOf_cons]
    by_cases h : e.1 = p
    · simp [h]
    · have hp' : p ∈ keysL L := by
        rw [keysL_eq, List.map_cons, List.mem_cons] at hp
        exact hp.resolve_left (Ne.symm h)
      simp only [show (e.1 == p) = false from beq_false_of_ne h, cond_false, List.getD_cons_succ]
      exact ih hp'

/-- **On a listed pair the tag table gives the newest entry's tag:**
`p ∈ keysL L → ovr (L-tags ++ X) R p = (L.getD ((keysL L).idxOf p) _).2.1`. -/
theorem ovr_tags_of_mem (L : List (LEntry n))
    (X : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool)))
    (R : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) {p : Fin (2 * n) → Bool}
    (hp : p ∈ keysL L) :
    ovr (L.map (fun e => (e.1, e.2.1)) ++ X) R p = (L.getD ((keysL L).idxOf p) default).2.1 := by
  induction L with
  | nil => simp [keysL_eq] at hp
  | cons e L ih =>
    rw [List.map_cons, List.cons_append, ovr_cons, keysL_eq, List.map_cons, List.idxOf_cons]
    by_cases h : e.1 = p
    · subst h
      simp
    · have hp' : p ∈ keysL L := by
        rw [keysL_eq, List.map_cons, List.mem_cons] at hp
        exact hp.resolve_left (Ne.symm h)
      rw [Function.update_of_ne (Ne.symm h)]
      simp only [show (e.1 == p) = false from beq_false_of_ne h, cond_false, List.getD_cons_succ]
      exact ih hp'

/-- The keys of the tag table: the listed pairs, then the challenge's pair,
`(tagTbl s).map Prod.fst = keysL s.2 ++ [pairW n ⟦c⟧]` for `s.1 = some c`, and
`(tagTbl s).map Prod.fst = keysL s.2 ++ []` for `s.1 = none`. -/
theorem keys_tagTbl (s : LSt n d) :
    (tagTbl s).map Prod.fst = keysL s.2 ++
      match s.1 with
      | some c => [pairW n (List.ofFn c)]
      | none => [] := by
  rw [tagTbl_eq, List.map_append, List.map_map, keysL_eq]
  congr 1
  cases s.1 <;> rfl

/-- **`tagOf` reads the tag table:** for every `R`, `tagOf s p` is `ovr (tagTbl s) R p` on the keys
of the tag table, and none elsewhere,
`tagOf s p = if p ∈ (tagTbl s).map Prod.fst then some (ovr (tagTbl s) R p) else none`. -/
theorem tagOf_eq_ovr (s : LSt n d) (p : Fin (2 * n) → Bool)
    (R : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) :
    tagOf s p = if p ∈ (tagTbl s).map Prod.fst then some (ovr (tagTbl s) R p) else none := by
  rw [tagOf_eq, keys_tagTbl, tagTbl_eq]
  by_cases hp : p ∈ keysL s.2
  · rw [lookL_eq, if_pos hp, if_pos (List.mem_append_left _ hp), ovr_tags_of_mem _ _ _ hp]
  · rw [lookL_eq, if_neg hp, ovr_append, ovr_of_not_mem (by rwa [List.map_map]) _]
    obtain ⟨o, L⟩ := s
    cases o with
    | none => simp [hp]
    | some c =>
      simp only
      by_cases hc : pairW n (List.ofFn c) = p
      · subst hc
        simp [ovr_cons, ovr_nil]
      · simp only [if_neg hc, List.mem_append, hp, List.mem_singleton, false_or]
        rw [if_neg (Ne.symm hc)]

/-- The tag table after an entry: `tagTbl (o, (p, t, m) :: L) = (p, t) :: tagTbl (o, L)`. -/
private theorem tagTbl_cons (o : Option (Fin d → Bool)) (p t : Fin (2 * n) → Bool) (m : List Bool)
    (L : List (LEntry n)) : tagTbl (o, (p, t, m) :: L) = (p, t) :: tagTbl (o, L) := by
  rw [tagTbl_eq, tagTbl_eq, List.map_cons, List.cons_append]

/-- The pairs after an entry: `keysL ((p, t, m) :: L) = p :: keysL L`. -/
private theorem keysL_cons (p t : Fin (2 * n) → Bool) (m : List Bool) (L : List (LEntry n)) :
    keysL ((p, t, m) :: L) = p :: keysL L := by
  rw [keysL_eq, keysL_eq, List.map_cons]

/-- Writing a value the table already gives changes nothing:
`ovr M R p = y → ovr ((p, y) :: M) R = ovr M R`. -/
private theorem ovr_cons_self {M : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))}
    {R : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)} {p y : Fin (2 * n) → Bool}
    (h : ovr M R p = y) : ovr ((p, y) :: M) R = ovr M R := by
  rw [ovr_cons, ← h, Function.update_eq_self]

/-- Appending a value at a key changes nothing: `p ∈ keys M → ovr (M ++ [(p, y)]) R = ovr M R`. -/
private theorem ovr_append_of_mem {M : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))}
    {p : Fin (2 * n) → Bool} (hp : p ∈ M.map Prod.fst) (y : Fin (2 * n) → Bool)
    (R : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) : ovr (M ++ [(p, y)]) R = ovr M R := by
  rw [ovr_append, ovr_cons, ovr_nil]
  funext x
  by_cases hx : x ∈ M.map Prod.fst
  · exact ovr_of_mem hx _ _
  · rw [ovr_of_not_mem hx, ovr_of_not_mem hx,
      Function.update_of_ne (fun h => hx (by rw [h]; exact hp))]

/-- Appending a value at a new key is writing it first:
`p ∉ keys M → ovr (M ++ [(p, y)]) R = ovr ((p, y) :: M) R`. -/
private theorem ovr_append_of_not_mem {M : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))}
    {p : Fin (2 * n) → Bool} (hp : p ∉ M.map Prod.fst) (y : Fin (2 * n) → Bool)
    (R : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) :
    ovr (M ++ [(p, y)]) R = ovr ((p, y) :: M) R := by
  rw [ovr_append, ovr_cons, ovr_nil, ovr_cons, ovr_update hp]

end Ovr

/-! ### The lazy experiment -/

/-- **XOR twice with the same pad is the identity** (generic; several modules keep a private
copy): `(m ⊕ p) ⊕ p = m` when `|m| ≤ |p|`. -/
theorem zipWith_xor_cancel : ∀ (m p : List Bool), m.length ≤ p.length →
    List.zipWith xor (List.zipWith xor m p) p = m
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | a :: m, c :: p, h => by
    simp only [List.zipWith_cons_cons, List.cons.injEq]
    exact ⟨by cases a <;> cases c <;> rfl, zipWith_xor_cancel m p (by simpa using h)⟩

section Lazy

variable (ins outs : Fin 3 → ℕ) (d n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)) (b : Bool)

/-- **The invariant of the lazy table:** every entry `(p, t, m)` has an `n`-bit message `m` and the
pair `p = r ‖ (m ⊕ f(r))` of some nonce `r`. -/
def LInv {d : ℕ} (s : LSt n d) : Prop :=
  ∀ e ∈ s.2, ∃ r : Fin n → Bool, e.1 = pairV n (List.ofFn r) (maskL f r e.2.2) ∧ e.2.2.length = n

/-- `LInv f s` unfolded:
`LInv n f s ↔ ∀ e ∈ s.2, ∃ r, e.1 = pairV n ⟦r⟧ (maskL f r e.2.2) ∧ |e.2.2| = n`. -/
theorem lInv_iff {d : ℕ} (s : LSt n d) :
    LInv n f s ↔ ∀ e ∈ s.2,
      ∃ r : Fin n → Bool, e.1 = pairV n (List.ofFn r) (maskL f r e.2.2) ∧ e.2.2.length = n :=
  Iff.rfl

/-- The empty table has the invariant: `LInv n f (o, [])`, vacuously, since `LInv n f s`
quantifies over `e ∈ s.2` and here `s.2 = []`. -/
theorem lInv_nil {d : ℕ} (o : Option (Fin d → Bool)) : LInv n f ((o, []) : LSt n d) :=
  fun _ he => absurd he List.not_mem_nil

/-- **The rejecting decryption answer with the table's tags is the lazy answer:** under the
invariant, `decAnsW f (ovr (tagTbl s) R) true (s.1, keysL s.2) w = lazyDec s w`.

**Proof sketch.** A refused or malformed word gets `⊥` in both. A well-formed word with a listed
pair reads the newest entry `(p, t, m)` at it (`ovr_tags_of_mem`, `getD_idxOf_fst`); its fields are
`r` and `m ⊕ f(r)` (`eq_of_pairV_eq`), so `decL f w = ⟨1, m⟩` (`zipWith_xor_cancel`). A fresh pair
is rejected by both. -/
theorem decAnsW_tagTbl {d : ℕ} (s : LSt n d) (hs : LInv n f s)
    (R : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (w : List Bool) :
    decAnsW f (ovr (tagTbl s) R) true (s.1, keysL s.2) w = lazyDec s w := by
  rw [decAnsW_eq, lazyDec_eq, validW_eq]
  simp only [Bool.not_true, Bool.false_or]
  by_cases hr : refW s.1 w = true
  · simp [hr]
  · rw [Bool.not_eq_true] at hr
    simp only [hr, Bool.not_false, Bool.true_and]
    by_cases hw : wfW n w = true
    · simp only [hw, Bool.true_and]
      have hw' := hw
      rw [wfW_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hw'
      by_cases hk : pairW n w ∈ keysL s.2
      · rw [lookL_eq, if_pos hk, tagL_eq, ← pairW_eq, tagTbl_eq, ovr_tags_of_mem _ _ _ hk]
        simp only [decide_eq_true hk, Bool.and_true, decide_eq_true_eq, ↓reduceIte]
        have hfst := getD_idxOf_fst hk
        have hlt : (keysL s.2).idxOf (pairW n w) < s.2.length := by
          have := List.idxOf_lt_length_of_mem hk
          rwa [keysL_eq, List.length_map] at this
        obtain ⟨r, hp, hl⟩ := hs (s.2.getD ((keysL s.2).idxOf (pairW n w)) default) (by
          rw [List.getD_eq_getElem _ _ hlt]
          exact List.getElem_mem hlt)
        by_cases ht : wT w = List.ofFn (s.2.getD ((keysL s.2).idxOf (pairW n w)) default).2.1
        · rw [if_pos ht, if_pos ht.symm, decL_eq]
          obtain ⟨h₁, h₂⟩ := eq_of_pairV_eq hw'.1 hw'.2 List.length_ofFn
            (length_maskL f r hl) ((pairW_eq n w).symm.trans (hfst.symm.trans hp))
          rw [h₁, h₂, padFin_ofFn, maskL_eq, zipWith_xor_cancel _ _ (by
            rw [List.length_ofFn, hl])]
        · rw [if_neg ht, if_neg (Ne.symm ht)]
      · rw [lookL_eq, if_neg hk]
        simp [hk]
    · rw [Bool.not_eq_true] at hw
      simp [hw]

/-- **One step of the lazy experiment** with the nonce `r` and the tape `t` (see the module
docstring), with inputs read by `⟦·⟧` and answers and records written by `padFin`: for
`c₁ = maskL f r m`, `p = pairV n ⟦r⟧ c₁` and `τ = (tagOf s p).getD t`,
`lazyStep … r t 0 m s = (ctW ⟦r⟧ c₁ ⟦τ⟧, (s.1, (p, τ, m) :: s.2))`,
`lazyStep … r t 1 w s = (lazyDec s w, s)`,
`lazyStep … r t 2 mm (some c, L) = (⟦c⟧, (some c, L))` and
`lazyStep … r t 2 mm (none, L) = (e, (some e, L))` with `e = ctW ⟦r⟧ c₁ ⟦τ⟧`, where here
`m = msgOf n b mm` and `s = (none, L)`. -/
def lazyStep (r : Fin n → Bool) (t : Fin (2 * n) → Bool) :
    ∀ i : Fin 3, (Fin (ins i) → Bool) → LSt n d → (Fin (outs i) → Bool) × LSt n d
  | 0, m, s => (padFin _ (ctW (List.ofFn r) (maskL f r (List.ofFn m))
        (List.ofFn ((tagOf s (pairV n (List.ofFn r) (maskL f r (List.ofFn m)))).getD t))),
      (s.1, (pairV n (List.ofFn r) (maskL f r (List.ofFn m)),
        (tagOf s (pairV n (List.ofFn r) (maskL f r (List.ofFn m)))).getD t, List.ofFn m) :: s.2))
  | 1, w, s => (padFin _ (lazyDec s (List.ofFn w)), s)
  | 2, _, (some c, L) => (padFin _ (List.ofFn c), (some c, L))
  | 2, mm, (none, L) =>
    (padFin _ (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))
        (List.ofFn ((tagOf ((none, L) : LSt n d) (pairV n (List.ofFn r)
          (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))))).getD t))),
      (some (padFin d (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))
        (List.ofFn ((tagOf ((none, L) : LSt n d) (pairV n (List.ofFn r)
          (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))))).getD t)))), L))

/-- `Enc′` in the lazy experiment: the tag `tagOf s p` or the tape, and a new entry,
`lazyStep … r t 0 m s = (padFin _ (ctW ⟦r⟧ c₁ ⟦τ⟧), (s.1, (p, τ, ⟦m⟧) :: s.2))` with
`c₁ = maskL f r ⟦m⟧`, `p = pairV n ⟦r⟧ c₁` and `τ = (tagOf s p).getD t`. -/
theorem lazyStep_enc (r : Fin n → Bool) (t : Fin (2 * n) → Bool) (m : Fin (ins 0) → Bool)
    (s : LSt n d) :
    lazyStep ins outs d n f b r t 0 m s =
      (padFin _ (ctW (List.ofFn r) (maskL f r (List.ofFn m))
          (List.ofFn ((tagOf s (pairV n (List.ofFn r) (maskL f r (List.ofFn m)))).getD t))),
        (s.1, (pairV n (List.ofFn r) (maskL f r (List.ofFn m)),
          (tagOf s (pairV n (List.ofFn r) (maskL f r (List.ofFn m)))).getD t,
          List.ofFn m) :: s.2)) := rfl

/-- `Dec′` in the lazy experiment answers `lazyDec`:
`lazyStep … r t 1 w s = (padFin _ (lazyDec s ⟦w⟧), s)`. -/
theorem lazyStep_dec (r : Fin n → Bool) (t : Fin (2 * n) → Bool) (w : Fin (ins 1) → Bool)
    (s : LSt n d) :
    lazyStep ins outs d n f b r t 1 w s = (padFin _ (lazyDec s (List.ofFn w)), s) := rfl

/-- A repeated challenge in the lazy experiment:
`lazyStep … r t 2 mm (some c, L) = (padFin _ ⟦c⟧, (some c, L))`. -/
theorem lazyStep_challenge_some (r : Fin n → Bool) (t : Fin (2 * n) → Bool)
    (mm : Fin (ins 2) → Bool) (c : Fin d → Bool) (L : List (LEntry n)) :
    lazyStep ins outs d n f b r t 2 mm (some c, L) = (padFin _ (List.ofFn c), (some c, L)) := rfl

/-- The first challenge in the lazy experiment:
`lazyStep … r t 2 mm (none, L) = (padFin _ e, (some (padFin d e), L))` with
`e = ctW ⟦r⟧ c₁ ⟦(tagOf (none, L) (pairV n ⟦r⟧ c₁)).getD t⟧` and
`c₁ = maskL f r (msgOf n b ⟦mm⟧)`. -/
theorem lazyStep_challenge_none (r : Fin n → Bool) (t : Fin (2 * n) → Bool)
    (mm : Fin (ins 2) → Bool) (L : List (LEntry n)) :
    lazyStep ins outs d n f b r t 2 mm (none, L) =
      (padFin _ (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))
          (List.ofFn ((tagOf ((none, L) : LSt n d) (pairV n (List.ofFn r)
            (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))))).getD t))),
        (some (padFin d (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))
          (List.ofFn ((tagOf ((none, L) : LSt n d) (pairV n (List.ofFn r)
            (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))))).getD t)))), L)) := rfl

/-- One call of the lazy experiment with the tape `t`: draw the nonce and take `lazyStep`,
`ettLazyK … i x s t = (sample (Fin n → Bool)).bind fun r => pure (lazyStep … r t i x s)`. -/
noncomputable def ettLazyK (i : Fin 3) (x : Fin (ins i) → Bool) (s : LSt n d)
    (t : Fin (2 * n) → Bool) : ProbComp ((Fin (outs i) → Bool) × LSt n d) :=
  (sample (Fin n → Bool)).bind fun r => .pure (lazyStep ins outs d n f b r t i x s)

/-- `ettLazyK … i x s t = (sample (Fin n → Bool)).bind fun r => pure (lazyStep … r t i x s)`. -/
theorem ettLazyK_eq (i : Fin 3) (x : Fin (ins i) → Bool) (s : LSt n d) (t : Fin (2 * n) → Bool) :
    ettLazyK ins outs d n f b i x s t =
      (sample (Fin n → Bool)).bind fun r => .pure (lazyStep ins outs d n f b r t i x s) := rfl

/-- **The lazy experiment:** one fresh tape per query (`freshImpl`):
`ettLazy … = freshImpl (ettLazyK …)`. -/
noncomputable def ettLazy : QueryImpl (bitSpec ins outs) (LSt n d) unifSpec :=
  freshImpl (ettLazyK ins outs d n f b)

/-- `ettLazy … = freshImpl (ettLazyK …)`. -/
theorem ettLazy_eq : ettLazy ins outs d n f b = freshImpl (ettLazyK ins outs d n f b) := rfl

/-- **The lazy experiment with tapes in advance** (`tapeImpl`):
`ettLazyTape … T = tapeImpl (ettLazyK …) T`. -/
noncomputable def ettLazyTape (T : ℕ → Fin (2 * n) → Bool) :
    QueryImpl (bitSpec ins outs) (LSt n d × ℕ) unifSpec :=
  tapeImpl (ettLazyK ins outs d n f b) T

/-- `ettLazyTape … T = tapeImpl (ettLazyK …) T`. -/
theorem ettLazyTape_eq (T : ℕ → Fin (2 * n) → Bool) :
    ettLazyTape ins outs d n f b T = tapeImpl (ettLazyK ins outs d n f b) T := rfl

/-- **Tapes in advance have the law of fresh tapes** (`expect_simulate_tapeImpl`): for a
computation with at most `m` queries and `j + m ≤ κ`,
`𝔼_{T ← ({0,1}^{2n})^κ} 𝔼[G (simulate (ettLazyTape … (extTape T)) c (s, j))] =
𝔼[G (simulate (ettLazy …) c s)]`. -/
theorem expect_ettLazyTape (κ : ℕ) {α : Type} (G : α → ℝ) (c : OracleComp (bitSpec ins outs) α)
    (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : LSt n d) (j : ℕ) (hj : j + m ≤ κ) :
    expect (sample (Fin κ → Fin (2 * n) → Bool))
        (fun T => expect (simulate (ettLazyTape ins outs d n f b (AdaptiveCPA.extTape T)) c (s, j))
          fun p => G p.1) =
      expect (simulate (ettLazy ins outs d n f b) c s) fun p => G p.1 :=
  expect_simulate_tapeImpl _ κ G c m hc s j hj

end Lazy

/-! ### The law of the lazy experiment -/

section LazyLaw

variable (ins outs : Fin 3 → ℕ) (d n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)) (b : Bool)

/-- One call of the lazy experiment: draw the tape, then the nonce, and take `lazyStep`,
`ettLazy … i x s = (sample (Fin (2n) → Bool)).bind fun t =>
(sample (Fin n → Bool)).bind fun r => pure (lazyStep … r t i x s)`. -/
theorem ettLazy_apply (i : Fin 3) (x : Fin (ins i) → Bool) (s : LSt n d) :
    ettLazy ins outs d n f b i x s =
      (sample (Fin (2 * n) → Bool)).bind fun t =>
        (sample (Fin n → Bool)).bind fun r => .pure (lazyStep ins outs d n f b r t i x s) := by
  rw [ettLazy_eq, freshImpl_apply]
  rfl

/-- **The rejecting experiment with a uniform random tag function is the lazy experiment**
[PS10, Thm 170.4, proof]: for `(6n + 4)`-bit records, `n`-bit messages and `2n`-bit challenge
queries, from a lazy state with the invariant `LInv`, averaging over `R` with the table's tags
written over it, `𝔼_R 𝔼[G (simulate (ettImpl … (ovr (tagTbl s) R) true b) c (s.1, keysL s.2))] =
𝔼[G (simulate (ettLazy …) c s)]`.

**Proof sketch.** Induction on `c`; both sides draw a nonce per query (exchanged with the
average, `expect_sample_comm`). An encryption or a first challenge at a pair of the tag table reads
the table (`tagOf_eq_ovr`, `ovr_of_mem`), and the new entry repeats it (`ovr_cons_self`,
`ovr_append_of_mem`); at a new pair it reads `R` there, moved into the table by
`expect_sample_ovr` and matched by the lazy tape (`ovr_append_of_not_mem`). Decryption answers agree
(`decAnsW_tagTbl`). A repeated challenge reads nothing. -/
theorem expect_ettImpl_lazy (hd : d = 6 * n + 4) (hi0 : ins 0 = n) (hi2 : ins 2 = n + n)
    {α : Type} (G : α → ℝ) (c : OracleComp (bitSpec ins outs) α) (s : LSt n d)
    (hs : LInv n f s) :
    expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)))
        (fun R => expect (simulate (ettImpl ins outs d n f (ovr (tagTbl s) R) true b) c
          (s.1, keysL s.2)) fun p => G p.1) =
      expect (simulate (ettLazy ins outs d n f b) c s) fun p => G p.1 := by
  induction c generalizing s with
  | pure a =>
    simp only [simulate_pure, expect_pure]
    exact expect_const _ _
  | query i x k ih =>
    rw [simulate_query, ettLazy_apply]
    simp only [simulate_query, ettImpl_apply, OracleComp.bind_assoc, OracleComp.pure_bind,
      expect_bind]
    rw [expect_sample_comm (α := (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)),
      expect_sample_comm (α := Fin (2 * n) → Bool)]
    refine congrArg _ (funext fun r => ?_)
    match i, x, k, ih with
    | 0, m, k, ih =>
      have hm : (List.ofFn m).length = n := by rw [List.length_ofFn, hi0]
      simp only [ettStep_enc, lazyStep_enc, encW_eq_ctW]
      by_cases hp : pairV n (List.ofFn r) (maskL f r (List.ofFn m)) ∈ (tagTbl s).map Prod.fst
      · -- the pair has a tag already
        have hy : ∀ R, ovr (tagTbl s) R (pairV n (List.ofFn r) (maskL f r (List.ofFn m))) =
            ovr (tagTbl s) (fun _ => pairV n (List.ofFn r) (maskL f r (List.ofFn m)))
              (pairV n (List.ofFn r) (maskL f r (List.ofFn m))) := fun R => ovr_of_mem hp R _
        rw [tagOf_eq_ovr s _ (fun _ => pairV n (List.ofFn r) (maskL f r (List.ofFn m))),
          if_pos hp]
        simp only [Option.getD_some, hy, expect_const]
        have hs' : LInv n f (s.1, (pairV n (List.ofFn r) (maskL f r (List.ofFn m)),
            ovr (tagTbl s) (fun _ => pairV n (List.ofFn r) (maskL f r (List.ofFn m)))
              (pairV n (List.ofFn r) (maskL f r (List.ofFn m))), List.ofFn m) :: s.2) := by
          intro e he
          rcases List.mem_cons.1 he with rfl | he
          · exact ⟨r, rfl, hm⟩
          · exact hs e he
        rw [← ih _ _ hs', tagTbl_cons, keysL_cons, Prod.mk.eta]
        refine congrArg _ (funext fun R => ?_)
        rw [ovr_cons_self (hy R)]
      · -- a new pair: its tag is the tape
        rw [tagOf_eq_ovr s _ (fun _ => pairV n (List.ofFn r) (maskL f r (List.ofFn m))),
          if_neg hp]
        simp only [Option.getD_none]
        have e : ∀ R, ovr (tagTbl s) R (pairV n (List.ofFn r) (maskL f r (List.ofFn m))) =
            R (pairV n (List.ofFn r) (maskL f r (List.ofFn m))) := fun R => ovr_of_not_mem hp R
        simp only [e]
        rw [expect_sample_ovr (tagTbl s) hp (fun t g => expect (simulate
          (ettImpl ins outs d n f g true b) (k (padFin _ (ctW (List.ofFn r)
            (maskL f r (List.ofFn m)) (List.ofFn t))))
          (s.1, pairV n (List.ofFn r) (maskL f r (List.ofFn m)) :: keysL s.2)) fun p => G p.1)]
        refine congrArg _ (funext fun t => ?_)
        have hs' : LInv n f (s.1, (pairV n (List.ofFn r) (maskL f r (List.ofFn m)), t,
            List.ofFn m) :: s.2) := by
          intro e he
          rcases List.mem_cons.1 he with rfl | he
          · exact ⟨r, rfl, hm⟩
          · exact hs e he
        rw [← ih _ _ hs', tagTbl_cons, keysL_cons, Prod.mk.eta]
    | 1, w, k, ih =>
      simp only [ettStep_dec, lazyStep_dec, decAnsW_tagTbl n f s hs, expect_const]
      exact ih _ s hs
    | 2, mm, k, ih =>
      obtain ⟨o, L⟩ := s
      cases o with
      | some c =>
        simp only [ettStep_challenge_some, lazyStep_challenge_some, expect_const]
        exact ih _ (some c, L) hs
      | none =>
        have hmsg : (AdaptiveCPA.msgOf n b (List.ofFn mm)).length = n := by
          have : (List.ofFn mm).length = n + n := by rw [List.length_ofFn, hi2]
          rw [AdaptiveCPA.msgOf_eq]
          cases b <;> simp [this]
        have hl := length_maskL f r hmsg
        have hrec : ∀ t : Fin (2 * n) → Bool,
            List.ofFn (padFin d (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b
              (List.ofFn mm))) (List.ofFn t))) =
            ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))) (List.ofFn t) := by
          intro t
          refine ofFn_padFin_of_length ?_
          rw [ctW_eq, length_pairEncode, length_pairEncode, List.length_ofFn, hl, List.length_ofFn,
            hd]
          omega
        have htbl : ∀ t : Fin (2 * n) → Bool,
            tagTbl ((some (padFin d (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b
              (List.ofFn mm))) (List.ofFn t))), L) : LSt n d) =
            tagTbl ((none, L) : LSt n d) ++ [(pairV n (List.ofFn r)
              (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))), t)] := by
          intro t
          rw [tagTbl_eq, tagTbl_eq, List.append_nil]
          simp only
          rw [hrec, pairW_eq, wR_ctW, wC_ctW, wT_ctW, padFin_ofFn]
        simp only [ettStep_challenge_none, lazyStep_challenge_none, encW_eq_ctW]
        by_cases hp : pairV n (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))) ∈
            (tagTbl ((none, L) : LSt n d)).map Prod.fst
        · have hy : ∀ R, ovr (tagTbl ((none, L) : LSt n d)) R (pairV n (List.ofFn r)
              (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))) =
              ovr (tagTbl ((none, L) : LSt n d)) (fun _ => pairV n (List.ofFn r)
                (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))) (pairV n (List.ofFn r)
                (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))) := fun R => ovr_of_mem hp R _
          rw [tagOf_eq_ovr _ _ (fun _ => pairV n (List.ofFn r)
            (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))), if_pos hp]
          simp only [Option.getD_some, hy, expect_const]
          rw [← ih _ (some (padFin d (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b
            (List.ofFn mm))) (List.ofFn (ovr (tagTbl ((none, L) : LSt n d)) (fun _ => pairV n
              (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))))
              (pairV n (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))))))), L) hs,
            htbl]
          refine congrArg _ (funext fun R => ?_)
          rw [ovr_append_of_mem hp]
        · rw [tagOf_eq_ovr _ _ (fun _ => pairV n (List.ofFn r)
            (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))), if_neg hp]
          simp only [Option.getD_none]
          have e : ∀ R, ovr (tagTbl ((none, L) : LSt n d)) R (pairV n (List.ofFn r)
              (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))) =
              R (pairV n (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))) :=
            fun R => ovr_of_not_mem hp R
          simp only [e]
          rw [expect_sample_ovr (tagTbl ((none, L) : LSt n d)) hp (fun t g => expect (simulate
            (ettImpl ins outs d n f g true b) (k (padFin _ (ctW (List.ofFn r)
              (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))) (List.ofFn t))))
            (some (padFin d (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))
              (List.ofFn t))), keysL L)) fun p => G p.1)]
          refine congrArg _ (funext fun t => ?_)
          rw [← ih _ (some (padFin d (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b
            (List.ofFn mm))) (List.ofFn t))), L) hs, htbl]
          refine congrArg _ (funext fun R => ?_)
          rw [ovr_append_of_not_mem hp]

end LazyLaw

end TCSlib.Cryptography.Composability.ETTGame

## ===== TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Machines.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Efficiency.Strings
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.ChallengeSim
import TCSlib.Complexity.Randomized.Repetition

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine constructions for the encrypt-then-tag proof

Two generic constructions on machines used by the proof of [PS10, Theorem 170.4]
(`Composability.ccaScheme_cca2`); both are candidates for promotion.

* **A budget cap** (`exists_capMachine`): for a machine `A` and a polynomial `q` there is a machine
  `A'` that behaves as `A` with budget `q(n)` at every budget `K ≥ q(n)`: once its log holds `q(n)`
  entries, a query of `A` is replaced by the empty word, which every bit codec reads as the
  all-`false` output, the timeout of the bit codec. The PRF reduction of the encrypt-then-tag proof
  runs at parameter `2n` with budget `q(2n)` an adversary whose budget is `q(n)`.
* **Halving the parameter** (`exists_halfMachine`): for a next-query machine `B` there is a machine
  `D` whose oracle adversary at parameter `2n` accepts any oracle with the probability that `B`'s
  accepts it at parameter `n` (`NUPPT.exists_reparam_advice` with `φ m = m / 2`; the coins `D` does
  not read are an independent uniform factor).

## Main definitions

* `ETTGame.logCount`: the number of entries of a nested-pair log, in unary.

## Main results

* `ETTGame.length_logCount_encodeLog`: `logCount` counts the entries of an encoded log.
* `ETTGame.buildComp_cap`: a next-move function capped after `q` entries computes, at every budget
  `K ≥ q`, what the original computes with budget `q`.
* `ETTGame.exists_capMachine`, `ETTGame.exists_halfMachine`, `ETTGame.eval_toOracleAdversary_len`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (non-uniform machines) and Theorem 170.4 (book p. 170).
-/

namespace TCSlib.Cryptography.Composability.ETTGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

/-! ### Counting the entries of a log -/

/-- **The number of entries of a nested-pair log `⟨e₁, ⟨e₂, …⟩⟩`, in unary:** one `true` for every
nonempty suffix `pairSndD^[i] L`, `i ≤ |L|` (`cntRead`). -/
def logCount (L : List Bool) : List Bool :=
  (List.range (PolyExpr.var.eval L.length + 1)).flatMap fun i => cntRead (pairSndD^[i] L)

/-- `logCount L = ⋃_{i ≤ |L|} cntRead (pairSndD^[i] L)`. -/
theorem logCount_eq (L : List Bool) :
    logCount L =
      (List.range (PolyExpr.var.eval L.length + 1)).flatMap fun i => cntRead (pairSndD^[i] L) :=
  rfl

/-- The entry count is polynomial-time, `PolyTimeComputable logCount`, i.e.
`∃ M C c, M.ComputesFunInTime logCount (fun n => C * (n + 1)^c)`: an iterated emission
(`polyTimeComputable_iterateEmit`) along `pairSndD`, which does not lengthen its argument
(`length_pairSndD_le`). -/
theorem polyTimeComputable_logCount : PolyTimeComputable logCount := by
  have horb : ∀ (x : List Bool) (i : ℕ), (pairSndD^[i] x).length ≤ x.length := by
    intro x i
    induction i with
    | zero => exact le_rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact (length_pairSndD_le _).trans ih
  exact polyTimeComputable_iterateEmit polyTimeComputable_pairSndD polyTimeComputable_cntRead
    .var .var fun x i _ => by rw [PolyExpr.eval_var]; exact horb x i

/-- `#{i < N : i < L} = min N L`, as the length of an emission of `[true]` below `L`. -/
private theorem length_flatMap_range_lt (N L : ℕ) :
    ((List.range N).flatMap fun i => if i < L then [true] else []).length = min N L := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    by_cases h : N < L
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, if_pos h,
        List.length_singleton]
      omega
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, if_neg h, List.length_nil]
      omega

/-- An encoded log has at least as many bits as entries. -/
private theorem length_le_length_encodeLog {ι α : Type} {spec : OracleSpec ι}
    (codec : MachineCodec spec α) (h : QueryLog spec) : h.length ≤ (codec.encodeLog h).length := by
  induction h with
  | nil => simp
  | cons e h ih =>
    rw [MachineCodec.encodeLog_cons, length_pairEncode, List.length_cons]
    omega

/-- **`logCount` counts the entries of an encoded log:** `|logCount (codec.encodeLog h)| = |h|`.

**Proof sketch.** The `i`-th suffix of `encodeLog h` is `encodeLog (h.drop i)`
(`MachineCodec.encodeLog_cons`, `pairSndD_pairEncode`), nonempty exactly for `i < |h|`
(`pairEncode_ne_nil`); every entry adds at least two bits (`length_pairEncode`), so the range
`i ≤ |encodeLog h|` covers all of them (`length_flatMap_range_lt`). -/
theorem length_logCount_encodeLog {ι α : Type} {spec : OracleSpec ι} (codec : MachineCodec spec α)
    (h : QueryLog spec) : (logCount (codec.encodeLog h)).length = h.length := by
  have hsuf : ∀ (i : ℕ) (h : QueryLog spec),
      pairSndD^[i] (codec.encodeLog h) = codec.encodeLog (h.drop i) := by
    intro i
    induction i with
    | zero => intro h; rfl
    | succ i ih =>
      intro h
      cases h with
      | nil =>
        rw [List.drop_nil, Function.iterate_succ_apply, MachineCodec.encodeLog_nil]
        have : pairSndD ([] : List Bool) = [] := by
          have h1 := Complexity.BinArith.iterate_pairSndD_nil 1
          rwa [Function.iterate_one] at h1
        rw [this]
        have hn := ih []
        rwa [List.drop_nil, MachineCodec.encodeLog_nil] at hn
      | cons e h =>
        rw [Function.iterate_succ_apply, MachineCodec.encodeLog_cons, pairSndD_pairEncode, ih,
          List.drop_succ_cons]
  have hcnt : ∀ i : ℕ, cntRead (pairSndD^[i] (codec.encodeLog h)) =
      if i < h.length then [true] else [] := by
    intro i
    rw [hsuf, cntRead_eq]
    by_cases hi : i < h.length
    · rw [if_pos hi]
      obtain ⟨e, t, ht⟩ : ∃ e t, h.drop i = e :: t := by
        cases hd : h.drop i with
        | nil => rw [List.drop_eq_nil_iff] at hd; omega
        | cons e t => exact ⟨e, t, rfl⟩
      rw [ht, MachineCodec.encodeLog_cons, decide_eq_false (pairEncode_ne_nil _ _)]
      rfl
    · rw [if_neg hi, List.drop_eq_nil_of_le (by omega), MachineCodec.encodeLog_nil]
      rfl
  have hlen := length_le_length_encodeLog codec h
  rw [logCount_eq]
  simp only [hcnt]
  rw [length_flatMap_range_lt, PolyExpr.eval_var]
  omega

/-! ### Capping a next-move function -/

/-- **Budget cap for `buildComp`.** Let `next'` agree with `next` on logs shorter than `q`, and on
logs of length `q` return `next`'s output, or the timeout `t` in place of a query. Then from a log
of length `|hist| = q - j`, at every budget `K ≥ j`, the computation of `next'` is the computation
of `next` at budget `j`: `buildComp next' t K hist = buildComp next t j hist`.

**Proof sketch.** Induction on `j`. At `j = 0` the log has length `q`, and `next'` returns
(`buildComp_of_ret`) what `buildComp next t 0` returns: the output, or `t` for a query. Below `q`
the moves agree; a query is asked at budgets `K = K' + 1` and `j' + 1` and both continue from the
log extended by the answer. -/
theorem buildComp_cap {ι α : Type} {spec : OracleSpec ι} (next next' : QueryLog spec → Move spec α)
    (t : α) (q : ℕ) (h₁ : ∀ hist : QueryLog spec, hist.length < q → next' hist = next hist)
    (h₂ : ∀ hist : QueryLog spec, hist.length = q →
      (∀ a, next hist = .ret a → next' hist = .ret a) ∧
        (∀ i x, next hist = .query i x → next' hist = .ret t)) :
    ∀ (j K : ℕ) (hist : QueryLog spec), hist.length + j = q → j ≤ K →
      buildComp next' t K hist = buildComp next t j hist := by
  intro j
  induction j with
  | zero =>
    intro K hist hq _
    obtain ⟨hr, hqy⟩ := h₂ hist (by omega)
    cases h : next hist with
    | ret a => rw [buildComp_of_ret (hr a h), buildComp_zero_of_ret h]
    | query i x => rw [buildComp_of_ret (hqy i x h), buildComp_zero_of_query h]
  | succ j ih =>
    intro K hist hq hK
    obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have hn := h₁ hist (by omega)
    cases h : next hist with
    | ret a =>
      rw [buildComp_succ_of_ret (hn.trans h), buildComp_succ_of_ret h]
    | query i x =>
      rw [buildComp_succ_of_query (hn.trans h), buildComp_succ_of_query h]
      congr 1
      funext y
      exact ih K _ (by rw [List.length_append, List.length_singleton]; omega) (by omega)

/-- A word with first component `[false]` decodes as a query or as the default output:
`pairFstD w = [false] → decodeBitMove din dout dα w = ret a → a = zeroBits dα`.

**Proof sketch.** Such a word is not a canonical output word, whose first component is `[true]`
(`pairFstD_pairEncode`); if it is not a canonical query word either, it decodes to the default
(`decodeBitMove_of_not_canonical`); a canonical query word decodes as a query
(`decodeBitMove_query`). -/
private theorem eq_zeroBits_of_pairFstD_false {k : ℕ} {din dout : Fin k → ℕ} {dα : ℕ}
    {w : List Bool} (hw : pairFstD w = [false]) {a : Fin dα → Bool}
    (ha : decodeBitMove din dout dα w = .ret a) : a = zeroBits dα := by
  by_cases hq : ∃ (i : Fin k) (x : Fin (din i) → Bool),
      w = pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x))
  · obtain ⟨i, x, rfl⟩ := hq
    rw [decodeBitMove_query] at ha
    cases ha
  · push_neg at hq
    have hr : ∀ a' : Fin dα → Bool, w ≠ pairEncode [true] (List.ofFn a') := by
      intro a' h
      rw [h, pairFstD_pairEncode] at hw
      cases hw
    rw [decodeBitMove_of_not_canonical hq hr] at ha
    cases ha
    rfl

/-- The empty word decodes to the default output: `decodeBitMove din dout dα [] = ret 0^{dα}`. -/
private theorem decodeBitMove_nil {k : ℕ} (din dout : Fin k → ℕ) (dα : ℕ) :
    decodeBitMove din dout dα [] = .ret (zeroBits dα) :=
  decodeBitMove_of_not_canonical (fun _ _ h => pairEncode_ne_nil _ _ h.symm)
    (fun _ h => pairEncode_ne_nil _ _ h.symm)

/-- A query word has first component `[false]`:
`decodeBitMove din dout dα w = query i x → pairFstD w = [false]`. -/
private theorem pairFstD_of_query {k : ℕ} {din dout : Fin k → ℕ} {dα : ℕ} {w : List Bool}
    {i : Fin k} {x : Fin (din i) → Bool} (h : decodeBitMove din dout dα w = .query i x) :
    pairFstD w = [false] := by
  rw [decodeBitMove_eq_query_iff.1 h, pairFstD_pairEncode]

/-- The raw function of the capped machine: `A`'s output, except that once the argument (the
encoded log) has `q(n)` entries, an output with first component `[false]` (a query word) becomes
the empty word: `capRaw A q z = if |logCount (inArg z)| = q(|inParam z|) ∧
pairFstD (A.output z) = [false] then [] else A.output z`. -/
noncomputable def capRaw (A : NUPPT) (q : PolyExpr) (z : List Bool) : List Bool :=
  if decide ((logCount (NUPPT.inArg z)).length = q.eval (NUPPT.inParam z).length) &&
      decide (pairFstD (A.output z) = [false]) then [] else A.output z

/-- `capRaw A q z = if |logCount (inArg z)| = q(|inParam z|) ∧ pairFstD (A.output z) = [false]
then [] else A.output z`. -/
theorem capRaw_eq (A : NUPPT) (q : PolyExpr) (z : List Bool) :
    capRaw A q z =
      if decide ((logCount (NUPPT.inArg z)).length = q.eval (NUPPT.inParam z).length) &&
          decide (pairFstD (A.output z) = [false]) then [] else A.output z :=
  rfl

/-- The capped raw function is polynomial-time, `PolyTimeComputable (capRaw A q)`, i.e.
`∃ M C c, M.ComputesFunInTime (capRaw A q) (fun n => C * (n + 1)^c)`: the entry count
(`polyTimeComputable_logCount`), a length comparison with `1^{q(n)}` (`EffFill.lenEq_poly`,
`polyTimeComputable_unaryPoly`), a word comparison (`polyTimeComputable_pairEq`) and `A`'s output.
-/
theorem polyTimeComputable_capRaw (A : NUPPT) (q : PolyExpr) :
    PolyTimeComputable (capRaw A q) := by
  have hc := EffFill.lenEq_poly (polyTimeComputable_logCount.comp NUPPT.polyTimeComputable_inArg)
    ((polyTimeComputable_unaryPoly q).comp NUPPT.polyTimeComputable_inParam)
  have he : PolyTimeComputable fun z => [decide (pairFstD (A.output z) = [false])] :=
    (polyTimeComputable_pairEq.comp ((polyTimeComputable_pairFstD.comp
      A.polyTimeComputable_output).pairEncode (polyTimeComputable_const [false]))).congr fun z => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  refine (polyTimeComputable_ite (polyTimeComputable_and hc he) (polyTimeComputable_const [])
    A.polyTimeComputable_output).congr fun z => ?_
  simp only [Function.comp_apply, List.length_replicate, capRaw_eq]

/-- **A budget cap** (generic; candidate for promotion). For a machine `A` and a polynomial `q`
there is a machine `A'` with `A`'s coins whose computation through any bit codec, at any budget
`K ≥ q(n)`, is `A`'s computation at budget `q(n)`:
`A'.toComp (bitCodec ins outs dα) n K (coinsCongr h n r) =
A.toComp (bitCodec ins outs dα) n (q n) r`.

**Proof sketch.** `A' := NUPPT.ofPolyTime` of `capRaw A q` with `A`'s coins and advice
(`runAtL_ofPolyTime`). On the encoded log of `hist` the entry count is `|hist|`
(`length_logCount_encodeLog`). Below `q(n)` entries the move is `A`'s; at `q(n)` entries a query
word becomes the empty word, which decodes to the all-`false` output (`decodeBitMove_nil`, the
codec's timeout), and an output word with first component `[false]` already decoded to it
(`eq_zeroBits_of_pairFstD_false`); `buildComp_cap` concludes. -/
theorem exists_capMachine (A : NUPPT) (q : PolyExpr) :
    ∃ (A' : NUPPT) (h : A.coins = A'.coins), ∀ (n : ℕ) {k : ℕ} (ins outs : Fin k → ℕ)
      (dα K : ℕ) (r : A.Coins n), q.eval n ≤ K →
      A'.toComp (bitCodec ins outs dα) n K (NUPPT.coinsCongr h n r) =
        A.toComp (bitCodec ins outs dα) n (q.eval n) r := by
  refine ⟨NUPPT.ofPolyTime (polyTimeComputable_capRaw A q) A.coins A.adv A.advice
    A.advice_length, (NUPPT.coins_ofPolyTime _ _ _ _ _).symm, fun n k ins outs dα K r hK => ?_⟩
  have hrun : ∀ y, (NUPPT.ofPolyTime (polyTimeComputable_capRaw A q) A.coins A.adv A.advice
      A.advice_length).runAt n y (NUPPT.coinsCongr (NUPPT.coins_ofPolyTime _ _ _ _ _).symm n r) =
      if decide ((logCount y).length = q.eval n) && decide (pairFstD (A.runAt n y r) = [false])
      then [] else A.runAt n y r := by
    intro y
    rw [NUPPT.runAt_coinsCongr, NUPPT.runAtL_ofPolyTime, capRaw_eq, NUPPT.runAt_eq A,
      NUPPT.runAtL_eq A, NUPPT.inArg_eq, NUPPT.inParam_eq, NUPPT.advInput_eq]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
  rw [NUPPT.toComp_eq, NUPPT.toComp_eq, bitCodec_timeout]
  refine buildComp_cap _ _ _ (q.eval n) (fun hist hl => ?_) (fun hist hl => ⟨?_, ?_⟩) (q.eval n)
    K [] (by simp) hK
  · rw [bitCodec_decodeMove, bitCodec_decodeMove, hrun, length_logCount_encodeLog,
      decide_eq_false (Nat.ne_of_lt hl), Bool.false_and, if_neg Bool.false_ne_true]
  · intro a ha
    rw [bitCodec_decodeMove] at ha ⊢
    rw [hrun, length_logCount_encodeLog, decide_eq_true hl, Bool.true_and]
    by_cases hw : pairFstD (A.runAt n ((bitCodec ins outs dα).encodeLog hist) r) = [false]
    · rw [decide_eq_true hw, if_pos rfl, decodeBitMove_nil, eq_zeroBits_of_pairFstD_false hw ha]
    · rw [decide_eq_false hw, if_neg Bool.false_ne_true, ha]
  · intro i x hx
    rw [bitCodec_decodeMove] at hx ⊢
    rw [hrun, length_logCount_encodeLog, decide_eq_true hl, Bool.true_and,
      decide_eq_true (pairFstD_of_query hx), if_pos rfl, decodeBitMove_nil]

/-! ### Halving the parameter of a next-query machine -/

/-- **Halving the parameter** (generic; candidate for promotion). For a next-query machine `B`
there is a machine `D` whose oracle adversary at parameter `2n` accepts every oracle `h` with the
probability that `B`'s accepts it at parameter `n`, for all oracle lengths and budgets:
`𝔼_c [D^h(2n; c)] = 𝔼_c [B^h(n; c)]`.

**Proof sketch.** `D := NUPPT.exists_reparam_advice B (· / 2) var`: at parameter `2n` it runs
`B` at `2n / 2 = n` on the first `B.coinLen n` of its `B.coinLen (2n)` coins
(`PolyExpr.eval_subst`, `PolyExpr.eval_mono`). Split `D`'s coins as `B`'s coins and the rest
(`EnsembleLemmas.coinsEquiv`, `take_ofFn_coinsEquiv`); the trees agree (`toOracleAdversary_eq`)
and the unread coins average out (`expect_sample_prod`, `expect_const`). -/
theorem exists_halfMachine (B : NUPPT) :
    ∃ D : NUPPT, ∀ (n ℓ₁ ℓ₂ K : ℕ) (h : (Fin ℓ₁ → Bool) → (Fin ℓ₂ → Bool)),
      expect (sample (D.Coins (2 * n)))
          (fun c => if (D.toOracleAdversary (2 * n) ℓ₁ ℓ₂ K c).eval h = true then (1 : ℝ) else 0) =
        expect (sample (B.Coins n))
          (fun c => if (B.toOracleAdversary n ℓ₁ ℓ₂ K c).eval h = true then (1 : ℝ) else 0) := by
  obtain ⟨D, hDc, hD⟩ := B.exists_reparam_advice (fun m => m / 2) .var
    (fun m => by rw [PolyExpr.eval_var]; exact Nat.div_le_self m 2)
  refine ⟨D, fun n ℓ₁ ℓ₂ K h => ?_⟩
  have h2 : 2 * n / 2 = n := by omega
  have hle : B.coinLen n ≤ B.coinLen (2 * n) := by
    rw [NUPPT.coinLen_eq, NUPPT.coinLen_eq]
    exact B.coins.eval_mono (by omega)
  have hlen : D.coinLen (2 * n) = B.coinLen n + (B.coinLen (2 * n) - B.coinLen n) := by
    rw [NUPPT.coinLen_eq, hDc, PolyExpr.eval_subst, PolyExpr.eval_var, ← NUPPT.coinLen_eq]
    omega
  rw [← expect_sample_equiv (EnsembleLemmas.coinsEquiv hlen), ChallengeSim.expect_sample_prod]
  refine congrArg _ (funext fun c₁ => ?_)
  refine (congrArg _ (funext fun c₂ => ?_)).trans (expect_const _ _)
  have hrun :
      ∀ y, D.runAt (2 * n) y (EnsembleLemmas.coinsEquiv hlen (c₁, c₂)) = B.runAt n y c₁ := by
    intro y
    rw [NUPPT.runAt_eq D, hD, NUPPT.runAt_eq B]
    simp only [h2]
    rw [EnsembleLemmas.take_ofFn_coinsEquiv]
  rw [NUPPT.toOracleAdversary_eq, NUPPT.toOracleAdversary_eq]
  simp only [hrun]

/-- **An oracle adversary read at equal widths** (generic; the width-changing form of
`PRFGame.eval_toOracleAdversary_width`, which fixes the widths to the parameter): for `ℓ = ℓ'`,
running `D.toOracleAdversary n ℓ ℓ K c` against `f` is running `D.toOracleAdversary n ℓ' ℓ' K c`
against `f` with its inputs and outputs read at width `ℓ'`.

**Proof sketch.** Substitute `ℓ' = ℓ`; the readings are identities (`padFin_ofFn`). -/
theorem eval_toOracleAdversary_len (D : NUPPT) (n K : ℕ) (c : D.Coins n) {ℓ ℓ' : ℕ}
    (h : ℓ' = ℓ) (f : (Fin ℓ → Bool) → (Fin ℓ → Bool)) :
    (D.toOracleAdversary n ℓ ℓ K c).eval f =
      (D.toOracleAdversary n ℓ' ℓ' K c).eval
        (fun x => padFin ℓ' (List.ofFn (f (padFin ℓ (List.ofFn x))))) := by
  subst h
  have e : (fun x => padFin ℓ' (List.ofFn (f (padFin ℓ' (List.ofFn x))))) = f := by
    funext x
    rw [padFin_ofFn, padFin_ofFn]
  rw [e]

end TCSlib.Cryptography.Composability.ETTGame

## ===== TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Reduction.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Handler
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Machines
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Reduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The tag-key PRF reduction for the encrypt-then-tag scheme

The reduction of [PS10, Theorem 170.4], step 1, as a next-query oracle machine at parameter `2n`:
the budget cap of the adversary (`exists_capMachine`), the input-free companion
(`Games.exists_toCompOn_of_toComp`), T2 (`Games.exists_interactiveHandlerMachine`) applied to the
handler `dHandler` with the budget `q(2n)`, T4 (`Games.exists_toOracleAdversary_of_bitCodec`) at
the length `2n`, and the parameter halving (`exists_halfMachine`). Its acceptance probability at
parameter `2n` against any function `g` on `2n` bits is the acceptance probability of the CCA2
experiment with `f_{k₁}` and `g` (`exists_tagReduction`).

The proof answers the handler's outer queries by `g` (`gOuter`) and composes the two
implementations (`QueryImpl.comp`). Each composed call, from the encoded state `dState j o`, is the
call of `ettTape` from `((o, T), j)` with the handler's tapes in advance (`comp_dAbs`), as long as
`j` is below the number `q(2n)` of tapes; the capped adversary asks at most `q(n) ≤ q(2n)` queries,
so this holds along every run (`Games.simulate_eq_of_abs_bounded`). Drawing the seed uniformly
gives the key and fresh nonces (`expect_ettTape`).

## Main definitions

* `ETTGame.gOuter`: the outer oracle answering with `g`.
* `ETTGame.dAbs`: the handler's state as a function of `ettTape`'s state.

## Main results

* `ETTGame.comp_dAbs`: one composed call is a call of `ettTape`.
* `ETTGame.exists_tagReduction`: the reduction.
* `ETTGame.prfAdv_eq_expect`: the PRF advantage as expectations.
* `ETTGame.exists_tagStep`: step 1, the gap to the random tag function is a PRF advantage at `2n`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 170.4 (book p. 170).
-/

namespace TCSlib.Cryptography.Composability.ETTGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

/-! ### The outer oracle and the composed calls -/

/-- **The outer oracle answering with `g`:** a query `x` is answered `g x`, lengths adjusted,
`gOuter n g i x s = pure (padFin _ ⟦g (padFin (2n) ⟦x⟧)⟧, s)`. -/
noncomputable def gOuter (n : ℕ) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) :
    QueryImpl (bitSpecAt tagOut tagOut n) Unit unifSpec :=
  QueryImpl.ofComp fun _ x => .pure (padFin _ (List.ofFn (g (padFin (2 * n) (List.ofFn x)))))

/-- `gOuter n g i x s = pure (padFin _ ⟦g (padFin (2n) ⟦x⟧)⟧, s)`. -/
theorem gOuter_apply (n : ℕ) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (i : Fin 1)
    (x : (bitSpecAt tagOut tagOut n).dom i) (s : Unit) :
    gOuter n g i x s = .pure (padFin _ (List.ofFn (g (padFin (2 * n) (List.ofFn x)))), s) := by
  rw [gOuter, QueryImpl.ofComp_apply, OracleComp.pure_bind]

section Composed

variable (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
  (E : List Bool → List Bool) (hE : PolyTimeComputable E)
  (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (F n s x))
  (q : PolyExpr) (b : Bool) (n : ℕ) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))
  (z : List Bool) (k : Fin n → Bool) (W : Fin (q.eval n * n) → Bool)

/-- The handler's state and the (trivial) outer state, as functions of `ettTape`'s state:
`dAbs … (σ, j) = (dHState q E hE b n j σ.1, ())`. -/
def dAbs (s : St n (ettCt.eval n) × ℕ) :
    (Fin ((dHandler q E hE b).stateLen.eval n) → Bool) × Unit :=
  (dHState q E hE b n s.2 s.1.1, ())

/-- `dAbs q E hE b n s = (dHState q E hE b n s.2 s.1.1, ())`. -/
theorem dAbs_eq (s : St n (ettCt.eval n) × ℕ) :
    dAbs E hE q b n s = (dHState q E hE b n s.2 s.1.1, ()) :=
  rfl

/-- The tapes of the tape word, extended to every index (`AdaptiveCPA.extTape`):
`dTapes q n W = extTape (blocks (q n) n W)`. -/
noncomputable def dTapes : ℕ → Fin n → Bool :=
  AdaptiveCPA.extTape (EnsembleLemmas.blocks (q.eval n) n W)

/-- `dTapes q n W = extTape (blocks (q n) n W)`. -/
theorem dTapes_eq : dTapes q n W = AdaptiveCPA.extTape (EnsembleLemmas.blocks (q.eval n) n W) :=
  rfl

/-- Below `q(n)`, the extended tapes are the tapes: `dTapes q n W j = dTape q n W j hj`. -/
theorem dTapes_of_lt (j : ℕ) (hj : j < q.eval n) : dTapes q n W j = dTape q n W j hj := by
  rw [dTapes_eq, AdaptiveCPA.extTape_of_lt _ hj, dTape_eq]

/-- Reading the answer of `g` to a pair `r ‖ c₁` with `|r| = |c₁| = n` through the outer oracle:
`⟦padFin _ ⟦g (padFin (2n) ⟦padFin _ (r ++ c₁)⟧)⟧⟧ = tagL g r c₁`. -/
private theorem gOuter_pair {r c : List Bool} (hr : r.length = n) (hc : c.length = n) :
    List.ofFn (padFin ((tagOut 0).eval n) (List.ofFn (g (padFin (2 * n)
      (List.ofFn (padFin ((tagOut 0).eval n) (r ++ c))))))) = tagL g r c := by
  have h2 : (tagOut 0).eval n = 2 * n := by rw [tagOut_eq, tagLen_eval]
  have e1 : List.ofFn (padFin ((tagOut 0).eval n) (r ++ c)) = r ++ c :=
    ofFn_padFin_of_length (by rw [List.length_append, hr, hc, h2]; omega)
  rw [e1, ofFn_padFin_of_length (by rw [List.length_ofFn, h2]), tagL_eq, pairV_eq]

include hFE in
/-- **One composed call is a call of `ettTape` with the tapes in advance:** from the encoded state
`dState j o` with `j < q(n)`, the handler composed with `gOuter g` answers as `ettTape` with pad
function `f_k` and tag function `g` and the tapes `dTapes W` from `((o, T), j)`, both
deterministic, with the new state abstracted; the counter grows by one.

**Proof sketch.** By the oracle, the record, the refusal test and well-formedness: encryption and a
first challenge ask `g` at `r ‖ c₁` (`dHandler_impl_enc`, `dHandler_impl_challenge_none`); a
well-formed decryption that is not refused asks `g` at its pair (`dHandler_impl_dec_wf`); the
other calls answer directly. The outer oracle answers `g` (`gOuter_apply`, `gOuter_pair`), and the
answers are `ettStep`'s (`ettStep_enc`, …, `decAnsW_eq`). -/
theorem comp_dAbs (i : Fin 3) (x : (bitSpecAt ettDin ettDout n).dom i)
    (s : St n (ettCt.eval n) × ℕ) (hs : s.2 < q.eval n) :
    ∃ (y : (bitSpecAt ettDin ettDout n).rng i) (s' : St n (ettCt.eval n) × ℕ),
      ettTape (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n (F n k)
          g b (dTapes q n W) i x s = .pure (y, s') ∧ s'.2 ≤ s.2 + 1 ∧
      (gOuter n g).comp ((dHandler q E hE b).impl n z (dHSeed q E hE b n (k, W))) i x
          (dAbs E hE q b n s) = .pure (y, dAbs E hE q b n s') := by
  obtain ⟨⟨o, T⟩, j⟩ := s
  have hj : j < q.eval n := hs
  refine ⟨(ettStep (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
      (F n k) g false b (dTapes q n W j) i x (o, T)).1,
    ((ettStep (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
      (F n k) g false b (dTapes q n W j) i x (o, T)).2, j + 1),
    ettTape_apply (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
      (F n k) g b (dTapes q n W) i x (o, T) j, le_rfl, ?_⟩
  rw [dTapes_of_lt q n W j hj, QueryImpl.comp_apply, dAbs_eq]
  simp only
  match i, x with
  | 0, x =>
    have hx : (List.ofFn x).length = n := by
      rw [List.length_ofFn]
      show (ettDin 0).eval n = n
      rw [ettDin_zero, PolyExpr.eval_var]
    rw [dHandler_impl_enc q E hE b F hFE n z k W x j o hj, simulate_query, gOuter_apply,
      OracleComp.pure_bind, simulate_pure, OracleComp.pure_bind, ettStep_enc, dAbs_eq,
      gOuter_pair n g List.length_ofFn (length_maskL (F n k) _ hx), ← encW_eq]
  | 1, x =>
    rw [ettStep_dec, decAnsW_eq]
    by_cases href : refW o (List.ofFn x) = true
    · rw [dHandler_impl_dec_ref q E hE b n z k W x j o hj href, simulate_pure,
        OracleComp.pure_bind, dAbs_eq]
      simp only [href, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false]
    · rw [Bool.not_eq_true] at href
      by_cases hwf : wfW n (List.ofFn x) = true
      · have hwf' := hwf
        rw [wfW_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hwf'
        rw [dHandler_impl_dec_wf q E hE b F hFE n z k W x j o hj href hwf, simulate_query,
          gOuter_apply, OracleComp.pure_bind, simulate_pure, OracleComp.pure_bind, dAbs_eq,
          gOuter_pair n g hwf'.1 hwf'.2, validW_eq, hwf, href]
        simp only [Bool.not_false, Bool.true_and, Bool.true_or, Bool.and_true, decide_eq_true_eq]
        by_cases ht : tagL g (wR (List.ofFn x)) (wC (List.ofFn x)) = wT (List.ofFn x)
        · rw [if_pos ht, if_pos ht.symm]
        · rw [if_neg ht, if_neg (Ne.symm ht)]
      · rw [Bool.not_eq_true] at hwf
        rw [dHandler_impl_dec_nwf q E hE b n z k W x j o hj href hwf, simulate_pure,
          OracleComp.pure_bind, dAbs_eq, validW_eq, hwf]
        simp only [Bool.false_and, Bool.and_false, Bool.false_eq_true, if_false]
  | 2, x =>
    cases o with
    | some c =>
      rw [dHandler_impl_challenge_some q E hE b n z k W x j c hj, simulate_pure,
        OracleComp.pure_bind, ettStep_challenge_some, dAbs_eq]
    | none =>
      have hmsg : (AdaptiveCPA.msgOf n b (List.ofFn x)).length = n := by
        have hx : (List.ofFn x).length = n + n := by
          rw [List.length_ofFn]
          show (ettDin 2).eval n = n + n
          rw [ettDin_two, PolyExpr.eval_add, PolyExpr.eval_var]
        rw [AdaptiveCPA.msgOf_eq]
        cases b <;> simp [hx]
      rw [dHandler_impl_challenge_none q E hE b F hFE n z k W x j hj, simulate_query,
        gOuter_apply, OracleComp.pure_bind, simulate_pure, OracleComp.pure_bind,
        ettStep_challenge_none, dAbs_eq,
        gOuter_pair n g List.length_ofFn (length_maskL (F n k) _ hmsg), ← encW_eq]

end Composed

/-! ### The reduction -/

/-- The budget `q(2n)` of the handler's adversary: `(q.subst tagLen).eval n = q(2n)`. -/
theorem eval_subst_tagLen (q : PolyExpr) (n : ℕ) : (q.subst tagLen).eval n = q.eval (2 * n) := by
  rw [PolyExpr.eval_subst, tagLen_eval]

/-- **The experiment does not see the output width:** for `d = d'`, the expected first output bit
of the run through `bitCodec ins outs d` and through `bitCodec ins outs d'` agree.

**Proof sketch.** Substitute `d = d'`. -/
theorem expect_ettImpl_outLen {ins outs : Fin 3 → ℕ} {c n : ℕ} {d d' : ℕ} (hd : d = d')
    (f : (Fin n → Bool) → (Fin n → Bool)) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))
    (rej b : Bool) (A : NUPPT) (Q : ℕ) (r : A.Coins n) :
    expect (simulate (ettImpl ins outs c n f g rej b) (A.toComp (bitCodec ins outs d) n Q r)
        (none, [])) (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) =
      expect (simulate (ettImpl ins outs c n f g rej b) (A.toComp (bitCodec ins outs d') n Q r)
        (none, [])) (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
  subst hd
  rfl

section Reduction

variable (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
  (E : List Bool → List Bool) (hE : PolyTimeComputable E)
  (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (F n s x))

include hE hFE in
/-- **The tag-key PRF reduction** [PS10, Theorem 170.4, step 1]: for a machine adversary `A` with
budget `q` and a challenge bit `b`, there is a next-query machine `D` such that, at every `n` and
for every function `g` on `2n` bits, `D` at parameter `2n` with budget `q(2n)` accepts against `g`
with the probability that `A` outputs `1` in the CCA2 experiment with `f_k` (`k` a uniform `n`-bit
key) and `g` in place of `f_{k₂}` (the oracles `ettImpl … false b`, on the lengths `ettDin`,
`ettDout`):
`𝔼_c [D^g(2n; c) = 1] = 𝔼_k 𝔼_r 𝔼[⟦A's output⟧₀ = 1 | simulate (ettImpl … f_k g false b) (A …) ∅]`.

**Proof sketch.** `D` is the halving (`exists_halfMachine`) of T4 at length `2n` applied to T2's
machine `B` for `dHandler` with budget `q(2n)` and the input-free companion of the capped adversary
(`exists_capMachine`). Its coins at `2n` are, through the halving and the bijections of T4, T2, the
companion and the cap, a seed `(k, W)` and `A`'s coins `r` (`expect_sample_equiv`,
`ChallengeSim.expect_sample_prod`, `expect_sample_comm`). For fixed seed and coins, T4 and T2 turn
`D`'s run against `g` into the evaluation, with `g`, of the reduction; evaluation is simulation
with `gOuter g` (`simulate_ofComp_pure`), which composes with the handler (`simulate_bind`,
`simulate_comp`, `dHandler_finish`); along the adversary's run (at most `q(2n)` queries) the
composite is `ettTape` with the tapes of `W` (`simulate_eq_of_abs_bounded`, `comp_dAbs`). Drawing
`W` uniformly gives fresh nonces (`expect_ettTape`), and the capped adversary at budget `q(2n)` is
`A` at budget `q(n)` (`exists_capMachine`). Widths are transported by
`eval_toOracleAdversary_len`, `PRFGame.ofFn_evalFn_toCompOn` and `expect_ettImpl_outLen`. -/
theorem exists_tagReduction (A : NUPPT) (q : PolyExpr) (b : Bool) :
    ∃ D : NUPPT, ∀ (n : ℕ) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)),
      expect (sample (D.Coins (2 * n)))
          (fun c =>
            if (D.toOracleAdversary (2 * n) (2 * n) (2 * n) (q.eval (2 * n)) c).eval g = true
            then (1 : ℝ) else 0) =
        expect (sample (Fin n → Bool)) fun k => expect (sample (A.Coins n)) fun r =>
          expect (simulate (ettImpl (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
              (ettCt.eval n) n (F n k) g false b)
              (A.toComp (bitCodec (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) 1) n
                (q.eval n) r) (none, []))
            (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
  obtain ⟨A₁, hA₁c, hA₁⟩ := exists_capMachine A q
  obtain ⟨A₂, -, hA₂⟩ := exists_toCompOn_of_toComp A₁
  obtain ⟨B, hB⟩ := exists_interactiveHandlerMachine A₂ (q.subst tagLen) ettDin ettDout tagOut
    tagOut (.const 1) (dHandler (q.subst tagLen) E hE b)
  obtain ⟨B', -, hB'⟩ := exists_toOracleAdversary_of_bitCodec B tagLen tagLen
  obtain ⟨D, hD⟩ := exists_halfMachine B'
  refine ⟨D, fun n g => ?_⟩
  obtain ⟨φ₀, hφ₀⟩ := hA₂ n
  obtain ⟨φ₂, hφ₂⟩ := hB n
  obtain ⟨φ₄, hφ₄⟩ := hB' n
  have hq₂ : (q.subst tagLen).eval n = q.eval (2 * n) := eval_subst_tagLen q n
  have hQ : (q.subst tagLen).eval n * (dHandler (q.subst tagLen) E hE b).perCall.eval n +
      (dHandler (q.subst tagLen) E hE b).finCall.eval n = q.eval (2 * n) := by
    rw [dHandler_perCall, dHandler_finCall, PolyExpr.eval_const, PolyExpr.eval_const, hq₂]
    ring
  have hout : (dHandler (q.subst tagLen) E hE b).outLen.eval n = 1 := by
    rw [dHandler_outLen, PolyExpr.eval_const]
  have hle : q.eval n ≤ (q.subst tagLen).eval n := by
    rw [hq₂]
    exact q.eval_mono (by omega)
  -- `D`'s coins at `2n` are `B'`'s at `n`, then a seed and `A`'s coins.
  rw [hD n (2 * n) (2 * n) (q.eval (2 * n)) g, ← expect_sample_equiv φ₄, ← expect_sample_equiv φ₂,
    ChallengeSim.expect_sample_prod, expect_sample_comm, ← expect_sample_equiv φ₀,
    ← expect_sample_equiv (NUPPT.coinsCongr hA₁c n)]
  conv_rhs => rw [expect_sample_comm]
  refine congrArg _ (funext fun r => ?_)
  rw [← expect_sample_equiv (dHSeed (q.subst tagLen) E hE b n), ChallengeSim.expect_sample_prod]
  refine congrArg _ (funext fun k => ?_)
  -- One run of `D` is the reduction evaluated with `g`.
  have hrun : ∀ W : Fin ((q.subst tagLen).eval n * n) → Bool,
      (if (B'.toOracleAdversary n (2 * n) (2 * n) (q.eval (2 * n))
          (φ₄ (φ₂ (dHSeed (q.subst tagLen) E hE b n (k, W),
            φ₀ (NUPPT.coinsCongr hA₁c n r))))).eval g = true then (1 : ℝ) else 0) =
      expect (simulate (ettTape (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
          (ettCt.eval n) n (F n k) g b (dTapes (q.subst tagLen) n W))
          (A₂.toCompOn (bitCodec (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
            ((PolyExpr.const 1).eval n)) n ((q.subst tagLen).eval n) []
            (φ₀ (NUPPT.coinsCongr hA₁c n r))) ((none, []), 0))
        (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
    intro W
    have key : ∀ v : Fin 1 → Bool, (if v 0 = true then (1 : ℝ) else 0) =
        if (List.ofFn v).headD false = true then 1 else 0 := fun v => by
      rw [headD_ofFn_one]
    have h2 : _ = B.toCompOn (bitCodec (fun _ : Fin 1 => tagLen.eval n)
        (fun _ => tagLen.eval n) ((dHandler (q.subst tagLen) E hE b).outLen.eval n)) n
        ((q.subst tagLen).eval n * (dHandler (q.subst tagLen) E hE b).perCall.eval n +
          (dHandler (q.subst tagLen) E hE b).finCall.eval n)
        [] (φ₂ (dHSeed (q.subst tagLen) E hE b n (k, W), φ₀ (NUPPT.coinsCongr hA₁c n r))) :=
      hφ₂ [] (dHSeed (q.subst tagLen) E hE b n (k, W)) (φ₀ (NUPPT.coinsCongr hA₁c n r))
    rw [eval_toOracleAdversary_len B' n _ _ (tagLen_eval n), hφ₄, ← hQ, key,
      PRFGame.ofFn_evalFn_toCompOn hout.symm B n _ [] _, ← h2, dHandler_advInput]
    have hev : simulate (gOuter n g) ((simulate ((dHandler (q.subst tagLen) E hE b).impl n []
        (dHSeed (q.subst tagLen) E hE b n (k, W)))
        (A₂.toCompOn (bitCodec (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
          ((PolyExpr.const 1).eval n)) n ((q.subst tagLen).eval n) []
          (φ₀ (NUPPT.coinsCongr hA₁c n r)))
        ((dHandler (q.subst tagLen) E hE b).init n)).bind
        (fun res => (dHandler (q.subst tagLen) E hE b).finish n []
          (dHSeed (q.subst tagLen) E hE b n (k, W)) res.2 res.1)) () = _ :=
      simulate_ofComp_pure _ _ _
    have h1 := congrArg (fun c => expect c
      (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0)) hev
    simp only [expect_pure] at h1
    refine h1.symm.trans ?_
    rw [simulate_bind, simulate_comp, OracleComp.bind_assoc, expect_bind]
    simp only [OracleComp.pure_bind, dHandler_finish, simulate_pure, expect_pure]
    rw [dHandler_init_hstate, show (dHState (q.subst tagLen) E hE b n 0 none, ()) =
        dAbs E hE (q.subst tagLen) b n ((none, []), 0) from
          (dAbs_eq E hE (q.subst tagLen) b n ((none, []), 0)).symm,
      simulate_eq_of_abs_bounded _ _ (dAbs E hE (q.subst tagLen) b n) (fun s => s.2)
        ((q.subst tagLen).eval n)
        (fun i x s hs => comp_dAbs F E hE hFE (q.subst tagLen) b n g [] k W i x s hs) _
        ((q.subst tagLen).eval n) (A₂.toCompOn_costBoundedBy _ n _ _ _) ((none, []), 0)
        (Nat.zero_add _).le,
      expect_bind]
    simp only [expect_pure]
    refine congrArg _ (funext fun p => ?_)
    rw [ofFn_padFin_of_length (by rw [List.length_ofFn, dHandler_outLen])]
  simp only [hrun, dTapes_eq]
  rw [expect_sample_equiv (EnsembleLemmas.blocks ((q.subst tagLen).eval n) n) (fun T =>
      expect (simulate (ettTape (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
          (ettCt.eval n) n (F n k) g b (AdaptiveCPA.extTape T))
          (A₂.toCompOn (bitCodec (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
            ((PolyExpr.const 1).eval n)) n ((q.subst tagLen).eval n) []
            (φ₀ (NUPPT.coinsCongr hA₁c n r))) ((none, []), 0))
        (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0)),
    expect_ettTape _ _ _ _ _ _ _ ((q.subst tagLen).eval n)
      (fun a => if (List.ofFn a).headD false = true then (1 : ℝ) else 0) _
      ((q.subst tagLen).eval n) (A₂.toCompOn_costBoundedBy _ n _ _ _) (none, []) 0 (by omega),
    hφ₀, hA₁ n _ _ _ _ _ hle]
  exact expect_ettImpl_outLen (PolyExpr.eval_const 1 n) _ _ _ _ A _ r

/-- **The PRF advantage as expectations** (PRFGame overlap: `prfAdv_prfReduction`, re-derived here
in general form from the published readers): for an oracle adversary `A'` on `m`-bit strings,
`prfAdv F A' = |𝔼_k 𝔼_c [A'(c)^{F k} = 1] − 𝔼_R 𝔼_c [A'(c)^R = 1]|`.

**Proof sketch.** `prfAdv_def`, `distAdv_def`; each acceptance probability is an average over the
key (resp. the function table) and the coins (`Bridge.acceptProb_eq`, `accept_eq`,
`Bridge.acceptGame_eq`, `prob_bind`, `oracleDist_apply`, `randomFunction_apply`). -/
theorem prfAdv_eq_expect {m : ℕ} (Fm : (Fin m → Bool) → (Fin m → Bool) → (Fin m → Bool))
    {ρ : Type} [Fintype ρ] [Nonempty ρ] (A' : OracleAdversary ρ (Fin m → Bool) (Fin m → Bool)) :
    prfAdv Fm A' =
      |expect (sample (Fin m → Bool))
          (fun k => expect (sample ρ) fun c => if (A' c).eval (Fm k) = true then (1 : ℝ) else 0) -
        expect (sample ((Fin m → Bool) → (Fin m → Bool)))
          (fun R => expect (sample ρ) fun c => if (A' c).eval R = true then (1 : ℝ) else 0)| := by
  rw [prfAdv_def, distAdv_def, Bridge.acceptProb_eq, Bridge.acceptProb_eq, accept_eq, accept_eq,
    Bridge.acceptGame_eq, Bridge.acceptGame_eq, prob_bind, prob_bind]
  congr 2
  · refine congrArg _ (funext fun k => ?_)
    simp only [prob_bind, prob_pure, oracleDist_apply]
  · refine congrArg _ (funext fun R => ?_)
    simp only [prob_bind, prob_pure, oracleDist_apply, randomFunction_apply]

include hE hFE in
/-- **Step 1 of [PS10, Thm 170.4]: the tag key becomes a random function**,
`∃ D, ∀ n, |𝔼_{k₁} 𝔼_{k₂} ettAcc … (F n k₁) (F (2n) k₂) false b A (q n) -
𝔼_{k₁} 𝔼_R ettAcc … (F n k₁) R false b A (q n)| =
prfAdv (F (2n)) (D.toOracleAdversary (2n) (2n) (2n) (q (2n)))`.
For a machine adversary `A` with budget `q` and a challenge bit `b` there is a next-query machine
`D` such that at
every `n` the gap between the experiments with the tag functions `f_{k₂}` (`k₂` a uniform `2n`-bit
key) and a uniform random function on `2n` bits, the pad function being `f_{k₁}`, is the PRF
advantage of `D` at parameter `2n` with budget `q(2n)`.

**Proof sketch.** `exists_tagReduction` gives `D` and its acceptance probability against every `g`;
`prfAdv_eq_expect` writes the advantage as the gap between the averages over `k₂` and over the
function table; exchange the averages with the key `k₁` (`expect_sample_comm`). -/
theorem exists_tagStep (A : NUPPT) (q : PolyExpr) (b : Bool) :
    ∃ D : NUPPT, ∀ n : ℕ,
      |(expect (sample (Fin n → Bool)) fun k => expect (sample (Fin (2 * n) → Bool)) fun k₂ =>
          ettAcc (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
            (F n k) (F (2 * n) k₂) false b A (q.eval n)) -
        (expect (sample (Fin n → Bool)) fun k =>
          expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))) fun R =>
            ettAcc (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
              (F n k) R false b A (q.eval n))| =
        prfAdv (F (2 * n)) (D.toOracleAdversary (2 * n) (2 * n) (2 * n) (q.eval (2 * n))) := by
  obtain ⟨D, hD⟩ := exists_tagReduction F E hE hFE A q b
  refine ⟨D, fun n => ?_⟩
  rw [prfAdv_eq_expect]
  simp only [hD n, ettAcc_eq]
  rw [expect_sample_comm (α := Fin n → Bool) (β := Fin (2 * n) → Bool),
    expect_sample_comm (α := Fin n → Bool) (β := (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))]

end Reduction

end TCSlib.Cryptography.Composability.ETTGame

## ===== TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Tools.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Hopping
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Hybrid

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Simulation tools for the encrypt-then-tag proof

Generic facts on simulations of oracle computations used by the proof of [PS10, Theorem 170.4]
(`Composability.ccaScheme_cca2`). They are stated for arbitrary oracle specifications and are
candidates for promotion to the `Games` layer.

* **Simulation through a state abstraction, in law** (`expect_simulate_abs`): if every call of
  `impl₁` from the abstract image `f s` has the law of the call of `impl₂` from `s` with its new
  state abstracted, so do whole simulations, along runs within a query budget.
* **Coins in advance** (`expect_simulate_tapeImpl`): an implementation that draws one fresh coin
  `t` per query (`freshImpl`) has the law of the implementation that reads the `j`-th query's coin
  from a tape `T j` drawn in advance (`tapeImpl`), for computations with at most `κ` queries.
* **Functions overridden by a table** (`ovr`): `ovr M R` is `R` with the values of the table `M`
  written over it; resampling `R` at a point outside the table moves into the table
  (`expect_sample_ovr`).

## Main definitions

* `ETTGame.freshImpl`, `ETTGame.tapeImpl`: per-query coins drawn fresh, and read from tapes.
* `ETTGame.ovr`: a function overridden by a finite table.

## Main results

* `ETTGame.expect_simulate_abs`, `ETTGame.expect_simulate_abs_inv`,
  `ETTGame.expect_simulate_tapeImpl`, `ETTGame.expect_sample_ovr`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 170.4 (book p. 170).
-/

namespace TCSlib.Cryptography.Composability.ETTGame

open TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

/-! ### Simulation through a state abstraction, in law -/

section Abs

variable {ι : Type} {spec : OracleSpec ι} {σ₁ σ₂ α : Type}

/-- **Simulation through a state abstraction, in law, along runs with a query budget.** Let every
call of `impl₂` from a state `s` with `cnt s < κ` raise `cnt` by at most one, and give every
function `g` of the answer and the abstracted new state the expectation that the call of `impl₁`
from `f s` gives it. Then for a computation `c` with at most `m` queries and `cnt s + m ≤ κ`,
`𝔼[G] (simulate impl₁ c (f s)) = 𝔼[fun p => G (p.1, f p.2)] (simulate impl₂ c s)`.

**Proof sketch.** Induction on `c`. A query costs one unit, so it is asked from a state with
`cnt s < κ`: rewrite the call of `impl₁` by the hypothesis, and on each possible outcome of the
call of `impl₂` (where `cnt` grew by at most one) apply the induction hypothesis
(`expect_congr_of_allOutputs`). -/
theorem expect_simulate_abs (impl₁ : QueryImpl spec σ₁ unifSpec)
    (impl₂ : QueryImpl spec σ₂ unifSpec) (f : σ₂ → σ₁) (cnt : σ₂ → ℕ) (κ : ℕ)
    (h : ∀ i x s, cnt s < κ → ∀ g : spec.rng i × σ₁ → ℝ,
      expect (impl₁ i x (f s)) g = expect (impl₂ i x s) fun p => g (p.1, f p.2))
    (hcnt : ∀ i x s, cnt s < κ → (impl₂ i x s).AllOutputs fun p => cnt p.2 ≤ cnt s + 1)
    (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ₂)
    (hs : cnt s + m ≤ κ) (G : α × σ₁ → ℝ) :
    expect (simulate impl₁ c (f s)) G = expect (simulate impl₂ c s) fun p => G (p.1, f p.2) := by
  induction c generalizing m s with
  | pure a => simp only [simulate_pure, expect_pure]
  | query i x k ih =>
    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
    have hm1 : 1 ≤ m := hm
    rw [simulate_query, simulate_query, expect_bind, expect_bind, h i x s (by omega)]
    refine expect_congr_of_allOutputs (hcnt i x s (by omega)) fun p hp => ?_
    exact ih p.1 (m - 1) (hk p.1) p.2 (by omega)

/-- **Simulation through a state abstraction, in law, along runs with a query budget and an
invariant:** as `expect_simulate_abs`, with the hypotheses only on the states satisfying an
invariant `P` that every call of `impl₂` keeps: for `c` with at most `m` queries, `P s` and
`cnt s + m ≤ κ`, `𝔼[G | simulate impl₁ c (f s)] = 𝔼[fun p => G (p.1, f p.2) | simulate impl₂ c s]`.

**Proof sketch.** As `expect_simulate_abs`, carrying `P` through the possible outcomes. -/
theorem expect_simulate_abs_inv (impl₁ : QueryImpl spec σ₁ unifSpec)
    (impl₂ : QueryImpl spec σ₂ unifSpec) (f : σ₂ → σ₁) (P : σ₂ → Prop) (cnt : σ₂ → ℕ) (κ : ℕ)
    (h : ∀ i x s, P s → cnt s < κ → ∀ g : spec.rng i × σ₁ → ℝ,
      expect (impl₁ i x (f s)) g = expect (impl₂ i x s) fun p => g (p.1, f p.2))
    (hcnt : ∀ i x s, P s → cnt s < κ →
      (impl₂ i x s).AllOutputs fun p => P p.2 ∧ cnt p.2 ≤ cnt s + 1)
    (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ₂) (hP : P s)
    (hs : cnt s + m ≤ κ) (G : α × σ₁ → ℝ) :
    expect (simulate impl₁ c (f s)) G = expect (simulate impl₂ c s) fun p => G (p.1, f p.2) := by
  induction c generalizing m s with
  | pure a => simp only [simulate_pure, expect_pure]
  | query i x k ih =>
    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
    have hm1 : 1 ≤ m := hm
    rw [simulate_query, simulate_query, expect_bind, expect_bind, h i x s hP (by omega)]
    refine expect_congr_of_allOutputs (hcnt i x s hP (by omega)) fun p hp => ?_
    exact ih p.1 (m - 1) (hk p.1) p.2 hp.1 (by omega)

end Abs

/-! ### Coins drawn fresh and coins in advance -/

section Tapes

variable {ι : Type} {spec : OracleSpec ι} {σ τ α : Type}

/-- **One fresh coin per query:** the query `x` to oracle `i` in state `s` draws a uniform
`t ∈ τ`, then runs `K i x s t`. -/
noncomputable def freshImpl [Fintype τ] [Nonempty τ]
    (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ)) :
    QueryImpl spec σ unifSpec :=
  fun i x s => (sample τ).bind (K i x s)

/-- `freshImpl K i x s = (sample τ).bind (K i x s)`. -/
theorem freshImpl_apply [Fintype τ] [Nonempty τ]
    (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ)) (i : ι)
    (x : spec.dom i) (s : σ) : freshImpl K i x s = (sample τ).bind (K i x s) :=
  rfl

/-- **One coin per query, from tapes in advance:** the query `x` to oracle `i` in state `(s, j)`
runs `K i x s (T j)` and advances the query counter `j`,
`tapeImpl K T i x (s, j) = (K i x s (T j)).bind fun p => pure (p.1, (p.2, j + 1))`. -/
def tapeImpl (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ)) (T : ℕ → τ) :
    QueryImpl spec (σ × ℕ) unifSpec :=
  fun i x s => (K i x s.1 (T s.2)).bind fun p => .pure (p.1, (p.2, s.2 + 1))

/-- `tapeImpl K T i x (s, j) = (K i x s (T j)).bind fun p => pure (p.1, (p.2, j + 1))`. -/
theorem tapeImpl_apply (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ)) (T : ℕ → τ)
    (i : ι) (x : spec.dom i) (s : σ) (j : ℕ) :
    tapeImpl K T i x (s, j) = (K i x s (T j)).bind fun p => .pure (p.1, (p.2, j + 1)) :=
  rfl

/-- **The run from the counter `j` ignores the tapes below `j`:** if `T m = T' m` for every
`m ≥ j`, the runs of `tapeImpl K T` and `tapeImpl K T'` from `(s, j)` agree.

**Proof sketch.** Induction on the computation: a query at counter `j' ≥ j` reads `T j'` and
moves to `j' + 1`. -/
theorem simulate_tapeImpl_congr (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ))
    (T T' : ℕ → τ) (c : OracleComp spec α) (s : σ) (j : ℕ) (hT : ∀ m, j ≤ m → T m = T' m) :
    simulate (tapeImpl K T) c (s, j) = simulate (tapeImpl K T') c (s, j) := by
  induction c generalizing s j with
  | pure a => rw [simulate_pure, simulate_pure]
  | query i x k ih =>
    rw [simulate_query, simulate_query, tapeImpl_apply, tapeImpl_apply, hT j le_rfl,
      OracleComp.bind_assoc, OracleComp.bind_assoc]
    congr 1
    funext p
    rw [OracleComp.pure_bind, OracleComp.pure_bind]
    exact ih p.1 p.2 (j + 1) fun m hm => hT m (by omega)

/-- **Coins in advance have the law of fresh coins:** for a computation with at most `m` queries,
a counter `j` with `j + m ≤ κ`, and every function `G` of the output,
`𝔼_{T ← τ^κ} 𝔼[G (simulate (tapeImpl K (extTape T)) c (s, j))] = 𝔼[G (simulate (freshImpl K) c s)]`.

**Proof sketch.** Induction on `c`, generalizing the counter, the state and the budget. A query
costs one unit, so it reads the tape `T j` with `j < κ`; the continuation runs from `j + 1`, so it
ignores `T j` (`simulate_tapeImpl_congr`, `AdaptiveCPA.extTape_update`), and
`ProbComp.expect_sample_coord` replaces `T j` by the fresh coin of `freshImpl`
(`expect_expect_sample` exchanges the tape with the call). -/
theorem expect_simulate_tapeImpl [Fintype τ] [Nonempty τ]
    (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ))
    (κ : ℕ) (G : α → ℝ) (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m)
    (s : σ) (j : ℕ) (hj : j + m ≤ κ) :
    expect (sample (Fin κ → τ))
        (fun T => expect (simulate (tapeImpl K (AdaptiveCPA.extTape T)) c (s, j))
          fun p => G p.1) =
      expect (simulate (freshImpl K) c s) fun p => G p.1 := by
  induction c generalizing m s j with
  | pure a =>
    simp only [simulate_pure, expect_pure]
    exact expect_const _ _
  | query i x k ih =>
    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
    have hm1 : 1 ≤ m := hm
    have hjk : j < κ := by omega
    let jj : Fin κ := ⟨j, hjk⟩
    have hT : ∀ T : Fin κ → τ, AdaptiveCPA.extTape T j = T jj :=
      fun T => AdaptiveCPA.extTape_of_lt T hjk
    simp only [simulate_query, tapeImpl_apply, freshImpl_apply, OracleComp.bind_assoc,
      OracleComp.pure_bind, expect_bind, hT]
    refine (expect_sample_coord jj (fun t T => expect (K i x s t) fun p =>
      expect (simulate (tapeImpl K (AdaptiveCPA.extTape T)) (k p.1) (p.2, j + 1))
        fun q => G q.1) ?_).trans ?_
    · intro t t' T
      show expect (K i x s t) (fun p => expect (simulate (tapeImpl K
          (AdaptiveCPA.extTape (Function.update T jj t'))) (k p.1) (p.2, j + 1)) fun q => G q.1) =
        expect (K i x s t) fun p => expect (simulate (tapeImpl K (AdaptiveCPA.extTape T)) (k p.1)
          (p.2, j + 1)) fun q => G q.1
      refine congrArg _ (funext fun p => ?_)
      refine congrArg (fun c => expect c fun q => G q.1)
        (simulate_tapeImpl_congr K _ _ _ _ _ fun m' hm' => ?_)
      exact AdaptiveCPA.extTape_update T jj t' (by
        intro h
        have : m' = j := h
        omega)
    · refine congrArg _ (funext fun t => ?_)
      rw [← expect_expect_sample]
      refine congrArg _ (funext fun p => ?_)
      exact ih p.1 (m - 1) (hk p.1) p.2 (j + 1) (by omega)

end Tapes

/-! ### Functions overridden by a table -/

section Override

variable {κ β : Type} [DecidableEq κ]

/-- **A function overridden by a table:** `ovr M R` is `R` with the entries `(p, y)` of `M`
written over it, the first entry of a key winning: `ovr [] R = R`,
`ovr ((p, y) :: M) R = update (ovr M R) p y`. -/
def ovr : List (κ × β) → (κ → β) → κ → β
  | [], R => R
  | e :: M, R => Function.update (ovr M R) e.1 e.2

/-- `ovr [] R = R`. -/
theorem ovr_nil (R : κ → β) : ovr ([] : List (κ × β)) R = R :=
  rfl

/-- `ovr ((p, y) :: M) R = update (ovr M R) p y`. -/
theorem ovr_cons (p : κ) (y : β) (M : List (κ × β)) (R : κ → β) :
    ovr ((p, y) :: M) R = Function.update (ovr M R) p y :=
  rfl

/-- Outside the keys of the table, the overridden function is `R`:
`p ∉ M.map Prod.fst → ovr M R p = R p`. -/
theorem ovr_of_not_mem {M : List (κ × β)} {p : κ} (hp : p ∉ M.map Prod.fst) (R : κ → β) :
    ovr M R p = R p := by
  induction M with
  | nil => rfl
  | cons e M ih =>
    obtain ⟨q, y⟩ := e
    simp only [List.map_cons, List.mem_cons, not_or] at hp
    rw [ovr_cons, Function.update_of_ne hp.1]
    exact ih hp.2

/-- On the keys of the table, the overridden function does not read `R`:
`p ∈ M.map Prod.fst → ovr M R p = ovr M R' p`. -/
theorem ovr_of_mem {M : List (κ × β)} {p : κ} (hp : p ∈ M.map Prod.fst) (R R' : κ → β) :
    ovr M R p = ovr M R' p := by
  induction M with
  | nil => simp at hp
  | cons e M ih =>
    obtain ⟨q, y⟩ := e
    rw [ovr_cons, ovr_cons]
    by_cases hpq : p = q
    · subst hpq
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hpq, Function.update_of_ne hpq]
      simp only [List.map_cons, List.mem_cons] at hp
      exact ih (hp.resolve_left hpq)

/-- Changing `R` at a point outside the table changes the overridden function there only:
`p ∉ M.map Prod.fst → ovr M (update R p y) = update (ovr M R) p y`. -/
theorem ovr_update {M : List (κ × β)} {p : κ} (hp : p ∉ M.map Prod.fst) (R : κ → β) (y : β) :
    ovr M (Function.update R p y) = Function.update (ovr M R) p y := by
  induction M with
  | nil => rfl
  | cons e M ih =>
    obtain ⟨q, z⟩ := e
    simp only [List.map_cons, List.mem_cons, not_or] at hp
    rw [ovr_cons, ovr_cons, ih hp.2]
    exact Function.update_comm hp.1 _ _ _

variable [Fintype κ] [Fintype β] [Nonempty β]

/-- **Resampling a point outside the table moves it into the table:** for `p` not a key of `M`,
`𝔼_R F (R p) (ovr M R) = 𝔼_y 𝔼_R F y (ovr ((p, y) :: M) R)`.

**Proof sketch.** `ProbComp.expect_sample_coord` at the coordinate `p` with
`F' y R = F y (ovr ((p, y) :: M) R)`, which does not read `R p` (`ovr_update`,
`Function.update_idem`); at `y = R p` the new entry repeats `ovr M R p = R p`
(`ovr_of_not_mem`, `Function.update_eq_self`). -/
theorem expect_sample_ovr (M : List (κ × β)) {p : κ} (hp : p ∉ M.map Prod.fst)
    (F : β → (κ → β) → ℝ) :
    expect (sample (κ → β)) (fun R => F (R p) (ovr M R)) =
      expect (sample β) fun y => expect (sample (κ → β)) fun R => F y (ovr ((p, y) :: M) R) := by
  have h := expect_sample_coord p (fun y R => F y (ovr ((p, y) :: M) R)) fun y y' R => by
    show F y (ovr ((p, y) :: M) (Function.update R p y')) = F y (ovr ((p, y) :: M) R)
    rw [ovr_cons, ovr_cons, ovr_update hp, Function.update_idem]
  refine Eq.trans ?_ h
  refine congrArg _ (funext fun R => ?_)
  show F (R p) (ovr M R) = F (R p) (ovr ((p, R p) :: M) R)
  rw [ovr_cons, ← ovr_of_not_mem hp R, Function.update_eq_self]

end Override

end TCSlib.Cryptography.Composability.ETTGame

## ===== TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Transfer.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Games
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.ChallengeSim

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# From the CCA2 experiment to the experiment with a pad and a tag function

Generic transfer lemmas for step 1 of [PS10, Theorem 170.4]: a fixed-length private-key scheme
whose encryption with a key is `⟨r, ⟨c₁, g(r ‖ c₁)⟩⟩` with `c₁ = m ⊕ f(r)` and a uniform nonce `r`,
and whose decryption answers `⟨1, c₁ ⊕ f(r)⟩` on valid words (`validW g`) and `⊥` otherwise, has,
call by call, the oracles `ettImpl … f g false b` of the CCA2 experiment
(`expect_indImpl_ettImpl`); so the experiment `IND_b` is the experiment with `f` and `g`, averaged
over the key (`accept_indGame_eq`).

## Main definitions

* `ETTGame.stRec`: the challenge record of the experiment's state, `stRec s = s.1`.

## Main results

* `ETTGame.expect_indImpl_ettImpl`: one call of `IND_b` has the law of `ettImpl`.
* `ETTGame.accept_indGame_eq`: the CCA2 experiment as the experiment with a pad and a tag
  function.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Algorithm 169.3 and Theorem 170.4 (book pp. 169–171).
-/

namespace TCSlib.Cryptography.Composability.ETTGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

/-- The challenge record of the experiment's state: `stRec s = s.1`. -/
def stRec {n d : ℕ} (s : St n d) : Option (Fin d → Bool) := s.1

/-- `stRec s = s.1`. -/
theorem stRec_eq {n d : ℕ} (s : St n d) : stRec s = s.1 := rfl

section Transfer

variable (S : FixedLengthScheme) (b : Bool) (n : ℕ) (key : List Bool)
  (f : (Fin n → Bool) → (Fin n → Bool)) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))

/-- **One call of `IND_b` under CCA2 with the key `key` has the law of `ettImpl` with `f` and `g`**,
for every function `G` of the answer and the record, for a scheme `S` whose encryption with `key`
is `encW f g` with the nonce `ν re` of a bijection `ν` (`henc`), whose decryption is `decL f` on
valid words and `⊥` otherwise (`hdec`), with `(6n + 4)`-bit ciphertexts:
`𝔼[G] (S.indImpl .cca2 b n key i x (stRec s)) = 𝔼[G ∘ (id × stRec)] (ettImpl … f g false b i x s)`.

**Proof sketch.** By the oracle (the `_onSpec` readers). Encryption and the first challenge
sample the coins of `Enc`, which are the nonce (`expect_sample_equiv ν`), and encrypt as `encW`;
the selected half is `msgOf` (`ofFn_splitHalf_fst`, `_snd`). Decryption refuses the record
(`refW`) and otherwise answers `decAnsW`; its coins and the experiment's nonce are unused
(`expect_const`). A repeated challenge returns the record. -/
theorem expect_indImpl_ettImpl (hct : S.ctLen.eval n = 6 * n + 4)
    (ν : S.enc.Coins n ≃ (Fin n → Bool))
    (henc : ∀ (m : Fin n → Bool) (re : S.enc.Coins n),
      List.ofFn (S.encryptAt n key m re) = encW f g (ν re) (List.ofFn m))
    (hdec : ∀ (w : List Bool) (rd : S.dec.Coins n),
      List.ofFn (FixedLengthScheme.decAnswer (decodeFin n
          (S.dec.runAt n (pairEncode key w) rd))) =
        if validW g w = true then decL f w else List.replicate (n + 1) false)
    (i : Fin 3) (x : (S.indSpec n).dom i) (s : St n (S.ctLen.eval n))
    (G : (S.indSpec n).rng i × Option (Fin (S.ctLen.eval n) → Bool) → ℝ) :
    expect (S.indImpl .cca2 b n key i x (stRec s)) G =
      expect (ettImpl (S.inLens n) (S.outLens n) (S.ctLen.eval n) n f g false b i x s)
        (fun p => G (p.1, stRec p.2)) := by
  have hlenEnc : ∀ (r : Fin n → Bool) {m : List Bool}, m.length = n →
      (encW f g r m).length = S.ctLen.eval n := fun r m hm => by rw [length_encW f g r hm, hct]
  rw [ettImpl_apply, expect_bind]
  match i, x with
  | 0, m =>
    rw [S.indImpl_enc_onSpec, expect_bind, ← expect_sample_equiv ν]
    refine congrArg _ (funext fun re => ?_)
    rw [expect_pure, expect_pure, ettStep_enc, stRec_eq, stRec_eq]
    have hm : List.ofFn (cast (S.indSpec_encDom n) m) = List.ofFn m :=
      ofFn_cast (S.inLens_zero n) _ m
    have hm' : cast (S.indSpec_encDom n) m = padFin n (List.ofFn m) :=
      List.ofFn_injective (by rw [hm, ofFn_padFin_of_length (by
        rw [List.length_ofFn, S.inLens_zero])])
    have hmn : (List.ofFn m).length = n := by rw [List.length_ofFn, S.inLens_zero]
    congr 2
    refine List.ofFn_injective ?_
    rw [ofFn_cast (S.outLens_zero n).symm _ _, hm', henc, ofFn_padFin_of_length hmn,
      ofFn_padFin_of_length (by rw [hlenEnc _ hmn, S.outLens_zero])]
  | 1, c =>
    rw [S.indImpl_dec_onSpec, FixedLengthScheme.decOpen_cca2, Bool.true_and]
    have hc : List.ofFn (cast (S.indSpec_decDom n) c) = List.ofFn c :=
      ofFn_cast (S.inLens_one n) _ c
    have href : (!decide (s.1 = some (cast (S.indSpec_decDom n) c))) =
        !refW s.1 (List.ofFn c) := by
      obtain ⟨o, T⟩ := s
      cases o with
      | none => simp [refW_none]
      | some c' =>
        rw [refW_some]
        simp only [Option.some.injEq]
        congr 1
        exact decide_eq_decide.2 ⟨fun h => by rw [h, hc],
          fun h => List.ofFn_injective (h.trans hc.symm)⟩
    simp only [expect_pure, ettStep_dec, stRec_eq]
    rw [expect_const]
    by_cases hr : refW s.1 (List.ofFn c) = true
    · rw [if_neg (by rw [href, hr]; exact Bool.false_ne_true), expect_pure, decAnsW_eq,
        if_neg (by rw [hr]; simp), padFin_nil]
    · rw [Bool.not_eq_true] at hr
      rw [if_pos (by rw [href, hr]; rfl), expect_bind]
      refine (congrArg _ (funext fun rd => ?_)).trans (expect_const _ _)
      rw [expect_pure]
      congr 2
      refine List.ofFn_injective ?_
      rw [ofFn_cast (S.outLens_one n).symm _ _, hc, hdec, decAnsW_eq, hr]
      simp only [Bool.not_false, Bool.true_and, Bool.true_or, Bool.and_true]
      by_cases hv : validW g (List.ofFn c) = true
      · rw [if_pos hv, if_pos hv]
        have hlen : (decL f (List.ofFn c)).length = S.outLens n 1 := by
          rw [validW_eq, Bool.and_eq_true, wfW_eq, Bool.and_eq_true, decide_eq_true_eq,
            decide_eq_true_eq] at hv
          rw [decL_eq, List.length_cons, List.length_zipWith, List.length_ofFn, hv.1.2,
            Nat.min_self, S.outLens_one]
        rw [ofFn_padFin_of_length hlen]
      · rw [if_neg hv, if_neg hv, padFin_nil, ofFn_zeroBits, S.outLens_one]
  | 2, mm =>
    have hmm : List.ofFn (cast (S.indSpec_challengeDom n) mm) = List.ofFn mm :=
      ofFn_cast (S.inLens_two n) _ mm
    have hmsg : (AdaptiveCPA.msgOf n b (List.ofFn mm)).length = n := by
      have : (List.ofFn mm).length = n + n := by rw [List.length_ofFn, S.inLens_two]
      rw [AdaptiveCPA.msgOf_eq]
      cases b <;> simp [this]
    have hsel : (if b then (FixedLengthScheme.splitHalf
        (cast (S.indSpec_challengeDom n) mm)).2 else (FixedLengthScheme.splitHalf
        (cast (S.indSpec_challengeDom n) mm)).1) =
        padFin n (AdaptiveCPA.msgOf n b (List.ofFn mm)) := by
      refine List.ofFn_injective ?_
      rw [ofFn_padFin_of_length hmsg, AdaptiveCPA.msgOf_eq, ← hmm]
      cases b
      · exact FixedLengthScheme.ofFn_splitHalf_fst _
      · exact FixedLengthScheme.ofFn_splitHalf_snd _
    obtain ⟨o, T⟩ := s
    cases o with
    | some c =>
      rw [stRec_eq, S.indImpl_challenge_repeat_onSpec, expect_pure]
      simp only [expect_pure, ettStep_challenge_some, stRec_eq]
      rw [expect_const]
      congr 2
      refine List.ofFn_injective ?_
      rw [ofFn_cast (S.outLens_two n).symm _ _,
        ofFn_padFin_of_length (by rw [List.length_ofFn, S.outLens_two])]
    | none =>
      rw [stRec_eq, S.indImpl_challenge_none_onSpec, expect_bind, ← expect_sample_equiv ν]
      refine congrArg _ (funext fun re => ?_)
      simp only [expect_pure, ettStep_challenge_none, stRec_eq]
      have henc' : List.ofFn (S.encryptAt n key (if b then (FixedLengthScheme.splitHalf
          (cast (S.indSpec_challengeDom n) mm)).2 else (FixedLengthScheme.splitHalf
          (cast (S.indSpec_challengeDom n) mm)).1) re) =
          encW f g (ν re) (AdaptiveCPA.msgOf n b (List.ofFn mm)) := by
        rw [hsel, henc, ofFn_padFin_of_length hmsg]
      congr 2
      · refine List.ofFn_injective ?_
        rw [ofFn_cast (S.outLens_two n).symm _ _, henc',
          ofFn_padFin_of_length (by rw [hlenEnc _ hmsg, S.outLens_two])]
      · congr 1
        refine List.ofFn_injective ?_
        rw [henc', ofFn_padFin_of_length (hlenEnc _ hmsg)]

/-- **The CCA2 experiment is the experiment with a pad and a tag function** (step 1 of
[PS10, Thm 170.4], transfer): for a scheme `S` whose encryption with the key generated from the
coins `rg` is `encW (fk rg) (gk rg)` with nonces `ν re`, and whose decryption is `decL (fk rg)` on
valid words for `gk rg` and `⊥` otherwise, with `(6n + 4)`-bit ciphertexts,
`Pr[IND_b = 1] = 𝔼_{rg} 𝔼_r 𝔼[⟦A's output⟧₀ = 1 | simulate (ettImpl … (fk rg) (gk rg) false b) …]`.

**Proof sketch.** `FixedLengthScheme.indGame_eq` and `accept_eq`; for each key and coins, the
oracles of `IND_b` have the laws of `ettImpl` through the record (`expect_indImpl_ettImpl`,
`expect_simulate_abs` with a constant counter); the game's codec is a bit codec
(`FixedLengthScheme.indCodec_eq_bitCodec`) and its bit is the head of the output
(`headD_ofFn_one`). -/
theorem accept_indGame_eq (A : NUPPT) (Q : ℕ) (hct : S.ctLen.eval n = 6 * n + 4)
    (fk : S.gen.Coins n → (Fin n → Bool) → (Fin n → Bool))
    (gk : S.gen.Coins n → (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))
    (ν : S.enc.Coins n ≃ (Fin n → Bool))
    (henc : ∀ (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.enc.Coins n),
      List.ofFn (S.encryptAt n (S.gen.runAt n [] rg) m re) =
        encW (fk rg) (gk rg) (ν re) (List.ofFn m))
    (hdec : ∀ (rg : S.gen.Coins n) (w : List Bool) (rd : S.dec.Coins n),
      List.ofFn (FixedLengthScheme.decAnswer (decodeFin n
          (S.dec.runAt n (pairEncode (S.gen.runAt n [] rg) w) rd))) =
        if validW (gk rg) w = true then decL (fk rg) w else List.replicate (n + 1) false) :
    accept (S.indGame .cca2 A Q b n) =
      expect (sample (S.gen.Coins n)) fun rg => expect (sample (A.Coins n)) fun r =>
        expect (simulate (ettImpl (S.inLens n) (S.outLens n) (S.ctLen.eval n) n (fk rg) (gk rg)
            false b) (A.toComp (bitCodec (S.inLens n) (S.outLens n) 1) n Q r) (none, []))
          (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
  rw [accept_eq, FixedLengthScheme.indGame_eq, prob_bind]
  refine congrArg _ (funext fun rg => ?_)
  rw [prob_bind]
  refine congrArg _ (funext fun r => ?_)
  rw [prob_bind, FixedLengthScheme.indCodec_eq_bitCodec]
  have h1 : (fun res : (Fin 1 → Bool) × Option (Fin (S.ctLen.eval n) → Bool) =>
      ProbComp.prob (.pure (res.1 0)) (· = true)) =
      fun res => if (List.ofFn res.1).headD false = true then (1 : ℝ) else 0 := by
    funext res
    rw [prob_pure, headD_ofFn_one]
  rw [h1]
  exact expect_simulate_abs _ _ stRec (fun _ => 0) (Q + 1)
    (fun i x s _ G => expect_indImpl_ettImpl S b n _ (fk rg) (gk rg) hct ν (henc rg) (hdec rg)
      i x s G)
    (fun i x s _ => (OracleComp.allOutputs_true _).mono fun _ _ => Nat.zero_le _)
    _ Q (A.toComp_costBoundedBy _ n Q r) (none, []) (by simp) _

end Transfer

end TCSlib.Cryptography.Composability.ETTGame
