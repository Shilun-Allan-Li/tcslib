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
