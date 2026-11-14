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
