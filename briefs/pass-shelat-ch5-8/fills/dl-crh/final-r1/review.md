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
2. **Different selector bits:** equal images under different selector bits are impossible, by `expF_injective`.
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
