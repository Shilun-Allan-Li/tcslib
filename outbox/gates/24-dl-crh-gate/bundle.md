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

## ===== briefs/pass-shelat-ch5-8/gates/24-dl-crh/review.md =====

# dl-crh · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS.** LE-facade is done. LE-doc (formula docstrings) is written and waits for its
rebuild.

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
  - every new public declaration now passes the docaudit, except the target, whose first line is prose.
- **Rebase:** The branch was rebased onto `a757b6a1`; the unit files are byte-identical, and LE-facade is now `d84381ee`. The rebase makes Claude the committer of the worker commits; authors are unchanged.
- **Build** on `$SP/dl-oleans`: 22 modules (`DiscreteLog` and everything downstream, the helpers, `Hashing`, base-delta, root `TCSlib`, `audits/pass-shelat/Checks`) rc 0; Checks byte-identical to the base; full head check 1207 modules OK. The tree was restored to the base snapshot afterwards.
- **Lint (#305):** 92 FAIL / 102 WARN, with the same lines at the head as at the records tip.
- **Evidence:** `ledoc-evidence.zip`, SHA-256 `172de674962865dc2f1ab2eb754a2ee40fe13a92d35204b995b2d26d67eec4b6`, 128 entries. Its manifest is `ledoc-evidence-SHA256SUMS`, and extracts
  are in `landing-ledoc/`.
- **PR:** draft [PR #307](https://github.com/Shilun-Allan-Li/tcslib/pull/307).

## ===== briefs/pass-shelat-ch5-8/gates/24-dl-crh/worker-report.md =====

# dl-crh — final proof report

**Status: proof complete, with the recorded user scope and lint exceptions.**
`TCSlib.Cryptography.Authentication.dlHash_crh` is proved with its original statement.
The proof branch `fill/dl-crh` remains local. Only the assigned exchange delivery path is used.

Issue pack: `b436d19a0310265b214447ea6710deba32df6dd8`. Issue base: `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`.
Final proof commit: `fa33b9b8fa3a9b801a7db8857d7a2739c61c1e16`. Lean: `leanprover/lean4:v4.25.0`.
Pinned Mathlib: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.

## Delivered mathematics and edge cases



1. **Read the honest key.** The user-authorized provider readers are
   `expGenFun_eq` and `expSampleRaw_eq`
   (`TCSlib/Cryptography/Candidates/DiscreteLog.lean:486`, `:657`).
   `dlHashIdx_layout` and `dlHashGenFun_layout` expose generator and sampler tape
   segments (`TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:91`, `:121`).
   `dlHashGenFun_key` (`:141`) proves the sampled exponent, including the fallback,
   is below the positive order and identifies the key as `⟨i, expF i z⟩`.
   The published coin equivalence and activation readers separate the two honest
   tapes (`dlHash_coinsEquiv`, `:446`; `dlHash_gen_runAt`, `:474`).

2. **Compression.** `dlHashEval_expF` (`FromDiscreteLog.lean:264`) identifies
   evaluation with the numeral of the unit `(if b then g^z else 1) * g^x`.
   `dlHashEval_range` (`:324`) proves exact output width `n` and positive value
   below `p`. `dlHash_compresses` (`:489`) uses the generator threshold, this
   range lemma, and `card_boundedInput`/`card_boundedRange`
   (`FromDiscreteLog/Encoding.lean:152`, `:164`). The cardinalities are `2m` and
   `p-1=m`, with `m>0`; hence the range is strictly smaller than the domain.

3. **Collision shape and extraction.** Equal selectors cancel their common unit
   factor. `unitCollision_selector_ne` (`FromDiscreteLog/Algebra.lean:76`) then
   applies published `expF_injective` (`Candidates/DiscreteLog.lean:299`) and
   bounded residue canonicity. For unequal selectors, `unitCollision_extract`
   (`Algebra.lean:110`) uses the generator's order and modular addition to recover
   `z.val`: the residue of `x' + (m-x)` if the first selector is true, or
   `x + (m-x')` otherwise. `dlHashEval_collision`
   (`FromDiscreteLog.lean:292`) connects distinct bit inputs and their equal
   evaluations to this unit-group statement.

4. **The concrete NUPPT reduction.** `collisionPost`
   (`FromDiscreteLog/Reduction.lean:85`) pads/truncates the finder output to two
   `(n+1)`-bit inputs, reads their exponent prefixes and the first selector, and
   evaluates the selected modular difference through subtraction, addition, and
   division. `polyTimeComputable_collisionPost` (`:116`) proves its efficiency.
   `collisionReduction` (`:290`) wraps the raw finder/output composition using
   `NUPPT.ofPolyTime`; its coin, advice, and activation readers (`:301`, `:306`,
   `:311`, `:317`, `:328`) retain the finder's tapes and advice.
   `collisionPost_split` (`:222`) covers arbitrary raw finder outputs.
   `dlHash_reduction_success` (`FromDiscreteLog.lean:581`) removes padding from
   the proved exact-length hash values, applies extraction, and proves that the
   reduction writes and decodes the canonical `n`-bit numeral of `z.val`.
   `dlHash_ideal_collision_le` (`:631`) transports equal-length finder/reduction
   coins and lifts that pointwise implication to uniform probabilities.

5. **Distribution switch and negligibility.** `collision_accept_eq`
   (`FromDiscreteLog/Probability.lean:50`) reads the CRH game as a generator-coin
   average of finder-coin probabilities. The specialized reader
   `dlHash_collision_accept_eq` (`FromDiscreteLog.lean:549`) separates the honest
   sampler tape as well. `sampleBelowL_uprob_le`
   (`FromDiscreteLog/Sampling.lean:81`) applies the published sampler closeness
   with independent auxiliary finder coins and relabels the ideal seed through
   Mathlib's value-preserving finite-residue equivalence. The canonical evaluator
   reader at `Sampling.lean:66` identifies the resulting ideal key with `expF i z`.
   Averaging and the reduction bound give `dlHash_collision_bound`
   (`FromDiscreteLog.lean:658`): for `n ≥ G.n₀`, collision acceptance is at most
   `G.dlProb B n + (1/2)^n`. The target proof (`:710`) combines `hDL B`,
   `negligible_two_pow_neg`, addition, and eventual domination. It chooses the
   collision probability itself as the all-parameter negligible upper bound.

## All six brief edge cases

| Edge case | How the delivered proof covers it |
|---|---|
| Parameters below `G.n₀` | Compression is explicitly eventual (`dlHash_compresses`, main file `:489`). Security uses `Negligible.mono` with threshold `G.n₀` in `dlHash_crh` (`:710`), so it imposes no invalid asymptotic bound below the threshold. The chosen bound equals actual collision acceptance at every parameter. |
| Invalid indices | Pointwise algebra/evaluation/reduction lemmas explicitly require `ExpValid`. The generated-index proof obtains it from `G.valid` and `hV` above the threshold (`dlHashGenFun_key`, `:141`; `dlHash_collision_bound`, `:658`). It makes no security or range claim for arbitrary invalid externally supplied indices. |
| Equal selectors `b=b'` | `unitCollision_selector_ne` (`Algebra.lean:76`) cancels the common factor and applies `expF_injective`; bounded equal exponents and equal selectors contradict input distinctness. |
| Equal exponent prefixes `x=x'` | Unequal selectors are still permitted. `unitCollision_extract` (`Algebra.lean:110`) has no exponent-inequality assumption; its modular-difference formula gives `m mod m=0` in this case. The reduction therefore recovers the zero challenge rather than discarding this collision. |
| Inputs outside `D_i` | `dlHashCollision_iff` (`FromDiscreteLog.lean:533`) retains both exponent-below-`m` guards. `dlHash_collision_accept_eq` (`:549`) proves this is exactly the CRH game's guarded event. `dlHash_reduction_success` (`:581`) consumes those guards; no unguarded finder output is counted as a successful collision. |
| Honest `y=g^w` with `w=0` | `dlHashGenFun_key` (`:141`) handles both an accepted zero and the sampler's fallback zero. The unit formula and extraction theorems quantify over every residue `z`, with no nonzero hypothesis. Thus the identity key and collisions with equal exponent prefixes are included in the same proof. |

No new hardness assumption, full-length-prime assumption, or narrowed adversary
class is introduced. The full-group equation `m=p-1` is used for compression;
the collision reduction itself only needs the valid exponentiation-group data.


## Scope, declarations, and sketch

Eight Lean files changed: the owned hashing module, six helpers, and the two expressly authorized
reader equations in Candidates/DiscreteLog.lean. No target or existing declaration type changed;
the separate source-preservation check retains all 16 other original bodies and all 17 original
declaration docstrings byte-for-byte, together with the frozen target statement.
the stored metadata comparison reports no kind/type/reducibility/abbreviation/simp/instance/protected delta.
The hashing title drops statement phase, Main results records the proof, and Contents lists all six helpers.
The sketch follows compression, selector inequality, the concrete reduction, and the sampler switch.

The complete 69-entry source declaration inventory, with qualified names, kinds, visibility, files,
and source lines, is `evidence/new-declarations-final3.md` and `evidence/new-declarations-final3.json`, generated by
`python3 -I evidence/tools/new_declarations.py`. Both private helper declarations are included.
Generated kernel constants are included separately in the stored-constant census.

## Promotions and resolved reader requests

The initial missing-reader escalation was resolved by the user's scoped authorization for
`expGenFun_eq` and `expSampleRaw_eq`; both are delivered with equation docstrings and no simp attribute.
No outstanding foreign-reader request remains.

- Encoding: ofFn_splitBits_fst, ofFn_splitBits_snd, inputWord_split, inputWord_take, inputWord_drop, inputWord_ext, inputWord_num_ext, boundedInputEquiv, boundedInputEquiv_apply, boundedInputEquiv_symm_apply, card_boundedInput, and card_boundedRange → shared authentication/bit-vector encoding.
- Algebra: private residue_difference → shared natural modular arithmetic; expUnit_pow_val → the candidate unit-power interface.
- Coins: sumCoinsEquiv, sumCoinsEquiv_eq, and sumCoinsEquiv_symm_ofFn → the shared randomized/collection coin interface.
- Reduction: modularDifference, modularDifference_eq, modularDifference_value, and polyTimeComputable_modularDifference → the shared arithmetic string layer. The local padding-idempotence argument in collisionPost_split is a candidate shared padStr lemma.
- Probability: expect_sample_eq_uexp → the shared games bridge/probability layer; collision_accept_eq → Hashing/CollisionResistant.
- Sampling: residueFinEquiv, residueFinEquiv_eq, and residueFinEquiv_val → finite-residue encoding; sampleBelowL_uprob_le → the candidate sampler interface; expEval_natToList_val → canonical candidate-evaluator readers.

Searches and detailed provenance are retained in `evidence/PROMOTION.md` and the delivered tools/logs.
Existing public lemmas are imported. No private provider proof was copied.

## All four overlap disclosures

**overlap: TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean dlb_expo_val**

Arbitrary-natural unit-power values were rederived from public val_units_pow, coe_expUnit, and expValid_iff.

**overlap: TCSlib/Cryptography/Candidates/Factoring.lean fac_listToNat_inj**

Equal-width numeral injectivity was rederived through public numeral canonicity in inputWord_num_ext.

**overlap: TCSlib/Cryptography/Asymptotic/UniversalPadding.lean ofFn_splitCoins_symm_cast**

Coin-cast concatenation was rederived using public ofFn_arrowCongr_finCongr and ofFn_splitCoins_symm.

**overlap: TCSlib/Cryptography/Candidates/DiscreteLog.lean dla_statClose_expDec**

Overlapping residue relabel/statistical-switch submaterial uses public sampler closeness and Mathlib ZMod.finEquiv; the private implementation was not copied.

## Checks and admissions

The original seven pack checksums and 170 issue-source checksums passed; original raw evidence remains
verbatim in `evidence/initial-escalation.zip`. The canonical final sweep under
`evidence/logs/final-sweep-repaired/` checked all 176 modules, one module per
`scripts/lean_check_tree.sh` call, with zero errors. Source/log hashes are bound in raw results.
The earlier complete pass under `logs/final-sweep/` also built previously unbuilt downstream
prerequisites. It remains labeled preliminary; `evidence/sweep-phases.md` records why the fully
bootstrapped order was then checked again. No running Lean process was interrupted.
The admission comparison is exactly 22 → 21: only `dlHash_crh` was removed, with no added admission.
`evidence/admission-delta-repaired.json` retains every warning and its source/log location.

No project `lake build` or unfiltered cache fetch was used. Python commands use `python3 -I`.
Development failures, repairs, raw logs, probe sources, manifests, request records, and tools are retained.

## Axioms and stored metadata

Target axioms: `propext`, `Classical.choice`, `Quot.sound`.
All-stored census: base 172, final 265; 93 added stored constants and 0 removed.
Metadata changes: 0. New nonstandard-axiom dependencies: 0.
The full raw census, including generated matchers/projections, is delivered and named in the summary.

Every axiom delta:

- `TCSlib.Cryptography.Hashing.FromDiscreteLog` / `TCSlib.Cryptography.Authentication.dlHash_crh`: `['Classical.choice', 'Quot.sound', 'propext', 'sorryAx']` → `['Classical.choice', 'Quot.sound', 'propext']`.

Inherited final nonstandard entries: 0; none is new or worsened:


## Rule 10 seals, controls, and explicit scan

A excludes exactly `Complexity.PolyExpr.eval` as notation; B seals it. Both seal all ordinary
foreign TCSlib definitions in the full import closure, including eligible generated matchers and
definition instances; recorded abbreviation/status exclusions remain visible in request records.
Base covers the two pre-existing changed files; all six new helpers are absent at base. Final covers
all eight files. Every harness and mask check is valid, and there are zero new failing declarations.

Current baseline/final source declaration results, by side/owner/variant:

### Explicit reuse of the unchanged original baseline

Fresh final-source evidence belongs to `final3`. The four original baseline seals,
eight baseline control runs, baseline census, and 208-row baseline scan/review remain in
their actual `final2` paths; they were not copied or relabeled as fresh runs.
The reuse record binds all original raw evidence, the unchanged 98-source baseline closure,
and 98 runtime-object verifications. Fresh final-source snapshots, seals, controls, census,
and manual scan review are separately checked against the repaired current proof bytes.
Binding record: `evidence/probes/Rule10/final3/baseline-reuse.json`.

### Harness revision and measured pilot equivalence

This report uses final-source edition `final3` and harness revision `batch2048-ordinary-local-attribute-api-v2`.
The optimization pilot/benchmark is historical evidence from `final2`.
Its original-source/request preservation claims refer to that historical before/after harness
comparison. They do not assert that the pilot's source snapshot equals the repaired final
proof source snapshot. The fresh final-source evidence is independently bound above.
The original final1 probes, logs, and versioned tools are retained. Performance investigation
identified 24 full-environment scans and 12 mask snapshots for the original 1409-request base-A
probe. The revision
uses batches of at most 2048 requests through the same ordinary registered local attribute API,
with component/mask checks at install and EOF. It does not use a direct reducibility setter,
unsafe reducibility, or source/proof changes. Static assembly alone was explicitly insufficient;
the delivered completed provenance also contains actual native controls and a full base-A pilot.

The optimized unsealed/reader controls passed; each sealed negative failed exactly once.
The complete optimized base-A failure set equals the completed original base-A failure set.
Measured original base-A duration: 637.935793 seconds; optimized base-A:
56.96355 seconds (ratio 11.199).
Actual logs, API source hashes, assembly data, and comparisons: `evidence/probes/Rule10/final2/seal-provenance.json`.
The complete base/final seals, controls, census, and full per-row scan reviews are separately
required by this report; pilot results do not substitute for those checks.

### base / TCSlib.Cryptography.Candidates.DiscreteLog / A

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final2/seals-base/evidence_probes_Rule10_final2_seals_base_A_DlCrh_base_A_TCSlib_Cryptography_Candidates_DiscreteLog.001.log`.

None.

### base / TCSlib.Cryptography.Candidates.DiscreteLog / B

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final2/seals-base/evidence_probes_Rule10_final2_seals_base_B_DlCrh_base_B_TCSlib_Cryptography_Candidates_DiscreteLog.001.log`.

None.

### base / TCSlib.Cryptography.Hashing.FromDiscreteLog / A

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final2/seals-base/evidence_probes_Rule10_final2_seals_base_A_DlCrh_base_A_TCSlib_Cryptography_Hashing_FromDiscreteLog.001.log`.

None.

### base / TCSlib.Cryptography.Hashing.FromDiscreteLog / B

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final2/seals-base/evidence_probes_Rule10_final2_seals_base_B_DlCrh_base_B_TCSlib_Cryptography_Hashing_FromDiscreteLog.001.log`.

None.

### final / TCSlib.Cryptography.Candidates.DiscreteLog / A

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_A_DlCrh_final_A_TCSlib_Cryptography_Candidates_DiscreteLog.001.log`.

None.

### final / TCSlib.Cryptography.Candidates.DiscreteLog / B

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_B_DlCrh_final_B_TCSlib_Cryptography_Candidates_DiscreteLog.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog / A

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_A_DlCrh_final_A_TCSlib_Cryptography_Hashing_FromDiscreteLog.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog / B

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_B_DlCrh_final_B_TCSlib_Cryptography_Hashing_FromDiscreteLog.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog.Algebra / A

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_A_DlCrh_final_A_TCSlib_Cryptography_Hashing_FromDiscreteLog_Algebra.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog.Algebra / B

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_B_DlCrh_final_B_TCSlib_Cryptography_Hashing_FromDiscreteLog_Algebra.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog.Coins / A

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_A_DlCrh_final_A_TCSlib_Cryptography_Hashing_FromDiscreteLog_Coins.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog.Coins / B

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_B_DlCrh_final_B_TCSlib_Cryptography_Hashing_FromDiscreteLog_Coins.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog.Encoding / A

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_A_DlCrh_final_A_TCSlib_Cryptography_Hashing_FromDiscreteLog_Encoding.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog.Encoding / B

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_B_DlCrh_final_B_TCSlib_Cryptography_Hashing_FromDiscreteLog_Encoding.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog.Probability / A

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_A_DlCrh_final_A_TCSlib_Cryptography_Hashing_FromDiscreteLog_Probability.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog.Probability / B

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_B_DlCrh_final_B_TCSlib_Cryptography_Hashing_FromDiscreteLog_Probability.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog.Reduction / A

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_A_DlCrh_final_A_TCSlib_Cryptography_Hashing_FromDiscreteLog_Reduction.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog.Reduction / B

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_B_DlCrh_final_B_TCSlib_Cryptography_Hashing_FromDiscreteLog_Reduction.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog.Sampling / A

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_A_DlCrh_final_A_TCSlib_Cryptography_Hashing_FromDiscreteLog_Sampling.001.log`.

None.

### final / TCSlib.Cryptography.Hashing.FromDiscreteLog.Sampling / B

Valid harness; exit 0. Raw log: `evidence/logs/rule10/final3/seals-final/evidence_probes_Rule10_final3_seals_final_B_DlCrh_final_B_TCSlib_Cryptography_Hashing_FromDiscreteLog_Sampling.001.log`.

None.

### Superseded final2 seal failures and their repairs

The superseded final2 runs checked source commit `5a24269932a72f672104b18280609879dd992c82`. Their source failures
are disclosed below even though every fresh final3 source seal now has zero errors. The generator
rehashes each original raw log and checks every diagnostic against the mapped native records;
the final3 success does not erase these earlier findings.

| Variant | Failing declaration | Diagnostics | Original source lines | Raw probe lines |
|---|---|---:|---|---|
| B | `TCSlib.Cryptography.Authentication.dlHash_collision_accept_eq` | 1 | 556 | 666 |
| B | `TCSlib.Cryptography.Authentication.dlHash_compresses` | 3 | 511, 512, 514 | 621, 622, 624 |
| A | `TCSlib.Cryptography.Authentication.FromDiscreteLog.collisionPost_split` | 1 | 242 | 352 |
| B | `TCSlib.Cryptography.Authentication.FromDiscreteLog.collisionPost_split` | 1 | 242 | 352 |

Original raw-log bindings (shared logs intentionally occur for both affected declarations):

- B / `TCSlib.Cryptography.Authentication.dlHash_collision_accept_eq`: `evidence/logs/rule10/final2/seals-final/evidence_probes_Rule10_final2_seals_final_B_DlCrh_final_B_TCSlib_Cryptography_Hashing_FromDiscreteLog.001.log`;
  SHA-256 `fccb646130f454d0e540c5ea868ea6b0a04f13c98c7169f2256eecdb51f8b000`.
- B / `TCSlib.Cryptography.Authentication.dlHash_compresses`: `evidence/logs/rule10/final2/seals-final/evidence_probes_Rule10_final2_seals_final_B_DlCrh_final_B_TCSlib_Cryptography_Hashing_FromDiscreteLog.001.log`;
  SHA-256 `fccb646130f454d0e540c5ea868ea6b0a04f13c98c7169f2256eecdb51f8b000`.
- A / `TCSlib.Cryptography.Authentication.FromDiscreteLog.collisionPost_split`: `evidence/logs/rule10/final2/seals-final/evidence_probes_Rule10_final2_seals_final_A_DlCrh_final_A_TCSlib_Cryptography_Hashing_FromDiscreteLog_Reduction.001.log`;
  SHA-256 `466b9ffcf10b96592b9f69f3951ed13f1546affc52064c481d05e5fd472a831c`.
- B / `TCSlib.Cryptography.Authentication.FromDiscreteLog.collisionPost_split`: `evidence/logs/rule10/final2/seals-final/evidence_probes_Rule10_final2_seals_final_B_DlCrh_final_B_TCSlib_Cryptography_Hashing_FromDiscreteLog_Reduction.001.log`;
  SHA-256 `e96e6ca1cbf671e0aa777b261109a37c9565b600cbefeefb37f8b6b113d71d1c`.

The four variant/declaration rows contain six diagnostics in three raw logs:

- `collisionPost_split` (A and B, one diagnostic each): the original `simpa` required an implicit
  dependent transport of the padded-word width. The repair first proves `hwidth` with the public
  polynomial-evaluation readers, then uses `congrArg (fun k : ℕ => List.ofFn (padFin k raw)) hwidth`,
  reverses that equality, and composes it with the public `ofFn_padFin_eq_padStr` equation.
- `dlHash_compresses` (B, three diagnostics) and `dlHash_collision_accept_eq` (B, one diagnostic):
  combined simplification normalized dependent input widths before the CRH field/hash readers
  could match while `PolyExpr.eval` was sealed. The repair stages simplification: first
  `dlHash_inDom`, `dlHash_inRange` where needed, `CRH.hash_eq`, `dlHash_eval`, pair/guard readers;
  then `dlHash_domLen`, `dlHash_rangeLen`, and the published polynomial evaluation equations.

All three theorem headers/types are byte-identical before and after these repairs, as checked
again by this generator. No statement, hardness assumption, global simp attribute, or mathematics
changed. Fresh final3 seals validate the repaired bytes: all 16 final owner/variant runs have
zero failing declarations, including Reduction A/B and the owned module B.

base: 8 control probe runs, 120 per-case checks, 28 sealed negatives; each negative fails exactly once and every expected positive/unsealed case passes.

base explicit scan: 208 individually reviewed rows. Raw scanner foreign-definition candidates: 0; raw unresolved rows before manual review: 10. Final manual disposition: pending 0, new foreign-definition BODY-reading violations 0. Review: `evidence/probes/Rule10/final2/base-explicit-manual-review.json`.

final: 32 control probe runs, 520 per-case checks, 122 sealed negatives; each negative fails exactly once and every expected positive/unsealed case passes.

final explicit scan: 595 individually reviewed rows. Raw scanner foreign-definition candidates: 4; raw unresolved rows before manual review: 15. Final manual disposition: pending 0, new foreign-definition BODY-reading violations 0. Review: `evidence/probes/Rule10/final3/final-explicit-manual-review.json`.

The four raw final candidates are the following registered built-in simproc invocations:

- `TCSlib/Cryptography/Hashing/FromDiscreteLog/Algebra.lean:124`, `TCSlib.Cryptography.Authentication.FromDiscreteLog.unitCollision_extract`: `↓reduceIte`.
- `TCSlib/Cryptography/Hashing/FromDiscreteLog/Algebra.lean:126`, `TCSlib.Cryptography.Authentication.FromDiscreteLog.unitCollision_extract`: `↓reduceIte`.
- `TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:279`, `TCSlib.Cryptography.Authentication.dlHashEval_expF`: `↓reduceIte`.
- `TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:281`, `TCSlib.Cryptography.Authentication.dlHashEval_expF`: `↓reduceIte`.

The finalized per-row review retains the pinned `builtin_simproc` registration and the
`.simproc` → `.addSimproc` elaborator path. These `↓reduceIte` items invoke the registered
simproc, which produces proofs through `ite_cond_eq_true` / `ite_cond_eq_false`; they do not
ask simp to unfold the metaprogram's definition body. The raw candidate counts remain 0/4
and raw unresolved counts remain 10/15; manual clearance means zero newly introduced
foreign-definition body readings, not zero raw candidates.

## Lint and explicit exceptions

Required lint: **222 FAIL / 102 WARN**, versus baseline **216 FAIL / 102 WARN**.
The exact six added FAIL entries are the frozen ancestor Hashing.lean facade's direct-import
diagnostics for Algebra, Coins, Encoding, Probability, Reduction, and Sampling. All six helpers are
exported through the owned FromDiscreteLog facade. The user explicitly authorized:

> Acknowledge exactly six lint false positives

This is an exception to literal zero-new-FAIL lint, not a claim that the lint mechanically passed.
No other added FAIL is accepted. Raw baseline/final logs and every changed WARN message are in
`evidence/style-delta-repaired.md` / `evidence/style-delta-repaired.json`; the inherited provider-size warning changes 1192 → 1209 lines,
and its missing-reader warning list drops expSampleRaw after its new equation reader.
The scoped provider exception preserves this pre-existing over-1000-line file without unrelated
splitting. Every owned/new hashing file remains below 1000 lines. No global simp attribute was added.

## Host, cache, and bootstrap

Resumption preflight: 12 CPUs; physical RAM 19,327,352,832 bytes; APFS free space
264,007,364,608 bytes (>12 GiB). Native non-cache memory-use proxy 12,238,684,160 bytes and
headroom proxy 7,088,668,672 bytes (>4 GiB). macOS lacks Linux cgroup/MemAvailable counters;
the native proxy is explicitly not claimed to be Linux MemAvailable. Raw native readings and
subsequent resource logs are retained under `evidence/logs/resume-1/`.
The user overrode host serialization to at most three Lean processes. This worker checks one
module at a time in its own olean tree and counts other host processes before launch. Exact
authorizations and the authorized coordination-note provenance are in `evidence/authorization.md`.

Only the 87 issued Mathlib roots were fetched. The narrowed cache command exited 0:
2,339 files decompressed, zero files downloaded, from the pre-existing hash-addressed archive store
(32,667 files; 1,595,387,830 bytes; precise originating sessions unknown). All 11 present packages
match manifest URLs/revisions; doc-gen4, UnicodeBasic, BibtexQuery, and MD4Lean are absent.
No empty olean was found; the Mathlib-root import probe and bootstrap passed. No dependency tree
was copied or reused from another session, and no memory-backed scratch filesystem was used.
Module timestamps and native maximum-memory outputs are retained. Checks standardized on Lean -j4
without self-imposed timeouts; earlier wrapper versions and their logs remain delivered.

## Patch reproduction and transport history

The complete 4-patch series from the exact issue base reproduces all eight changed/new files
byte-for-byte. `evidence/patch-reproduction-repaired/result.json` records every reproduced/head hash:

- `TCSlib/Cryptography/Candidates/DiscreteLog.lean`: `ef7cf001f483ce0a5c47025924ee9c10fb78a9b59f73e4e5482091ad05a2aa67`.
- `TCSlib/Cryptography/Hashing/FromDiscreteLog.lean`: `9d500a96e0e112a092ec0f2e548c5a648752dba89faa4bee40272ef55fcf78d0`.
- `TCSlib/Cryptography/Hashing/FromDiscreteLog/Algebra.lean`: `adffb2ec4b9a064aa2a21948ab8a0b79510efda5b1d9be8b48bbc055e02bd221`.
- `TCSlib/Cryptography/Hashing/FromDiscreteLog/Coins.lean`: `1ab5d3ece9c424a456e380d2e40eba45b6f0a8f76b69d12d03bd36842eecd6cb`.
- `TCSlib/Cryptography/Hashing/FromDiscreteLog/Encoding.lean`: `79669605ededcae778a0d719f0db5bd6a998f221ded322fd283c65e04411aaa4`.
- `TCSlib/Cryptography/Hashing/FromDiscreteLog/Probability.lean`: `bf943d5aea5c9da86ada6d9171576b40949b96f2dc4882699dd66112f00f610b`.
- `TCSlib/Cryptography/Hashing/FromDiscreteLog/Reduction.lean`: `27e4d37dc581ff2db70336b8b19ce3a92531de09c0e42ff260a9ffd4685b04c6`.
- `TCSlib/Cryptography/Hashing/FromDiscreteLog/Sampling.lean`: `398337fbdf7e1e2d46f6658262ee47cf887a5d3707e18c6c8807dda9f0a55c15`.

Patch files:

- `0001-Prove-discrete-log-hash-compression-and-collision-ex.patch`.
- `0002-Prove-the-collision-finder-reduction-recovers-discre.patch`.
- `0003-Complete-the-discrete-log-hash-collision-resistance-.patch`.
- `0004-Make-dependent-length-transports-explicit-under-Rule.patch`.

Exchange records already pushed only under `inbox/fills/dl-crh/`:

- checkpoint 1: reader escalation: `396c734fac3ba4a0e8d06320517f56017962f734`.
- initial escalation final record (proof remained admitted): `dc9846a2d46aca5be8fe6d48f2c9064090a48014`.
- checkpoint 2: compression and collision shape: `cb64931761fae93c916535fc454f8c5a5a4bcab0`.
- checkpoint 3: concrete reduction and collision-to-DL success: `88cca5e5dd801753da004f86c982f1f80f0a270a`.

The final exchange push identity belongs in the final chat, not recursively inside its own payload.
The payload contains REPORT.md, the full patch series, exact src bytes, and all evidence. Packaging
generates manifests after this report and verifies exact path-set/hash equality and ZIP bytes; its
actual output is retained separately. The fallback ZIP has `dl-crh/` at its root.

## Bound report inputs

- `evidence/probes/Rule10/final3/summary.json`: `fa1887f91bae1faaa9b5620942e463d11ae87cbc1bef56aad2db197ecc60438b`.
- `evidence/probes/Rule10/final2/base-explicit-manual-review.json`: `9ff0fcf99932d2a46b42d9e086a333f1425d8bca6cb651ad5236794a48256afd`.
- `evidence/probes/Rule10/final3/final-explicit-manual-review.json`: `110377418a1d9992224a598bb8ee6477906b7ccd961cf172eedac2850591e3b6`.
- `evidence/admission-delta-repaired.json`: `b133743a17f1b9573501b63de18978dc2e53ee1b016ead9c913df01d96a9decd`.
- `evidence/style-delta-repaired.json`: `cc01140ef7ea2ea98593708354a1604df6ec5698e38dcab2021099bf63ceb2af`.
- `evidence/new-declarations-final3.json`: `f94d72655e4cabcf6f8467dde3d80f6a104d442ffa245d53b33c43bc60e15a2c`.
- `evidence/proof-route-final3.md`: `b2b816a6f1ae755106cf816d096947465944321a274bf7c60e06f2e10b415738`.
- `evidence/logs/final-source-preservation-repaired.json`: `3805dfc5098162881b07d706421559a784d8b7bbae8f00e3eb22fde7beba4b9d`.
- `evidence/patch-reproduction-repaired/result.json`: `78f92a60be48ca49eced8b86c3d24165fc98aaddc901a0befcca3c7a7397f29b`.
- `evidence/logs/rule10/final2/seals-final/results.jsonl`: `c01d37a576d9c150c8aa18cb34059ed3dbebaf5d06ca9c8bd5fbbdd432200094`.
- `evidence/probes/Rule10/final2/seal-provenance.json`: `47da8df048526401948663d2c5f89d5252b546a382bdacc9df67773913fc5178`.
- `evidence/probes/Rule10/final3/baseline-reuse.json`: `f111e21dd9b7ce9a20e426f0a89b02d9a875294f589a36d4dfb6550ddee128b4`.

Proof commit: `fa33b9b8fa3a9b801a7db8857d7a2739c61c1e16`. Issue base: `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`.

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

## ===== briefs/pass-shelat-ch5-8/fills/dl-crh/issued-r1/brief.md =====

# Codex fill · the discrete-log hash is collision-resistant (`dlHash_crh`, Theorem 142.3)

**Issue base** `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9` on `cryptography/pass-shelat-ch2-4` (the merge of #299).
**Unit** `dl-crh`. **Worker** Codex (Seyoon, 2026-11-14). **Lean** 4.25.0 and the Mathlib revision in that
commit's `lake-manifest.json`.

Prove the admitted theorem `dlHash_crh` of [PS10, Theorem 142.3] in `TCSlib/Cryptography/Hashing/FromDiscreteLog.lean`. The
statement passed Gate 06 (prong A) and is frozen. Its docstring holds the maintainer's proof sketch.

## Checkout and delivery

- Work in a local checkout of the repository. Fetch `cryptography/pass-shelat-ch2-4` and start a local branch
  `fill/dl-crh` at the exact issue base. Record the base in `REPORT.md`. Keep the proof branch local: never push it.
- Read `policy.md`, the attached environment addendum and `README.md`.
- **Deliver** every checkpoint and the final payload under `inbox/fills/dl-crh/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `src/`: the changed and new files;
  - `evidence/`, with a `SHA256SUMS` manifest (see *Evidence completeness*).
- Commit as `fill dl-crh: checkpoint N` and `fill dl-crh: final`. Pull with rebase before pushing, push only your
  delivery path, and never force-push.
- **At the end, also return the final payload in the chat** as a ZIP with `dl-crh/` at its root, holding the same
  `REPORT.md`, `patches/`, `src/` and `evidence/`. This is a fallback in case the push fails.
- Campaign changes land by a maintainer PR for Seyoon's approval.

## Target (frozen; quoted from the issue base)

```lean
theorem dlHash_crh (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i ∧ dlM i = dlP i - 1) (hDL : G.DLHard) :
    (dlHash H G).Compresses ∧ (dlHash H G).CollisionResistant := by
  sorry
```

It lives in namespace `TCSlib.Cryptography.Authentication`. The section variable is `{V : List Bool → Prop}`. `dlHash H G` is Protocol 142.2 as a `CRH` (keys `⟨i, y⟩`, domain `{(x, b) : x < m}`, range `Z_p^*`); `Compresses` and `CollisionResistant` are in `Hashing/CollisionResistant.lean`; `G.DLHard` is the discrete-log assumption (`Candidates/DiscreteLog.lean`). Read the module docstring's source notes on the domain and the full group.

The target's docstring sketch is the route. You may edit it to describe the delivered proof.

## Published interfaces

| Interface | Provider |
|---|---|
| `dlHashGenFun`, `dlHashEval`, `dlHashMul`, `dlHashPow` and their `_eq`/`polyTimeComputable_*`; `dlHash` and its `simps` fields | owned file |
| `CRH`, `Compresses`, `CollisionResistant` and readers | `Hashing/CollisionResistant.lean` |
| `ExpGroupGen`, `DLHard`, `expGen`, `expSampleRaw`, `expF_injective`, `statClose_sampleBelowL`, `dlP`, `dlM`, `ExpValid`, `ArithmeticFP` | `Candidates/DiscreteLog.lean` and the ch. 2–4 candidate layer |
| `NUPPT.exists_comp`, `exists_compParam`, `exists_reparam`; run/coin readers; `Negligible` closure (`add`, `mono`, `negligible_two_pow_neg`) | `Complexity/Randomized/Closure.lean`, `Asymptotic/*`, `Foundations/Negligible.lean` |
| `simulate` and `OracleComp` laws, `buildComp_*`, `CostBoundedBy`, `bitCodec_*`, `ProbComp.expect_*`, `advantage_eq`, `accept_eq`, `prob_eq_until_bad` | `Games/*` |

## Proof route and checkpoints

1. **Checkpoint 1 · compression and collision shape (sketch steps 1–2).** Prove `Compresses` from `G.n₀` on (valid index, `|D_i| = 2m = 2(p − 1)`, `|R_i| = p − 1`, `h` lands in the units). Prove that a collision has `b ≠ b'` (`expF_injective`). Send this checkpoint.
2. **Checkpoint 2 · the reduction (sketch step 3).** Build `B(1^n, ⟨i, g^z⟩)`: run `A` on `⟨i, g^z⟩` and output `x − x' mod m` (or `x' − x`) from a collision. Prove it is a NUPPT and that it succeeds whenever `A` collides on that key. Send this checkpoint.
3. **Final · the key distribution (sketch step 4).** `A`'s key is `g^w` with `w` from the sampler, within `2^{-n}` of uniform (`statClose_sampleBelowL`). Conclude that `A`'s collision probability is at most `B`'s DL probability plus `2^{-n}`, negligible by `hDL`.

Check the edge cases: parameters below `G.n₀` (finite exception); invalid indices; `b = b'`; `x = x'`; inputs outside `D_i` (the `inDom` guard); `y = g^w` with `w = 0`.

If the sketch is wrong, or the target is false as stated, stop and escalate with the exact obligation: a
checkpoint with the counterexample or the missing fact. Do not weaken the statement.

## Scope and proof discipline

- **Owned file.** You own `Hashing/FromDiscreteLog.lean`. Replace the target's proof body and edit its sketch. Update the module title (drop
  "(statement phase)") and the `## Main results` status.
- **Helper modules.** They are permitted under `TCSlib/Cryptography/Hashing/FromDiscreteLog/`. The owned file imports them precisely and
  gets a `## Contents` list.
- **Size.** Keep every file below 1000 lines.
- **Frozen.** Do not edit any other file.
  - `Games/Efficiency.lean` is at 982 lines and must be split before it grows. Do not add to it.
  - If a lemma belongs in an existing file, put it in your helper module and list it as a promotion request.
  - If a reader of another file's definition is missing, escalate: record the exact obligation and the reader you
    need, and push a checkpoint.
- **Parallel fills.** Four Codex fills (`ext-nosrc`, `dl-crh`, `hash-sign`, `lamport`) and one Claude fill
  (`cca2-ett`) run from the same base. Edit only your own owned file and helper directory.
- **Duplication (binding).**
  - Do not copy public lemmas: import them.
  - Do not copy private lemmas of another file. If you need one, re-derive it from published readers in your helper
    module, disclose it in `REPORT.md` as **"overlap: <file> <item>"**, and keep its statement general.
  - Any other generic probability, machine or list fact goes on your promotion list. Grep first, and report the
    searches.
- **Statements.** Preserve the target statement, every other declaration, the statement prose and the global simp
  attributes.
- **Docstrings.** Public helpers get docstrings with their formulas, and proof sketches when nontrivial
  (policy §3). Add no `@[simp]`. A new public `abbrev` needs an `_eq`/`_iff` lemma.
- **Rule 10.** Use only published readers for other files' definitions, including generated matchers and
  projections. Your helper modules count as foreign to each other and to the owned file. The owned file's
  definitions are foreign to your helpers.

## Checks and report

- **Bootstrap.** Bootstrap from `order.txt` (170 modules) and the narrow `roots.txt` (87), following the
  addendum. Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree. Never run
  `lake build` or an unfiltered cache get. Run Python as `python3 -I`. Insert helper modules before their consumers.
- **Sweep.**
  - Recheck the owned module, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (22 declarations in 12 modules). The only change
    must be the removal of `dlHash_crh`.
- **Axioms.**
  - Print the axioms of `dlHash_crh`. Expect only `propext`, `Classical.choice` and `Quot.sound`.
  - Print them for every stored constant of the changed and new files.
- **Rule 10 evidence.**
  - Run whole-file seals A and B of every changed or new file over its full TCSlib import closure, at base and
    final, and report every failing declaration.
  - Add paired controls that pass unsealed and fail sealed, each sealed negative failing exactly once.
  - Run the explicit-unfold scan.
  - Report the seals with `PolyExpr.eval` both excluded as notation and sealed.
- **Lint.** Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b`. It must show no new FAIL.
- **Report.** Give:
  - the base and the target's status;
  - the changed files and the sketch edits;
  - the new declarations;
  - the promotion and reader requests;
  - every "overlap" item;
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

## ===== briefs/pass-shelat-ch5-8/gates/24-dl-crh/pr.diff.txt =====

diff --git a/TCSlib/Cryptography/Candidates/DiscreteLog.lean b/TCSlib/Cryptography/Candidates/DiscreteLog.lean
index 57dba465a..a423be2b5 100644
--- a/TCSlib/Cryptography/Candidates/DiscreteLog.lean
+++ b/TCSlib/Cryptography/Candidates/DiscreteLog.lean
@@ -481,6 +481,16 @@ def expGenFun {V : List Bool → Prop} (G : ExpGroupGen V) (z : List Bool) : Lis
     pairEncode (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z))) []
   else pairEncode dlDefaultIndex []
 
+/-- The raw index generator pairs the instance generator's output with the empty trapdoor
+when the parameter length is at least `G.n₀`, and otherwise pairs `dlDefaultIndex` with it:
+`expGenFun G z = if G.n₀ ≤ u.length then pairEncode o [] else pairEncode dlDefaultIndex []`,
+where `u = NUPPT.inParam z` and `o = G.gen.output (NUPPT.layout u [] [] (NUPPT.inCoins z))`. -/
+theorem expGenFun_eq {V : List Bool → Prop} (G : ExpGroupGen V) (z : List Bool) :
+    expGenFun G z =
+      if G.n₀ ≤ (NUPPT.inParam z).length then
+        pairEncode (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z))) []
+      else pairEncode dlDefaultIndex [] := rfl
+
 /-- The index generator's string function is polynomial-time: the threshold test compares
 the length of `1^n` with the constant `1^{n₀}` (`polyTimeComputable_lenLe`), then
 `polyTimeComputable_ite` between the instance generator's output and a constant. -/
@@ -643,6 +653,16 @@ def expSampleRaw (z : List Bool) : List Bool :=
     ((sampleBelowL (dlM (NUPPT.inArg z)) (Nat.size (dlM (NUPPT.inArg z)))
       (NUPPT.inParam z).length (NUPPT.inParam z).length (NUPPT.inCoins z)).getD 0)
 
+/-- The raw exponent sampler writes the result of `sampleBelowL m (Nat.size m) n n r`,
+with fallback zero, at the width of the input index:
+`expSampleRaw z = natToList (dlW i) ((sampleBelowL m (Nat.size m) n n r).getD 0)`, where
+`i = NUPPT.inArg z`, `m = dlM i`, and `n` and `r` are the input parameter length and coins. -/
+theorem expSampleRaw_eq (z : List Bool) :
+    expSampleRaw z =
+      natToList (dlW (NUPPT.inArg z))
+        ((sampleBelowL (dlM (NUPPT.inArg z)) (Nat.size (dlM (NUPPT.inArg z)))
+          (NUPPT.inParam z).length (NUPPT.inParam z).length (NUPPT.inCoins z)).getD 0) := rfl
+
 /-! ### The comparison test of the domain sampler (helper of `polyTimeComputable_expSampleRaw`) -/
 
 /-- The comparison test on a pair `⟨w, b⟩`: not `⟦w⟧ ≤ ⟦b⟧`, i.e. the trial value is below `⟦w⟧`. -/
diff --git a/TCSlib/Cryptography/Hashing.lean b/TCSlib/Cryptography/Hashing.lean
index c19d2562c..5240b73b9 100644
--- a/TCSlib/Cryptography/Hashing.lean
+++ b/TCSlib/Cryptography/Hashing.lean
@@ -4,6 +4,12 @@ Released under Apache 2.0 license as described in the file LICENSE.
 -/
 import TCSlib.Cryptography.Hashing.CollisionResistant
 import TCSlib.Cryptography.Hashing.FromDiscreteLog
+import TCSlib.Cryptography.Hashing.FromDiscreteLog.Algebra
+import TCSlib.Cryptography.Hashing.FromDiscreteLog.Coins
+import TCSlib.Cryptography.Hashing.FromDiscreteLog.Encoding
+import TCSlib.Cryptography.Hashing.FromDiscreteLog.Probability
+import TCSlib.Cryptography.Hashing.FromDiscreteLog.Reduction
+import TCSlib.Cryptography.Hashing.FromDiscreteLog.Sampling
 import TCSlib.Cryptography.Hashing.SIS
 
 set_option maxHeartbeats 0
diff --git a/TCSlib/Cryptography/Hashing/FromDiscreteLog.lean b/TCSlib/Cryptography/Hashing/FromDiscreteLog.lean
index 5f78f24b8..aa748c253 100644
--- a/TCSlib/Cryptography/Hashing/FromDiscreteLog.lean
+++ b/TCSlib/Cryptography/Hashing/FromDiscreteLog.lean
@@ -4,6 +4,12 @@ Released under Apache 2.0 license as described in the file LICENSE.
 -/
 import TCSlib.Cryptography.Hashing.CollisionResistant
 import TCSlib.Cryptography.Candidates.DiscreteLog
+import TCSlib.Cryptography.Hashing.FromDiscreteLog.Encoding
+import TCSlib.Cryptography.Hashing.FromDiscreteLog.Algebra
+import TCSlib.Cryptography.Hashing.FromDiscreteLog.Coins
+import TCSlib.Cryptography.Hashing.FromDiscreteLog.Reduction
+import TCSlib.Cryptography.Hashing.FromDiscreteLog.Probability
+import TCSlib.Cryptography.Hashing.FromDiscreteLog.Sampling
 import Mathlib.Tactic.Simps.Basic
 
 set_option maxHeartbeats 0
@@ -11,7 +17,7 @@ set_option relaxedAutoImplicit false
 set_option autoImplicit false
 
 /-!
-# A collision-resistant hash from discrete logarithms (statement phase)
+# A collision-resistant hash from discrete logarithms
 
 [PS10, Protocol 142.2]: `Gen(1^n)` outputs `(p, g, y)` with `p` an `n`-bit prime, `g` a
 generator of `Z_p^*` and `y` a random element of `Z_p^*`; `h_{p,g,y}(x, b) = y^b g^x mod p`.
@@ -22,8 +28,8 @@ compresses by one bit.
 `G : ExpGroupGen V` through the collection's generator `expGen` (indices `⟨p, ⟨m, g⟩⟩`, valid at
 every parameter, D10). `y = g^w` for `w` drawn by the collection's domain sampler
 (`expSampleRaw`, within `2^{-n}` of uniform on `Z_m`). Consequently `y` is within `2^{-n}`
-of uniform on `⟨g⟩`, and, when `m = p − 1` (hypothesis `hV` of the theorem), on `Z_p^*`. Arithmetic is through the bundle
-`ArithmeticFP` (D11), as for every ch. 2–4 candidate.
+of uniform on `⟨g⟩`, and, when `m = p − 1` (hypothesis `hV` of the theorem), on `Z_p^*`.
+Arithmetic is through the bundle `ArithmeticFP` (D11), as for every ch. 2–4 candidate.
 
 **Source notes.**
 - The domain: the source says "an `n`-bit string `x`", but its proof needs `x < p − 1`, since
@@ -40,7 +46,17 @@ of uniform on `⟨g⟩`, and, when `m = p − 1` (hypothesis `hV` of the theorem
 
 ## Main results
 
-* `Authentication.dlHash_crh` (Thm 142.3, stated; a `sorry` under the source's sketch).
+* `Authentication.dlHash_compresses`: the compression part of Theorem 142.3 (proved).
+* `Authentication.dlHash_crh`: Theorem 142.3 (proved).
+
+## Contents
+
+* `FromDiscreteLog.Encoding`: bounded domain/range cardinalities and bit-vector readers.
+* `FromDiscreteLog.Algebra`: collision shape and exponent extraction in the unit group.
+* `FromDiscreteLog.Coins`: coin splitting through published machine readers.
+* `FromDiscreteLog.Reduction`: the efficient collision-to-discrete-log machine.
+* `FromDiscreteLog.Probability`: collision acceptance as a uniform average.
+* `FromDiscreteLog.Sampling`: the statistical switch to uniform exponents.
 
 ## References
 
@@ -70,6 +86,23 @@ theorem dlHashIdx_eq (G : ExpGroupGen V) (z : List Bool) :
       pairFstD (expGenFun G (NUPPT.layout (NUPPT.inParam z) [] []
         ((NUPPT.inCoins z).take (G.gen.coins.eval (NUPPT.inParam z).length)))) := rfl
 
+/-- On generator coins followed by sampler coins, the raw hash index is the instance
+generator's output above its threshold and the fixed default index below it:
+`dlHashIdx G z₀ = if G.n₀ ≤ n then G.gen.runAt n [] r else dlDefaultIndex`, where
+`z₀ = NUPPT.layout (List.replicate n true) [] [] (List.ofFn r ++ s)`. -/
+theorem dlHashIdx_layout (G : ExpGroupGen V) (n : ℕ) (r : G.gen.Coins n)
+    (s : List Bool) :
+    dlHashIdx G (NUPPT.layout (List.replicate n true) [] [] (List.ofFn r ++ s)) =
+      if G.n₀ ≤ n then G.gen.runAt n [] r else dlDefaultIndex := by
+  have hr : (List.ofFn r).length = G.gen.coins.eval n := by
+    rw [List.length_ofFn, NUPPT.coinLen_eq]
+  simp only [dlHashIdx_eq, NUPPT.inParam_layout, NUPPT.inCoins_layout,
+    List.length_replicate, List.take_left' hr, expGenFun_eq]
+  split_ifs with hn
+  · rw [pairFstD_pairEncode, NUPPT.Uniform.runAt_eq G.gen_uniform,
+      NUPPT.layout_eq, NUPPT.advInput_eq]
+  · exact pairFstD_pairEncode _ _
+
 /-- `Gen` on the raw layout: the key `⟨i, y⟩`, with `i` the group index and `y = g^w mod p` for
 `w` drawn by the domain sampler from the remaining coins. -/
 def dlHashGenFun (G : ExpGroupGen V) (z : List Bool) : List Bool :=
@@ -85,6 +118,55 @@ theorem dlHashGenFun_eq (G : ExpGroupGen V) (z : List Bool) :
         (expSampleRaw (NUPPT.layout (NUPPT.inParam z) (dlHashIdx G z) []
           ((NUPPT.inCoins z).drop (G.gen.coins.eval (NUPPT.inParam z).length)))))) := rfl
 
+/-- Above the threshold, generator coins followed by sampler coins produce the group
+index and the exponentiation of the rejection-sampled exponent: for `G.n₀ ≤ n`,
+`dlHashGenFun G z₀ = pairEncode i (expEval (pairEncode i (natToList (dlW i) w)))`, where
+`z₀ = NUPPT.layout (List.replicate n true) [] [] (List.ofFn r ++ s)`, `i = G.gen.runAt n [] r`
+and `w = (sampleBelowL (dlM i) (Nat.size (dlM i)) n n s).getD 0` [PS10, Protocol 142.2]. -/
+theorem dlHashGenFun_layout (G : ExpGroupGen V) (n : ℕ) (r : G.gen.Coins n)
+    (s : List Bool) (hn : G.n₀ ≤ n) :
+    dlHashGenFun G (NUPPT.layout (List.replicate n true) [] [] (List.ofFn r ++ s)) =
+      pairEncode (G.gen.runAt n [] r)
+        (expEval (pairEncode (G.gen.runAt n [] r)
+          (natToList (dlW (G.gen.runAt n [] r))
+            ((sampleBelowL (dlM (G.gen.runAt n [] r))
+              (Nat.size (dlM (G.gen.runAt n [] r))) n n s).getD 0)))) := by
+  have hr : (List.ofFn r).length = G.gen.coins.eval n := by
+    rw [List.length_ofFn, NUPPT.coinLen_eq]
+  simp only [dlHashGenFun_eq, dlHashIdx_layout, if_pos hn, NUPPT.inParam_layout,
+    NUPPT.inCoins_layout, List.length_replicate, List.drop_left' hr, expSampleRaw_eq]
+  simp only [NUPPT.inArg_layout]
+
+/-- Above the generator threshold, every raw generated key has the form `⟨i, g^z⟩`
+for an exponent in the domain of its valid group index: for `G.n₀ ≤ n`,
+`∃ z : ZMod (expOrd i), dlHashGenFun G z₀ = pairEncode i (expF i z)`, where
+`i = G.gen.runAt n [] r` and `z₀ = NUPPT.layout (List.replicate n true) [] [] (List.ofFn r ++ s)`
+[PS10, Protocol 142.2].
+
+**Proof sketch.** Every accepted rejection-sampler output is below `m`; its fallback zero
+is also below the positive group order. Its residue therefore has exactly that value,
+so the sampler's numeral is the canonical exponent encoding. -/
+theorem dlHashGenFun_key (G : ExpGroupGen V) (hV : ∀ i, V i → ExpValid i)
+    (n : ℕ) (r : G.gen.Coins n) (s : List Bool) (hn : G.n₀ ≤ n) :
+    ∃ z : ZMod (expOrd (G.gen.runAt n [] r)),
+      dlHashGenFun G (NUPPT.layout (List.replicate n true) [] [] (List.ofFn r ++ s)) =
+        pairEncode (G.gen.runAt n [] r) (expF (G.gen.runAt n [] r) z) := by
+  let i := G.gen.runAt n [] r
+  let w := (sampleBelowL (dlM i) (Nat.size (dlM i)) n n s).getD 0
+  have hi : ExpValid i := hV _ (G.valid n r hn)
+  have hw : w < dlM i := by
+    cases hs : sampleBelowL (dlM i) (Nat.size (dlM i)) n n s with
+    | none =>
+      simpa only [w, hs, Option.getD_none] using ((expValid_iff i).1 hi).2.1
+    | some v =>
+      simpa only [w, hs, Option.getD_some] using sampleBelowL_lt hs
+  let z : ZMod (expOrd i) := (w : ℕ)
+  have hz : z.val = w := by
+    change ((w : ℕ) : ZMod (expOrd i)).val = w
+    rw [ZMod.val_natCast, expOrd_of_valid hi, Nat.mod_eq_of_lt hw]
+  refine ⟨z, ?_⟩
+  rw [dlHashGenFun_layout G n r s hn, ← expEval_spec i z, expEnc_eq, hz]
+
 /-- `g^x mod p` on `⟨1^n, ⟨⟨i, y⟩, xb⟩⟩`, with `x` the first `n` bits of `xb`. -/
 def dlHashPow (z : List Bool) : List Bool :=
   expEval (pairEncode (pairFstD (pairFstD (pairSndD z)))
@@ -97,6 +179,31 @@ theorem dlHashPow_eq (z : List Bool) :
       expEval (pairEncode (pairFstD (pairFstD (pairSndD z)))
         ((pairSndD (pairSndD z)).take (pairFstD z).length)) := rfl
 
+/-- At a well-formed valid index, the exponentiation part reads the first `n` input bits
+and returns the `n`-bit numeral of their power of `g` modulo `p`:
+`dlHashPow a = natToList n (dlG i ^ x₀ % dlP i)`, where
+`a = atParam n (pairEncode (pairEncode i y) (List.ofFn x))` and
+`x₀ = listToNat ((List.ofFn x).take n) < dlM i`. -/
+theorem dlHashPow_atParam (n : ℕ) (i y : List Bool) (x : Fin (n + 1) → Bool)
+    (hi : ExpValid i) (hw : WellFormedIndex n i)
+    (hx : listToNat ((List.ofFn x).take n) < dlM i) :
+    dlHashPow (atParam n (pairEncode (pairEncode i y) (List.ofFn x))) =
+      natToList n (dlG i ^ listToNat ((List.ofFn x).take n) % dlP i) := by
+  have he : expEnc i
+      ((listToNat ((List.ofFn x).take n) : ℕ) : ZMod (expOrd i)) =
+      (List.ofFn x).take n := by
+    rw [expEnc_eq, hw.dlW_eq, ZMod.val_natCast, expOrd_of_valid hi,
+      Nat.mod_eq_of_lt hx]
+    have hcanon := natToList_length_listToNat ((List.ofFn x).take n)
+    simpa only [List.length_take, List.length_ofFn,
+      Nat.min_eq_left (Nat.le_succ n)] using hcanon
+  have hs := expEval_spec i
+    ((listToNat ((List.ofFn x).take n) : ℕ) : ZMod (expOrd i))
+  rw [he, expF_eq, hw.dlW_eq, ZMod.val_natCast, expOrd_of_valid hi,
+    Nat.mod_eq_of_lt hx] at hs
+  simpa only [dlHashPow_eq, atParam_eq, pairFstD_pairEncode,
+    pairSndD_pairEncode, List.length_replicate] using hs
+
 /-- `y · g^x mod p` on `⟨1^n, ⟨⟨i, y⟩, xb⟩⟩`: one multiplication and one reduction modulo `p`. -/
 def dlHashMul (z : List Bool) : List Bool :=
   pairSndD (divModStr (pairEncode
@@ -111,6 +218,30 @@ theorem dlHashMul_eq (z : List Bool) :
         (mulStr (pairEncode (dlHashPow z) (pairSndD (pairFstD (pairSndD z)))))
         (pairFstD (pairFstD (pairFstD (pairSndD z)))))) := rfl
 
+/-- The multiplication part returns the `n`-bit numeral of the power of `g` times the
+key element, reduced modulo `p`, at a valid well-formed index:
+`dlHashMul a = natToList n ((dlG i ^ x₀ % dlP i * listToNat y) % dlP i)`, where
+`a = atParam n (pairEncode (pairEncode i y) (List.ofFn x))` and
+`x₀ = listToNat ((List.ofFn x).take n) < dlM i`. -/
+theorem dlHashMul_atParam (n : ℕ) (i y : List Bool) (x : Fin (n + 1) → Bool)
+    (hi : ExpValid i) (hw : WellFormedIndex n i)
+    (hx : listToNat ((List.ofFn x).take n) < dlM i) :
+    dlHashMul (atParam n (pairEncode (pairEncode i y) (List.ofFn x))) =
+      natToList n
+        ((dlG i ^ listToNat ((List.ofFn x).take n) % dlP i * listToNat y) % dlP i) := by
+  have hw' : (pairFstD i).length = n := by
+    obtain ⟨a, b, c, he, ha, _, _⟩ := (wellFormedIndex_iff n i).1 hw
+    rw [he, pairFstD_pairEncode]
+    exact ha
+  have hp : dlP i < 2 ^ n := by
+    simpa only [hw.dlW_eq] using dlP_lt_two_pow i
+  have hpow : dlG i ^ listToNat ((List.ofFn x).take n) % dlP i < 2 ^ n :=
+    (Nat.mod_lt _ ((expValid_iff i).1 hi).1.pos).trans hp
+  rw [dlHashMul_eq, dlHashPow_atParam n i y x hi hw hx]
+  simp only [atParam_eq, pairFstD_pairEncode, pairSndD_pairEncode,
+    divModStr_pairEncode, listToNat_mulStr, hw']
+  rw [← dlP_eq i, listToNat_natToList hpow]
+
 /-- **The hash** `h_{p,g,y}(x, b) = y^b g^x mod p` on `⟨1^n, ⟨⟨i, y⟩, xb⟩⟩`, with `x` the first
 `n` bits of `xb` and `b` its bit at position `n`: one modular exponentiation, and for `b = 1` one
 multiplication and one reduction modulo `p` (`dlHashMul`), each a numeral of the width of `p`. -/
@@ -125,6 +256,122 @@ theorem dlHashEval_eq (z : List Bool) :
       if ((pairSndD (pairSndD z)).drop (pairFstD z).length).headD false then dlHashMul z
       else dlHashPow z := rfl
 
+/-- Hash evaluation at a valid well-formed index is the `n`-bit numeral of `g^x mod p`
+for selector false, and of `(g^x mod p) y mod p` for selector true:
+`dlHashEval a = natToList n (if x (Fin.last n) then (e * listToNat y) % dlP i else e)`, where
+`a = atParam n (pairEncode (pairEncode i y) (List.ofFn x))`, `e = dlG i ^ x₀ % dlP i` and
+`x₀ = listToNat ((List.ofFn x).take n) < dlM i` [PS10, Protocol 142.2]. -/
+theorem dlHashEval_atParam (n : ℕ) (i y : List Bool) (x : Fin (n + 1) → Bool)
+    (hi : ExpValid i) (hw : WellFormedIndex n i)
+    (hx : listToNat ((List.ofFn x).take n) < dlM i) :
+    dlHashEval (atParam n (pairEncode (pairEncode i y) (List.ofFn x))) =
+      natToList n (if x (Fin.last n) then
+        (dlG i ^ listToNat ((List.ofFn x).take n) % dlP i * listToNat y) % dlP i
+        else dlG i ^ listToNat ((List.ofFn x).take n) % dlP i) := by
+  rw [dlHashEval_eq, dlHashMul_atParam n i y x hi hw hx,
+    dlHashPow_atParam n i y x hi hw hx]
+  simp only [atParam_eq, pairFstD_pairEncode, pairSndD_pairEncode,
+    List.length_replicate, FromDiscreteLog.inputWord_drop, List.headD_cons]
+  split_ifs <;> rfl
+
+/-- For the key element `g^z`, evaluation writes the residue of the unit
+`(if b then g^z else 1) * g^x`, where `x` is the exponent prefix and `b` is the last bit:
+`dlHashEval a = natToList n (v : ZMod (dlP i)).val`, where
+`a = atParam n (pairEncode (pairEncode i (expF i z)) (List.ofFn x))`, the unit is
+`v = (if x (Fin.last n) then u ^ z.val else 1) * u ^ x₀ : (ZMod (dlP i))ˣ`, `u = expUnit hi`
+and `x₀ = listToNat ((List.ofFn x).take n) < dlM i` [PS10, Protocol 142.2]. -/
+theorem dlHashEval_expF (n : ℕ) (i : List Bool) (z : ZMod (expOrd i))
+    (x : Fin (n + 1) → Bool) (hi : ExpValid i) (hw : WellFormedIndex n i)
+    (hx : listToNat ((List.ofFn x).take n) < dlM i) :
+    dlHashEval (atParam n (pairEncode (pairEncode i (expF i z)) (List.ofFn x))) =
+      natToList n
+        (((if x (Fin.last n) then expUnit hi ^ z.val else 1) *
+          expUnit hi ^ listToNat ((List.ofFn x).take n) : (ZMod (dlP i))ˣ) :
+            ZMod (dlP i)).val := by
+  have hp : dlP i < 2 ^ n := by
+    simpa only [hw.dlW_eq] using dlP_lt_two_pow i
+  have hz : dlG i ^ z.val % dlP i < 2 ^ n :=
+    (Nat.mod_lt _ ((expValid_iff i).1 hi).1.pos).trans hp
+  rw [dlHashEval_atParam n i (expF i z) x hi hw hx, expF_eq, hw.dlW_eq,
+    listToNat_natToList hz]
+  cases hb : x (Fin.last n)
+  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul,
+      FromDiscreteLog.expUnit_pow_val]
+  · simp only [↓reduceIte, Units.val_mul, ZMod.val_mul,
+      FromDiscreteLog.expUnit_pow_val]
+    rw [Nat.mul_comm]
+
+/-- Equal evaluations on two distinct domain inputs force different selectors and reveal
+the challenge exponent as the corresponding difference modulo `m`: if `x ≠ x'`, `x₀ < m`,
+`x₀' < m` and `dlHashEval a = dlHashEval a'`, then `x (Fin.last n) ≠ x' (Fin.last n)` and
+`z.val = if x (Fin.last n) then (x₀' + (m - x₀)) % m else (x₀ + (m - x₀')) % m`, where
+`a = atParam n (pairEncode (pairEncode i (expF i z)) (List.ofFn x))` (`a'` likewise for `x'`),
+`x₀ = listToNat ((List.ofFn x).take n)`, `x₀'` likewise and `m = dlM i`
+[PS10, proof of Theorem 142.3].
+
+**Proof sketch.** Evaluation writes the residue of the associated unit. Equal fixed-width
+numerals therefore give equal units. The unit-group collision lemma rules out equal
+selectors and extracts the unique exponent residue. -/
+theorem dlHashEval_collision (n : ℕ) (i : List Bool) (z : ZMod (expOrd i))
+    (x x' : Fin (n + 1) → Bool) (hi : ExpValid i) (hw : WellFormedIndex n i)
+    (hx : listToNat ((List.ofFn x).take n) < dlM i)
+    (hx' : listToNat ((List.ofFn x').take n) < dlM i) (hne : x ≠ x')
+    (hc : dlHashEval (atParam n (pairEncode (pairEncode i (expF i z)) (List.ofFn x))) =
+      dlHashEval (atParam n (pairEncode (pairEncode i (expF i z)) (List.ofFn x')))) :
+    x (Fin.last n) ≠ x' (Fin.last n) ∧ z.val =
+      if x (Fin.last n) then
+        (listToNat ((List.ofFn x').take n) +
+          (dlM i - listToNat ((List.ofFn x).take n))) % dlM i
+      else (listToNat ((List.ofFn x).take n) +
+          (dlM i - listToNat ((List.ofFn x').take n))) % dlM i := by
+  haveI : NeZero (dlP i) := ⟨((expValid_iff i).1 hi).1.ne_zero⟩
+  have hp : dlP i < 2 ^ n := by
+    simpa only [hw.dlW_eq] using dlP_lt_two_pow i
+  have hbound (u : (ZMod (dlP i))ˣ) : (u : ZMod (dlP i)).val < 2 ^ n :=
+    (ZMod.val_lt _).trans hp
+  rw [dlHashEval_expF n i z x hi hw hx, dlHashEval_expF n i z x' hi hw hx'] at hc
+  have hv := natToList_injOn (hbound _) (hbound _) hc
+  have hu := Units.ext (ZMod.val_injective (dlP i) hv)
+  have hd : (listToNat ((List.ofFn x).take n), x (Fin.last n)) ≠
+      (listToNat ((List.ofFn x').take n), x' (Fin.last n)) := by
+    intro he
+    exact hne (FromDiscreteLog.inputWord_num_ext
+      (congrArg Prod.fst he) (congrArg Prod.snd he))
+  exact FromDiscreteLog.unitCollision_extract hi hx hx' z hd hu
+
+/-- Evaluation on a domain input at a valid well-formed key has exactly `n` bits and
+reads as a positive residue below `p`:
+`(dlHashEval a).length = n ∧ 0 < listToNat (dlHashEval a) ∧ listToNat (dlHashEval a) < dlP i`,
+where `a = atParam n (pairEncode (pairEncode i (expF i z)) (List.ofFn x))` and
+`listToNat ((List.ofFn x).take n) < dlM i` [PS10, compression in Theorem 142.3].
+
+**Proof sketch.** The evaluation is the numeral of a unit's residue. A unit has positive
+residue below `p`, and the well-formed width is large enough to encode it exactly. -/
+theorem dlHashEval_range (n : ℕ) (i : List Bool) (z : ZMod (expOrd i))
+    (x : Fin (n + 1) → Bool) (hi : ExpValid i) (hw : WellFormedIndex n i)
+    (hx : listToNat ((List.ofFn x).take n) < dlM i) :
+    (dlHashEval (atParam n (pairEncode (pairEncode i (expF i z)) (List.ofFn x)))).length = n ∧
+      0 < listToNat (dlHashEval (atParam n
+        (pairEncode (pairEncode i (expF i z)) (List.ofFn x)))) ∧
+      listToNat (dlHashEval (atParam n
+        (pairEncode (pairEncode i (expF i z)) (List.ofFn x)))) < dlP i := by
+  have hp2 : 2 ≤ dlP i := ((expValid_iff i).1 hi).1.two_le
+  haveI : Fact (1 < dlP i) := ⟨by omega⟩
+  haveI : NeZero (dlP i) := ⟨by omega⟩
+  let u : (ZMod (dlP i))ˣ :=
+    (if x (Fin.last n) then expUnit hi ^ z.val else 1) *
+      expUnit hi ^ listToNat ((List.ofFn x).take n)
+  have hpw : dlP i < 2 ^ n := by
+    simpa only [hw.dlW_eq] using dlP_lt_two_pow i
+  have hval : (u : ZMod (dlP i)).val < 2 ^ n := (ZMod.val_lt _).trans hpw
+  have hu := units_val_mem u
+  rw [dlHashEval_expF n i z x hi hw hx]
+  change (natToList n (u : ZMod (dlP i)).val).length = n ∧
+    0 < listToNat (natToList n (u : ZMod (dlP i)).val) ∧
+      listToNat (natToList n (u : ZMod (dlP i)).val) < dlP i
+  rw [length_natToList, listToNat_natToList hval]
+  exact ⟨rfl, lt_of_lt_of_le Nat.zero_lt_one hu.1, ZMod.val_lt _⟩
+
 /-! ### Efficiency -/
 
 /-- The group index of `Gen` is polynomial-time. -/
@@ -214,6 +461,292 @@ noncomputable def dlHash (H : ArithmeticFP) (G : ExpGroupGen V) : CRH where
 
 attribute [simps (config := { isSimp := false }) domLen rangeLen gen eval inDom inRange] dlHash
 
+/-- The hash generator uses the instance generator's coin polynomial plus `n²` sampler
+coins: `(dlHash H G).gen.coins = .add G.gen.coins (.mul .var .var)` [PS10, Protocol 142.2]. -/
+theorem dlHash_gen_coins (H : ArithmeticFP) (G : ExpGroupGen V) :
+    (dlHash H G).gen.coins = .add G.gen.coins (.mul .var .var) := by
+  rw [dlHash_gen, NUPPT.coins_ofPolyTimeUniform]
+
+/-- The hash generator's coins are the instance generator's coins and an independent
+`n²`-bit sampler tape: `(dlHash H G).gen.Coins n ≃ G.gen.Coins n × (Fin (n * n) → Bool)`
+[PS10, Protocol 142.2]. -/
+noncomputable def dlHash_coinsEquiv (H : ArithmeticFP) (G : ExpGroupGen V) (n : ℕ) :
+    (dlHash H G).gen.Coins n ≃ G.gen.Coins n × (Fin (n * n) → Bool) :=
+  (FromDiscreteLog.sumCoinsEquiv (dlHash H G).gen (dlHash_gen_coins H G) n).trans
+    (Equiv.prodCongr (NUPPT.coinsEquivPoly (A := G.gen) rfl n).symm
+      (Equiv.arrowCongr (finCongr (by rw [PolyExpr.eval_mul, PolyExpr.eval_var]))
+        (Equiv.refl Bool)))
+
+/-- The hash coin equivalence splits the sum polynomial, identifies its first component
+with the generator's coins, and reads the second component as `n²` bits:
+`dlHash_coinsEquiv H G n = (sumCoinsEquiv (dlHash H G).gen _ n).trans (Equiv.prodCongr e₁ e₂)`,
+where `e₁ = (NUPPT.coinsEquivPoly (A := G.gen) rfl n).symm` and
+`e₂ = Equiv.arrowCongr (finCongr _) (Equiv.refl Bool)` transports
+`(.mul .var .var).eval n = n * n`. -/
+theorem dlHash_coinsEquiv_eq (H : ArithmeticFP) (G : ExpGroupGen V) (n : ℕ) :
+    dlHash_coinsEquiv H G n =
+      (FromDiscreteLog.sumCoinsEquiv (dlHash H G).gen (dlHash_gen_coins H G) n).trans
+        (Equiv.prodCongr (NUPPT.coinsEquivPoly (A := G.gen) rfl n).symm
+          (Equiv.arrowCongr (finCongr (by rw [PolyExpr.eval_mul, PolyExpr.eval_var]))
+            (Equiv.refl Bool))) := rfl
+
+/-- Combining a generator tape and a sampler tape concatenates their encoded words:
+`List.ofFn ((dlHash_coinsEquiv H G n).symm (r, s)) = List.ofFn r ++ List.ofFn s`. -/
+theorem dlHash_coinsEquiv_symm_ofFn (H : ArithmeticFP) (G : ExpGroupGen V) (n : ℕ)
+    (r : G.gen.Coins n) (s : Fin (n * n) → Bool) :
+    List.ofFn ((dlHash_coinsEquiv H G n).symm (r, s)) = List.ofFn r ++ List.ofFn s := by
+  rw [dlHash_coinsEquiv_eq, Equiv.symm_trans_apply, Equiv.prodCongr_symm,
+    Equiv.prodCongr_apply, Equiv.symm_symm, FromDiscreteLog.sumCoinsEquiv_symm_ofFn,
+    Prod.map_fst, Prod.map_snd, NUPPT.coinsEquivPoly_ofFn,
+    Equiv.arrowCongr_symm, finCongr_symm, Equiv.refl_symm,
+    ofFn_arrowCongr_finCongr]
+
+/-- On recombined generator and sampler coins, the hash generator runs its raw function
+on their concatenation:
+`(dlHash H G).gen.runAt n [] ((dlHash_coinsEquiv H G n).symm (r, s)) = dlHashGenFun G z₀`,
+where `z₀ = NUPPT.layout (List.replicate n true) [] [] (List.ofFn r ++ List.ofFn s)`
+[PS10, Protocol 142.2]. -/
+theorem dlHash_gen_runAt (H : ArithmeticFP) (G : ExpGroupGen V) (n : ℕ)
+    (r : G.gen.Coins n) (s : Fin (n * n) → Bool) :
+    (dlHash H G).gen.runAt n [] ((dlHash_coinsEquiv H G n).symm (r, s)) =
+      dlHashGenFun G (NUPPT.layout (List.replicate n true) [] []
+        (List.ofFn r ++ List.ofFn s)) := by
+  rw [NUPPT.runAt_eq, dlHash_coinsEquiv_symm_ofFn, dlHash_gen,
+    NUPPT.runAtL_ofPolyTimeUniform, NUPPT.advInput_eq, NUPPT.layout_eq]
+
+/-- The discrete-log hash compresses at every parameter above the instance generator's
+threshold when its groups are the full unit groups:
+`(∀ i, V i → ExpValid i ∧ dlM i = dlP i - 1) → (dlHash H G).Compresses` [PS10, Theorem 142.3].
+
+**Proof sketch.** Split a generated key's coins into the instance and sampler tapes. Its
+index is valid and well formed, and its key element is a power of the generator. Evaluation
+therefore lands in the positive residues. There are `2m` domain inputs and `p - 1 = m`
+range values, with `m > 0`. -/
+theorem dlHash_compresses (H : ArithmeticFP) (G : ExpGroupGen V)
+    (hV : ∀ i, V i → ExpValid i ∧ dlM i = dlP i - 1) : (dlHash H G).Compresses := by
+  rw [CRH.compresses_iff]
+  refine ⟨G.n₀, ?_⟩
+  intro n hn rg
+  obtain ⟨⟨r, s⟩, rfl⟩ := (dlHash_coinsEquiv H G n).symm.surjective rg
+  rw [dlHash_gen_runAt]
+  obtain ⟨z, hkey⟩ := dlHashGenFun_key G (fun i hi => (hV i hi).1)
+    n r (List.ofFn s) hn
+  rw [hkey]
+  have hi := (hV _ (G.valid n r hn)).1
+  have hmfull := (hV _ (G.valid n r hn)).2
+  have hw := G.wellFormed n r hn
+  have hp : dlP (G.gen.runAt n [] r) < 2 ^ n := by
+    simpa only [hw.dlW_eq] using dlP_lt_two_pow (G.gen.runAt n [] r)
+  have hm : dlM (G.gen.runAt n [] r) < 2 ^ n :=
+    ((expValid_iff _).1 hi).2.2.1.trans hp
+  simp only [dlHash_inDom, dlHash_inRange, CRH.hash_eq, dlHash_eval,
+    pairFstD_pairEncode, decide_eq_true_eq]
+  simp only [dlHash_domLen, dlHash_rangeLen, PolyExpr.eval_add, PolyExpr.eval_var,
+    PolyExpr.eval_const]
+  constructor
+  · intro x hx
+    have hr := dlHashEval_range n _ z x hi hw hx
+    rw [ofFn_padFin_of_length hr.1]
+    exact hr.2
+  · rw [FromDiscreteLog.card_boundedInput n _ hm.le,
+      FromDiscreteLog.card_boundedRange n _ ((expValid_iff _).1 hi).1.pos hp.le,
+      ← hmfull]
+    have hpos := ((expValid_iff _).1 hi).2.1
+    omega
+
+/-- The collision test for a raw finder output on key `⟨i, y⟩`: its two padded inputs
+are distinct, have exponent prefixes below `m`, and have equal padded hash values,
+`dlHashCollision n i y raw = (x₀ < dlM i ∧ x₀' < dlM i ∧ xx.1 ≠ xx.2 ∧ h xx.1 = h xx.2)`, where
+`xx = splitBits (padFin ((n + 1) + (n + 1)) raw)` (blocks of `n + 1` bits),
+`x₀ = listToNat ((List.ofFn xx.1).take n)`, `x₀'` likewise for `xx.2`, and
+`h v = padFin n (dlHashEval (atParam n (pairEncode (pairEncode i y) (List.ofFn v))))`
+[PS10, Definition 140.1]. -/
+def dlHashCollision (n : ℕ) (i y raw : List Bool) : Prop :=
+  let xx := splitBits (a := n + 1) (b := n + 1) (padFin ((n + 1) + (n + 1)) raw)
+  listToNat ((List.ofFn xx.1).take n) < dlM i ∧
+    listToNat ((List.ofFn xx.2).take n) < dlM i ∧ xx.1 ≠ xx.2 ∧
+    padFin n (dlHashEval (atParam n (pairEncode (pairEncode i y) (List.ofFn xx.1)))) =
+      padFin n (dlHashEval (atParam n (pairEncode (pairEncode i y) (List.ofFn xx.2))))
+
+/-- The raw collision predicate is exactly the domain, distinctness, and equal-hash test
+on its two padded output halves:
+`dlHashCollision n i y raw ↔ x₀ < dlM i ∧ x₀' < dlM i ∧ xx.1 ≠ xx.2 ∧ h xx.1 = h xx.2`,
+with `xx`, `x₀`, `x₀'` and `h` as in `dlHashCollision`. -/
+theorem dlHashCollision_iff (n : ℕ) (i y raw : List Bool) :
+    dlHashCollision n i y raw ↔
+      let xx := splitBits (a := n + 1) (b := n + 1) (padFin ((n + 1) + (n + 1)) raw)
+      listToNat ((List.ofFn xx.1).take n) < dlM i ∧
+        listToNat ((List.ofFn xx.2).take n) < dlM i ∧ xx.1 ≠ xx.2 ∧
+        padFin n (dlHashEval (atParam n (pairEncode (pairEncode i y) (List.ofFn xx.1)))) =
+          padFin n (dlHashEval (atParam n (pairEncode (pairEncode i y) (List.ofFn xx.2)))) :=
+  Iff.rfl
+
+/-- Above the generator threshold, collision acceptance is the average over instance
+coins of the joint probability over sampler and finder coins of the raw collision test:
+for `G.n₀ ≤ n`, `accept ((dlHash H G).collisionGame A n) = uexp (fun r => uprob (fun rs =>`
+`dlHashCollision n i y (A.runAt n (pairEncode i y) rs.2)))` over `r : G.gen.Coins n` and
+`rs : (Fin (n * n) → Bool) × A.Coins n`, where `i = G.gen.runAt n [] r`,
+`y = expEval (pairEncode i (natToList n w))` and
+`w = (sampleBelowL (dlM i) (Nat.size (dlM i)) n n (List.ofFn rs.1)).getD 0`
+[PS10, key distribution in Theorem 142.3].
+
+**Proof sketch.** Reindex the generator's uniform coins by their two independent tapes,
+read its activation, and expose the collision game's fields through their public readers.
+Fubini combines the sampler and finder tapes into a product probability. -/
+theorem dlHash_collision_accept_eq (H : ArithmeticFP) (G : ExpGroupGen V) (A : NUPPT)
+    (n : ℕ) (hn : G.n₀ ≤ n) :
+    accept ((dlHash H G).collisionGame A n) =
+      uexp (fun r : G.gen.Coins n =>
+        uprob (fun rs : (Fin (n * n) → Bool) × A.Coins n =>
+          let i := G.gen.runAt n [] r
+          let y := expEval (pairEncode i (natToList n
+            ((sampleBelowL (dlM i) (Nat.size (dlM i)) n n (List.ofFn rs.1)).getD 0)))
+          dlHashCollision n i y (A.runAt n (pairEncode i y) rs.2))) := by
+  rw [FromDiscreteLog.collision_accept_eq,
+    ← HardcoreBit.uexp_comp_equiv (dlHash_coinsEquiv H G n).symm,
+    HardcoreBit.uexp_prod]
+  congr 1
+  funext r
+  rw [uprob_prod]
+  congr 1
+  funext s
+  apply OneWay.uprob_congr
+  intro ra
+  rw [dlHash_gen_runAt, dlHashGenFun_layout G n r (List.ofFn s) hn]
+  have hw := G.wellFormed n r hn
+  simp only [dlHashCollision_iff, dlHash_inDom, CRH.hash_eq, dlHash_eval,
+    pairFstD_pairEncode, decide_eq_true_eq, hw.dlW_eq]
+  simp only [dlHash_domLen, dlHash_rangeLen, PolyExpr.eval_add, PolyExpr.eval_var,
+    PolyExpr.eval_const]
+
+/-- Whenever the finder produces a collision on a valid key `⟨i, g^z⟩`, the reduction's
+answer decodes to the challenge exponent: if the finder's output
+`A.runAt n k (NUPPT.coinsCongr (collisionReduction_coins H A) n r)` passes the
+`dlHashCollision n i (expF i z)` test (stated unfolded), then
+`∃ out : Fin n → Bool, decodeFin n (B.runAt n k r) = some out ∧ bitsToNat out = z.val`, where
+`k = pairEncode i (expF i z)` and `B = collisionReduction H A`
+[PS10, reduction in Theorem 142.3].
+
+**Proof sketch.** Remove the hash-output padding using its proved exact length. The
+collision-extraction lemma identifies the postprocessor's modular difference with `z`.
+The reduction therefore writes the canonical `n`-bit numeral of `z`, which decodes exactly. -/
+theorem dlHash_reduction_success (H : ArithmeticFP) (A : NUPPT) (n : ℕ)
+    (i : List Bool) (z : ZMod (expOrd i)) (hi : ExpValid i) (hw : WellFormedIndex n i)
+    (r : (FromDiscreteLog.collisionReduction H A).Coins n)
+    (hc :
+      let xx := splitBits (a := n + 1) (b := n + 1)
+        (padFin ((n + 1) + (n + 1)) (A.runAt n (pairEncode i (expF i z))
+          (NUPPT.coinsCongr (FromDiscreteLog.collisionReduction_coins H A) n r)))
+      listToNat ((List.ofFn xx.1).take n) < dlM i ∧
+        listToNat ((List.ofFn xx.2).take n) < dlM i ∧ xx.1 ≠ xx.2 ∧
+        padFin n (dlHashEval (atParam n (pairEncode (pairEncode i (expF i z))
+          (List.ofFn xx.1)))) =
+        padFin n (dlHashEval (atParam n (pairEncode (pairEncode i (expF i z))
+          (List.ofFn xx.2))))) :
+    ∃ out : Fin n → Bool,
+      decodeFin n ((FromDiscreteLog.collisionReduction H A).runAt n
+        (pairEncode i (expF i z)) r) = some out ∧ bitsToNat out = z.val := by
+  let key := pairEncode i (expF i z)
+  let ra := NUPPT.coinsCongr (FromDiscreteLog.collisionReduction_coins H A) n r
+  let xx := splitBits (a := n + 1) (b := n + 1)
+    (padFin ((n + 1) + (n + 1)) (A.runAt n key ra))
+  change listToNat ((List.ofFn xx.1).take n) < dlM i ∧
+    listToNat ((List.ofFn xx.2).take n) < dlM i ∧ xx.1 ≠ xx.2 ∧
+      padFin n (dlHashEval (atParam n (pairEncode key (List.ofFn xx.1)))) =
+        padFin n (dlHashEval (atParam n (pairEncode key (List.ofFn xx.2)))) at hc
+  obtain ⟨hx, hx', hne, hhash⟩ := hc
+  have heq : dlHashEval (atParam n (pairEncode key (List.ofFn xx.1))) =
+      dlHashEval (atParam n (pairEncode key (List.ofFn xx.2))) := by
+    have hh := congrArg List.ofFn hhash
+    change List.ofFn (padFin n (dlHashEval (atParam n (pairEncode key (List.ofFn xx.1))))) =
+      List.ofFn (padFin n (dlHashEval (atParam n (pairEncode key (List.ofFn xx.2))))) at hh
+    rw [ofFn_padFin_of_length (dlHashEval_range n i z xx.1 hi hw hx).1,
+      ofFn_padFin_of_length (dlHashEval_range n i z xx.2 hi hw hx').1] at hh
+    exact hh
+  have hz := (dlHashEval_collision n i z xx.1 xx.2 hi hw hx hx' hne heq).2
+  have hb := FromDiscreteLog.collisionReduction_runAt H A n key r
+  rw [FromDiscreteLog.collisionPost_split n i (expF i z) _ hw] at hb
+  have hanswer : (FromDiscreteLog.collisionReduction H A).runAt n key r =
+      natToList n z.val := hb.trans (congrArg (natToList n) hz.symm)
+  refine ⟨natToBits n z.val, ?_, ?_⟩
+  · rw [hanswer, natToList_eq, decodeFin_ofFn]
+  · exact bitsToNat_natToBits (by
+      simpa only [hw.dlW_eq] using val_lt_two_pow_dlW i z)
+
+/-- For a fixed valid well-formed index and a uniform challenge exponent, the finder's
+collision probability is bounded by the reduction's discrete-log success probability:
+`uprob CA ≤ uprob DB`, where `CA (z, r) = dlHashCollision n i (expF i z) (A.runAt n k r)` on
+`ZMod (expOrd i) × A.Coins n`, and on `ZMod (expOrd i) × B.Coins n`,
+`DB (z, r) = ∃ out : Fin n → Bool, decodeFin n (B.runAt n k r) = some out ∧ bitsToNat out = z.val`,
+with `k = pairEncode i (expF i z)` and `B = collisionReduction H A`
+[PS10, reduction in Theorem 142.3].
+
+**Proof sketch.** Reindex the reduction's coins by the finder's equal-length coin tape.
+Every collision in the reindexed experiment implies successful decoding of the challenge
+exponent by the pointwise reduction theorem. Monotonicity of uniform probability concludes. -/
+theorem dlHash_ideal_collision_le (H : ArithmeticFP) (A : NUPPT) (n : ℕ)
+    (i : List Bool) (hi : ExpValid i) (hw : WellFormedIndex n i) :
+    uprob (fun zr : ZMod (expOrd i) × A.Coins n =>
+      dlHashCollision n i (expF i zr.1) (A.runAt n (pairEncode i (expF i zr.1)) zr.2)) ≤
+      uprob (fun zr : ZMod (expOrd i) × (FromDiscreteLog.collisionReduction H A).Coins n =>
+        ∃ out : Fin n → Bool,
+          decodeFin n ((FromDiscreteLog.collisionReduction H A).runAt n
+            (pairEncode i (expF i zr.1)) zr.2) = some out ∧ bitsToNat out = zr.1.val) := by
+  rw [← uprob_comp_equiv (Equiv.prodCongr (Equiv.refl (ZMod (expOrd i)))
+    (NUPPT.coinsCongr (FromDiscreteLog.collisionReduction_coins H A) n))]
+  apply uprob_mono
+  intro zr hc
+  have hh : dlHashCollision n i (expF i zr.1)
+      (A.runAt n (pairEncode i (expF i zr.1))
+        (NUPPT.coinsCongr (FromDiscreteLog.collisionReduction_coins H A) n zr.2)) := by
+    simpa only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply] using hc
+  exact dlHash_reduction_success H A n i zr.1 hi hw zr.2
+    ((dlHashCollision_iff n i (expF i zr.1) _).1 hh)
+
+/-- Above the generator threshold, collision acceptance is at most the concrete
+reduction's discrete-log success probability plus `(1/2)^n`: for `G.n₀ ≤ n`,
+`accept ((dlHash H G).collisionGame A n) ≤ G.dlProb (collisionReduction H A) n + (1/2)^n`
+[PS10, probability bound in Theorem 142.3].
+
+**Proof sketch.** Read the honest key distribution as the average over instance coins
+and independent sampler/finder tapes. The bounded sampler is within `(1/2)^n` of a
+uniform exponent. For the uniform experiment every collision makes the reduction
+succeed. Average the pointwise bounds and identify the discrete-log experiment. -/
+theorem dlHash_collision_bound (H : ArithmeticFP) (G : ExpGroupGen V)
+    (hV : ∀ i, V i → ExpValid i) (A : NUPPT) (n : ℕ) (hn : G.n₀ ≤ n) :
+    accept ((dlHash H G).collisionGame A n) ≤
+      G.dlProb (FromDiscreteLog.collisionReduction H A) n + (1 / 2 : ℝ) ^ n := by
+  rw [dlHash_collision_accept_eq H G A n hn, ExpGroupGen.dlProb_eq]
+  calc
+    _ ≤ uexp (fun r : G.gen.Coins n =>
+        uprob (fun zr : ZMod (expOrd (G.gen.runAt n [] r)) × A.Coins n =>
+          dlHashCollision n (G.gen.runAt n [] r) (expF _ zr.1)
+            (A.runAt n (pairEncode (G.gen.runAt n [] r) (expF _ zr.1)) zr.2)) +
+          (1 / 2 : ℝ) ^ n) := by
+      apply HardcoreBit.uexp_mono
+      intro r
+      have hi := hV _ (G.valid n r hn)
+      have hw := G.wellFormed n r hn
+      have hp : dlP (G.gen.runAt n [] r) < 2 ^ n := by
+        simpa only [hw.dlW_eq] using dlP_lt_two_pow (G.gen.runAt n [] r)
+      have hm : dlM (G.gen.runAt n [] r) < 2 ^ n :=
+        ((expValid_iff _).1 hi).2.2.1.trans hp
+      have hs := FromDiscreteLog.sampleBelowL_uprob_le hi hm
+        (ρ := A.Coins n) (fun v ra =>
+          let i := G.gen.runAt n [] r
+          let y := expEval (pairEncode i (natToList n v))
+          dlHashCollision n i y (A.runAt n (pairEncode i y) ra))
+      simpa only [FromDiscreteLog.expEval_natToList_val hw] using hs
+    _ = uexp (fun r : G.gen.Coins n =>
+        uprob (fun zr : ZMod (expOrd (G.gen.runAt n [] r)) × A.Coins n =>
+          dlHashCollision n (G.gen.runAt n [] r) (expF _ zr.1)
+            (A.runAt n (pairEncode (G.gen.runAt n [] r) (expF _ zr.1)) zr.2))) +
+          (1 / 2 : ℝ) ^ n := by
+      rw [HardcoreBit.uexp_add, HardcoreBit.uexp_const]
+    _ ≤ _ := add_le_add_right (HardcoreBit.uexp_mono fun r =>
+      dlHash_ideal_collision_le H A n _ (hV _ (G.valid n r hn))
+        (G.wellFormed n r hn)) _
+
 /-- **Theorem 142.3: Protocol 142.2 is a collision-resistant hash compressing by one bit**
 [PS10, Theorem 142.3], under the discrete-log assumption for an instance generator of the full
 groups `Z_p^*` (`m = p − 1`).
@@ -234,6 +767,19 @@ groups `Z_p^*` (`m = p − 1`).
 theorem dlHash_crh (H : ArithmeticFP) (G : ExpGroupGen V)
     (hV : ∀ i, V i → ExpValid i ∧ dlM i = dlP i - 1) (hDL : G.DLHard) :
     (dlHash H G).Compresses ∧ (dlHash H G).CollisionResistant := by
-  sorry
+  refine ⟨dlHash_compresses H G hV, ?_⟩
+  rw [CRH.collisionResistant_iff]
+  intro A
+  have hhard := (ExpGroupGen.dlHard_iff G).1 hDL
+    (FromDiscreteLog.collisionReduction H A)
+  have hhalf : Negligible (fun n : ℕ => (1 / 2 : ℝ) ^ n) := by
+    simpa only [one_div] using negligible_two_pow_neg
+  have hneg : Negligible (fun n => accept ((dlHash H G).collisionGame A n)) := by
+    refine (hhard.add hhalf).mono ⟨G.n₀, ?_⟩
+    intro n hn
+    rw [abs_of_nonneg (accept_nonneg _),
+      abs_of_nonneg (add_nonneg (G.dlProb_nonneg _ n) (pow_nonneg (by norm_num) _))]
+    exact dlHash_collision_bound H G (fun i hi => (hV i hi).1) A n hn
+  exact ⟨_, hneg, fun _ => le_rfl⟩
 
 end TCSlib.Cryptography.Authentication
diff --git a/TCSlib/Cryptography/Hashing/FromDiscreteLog/Algebra.lean b/TCSlib/Cryptography/Hashing/FromDiscreteLog/Algebra.lean
new file mode 100644
index 000000000..b4f079b8f
--- /dev/null
+++ b/TCSlib/Cryptography/Hashing/FromDiscreteLog/Algebra.lean
@@ -0,0 +1,134 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Candidates.DiscreteLog
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Recovering a discrete logarithm from a hash collision
+
+The algebraic part of the reduction in Theorem 142.3 works in the group of units.
+Equal selector bits force equal bounded exponents. With different selector bits,
+the collision determines the challenge exponent as a difference modulo the order.
+
+## Main definitions
+
+There are no new definitions.
+
+## Main results
+
+* `expUnit_pow_val` reads powers of the generator unit as modular exponentiation.
+* `unitCollision_selector_ne` rules out a collision with equal selector bits.
+* `unitCollision_extract` gives the residue extracted from a collision.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
+  2010, §5.5.2, proof of Theorem 142.3.
+-/
+
+namespace TCSlib.Cryptography.Authentication.FromDiscreteLog
+
+open TCSlib.Cryptography.Candidates
+
+/-- The residue of the generator unit raised to `e` is `g ^ e mod p` at a valid index,
+where `g = dlG i` and `p = dlP i`. -/
+theorem expUnit_pow_val {i : List Bool} (hi : ExpValid i) (e : ℕ) :
+    ((expUnit hi ^ e : (ZMod (dlP i))ˣ) : ZMod (dlP i)).val = dlG i ^ e % dlP i := by
+  have hvalid := (expValid_iff i).1 hi
+  haveI : NeZero (dlP i) := ⟨hvalid.1.ne_zero⟩
+  rw [val_units_pow, coe_expUnit, ZMod.val_natCast,
+    Nat.mod_eq_of_lt hvalid.2.2.2.2.1]
+
+/-- If adding `b ≤ m` to a residue `a < m` gives `c` modulo `m`, then adding
+`m - b` to `c` recovers `a` modulo `m`. -/
+private theorem residue_difference {m a b c : ℕ} (ha : a < m) (hb : b ≤ m)
+    (h : Nat.ModEq m (a + b) c) : a = (c + (m - b)) % m := by
+  have hh : (a + b + (m - b)) % m = (c + (m - b)) % m :=
+    Nat.ModEq.add_right (m - b) h
+  have heq : a + b + (m - b) = a + m := by omega
+  rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt ha] at hh
+  exact hh
+
+/-- In the group of a valid index, `g^a g^b = g^c` with `a,b < m` recovers
+`a = (c + (m - b)) mod m`, where `m` is the order of `g`. -/
+private theorem residue_of_unit_pow_mul {i : List Bool} (hi : ExpValid i)
+    {a b c : ℕ} (ha : a < dlM i) (hb : b < dlM i)
+    (h : expUnit hi ^ a * expUnit hi ^ b = expUnit hi ^ c) :
+    a = (c + (dlM i - b)) % dlM i := by
+  have hp : expUnit hi ^ (a + b) = expUnit hi ^ c := by
+    rw [pow_add]
+    exact h
+  have hm := pow_eq_pow_iff_modEq.1 hp
+  rw [orderOf_expUnit hi] at hm
+  exact residue_difference ha hb.le hm
+
+/-- A collision between two distinct bounded exponent/selector pairs has different
+selector bits: if `(x, b) ≠ (x', b')`, `x < dlM i`, `x' < dlM i` and
+`(if b then u ^ z.val else 1) * u ^ x = (if b' then u ^ z.val else 1) * u ^ x'` for
+`u = expUnit hi`, then `b ≠ b'` [PS10, proof of Theorem 142.3].
+
+**Proof sketch.** With equal selectors, cancel their common unit factor. Read the
+remaining powers through their numerals and apply the published injectivity of
+exponentiation. The bounded exponent residues, and hence the two pairs, are equal. -/
+theorem unitCollision_selector_ne {i : List Bool} (hi : ExpValid i)
+    {x x' : ℕ} (hx : x < dlM i) (hx' : x' < dlM i)
+    (z : ZMod (expOrd i)) {b b' : Bool}
+    (hdistinct : (x, b) ≠ (x', b'))
+    (hcollision :
+      (if b then expUnit hi ^ z.val else 1) * expUnit hi ^ x =
+      (if b' then expUnit hi ^ z.val else 1) * expUnit hi ^ x') : b ≠ b' := by
+  intro hb
+  subst b'
+  have hp : expUnit hi ^ x = expUnit hi ^ x' := mul_left_cancel hcollision
+  have hxord : x < expOrd i := by rw [expOrd_of_valid hi]; exact hx
+  have hxord' : x' < expOrd i := by rw [expOrd_of_valid hi]; exact hx'
+  have hxval : ((x : ℕ) : ZMod (expOrd i)).val = x := ZMod.val_cast_of_lt hxord
+  have hxval' : ((x' : ℕ) : ZMod (expOrd i)).val = x' := ZMod.val_cast_of_lt hxord'
+  have hnum := congrArg (fun u : (ZMod (dlP i))ˣ => (u : ZMod (dlP i)).val) hp
+  change ((expUnit hi ^ x : (ZMod (dlP i))ˣ) : ZMod (dlP i)).val =
+    ((expUnit hi ^ x' : (ZMod (dlP i))ˣ) : ZMod (dlP i)).val at hnum
+  rw [expUnit_pow_val hi x, expUnit_pow_val hi x'] at hnum
+  have hf : expF i ((x : ℕ) : ZMod (expOrd i)) =
+      expF i ((x' : ℕ) : ZMod (expOrd i)) := by
+    rw [expF_eq, expF_eq, hxval, hxval', hnum]
+  have hres := congrArg (fun z : ZMod (expOrd i) => z.val) (expF_injective hi hf)
+  change ((x : ℕ) : ZMod (expOrd i)).val = ((x' : ℕ) : ZMod (expOrd i)).val at hres
+  rw [hxval, hxval'] at hres
+  exact hdistinct (Prod.ext hres rfl)
+
+/-- A collision between distinct bounded exponent/selector pairs reveals the
+challenge exponent: it is `(x' + (m - x)) mod m` when the first selector is true,
+and `(x + (m - x')) mod m` otherwise, that is,
+`b ≠ b' ∧ z.val = if b then (x' + (m - x)) % m else (x + (m - x')) % m` for `m = dlM i`,
+under the hypotheses of `unitCollision_selector_ne` [PS10, proof of Theorem 142.3].
+
+**Proof sketch.** Equal selectors are impossible by cancellation. In the two remaining
+cases the collision reads either `g^z g^x = g^x'` or `g^z g^x' = g^x`. The order of
+the generator turns each equality into a congruence, and adding the complement of
+the second exponent recovers the unique challenge residue below the order. -/
+theorem unitCollision_extract {i : List Bool} (hi : ExpValid i)
+    {x x' : ℕ} (hx : x < dlM i) (hx' : x' < dlM i)
+    (z : ZMod (expOrd i)) {b b' : Bool}
+    (hdistinct : (x, b) ≠ (x', b'))
+    (hcollision :
+      (if b then expUnit hi ^ z.val else 1) * expUnit hi ^ x =
+      (if b' then expUnit hi ^ z.val else 1) * expUnit hi ^ x') :
+    b ≠ b' ∧ z.val =
+      if b then (x' + (dlM i - x)) % dlM i else (x + (dlM i - x')) % dlM i := by
+  have hne := unitCollision_selector_ne hi hx hx' z hdistinct hcollision
+  refine ⟨hne, ?_⟩
+  have hz : z.val < dlM i := lt_of_lt_of_eq (ZMod.val_lt z) (expOrd_of_valid hi)
+  cases b <;> cases b'
+  · exact (hne rfl).elim
+  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hcollision ⊢
+    exact residue_of_unit_pow_mul hi hz hx' hcollision.symm
+  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hcollision ⊢
+    exact residue_of_unit_pow_mul hi hz hx hcollision
+  · exact (hne rfl).elim
+
+end TCSlib.Cryptography.Authentication.FromDiscreteLog
diff --git a/TCSlib/Cryptography/Hashing/FromDiscreteLog/Coins.lean b/TCSlib/Cryptography/Hashing/FromDiscreteLog/Coins.lean
new file mode 100644
index 000000000..8805d7d15
--- /dev/null
+++ b/TCSlib/Cryptography/Hashing/FromDiscreteLog/Coins.lean
@@ -0,0 +1,67 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Complexity.Randomized.PPT
+import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Splitting a machine's coin polynomial
+
+A machine whose coin polynomial is a sum can read its coins as two consecutive bit vectors.
+The equivalence below combines the published machine-coin identification, an equality of
+evaluated polynomial lengths, and the shared coin-splitting equivalence.
+
+## Main definitions
+
+* `sumCoinsEquiv` splits the coins of a machine with coin polynomial `c + d`.
+
+## Main results
+
+* `sumCoinsEquiv_symm_ofFn` reads the reassembled coin string as a concatenation.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
+  2010, §5.5.2, Protocol 142.2 and the proof of Theorem 142.3.
+-/
+
+namespace TCSlib.Cryptography.Authentication.FromDiscreteLog
+
+open Complexity TCSlib.Cryptography
+
+/-- A machine with coin polynomial `c + d` has coins equivalent to a `c(n)`-bit vector and
+a `d(n)`-bit vector: for `h : A.coins = .add c d`,
+`A.Coins n ≃ (Fin (c.eval n) → Bool) × (Fin (d.eval n) → Bool)`. -/
+def sumCoinsEquiv (A : NUPPT) {c d : PolyExpr} (h : A.coins = .add c d) (n : ℕ) :
+    A.Coins n ≃ (Fin (c.eval n) → Bool) × (Fin (d.eval n) → Bool) :=
+  (NUPPT.coinsEquivPoly h n).trans
+    ((Equiv.arrowCongr (finCongr (PolyExpr.eval_add c d n)) (Equiv.refl Bool)).trans
+      (splitCoins (c.eval n) (d.eval n)))
+
+/-- The sum-coin equivalence first identifies the machine's polynomial-length coin vector,
+then transports its length through evaluation of addition and applies `splitCoins`:
+`sumCoinsEquiv A h n = (NUPPT.coinsEquivPoly h n).trans (e.trans s)`, where
+`e = Equiv.arrowCongr (finCongr (PolyExpr.eval_add c d n)) (Equiv.refl Bool)` and
+`s = splitCoins (c.eval n) (d.eval n)`. -/
+theorem sumCoinsEquiv_eq (A : NUPPT) {c d : PolyExpr} (h : A.coins = .add c d) (n : ℕ) :
+    sumCoinsEquiv A h n =
+      (NUPPT.coinsEquivPoly h n).trans
+        ((Equiv.arrowCongr (finCongr (PolyExpr.eval_add c d n)) (Equiv.refl Bool)).trans
+          (splitCoins (c.eval n) (d.eval n))) := rfl
+
+/-- Reassembling the two components of a machine's sum-length coins concatenates their
+words: `ofFn (sumCoinsEquiv.symm (r, s)) = ofFn r ++ ofFn s`. -/
+theorem sumCoinsEquiv_symm_ofFn (A : NUPPT) {c d : PolyExpr}
+    (h : A.coins = .add c d) (n : ℕ)
+    (r : Fin (c.eval n) → Bool) (s : Fin (d.eval n) → Bool) :
+    List.ofFn ((sumCoinsEquiv A h n).symm (r, s)) = List.ofFn r ++ List.ofFn s := by
+  rw [sumCoinsEquiv_eq, Equiv.symm_trans_apply, NUPPT.coinsEquivPoly_symm_ofFn,
+    Equiv.symm_trans_apply, Equiv.arrowCongr_symm]
+  rw [finCongr_symm, Equiv.refl_symm, ofFn_arrowCongr_finCongr, ofFn_splitCoins_symm]
+
+end TCSlib.Cryptography.Authentication.FromDiscreteLog
diff --git a/TCSlib/Cryptography/Hashing/FromDiscreteLog/Encoding.lean b/TCSlib/Cryptography/Hashing/FromDiscreteLog/Encoding.lean
new file mode 100644
index 000000000..cca76894e
--- /dev/null
+++ b/TCSlib/Cryptography/Hashing/FromDiscreteLog/Encoding.lean
@@ -0,0 +1,199 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Candidates.Arithmetic
+import TCSlib.Cryptography.Asymptotic.Adversary
+import TCSlib.Cryptography.Authentication.Encoding
+import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Bounded exponents with a selector bit
+
+The domain in Protocol 142.2 consists of an `n`-bit numeral below a bound `m`, followed
+by one unrestricted selector bit. These encoding lemmas identify that domain with
+`Fin m × Bool`.
+
+## Main definitions
+
+* `boundedInputEquiv` pairs a bounded exponent with its final selector bit.
+
+## Main results
+
+* `ofFn_splitBits_fst`, `ofFn_splitBits_snd` read the words of two consecutive bit vectors.
+* `inputWord_num_ext` reconstructs an input from its exponent value and selector bit.
+* `card_boundedInput` gives `2 * m` inputs when `m ≤ 2 ^ n`.
+* `card_boundedRange` gives `p - 1` positive `n`-bit numerals below `p`.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
+  2010, §5.5.2, Protocol 142.2 and the proof of Theorem 142.3.
+-/
+
+namespace TCSlib.Cryptography.Authentication.FromDiscreteLog
+
+open TCSlib.Cryptography TCSlib.Cryptography.Candidates TCSlib.Cryptography.NumberTheory
+
+/-- The word of the first component of `splitBits w` is the first `a` bits of `w`:
+`List.ofFn (splitBits w).1 = (List.ofFn w).take a`. -/
+theorem ofFn_splitBits_fst {a b : ℕ} (w : Fin (a + b) → Bool) :
+    List.ofFn (splitBits w).1 = (List.ofFn w).take a := by
+  have hfst : (splitBits w).1 = fun j : Fin a => w (Fin.castAdd b j) :=
+    funext fun j => splitBits_fst w j
+  rw [hfst]
+  have hwindow := ofFn_drop_take w 0 a (by omega)
+  simpa only [List.drop_zero, Nat.zero_add] using hwindow.symm
+
+/-- The word of the second component of `splitBits w` is the word of `w` after its first
+`a` bits: `List.ofFn (splitBits w).2 = (List.ofFn w).drop a`. -/
+theorem ofFn_splitBits_snd {a b : ℕ} (w : Fin (a + b) → Bool) :
+    List.ofFn (splitBits w).2 = (List.ofFn w).drop a := by
+  have hsnd : (splitBits w).2 = fun j : Fin b => w (Fin.natAdd a j) :=
+    funext fun j => splitBits_snd w j
+  rw [hsnd]
+  have hwindow := ofFn_drop_take w a b (by omega)
+  have hlen : ((List.ofFn w).drop a).length = b := by
+    simp only [List.length_drop, List.length_ofFn, Nat.add_sub_cancel_left]
+  rw [List.take_of_length_le hlen.le] at hwindow
+  exact hwindow.symm
+
+/-- The word of an `(n + 1)`-bit vector is its first `n` bits followed by its final bit:
+`List.ofFn x = List.ofFn (fun j : Fin n => x j.castSucc) ++ [x (Fin.last n)]`. -/
+theorem inputWord_split {n : ℕ} (x : Fin (n + 1) → Bool) :
+    List.ofFn x = List.ofFn (fun j : Fin n => x j.castSucc) ++ [x (Fin.last n)] := by
+  rw [List.ofFn_succ', List.concat_eq_append]
+
+/-- Taking the first `n` bits of an `(n + 1)`-bit word gives its restricted vector:
+`(List.ofFn x).take n = List.ofFn (fun j : Fin n => x j.castSucc)`. -/
+theorem inputWord_take {n : ℕ} (x : Fin (n + 1) → Bool) :
+    (List.ofFn x).take n = List.ofFn (fun j : Fin n => x j.castSucc) := by
+  rw [inputWord_split, List.take_left' (by simp)]
+
+/-- Dropping the first `n` bits of an `(n + 1)`-bit word leaves its final bit:
+`(List.ofFn x).drop n = [x (Fin.last n)]`. -/
+theorem inputWord_drop {n : ℕ} (x : Fin (n + 1) → Bool) :
+    (List.ofFn x).drop n = [x (Fin.last n)] := by
+  rw [inputWord_split, List.drop_left' (by simp)]
+
+/-- An `(n + 1)`-bit input is determined by its first `n` bits and its final bit:
+`(List.ofFn x).take n = (List.ofFn y).take n → x (Fin.last n) = y (Fin.last n) → x = y`. -/
+theorem inputWord_ext {n : ℕ} {x y : Fin (n + 1) → Bool}
+    (hprefix : (List.ofFn x).take n = (List.ofFn y).take n)
+    (hlast : x (Fin.last n) = y (Fin.last n)) : x = y := by
+  apply List.ofFn_injective
+  rw [inputWord_split x, inputWord_split y, ← inputWord_take x, ← inputWord_take y,
+    hprefix, hlast]
+
+/-- An `(n + 1)`-bit input is determined by the number read from its first `n` bits
+and its final selector bit: `x = y` whenever `x (Fin.last n) = y (Fin.last n)` and
+`listToNat ((List.ofFn x).take n) = listToNat ((List.ofFn y).take n)`. -/
+theorem inputWord_num_ext {n : ℕ} {x y : Fin (n + 1) → Bool}
+    (hnum : listToNat ((List.ofFn x).take n) = listToNat ((List.ofFn y).take n))
+    (hlast : x (Fin.last n) = y (Fin.last n)) : x = y := by
+  refine inputWord_ext ?_ hlast
+  have hxlen : ((List.ofFn x).take n).length = n := by
+    rw [inputWord_take, List.length_ofFn]
+  have hylen : ((List.ofFn y).take n).length = n := by
+    rw [inputWord_take, List.length_ofFn]
+  have hxcanon := natToList_length_listToNat ((List.ofFn x).take n)
+  have hycanon := natToList_length_listToNat ((List.ofFn y).take n)
+  rw [hxlen] at hxcanon
+  rw [hylen] at hycanon
+  have hword := congrArg (natToList n) hnum
+  rw [hxcanon, hycanon] at hword
+  exact hword
+
+/-- Bounded `(n + 1)`-bit inputs are exactly pairs of an exponent in `Fin m` and a selector
+bit, provided `m ≤ 2 ^ n` [PS10, Protocol 142.2].
+
+**Proof sketch.** Read the first `n` bits as the exponent and keep the last bit. In the other
+direction write the exponent as an `n`-bit numeral and append the selector. Numeral
+canonicity and the decomposition of an `(n + 1)`-bit vector prove the inverse laws. -/
+noncomputable def boundedInputEquiv (n m : ℕ) (hm : m ≤ 2 ^ n) :
+    {x : Fin (n + 1) → Bool // listToNat ((List.ofFn x).take n) < m} ≃ Fin m × Bool where
+  toFun x := (⟨listToNat ((List.ofFn x.1).take n), x.2⟩, x.1 (Fin.last n))
+  invFun z := ⟨padFin (n + 1) (natToList n z.1.val ++ [z.2]), by
+    rw [ofFn_padFin_of_length (by simp), List.take_left' (by simp),
+      listToNat_natToList (z.1.2.trans_le hm)]
+    exact z.1.2⟩
+  left_inv x := by
+    apply Subtype.ext
+    apply List.ofFn_injective
+    rw [ofFn_padFin_of_length (by simp)]
+    have hlen : ((List.ofFn x.1).take n).length = n := by
+      simp
+    have hcanon := natToList_length_listToNat ((List.ofFn x.1).take n)
+    rw [hlen] at hcanon
+    rw [hcanon, inputWord_take, inputWord_split x.1]
+  right_inv z := by
+    apply Prod.ext
+    · apply Fin.ext
+      change listToNat ((List.ofFn
+        (padFin (n + 1) (natToList n z.1.val ++ [z.2]))).take n) = z.1.val
+      rw [ofFn_padFin_of_length (by simp), List.take_left' (by simp),
+        listToNat_natToList (z.1.2.trans_le hm)]
+    · have hword := inputWord_drop
+        (padFin (n + 1) (natToList n z.1.val ++ [z.2]))
+      rw [ofFn_padFin_of_length (by simp), List.drop_left' (by simp)] at hword
+      exact List.singleton_inj.mp hword.symm
+
+/-- The bounded-input equivalence reads the exponent and the final selector bit:
+`boundedInputEquiv n m hm x = (⟨listToNat ((List.ofFn x.1).take n), x.2⟩, x.1 (Fin.last n))`. -/
+theorem boundedInputEquiv_apply (n m : ℕ) (hm : m ≤ 2 ^ n)
+    (x : {x : Fin (n + 1) → Bool // listToNat ((List.ofFn x).take n) < m}) :
+    boundedInputEquiv n m hm x =
+      (⟨listToNat ((List.ofFn x.1).take n), x.2⟩, x.1 (Fin.last n)) := rfl
+
+/-- The inverse equivalence writes an `n`-bit exponent and appends its selector bit:
+`((boundedInputEquiv n m hm).symm z).1 = padFin (n + 1) (natToList n z.1.val ++ [z.2])`. -/
+theorem boundedInputEquiv_symm_apply (n m : ℕ) (hm : m ≤ 2 ^ n) (z : Fin m × Bool) :
+    ((boundedInputEquiv n m hm).symm z).1 =
+      padFin (n + 1) (natToList n z.1.val ++ [z.2]) := rfl
+
+/-- There are `2 * m` bounded exponents with a selector bit when `m ≤ 2 ^ n`
+[PS10, proof of Theorem 142.3]. -/
+theorem card_boundedInput (n m : ℕ) (hm : m ≤ 2 ^ n) :
+    Fintype.card {x : Fin (n + 1) → Bool // listToNat ((List.ofFn x).take n) < m} = 2 * m := by
+  classical
+  rw [Fintype.card_congr (boundedInputEquiv n m hm), Fintype.card_prod, Fintype.card_fin,
+    Fintype.card_bool, Nat.mul_comm]
+
+/-- There are `p - 1` positive `n`-bit numerals below `p` when `0 < p ≤ 2 ^ n`
+[PS10, proof of Theorem 142.3].
+
+**Proof sketch.** Subtract one from the numeral's value to identify the range with
+`Fin (p - 1)`. The inverse writes `j + 1` in `n` bits. Reading and writing numerals are
+inverse on values below `2 ^ n`. -/
+theorem card_boundedRange (n p : ℕ) (hp : 0 < p) (hpw : p ≤ 2 ^ n) :
+    Fintype.card {y : Fin n → Bool //
+      0 < listToNat (List.ofFn y) ∧ listToNat (List.ofFn y) < p} = p - 1 := by
+  classical
+  let e : {y : Fin n → Bool //
+      0 < listToNat (List.ofFn y) ∧ listToNat (List.ofFn y) < p} ≃ Fin (p - 1) :=
+    { toFun := fun y => ⟨listToNat (List.ofFn y.1) - 1, by
+        have hpos := y.2.1
+        have hlt := y.2.2
+        omega⟩
+      invFun := fun j => ⟨natToBits n (j.val + 1), by
+        have hj : j.val + 1 < p := by have := j.2; omega
+        rw [← bitsToNat_eq_listToNat, bitsToNat_natToBits (hj.trans_le hpw)]
+        exact ⟨by omega, hj⟩⟩
+      left_inv := fun y => by
+        apply Subtype.ext
+        change natToBits n (listToNat (List.ofFn y.1) - 1 + 1) = y.1
+        have hpos : 1 ≤ listToNat (List.ofFn y.1) := by have := y.2.1; omega
+        rw [Nat.sub_add_cancel hpos, ← bitsToNat_eq_listToNat, natToBits_bitsToNat]
+      right_inv := fun j => by
+        apply Fin.ext
+        change listToNat (List.ofFn (natToBits n (j.val + 1))) - 1 = j.val
+        have hj : j.val + 1 < p := by have := j.2; omega
+        rw [← bitsToNat_eq_listToNat, bitsToNat_natToBits (hj.trans_le hpw)]
+        omega }
+  rw [Fintype.card_congr e, Fintype.card_fin]
+
+end TCSlib.Cryptography.Authentication.FromDiscreteLog
diff --git a/TCSlib/Cryptography/Hashing/FromDiscreteLog/Probability.lean b/TCSlib/Cryptography/Hashing/FromDiscreteLog/Probability.lean
new file mode 100644
index 000000000..d27c5c702
--- /dev/null
+++ b/TCSlib/Cryptography/Hashing/FromDiscreteLog/Probability.lean
@@ -0,0 +1,73 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Hashing.CollisionResistant
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Collision-game acceptance as a uniform average
+
+The collision game's two samples can be read as the existing uniform expectation
+over generator coins and uniform probability over finder coins. This provides the
+probability interface used by the discrete-logarithm reduction.
+
+## Main definitions
+
+There are no new definitions.
+
+## Main results
+
+* `expect_sample_eq_uexp` identifies finite uniform sampling with `uexp`.
+* `collision_accept_eq` reads collision-game acceptance as a nested uniform average.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
+  2010, Definition 140.1 and proof of Theorem 142.3.
+-/
+
+namespace TCSlib.Cryptography.Authentication.FromDiscreteLog
+
+open Complexity TCSlib.Cryptography TCSlib.Cryptography.Games
+
+/-- The expectation of `f` after sampling a nonempty finite type is the uniform
+average `uexp f`: `ProbComp.expect (ProbComp.sample α) f = uexp f`. Both expressions
+are the sum of `f` divided by the type's size. -/
+theorem expect_sample_eq_uexp {α : Type} [Fintype α] [Nonempty α] (f : α → ℝ) :
+    ProbComp.expect (ProbComp.sample α) f = uexp f := by
+  rw [ProbComp.expect_sample, uexp_def, inv_mul_eq_div]
+
+/-- Collision-game acceptance is the average over generator coins of the probability,
+over finder coins, that the two padded output halves are distinct domain elements
+with equal hashes: `accept (C.collisionGame A n) = uexp (fun rg => uprob (fun r => W rg r))`,
+where `W rg r` is `C.inDom n i xx.1 = true ∧ C.inDom n i xx.2 = true ∧ xx.1 ≠ xx.2 ∧`
+`C.hash n i xx.1 = C.hash n i xx.2` for `i = C.gen.runAt n [] rg` and
+`xx = splitBits (padFin (C.domLen.eval n + C.domLen.eval n) (A.runAt n i r))`
+[PS10, Definition 140.1].
+
+**Proof sketch.** Read the collision game and apply total probability to its two
+samples. A pure Boolean verdict accepts exactly when its collision predicate holds;
+the finite sampling expectations are the existing uniform average and probability. -/
+theorem collision_accept_eq (C : CRH) (A : NUPPT) (n : ℕ) :
+    accept (C.collisionGame A n) =
+      uexp (fun rg : C.gen.Coins n =>
+        uprob (fun r : A.Coins n =>
+          let i := C.gen.runAt n [] rg
+          let xx := splitBits
+            (padFin (C.domLen.eval n + C.domLen.eval n) (A.runAt n i r))
+          C.inDom n i xx.1 = true ∧ C.inDom n i xx.2 = true ∧ xx.1 ≠ xx.2 ∧
+            C.hash n i xx.1 = C.hash n i xx.2)) := by
+  classical
+  rw [accept_eq, CRH.collisionGame_eq, ProbComp.prob_bind, expect_sample_eq_uexp]
+  congr 1
+  funext rg
+  rw [ProbComp.prob_bind, expect_sample_eq_uexp, uprob_eq_uexp]
+  congr 1
+  funext r
+  simp only [ProbComp.prob_pure, decide_eq_true_eq]
+
+end TCSlib.Cryptography.Authentication.FromDiscreteLog
diff --git a/TCSlib/Cryptography/Hashing/FromDiscreteLog/Reduction.lean b/TCSlib/Cryptography/Hashing/FromDiscreteLog/Reduction.lean
new file mode 100644
index 000000000..d6a54f0eb
--- /dev/null
+++ b/TCSlib/Cryptography/Hashing/FromDiscreteLog/Reduction.lean
@@ -0,0 +1,374 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Candidates.Arithmetic
+import TCSlib.Cryptography.Candidates.DiscreteLog
+import TCSlib.Cryptography.Asymptotic.CollectionsLemmas
+import TCSlib.Cryptography.Hashing.FromDiscreteLog.Encoding
+import TCSlib.Complexity.Randomized.Closure
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The discrete-logarithm reduction's machine
+
+The reduction runs a collision finder on the supplied key, reads its two padded
+domain inputs, and writes their exponent difference modulo the supplied order.
+Its arithmetic uses the polynomial-time bundle and its coins and advice are the
+collision finder's coins and advice.
+
+## Main definitions
+
+* `modularDifference` computes a subtraction modulo an encoded order.
+* `collisionPost` reads the key and padded finder output and selects the difference.
+* `reductionRaw`, `collisionReduction` run the finder and apply the postprocessor.
+
+## Main results
+
+* `polyTimeComputable_collisionPost` proves postprocessing is polynomial-time.
+* `collisionPost_ofFn_append` reads the postprocessor on two fixed-width inputs.
+* `collisionPost_split` reads the postprocessor on an arbitrary raw finder output.
+* `collisionReduction_runAtL` gives the reduction's exact activation.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
+  2010, §5.5.2, proof of Theorem 142.3.
+-/
+
+namespace TCSlib.Cryptography.Authentication.FromDiscreteLog
+
+open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Candidates
+
+/-- The encoded modular difference of `a` and `b` modulo `m` is computed as
+`(a + (m - b)) mod m`, using truncated natural subtraction. When `b ≤ m`, this
+represents the group difference; the output has the width of `m`. -/
+def modularDifference (a b m : List Bool) : List Bool :=
+  pairSndD (divModStr (pairEncode
+    (addStr (pairEncode a (subStr (pairEncode m b)))) m))
+
+/-- The modular-difference routine adds `a` to the truncated subtraction of `b`
+from `m`, divides by `m`, and keeps the remainder:
+`modularDifference a b m = pairSndD (divModStr (pairEncode (addStr (pairEncode a s)) m))`,
+where `s = subStr (pairEncode m b)`. -/
+theorem modularDifference_eq (a b m : List Bool) :
+    modularDifference a b m =
+      pairSndD (divModStr (pairEncode
+        (addStr (pairEncode a (subStr (pairEncode m b)))) m)) := rfl
+
+/-- The modular-difference routine writes the `|m|`-bit numeral of
+`(⟦a⟧ + (⟦m⟧ - ⟦b⟧)) mod ⟦m⟧`:
+`modularDifference a b m = natToList m.length ((⟦a⟧ + (⟦m⟧ - ⟦b⟧)) % ⟦m⟧)`, where
+`⟦w⟧ = listToNat w`. -/
+theorem modularDifference_value (a b m : List Bool) :
+    modularDifference a b m = natToList m.length
+      ((NumberTheory.listToNat a +
+        (NumberTheory.listToNat m - NumberTheory.listToNat b)) % NumberTheory.listToNat m) := by
+  rw [modularDifference_eq, divModStr_pairEncode, pairSndD_pairEncode,
+    listToNat_addStr, listToNat_subStr]
+
+/-- Applying the modular-difference routine to three polynomial-time word functions
+is polynomial-time under the arithmetic bundle: given `H : ArithmeticFP`,
+`PolyTimeComputable a → PolyTimeComputable b → PolyTimeComputable m →`
+`PolyTimeComputable fun w => modularDifference (a w) (b w) (m w)`. -/
+theorem polyTimeComputable_modularDifference (H : ArithmeticFP)
+    {a b m : List Bool → List Bool} (ha : PolyTimeComputable a)
+    (hb : PolyTimeComputable b) (hm : PolyTimeComputable m) :
+    PolyTimeComputable fun w => modularDifference (a w) (b w) (m w) := by
+  have hs := H.sub.comp (hm.pairEncode hb)
+  have hadd := H.add.comp (ha.pairEncode hs)
+  have h := polyTimeComputable_pairSndD.comp (H.divMod.comp (hadd.pairEncode hm))
+  refine h.congr fun w => ?_
+  simp only [Function.comp_apply, modularDifference_eq]
+
+/-- On `w = ⟨u, ⟨⟨i,y⟩, raw⟩⟩`, pad or truncate `raw` to two blocks of `|u|+1` bits and output
+`collisionPost w = if s then modularDifference x' x m else modularDifference x x' m`.
+Here `x`, `x'` are read from each block's first `|u|` bits and the first selector `s` from its
+last bit, so the output is `x' - x mod m` if that selector is true and `x - x' mod m`
+otherwise, where `m` is the order word in the index `i` [PS10, Theorem 142.3]. -/
+def collisionPost (w : List Bool) : List Bool :=
+  let u := pairFstD w
+  let key := pairFstD (pairSndD w)
+  let raw := pairSndD (pairSndD w)
+  let m := pairFstD (pairSndD (pairFstD key))
+  let padded := padStr (.add (.add .var (.const 1)) (.add .var (.const 1))) u raw
+  let x := padded.take u.length
+  let x' := (padded.drop (u.length + 1)).take u.length
+  if (padded.drop u.length).headD false then modularDifference x' x m
+  else modularDifference x x' m
+
+/-- The postprocessor pads the raw output, reads two exponent prefixes and the first
+selector, and applies the corresponding modular difference:
+`collisionPost w = if s then modularDifference x' x m else modularDifference x x' m`, where
+`u = pairFstD w`, `m = pairFstD (pairSndD (pairFstD (pairFstD (pairSndD w))))`,
+`p = padStr (.add (.add .var (.const 1)) (.add .var (.const 1))) u (pairSndD (pairSndD w))`,
+`x = p.take u.length`, `x' = (p.drop (u.length + 1)).take u.length` and
+`s = (p.drop u.length).headD false`. -/
+theorem collisionPost_eq (w : List Bool) :
+    collisionPost w =
+      let u := pairFstD w
+      let key := pairFstD (pairSndD w)
+      let raw := pairSndD (pairSndD w)
+      let m := pairFstD (pairSndD (pairFstD key))
+      let padded := padStr (.add (.add .var (.const 1)) (.add .var (.const 1))) u raw
+      let x := padded.take u.length
+      let x' := (padded.drop (u.length + 1)).take u.length
+      if (padded.drop u.length).headD false then modularDifference x' x m
+      else modularDifference x x' m := rfl
+
+/-- The collision postprocessor is polynomial-time under the arithmetic bundle:
+`ArithmeticFP → PolyTimeComputable collisionPost`.
+
+**Proof sketch.** Pair projections read the parameter, raw output, and order word.
+The existing padding and polynomial-prefix cuts read the two exponents and selector.
+Both branches are compositions of subtraction, addition, and division, and the
+existing conditional constructor chooses between them. -/
+theorem polyTimeComputable_collisionPost (H : ArithmeticFP) :
+    PolyTimeComputable collisionPost := by
+  let width : PolyExpr := .add (.add .var (.const 1)) (.add .var (.const 1))
+  have hu := polyTimeComputable_pairFstD
+  have hkey := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
+  have hraw := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
+  have hm : PolyTimeComputable fun w =>
+      pairFstD (pairSndD (pairFstD (pairFstD (pairSndD w)))) := by
+    exact polyTimeComputable_pairFstD.comp
+      (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp hkey))
+  have hpad : PolyTimeComputable fun w =>
+      padStr width (pairFstD w) (pairSndD (pairSndD w)) := by
+    convert (polyTimeComputable_padStr width).comp (hu.pairEncode hraw) using 1
+    funext w
+    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
+  have hx : PolyTimeComputable fun w =>
+      (padStr width (pairFstD w) (pairSndD (pairSndD w))).take (pairFstD w).length := by
+    convert (polyTimeComputable_pairTakePoly .var).comp (hu.pairEncode hpad) using 1
+    funext w
+    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]
+  have hdrop : PolyTimeComputable fun w =>
+      (padStr width (pairFstD w) (pairSndD (pairSndD w))).drop
+        ((pairFstD w).length + 1) := by
+    convert (polyTimeComputable_pairDropPoly (.add .var (.const 1))).comp
+      (hu.pairEncode hpad) using 1
+    funext w
+    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
+      PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]
+  have hx' : PolyTimeComputable fun w =>
+      ((padStr width (pairFstD w) (pairSndD (pairSndD w))).drop
+        ((pairFstD w).length + 1)).take (pairFstD w).length := by
+    convert (polyTimeComputable_pairTakePoly .var).comp (hu.pairEncode hdrop) using 1
+    funext w
+    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]
+  have htail : PolyTimeComputable fun w =>
+      (padStr width (pairFstD w) (pairSndD (pairSndD w))).drop (pairFstD w).length := by
+    convert (polyTimeComputable_pairDropPoly .var).comp (hu.pairEncode hpad) using 1
+    funext w
+    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]
+  have hselector : PolyTimeComputable fun w =>
+      [((padStr width (pairFstD w) (pairSndD (pairSndD w))).drop
+        (pairFstD w).length).headD false] :=
+    polyTimeComputable_headD.comp htail
+  have h := polyTimeComputable_ite hselector
+    (polyTimeComputable_modularDifference H hx' hx hm)
+    (polyTimeComputable_modularDifference H hx hx' hm)
+  exact h
+
+/-- At a well-formed index, postprocessing the concatenation of two `(n + 1)`-bit
+inputs writes the `n`-bit numeral of their selected exponent difference modulo
+`dlM i`: `collisionPost (pairEncode (List.replicate n true) (pairEncode (pairEncode i y) v)) =`
+`natToList n (if x (Fin.last n) then (x₀' + (m - x₀)) % m else (x₀ + (m - x₀')) % m)`, where
+`v = List.ofFn x ++ List.ofFn x'`, `x₀ = listToNat ((List.ofFn x).take n)`, `x₀'` likewise and
+`m = dlM i`. The first input's final bit chooses `x' - x` when true and `x - x'`
+otherwise [PS10, proof of Theorem 142.3].
+
+**Proof sketch.** The concatenation already has the padding width. Cutting after
+`n + 1` bits separates the two inputs, and their first `n` bits give the exponent
+words. The input decomposition identifies the selector. Well-formedness supplies
+the order word's width, and the arithmetic reader evaluates each difference. -/
+theorem collisionPost_ofFn_append (n : ℕ) (i y : List Bool)
+    (x x' : Fin (n + 1) → Bool) (hw : WellFormedIndex n i) :
+    collisionPost (pairEncode (List.replicate n true)
+      (pairEncode (pairEncode i y) (List.ofFn x ++ List.ofFn x'))) =
+      natToList n (if x (Fin.last n) then
+        (NumberTheory.listToNat ((List.ofFn x').take n) +
+          (dlM i - NumberTheory.listToNat ((List.ofFn x).take n))) % dlM i
+        else (NumberTheory.listToNat ((List.ofFn x).take n) +
+          (dlM i - NumberTheory.listToNat ((List.ofFn x').take n))) % dlM i) := by
+  let width : PolyExpr := .add (.add .var (.const 1)) (.add .var (.const 1))
+  have hlen : (List.ofFn x ++ List.ofFn x').length =
+      width.eval (List.replicate n true).length := by
+    simp only [width, List.length_append, List.length_ofFn, List.length_replicate,
+      PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]
+  have hpad : padStr width (List.replicate n true) (List.ofFn x ++ List.ofFn x') =
+      List.ofFn x ++ List.ofFn x' := by
+    rw [padStr_of_length_le _ _ _ hlen.le, hlen, Nat.sub_self,
+      List.replicate_zero, List.append_nil]
+  dsimp only [width] at hpad
+  have hprefix : n ≤ (List.ofFn x).length := by
+    rw [List.length_ofFn]
+    omega
+  have hfirst : (List.ofFn x ++ List.ofFn x').take n = (List.ofFn x).take n :=
+    List.take_append_of_le_length hprefix
+  have hsecond : ((List.ofFn x ++ List.ofFn x').drop (n + 1)).take n =
+      (List.ofFn x').take n := by
+    rw [List.drop_left' (show (List.ofFn x).length = n + 1 by rw [List.length_ofFn])]
+  have hselector : ((List.ofFn x ++ List.ofFn x').drop n).headD false =
+      x (Fin.last n) := by
+    rw [List.drop_append_of_le_length hprefix, inputWord_drop]
+    rfl
+  have hmw : (pairFstD (pairSndD i)).length = n := by
+    obtain ⟨a, b, c, he, _, hb, _⟩ := (wellFormedIndex_iff n i).1 hw
+    rw [he, pairSndD_pairEncode, pairFstD_pairEncode]
+    exact hb
+  simp only [collisionPost_eq, pairFstD_pairEncode, pairSndD_pairEncode,
+    List.length_replicate, hpad, hfirst, hsecond, hselector]
+  simp only [modularDifference_value, hmw, ← dlM_eq i]
+  split_ifs <;> rfl
+
+/-- For any raw finder output, the postprocessor writes the selected difference
+of the two inputs obtained by the collision game's padding and splitting:
+`collisionPost (pairEncode (List.replicate n true) (pairEncode (pairEncode i y) raw)) =`
+`natToList n (if xx.1 (Fin.last n) then (x₀' + (m - x₀)) % m else (x₀ + (m - x₀')) % m)`,
+where `xx = splitBits (padFin ((n + 1) + (n + 1)) raw)`, `x₀ = listToNat ((List.ofFn xx.1).take n)`,
+`x₀'` likewise for `xx.2` and `m = dlM i`. It writes
+`x' - x mod m` when the first selector is true and `x - x' mod m` otherwise
+[PS10, proof of Theorem 142.3].
+
+**Proof sketch.** The words of the two split inputs concatenate to the padded raw
+word. Padding that word again does not change it, by the published padding/encoding
+readers and the fact that padding an encoded vector recovers the vector. Thus the
+fixed-width postprocessor contract applies to the two split inputs. -/
+theorem collisionPost_split (n : ℕ) (i y raw : List Bool) (hw : WellFormedIndex n i) :
+    let xx := splitBits (a := n + 1) (b := n + 1) (padFin ((n + 1) + (n + 1)) raw)
+    collisionPost (pairEncode (List.replicate n true)
+      (pairEncode (pairEncode i y) raw)) =
+      natToList n (if xx.1 (Fin.last n) then
+        (NumberTheory.listToNat ((List.ofFn xx.2).take n) +
+          (dlM i - NumberTheory.listToNat ((List.ofFn xx.1).take n))) % dlM i
+        else (NumberTheory.listToNat ((List.ofFn xx.1).take n) +
+          (dlM i - NumberTheory.listToNat ((List.ofFn xx.2).take n))) % dlM i) := by
+  let width : PolyExpr := .add (.add .var (.const 1)) (.add .var (.const 1))
+  let u := List.replicate n true
+  let xx := splitBits (a := n + 1) (b := n + 1) (padFin ((n + 1) + (n + 1)) raw)
+  have hsplit : List.ofFn xx.1 ++ List.ofFn xx.2 =
+      List.ofFn (padFin ((n + 1) + (n + 1)) raw) := by
+    change List.ofFn (splitBits (a := n + 1) (b := n + 1)
+      (padFin ((n + 1) + (n + 1)) raw)).1 ++
+      List.ofFn (splitBits (a := n + 1) (b := n + 1)
+        (padFin ((n + 1) + (n + 1)) raw)).2 = _
+    rw [ofFn_splitBits_fst, ofFn_splitBits_snd, List.take_append_drop]
+  have hword : List.ofFn (padFin ((n + 1) + (n + 1)) raw) = padStr width u raw := by
+    have hwidth : width.eval u.length = ((n + 1) + (n + 1)) := by
+      simp only [width, u, List.length_replicate, PolyExpr.eval_add, PolyExpr.eval_var,
+        PolyExpr.eval_const]
+    exact (congrArg (fun k : ℕ => List.ofFn (padFin k raw)) hwidth).symm.trans
+      (ofFn_padFin_eq_padStr width u raw)
+  have hidem : padStr width u (padStr width u raw) = padStr width u raw := by
+    calc
+      padStr width u (padStr width u raw) =
+          List.ofFn (padFin (width.eval u.length) (padStr width u raw)) :=
+        (ofFn_padFin_eq_padStr width u _).symm
+      _ = List.ofFn (padFin (width.eval u.length)
+          (List.ofFn (padFin (width.eval u.length) raw))) := by
+        rw [← ofFn_padFin_eq_padStr width u raw]
+      _ = List.ofFn (padFin (width.eval u.length) raw) := by rw [padFin_ofFn]
+      _ = padStr width u raw := ofFn_padFin_eq_padStr width u raw
+  have hpost : collisionPost (pairEncode u (pairEncode (pairEncode i y) raw)) =
+      collisionPost (pairEncode u
+        (pairEncode (pairEncode i y) (List.ofFn xx.1 ++ List.ofFn xx.2))) := by
+    rw [hsplit, hword]
+    dsimp only [width] at hidem
+    dsimp only [width]
+    simp only [collisionPost_eq, pairFstD_pairEncode, pairSndD_pairEncode, hidem]
+  exact hpost.trans (collisionPost_ofFn_append n i y xx.1 xx.2 hw)
+
+/-- On a raw NUPPT layout, run `A` and apply `collisionPost` to the parameter,
+the original key, and `A`'s raw output:
+`reductionRaw A z = collisionPost (pairEncode (inParam z) (pairEncode (inArg z) (A.output z)))`
+[PS10, proof of Theorem 142.3]. -/
+def reductionRaw (A : NUPPT) (z : List Bool) : List Bool :=
+  collisionPost (pairEncode (NUPPT.inParam z) (pairEncode (NUPPT.inArg z) (A.output z)))
+
+/-- The raw reduction passes its parameter and original argument together with
+the finder's raw output to the postprocessor:
+`reductionRaw A z = collisionPost (pairEncode (inParam z) (pairEncode (inArg z) (A.output z)))`,
+with `inParam = NUPPT.inParam` and `inArg = NUPPT.inArg`. -/
+theorem reductionRaw_eq (A : NUPPT) (z : List Bool) :
+    reductionRaw A z =
+      collisionPost (pairEncode (NUPPT.inParam z)
+        (pairEncode (NUPPT.inArg z) (A.output z))) := rfl
+
+/-- Running a polynomial-time finder and then postprocessing its output is
+polynomial-time under the arithmetic bundle:
+`ArithmeticFP → PolyTimeComputable (reductionRaw A)`. -/
+theorem polyTimeComputable_reductionRaw (H : ArithmeticFP) (A : NUPPT) :
+    PolyTimeComputable (reductionRaw A) := by
+  have h := (polyTimeComputable_collisionPost H).comp
+    (NUPPT.polyTimeComputable_inParam.pairEncode
+      (NUPPT.polyTimeComputable_inArg.pairEncode A.polyTimeComputable_output))
+  refine h.congr fun z => ?_
+  simp only [Function.comp_apply, reductionRaw_eq]
+
+/-- The discrete-log reduction runs the collision finder and extracts the exponent
+difference, using the same coins and advice: it realizes `reductionRaw A` in polynomial time
+with `(collisionReduction H A).coins = A.coins` and `(collisionReduction H A).advice = A.advice`
+[PS10, proof of Theorem 142.3]. -/
+noncomputable def collisionReduction (H : ArithmeticFP) (A : NUPPT) : NUPPT :=
+  NUPPT.ofPolyTime (polyTimeComputable_reductionRaw H A)
+    A.coins A.adv A.advice A.advice_length
+
+/-- The reduction is the polynomial-time realization of `reductionRaw A`, with
+the finder's coin polynomial, advice bound, and advice function:
+`collisionReduction H A = NUPPT.ofPolyTime hraw A.coins A.adv A.advice A.advice_length`,
+where `hraw = polyTimeComputable_reductionRaw H A`. -/
+theorem collisionReduction_eq (H : ArithmeticFP) (A : NUPPT) :
+    collisionReduction H A = NUPPT.ofPolyTime (polyTimeComputable_reductionRaw H A)
+      A.coins A.adv A.advice A.advice_length := rfl
+
+/-- The reduction uses the collision finder's coin polynomial:
+`(collisionReduction H A).coins = A.coins`. -/
+theorem collisionReduction_coins (H : ArithmeticFP) (A : NUPPT) :
+    (collisionReduction H A).coins = A.coins := by
+  rw [collisionReduction_eq, NUPPT.coins_ofPolyTime]
+
+/-- The reduction has the collision finder's advice bound:
+`(collisionReduction H A).adv = A.adv`. -/
+theorem collisionReduction_adv (H : ArithmeticFP) (A : NUPPT) :
+    (collisionReduction H A).adv = A.adv := by
+  rw [collisionReduction_eq, NUPPT.adv_ofPolyTime]
+
+/-- The reduction uses the collision finder's advice at every parameter:
+`(collisionReduction H A).advice = A.advice`. -/
+theorem collisionReduction_advice (H : ArithmeticFP) (A : NUPPT) :
+    (collisionReduction H A).advice = A.advice := by
+  rw [collisionReduction_eq, NUPPT.advice_ofPolyTime]
+
+/-- At parameter `n` on key `key` and coin list `r`, the reduction postprocesses
+`A.runAtL n key r` while retaining `1^n` and the original key:
+`(collisionReduction H A).runAtL n key r = collisionPost (pairEncode u (pairEncode key o))`,
+where `u = List.replicate n true` and `o = A.runAtL n key r`. -/
+theorem collisionReduction_runAtL (H : ArithmeticFP) (A : NUPPT)
+    (n : ℕ) (key r : List Bool) :
+    (collisionReduction H A).runAtL n key r =
+      collisionPost (pairEncode (List.replicate n true)
+        (pairEncode key (A.runAtL n key r))) := by
+  rw [collisionReduction_eq, NUPPT.runAtL_ofPolyTime, reductionRaw_eq]
+  simp only [NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.advInput_eq,
+    pairFstD_pairEncode, pairSndD_pairEncode, NUPPT.runAtL_eq]
+
+/-- On typed coins, the reduction postprocesses the finder's output on the same
+coin string, transported along the equality of their coin polynomials:
+`(collisionReduction H A).runAt n key r = collisionPost (pairEncode u (pairEncode key o))`,
+where `u = List.replicate n true`, `o = A.runAt n key r'` and
+`r' = NUPPT.coinsCongr (collisionReduction_coins H A) n r`. -/
+theorem collisionReduction_runAt (H : ArithmeticFP) (A : NUPPT)
+    (n : ℕ) (key : List Bool) (r : (collisionReduction H A).Coins n) :
+    (collisionReduction H A).runAt n key r =
+      collisionPost (pairEncode (List.replicate n true)
+        (pairEncode key (A.runAt n key
+          (NUPPT.coinsCongr (collisionReduction_coins H A) n r)))) := by
+  rw [NUPPT.runAt_eq, collisionReduction_runAtL, NUPPT.runAt_eq,
+    NUPPT.coinsCongr_ofFn]
+
+end TCSlib.Cryptography.Authentication.FromDiscreteLog
diff --git a/TCSlib/Cryptography/Hashing/FromDiscreteLog/Sampling.lean b/TCSlib/Cryptography/Hashing/FromDiscreteLog/Sampling.lean
new file mode 100644
index 000000000..c5e2b8245
--- /dev/null
+++ b/TCSlib/Cryptography/Hashing/FromDiscreteLog/Sampling.lean
@@ -0,0 +1,97 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Candidates.DiscreteLog
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Switching the sampled exponent to a uniform residue
+
+The bounded rejection sampler is statistically close to a uniform number below
+the group order. Identifying these numbers with the residues in `ZMod` gives the
+distribution switch used by the discrete-logarithm reduction, including arbitrary
+independent auxiliary coins.
+
+## Main definitions
+
+* `residueFinEquiv` identifies residues with bounded naturals at an equal modulus.
+
+## Main results
+
+* `sampleBelowL_uprob_le` bounds a sampled test by its ideal uniform-residue test
+  plus `(1/2)^n`.
+
+## Promotion requests
+
+`residueFinEquiv` and its readers are general finite-residue encoding helpers.
+`sampleBelowL_uprob_le` is a general reader of the candidate layer's sampler law.
+They can be promoted to the shared encoding and candidate layers respectively.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
+  2010, §5.5.2, proof of Theorem 142.3; the bounded sampler convention is that of
+  the exponentiation collection in §2.8.
+-/
+
+namespace TCSlib.Cryptography.Authentication.FromDiscreteLog
+
+open TCSlib.Cryptography TCSlib.Cryptography.Candidates
+
+/-- Residues modulo a nonzero `m` are equivalent to `Fin k` when `m = k`, using
+Mathlib's finite-residue ring equivalence and transport of the finite bound. -/
+def residueFinEquiv {m k : ℕ} [NeZero m] (h : m = k) : ZMod m ≃ Fin k :=
+  (ZMod.finEquiv m).symm.toEquiv.trans (finCongr h)
+
+/-- The residue-to-finite equivalence is Mathlib's inverse `finEquiv`, followed by
+transport along the equality of the moduli:
+`residueFinEquiv h = (ZMod.finEquiv m).symm.toEquiv.trans (finCongr h)`. -/
+theorem residueFinEquiv_eq {m k : ℕ} [NeZero m] (h : m = k) :
+    residueFinEquiv h = (ZMod.finEquiv m).symm.toEquiv.trans (finCongr h) := rfl
+
+/-- The residue-to-finite equivalence preserves the natural representative:
+`(residueFinEquiv h z).val = z.val`. -/
+theorem residueFinEquiv_val {m k : ℕ} [NeZero m] (h : m = k) (z : ZMod m) :
+    (residueFinEquiv h z).val = z.val := by
+  subst k
+  cases m with
+  | zero => exact (NeZero.ne 0 rfl).elim
+  | succ m => rfl
+
+/-- At an index well formed at parameter `n`, evaluating the `n`-bit numeral of
+a residue's natural representative returns `expF i z`:
+`expEval (pairEncode i (natToList n z.val)) = expF i z`. -/
+theorem expEval_natToList_val {n : ℕ} {i : List Bool} (hw : WellFormedIndex n i)
+    (z : ZMod (expOrd i)) :
+    expEval (Turing.pairEncode i (natToList n z.val)) = expF i z := by
+  have h := expEval_spec i z
+  simpa only [expEnc_eq, hw.dlW_eq] using h
+
+/-- For a valid group index of order below `2^n`, any test of the rejection-sampled
+exponent and independent finite auxiliary coins has probability at most its
+probability for a uniform exponent in `ZMod (expOrd i)` plus `(1/2)^n`: for `m = dlM i < 2^n`,
+`uprob (fun (s, a) => P ((sampleBelowL m (Nat.size m) n n (List.ofFn s)).getD 0) a) ≤`
+`uprob (fun (z, a) => P z.val a) + (1/2)^n` over `s : Fin (n * n) → Bool`,
+`z : ZMod (expOrd i)` and `a : ρ`
+[PS10, proof of Theorem 142.3, using the candidate-layer sampler convention].
+
+**Proof sketch.** Apply the published statistical-closeness theorem for bounded
+rejection sampling. Relabel its ideal finite seed by the value-preserving residue
+equivalence, then apply the statistical-switch bound with auxiliary coins and take
+the upper side of its absolute-value bound. -/
+theorem sampleBelowL_uprob_le {i : List Bool} (hi : ExpValid i) {n : ℕ}
+    (hmn : dlM i < 2 ^ n) {ρ : Type*} [Fintype ρ] (P : ℕ → ρ → Prop) :
+    uprob (fun z : (Fin (n * n) → Bool) × ρ =>
+      P ((sampleBelowL (dlM i) (Nat.size (dlM i)) n n (List.ofFn z.1)).getD 0) z.2) ≤
+      uprob (fun z : ZMod (expOrd i) × ρ => P z.1.val z.2) + (1 / 2 : ℝ) ^ n := by
+  have hm : 0 < dlM i := ((expValid_iff i).1 hi).2.1
+  have hs := ((statClose_sampleBelowL hm hmn).comp_equiv_right
+    (residueFinEquiv (expOrd_of_valid hi))).abs_uprob_sub_le_prod P
+  simp only [residueFinEquiv_val] at hs
+  linarith [(abs_le.1 hs).2]
+
+end TCSlib.Cryptography.Authentication.FromDiscreteLog

## ===== TCSlib/Cryptography/Hashing/FromDiscreteLog.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Hashing.CollisionResistant
import TCSlib.Cryptography.Candidates.DiscreteLog
import TCSlib.Cryptography.Hashing.FromDiscreteLog.Encoding
import TCSlib.Cryptography.Hashing.FromDiscreteLog.Algebra
import TCSlib.Cryptography.Hashing.FromDiscreteLog.Coins
import TCSlib.Cryptography.Hashing.FromDiscreteLog.Reduction
import TCSlib.Cryptography.Hashing.FromDiscreteLog.Probability
import TCSlib.Cryptography.Hashing.FromDiscreteLog.Sampling
import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A collision-resistant hash from discrete logarithms

[PS10, Protocol 142.2]: `Gen(1^n)` outputs `(p, g, y)` with `p` an `n`-bit prime, `g` a
generator of `Z_p^*` and `y` a random element of `Z_p^*`; `h_{p,g,y}(x, b) = y^b g^x mod p`.
Theorem 142.3: under the discrete-log assumption this is a collision-resistant hash that
compresses by one bit.

**The construction on the ch. 2–4 layer.** The group comes from an instance generator
`G : ExpGroupGen V` through the collection's generator `expGen` (indices `⟨p, ⟨m, g⟩⟩`, valid at
every parameter, D10). `y = g^w` for `w` drawn by the collection's domain sampler
(`expSampleRaw`, within `2^{-n}` of uniform on `Z_m`). Consequently `y` is within `2^{-n}`
of uniform on `⟨g⟩`, and, when `m = p − 1` (hypothesis `hV` of the theorem), on `Z_p^*`.
Arithmetic is through the bundle `ArithmeticFP` (D11), as for every ch. 2–4 candidate.

**Source notes.**
- The domain: the source says "an `n`-bit string `x`", but its proof needs `x < p − 1`, since
  `x` and `x + (p − 1)` collide (inventory Thm-142.3). So `D_i` is `{(x, b) : x < m}`, and
  `R_i = Z_p^*`; `|R_i| = p − 1 < 2(p − 1) = |D_i|`, the source's one-bit compression.
- The theorem's assumption is the discrete-log assumption for the full group `Z_p^*` (the
  generator `g` of `Z_p^*`), as in [PS10, Lemma 84.1], not the prime-order subgroup of
  Assumption 52.2.

## Main definitions

* `Authentication.dlHashGenFun`, `dlHashEval`: `Gen` and `h` as string functions.
* `Authentication.dlHash`: Protocol 142.2 as a `CRH`.

## Main results

* `Authentication.dlHash_compresses`: the compression part of Theorem 142.3 (proved).
* `Authentication.dlHash_crh`: Theorem 142.3 (proved).

## Contents

* `FromDiscreteLog.Encoding`: bounded domain/range cardinalities and bit-vector readers.
* `FromDiscreteLog.Algebra`: collision shape and exponent extraction in the unit group.
* `FromDiscreteLog.Coins`: coin splitting through published machine readers.
* `FromDiscreteLog.Reduction`: the efficient collision-to-discrete-log machine.
* `FromDiscreteLog.Probability`: collision acceptance as a uniform average.
* `FromDiscreteLog.Sampling`: the statistical switch to uniform exponents.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §5.5.2, Protocol 142.2 and Theorem 142.3 (book pp. 142–143).
-/

namespace TCSlib.Cryptography.Authentication

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Candidates
  TCSlib.Cryptography.NumberTheory TCSlib.Cryptography.Games

variable {V : List Bool → Prop}

/-! ### The string functions -/

/-- The group index `⟨p, ⟨m, g⟩⟩` of `Gen`, from its first `coins_G(n)` coins (the collection's
generator `expGenFun`). -/
def dlHashIdx (G : ExpGroupGen V) (z : List Bool) : List Bool :=
  pairFstD (expGenFun G (NUPPT.layout (NUPPT.inParam z) [] []
    ((NUPPT.inCoins z).take (G.gen.coins.eval (NUPPT.inParam z).length))))

/-- The hash index is the first component of `expGenFun`, run on the parameter and the first
`G.gen.coins.eval |inParam z|` input coins. -/
theorem dlHashIdx_eq (G : ExpGroupGen V) (z : List Bool) :
    dlHashIdx G z =
      pairFstD (expGenFun G (NUPPT.layout (NUPPT.inParam z) [] []
        ((NUPPT.inCoins z).take (G.gen.coins.eval (NUPPT.inParam z).length)))) := rfl

/-- On generator coins followed by sampler coins, the raw hash index is the instance
generator's output above its threshold and the fixed default index below it:
`dlHashIdx G z₀ = if G.n₀ ≤ n then G.gen.runAt n [] r else dlDefaultIndex`, where
`z₀ = NUPPT.layout (List.replicate n true) [] [] (List.ofFn r ++ s)`. -/
theorem dlHashIdx_layout (G : ExpGroupGen V) (n : ℕ) (r : G.gen.Coins n)
    (s : List Bool) :
    dlHashIdx G (NUPPT.layout (List.replicate n true) [] [] (List.ofFn r ++ s)) =
      if G.n₀ ≤ n then G.gen.runAt n [] r else dlDefaultIndex := by
  have hr : (List.ofFn r).length = G.gen.coins.eval n := by
    rw [List.length_ofFn, NUPPT.coinLen_eq]
  simp only [dlHashIdx_eq, NUPPT.inParam_layout, NUPPT.inCoins_layout,
    List.length_replicate, List.take_left' hr, expGenFun_eq]
  split_ifs with hn
  · rw [pairFstD_pairEncode, NUPPT.Uniform.runAt_eq G.gen_uniform,
      NUPPT.layout_eq, NUPPT.advInput_eq]
  · exact pairFstD_pairEncode _ _

/-- `Gen` on the raw layout: the key `⟨i, y⟩`, with `i` the group index and `y = g^w mod p` for
`w` drawn by the domain sampler from the remaining coins. -/
def dlHashGenFun (G : ExpGroupGen V) (z : List Bool) : List Bool :=
  pairEncode (dlHashIdx G z) (expEval (pairEncode (dlHashIdx G z)
    (expSampleRaw (NUPPT.layout (NUPPT.inParam z) (dlHashIdx G z) []
      ((NUPPT.inCoins z).drop (G.gen.coins.eval (NUPPT.inParam z).length))))))

/-- The raw hash generator pairs `dlHashIdx G z` with the exponentiation of a sample drawn
from the remaining input coins [PS10, Protocol 142.2]. -/
theorem dlHashGenFun_eq (G : ExpGroupGen V) (z : List Bool) :
    dlHashGenFun G z =
      pairEncode (dlHashIdx G z) (expEval (pairEncode (dlHashIdx G z)
        (expSampleRaw (NUPPT.layout (NUPPT.inParam z) (dlHashIdx G z) []
          ((NUPPT.inCoins z).drop (G.gen.coins.eval (NUPPT.inParam z).length)))))) := rfl

/-- Above the threshold, generator coins followed by sampler coins produce the group
index and the exponentiation of the rejection-sampled exponent: for `G.n₀ ≤ n`,
`dlHashGenFun G z₀ = pairEncode i (expEval (pairEncode i (natToList (dlW i) w)))`, where
`z₀ = NUPPT.layout (List.replicate n true) [] [] (List.ofFn r ++ s)`, `i = G.gen.runAt n [] r`
and `w = (sampleBelowL (dlM i) (Nat.size (dlM i)) n n s).getD 0` [PS10, Protocol 142.2]. -/
theorem dlHashGenFun_layout (G : ExpGroupGen V) (n : ℕ) (r : G.gen.Coins n)
    (s : List Bool) (hn : G.n₀ ≤ n) :
    dlHashGenFun G (NUPPT.layout (List.replicate n true) [] [] (List.ofFn r ++ s)) =
      pairEncode (G.gen.runAt n [] r)
        (expEval (pairEncode (G.gen.runAt n [] r)
          (natToList (dlW (G.gen.runAt n [] r))
            ((sampleBelowL (dlM (G.gen.runAt n [] r))
              (Nat.size (dlM (G.gen.runAt n [] r))) n n s).getD 0)))) := by
  have hr : (List.ofFn r).length = G.gen.coins.eval n := by
    rw [List.length_ofFn, NUPPT.coinLen_eq]
  simp only [dlHashGenFun_eq, dlHashIdx_layout, if_pos hn, NUPPT.inParam_layout,
    NUPPT.inCoins_layout, List.length_replicate, List.drop_left' hr, expSampleRaw_eq]
  simp only [NUPPT.inArg_layout]

/-- Above the generator threshold, every raw generated key has the form `⟨i, g^z⟩`
for an exponent in the domain of its valid group index: for `G.n₀ ≤ n`,
`∃ z : ZMod (expOrd i), dlHashGenFun G z₀ = pairEncode i (expF i z)`, where
`i = G.gen.runAt n [] r` and `z₀ = NUPPT.layout (List.replicate n true) [] [] (List.ofFn r ++ s)`
[PS10, Protocol 142.2].

**Proof sketch.** Every accepted rejection-sampler output is below `m`; its fallback zero
is also below the positive group order. Its residue therefore has exactly that value,
so the sampler's numeral is the canonical exponent encoding. -/
theorem dlHashGenFun_key (G : ExpGroupGen V) (hV : ∀ i, V i → ExpValid i)
    (n : ℕ) (r : G.gen.Coins n) (s : List Bool) (hn : G.n₀ ≤ n) :
    ∃ z : ZMod (expOrd (G.gen.runAt n [] r)),
      dlHashGenFun G (NUPPT.layout (List.replicate n true) [] [] (List.ofFn r ++ s)) =
        pairEncode (G.gen.runAt n [] r) (expF (G.gen.runAt n [] r) z) := by
  let i := G.gen.runAt n [] r
  let w := (sampleBelowL (dlM i) (Nat.size (dlM i)) n n s).getD 0
  have hi : ExpValid i := hV _ (G.valid n r hn)
  have hw : w < dlM i := by
    cases hs : sampleBelowL (dlM i) (Nat.size (dlM i)) n n s with
    | none =>
      simpa only [w, hs, Option.getD_none] using ((expValid_iff i).1 hi).2.1
    | some v =>
      simpa only [w, hs, Option.getD_some] using sampleBelowL_lt hs
  let z : ZMod (expOrd i) := (w : ℕ)
  have hz : z.val = w := by
    change ((w : ℕ) : ZMod (expOrd i)).val = w
    rw [ZMod.val_natCast, expOrd_of_valid hi, Nat.mod_eq_of_lt hw]
  refine ⟨z, ?_⟩
  rw [dlHashGenFun_layout G n r s hn, ← expEval_spec i z, expEnc_eq, hz]

/-- `g^x mod p` on `⟨1^n, ⟨⟨i, y⟩, xb⟩⟩`, with `x` the first `n` bits of `xb`. -/
def dlHashPow (z : List Bool) : List Bool :=
  expEval (pairEncode (pairFstD (pairFstD (pairSndD z)))
    ((pairSndD (pairSndD z)).take (pairFstD z).length))

/-- The exponentiation step applies `expEval` to the decoded group index and the first
`|pairFstD z|` exponent bits. -/
theorem dlHashPow_eq (z : List Bool) :
    dlHashPow z =
      expEval (pairEncode (pairFstD (pairFstD (pairSndD z)))
        ((pairSndD (pairSndD z)).take (pairFstD z).length)) := rfl

/-- At a well-formed valid index, the exponentiation part reads the first `n` input bits
and returns the `n`-bit numeral of their power of `g` modulo `p`:
`dlHashPow a = natToList n (dlG i ^ x₀ % dlP i)`, where
`a = atParam n (pairEncode (pairEncode i y) (List.ofFn x))` and
`x₀ = listToNat ((List.ofFn x).take n) < dlM i`. -/
theorem dlHashPow_atParam (n : ℕ) (i y : List Bool) (x : Fin (n + 1) → Bool)
    (hi : ExpValid i) (hw : WellFormedIndex n i)
    (hx : listToNat ((List.ofFn x).take n) < dlM i) :
    dlHashPow (atParam n (pairEncode (pairEncode i y) (List.ofFn x))) =
      natToList n (dlG i ^ listToNat ((List.ofFn x).take n) % dlP i) := by
  have he : expEnc i
      ((listToNat ((List.ofFn x).take n) : ℕ) : ZMod (expOrd i)) =
      (List.ofFn x).take n := by
    rw [expEnc_eq, hw.dlW_eq, ZMod.val_natCast, expOrd_of_valid hi,
      Nat.mod_eq_of_lt hx]
    have hcanon := natToList_length_listToNat ((List.ofFn x).take n)
    simpa only [List.length_take, List.length_ofFn,
      Nat.min_eq_left (Nat.le_succ n)] using hcanon
  have hs := expEval_spec i
    ((listToNat ((List.ofFn x).take n) : ℕ) : ZMod (expOrd i))
  rw [he, expF_eq, hw.dlW_eq, ZMod.val_natCast, expOrd_of_valid hi,
    Nat.mod_eq_of_lt hx] at hs
  simpa only [dlHashPow_eq, atParam_eq, pairFstD_pairEncode,
    pairSndD_pairEncode, List.length_replicate] using hs

/-- `y · g^x mod p` on `⟨1^n, ⟨⟨i, y⟩, xb⟩⟩`: one multiplication and one reduction modulo `p`. -/
def dlHashMul (z : List Bool) : List Bool :=
  pairSndD (divModStr (pairEncode
    (mulStr (pairEncode (dlHashPow z) (pairSndD (pairFstD (pairSndD z)))))
    (pairFstD (pairFstD (pairFstD (pairSndD z))))))

/-- The multiplication step takes the remainder of `dlHashPow z` times the decoded `y`,
divided by the decoded modulus `p`. -/
theorem dlHashMul_eq (z : List Bool) :
    dlHashMul z =
      pairSndD (divModStr (pairEncode
        (mulStr (pairEncode (dlHashPow z) (pairSndD (pairFstD (pairSndD z)))))
        (pairFstD (pairFstD (pairFstD (pairSndD z)))))) := rfl

/-- The multiplication part returns the `n`-bit numeral of the power of `g` times the
key element, reduced modulo `p`, at a valid well-formed index:
`dlHashMul a = natToList n ((dlG i ^ x₀ % dlP i * listToNat y) % dlP i)`, where
`a = atParam n (pairEncode (pairEncode i y) (List.ofFn x))` and
`x₀ = listToNat ((List.ofFn x).take n) < dlM i`. -/
theorem dlHashMul_atParam (n : ℕ) (i y : List Bool) (x : Fin (n + 1) → Bool)
    (hi : ExpValid i) (hw : WellFormedIndex n i)
    (hx : listToNat ((List.ofFn x).take n) < dlM i) :
    dlHashMul (atParam n (pairEncode (pairEncode i y) (List.ofFn x))) =
      natToList n
        ((dlG i ^ listToNat ((List.ofFn x).take n) % dlP i * listToNat y) % dlP i) := by
  have hw' : (pairFstD i).length = n := by
    obtain ⟨a, b, c, he, ha, _, _⟩ := (wellFormedIndex_iff n i).1 hw
    rw [he, pairFstD_pairEncode]
    exact ha
  have hp : dlP i < 2 ^ n := by
    simpa only [hw.dlW_eq] using dlP_lt_two_pow i
  have hpow : dlG i ^ listToNat ((List.ofFn x).take n) % dlP i < 2 ^ n :=
    (Nat.mod_lt _ ((expValid_iff i).1 hi).1.pos).trans hp
  rw [dlHashMul_eq, dlHashPow_atParam n i y x hi hw hx]
  simp only [atParam_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    divModStr_pairEncode, listToNat_mulStr, hw']
  rw [← dlP_eq i, listToNat_natToList hpow]

/-- **The hash** `h_{p,g,y}(x, b) = y^b g^x mod p` on `⟨1^n, ⟨⟨i, y⟩, xb⟩⟩`, with `x` the first
`n` bits of `xb` and `b` its bit at position `n`: one modular exponentiation, and for `b = 1` one
multiplication and one reduction modulo `p` (`dlHashMul`), each a numeral of the width of `p`. -/
def dlHashEval (z : List Bool) : List Bool :=
  if ((pairSndD (pairSndD z)).drop (pairFstD z).length).headD false then dlHashMul z
  else dlHashPow z

/-- Hash evaluation uses `dlHashMul z` when the decoded selector bit is true and `dlHashPow z`
otherwise [PS10, Protocol 142.2]. -/
theorem dlHashEval_eq (z : List Bool) :
    dlHashEval z =
      if ((pairSndD (pairSndD z)).drop (pairFstD z).length).headD false then dlHashMul z
      else dlHashPow z := rfl

/-- Hash evaluation at a valid well-formed index is the `n`-bit numeral of `g^x mod p`
for selector false, and of `(g^x mod p) y mod p` for selector true:
`dlHashEval a = natToList n (if x (Fin.last n) then (e * listToNat y) % dlP i else e)`, where
`a = atParam n (pairEncode (pairEncode i y) (List.ofFn x))`, `e = dlG i ^ x₀ % dlP i` and
`x₀ = listToNat ((List.ofFn x).take n) < dlM i` [PS10, Protocol 142.2]. -/
theorem dlHashEval_atParam (n : ℕ) (i y : List Bool) (x : Fin (n + 1) → Bool)
    (hi : ExpValid i) (hw : WellFormedIndex n i)
    (hx : listToNat ((List.ofFn x).take n) < dlM i) :
    dlHashEval (atParam n (pairEncode (pairEncode i y) (List.ofFn x))) =
      natToList n (if x (Fin.last n) then
        (dlG i ^ listToNat ((List.ofFn x).take n) % dlP i * listToNat y) % dlP i
        else dlG i ^ listToNat ((List.ofFn x).take n) % dlP i) := by
  rw [dlHashEval_eq, dlHashMul_atParam n i y x hi hw hx,
    dlHashPow_atParam n i y x hi hw hx]
  simp only [atParam_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate, FromDiscreteLog.inputWord_drop, List.headD_cons]
  split_ifs <;> rfl

/-- For the key element `g^z`, evaluation writes the residue of the unit
`(if b then g^z else 1) * g^x`, where `x` is the exponent prefix and `b` is the last bit:
`dlHashEval a = natToList n (v : ZMod (dlP i)).val`, where
`a = atParam n (pairEncode (pairEncode i (expF i z)) (List.ofFn x))`, the unit is
`v = (if x (Fin.last n) then u ^ z.val else 1) * u ^ x₀ : (ZMod (dlP i))ˣ`, `u = expUnit hi`
and `x₀ = listToNat ((List.ofFn x).take n) < dlM i` [PS10, Protocol 142.2]. -/
theorem dlHashEval_expF (n : ℕ) (i : List Bool) (z : ZMod (expOrd i))
    (x : Fin (n + 1) → Bool) (hi : ExpValid i) (hw : WellFormedIndex n i)
    (hx : listToNat ((List.ofFn x).take n) < dlM i) :
    dlHashEval (atParam n (pairEncode (pairEncode i (expF i z)) (List.ofFn x))) =
      natToList n
        (((if x (Fin.last n) then expUnit hi ^ z.val else 1) *
          expUnit hi ^ listToNat ((List.ofFn x).take n) : (ZMod (dlP i))ˣ) :
            ZMod (dlP i)).val := by
  have hp : dlP i < 2 ^ n := by
    simpa only [hw.dlW_eq] using dlP_lt_two_pow i
  have hz : dlG i ^ z.val % dlP i < 2 ^ n :=
    (Nat.mod_lt _ ((expValid_iff i).1 hi).1.pos).trans hp
  rw [dlHashEval_atParam n i (expF i z) x hi hw hx, expF_eq, hw.dlW_eq,
    listToNat_natToList hz]
  cases hb : x (Fin.last n)
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul,
      FromDiscreteLog.expUnit_pow_val]
  · simp only [↓reduceIte, Units.val_mul, ZMod.val_mul,
      FromDiscreteLog.expUnit_pow_val]
    rw [Nat.mul_comm]

/-- Equal evaluations on two distinct domain inputs force different selectors and reveal
the challenge exponent as the corresponding difference modulo `m`: if `x ≠ x'`, `x₀ < m`,
`x₀' < m` and `dlHashEval a = dlHashEval a'`, then `x (Fin.last n) ≠ x' (Fin.last n)` and
`z.val = if x (Fin.last n) then (x₀' + (m - x₀)) % m else (x₀ + (m - x₀')) % m`, where
`a = atParam n (pairEncode (pairEncode i (expF i z)) (List.ofFn x))` (`a'` likewise for `x'`),
`x₀ = listToNat ((List.ofFn x).take n)`, `x₀'` likewise and `m = dlM i`
[PS10, proof of Theorem 142.3].

**Proof sketch.** Evaluation writes the residue of the associated unit. Equal fixed-width
numerals therefore give equal units. The unit-group collision lemma rules out equal
selectors and extracts the unique exponent residue. -/
theorem dlHashEval_collision (n : ℕ) (i : List Bool) (z : ZMod (expOrd i))
    (x x' : Fin (n + 1) → Bool) (hi : ExpValid i) (hw : WellFormedIndex n i)
    (hx : listToNat ((List.ofFn x).take n) < dlM i)
    (hx' : listToNat ((List.ofFn x').take n) < dlM i) (hne : x ≠ x')
    (hc : dlHashEval (atParam n (pairEncode (pairEncode i (expF i z)) (List.ofFn x))) =
      dlHashEval (atParam n (pairEncode (pairEncode i (expF i z)) (List.ofFn x')))) :
    x (Fin.last n) ≠ x' (Fin.last n) ∧ z.val =
      if x (Fin.last n) then
        (listToNat ((List.ofFn x').take n) +
          (dlM i - listToNat ((List.ofFn x).take n))) % dlM i
      else (listToNat ((List.ofFn x).take n) +
          (dlM i - listToNat ((List.ofFn x').take n))) % dlM i := by
  haveI : NeZero (dlP i) := ⟨((expValid_iff i).1 hi).1.ne_zero⟩
  have hp : dlP i < 2 ^ n := by
    simpa only [hw.dlW_eq] using dlP_lt_two_pow i
  have hbound (u : (ZMod (dlP i))ˣ) : (u : ZMod (dlP i)).val < 2 ^ n :=
    (ZMod.val_lt _).trans hp
  rw [dlHashEval_expF n i z x hi hw hx, dlHashEval_expF n i z x' hi hw hx'] at hc
  have hv := natToList_injOn (hbound _) (hbound _) hc
  have hu := Units.ext (ZMod.val_injective (dlP i) hv)
  have hd : (listToNat ((List.ofFn x).take n), x (Fin.last n)) ≠
      (listToNat ((List.ofFn x').take n), x' (Fin.last n)) := by
    intro he
    exact hne (FromDiscreteLog.inputWord_num_ext
      (congrArg Prod.fst he) (congrArg Prod.snd he))
  exact FromDiscreteLog.unitCollision_extract hi hx hx' z hd hu

/-- Evaluation on a domain input at a valid well-formed key has exactly `n` bits and
reads as a positive residue below `p`:
`(dlHashEval a).length = n ∧ 0 < listToNat (dlHashEval a) ∧ listToNat (dlHashEval a) < dlP i`,
where `a = atParam n (pairEncode (pairEncode i (expF i z)) (List.ofFn x))` and
`listToNat ((List.ofFn x).take n) < dlM i` [PS10, compression in Theorem 142.3].

**Proof sketch.** The evaluation is the numeral of a unit's residue. A unit has positive
residue below `p`, and the well-formed width is large enough to encode it exactly. -/
theorem dlHashEval_range (n : ℕ) (i : List Bool) (z : ZMod (expOrd i))
    (x : Fin (n + 1) → Bool) (hi : ExpValid i) (hw : WellFormedIndex n i)
    (hx : listToNat ((List.ofFn x).take n) < dlM i) :
    (dlHashEval (atParam n (pairEncode (pairEncode i (expF i z)) (List.ofFn x)))).length = n ∧
      0 < listToNat (dlHashEval (atParam n
        (pairEncode (pairEncode i (expF i z)) (List.ofFn x)))) ∧
      listToNat (dlHashEval (atParam n
        (pairEncode (pairEncode i (expF i z)) (List.ofFn x)))) < dlP i := by
  have hp2 : 2 ≤ dlP i := ((expValid_iff i).1 hi).1.two_le
  haveI : Fact (1 < dlP i) := ⟨by omega⟩
  haveI : NeZero (dlP i) := ⟨by omega⟩
  let u : (ZMod (dlP i))ˣ :=
    (if x (Fin.last n) then expUnit hi ^ z.val else 1) *
      expUnit hi ^ listToNat ((List.ofFn x).take n)
  have hpw : dlP i < 2 ^ n := by
    simpa only [hw.dlW_eq] using dlP_lt_two_pow i
  have hval : (u : ZMod (dlP i)).val < 2 ^ n := (ZMod.val_lt _).trans hpw
  have hu := units_val_mem u
  rw [dlHashEval_expF n i z x hi hw hx]
  change (natToList n (u : ZMod (dlP i)).val).length = n ∧
    0 < listToNat (natToList n (u : ZMod (dlP i)).val) ∧
      listToNat (natToList n (u : ZMod (dlP i)).val) < dlP i
  rw [length_natToList, listToNat_natToList hval]
  exact ⟨rfl, lt_of_lt_of_le Nat.zero_lt_one hu.1, ZMod.val_lt _⟩

/-! ### Efficiency -/

/-- The group index of `Gen` is polynomial-time. -/
theorem polyTimeComputable_dlHashIdx (G : ExpGroupGen V) : PolyTimeComputable (dlHashIdx G) := by
  have ht : PolyTimeComputable fun z =>
      (NUPPT.inCoins z).take (G.gen.coins.eval (NUPPT.inParam z).length) := by
    convert (polyTimeComputable_pairTakePoly G.gen.coins).comp
      (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins) using 1
    funext z
    simp [Function.comp_apply]
  exact polyTimeComputable_pairFstD.comp ((expGenFun_poly G).comp
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam
      (polyTimeComputable_const []) (polyTimeComputable_const []) ht))

/-- `Gen` is polynomial-time given the arithmetic bundle. -/
theorem polyTimeComputable_dlHashGenFun (H : ArithmeticFP) (G : ExpGroupGen V) :
    PolyTimeComputable (dlHashGenFun G) := by
  have hi := polyTimeComputable_dlHashIdx G
  have hd := (polyTimeComputable_pairDropPoly G.gen.coins).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins)
  have hw := (polyTimeComputable_expSampleRaw H).comp (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam hi (polyTimeComputable_const []) hd)
  have h := hi.pairEncode ((polyTimeComputable_expEval H).comp (hi.pairEncode hw))
  refine (congrArg PolyTimeComputable (?_ : dlHashGenFun G = _)).mpr h
  funext z
  simp only [dlHashGenFun, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- The exponentiation step is polynomial-time given the arithmetic bundle. -/
theorem polyTimeComputable_dlHashPow (H : ArithmeticFP) : PolyTimeComputable dlHashPow := by
  have ht : PolyTimeComputable fun z => (pairSndD (pairSndD z)).take (pairFstD z).length := by
    convert (polyTimeComputable_pairTakePoly .var).comp
      (polyTimeComputable_pairFstD.pairEncode
        (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)) using 1
    funext z
    simp [Function.comp_apply]
  have h := (polyTimeComputable_expEval H).comp (((polyTimeComputable_pairFstD.comp
    polyTimeComputable_pairFstD).comp polyTimeComputable_pairSndD).pairEncode ht)
  refine (congrArg PolyTimeComputable (?_ : dlHashPow = _)).mpr h
  funext z
  simp only [dlHashPow, Function.comp_apply]

/-- The multiplication step is polynomial-time given the arithmetic bundle. -/
theorem polyTimeComputable_dlHashMul (H : ArithmeticFP) : PolyTimeComputable dlHashMul := by
  have hp := polyTimeComputable_dlHashPow H
  have hy := (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD).comp
    polyTimeComputable_pairSndD
  have hP := ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).comp
    polyTimeComputable_pairFstD).comp polyTimeComputable_pairSndD
  have h := polyTimeComputable_pairSndD.comp
    (H.divMod.comp ((H.mul.comp (hp.pairEncode hy)).pairEncode hP))
  refine (congrArg PolyTimeComputable (?_ : dlHashMul = _)).mpr h
  funext z
  simp only [dlHashMul, Function.comp_apply]

/-- The hash is polynomial-time given the arithmetic bundle. -/
theorem polyTimeComputable_dlHashEval (H : ArithmeticFP) : PolyTimeComputable dlHashEval := by
  have hq := polyTimeComputable_pairFstD.pairEncode
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hb₀ := polyTimeComputable_headD.comp ((polyTimeComputable_pairDropPoly .var).comp hq)
  have hb : PolyTimeComputable fun z =>
      [((pairSndD (pairSndD z)).drop (pairFstD z).length).headD false] := by
    refine (congrArg PolyTimeComputable (?_ : (fun z =>
      [((pairSndD (pairSndD z)).drop (pairFstD z).length).headD false]) = _)).mpr hb₀
    funext z
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]
  exact polyTimeComputable_ite
    (p := fun z => ((pairSndD (pairSndD z)).drop (pairFstD z).length).headD false)
    (f := dlHashMul) (g := dlHashPow) hb (polyTimeComputable_dlHashMul H)
    (polyTimeComputable_dlHashPow H)

/-! ### The hash family -/

/-- **Protocol 142.2** [PS10] as a `CRH`, for the instance generator `G`: keys `⟨i, y⟩`,
domain `D_i = {(x, b) : x < m}` of `(n + 1)`-bit strings (`x` the first `n` bits, read as a
numeral), range `R_i = {y : 0 < y < p}` of `n`-bit numerals, and `h(x, b) = y^b g^x mod p`.
`Gen` uses the coins of `G` and `n²` sampler coins. -/
noncomputable def dlHash (H : ArithmeticFP) (G : ExpGroupGen V) : CRH where
  domLen := .add .var (.const 1)
  rangeLen := .var
  gen := NUPPT.ofPolyTimeUniform (polyTimeComputable_dlHashGenFun H G)
    (.add G.gen.coins (.mul .var .var))
  eval := dlHashEval
  inDom n k x := decide (listToNat ((List.ofFn x).take n) < dlM (pairFstD k))
  inRange _ k y := decide (0 < listToNat (List.ofFn y) ∧ listToNat (List.ofFn y) < dlP (pairFstD k))
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  eval_poly := polyTimeComputable_dlHashEval H

attribute [simps (config := { isSimp := false }) domLen rangeLen gen eval inDom inRange] dlHash

/-- The hash generator uses the instance generator's coin polynomial plus `n²` sampler
coins: `(dlHash H G).gen.coins = .add G.gen.coins (.mul .var .var)` [PS10, Protocol 142.2]. -/
theorem dlHash_gen_coins (H : ArithmeticFP) (G : ExpGroupGen V) :
    (dlHash H G).gen.coins = .add G.gen.coins (.mul .var .var) := by
  rw [dlHash_gen, NUPPT.coins_ofPolyTimeUniform]

/-- The hash generator's coins are the instance generator's coins and an independent
`n²`-bit sampler tape: `(dlHash H G).gen.Coins n ≃ G.gen.Coins n × (Fin (n * n) → Bool)`
[PS10, Protocol 142.2]. -/
noncomputable def dlHash_coinsEquiv (H : ArithmeticFP) (G : ExpGroupGen V) (n : ℕ) :
    (dlHash H G).gen.Coins n ≃ G.gen.Coins n × (Fin (n * n) → Bool) :=
  (FromDiscreteLog.sumCoinsEquiv (dlHash H G).gen (dlHash_gen_coins H G) n).trans
    (Equiv.prodCongr (NUPPT.coinsEquivPoly (A := G.gen) rfl n).symm
      (Equiv.arrowCongr (finCongr (by rw [PolyExpr.eval_mul, PolyExpr.eval_var]))
        (Equiv.refl Bool)))

/-- The hash coin equivalence splits the sum polynomial, identifies its first component
with the generator's coins, and reads the second component as `n²` bits:
`dlHash_coinsEquiv H G n = (sumCoinsEquiv (dlHash H G).gen _ n).trans (Equiv.prodCongr e₁ e₂)`,
where `e₁ = (NUPPT.coinsEquivPoly (A := G.gen) rfl n).symm` and
`e₂ = Equiv.arrowCongr (finCongr _) (Equiv.refl Bool)` transports
`(.mul .var .var).eval n = n * n`. -/
theorem dlHash_coinsEquiv_eq (H : ArithmeticFP) (G : ExpGroupGen V) (n : ℕ) :
    dlHash_coinsEquiv H G n =
      (FromDiscreteLog.sumCoinsEquiv (dlHash H G).gen (dlHash_gen_coins H G) n).trans
        (Equiv.prodCongr (NUPPT.coinsEquivPoly (A := G.gen) rfl n).symm
          (Equiv.arrowCongr (finCongr (by rw [PolyExpr.eval_mul, PolyExpr.eval_var]))
            (Equiv.refl Bool))) := rfl

/-- Combining a generator tape and a sampler tape concatenates their encoded words:
`List.ofFn ((dlHash_coinsEquiv H G n).symm (r, s)) = List.ofFn r ++ List.ofFn s`. -/
theorem dlHash_coinsEquiv_symm_ofFn (H : ArithmeticFP) (G : ExpGroupGen V) (n : ℕ)
    (r : G.gen.Coins n) (s : Fin (n * n) → Bool) :
    List.ofFn ((dlHash_coinsEquiv H G n).symm (r, s)) = List.ofFn r ++ List.ofFn s := by
  rw [dlHash_coinsEquiv_eq, Equiv.symm_trans_apply, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Equiv.symm_symm, FromDiscreteLog.sumCoinsEquiv_symm_ofFn,
    Prod.map_fst, Prod.map_snd, NUPPT.coinsEquivPoly_ofFn,
    Equiv.arrowCongr_symm, finCongr_symm, Equiv.refl_symm,
    ofFn_arrowCongr_finCongr]

/-- On recombined generator and sampler coins, the hash generator runs its raw function
on their concatenation:
`(dlHash H G).gen.runAt n [] ((dlHash_coinsEquiv H G n).symm (r, s)) = dlHashGenFun G z₀`,
where `z₀ = NUPPT.layout (List.replicate n true) [] [] (List.ofFn r ++ List.ofFn s)`
[PS10, Protocol 142.2]. -/
theorem dlHash_gen_runAt (H : ArithmeticFP) (G : ExpGroupGen V) (n : ℕ)
    (r : G.gen.Coins n) (s : Fin (n * n) → Bool) :
    (dlHash H G).gen.runAt n [] ((dlHash_coinsEquiv H G n).symm (r, s)) =
      dlHashGenFun G (NUPPT.layout (List.replicate n true) [] []
        (List.ofFn r ++ List.ofFn s)) := by
  rw [NUPPT.runAt_eq, dlHash_coinsEquiv_symm_ofFn, dlHash_gen,
    NUPPT.runAtL_ofPolyTimeUniform, NUPPT.advInput_eq, NUPPT.layout_eq]

/-- The discrete-log hash compresses at every parameter above the instance generator's
threshold when its groups are the full unit groups:
`(∀ i, V i → ExpValid i ∧ dlM i = dlP i - 1) → (dlHash H G).Compresses` [PS10, Theorem 142.3].

**Proof sketch.** Split a generated key's coins into the instance and sampler tapes. Its
index is valid and well formed, and its key element is a power of the generator. Evaluation
therefore lands in the positive residues. There are `2m` domain inputs and `p - 1 = m`
range values, with `m > 0`. -/
theorem dlHash_compresses (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i ∧ dlM i = dlP i - 1) : (dlHash H G).Compresses := by
  rw [CRH.compresses_iff]
  refine ⟨G.n₀, ?_⟩
  intro n hn rg
  obtain ⟨⟨r, s⟩, rfl⟩ := (dlHash_coinsEquiv H G n).symm.surjective rg
  rw [dlHash_gen_runAt]
  obtain ⟨z, hkey⟩ := dlHashGenFun_key G (fun i hi => (hV i hi).1)
    n r (List.ofFn s) hn
  rw [hkey]
  have hi := (hV _ (G.valid n r hn)).1
  have hmfull := (hV _ (G.valid n r hn)).2
  have hw := G.wellFormed n r hn
  have hp : dlP (G.gen.runAt n [] r) < 2 ^ n := by
    simpa only [hw.dlW_eq] using dlP_lt_two_pow (G.gen.runAt n [] r)
  have hm : dlM (G.gen.runAt n [] r) < 2 ^ n :=
    ((expValid_iff _).1 hi).2.2.1.trans hp
  simp only [dlHash_inDom, dlHash_inRange, CRH.hash_eq, dlHash_eval,
    pairFstD_pairEncode, decide_eq_true_eq]
  simp only [dlHash_domLen, dlHash_rangeLen, PolyExpr.eval_add, PolyExpr.eval_var,
    PolyExpr.eval_const]
  constructor
  · intro x hx
    have hr := dlHashEval_range n _ z x hi hw hx
    rw [ofFn_padFin_of_length hr.1]
    exact hr.2
  · rw [FromDiscreteLog.card_boundedInput n _ hm.le,
      FromDiscreteLog.card_boundedRange n _ ((expValid_iff _).1 hi).1.pos hp.le,
      ← hmfull]
    have hpos := ((expValid_iff _).1 hi).2.1
    omega

/-- The collision test for a raw finder output on key `⟨i, y⟩`: its two padded inputs
are distinct, have exponent prefixes below `m`, and have equal padded hash values,
`dlHashCollision n i y raw = (x₀ < dlM i ∧ x₀' < dlM i ∧ xx.1 ≠ xx.2 ∧ h xx.1 = h xx.2)`, where
`xx = splitBits (padFin ((n + 1) + (n + 1)) raw)` (blocks of `n + 1` bits),
`x₀ = listToNat ((List.ofFn xx.1).take n)`, `x₀'` likewise for `xx.2`, and
`h v = padFin n (dlHashEval (atParam n (pairEncode (pairEncode i y) (List.ofFn v))))`
[PS10, Definition 140.1]. -/
def dlHashCollision (n : ℕ) (i y raw : List Bool) : Prop :=
  let xx := splitBits (a := n + 1) (b := n + 1) (padFin ((n + 1) + (n + 1)) raw)
  listToNat ((List.ofFn xx.1).take n) < dlM i ∧
    listToNat ((List.ofFn xx.2).take n) < dlM i ∧ xx.1 ≠ xx.2 ∧
    padFin n (dlHashEval (atParam n (pairEncode (pairEncode i y) (List.ofFn xx.1)))) =
      padFin n (dlHashEval (atParam n (pairEncode (pairEncode i y) (List.ofFn xx.2))))

/-- The raw collision predicate is exactly the domain, distinctness, and equal-hash test
on its two padded output halves:
`dlHashCollision n i y raw ↔ x₀ < dlM i ∧ x₀' < dlM i ∧ xx.1 ≠ xx.2 ∧ h xx.1 = h xx.2`,
with `xx`, `x₀`, `x₀'` and `h` as in `dlHashCollision`. -/
theorem dlHashCollision_iff (n : ℕ) (i y raw : List Bool) :
    dlHashCollision n i y raw ↔
      let xx := splitBits (a := n + 1) (b := n + 1) (padFin ((n + 1) + (n + 1)) raw)
      listToNat ((List.ofFn xx.1).take n) < dlM i ∧
        listToNat ((List.ofFn xx.2).take n) < dlM i ∧ xx.1 ≠ xx.2 ∧
        padFin n (dlHashEval (atParam n (pairEncode (pairEncode i y) (List.ofFn xx.1)))) =
          padFin n (dlHashEval (atParam n (pairEncode (pairEncode i y) (List.ofFn xx.2)))) :=
  Iff.rfl

/-- Above the generator threshold, collision acceptance is the average over instance
coins of the joint probability over sampler and finder coins of the raw collision test:
for `G.n₀ ≤ n`, `accept ((dlHash H G).collisionGame A n) = uexp (fun r => uprob (fun rs =>`
`dlHashCollision n i y (A.runAt n (pairEncode i y) rs.2)))` over `r : G.gen.Coins n` and
`rs : (Fin (n * n) → Bool) × A.Coins n`, where `i = G.gen.runAt n [] r`,
`y = expEval (pairEncode i (natToList n w))` and
`w = (sampleBelowL (dlM i) (Nat.size (dlM i)) n n (List.ofFn rs.1)).getD 0`
[PS10, key distribution in Theorem 142.3].

**Proof sketch.** Reindex the generator's uniform coins by their two independent tapes,
read its activation, and expose the collision game's fields through their public readers.
Fubini combines the sampler and finder tapes into a product probability. -/
theorem dlHash_collision_accept_eq (H : ArithmeticFP) (G : ExpGroupGen V) (A : NUPPT)
    (n : ℕ) (hn : G.n₀ ≤ n) :
    accept ((dlHash H G).collisionGame A n) =
      uexp (fun r : G.gen.Coins n =>
        uprob (fun rs : (Fin (n * n) → Bool) × A.Coins n =>
          let i := G.gen.runAt n [] r
          let y := expEval (pairEncode i (natToList n
            ((sampleBelowL (dlM i) (Nat.size (dlM i)) n n (List.ofFn rs.1)).getD 0)))
          dlHashCollision n i y (A.runAt n (pairEncode i y) rs.2))) := by
  rw [FromDiscreteLog.collision_accept_eq,
    ← HardcoreBit.uexp_comp_equiv (dlHash_coinsEquiv H G n).symm,
    HardcoreBit.uexp_prod]
  congr 1
  funext r
  rw [uprob_prod]
  congr 1
  funext s
  apply OneWay.uprob_congr
  intro ra
  rw [dlHash_gen_runAt, dlHashGenFun_layout G n r (List.ofFn s) hn]
  have hw := G.wellFormed n r hn
  simp only [dlHashCollision_iff, dlHash_inDom, CRH.hash_eq, dlHash_eval,
    pairFstD_pairEncode, decide_eq_true_eq, hw.dlW_eq]
  simp only [dlHash_domLen, dlHash_rangeLen, PolyExpr.eval_add, PolyExpr.eval_var,
    PolyExpr.eval_const]

/-- Whenever the finder produces a collision on a valid key `⟨i, g^z⟩`, the reduction's
answer decodes to the challenge exponent: if the finder's output
`A.runAt n k (NUPPT.coinsCongr (collisionReduction_coins H A) n r)` passes the
`dlHashCollision n i (expF i z)` test (stated unfolded), then
`∃ out : Fin n → Bool, decodeFin n (B.runAt n k r) = some out ∧ bitsToNat out = z.val`, where
`k = pairEncode i (expF i z)` and `B = collisionReduction H A`
[PS10, reduction in Theorem 142.3].

**Proof sketch.** Remove the hash-output padding using its proved exact length. The
collision-extraction lemma identifies the postprocessor's modular difference with `z`.
The reduction therefore writes the canonical `n`-bit numeral of `z`, which decodes exactly. -/
theorem dlHash_reduction_success (H : ArithmeticFP) (A : NUPPT) (n : ℕ)
    (i : List Bool) (z : ZMod (expOrd i)) (hi : ExpValid i) (hw : WellFormedIndex n i)
    (r : (FromDiscreteLog.collisionReduction H A).Coins n)
    (hc :
      let xx := splitBits (a := n + 1) (b := n + 1)
        (padFin ((n + 1) + (n + 1)) (A.runAt n (pairEncode i (expF i z))
          (NUPPT.coinsCongr (FromDiscreteLog.collisionReduction_coins H A) n r)))
      listToNat ((List.ofFn xx.1).take n) < dlM i ∧
        listToNat ((List.ofFn xx.2).take n) < dlM i ∧ xx.1 ≠ xx.2 ∧
        padFin n (dlHashEval (atParam n (pairEncode (pairEncode i (expF i z))
          (List.ofFn xx.1)))) =
        padFin n (dlHashEval (atParam n (pairEncode (pairEncode i (expF i z))
          (List.ofFn xx.2))))) :
    ∃ out : Fin n → Bool,
      decodeFin n ((FromDiscreteLog.collisionReduction H A).runAt n
        (pairEncode i (expF i z)) r) = some out ∧ bitsToNat out = z.val := by
  let key := pairEncode i (expF i z)
  let ra := NUPPT.coinsCongr (FromDiscreteLog.collisionReduction_coins H A) n r
  let xx := splitBits (a := n + 1) (b := n + 1)
    (padFin ((n + 1) + (n + 1)) (A.runAt n key ra))
  change listToNat ((List.ofFn xx.1).take n) < dlM i ∧
    listToNat ((List.ofFn xx.2).take n) < dlM i ∧ xx.1 ≠ xx.2 ∧
      padFin n (dlHashEval (atParam n (pairEncode key (List.ofFn xx.1)))) =
        padFin n (dlHashEval (atParam n (pairEncode key (List.ofFn xx.2)))) at hc
  obtain ⟨hx, hx', hne, hhash⟩ := hc
  have heq : dlHashEval (atParam n (pairEncode key (List.ofFn xx.1))) =
      dlHashEval (atParam n (pairEncode key (List.ofFn xx.2))) := by
    have hh := congrArg List.ofFn hhash
    change List.ofFn (padFin n (dlHashEval (atParam n (pairEncode key (List.ofFn xx.1))))) =
      List.ofFn (padFin n (dlHashEval (atParam n (pairEncode key (List.ofFn xx.2))))) at hh
    rw [ofFn_padFin_of_length (dlHashEval_range n i z xx.1 hi hw hx).1,
      ofFn_padFin_of_length (dlHashEval_range n i z xx.2 hi hw hx').1] at hh
    exact hh
  have hz := (dlHashEval_collision n i z xx.1 xx.2 hi hw hx hx' hne heq).2
  have hb := FromDiscreteLog.collisionReduction_runAt H A n key r
  rw [FromDiscreteLog.collisionPost_split n i (expF i z) _ hw] at hb
  have hanswer : (FromDiscreteLog.collisionReduction H A).runAt n key r =
      natToList n z.val := hb.trans (congrArg (natToList n) hz.symm)
  refine ⟨natToBits n z.val, ?_, ?_⟩
  · rw [hanswer, natToList_eq, decodeFin_ofFn]
  · exact bitsToNat_natToBits (by
      simpa only [hw.dlW_eq] using val_lt_two_pow_dlW i z)

/-- For a fixed valid well-formed index and a uniform challenge exponent, the finder's
collision probability is bounded by the reduction's discrete-log success probability:
`uprob CA ≤ uprob DB`, where `CA (z, r) = dlHashCollision n i (expF i z) (A.runAt n k r)` on
`ZMod (expOrd i) × A.Coins n`, and on `ZMod (expOrd i) × B.Coins n`,
`DB (z, r) = ∃ out : Fin n → Bool, decodeFin n (B.runAt n k r) = some out ∧ bitsToNat out = z.val`,
with `k = pairEncode i (expF i z)` and `B = collisionReduction H A`
[PS10, reduction in Theorem 142.3].

**Proof sketch.** Reindex the reduction's coins by the finder's equal-length coin tape.
Every collision in the reindexed experiment implies successful decoding of the challenge
exponent by the pointwise reduction theorem. Monotonicity of uniform probability concludes. -/
theorem dlHash_ideal_collision_le (H : ArithmeticFP) (A : NUPPT) (n : ℕ)
    (i : List Bool) (hi : ExpValid i) (hw : WellFormedIndex n i) :
    uprob (fun zr : ZMod (expOrd i) × A.Coins n =>
      dlHashCollision n i (expF i zr.1) (A.runAt n (pairEncode i (expF i zr.1)) zr.2)) ≤
      uprob (fun zr : ZMod (expOrd i) × (FromDiscreteLog.collisionReduction H A).Coins n =>
        ∃ out : Fin n → Bool,
          decodeFin n ((FromDiscreteLog.collisionReduction H A).runAt n
            (pairEncode i (expF i zr.1)) zr.2) = some out ∧ bitsToNat out = zr.1.val) := by
  rw [← uprob_comp_equiv (Equiv.prodCongr (Equiv.refl (ZMod (expOrd i)))
    (NUPPT.coinsCongr (FromDiscreteLog.collisionReduction_coins H A) n))]
  apply uprob_mono
  intro zr hc
  have hh : dlHashCollision n i (expF i zr.1)
      (A.runAt n (pairEncode i (expF i zr.1))
        (NUPPT.coinsCongr (FromDiscreteLog.collisionReduction_coins H A) n zr.2)) := by
    simpa only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply] using hc
  exact dlHash_reduction_success H A n i zr.1 hi hw zr.2
    ((dlHashCollision_iff n i (expF i zr.1) _).1 hh)

/-- Above the generator threshold, collision acceptance is at most the concrete
reduction's discrete-log success probability plus `(1/2)^n`: for `G.n₀ ≤ n`,
`accept ((dlHash H G).collisionGame A n) ≤ G.dlProb (collisionReduction H A) n + (1/2)^n`
[PS10, probability bound in Theorem 142.3].

**Proof sketch.** Read the honest key distribution as the average over instance coins
and independent sampler/finder tapes. The bounded sampler is within `(1/2)^n` of a
uniform exponent. For the uniform experiment every collision makes the reduction
succeed. Average the pointwise bounds and identify the discrete-log experiment. -/
theorem dlHash_collision_bound (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (A : NUPPT) (n : ℕ) (hn : G.n₀ ≤ n) :
    accept ((dlHash H G).collisionGame A n) ≤
      G.dlProb (FromDiscreteLog.collisionReduction H A) n + (1 / 2 : ℝ) ^ n := by
  rw [dlHash_collision_accept_eq H G A n hn, ExpGroupGen.dlProb_eq]
  calc
    _ ≤ uexp (fun r : G.gen.Coins n =>
        uprob (fun zr : ZMod (expOrd (G.gen.runAt n [] r)) × A.Coins n =>
          dlHashCollision n (G.gen.runAt n [] r) (expF _ zr.1)
            (A.runAt n (pairEncode (G.gen.runAt n [] r) (expF _ zr.1)) zr.2)) +
          (1 / 2 : ℝ) ^ n) := by
      apply HardcoreBit.uexp_mono
      intro r
      have hi := hV _ (G.valid n r hn)
      have hw := G.wellFormed n r hn
      have hp : dlP (G.gen.runAt n [] r) < 2 ^ n := by
        simpa only [hw.dlW_eq] using dlP_lt_two_pow (G.gen.runAt n [] r)
      have hm : dlM (G.gen.runAt n [] r) < 2 ^ n :=
        ((expValid_iff _).1 hi).2.2.1.trans hp
      have hs := FromDiscreteLog.sampleBelowL_uprob_le hi hm
        (ρ := A.Coins n) (fun v ra =>
          let i := G.gen.runAt n [] r
          let y := expEval (pairEncode i (natToList n v))
          dlHashCollision n i y (A.runAt n (pairEncode i y) ra))
      simpa only [FromDiscreteLog.expEval_natToList_val hw] using hs
    _ = uexp (fun r : G.gen.Coins n =>
        uprob (fun zr : ZMod (expOrd (G.gen.runAt n [] r)) × A.Coins n =>
          dlHashCollision n (G.gen.runAt n [] r) (expF _ zr.1)
            (A.runAt n (pairEncode (G.gen.runAt n [] r) (expF _ zr.1)) zr.2))) +
          (1 / 2 : ℝ) ^ n := by
      rw [HardcoreBit.uexp_add, HardcoreBit.uexp_const]
    _ ≤ _ := add_le_add_right (HardcoreBit.uexp_mono fun r =>
      dlHash_ideal_collision_le H A n _ (hV _ (G.valid n r hn))
        (G.wellFormed n r hn)) _

/-- **Theorem 142.3: Protocol 142.2 is a collision-resistant hash compressing by one bit**
[PS10, Theorem 142.3], under the discrete-log assumption for an instance generator of the full
groups `Z_p^*` (`m = p − 1`).

**Proof sketch** (the source's, with its gap closed).
1. *Compression.* From `G.n₀` on, the index is valid with `n`-bit numerals, so
   `|D_i| = 2m = 2(p − 1)` and `|R_i| = p − 1`, and `y^b g^x mod p` is a unit (`g` and `y` are
   coprime to `p`): `h` maps `D_i` into `R_i`.
2. *A collision has `b ≠ b'`.* If `b = b'`, then `g^x = g^{x'}` with `x, x' < m`, so `x = x'`
   (`expF_injective`), and the two inputs are equal.
3. *The reduction.* `B(1^n, ⟨i, g^z⟩)` runs `A` on the key `⟨i, g^z⟩` and, from a collision
   `(x, 0), (x', 1)`, outputs `x − x' mod m`: `g^x = g^z g^{x'}`, so `z = x − x'`. With
   `b = 1` first it outputs `x' − x`.
4. `B` succeeds whenever `A` finds a collision, except that `A`'s key is `g^w` for the
   sampler's `w`, within `2^{-n}` of uniform (`statClose_sampleBelowL`). So `A`'s collision
   probability is at most `B`'s discrete-log probability plus `2^{-n}`: negligible by
   `hDL`. -/
theorem dlHash_crh (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i ∧ dlM i = dlP i - 1) (hDL : G.DLHard) :
    (dlHash H G).Compresses ∧ (dlHash H G).CollisionResistant := by
  refine ⟨dlHash_compresses H G hV, ?_⟩
  rw [CRH.collisionResistant_iff]
  intro A
  have hhard := (ExpGroupGen.dlHard_iff G).1 hDL
    (FromDiscreteLog.collisionReduction H A)
  have hhalf : Negligible (fun n : ℕ => (1 / 2 : ℝ) ^ n) := by
    simpa only [one_div] using negligible_two_pow_neg
  have hneg : Negligible (fun n => accept ((dlHash H G).collisionGame A n)) := by
    refine (hhard.add hhalf).mono ⟨G.n₀, ?_⟩
    intro n hn
    rw [abs_of_nonneg (accept_nonneg _),
      abs_of_nonneg (add_nonneg (G.dlProb_nonneg _ n) (pow_nonneg (by norm_num) _))]
    exact dlHash_collision_bound H G (fun i hi => (hV i hi).1) A n hn
  exact ⟨_, hneg, fun _ => le_rfl⟩

end TCSlib.Cryptography.Authentication

## ===== TCSlib/Cryptography/Hashing/FromDiscreteLog/Algebra.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Candidates.DiscreteLog

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Recovering a discrete logarithm from a hash collision

The algebraic part of the reduction in Theorem 142.3 works in the group of units.
Equal selector bits force equal bounded exponents. With different selector bits,
the collision determines the challenge exponent as a difference modulo the order.

## Main definitions

There are no new definitions.

## Main results

* `expUnit_pow_val` reads powers of the generator unit as modular exponentiation.
* `unitCollision_selector_ne` rules out a collision with equal selector bits.
* `unitCollision_extract` gives the residue extracted from a collision.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, §5.5.2, proof of Theorem 142.3.
-/

namespace TCSlib.Cryptography.Authentication.FromDiscreteLog

open TCSlib.Cryptography.Candidates

/-- The residue of the generator unit raised to `e` is `g ^ e mod p` at a valid index,
where `g = dlG i` and `p = dlP i`. -/
theorem expUnit_pow_val {i : List Bool} (hi : ExpValid i) (e : ℕ) :
    ((expUnit hi ^ e : (ZMod (dlP i))ˣ) : ZMod (dlP i)).val = dlG i ^ e % dlP i := by
  have hvalid := (expValid_iff i).1 hi
  haveI : NeZero (dlP i) := ⟨hvalid.1.ne_zero⟩
  rw [val_units_pow, coe_expUnit, ZMod.val_natCast,
    Nat.mod_eq_of_lt hvalid.2.2.2.2.1]

/-- If adding `b ≤ m` to a residue `a < m` gives `c` modulo `m`, then adding
`m - b` to `c` recovers `a` modulo `m`. -/
private theorem residue_difference {m a b c : ℕ} (ha : a < m) (hb : b ≤ m)
    (h : Nat.ModEq m (a + b) c) : a = (c + (m - b)) % m := by
  have hh : (a + b + (m - b)) % m = (c + (m - b)) % m :=
    Nat.ModEq.add_right (m - b) h
  have heq : a + b + (m - b) = a + m := by omega
  rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt ha] at hh
  exact hh

/-- In the group of a valid index, `g^a g^b = g^c` with `a,b < m` recovers
`a = (c + (m - b)) mod m`, where `m` is the order of `g`. -/
private theorem residue_of_unit_pow_mul {i : List Bool} (hi : ExpValid i)
    {a b c : ℕ} (ha : a < dlM i) (hb : b < dlM i)
    (h : expUnit hi ^ a * expUnit hi ^ b = expUnit hi ^ c) :
    a = (c + (dlM i - b)) % dlM i := by
  have hp : expUnit hi ^ (a + b) = expUnit hi ^ c := by
    rw [pow_add]
    exact h
  have hm := pow_eq_pow_iff_modEq.1 hp
  rw [orderOf_expUnit hi] at hm
  exact residue_difference ha hb.le hm

/-- A collision between two distinct bounded exponent/selector pairs has different
selector bits: if `(x, b) ≠ (x', b')`, `x < dlM i`, `x' < dlM i` and
`(if b then u ^ z.val else 1) * u ^ x = (if b' then u ^ z.val else 1) * u ^ x'` for
`u = expUnit hi`, then `b ≠ b'` [PS10, proof of Theorem 142.3].

**Proof sketch.** With equal selectors, cancel their common unit factor. Read the
remaining powers through their numerals and apply the published injectivity of
exponentiation. The bounded exponent residues, and hence the two pairs, are equal. -/
theorem unitCollision_selector_ne {i : List Bool} (hi : ExpValid i)
    {x x' : ℕ} (hx : x < dlM i) (hx' : x' < dlM i)
    (z : ZMod (expOrd i)) {b b' : Bool}
    (hdistinct : (x, b) ≠ (x', b'))
    (hcollision :
      (if b then expUnit hi ^ z.val else 1) * expUnit hi ^ x =
      (if b' then expUnit hi ^ z.val else 1) * expUnit hi ^ x') : b ≠ b' := by
  intro hb
  subst b'
  have hp : expUnit hi ^ x = expUnit hi ^ x' := mul_left_cancel hcollision
  have hxord : x < expOrd i := by rw [expOrd_of_valid hi]; exact hx
  have hxord' : x' < expOrd i := by rw [expOrd_of_valid hi]; exact hx'
  have hxval : ((x : ℕ) : ZMod (expOrd i)).val = x := ZMod.val_cast_of_lt hxord
  have hxval' : ((x' : ℕ) : ZMod (expOrd i)).val = x' := ZMod.val_cast_of_lt hxord'
  have hnum := congrArg (fun u : (ZMod (dlP i))ˣ => (u : ZMod (dlP i)).val) hp
  change ((expUnit hi ^ x : (ZMod (dlP i))ˣ) : ZMod (dlP i)).val =
    ((expUnit hi ^ x' : (ZMod (dlP i))ˣ) : ZMod (dlP i)).val at hnum
  rw [expUnit_pow_val hi x, expUnit_pow_val hi x'] at hnum
  have hf : expF i ((x : ℕ) : ZMod (expOrd i)) =
      expF i ((x' : ℕ) : ZMod (expOrd i)) := by
    rw [expF_eq, expF_eq, hxval, hxval', hnum]
  have hres := congrArg (fun z : ZMod (expOrd i) => z.val) (expF_injective hi hf)
  change ((x : ℕ) : ZMod (expOrd i)).val = ((x' : ℕ) : ZMod (expOrd i)).val at hres
  rw [hxval, hxval'] at hres
  exact hdistinct (Prod.ext hres rfl)

/-- A collision between distinct bounded exponent/selector pairs reveals the
challenge exponent: it is `(x' + (m - x)) mod m` when the first selector is true,
and `(x + (m - x')) mod m` otherwise, that is,
`b ≠ b' ∧ z.val = if b then (x' + (m - x)) % m else (x + (m - x')) % m` for `m = dlM i`,
under the hypotheses of `unitCollision_selector_ne` [PS10, proof of Theorem 142.3].

**Proof sketch.** Equal selectors are impossible by cancellation. In the two remaining
cases the collision reads either `g^z g^x = g^x'` or `g^z g^x' = g^x`. The order of
the generator turns each equality into a congruence, and adding the complement of
the second exponent recovers the unique challenge residue below the order. -/
theorem unitCollision_extract {i : List Bool} (hi : ExpValid i)
    {x x' : ℕ} (hx : x < dlM i) (hx' : x' < dlM i)
    (z : ZMod (expOrd i)) {b b' : Bool}
    (hdistinct : (x, b) ≠ (x', b'))
    (hcollision :
      (if b then expUnit hi ^ z.val else 1) * expUnit hi ^ x =
      (if b' then expUnit hi ^ z.val else 1) * expUnit hi ^ x') :
    b ≠ b' ∧ z.val =
      if b then (x' + (dlM i - x)) % dlM i else (x + (dlM i - x')) % dlM i := by
  have hne := unitCollision_selector_ne hi hx hx' z hdistinct hcollision
  refine ⟨hne, ?_⟩
  have hz : z.val < dlM i := lt_of_lt_of_eq (ZMod.val_lt z) (expOrd_of_valid hi)
  cases b <;> cases b'
  · exact (hne rfl).elim
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hcollision ⊢
    exact residue_of_unit_pow_mul hi hz hx' hcollision.symm
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hcollision ⊢
    exact residue_of_unit_pow_mul hi hz hx hcollision
  · exact (hne rfl).elim

end TCSlib.Cryptography.Authentication.FromDiscreteLog

## ===== TCSlib/Cryptography/Hashing/FromDiscreteLog/Coins.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Splitting a machine's coin polynomial

A machine whose coin polynomial is a sum can read its coins as two consecutive bit vectors.
The equivalence below combines the published machine-coin identification, an equality of
evaluated polynomial lengths, and the shared coin-splitting equivalence.

## Main definitions

* `sumCoinsEquiv` splits the coins of a machine with coin polynomial `c + d`.

## Main results

* `sumCoinsEquiv_symm_ofFn` reads the reassembled coin string as a concatenation.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, §5.5.2, Protocol 142.2 and the proof of Theorem 142.3.
-/

namespace TCSlib.Cryptography.Authentication.FromDiscreteLog

open Complexity TCSlib.Cryptography

/-- A machine with coin polynomial `c + d` has coins equivalent to a `c(n)`-bit vector and
a `d(n)`-bit vector: for `h : A.coins = .add c d`,
`A.Coins n ≃ (Fin (c.eval n) → Bool) × (Fin (d.eval n) → Bool)`. -/
def sumCoinsEquiv (A : NUPPT) {c d : PolyExpr} (h : A.coins = .add c d) (n : ℕ) :
    A.Coins n ≃ (Fin (c.eval n) → Bool) × (Fin (d.eval n) → Bool) :=
  (NUPPT.coinsEquivPoly h n).trans
    ((Equiv.arrowCongr (finCongr (PolyExpr.eval_add c d n)) (Equiv.refl Bool)).trans
      (splitCoins (c.eval n) (d.eval n)))

/-- The sum-coin equivalence first identifies the machine's polynomial-length coin vector,
then transports its length through evaluation of addition and applies `splitCoins`:
`sumCoinsEquiv A h n = (NUPPT.coinsEquivPoly h n).trans (e.trans s)`, where
`e = Equiv.arrowCongr (finCongr (PolyExpr.eval_add c d n)) (Equiv.refl Bool)` and
`s = splitCoins (c.eval n) (d.eval n)`. -/
theorem sumCoinsEquiv_eq (A : NUPPT) {c d : PolyExpr} (h : A.coins = .add c d) (n : ℕ) :
    sumCoinsEquiv A h n =
      (NUPPT.coinsEquivPoly h n).trans
        ((Equiv.arrowCongr (finCongr (PolyExpr.eval_add c d n)) (Equiv.refl Bool)).trans
          (splitCoins (c.eval n) (d.eval n))) := rfl

/-- Reassembling the two components of a machine's sum-length coins concatenates their
words: `ofFn (sumCoinsEquiv.symm (r, s)) = ofFn r ++ ofFn s`. -/
theorem sumCoinsEquiv_symm_ofFn (A : NUPPT) {c d : PolyExpr}
    (h : A.coins = .add c d) (n : ℕ)
    (r : Fin (c.eval n) → Bool) (s : Fin (d.eval n) → Bool) :
    List.ofFn ((sumCoinsEquiv A h n).symm (r, s)) = List.ofFn r ++ List.ofFn s := by
  rw [sumCoinsEquiv_eq, Equiv.symm_trans_apply, NUPPT.coinsEquivPoly_symm_ofFn,
    Equiv.symm_trans_apply, Equiv.arrowCongr_symm]
  rw [finCongr_symm, Equiv.refl_symm, ofFn_arrowCongr_finCongr, ofFn_splitCoins_symm]

end TCSlib.Cryptography.Authentication.FromDiscreteLog

## ===== TCSlib/Cryptography/Hashing/FromDiscreteLog/Encoding.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Candidates.Arithmetic
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers

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
    List.ofFn x = List.ofFn (fun j : Fin n => x j.castSucc) ++ [x (Fin.last n)] := by
  rw [List.ofFn_succ', List.concat_eq_append]

/-- Taking the first `n` bits of an `(n + 1)`-bit word gives its restricted vector:
`(List.ofFn x).take n = List.ofFn (fun j : Fin n => x j.castSucc)`. -/
theorem inputWord_take {n : ℕ} (x : Fin (n + 1) → Bool) :
    (List.ofFn x).take n = List.ofFn (fun j : Fin n => x j.castSucc) := by
  rw [inputWord_split, List.take_left' (by simp)]

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

## ===== TCSlib/Cryptography/Hashing/FromDiscreteLog/Probability.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Hashing.CollisionResistant

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Collision-game acceptance as a uniform average

The collision game's two samples can be read as the existing uniform expectation
over generator coins and uniform probability over finder coins. This provides the
probability interface used by the discrete-logarithm reduction.

## Main definitions

There are no new definitions.

## Main results

* `expect_sample_eq_uexp` identifies finite uniform sampling with `uexp`.
* `collision_accept_eq` reads collision-game acceptance as a nested uniform average.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Definition 140.1 and proof of Theorem 142.3.
-/

namespace TCSlib.Cryptography.Authentication.FromDiscreteLog

open Complexity TCSlib.Cryptography TCSlib.Cryptography.Games

/-- The expectation of `f` after sampling a nonempty finite type is the uniform
average `uexp f`: `ProbComp.expect (ProbComp.sample α) f = uexp f`. Both expressions
are the sum of `f` divided by the type's size. -/
theorem expect_sample_eq_uexp {α : Type} [Fintype α] [Nonempty α] (f : α → ℝ) :
    ProbComp.expect (ProbComp.sample α) f = uexp f := by
  rw [ProbComp.expect_sample, uexp_def, inv_mul_eq_div]

/-- Collision-game acceptance is the average over generator coins of the probability,
over finder coins, that the two padded output halves are distinct domain elements
with equal hashes: `accept (C.collisionGame A n) = uexp (fun rg => uprob (fun r => W rg r))`,
where `W rg r` is `C.inDom n i xx.1 = true ∧ C.inDom n i xx.2 = true ∧ xx.1 ≠ xx.2 ∧`
`C.hash n i xx.1 = C.hash n i xx.2` for `i = C.gen.runAt n [] rg` and
`xx = splitBits (padFin (C.domLen.eval n + C.domLen.eval n) (A.runAt n i r))`
[PS10, Definition 140.1].

**Proof sketch.** Read the collision game and apply total probability to its two
samples. A pure Boolean verdict accepts exactly when its collision predicate holds;
the finite sampling expectations are the existing uniform average and probability. -/
theorem collision_accept_eq (C : CRH) (A : NUPPT) (n : ℕ) :
    accept (C.collisionGame A n) =
      uexp (fun rg : C.gen.Coins n =>
        uprob (fun r : A.Coins n =>
          let i := C.gen.runAt n [] rg
          let xx := splitBits
            (padFin (C.domLen.eval n + C.domLen.eval n) (A.runAt n i r))
          C.inDom n i xx.1 = true ∧ C.inDom n i xx.2 = true ∧ xx.1 ≠ xx.2 ∧
            C.hash n i xx.1 = C.hash n i xx.2)) := by
  classical
  rw [accept_eq, CRH.collisionGame_eq, ProbComp.prob_bind, expect_sample_eq_uexp]
  congr 1
  funext rg
  rw [ProbComp.prob_bind, expect_sample_eq_uexp, uprob_eq_uexp]
  congr 1
  funext r
  simp only [ProbComp.prob_pure, decide_eq_true_eq]

end TCSlib.Cryptography.Authentication.FromDiscreteLog

## ===== TCSlib/Cryptography/Hashing/FromDiscreteLog/Reduction.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Candidates.Arithmetic
import TCSlib.Cryptography.Candidates.DiscreteLog
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas
import TCSlib.Cryptography.Hashing.FromDiscreteLog.Encoding
import TCSlib.Complexity.Randomized.Closure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The discrete-logarithm reduction's machine

The reduction runs a collision finder on the supplied key, reads its two padded
domain inputs, and writes their exponent difference modulo the supplied order.
Its arithmetic uses the polynomial-time bundle and its coins and advice are the
collision finder's coins and advice.

## Main definitions

* `modularDifference` computes a subtraction modulo an encoded order.
* `collisionPost` reads the key and padded finder output and selects the difference.
* `reductionRaw`, `collisionReduction` run the finder and apply the postprocessor.

## Main results

* `polyTimeComputable_collisionPost` proves postprocessing is polynomial-time.
* `collisionPost_ofFn_append` reads the postprocessor on two fixed-width inputs.
* `collisionPost_split` reads the postprocessor on an arbitrary raw finder output.
* `collisionReduction_runAtL` gives the reduction's exact activation.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, §5.5.2, proof of Theorem 142.3.
-/

namespace TCSlib.Cryptography.Authentication.FromDiscreteLog

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Candidates

/-- The encoded modular difference of `a` and `b` modulo `m` is computed as
`(a + (m - b)) mod m`, using truncated natural subtraction. When `b ≤ m`, this
represents the group difference; the output has the width of `m`. -/
def modularDifference (a b m : List Bool) : List Bool :=
  pairSndD (divModStr (pairEncode
    (addStr (pairEncode a (subStr (pairEncode m b)))) m))

/-- The modular-difference routine adds `a` to the truncated subtraction of `b`
from `m`, divides by `m`, and keeps the remainder:
`modularDifference a b m = pairSndD (divModStr (pairEncode (addStr (pairEncode a s)) m))`,
where `s = subStr (pairEncode m b)`. -/
theorem modularDifference_eq (a b m : List Bool) :
    modularDifference a b m =
      pairSndD (divModStr (pairEncode
        (addStr (pairEncode a (subStr (pairEncode m b)))) m)) := rfl

/-- The modular-difference routine writes the `|m|`-bit numeral of
`(⟦a⟧ + (⟦m⟧ - ⟦b⟧)) mod ⟦m⟧`:
`modularDifference a b m = natToList m.length ((⟦a⟧ + (⟦m⟧ - ⟦b⟧)) % ⟦m⟧)`, where
`⟦w⟧ = listToNat w`. -/
theorem modularDifference_value (a b m : List Bool) :
    modularDifference a b m = natToList m.length
      ((NumberTheory.listToNat a +
        (NumberTheory.listToNat m - NumberTheory.listToNat b)) % NumberTheory.listToNat m) := by
  rw [modularDifference_eq, divModStr_pairEncode, pairSndD_pairEncode,
    listToNat_addStr, listToNat_subStr]

/-- Applying the modular-difference routine to three polynomial-time word functions
is polynomial-time under the arithmetic bundle: given `H : ArithmeticFP`,
`PolyTimeComputable a → PolyTimeComputable b → PolyTimeComputable m →`
`PolyTimeComputable fun w => modularDifference (a w) (b w) (m w)`. -/
theorem polyTimeComputable_modularDifference (H : ArithmeticFP)
    {a b m : List Bool → List Bool} (ha : PolyTimeComputable a)
    (hb : PolyTimeComputable b) (hm : PolyTimeComputable m) :
    PolyTimeComputable fun w => modularDifference (a w) (b w) (m w) := by
  have hs := H.sub.comp (hm.pairEncode hb)
  have hadd := H.add.comp (ha.pairEncode hs)
  have h := polyTimeComputable_pairSndD.comp (H.divMod.comp (hadd.pairEncode hm))
  refine h.congr fun w => ?_
  simp only [Function.comp_apply, modularDifference_eq]

/-- On `w = ⟨u, ⟨⟨i,y⟩, raw⟩⟩`, pad or truncate `raw` to two blocks of `|u|+1` bits and output
`collisionPost w = if s then modularDifference x' x m else modularDifference x x' m`.
Here `x`, `x'` are read from each block's first `|u|` bits and the first selector `s` from its
last bit, so the output is `x' - x mod m` if that selector is true and `x - x' mod m`
otherwise, where `m` is the order word in the index `i` [PS10, Theorem 142.3]. -/
def collisionPost (w : List Bool) : List Bool :=
  let u := pairFstD w
  let key := pairFstD (pairSndD w)
  let raw := pairSndD (pairSndD w)
  let m := pairFstD (pairSndD (pairFstD key))
  let padded := padStr (.add (.add .var (.const 1)) (.add .var (.const 1))) u raw
  let x := padded.take u.length
  let x' := (padded.drop (u.length + 1)).take u.length
  if (padded.drop u.length).headD false then modularDifference x' x m
  else modularDifference x x' m

/-- The postprocessor pads the raw output, reads two exponent prefixes and the first
selector, and applies the corresponding modular difference:
`collisionPost w = if s then modularDifference x' x m else modularDifference x x' m`, where
`u = pairFstD w`, `m = pairFstD (pairSndD (pairFstD (pairFstD (pairSndD w))))`,
`p = padStr (.add (.add .var (.const 1)) (.add .var (.const 1))) u (pairSndD (pairSndD w))`,
`x = p.take u.length`, `x' = (p.drop (u.length + 1)).take u.length` and
`s = (p.drop u.length).headD false`. -/
theorem collisionPost_eq (w : List Bool) :
    collisionPost w =
      let u := pairFstD w
      let key := pairFstD (pairSndD w)
      let raw := pairSndD (pairSndD w)
      let m := pairFstD (pairSndD (pairFstD key))
      let padded := padStr (.add (.add .var (.const 1)) (.add .var (.const 1))) u raw
      let x := padded.take u.length
      let x' := (padded.drop (u.length + 1)).take u.length
      if (padded.drop u.length).headD false then modularDifference x' x m
      else modularDifference x x' m := rfl

/-- The collision postprocessor is polynomial-time under the arithmetic bundle:
`ArithmeticFP → PolyTimeComputable collisionPost`.

**Proof sketch.** Pair projections read the parameter, raw output, and order word.
The existing padding and polynomial-prefix cuts read the two exponents and selector.
Both branches are compositions of subtraction, addition, and division, and the
existing conditional constructor chooses between them. -/
theorem polyTimeComputable_collisionPost (H : ArithmeticFP) :
    PolyTimeComputable collisionPost := by
  let width : PolyExpr := .add (.add .var (.const 1)) (.add .var (.const 1))
  have hu := polyTimeComputable_pairFstD
  have hkey := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hraw := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hm : PolyTimeComputable fun w =>
      pairFstD (pairSndD (pairFstD (pairFstD (pairSndD w)))) := by
    exact polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp hkey))
  have hpad : PolyTimeComputable fun w =>
      padStr width (pairFstD w) (pairSndD (pairSndD w)) := by
    convert (polyTimeComputable_padStr width).comp (hu.pairEncode hraw) using 1
    funext w
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hx : PolyTimeComputable fun w =>
      (padStr width (pairFstD w) (pairSndD (pairSndD w))).take (pairFstD w).length := by
    convert (polyTimeComputable_pairTakePoly .var).comp (hu.pairEncode hpad) using 1
    funext w
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]
  have hdrop : PolyTimeComputable fun w =>
      (padStr width (pairFstD w) (pairSndD (pairSndD w))).drop
        ((pairFstD w).length + 1) := by
    convert (polyTimeComputable_pairDropPoly (.add .var (.const 1))).comp
      (hu.pairEncode hpad) using 1
    funext w
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
      PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]
  have hx' : PolyTimeComputable fun w =>
      ((padStr width (pairFstD w) (pairSndD (pairSndD w))).drop
        ((pairFstD w).length + 1)).take (pairFstD w).length := by
    convert (polyTimeComputable_pairTakePoly .var).comp (hu.pairEncode hdrop) using 1
    funext w
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]
  have htail : PolyTimeComputable fun w =>
      (padStr width (pairFstD w) (pairSndD (pairSndD w))).drop (pairFstD w).length := by
    convert (polyTimeComputable_pairDropPoly .var).comp (hu.pairEncode hpad) using 1
    funext w
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]
  have hselector : PolyTimeComputable fun w =>
      [((padStr width (pairFstD w) (pairSndD (pairSndD w))).drop
        (pairFstD w).length).headD false] :=
    polyTimeComputable_headD.comp htail
  have h := polyTimeComputable_ite hselector
    (polyTimeComputable_modularDifference H hx' hx hm)
    (polyTimeComputable_modularDifference H hx hx' hm)
  exact h

/-- At a well-formed index, postprocessing the concatenation of two `(n + 1)`-bit
inputs writes the `n`-bit numeral of their selected exponent difference modulo
`dlM i`: `collisionPost (pairEncode (List.replicate n true) (pairEncode (pairEncode i y) v)) =`
`natToList n (if x (Fin.last n) then (x₀' + (m - x₀)) % m else (x₀ + (m - x₀')) % m)`, where
`v = List.ofFn x ++ List.ofFn x'`, `x₀ = listToNat ((List.ofFn x).take n)`, `x₀'` likewise and
`m = dlM i`. The first input's final bit chooses `x' - x` when true and `x - x'`
otherwise [PS10, proof of Theorem 142.3].

**Proof sketch.** The concatenation already has the padding width. Cutting after
`n + 1` bits separates the two inputs, and their first `n` bits give the exponent
words. The input decomposition identifies the selector. Well-formedness supplies
the order word's width, and the arithmetic reader evaluates each difference. -/
theorem collisionPost_ofFn_append (n : ℕ) (i y : List Bool)
    (x x' : Fin (n + 1) → Bool) (hw : WellFormedIndex n i) :
    collisionPost (pairEncode (List.replicate n true)
      (pairEncode (pairEncode i y) (List.ofFn x ++ List.ofFn x'))) =
      natToList n (if x (Fin.last n) then
        (NumberTheory.listToNat ((List.ofFn x').take n) +
          (dlM i - NumberTheory.listToNat ((List.ofFn x).take n))) % dlM i
        else (NumberTheory.listToNat ((List.ofFn x).take n) +
          (dlM i - NumberTheory.listToNat ((List.ofFn x').take n))) % dlM i) := by
  let width : PolyExpr := .add (.add .var (.const 1)) (.add .var (.const 1))
  have hlen : (List.ofFn x ++ List.ofFn x').length =
      width.eval (List.replicate n true).length := by
    simp only [width, List.length_append, List.length_ofFn, List.length_replicate,
      PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]
  have hpad : padStr width (List.replicate n true) (List.ofFn x ++ List.ofFn x') =
      List.ofFn x ++ List.ofFn x' := by
    rw [padStr_of_length_le _ _ _ hlen.le, hlen, Nat.sub_self,
      List.replicate_zero, List.append_nil]
  dsimp only [width] at hpad
  have hprefix : n ≤ (List.ofFn x).length := by
    rw [List.length_ofFn]
    omega
  have hfirst : (List.ofFn x ++ List.ofFn x').take n = (List.ofFn x).take n :=
    List.take_append_of_le_length hprefix
  have hsecond : ((List.ofFn x ++ List.ofFn x').drop (n + 1)).take n =
      (List.ofFn x').take n := by
    rw [List.drop_left' (show (List.ofFn x).length = n + 1 by rw [List.length_ofFn])]
  have hselector : ((List.ofFn x ++ List.ofFn x').drop n).headD false =
      x (Fin.last n) := by
    rw [List.drop_append_of_le_length hprefix, inputWord_drop]
    rfl
  have hmw : (pairFstD (pairSndD i)).length = n := by
    obtain ⟨a, b, c, he, _, hb, _⟩ := (wellFormedIndex_iff n i).1 hw
    rw [he, pairSndD_pairEncode, pairFstD_pairEncode]
    exact hb
  simp only [collisionPost_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate, hpad, hfirst, hsecond, hselector]
  simp only [modularDifference_value, hmw, ← dlM_eq i]
  split_ifs <;> rfl

/-- For any raw finder output, the postprocessor writes the selected difference
of the two inputs obtained by the collision game's padding and splitting:
`collisionPost (pairEncode (List.replicate n true) (pairEncode (pairEncode i y) raw)) =`
`natToList n (if xx.1 (Fin.last n) then (x₀' + (m - x₀)) % m else (x₀ + (m - x₀')) % m)`,
where `xx = splitBits (padFin ((n + 1) + (n + 1)) raw)`, `x₀ = listToNat ((List.ofFn xx.1).take n)`,
`x₀'` likewise for `xx.2` and `m = dlM i`. It writes
`x' - x mod m` when the first selector is true and `x - x' mod m` otherwise
[PS10, proof of Theorem 142.3].

**Proof sketch.** The words of the two split inputs concatenate to the padded raw
word. Padding that word again does not change it, by the published padding/encoding
readers and the fact that padding an encoded vector recovers the vector. Thus the
fixed-width postprocessor contract applies to the two split inputs. -/
theorem collisionPost_split (n : ℕ) (i y raw : List Bool) (hw : WellFormedIndex n i) :
    let xx := splitBits (a := n + 1) (b := n + 1) (padFin ((n + 1) + (n + 1)) raw)
    collisionPost (pairEncode (List.replicate n true)
      (pairEncode (pairEncode i y) raw)) =
      natToList n (if xx.1 (Fin.last n) then
        (NumberTheory.listToNat ((List.ofFn xx.2).take n) +
          (dlM i - NumberTheory.listToNat ((List.ofFn xx.1).take n))) % dlM i
        else (NumberTheory.listToNat ((List.ofFn xx.1).take n) +
          (dlM i - NumberTheory.listToNat ((List.ofFn xx.2).take n))) % dlM i) := by
  let width : PolyExpr := .add (.add .var (.const 1)) (.add .var (.const 1))
  let u := List.replicate n true
  let xx := splitBits (a := n + 1) (b := n + 1) (padFin ((n + 1) + (n + 1)) raw)
  have hsplit : List.ofFn xx.1 ++ List.ofFn xx.2 =
      List.ofFn (padFin ((n + 1) + (n + 1)) raw) := by
    change List.ofFn (splitBits (a := n + 1) (b := n + 1)
      (padFin ((n + 1) + (n + 1)) raw)).1 ++
      List.ofFn (splitBits (a := n + 1) (b := n + 1)
        (padFin ((n + 1) + (n + 1)) raw)).2 = _
    rw [ofFn_splitBits_fst, ofFn_splitBits_snd, List.take_append_drop]
  have hword : List.ofFn (padFin ((n + 1) + (n + 1)) raw) = padStr width u raw := by
    have hwidth : width.eval u.length = ((n + 1) + (n + 1)) := by
      simp only [width, u, List.length_replicate, PolyExpr.eval_add, PolyExpr.eval_var,
        PolyExpr.eval_const]
    exact (congrArg (fun k : ℕ => List.ofFn (padFin k raw)) hwidth).symm.trans
      (ofFn_padFin_eq_padStr width u raw)
  have hidem : padStr width u (padStr width u raw) = padStr width u raw := by
    calc
      padStr width u (padStr width u raw) =
          List.ofFn (padFin (width.eval u.length) (padStr width u raw)) :=
        (ofFn_padFin_eq_padStr width u _).symm
      _ = List.ofFn (padFin (width.eval u.length)
          (List.ofFn (padFin (width.eval u.length) raw))) := by
        rw [← ofFn_padFin_eq_padStr width u raw]
      _ = List.ofFn (padFin (width.eval u.length) raw) := by rw [padFin_ofFn]
      _ = padStr width u raw := ofFn_padFin_eq_padStr width u raw
  have hpost : collisionPost (pairEncode u (pairEncode (pairEncode i y) raw)) =
      collisionPost (pairEncode u
        (pairEncode (pairEncode i y) (List.ofFn xx.1 ++ List.ofFn xx.2))) := by
    rw [hsplit, hword]
    dsimp only [width] at hidem
    dsimp only [width]
    simp only [collisionPost_eq, pairFstD_pairEncode, pairSndD_pairEncode, hidem]
  exact hpost.trans (collisionPost_ofFn_append n i y xx.1 xx.2 hw)

/-- On a raw NUPPT layout, run `A` and apply `collisionPost` to the parameter,
the original key, and `A`'s raw output:
`reductionRaw A z = collisionPost (pairEncode (inParam z) (pairEncode (inArg z) (A.output z)))`
[PS10, proof of Theorem 142.3]. -/
def reductionRaw (A : NUPPT) (z : List Bool) : List Bool :=
  collisionPost (pairEncode (NUPPT.inParam z) (pairEncode (NUPPT.inArg z) (A.output z)))

/-- The raw reduction passes its parameter and original argument together with
the finder's raw output to the postprocessor:
`reductionRaw A z = collisionPost (pairEncode (inParam z) (pairEncode (inArg z) (A.output z)))`,
with `inParam = NUPPT.inParam` and `inArg = NUPPT.inArg`. -/
theorem reductionRaw_eq (A : NUPPT) (z : List Bool) :
    reductionRaw A z =
      collisionPost (pairEncode (NUPPT.inParam z)
        (pairEncode (NUPPT.inArg z) (A.output z))) := rfl

/-- Running a polynomial-time finder and then postprocessing its output is
polynomial-time under the arithmetic bundle:
`ArithmeticFP → PolyTimeComputable (reductionRaw A)`. -/
theorem polyTimeComputable_reductionRaw (H : ArithmeticFP) (A : NUPPT) :
    PolyTimeComputable (reductionRaw A) := by
  have h := (polyTimeComputable_collisionPost H).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode
      (NUPPT.polyTimeComputable_inArg.pairEncode A.polyTimeComputable_output))
  refine h.congr fun z => ?_
  simp only [Function.comp_apply, reductionRaw_eq]

/-- The discrete-log reduction runs the collision finder and extracts the exponent
difference, using the same coins and advice: it realizes `reductionRaw A` in polynomial time
with `(collisionReduction H A).coins = A.coins` and `(collisionReduction H A).advice = A.advice`
[PS10, proof of Theorem 142.3]. -/
noncomputable def collisionReduction (H : ArithmeticFP) (A : NUPPT) : NUPPT :=
  NUPPT.ofPolyTime (polyTimeComputable_reductionRaw H A)
    A.coins A.adv A.advice A.advice_length

/-- The reduction is the polynomial-time realization of `reductionRaw A`, with
the finder's coin polynomial, advice bound, and advice function:
`collisionReduction H A = NUPPT.ofPolyTime hraw A.coins A.adv A.advice A.advice_length`,
where `hraw = polyTimeComputable_reductionRaw H A`. -/
theorem collisionReduction_eq (H : ArithmeticFP) (A : NUPPT) :
    collisionReduction H A = NUPPT.ofPolyTime (polyTimeComputable_reductionRaw H A)
      A.coins A.adv A.advice A.advice_length := rfl

/-- The reduction uses the collision finder's coin polynomial:
`(collisionReduction H A).coins = A.coins`. -/
theorem collisionReduction_coins (H : ArithmeticFP) (A : NUPPT) :
    (collisionReduction H A).coins = A.coins := by
  rw [collisionReduction_eq, NUPPT.coins_ofPolyTime]

/-- The reduction has the collision finder's advice bound:
`(collisionReduction H A).adv = A.adv`. -/
theorem collisionReduction_adv (H : ArithmeticFP) (A : NUPPT) :
    (collisionReduction H A).adv = A.adv := by
  rw [collisionReduction_eq, NUPPT.adv_ofPolyTime]

/-- The reduction uses the collision finder's advice at every parameter:
`(collisionReduction H A).advice = A.advice`. -/
theorem collisionReduction_advice (H : ArithmeticFP) (A : NUPPT) :
    (collisionReduction H A).advice = A.advice := by
  rw [collisionReduction_eq, NUPPT.advice_ofPolyTime]

/-- At parameter `n` on key `key` and coin list `r`, the reduction postprocesses
`A.runAtL n key r` while retaining `1^n` and the original key:
`(collisionReduction H A).runAtL n key r = collisionPost (pairEncode u (pairEncode key o))`,
where `u = List.replicate n true` and `o = A.runAtL n key r`. -/
theorem collisionReduction_runAtL (H : ArithmeticFP) (A : NUPPT)
    (n : ℕ) (key r : List Bool) :
    (collisionReduction H A).runAtL n key r =
      collisionPost (pairEncode (List.replicate n true)
        (pairEncode key (A.runAtL n key r))) := by
  rw [collisionReduction_eq, NUPPT.runAtL_ofPolyTime, reductionRaw_eq]
  simp only [NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.advInput_eq,
    pairFstD_pairEncode, pairSndD_pairEncode, NUPPT.runAtL_eq]

/-- On typed coins, the reduction postprocesses the finder's output on the same
coin string, transported along the equality of their coin polynomials:
`(collisionReduction H A).runAt n key r = collisionPost (pairEncode u (pairEncode key o))`,
where `u = List.replicate n true`, `o = A.runAt n key r'` and
`r' = NUPPT.coinsCongr (collisionReduction_coins H A) n r`. -/
theorem collisionReduction_runAt (H : ArithmeticFP) (A : NUPPT)
    (n : ℕ) (key : List Bool) (r : (collisionReduction H A).Coins n) :
    (collisionReduction H A).runAt n key r =
      collisionPost (pairEncode (List.replicate n true)
        (pairEncode key (A.runAt n key
          (NUPPT.coinsCongr (collisionReduction_coins H A) n r)))) := by
  rw [NUPPT.runAt_eq, collisionReduction_runAtL, NUPPT.runAt_eq,
    NUPPT.coinsCongr_ofFn]

end TCSlib.Cryptography.Authentication.FromDiscreteLog

## ===== TCSlib/Cryptography/Hashing/FromDiscreteLog/Sampling.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Candidates.DiscreteLog

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Switching the sampled exponent to a uniform residue

The bounded rejection sampler is statistically close to a uniform number below
the group order. Identifying these numbers with the residues in `ZMod` gives the
distribution switch used by the discrete-logarithm reduction, including arbitrary
independent auxiliary coins.

## Main definitions

* `residueFinEquiv` identifies residues with bounded naturals at an equal modulus.

## Main results

* `sampleBelowL_uprob_le` bounds a sampled test by its ideal uniform-residue test
  plus `(1/2)^n`.

## Promotion requests

`residueFinEquiv` and its readers are general finite-residue encoding helpers.
`sampleBelowL_uprob_le` is a general reader of the candidate layer's sampler law.
They can be promoted to the shared encoding and candidate layers respectively.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, §5.5.2, proof of Theorem 142.3; the bounded sampler convention is that of
  the exponentiation collection in §2.8.
-/

namespace TCSlib.Cryptography.Authentication.FromDiscreteLog

open TCSlib.Cryptography TCSlib.Cryptography.Candidates

/-- Residues modulo a nonzero `m` are equivalent to `Fin k` when `m = k`, using
Mathlib's finite-residue ring equivalence and transport of the finite bound. -/
def residueFinEquiv {m k : ℕ} [NeZero m] (h : m = k) : ZMod m ≃ Fin k :=
  (ZMod.finEquiv m).symm.toEquiv.trans (finCongr h)

/-- The residue-to-finite equivalence is Mathlib's inverse `finEquiv`, followed by
transport along the equality of the moduli:
`residueFinEquiv h = (ZMod.finEquiv m).symm.toEquiv.trans (finCongr h)`. -/
theorem residueFinEquiv_eq {m k : ℕ} [NeZero m] (h : m = k) :
    residueFinEquiv h = (ZMod.finEquiv m).symm.toEquiv.trans (finCongr h) := rfl

/-- The residue-to-finite equivalence preserves the natural representative:
`(residueFinEquiv h z).val = z.val`. -/
theorem residueFinEquiv_val {m k : ℕ} [NeZero m] (h : m = k) (z : ZMod m) :
    (residueFinEquiv h z).val = z.val := by
  subst k
  cases m with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m => rfl

/-- At an index well formed at parameter `n`, evaluating the `n`-bit numeral of
a residue's natural representative returns `expF i z`:
`expEval (pairEncode i (natToList n z.val)) = expF i z`. -/
theorem expEval_natToList_val {n : ℕ} {i : List Bool} (hw : WellFormedIndex n i)
    (z : ZMod (expOrd i)) :
    expEval (Turing.pairEncode i (natToList n z.val)) = expF i z := by
  have h := expEval_spec i z
  simpa only [expEnc_eq, hw.dlW_eq] using h

/-- For a valid group index of order below `2^n`, any test of the rejection-sampled
exponent and independent finite auxiliary coins has probability at most its
probability for a uniform exponent in `ZMod (expOrd i)` plus `(1/2)^n`: for `m = dlM i < 2^n`,
`uprob (fun (s, a) => P ((sampleBelowL m (Nat.size m) n n (List.ofFn s)).getD 0) a) ≤`
`uprob (fun (z, a) => P z.val a) + (1/2)^n` over `s : Fin (n * n) → Bool`,
`z : ZMod (expOrd i)` and `a : ρ`
[PS10, proof of Theorem 142.3, using the candidate-layer sampler convention].

**Proof sketch.** Apply the published statistical-closeness theorem for bounded
rejection sampling. Relabel its ideal finite seed by the value-preserving residue
equivalence, then apply the statistical-switch bound with auxiliary coins and take
the upper side of its absolute-value bound. -/
theorem sampleBelowL_uprob_le {i : List Bool} (hi : ExpValid i) {n : ℕ}
    (hmn : dlM i < 2 ^ n) {ρ : Type*} [Fintype ρ] (P : ℕ → ρ → Prop) :
    uprob (fun z : (Fin (n * n) → Bool) × ρ =>
      P ((sampleBelowL (dlM i) (Nat.size (dlM i)) n n (List.ofFn z.1)).getD 0) z.2) ≤
      uprob (fun z : ZMod (expOrd i) × ρ => P z.1.val z.2) + (1 / 2 : ℝ) ^ n := by
  have hm : 0 < dlM i := ((expValid_iff i).1 hi).2.1
  have hs := ((statClose_sampleBelowL hm hmn).comp_equiv_right
    (residueFinEquiv (expOrd_of_valid hi))).abs_uprob_sub_le_prod P
  simp only [residueFinEquiv_val] at hs
  linarith [(abs_le.1 hs).2]

end TCSlib.Cryptography.Authentication.FromDiscreteLog

## ===== TCSlib/Cryptography/Candidates/DiscreteLog.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Complexity.Randomized.NonUniform
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Cryptography.Candidates.Arithmetic
import TCSlib.Cryptography.Candidates.Concrete
import TCSlib.Cryptography.Asymptotic.Collections
import TCSlib.Cryptography.NumberTheory.Units
import Mathlib.Data.Nat.Size
import Mathlib.GroupTheory.OrderOfElement

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The discrete-logarithm assumption and the discrete-logarithm collection

The discrete-logarithm material of [PS10, §2.8]: the *discrete-log assumption* for a family
of prime-order groups [PS10, Assumption 52.2] and the collection
`DL = {f_{q,g}(x) = g^x : Z_q → G_q}` with indices `(q, g)`, which is a collection of
one-way functions under that assumption [PS10, Theorem 52.3].

**The groups.** Following the text's own instantiation (p. 52, "one usually picks a prime of
the form `p = 2q + 1` … and then sets `G` to be the subgroup of squares in `Z_p^*`"), the
prime-order group `G_q` is the subgroup of squares of `Z_p^* = (ZMod p)ˣ` for a *safe prime*
`p = 2q + 1`. A group instance is the string index `⟨p, ⟨m, g⟩⟩` of three `n`-bit numerals:
the prime `p`, the order `m` of the group generated by `g` (the domain of the exponentiation
is `Z_m`), and the generator `g` (`ExpValid`: `orderOf g = m` in `Z_p`). The same index
format serves the full-group collection of `TCSlib.Cryptography.Candidates.DiscreteLogHardcore`
(`m = p − 1`, `g` a generator of `Z_p^*`, [PS10, Lemma 84.1]) and the El Gamal keys of
`TCSlib.Cryptography.Encryption.PublicKey.ElGamal`, so the exponentiation collection is built once,
generically over a validity predicate `V` on indices: `expCollection`.

**The sampler of instances.** The text samples `q ← Π_n; g ← Gen_{G_q}` and notes (p. 52–53)
that no efficient procedure for safe primes is known. Foundation decision D10 and the
deviation register (#15) replace the ideal sampler by an explicit *instance generator*
`ExpGroupGen V`: a PPT `Gen(1^n)` whose outputs, from a threshold `n₀` on, are valid indices
of three `n`-bit numerals. The assumption and the theorems are relative to the generator;
every statement about machines is conditional on the arithmetic bundle `ArithmeticFP` (D11).
Below the threshold the collection's own generator `expGen` outputs the fixed valid instance
`dlDefaultIndex = ⟨3, ⟨2, 2⟩⟩`, so that every generated index is valid and the sampler's
outputs decode at every parameter (`Collection.sample_spec`, run-3 audit P3-1); the
collection `expCollection H G hV` therefore takes the validity bridge `hV : ∀ i, V i → ExpValid i`
as an argument.

**Full-length primes.** Where a proof divides by `q` or `p − 1` (Lemma 84.1's range reduction,
the `1/q` term of Theorem 107.3) the proofs use full length `2^{n−1} ≤ p` (a convenience: the
hypothesis is dispensable in both headline theorems, gate 03f1 review, M1). This is
demanded only *except on a negligible set of coins* (`ExpGroupGen.FullLengthExcept δ` with
`Negligible δ`): a strict-PPT generator may fall back to a fixed instance when its rejection
loop fails (D10), and demanding full length on every coin string (`ExpGroupGen.FullLength`)
would require a deterministic polynomial-time construction of full-length primes of the
required form, which is not known (run-3 audit P8-2). The rejection sampler of numbers below
`m` (`sampleBelowL`) is within `(1/2)^n` of uniform (`statClose_sampleBelowL`, D10), the
closeness fact shared by the collection's domain sampler and the El Gamal samplers.

**Deviation:** Candidates: `A` receives `1^n` in Assumptions 30.1/52.2/53.1; `Π_n`
throughout; `p ≠ q` (odd / Blum) in RSA and Rabin; expected time replaced by strict PPT
with `2^{-n}` failure. Concretely: the adversary of Assumption 52.2 receives `⟨1^n, ⟨i, g^x⟩⟩`
with the whole index `i = ⟨p, ⟨q, g⟩⟩` (the text passes `g^x` only, source error 8), the
exponent `x ← Z_q` is ideal uniform in the experiment while the honest domain sampler is a
truncated rejection sampler within `2^{-n}` of uniform (D10), the answer is read as an
`n`-bit numeral (wrong length = failure, D5), "`Pr[…] < ε(n)` for a negligible `ε`" is
"`Pr[…]` is negligible", and the ideal "`q ← Π_n; g ← Gen_{G_q}`" is the law of the instance
generator. Theorem 52.3's `R_i = G_p`, `f_{p,g}` are read as `G_q`, `f_{q,g}` (source
error 8) and `k` as `n`.

## Main definitions

* `TCSlib.Cryptography.Candidates.dlP`, `dlM`, `dlG`, `dlW`, `WellFormedIndex` — reading the
  index `⟨p, ⟨m, g⟩⟩`; `TCSlib.Cryptography.Candidates.ExpValid` — valid indices.
* `TCSlib.Cryptography.Candidates.expOrd`, `expEnc`, `expDec`, `expF`, `expEval` — the
  domain `Z_m`, its encoding, the function `x ↦ g^x mod p` and its evaluator.
* `TCSlib.Cryptography.Candidates.ExpGroupGen` — instance generators;
  `ExpGroupGen.dlProb`, `ExpGroupGen.DLHard` — the discrete-log experiment and hardness;
  `ExpGroupGen.FullLength`, `ExpGroupGen.FullLengthExcept` — full-length primes (on every
  coin string / except on a set of coins of probability `δ n`).
* `TCSlib.Cryptography.Candidates.sampleBelowL`, `expSampler`, `dlDefaultIndex`, `expGen`,
  `expCollection` — the exponentiation collection of an instance generator.
* `TCSlib.Cryptography.Candidates.SafePrimeValid`, `SafePrimeGen`,
  `TCSlib.Cryptography.Candidates.DLAssumption` — [PS10, Assumption 52.2];
  `TCSlib.Cryptography.Candidates.dlCollection` — the collection `DL` [PS10, Theorem 52.3].

## Main results

* `TCSlib.Cryptography.Candidates.expF_injective` — `x ↦ g^x` is injective on `Z_m` at a
  valid index (the remark after [PS10, Theorem 52.3]; Claim-53.2 of the inventory, proved).
* `TCSlib.Cryptography.Candidates.expEval_spec`, `expDec_expEnc` — the collection data
  (proved).
* `TCSlib.Cryptography.Candidates.statClose_sampleBelowL` — the rejection sampler of numbers
  below `m` is within `(1/2)^n` of uniform (D10);
  `ExpGroupGen.FullLength.fullLengthExcept`, `ExpGroupGen.FullLength.exists_fullLengthExcept` —
  full length on every coin string is the `δ = 0` case (proved).
* `TCSlib.Cryptography.Candidates.expCollection_invProbAt_le` — inverting the collection is
  the discrete-log experiment; `expCollection_sampleClose`, `expCollection_oneWay`.
* `TCSlib.Cryptography.Candidates.dlCollection_oneWay` — [PS10, Theorem 52.3].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.8: Definition 52.1, Assumption 52.2, Theorem 52.3 and the remarks on pp. 52–53.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Definition 2.1 (the concrete inversion experiment).
-/

namespace TCSlib.Cryptography.Candidates

open Complexity Turing NumberTheory Finset

/-! ## Group instances `⟨p, ⟨m, g⟩⟩` -/

/-- The prime `p` read from the index `⟨p, ⟨m, g⟩⟩`. -/
def dlP (i : List Bool) : ℕ := listToNat (pairFstD i)

/-- The defining equation of `dlP`: `dlP i = listToNat (pairFstD i)`, the number read from the
first component of `⟨p, ⟨m, g⟩⟩`. -/
theorem dlP_eq (i : List Bool) : dlP i = listToNat (pairFstD i) := rfl

/-- The group order `m` read from the index `⟨p, ⟨m, g⟩⟩` (the domain of the exponentiation
is `Z_m`; `m = q` for the prime-order groups, `m = p − 1` for `Z_p^*`). -/
def dlM (i : List Bool) : ℕ := listToNat (pairFstD (pairSndD i))

/-- The defining equation of `dlM`: `dlM i = listToNat (pairFstD (pairSndD i))`, the number read
from the middle component of `⟨p, ⟨m, g⟩⟩`. -/
theorem dlM_eq (i : List Bool) : dlM i = listToNat (pairFstD (pairSndD i)) := rfl

/-- The generator `g` read from the index `⟨p, ⟨m, g⟩⟩`. -/
def dlG (i : List Bool) : ℕ := listToNat (pairSndD (pairSndD i))

/-- The defining equation of `dlG`: `dlG i = listToNat (pairSndD (pairSndD i))`, the number read
from the last component of `⟨p, ⟨m, g⟩⟩`. -/
theorem dlG_eq (i : List Bool) : dlG i = listToNat (pairSndD (pairSndD i)) := rfl

/-- The numeral width of an index: the width of the numeral of `p` (all group elements are
encoded with this width). -/
def dlW (i : List Bool) : ℕ := (pairFstD i).length

/-- An index is *well formed at parameter `n`* when it is a pair `⟨a, ⟨b, c⟩⟩` of three
`n`-bit numerals (the text's "`p` of length `n`"). -/
def WellFormedIndex (n : ℕ) (i : List Bool) : Prop :=
  ∃ a b c : List Bool, i = pairEncode a (pairEncode b c) ∧ a.length = n ∧ b.length = n ∧ c.length = n

/-- Unfolding `WellFormedIndex`: `i` is well formed at `n` iff `i = ⟨a, ⟨b, c⟩⟩` for three
`n`-bit strings `a`, `b`, `c`. -/
theorem wellFormedIndex_iff (n : ℕ) (i : List Bool) :
    WellFormedIndex n i ↔ ∃ a b c : List Bool,
      i = pairEncode a (pairEncode b c) ∧ a.length = n ∧ b.length = n ∧ c.length = n :=
  Iff.rfl

/-- The width of a well-formed index is `n`. -/
theorem WellFormedIndex.dlW_eq {n : ℕ} {i : List Bool} (h : WellFormedIndex n i) : dlW i = n := by
  obtain ⟨a, b, c, rfl, ha, -, -⟩ := h
  simp [dlW, ha]

/-- A well-formed index at parameter `n` has length `5n + 4`. -/
theorem WellFormedIndex.length_eq {n : ℕ} {i : List Bool} (h : WellFormedIndex n i) :
    i.length = 5 * n + 4 := by
  obtain ⟨a, b, c, rfl, ha, hb, hc⟩ := h
  simp only [length_pairEncode, ha, hb, hc]
  ring

/-- `p < 2^{dlW i}`: the prime fits its numeral. -/
theorem dlP_lt_two_pow (i : List Bool) : dlP i < 2 ^ dlW i := listToNat_lt_two_pow _

/-- An index `⟨p, ⟨m, g⟩⟩` is *valid* when `p` is prime, `0 < m < p`, `0 < g < p`, and `g` has
order exactly `m` in `Z_p` (so `x ↦ g^x` is a bijection of `Z_m` onto the subgroup generated
by `g`, [PS10, Definition 52.1]). (Not efficiently decidable from the index — generators only
ever output valid indices.) -/
def ExpValid (i : List Bool) : Prop :=
  (dlP i).Prime ∧ 0 < dlM i ∧ dlM i < dlP i ∧ 0 < dlG i ∧ dlG i < dlP i ∧
    orderOf ((dlG i : ℕ) : ZMod (dlP i)) = dlM i

/-- Unfolding `ExpValid`: `i` is valid iff `p` is prime, `0 < m < p`, `0 < g < p` and `g` has
order `m` in `Z_p` (with `p = dlP i`, `m = dlM i`, `g = dlG i`). -/
theorem expValid_iff (i : List Bool) :
    ExpValid i ↔ (dlP i).Prime ∧ 0 < dlM i ∧ dlM i < dlP i ∧ 0 < dlG i ∧ dlG i < dlP i ∧
      orderOf ((dlG i : ℕ) : ZMod (dlP i)) = dlM i :=
  Iff.rfl

noncomputable instance : DecidablePred ExpValid := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The order of the domain at an index: `m` for a valid index and `1` otherwise (so that the
domain `Z_m` is always a finite group). -/
noncomputable def expOrd (i : List Bool) : ℕ := if ExpValid i then dlM i else 1

instance (i : List Bool) : NeZero (expOrd i) := by
  unfold expOrd
  split_ifs with h
  · exact ⟨h.2.1.ne'⟩
  · exact ⟨one_ne_zero⟩

/-- `expOrd` of a valid index is `m`. -/
theorem expOrd_of_valid {i : List Bool} (h : ExpValid i) : expOrd i = dlM i := if_pos h

/-- `expOrd` of an invalid index is `1`. -/
theorem expOrd_of_not_valid {i : List Bool} (h : ¬ ExpValid i) : expOrd i = 1 := if_neg h

/-- The order of the domain fits the numeral width: `expOrd i ≤ 2^{dlW i}`. -/
theorem expOrd_le_two_pow (i : List Bool) : expOrd i ≤ 2 ^ dlW i := by
  unfold expOrd
  split_ifs with h
  · exact (h.2.2.1.trans (dlP_lt_two_pow i)).le
  · exact Nat.one_le_two_pow

/-- The residue of an element of the domain fits the numeral width. -/
theorem val_lt_two_pow_dlW (i : List Bool) (x : ZMod (expOrd i)) : x.val < 2 ^ dlW i :=
  lt_of_lt_of_le (ZMod.val_lt x) (expOrd_le_two_pow i)

/-- `g` is coprime to `p` at a valid index (`0 < g < p` and `p` prime). -/
theorem coprime_dlG_dlP {i : List Bool} (h : ExpValid i) : Nat.Coprime (dlG i) (dlP i) :=
  ((Nat.Prime.coprime_iff_not_dvd h.1).2 (Nat.not_dvd_of_pos_of_lt h.2.2.2.1 h.2.2.2.2.1)).symm

/-- The generator `g` as a unit of `Z_p` at a valid index. -/
noncomputable def expUnit {i : List Bool} (h : ExpValid i) : (ZMod (dlP i))ˣ :=
  ZMod.unitOfCoprime (dlG i) (coprime_dlG_dlP h)

/-- The value of `expUnit` is `g mod p`. -/
theorem coe_expUnit {i : List Bool} (h : ExpValid i) :
    (expUnit h : ZMod (dlP i)) = ((dlG i : ℕ) : ZMod (dlP i)) := ZMod.coe_unitOfCoprime _ _

/-- The order of the unit `g` is `m` [PS10, Definition 52.1, "`g` is a generator"]. -/
theorem orderOf_expUnit {i : List Bool} (h : ExpValid i) : orderOf (expUnit h) = dlM i := by
  rw [← orderOf_units, coe_expUnit]
  exact h.2.2.2.2.2

/-! ## The domain `Z_m`, its encoding and the function `x ↦ g^x` -/

/-- The string encoding of `x ∈ Z_m`: its residue as a numeral of the index width. -/
noncomputable def expEnc (i : List Bool) (x : ZMod (expOrd i)) : List Bool := natToList (dlW i) x.val

/-- The defining equation of `expEnc`: `expEnc i x = ⟦x.val⟧_{dlW i}`, the residue of `x` as a
numeral of the index width. -/
theorem expEnc_eq (i : List Bool) (x : ZMod (expOrd i)) : expEnc i x = natToList (dlW i) x.val :=
  rfl

/-- The decoder of `Z_m`: a numeral of the index width reading as a number below `m`. -/
noncomputable def expDec (i : List Bool) (w : List Bool) : Option (ZMod (expOrd i)) :=
  if w.length = dlW i ∧ listToNat w < expOrd i then some ((listToNat w : ℕ) : ZMod (expOrd i))
  else none

/-- Decoding inverts encoding (the clause `decD_encD` of `Collection`). -/
theorem expDec_expEnc (i : List Bool) (x : ZMod (expOrd i)) : expDec i (expEnc i x) = some x := by
  have hl : listToNat (expEnc i x) = x.val := listToNat_natToList (val_lt_two_pow_dlW i x)
  rw [expDec, if_pos ⟨by simp [expEnc], by rw [hl]; exact ZMod.val_lt x⟩, hl,
    ZMod.natCast_zmod_val]

/-- **Decoding is canonical** (the clause `Collection.encD_decD` of `expCollection`; gate 03b,
finding 1): a string that `expDec i` decodes to `x` is `expEnc i x`, since it is a numeral of
the index width reading below `m` (`natToList_val_natCast`). -/
theorem expEnc_of_expDec {i w : List Bool} {x : ZMod (expOrd i)} (h : expDec i w = some x) :
    expEnc i x = w := by
  rw [expDec] at h
  split_ifs at h with hw
  rw [← Option.some.inj h, expEnc, natToList_val_natCast hw.1 hw.2]

/-- **The function `f_{q,g}(x) = g^x mod p`** [PS10, Theorem 52.3] as a string function on
`Z_m`: the numeral of `g^x mod p` of the index width (the evaluator `modExpStr` mirrored). -/
noncomputable def expF (i : List Bool) (x : ZMod (expOrd i)) : List Bool :=
  natToList (dlW i) (dlG i ^ x.val % dlP i)

/-- The defining equation of `expF`: `expF i x = ⟦g^x mod p⟧_{dlW i}`, the numeral of
`dlG i ^ x.val % dlP i` of the index width. -/
theorem expF_eq (i : List Bool) (x : ZMod (expOrd i)) :
    expF i x = natToList (dlW i) (dlG i ^ x.val % dlP i) := rfl

/-- The evaluator of the exponentiation collection on `⟨⟨p, ⟨m, g⟩⟩, x⟩`: one modular
exponentiation `modExpStr ⟨g, ⟨x, p⟩⟩` [PS10, Theorem 52.3, "it is easy to evaluate"]. -/
def expEval (z : List Bool) : List Bool :=
  modExpStr (pairEncode (pairSndD (pairSndD (pairFstD z)))
    (pairEncode (pairSndD z) (pairFstD (pairFstD z))))

/-- The evaluator computes `expF` on encoded elements. -/
theorem expEval_spec (i : List Bool) (x : ZMod (expOrd i)) :
    expEval (pairEncode i (expEnc i x)) = expF i x := by
  have hl : listToNat (natToList (dlW i) x.val) = x.val :=
    listToNat_natToList (val_lt_two_pow_dlW i x)
  simp only [expEval, expF, expEnc, dlG, dlP, dlW, pairFstD_pairEncode, pairSndD_pairEncode,
    modExpStr_pairEncode] at hl ⊢
  rw [hl]

/-- The evaluator is polynomial-time given modular exponentiation. -/
theorem polyTimeComputable_expEval (H : ArithmeticFP) : PolyTimeComputable expEval :=
  H.modExp.comp ((polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp
    polyTimeComputable_pairFstD)).pairEncode (polyTimeComputable_pairSndD.pairEncode
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)))

/-- **`x ↦ g^x` is injective on `Z_m`** at a valid index (the remark after
[PS10, Theorem 52.3]: "each function is a permutation"; Claim-53.2 of the inventory): since
`g` has order `m` in `Z_p`, `g^a = g^b` forces `a ≡ b (mod m)`.

**Proof sketch.** Both numerals have width `dlW i` and read as numbers below `p < 2^{dlW i}`
(`natToList_injOn`), so `g^a ≡ g^b (mod p)`; in the group of units, `pow_eq_pow_iff_modEq`
with `orderOf_expUnit` gives `a ≡ b (mod m)`, and `a, b < m`. -/
theorem expF_injective {i : List Bool} (h : ExpValid i) : Function.Injective (expF i) := by
  intro x y hxy
  have hlt : ∀ e : ℕ, dlG i ^ e % dlP i < 2 ^ dlW i :=
    fun e => (Nat.mod_lt _ h.1.pos).trans (dlP_lt_two_pow i)
  have h1 : dlG i ^ x.val % dlP i = dlG i ^ y.val % dlP i := natToList_injOn (hlt _) (hlt _) hxy
  have h2 : expUnit h ^ x.val = expUnit h ^ y.val := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, coe_expUnit, ← Nat.cast_pow,
      ← Nat.cast_pow, ← ZMod.natCast_mod, h1, ZMod.natCast_mod]
  have h3 := pow_eq_pow_iff_modEq.1 h2
  rw [orderOf_expUnit h] at h3
  have hx : x.val < dlM i := lt_of_lt_of_eq (ZMod.val_lt x) (expOrd_of_valid h)
  have hy : y.val < dlM i := lt_of_lt_of_eq (ZMod.val_lt y) (expOrd_of_valid h)
  exact ZMod.val_injective _ (h3.eq_of_lt_of_lt hx hy)

/-! ## Instance generators and the discrete-log experiment -/

/-- An **instance generator** for exponentiation collections with validity predicate `V`:
a PPT `Gen(1^n)` whose outputs, from the threshold `n₀` on, satisfy `V` and are well-formed
indices of three `n`-bit numerals. The formal counterpart of the text's
"`q ← Π_n; g ← Gen_{G_q}`" [PS10, Assumption 52.2] and "pick a safe prime `p = 2q + 1` of
length `n`" [PS10, Algorithm 106.2]; the text itself notes (pp. 52–53) that no efficient
sampler of safe primes with generators is known, so the generator is a hypothesis object.

**Deviation:** the ideal samplers of the text are replaced by a PPT generator relative to
which the assumptions are stated (D10, deviations register #15); outputs below `n₀` are
unconstrained (the degenerate parameters). -/
structure ExpGroupGen (V : List Bool → Prop) where
  /-- The generator `Gen(1^n)`. -/
  gen : NUPPT
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- The threshold from which the outputs are valid. -/
  n₀ : ℕ
  /-- Outputs are valid from the threshold on. -/
  valid : ∀ n (r : gen.Coins n), n₀ ≤ n → V (gen.runAt n [] r)
  /-- Outputs are well-formed indices of `n`-bit numerals from the threshold on. -/
  wellFormed : ∀ n (r : gen.Coins n), n₀ ≤ n → WellFormedIndex n (gen.runAt n [] r)

namespace ExpGroupGen

variable {V : List Bool → Prop} (G : ExpGroupGen V)

/-- The generator outputs primes of *full length* `n` on **every** coin string: `2^{n-1} ≤ p`
at every generated index from `n₀` on (the text's "`p` of length `n`" read with a leading
`1`; `p < 2^n` already follows from `wellFormed`). Too strong as a hypothesis of a theorem
(see `FullLengthExcept`, run-3 audit P8-2): together with `valid` it asks for a deterministic
polynomial-time construction (run the generator on the all-zero coins) of a full-length prime
of the required form at every `n ≥ n₀`, which is not known. Kept as the deterministic
special case (`FullLength.fullLengthExcept`). -/
def FullLength : Prop :=
  ∀ n (r : G.gen.Coins n), G.n₀ ≤ n → 2 ^ (n - 1) ≤ dlP (G.gen.runAt n [] r)

/-- The generator outputs primes of full length `n` **except on a set of coins of probability
at most `δ n`**: for `n ≥ n₀`, `Pr_r[p < 2^{n−1}] ≤ δ n` (the fallback instance of a strict-PPT
rejection sampler, D10). Used, with `Negligible δ`, by the proofs that divide by `q` or
`p − 1` (Lemma 84.1's range reduction, the `1/q` term of Theorem 107.3): the short-prime coins
are discarded and contribute at most `δ n`. This is a convenience: instances with `p − 1` below
a polynomial can be inverted by exhaustive search, so `hbig` could be dropped (gate 03f1
review, M1; ruling R-03f1-1 (A) keeps it). Whether safe primes (resp. primes `≡ 3 (mod 4)`
with a generator) of full length can be produced for every `n` except with negligible
probability is itself open ([PS10, p. 52]: the sampler's "basic theoretical properties are
unknown"); the hypothesis `∃ δ, Negligible δ ∧ G.FullLengthExcept δ` of the headline theorems
records this.

Repair (run-3 audit P8-2): replaces the hypothesis `G.FullLength` of
`fullDLCollection_hardCore` and `elGamal_secure`, which demanded `2^{n−1} ≤ p` on every coin
string and made `{G // G.FullLength}` not known to be inhabited for reasons unrelated to any
cryptographic assumption (contrary to D10 / deviation 15, strict PPT with `2^{-n}` failure). -/
def FullLengthExcept (δ : ℕ → ℝ) : Prop :=
  ∀ n, G.n₀ ≤ n → uprob (fun r : G.gen.Coins n => dlP (G.gen.runAt n [] r) < 2 ^ (n - 1)) ≤ δ n

/-- Unfolding `FullLengthExcept`: `G.FullLengthExcept δ` iff for every `n ≥ n₀` the probability
over the generator's coins that `p < 2^{n−1}` is at most `δ n`. -/
theorem fullLengthExcept_iff (δ : ℕ → ℝ) :
    G.FullLengthExcept δ ↔ ∀ n, G.n₀ ≤ n →
      uprob (fun r : G.gen.Coins n => dlP (G.gen.runAt n [] r) < 2 ^ (n - 1)) ≤ δ n :=
  Iff.rfl

/-- **The discrete-log experiment** [PS10, Assumption 52.2]:
`Pr[i ← Gen(1^n); x ← Z_m : A(1^n, ⟨i, g^x⟩) = x]`, the average over the generator's coins
of the probability, over the ideal uniform `x ∈ Z_m` and the coins of `A`, that the answer of
`A` decodes to an `n`-bit numeral reading as `x`.

**Deviation:** `A` receives `1^n` and the index (the text's `A(g^x)`); ideal uniform `x`;
`n`-bit answers (module docstring). -/
noncomputable def dlProb (A : NUPPT) (n : ℕ) : ℝ :=
  uexp fun r : G.gen.Coins n =>
    uprob fun z : ZMod (expOrd (G.gen.runAt n [] r)) × A.Coins n =>
      ∃ x : Fin n → Bool,
        decodeFin n (A.runAt n (pairEncode (G.gen.runAt n [] r) (expF _ z.1)) z.2) = some x ∧
          bitsToNat x = z.1.val

/-- The defining equation of `dlProb`: `G.dlProb A n` is the average over the generator's coins
`r` of the probability, over `x ∈ Z_m` and the coins of `A`, that `A`'s answer on
`⟨Gen(1^n; r), g^x⟩` decodes to an `n`-bit numeral reading as `x`. -/
theorem dlProb_eq (A : NUPPT) (n : ℕ) :
    G.dlProb A n = uexp fun r : G.gen.Coins n =>
      uprob fun z : ZMod (expOrd (G.gen.runAt n [] r)) × A.Coins n =>
        ∃ x : Fin n → Bool,
          decodeFin n (A.runAt n (pairEncode (G.gen.runAt n [] r) (expF _ z.1)) z.2) = some x ∧
            bitsToNat x = z.1.val :=
  rfl

/-- **Discrete-log hardness relative to the generator**: every non-uniform PPT solves the
discrete-log experiment with negligible probability. The safe-prime instance is
[PS10, Assumption 52.2] (`DLAssumption`); the full-group instance is the assumption of
[PS10, Lemma 84.1] (`DiscreteLogHardcore`). -/
def DLHard : Prop := ∀ A : NUPPT, Negligible fun n => G.dlProb A n

/-- Unfolding `DLHard`: `G.DLHard` iff `n ↦ G.dlProb A n` is negligible for every non-uniform
PPT `A`. -/
theorem dlHard_iff : G.DLHard ↔ ∀ A : NUPPT, Negligible fun n => G.dlProb A n := Iff.rfl

/-- The discrete-log probability is nonnegative. -/
theorem dlProb_nonneg (A : NUPPT) (n : ℕ) : 0 ≤ G.dlProb A n := by
  unfold dlProb
  rw [uexp_def]
  exact div_nonneg (Finset.sum_nonneg fun z _ => uprob_nonneg _) (Nat.cast_nonneg _)

/-- The discrete-log probability is at most one. -/
theorem dlProb_le_one (A : NUPPT) (n : ℕ) : G.dlProb A n ≤ 1 := by
  haveI : Nonempty (G.gen.Coins n) := ⟨fun _ => false⟩
  unfold dlProb
  exact (OneWay.uexp_mono fun r => uprob_le_one _).trans (OneWay.uexp_const 1).le

end ExpGroupGen

/-- Full length on every coin string is full length except on a set of probability `0`. -/
theorem ExpGroupGen.FullLength.fullLengthExcept {V : List Bool → Prop} {G : ExpGroupGen V}
    (h : G.FullLength) : G.FullLengthExcept fun _ => 0 := by
  intro n hn
  have hz : uprob (fun r : G.gen.Coins n => dlP (G.gen.runAt n [] r) < 2 ^ (n - 1)) = 0 := by
    rw [← uprob_false (α := G.gen.Coins n)]
    exact OneWay.uprob_congr fun r => ⟨fun hlt => (not_le.mpr hlt (h n r hn)).elim, False.elim⟩
  exact hz.le

/-- A generator of full length on every coin string satisfies the hypothesis
`∃ δ, Negligible δ ∧ G.FullLengthExcept δ` of the headline theorems (with `δ = 0`). -/
theorem ExpGroupGen.FullLength.exists_fullLengthExcept {V : List Bool → Prop} {G : ExpGroupGen V}
    (h : G.FullLength) : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.FullLengthExcept δ := by
  refine ⟨fun _ => 0, (negligible_iff _).2 fun c => ⟨1, fun n hn => ?_⟩, h.fullLengthExcept⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [abs_zero]
  positivity

/-! ## The exponentiation collection of an instance generator -/

/-- The fixed valid instance `⟨p, ⟨m, g⟩⟩ = ⟨3, ⟨2, 2⟩⟩` with `2`-bit numerals (`2` has order
`2` in `Z_3`): the index output by the collection's generator below the threshold `n₀` of the
instance generator, where the latter's outputs are unconstrained.

Repair (run-3 audit P3-1): `Collection.sample_spec` requires the sampler's outputs to decode
at *every* generated index, so the collection's generator must output valid indices at every
parameter. -/
def dlDefaultIndex : List Bool :=
  pairEncode (natToList 2 3) (pairEncode (natToList 2 2) (natToList 2 2))

/-- The default index is valid: `3` is prime, `0 < 2 < 3`, and `2` has order `2` in `Z_3`. -/
theorem expValid_dlDefaultIndex : ExpValid dlDefaultIndex := by
  have h3 : dlP dlDefaultIndex = 3 := by
    simp [dlP, dlDefaultIndex, listToNat_natToList (by norm_num : 3 < 2 ^ 2)]
  have h2 : dlM dlDefaultIndex = 2 := by
    simp [dlM, dlDefaultIndex, listToNat_natToList (by norm_num : 2 < 2 ^ 2)]
  have hg : dlG dlDefaultIndex = 2 := by
    simp [dlG, dlDefaultIndex, listToNat_natToList (by norm_num : 2 < 2 ^ 2)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h3]; exact Nat.prime_three
  · rw [h2]; norm_num
  · rw [h2, h3]; norm_num
  · rw [hg]; norm_num
  · rw [hg, h3]; norm_num
  · rw [hg, h2, h3]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by decide) (by decide)

/-- The string function of the collection's index generator on the raw layout
`⟨⟨⟨1^n, []⟩, α⟩, r⟩`: `⟨Gen(1^n; r), []⟩` (no trapdoor) from the threshold `n₀` on, and
`⟨dlDefaultIndex, []⟩` below it (where the instance generator's outputs are unconstrained;
run-3 audit P3-1). -/
def expGenFun {V : List Bool → Prop} (G : ExpGroupGen V) (z : List Bool) : List Bool :=
  if G.n₀ ≤ (NUPPT.inParam z).length then
    pairEncode (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z))) []
  else pairEncode dlDefaultIndex []

/-- The raw index generator pairs the instance generator's output with the empty trapdoor
when the parameter length is at least `G.n₀`, and otherwise pairs `dlDefaultIndex` with it:
`expGenFun G z = if G.n₀ ≤ u.length then pairEncode o [] else pairEncode dlDefaultIndex []`,
where `u = NUPPT.inParam z` and `o = G.gen.output (NUPPT.layout u [] [] (NUPPT.inCoins z))`. -/
theorem expGenFun_eq {V : List Bool → Prop} (G : ExpGroupGen V) (z : List Bool) :
    expGenFun G z =
      if G.n₀ ≤ (NUPPT.inParam z).length then
        pairEncode (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z))) []
      else pairEncode dlDefaultIndex [] := rfl

/-- The index generator's string function is polynomial-time: the threshold test compares
the length of `1^n` with the constant `1^{n₀}` (`polyTimeComputable_lenLe`), then
`polyTimeComputable_ite` between the instance generator's output and a constant. -/
theorem expGenFun_poly {V : List Bool → Prop} (G : ExpGroupGen V) : PolyTimeComputable (expGenFun G) := by
  have hp : PolyTimeComputable fun z => [decide (G.n₀ ≤ (NUPPT.inParam z).length)] := by
    have h := polyTimeComputable_lenLe.comp
      (NUPPT.polyTimeComputable_inParam.pairEncode (polyTimeComputable_const (List.replicate G.n₀ true)))
    convert h using 1
    funext z
    simp [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hf : PolyTimeComputable fun z =>
      pairEncode (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z))) [] :=
    (G.gen.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
      NUPPT.polyTimeComputable_inParam (polyTimeComputable_const []) (polyTimeComputable_const [])
      NUPPT.polyTimeComputable_inCoins)).pairEncode (polyTimeComputable_const [])
  have h := polyTimeComputable_ite hp hf (polyTimeComputable_const (pairEncode dlDefaultIndex []))
  convert h using 1
  funext z
  simp only [expGenFun, decide_eq_true_eq]

/-- The index generator of the collection: `Gen(1^n) = ⟨i, []⟩` with `i` the output of the
instance generator (from `n₀` on; `dlDefaultIndex` below), same coins. -/
noncomputable def expGen {V : List Bool → Prop} (G : ExpGroupGen V) : NUPPT :=
  NUPPT.ofPolyTimeUniform (expGenFun_poly G) G.gen.coins

/-- The collection's generator has the coins of the instance generator:
`(expGen G).coins = G.gen.coins`. -/
theorem expGen_coins {V : List Bool → Prop} (G : ExpGroupGen V) :
    (expGen G).coins = G.gen.coins := by
  unfold expGen
  exact NUPPT.coins_ofPolyTimeUniform _ _

/-- The coin length of the collection's generator is the instance generator's:
`(expGen G).coinLen n = G.gen.coinLen n`. -/
theorem expGen_coinLen {V : List Bool → Prop} (G : ExpGroupGen V) (n : ℕ) :
    (expGen G).coinLen n = G.gen.coinLen n := by
  rw [NUPPT.coinLen_eq, NUPPT.coinLen_eq, expGen_coins]

/-- **The coins of the collection's generator are the instance generator's**: the published
equivalence `(expGen G).Coins n ≃ G.gen.Coins n` (`NUPPT.coinsCongr` along `expGen_coins`), the
interface between the averages over the collection's coins (`Collection.HardCore`,
`SampleClose`, `invProbAt`) and those over `G.gen`'s (`dlProb`, `FullLengthExcept`). -/
noncomputable def expGen_coinsEquiv {V : List Bool → Prop} (G : ExpGroupGen V) (n : ℕ) :
    (expGen G).Coins n ≃ G.gen.Coins n :=
  NUPPT.coinsCongr (expGen_coins G) n

/-- The coin equivalence keeps the coin string:
`List.ofFn (expGen_coinsEquiv G n r) = List.ofFn r`. -/
theorem expGen_coinsEquiv_ofFn {V : List Bool → Prop} (G : ExpGroupGen V) (n : ℕ)
    (r : (expGen G).Coins n) : List.ofFn (expGen_coinsEquiv G n r) = List.ofFn r :=
  NUPPT.coinsCongr_ofFn (expGen_coins G) n r

/-- **The coin equivalence carries the uniform distribution**: for `P` on `G.gen`'s coins,
`Pr_{r ← (expGen G).Coins n}[P (φ r)] = Pr_{r'}[P r']` with `φ = expGen_coinsEquiv G n`
(`uprob_comp_equiv`). -/
theorem expGen_coinsEquiv_uprob {V : List Bool → Prop} (G : ExpGroupGen V) (n : ℕ)
    (P : G.gen.Coins n → Prop) :
    uprob (fun r : (expGen G).Coins n => P (expGen_coinsEquiv G n r)) = uprob P :=
  uprob_comp_equiv _ P

/-- **The coin equivalence carries averages**: for `F` on `G.gen`'s coins,
`E_{r ← (expGen G).Coins n}[F (φ r)] = E_{r'}[F r']` with `φ = expGen_coinsEquiv G n`
(`HardcoreBit.uexp_comp_equiv`). -/
theorem expGen_coinsEquiv_uexp {V : List Bool → Prop} (G : ExpGroupGen V) (n : ℕ)
    (F : G.gen.Coins n → ℝ) :
    uexp (fun r : (expGen G).Coins n => F (expGen_coinsEquiv G n r)) = uexp F :=
  HardcoreBit.uexp_comp_equiv _ F

/-- The activation of the collection's generator: `⟨Gen(1^n; φ r), []⟩` for `n ≥ n₀`,
`⟨dlDefaultIndex, []⟩` below, with the coins read through `φ = expGen_coinsEquiv G n`. -/
theorem expGen_runAt {V : List Bool → Prop} (G : ExpGroupGen V) (n : ℕ) (r : (expGen G).Coins n) :
    (expGen G).runAt n [] r =
      if G.n₀ ≤ n then pairEncode (G.gen.runAt n [] (expGen_coinsEquiv G n r)) []
      else pairEncode dlDefaultIndex [] := by
  rw [NUPPT.runAt_eq, NUPPT.runAt_eq, expGen_coinsEquiv_ofFn, NUPPT.Uniform.runAtL_eq G.gen_uniform]
  unfold expGen
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp only [expGenFun, NUPPT.inParam_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq, NUPPT.layout_eq,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- **Rejection sampling of a number below `m`** from a coin list: `T` trials, trial `t`
reading the first `k` bits of the `t`-th block of `B` bits as a number `v`, accepted iff
`v < m`; `none` if every trial is rejected. With `k` the bit length of `m` the acceptance rate
is `m / 2^k ≥ 1/2` [PS10, Theorem 52.3, "it is easy to sample the domain `D_i`"]. -/
def sampleBelowL (m k B T : ℕ) (r : List Bool) : Option ℕ :=
  (List.range T).findSome? fun t =>
    if listToNat ((r.drop (t * B)).take k) < m then some (listToNat ((r.drop (t * B)).take k))
    else none

/-- `sampleBelowL` is block rejection sampling with the test `v < m`:
`sampleBelowL m k B T = rejectBlocksL (· < m) k B T` (the same blocks, the same test; gate 03f1
review, M2). -/
theorem sampleBelowL_eq_rejectBlocksL (m k B T : ℕ) :
    sampleBelowL m k B T = rejectBlocksL (· < m) k B T := by
  funext r
  rw [rejectBlocksL_eq]
  rfl

/-- A sampled value is below `m`. -/
theorem sampleBelowL_lt {m k B T : ℕ} {r : List Bool} {v : ℕ} (h : sampleBelowL m k B T r = some v) :
    v < m := by
  unfold sampleBelowL at h
  rw [List.findSome?_eq_some_iff] at h
  obtain ⟨_, t, _, _, ht, _⟩ := h
  split_ifs at ht with hc
  rw [Option.some.injEq] at ht
  exact ht ▸ hc

/-- **The rejection sampler is close to uniform** (D10; lemma C4 of the Chapter 2 inventory for
`sampleBelowL`): for `0 < m < 2^n`, `n` trials reading `k = Nat.size m` bits from each of `n`
blocks of `n` uniform coins, with the fallback `0`, output a number within statistical
distance `(1/2)^n` of the uniform number below `m`. The closeness fact behind
`expCollection_sampleClose` and the El Gamal samplers (`egUnit`, `egGenParts`, `egEncParts`,
`ddhExpo`).

**Proof sketch.** A corollary of `statClose_rejectBlocksL` (gate 03f1 review, M2; that lemma is
filled first, and this one is not filled a second time). With `k = Nat.size m`, `k ≤ n` by
`Nat.size_le` (`m < 2^n`), and `sampleBelowL m k n n = rejectBlocksL (· < m) k n n`
(`sampleBelowL_eq_rejectBlocksL`). `statClose_rejectBlocksL (· < m) k n n` with the default
`d = 0` (`0 < m`, `0 < 2^k`) gives closeness `(1 − Pr_{v < 2^k}[v < m])^n = (1 − m/2^k)^n` to
the uniform element of `{v : Fin (2^k) // v < m}`, and `(1 − m/2^k)^n ≤ (1/2)^n` since
`2^k ≤ 2m` (`Nat.lt_size_self` and the minimality of `Nat.size`: `m/2^k ≥ 1/2`). Transport the
target along the value-preserving bijection `{v : Fin (2^k) // v < m} ≃ Fin m`
(`StatClose.comp_equiv_right`) and weaken the bound (`StatClose.mono`). -/
theorem statClose_sampleBelowL {m n : ℕ} (hm : 0 < m) (hmn : m < 2 ^ n) :
    StatClose (fun b : Fin (n * n) → Bool => (sampleBelowL m (Nat.size m) n n (List.ofFn b)).getD 0)
      (fun x : Fin m => (x : ℕ)) ((1 / 2 : ℝ) ^ n) := by
  have hkn : Nat.size m ≤ n := Nat.size_le.2 hmn
  have hmk : m < 2 ^ Nat.size m := Nat.lt_size_self m
  -- `2^k ≤ 2m`: the top bit of `m` is bit `k − 1`
  have hk2 : 2 ^ Nat.size m ≤ 2 * m := two_pow_size_le_two_mul hm
  -- the block sampler with the test `v < m` and the default `0`
  have h := statClose_rejectBlocksL (· < m) (Nat.size m) n n hkn (d := 0) hm
    (Nat.pow_pos two_pos)
  -- the uniform element of `{v < 2^k | v < m}` is the uniform element of `Fin m`
  let e : Fin m ≃ {v : Fin (2 ^ Nat.size m) // (v : ℕ) < m} :=
    { toFun := fun x => ⟨⟨x.val, lt_trans x.2 hmk⟩, x.2⟩
      invFun := fun v => ⟨v.1.val, v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h' := h.comp_equiv_right e
  -- the acceptance probability is `m / 2^k ≥ 1/2`
  have hacc : uprob (fun v : Fin (2 ^ Nat.size m) => (v : ℕ) < m) = m / 2 ^ Nat.size m := by
    rw [← uprob_comp_equiv (bitsEquiv (Nat.size m)) (fun v : Fin (2 ^ Nat.size m) => (v : ℕ) < m)]
    simp only [bitsEquiv_val]
    exact uprob_bitsToNat_lt hmk.le
  rw [hacc] at h'
  have hpow : (1 - (m : ℝ) / 2 ^ Nat.size m) ^ n ≤ (1 / 2 : ℝ) ^ n := by
    rw [← uprob_rejectionSample_none m (Nat.size m) n hm hmk.le]
    exact uprob_rejectionSample_none_le_half_pow m (Nat.size m) n hm hmk.le hk2
  rw [sampleBelowL_eq_rejectBlocksL]
  exact h'.mono hpow

/-- The string function of the domain sampler on the raw layout `⟨⟨⟨1^n, i⟩, α⟩, r⟩`: a number
below the order `m` read from the index, by rejection over `n` trials of `n`-bit blocks
(reading the bit length of `m` from each block), written as a numeral of the index width;
the fallback `0` on failure. -/
def expSampleRaw (z : List Bool) : List Bool :=
  natToList (dlW (NUPPT.inArg z))
    ((sampleBelowL (dlM (NUPPT.inArg z)) (Nat.size (dlM (NUPPT.inArg z)))
      (NUPPT.inParam z).length (NUPPT.inParam z).length (NUPPT.inCoins z)).getD 0)

/-- The raw exponent sampler writes the result of `sampleBelowL m (Nat.size m) n n r`,
with fallback zero, at the width of the input index:
`expSampleRaw z = natToList (dlW i) ((sampleBelowL m (Nat.size m) n n r).getD 0)`, where
`i = NUPPT.inArg z`, `m = dlM i`, and `n` and `r` are the input parameter length and coins. -/
theorem expSampleRaw_eq (z : List Bool) :
    expSampleRaw z =
      natToList (dlW (NUPPT.inArg z))
        ((sampleBelowL (dlM (NUPPT.inArg z)) (Nat.size (dlM (NUPPT.inArg z)))
          (NUPPT.inParam z).length (NUPPT.inParam z).length (NUPPT.inCoins z)).getD 0) := rfl

/-! ### The comparison test of the domain sampler (helper of `polyTimeComputable_expSampleRaw`) -/

/-- The comparison test on a pair `⟨w, b⟩`: not `⟦w⟧ ≤ ⟦b⟧`, i.e. the trial value is below `⟦w⟧`. -/
private def dla_belowAcc (x : List Bool) : Bool :=
  !decide (listToNat (pairFstD x) ≤ listToNat (pairSndD x))

/-- The comparison test is polynomial-time (`ArithmeticFP.le_poly`, `polyTimeComputable_not`). -/
private theorem dla_belowAcc_poly (H : ArithmeticFP) :
    PolyTimeComputable fun x => [dla_belowAcc x] :=
  polyTimeComputable_not (H.le_poly polyTimeComputable_pairFstD polyTimeComputable_pairSndD)

/-- The comparison test decides `⟦b⟧ < ⟦w⟧` on `⟨w, b⟩`. -/
private theorem dla_belowAcc_spec (w b : List Bool) :
    dla_belowAcc (pairEncode w b) = decide (listToNat b < listToNat w) := by
  rw [dla_belowAcc, pairFstD_pairEncode, pairSndD_pairEncode, ← decide_not, decide_eq_decide,
    Nat.not_le]

/-! ### The domain sampler and the collection -/

/-- **The domain sampler is polynomial-time** [PS10, Theorem 52.3, "it is easy to sample the
domain `D_i`"] given the arithmetic bundle.

**Proof sketch.** The bit length `Nat.size m` is the length of the numeral of `m` with its
leading zeros stripped (`H.size`). The sampler is `sampleBelowL m k n n = rejectBlocksL (· < m)
k n n` (`sampleBelowL_eq_rejectBlocksL`), an instance of the block-rejection host H15
(`polyTimeComputable_rejectBlocksL`): the test `v < m` on `⟨⟦m⟧, v⟩` is `H.le`, negated; the
parameter word is the middle numeral `⟦m⟧` of the index, the width word `1^k = sizeStr ⟦m⟧`, and
`1^n` serves as both the block-length and the trial-count word. H15 returns a polynomial-time `g`
whose output is `[]` when every trial is rejected and otherwise has a tail reading as the accepted
value; so the tail of `g z` (`polyTimeComputable_tail`, `List.drop_one`) reads as the sampler's
value with the fallback `0` (the empty tail reads `0`). The output is the last `|p|` bits of
`⟦0⟧_{|p|} ++ t` for that tail `t`, with `⟦0⟧_{|p|} = ⟦p − p⟧_{|p|}` (`H.sub`,
`polyTimeComputable_pairDropPoly`, `PolyTimeComputable.append`): the `|p|`-bit numeral of the
value, also when it is `≥ 2^{|p|}` (`natToList_zero_append_drop`). -/
theorem polyTimeComputable_expSampleRaw (H : ArithmeticFP) : PolyTimeComputable expSampleRaw := by
  -- the middle numeral `⟦m⟧` of the index
  have hms : PolyTimeComputable fun z => pairFstD (pairSndD (NUPPT.inArg z)) :=
    polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg)
  -- host H15 with the test `v < ⟦m⟧`: width `|sizeStr ⟦m⟧| = Nat.size ⟦m⟧`, `n` blocks of `n` coins
  obtain ⟨g, hg, hs⟩ := polyTimeComputable_rejectBlocksL (fun a v => v < a) (dla_belowAcc_poly H)
    dla_belowAcc_spec hms (H.size.comp hms) NUPPT.polyTimeComputable_inParam
    NUPPT.polyTimeComputable_inParam NUPPT.polyTimeComputable_inCoins
  -- the accepted value's word (the payload's tail), `[]` on failure
  have hb : PolyTimeComputable fun z => (g z).tail :=
    (PolyTimeComputable.comp' polyTimeComputable_tail hg).congr fun z => List.drop_one
  -- the numeral of `0` at the index width, `⟦p − p⟧_{|p|}` (`H.sub`)
  have hp : PolyTimeComputable fun z => pairFstD (NUPPT.inArg z) :=
    polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg
  have hz := H.sub.comp (hp.pairEncode hp)
  -- width normalization: the last `|p|` bits of `⟦0⟧_{|p|} ++ payload`
  have hq := (polyTimeComputable_pairDropPoly .var).comp (hb.pairEncode (hz.append hb))
  refine hq.congr fun z => ?_
  simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var,
    subStr_pairEncode, Nat.sub_self]
  rw [natToList_zero_append_drop]
  unfold expSampleRaw dlW
  congr 1
  rw [dlM_eq, ← length_sizeStr, sampleBelowL_eq_rejectBlocksL,
    show rejectBlocksL (· < listToNat (pairFstD (pairSndD (NUPPT.inArg z))))
        (sizeStr (pairFstD (pairSndD (NUPPT.inArg z)))).length (NUPPT.inParam z).length
        (NUPPT.inParam z).length (NUPPT.inCoins z) =
      if g z = [] then none else some (listToNat (g z).tail) from (hs z).2]
  split_ifs with he
  · rw [he, List.tail_nil, listToNat_nil]
    rfl
  · rfl

/-- **The domain sampler** of the exponentiation collection: a uniform `NUPPT` with `n · n`
coins. -/
noncomputable def expSampler (H : ArithmeticFP) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_expSampleRaw H) (.mul .var .var)

/-- The activation of the domain sampler on the index `i`. -/
theorem expSampler_runAt (H : ArithmeticFP) (n : ℕ) (i : List Bool) (s : (expSampler H).Coins n) :
    (expSampler H).runAt n i s =
      natToList (dlW i) ((sampleBelowL (dlM i) (Nat.size (dlM i)) n n (List.ofFn s)).getD 0) := by
  rw [NUPPT.runAt_eq]
  unfold expSampler
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp [expSampleRaw, NUPPT.inArg_eq, NUPPT.inParam_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq]

/-- **The domain sampler's outputs decode and evaluate honestly** (the clause `sample_spec` of
`Collection`, [PS10, Definition 41.1 (2)]; repair of the run-3 audit, P3-1): at every parameter
the generated index is valid — `hV` with `G.valid` from `n₀` on, `expValid_dlDefaultIndex`
below (`expGen_runAt`) — so the domain is `Z_m` with `0 < m < p < 2^{dlW i}`
(`expOrd_of_valid`, `dlP_lt_two_pow`); the sampler outputs `natToList (dlW i) v` with `v < m`
(`expSampler_runAt`, `sampleBelowL_lt`, or the fallback `0`), which `expDec` reads back
(`length_natToList`, `listToNat_natToList`) as `x = (v : Z_m)` with `expEnc i x` the same
numeral (`ZMod.val_natCast`, `Nat.mod_eq_of_lt`); `expEval_spec` gives the evaluator clause.

**Proof sketch.** Case split on `G.n₀ ≤ n` in `expGen_runAt`, then the computation above. -/
theorem expSampler_spec {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (n : ℕ) (r : (expGen G).Coins n) (s : (expSampler H).Coins n) :
    ∃ x, expDec (pairFstD ((expGen G).runAt n [] r))
        ((expSampler H).runAt n (pairFstD ((expGen G).runAt n [] r)) s) = some x ∧
      expEval (pairEncode (pairFstD ((expGen G).runAt n [] r))
        ((expSampler H).runAt n (pairFstD ((expGen G).runAt n [] r)) s)) = expF _ x := by
  -- the generated index is valid at every parameter
  have hvalid : ExpValid (pairFstD ((expGen G).runAt n [] r)) := by
    rw [expGen_runAt]
    split_ifs with hn
    · rw [pairFstD_pairEncode]
      exact hV _ (G.valid n _ hn)
    · rw [pairFstD_pairEncode]
      exact expValid_dlDefaultIndex
  generalize pairFstD ((expGen G).runAt n [] r) = i at hvalid ⊢
  rw [expSampler_runAt]
  -- the sampled value `v` is below `m` (accepted, or the fallback `0 < m`)
  set v := (sampleBelowL (dlM i) (Nat.size (dlM i)) n n (List.ofFn s)).getD 0 with hvdef
  have hv : v < dlM i := by
    rcases hs : sampleBelowL (dlM i) (Nat.size (dlM i)) n n (List.ofFn s) with _ | w
    · rw [hvdef, hs, Option.getD_none]
      exact ((expValid_iff i).1 hvalid).2.1
    · rw [hvdef, hs, Option.getD_some]
      exact sampleBelowL_lt hs
  have hvo : v < expOrd i := (expOrd_of_valid hvalid).symm ▸ hv
  -- `x = (v : Z_m)` is encoded by the same numeral
  have henc : expEnc i ((v : ℕ) : ZMod (expOrd i)) = natToList (dlW i) v := by
    rw [expEnc_eq, ZMod.val_natCast, Nat.mod_eq_of_lt hvo]
  refine ⟨((v : ℕ) : ZMod (expOrd i)), ?_, ?_⟩
  · rw [← henc, expDec_expEnc]
  · rw [← henc, expEval_spec]

/-- **The exponentiation collection of an instance generator**: indices `⟨p, ⟨m, g⟩⟩`,
domains `D_i = Z_m` (valid indices; `Z_1` otherwise), `f_i(x) = g^x mod p`, the generator
`expGen G` (the instance generator from `n₀` on, `dlDefaultIndex` below), the sampler
`expSampler H` and the evaluator `expEval` (one modular exponentiation); the validity bridge
`hV` makes every generated index valid, so that the sampler's outputs decode
(`expSampler_spec`, run-3 audit P3-1). The collection `DL` of [PS10, Theorem 52.3] is the
safe-prime instance `dlCollection`; the full-group collection of [PS10, Lemma 84.1] is the
instance of `DiscreteLogHardcore`. -/
noncomputable def expCollection {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) : Collection where
  D i := ZMod (expOrd i)
  encD := expEnc
  decD := expDec
  decD_encD := expDec_expEnc
  encD_decD _ _ _ := expEnc_of_expDec
  f := expF
  gen := expGen G
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  sample := expSampler H
  sample_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  eval := expEval
  eval_poly := polyTimeComputable_expEval H
  eval_spec := expEval_spec
  sample_spec := expSampler_spec H G hV

/-- **The domain of the exponentiation collection is `Z_m`**: the published equivalence
`(expCollection H G hV).D i ≃ ZMod (expOrd i)` (the identity). It is the interface to the
domain: elements of `D i` are read through it (`expCollection_f`, `expCollection_encD`,
`expCollection_decD`), so no statement needs the collection to reduce at the type level, and
uniform statements over `D i` transport along it (`uprob_comp_equiv`,
`StatClose.comp_equiv_right`). -/
def expCollection_domEquiv {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (i : List Bool) :
    (expCollection H G hV).D i ≃ ZMod (expOrd i) :=
  Equiv.refl _

/-- **The domain equivalence carries the uniform distribution**: for `P` on `Z_m`,
`Pr_{x ← D i}[P (φ x)] = Pr_y[P y]` with `φ = expCollection_domEquiv H G hV i` (`uprob_comp_equiv`),
the form in which uniform statements over the domain are read. -/
theorem expCollection_domEquiv_uprob {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (i : List Bool)
    (P : ZMod (expOrd i) → Prop) :
    uprob (fun x : (expCollection H G hV).D i => P (expCollection_domEquiv H G hV i x)) = uprob P :=
  uprob_comp_equiv _ P

/-- The function of the exponentiation collection is `expF`, read through the domain
equivalence: `(expCollection H G hV).f i x = expF i (expCollection_domEquiv H G hV i x)`. -/
theorem expCollection_f {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (i : List Bool) (x : (expCollection H G hV).D i) :
    (expCollection H G hV).f i x = expF i (expCollection_domEquiv H G hV i x) := rfl

/-- The encoder of the exponentiation collection is `expEnc`, read through the domain
equivalence: `(expCollection H G hV).encD i x = expEnc i (expCollection_domEquiv H G hV i x)`. -/
theorem expCollection_encD {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (i : List Bool) (x : (expCollection H G hV).D i) :
    (expCollection H G hV).encD i x = expEnc i (expCollection_domEquiv H G hV i x) := rfl

/-- The decoder of the exponentiation collection is `expDec`, carried back along the domain
equivalence:
`(expCollection H G hV).decD i w = (expDec i w).map (expCollection_domEquiv H G hV i).symm`. -/
theorem expCollection_decD {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (i w : List Bool) :
    (expCollection H G hV).decD i w = (expDec i w).map (expCollection_domEquiv H G hV i).symm := by
  show expDec i w = _
  cases expDec i w <;> rfl

/-- The index generator of the exponentiation collection is `expGen G`. -/
theorem expCollection_gen {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) : (expCollection H G hV).gen = expGen G := rfl

/-- The domain sampler of the exponentiation collection is `expSampler H`. -/
theorem expCollection_sample {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) : (expCollection H G hV).sample = expSampler H := rfl

/-- The evaluator of the exponentiation collection is `expEval`. -/
theorem expCollection_eval {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) : (expCollection H G hV).eval = expEval := rfl

/-- **The coins of the exponentiation collection's generator are the instance generator's**:
the published equivalence `(expCollection H G hV).gen.Coins n ≃ G.gen.Coins n`
(`expGen_coinsEquiv`), through which the collection's averages are read as averages over
`G.gen`'s coins (`expCollection_coinsEquiv_uprob`, `expCollection_coinsEquiv_uexp`). -/
noncomputable def expCollection_coinsEquiv {V : List Bool → Prop} (H : ArithmeticFP)
    (G : ExpGroupGen V) (hV : ∀ i, V i → ExpValid i) (n : ℕ) :
    (expCollection H G hV).gen.Coins n ≃ G.gen.Coins n :=
  expGen_coinsEquiv G n

/-- The collection's coin equivalence carries the uniform distribution:
`Pr_r[P (φ r)] = Pr_{r'}[P r']` with `φ = expCollection_coinsEquiv H G hV n`. -/
theorem expCollection_coinsEquiv_uprob {V : List Bool → Prop} (H : ArithmeticFP)
    (G : ExpGroupGen V) (hV : ∀ i, V i → ExpValid i) (n : ℕ) (P : G.gen.Coins n → Prop) :
    uprob (fun r : (expCollection H G hV).gen.Coins n => P (expCollection_coinsEquiv H G hV n r)) =
      uprob P :=
  uprob_comp_equiv _ P

/-- The collection's coin equivalence carries averages:
`E_r[F (φ r)] = E_{r'}[F r']` with `φ = expCollection_coinsEquiv H G hV n`. -/
theorem expCollection_coinsEquiv_uexp {V : List Bool → Prop} (H : ArithmeticFP)
    (G : ExpGroupGen V) (hV : ∀ i, V i → ExpValid i) (n : ℕ) (F : G.gen.Coins n → ℝ) :
    uexp (fun r : (expCollection H G hV).gen.Coins n => F (expCollection_coinsEquiv H G hV n r)) =
      uexp F :=
  HardcoreBit.uexp_comp_equiv _ F

/-- The index generated by the exponentiation collection from `n₀` on is the instance
generator's output on the coins read through `expCollection_coinsEquiv`. -/
theorem expCollection_index {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (n : ℕ) (r : (expCollection H G hV).gen.Coins n)
    (hn : G.n₀ ≤ n) :
    (expCollection H G hV).index n r = G.gen.runAt n [] (expCollection_coinsEquiv H G hV n r) := by
  rw [Collection.index_eq]
  exact (congrArg pairFstD (expGen_runAt G n r)).trans (by rw [if_pos hn, pairFstD_pairEncode]; rfl)

/-- The index generated by the exponentiation collection below `n₀` is the default index. -/
theorem expCollection_index_of_lt {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (n : ℕ) (r : (expCollection H G hV).gen.Coins n)
    (hn : n < G.n₀) :
    (expCollection H G hV).index n r = dlDefaultIndex := by
  rw [Collection.index_eq]
  exact (congrArg pairFstD (expGen_runAt G n r)).trans
    (by rw [if_neg (not_le.mpr hn), pairFstD_pairEncode])

/-- The domain of the exponentiation collection at an index is `Z_{expOrd i}`. -/
theorem expCollection_D {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (i : List Bool) :
    (expCollection H G hV).D i = ZMod (expOrd i) := rfl

/-- **The decoded domain sampler is `(1/2)^n`-close to uniform on `Z_m`** at a valid index of
width `n`: `statClose_sampleBelowL` on the sampler's `n · n` coins (read through
`NUPPT.coinsEquivPoly`), mapped through the decoder, which reads the numeral back exactly.

**Proof sketch.** At a valid index of width `n`, `0 < m` and `m < p < 2^n`. Identify the
sampler's coins with `Fin (n · n) → Bool` (`NUPPT.coinsEquivPoly`, `finCongr`; the coin list is
unchanged, `NUPPT.coinsEquivPoly_ofFn`) and `Z_m` with `Fin m` by the value map. Then
`statClose_sampleBelowL`, moved along the coin identification (`StatClose.comp_equiv_left`),
mapped through `v ↦ expDec i ⟦v⟧_n` (`StatClose.map`) and moved along `Z_m ≃ Fin m`
(`StatClose.comp_equiv_right`), is the claim: its left side is the decoded sampler output
(`expSampler_runAt`), and on its right side `expDec i ⟦y.val⟧_n = some y` (`expEnc_eq`,
`expDec_expEnc`). -/
private theorem dla_statClose_expDec (H : ArithmeticFP) {n : ℕ} {i : List Bool} (hv : ExpValid i)
    (hw : dlW i = n) :
    StatClose (fun s : (expSampler H).Coins n => expDec i ((expSampler H).runAt n i s))
      (fun x : ZMod (expOrd i) => some x) ((1 / 2 : ℝ) ^ n) := by
  have hv' := (expValid_iff i).1 hv
  have hm : 0 < dlM i := hv'.2.1
  have hmn : dlM i < 2 ^ n := hw ▸ hv'.2.2.1.trans (dlP_lt_two_pow i)
  have hord : expOrd i = dlM i := expOrd_of_valid hv
  -- the sampler's coins are `n · n` bits
  have hcoins : (expSampler H).coins = .mul .var .var := by
    unfold expSampler
    exact NUPPT.coins_ofPolyTimeUniform _ _
  have hlen : (PolyExpr.mul .var .var).eval n = n * n := by
    rw [PolyExpr.eval_mul, PolyExpr.eval_var]
  let e : (expSampler H).Coins n ≃ (Fin (n * n) → Bool) :=
    (NUPPT.coinsEquivPoly hcoins n).trans (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool))
  have hofn : ∀ s, List.ofFn (e s) = List.ofFn s := by
    intro s
    rw [← NUPPT.coinsEquivPoly_ofFn hcoins n s]
    exact (List.ofFn_congr hlen.symm _).trans rfl
  -- the residues below `m` are the elements of `Z_m`
  let e2 : ZMod (expOrd i) ≃ Fin (dlM i) :=
    { toFun := fun y => ⟨y.val, lt_of_lt_of_eq (ZMod.val_lt y) hord⟩
      invFun := fun x => ((x : ℕ) : ZMod (expOrd i))
      left_inv := fun y => ZMod.natCast_zmod_val y
      right_inv := fun x => Fin.ext (by
        show ((x : ℕ) : ZMod (expOrd i)).val = x
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_of_lt_of_eq x.2 hord.symm)]) }
  let g : ℕ → Option (ZMod (expOrd i)) := fun v => expDec i (natToList (dlW i) v)
  have h := (((statClose_sampleBelowL hm hmn).comp_equiv_left e).map g).comp_equiv_right e2
  have hX : (fun s : (expSampler H).Coins n =>
      g ((sampleBelowL (dlM i) (Nat.size (dlM i)) n n (List.ofFn (e s))).getD 0)) =
      fun s => expDec i ((expSampler H).runAt n i s) := by
    funext s
    rw [hofn, expSampler_runAt]
  have hY : (fun y : ZMod (expOrd i) => g ((e2 y : Fin (dlM i)) : ℕ)) = fun y => some y := by
    funext y
    show expDec i (natToList (dlW i) y.val) = some y
    rw [← expEnc_eq, expDec_expEnc]
  rw [hX, hY] at h
  exact h

/-- **The domain sampler is close to uniform** [PS10, Theorem 52.3, "it is easy to sample the
domain `D_i`"]: the decoded output of `expSampler` at a generated index is within a
negligible statistical distance of the uniform element of `Z_m`.

**Proof sketch.** Take `δ n := 1` for `n < n₀` and `δ n := (1/2)^n` for `n ≥ n₀`. At a
generated index `i` (`expCollection_index`, valid by `hV ∘ G.valid`, well formed with
`dlW i = n`) the sampler outputs `natToList n (sampleBelowL m k n n r).getD 0` with
`m = dlM i = expOrd i` (`expSampler_runAt`, `expOrd_of_valid`) and `k = Nat.size m ≤ n`
(`Nat.size_le`, `m < p < 2^n`): `n` trials each reading `k` uniform bits of a block of the
coins (`uprob_comp_equiv` on the block decomposition `NumberTheory.chunk`), accepted iff the
value is below `m`; `sampleBelowL` is `firstHit (· < m)` of the numbers read from the blocks
(`List.findSome?` over `List.range`), so `statClose_sampleBelowL` (`statClose_firstHit` on
`Fin (2^k)` transported along `bitsEquiv`) gives closeness `(1 - m/2^k)^n ≤ (1/2)^n`
(`Nat.lt_size_self`: `m/2^k ≥ 1/2`), and the decoder `expDec` reads the numeral back exactly
(`listToNat_natToList`, `StatClose.map`, `ZMod.natCast_zmod_val`). Negligibility by
`negligible_two_pow_neg` and `Negligible.mono`. -/
theorem expCollection_sampleClose {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) :
    ∃ δ : ℕ → ℝ, Negligible δ ∧ (expCollection H G hV).SampleClose δ := by
  refine ⟨fun n => if n < G.n₀ then 1 else (1 / 2 : ℝ) ^ n, ?_, ?_⟩
  · refine negligible_two_pow_neg.mono ⟨G.n₀, fun n hn => ?_⟩
    rw [if_neg (not_lt.2 hn), one_div]
  · rw [Collection.sampleClose_iff]
    intro n r
    by_cases hn : n < G.n₀
    · rw [if_pos hn]
      exact statClose_one _ _
    rw [if_neg hn]
    have hn' : G.n₀ ≤ n := not_lt.1 hn
    -- the generated index is valid and of width `n`
    have hidx := expCollection_index H G hV n r hn'
    have hv : ExpValid ((expCollection H G hV).index n r) := hidx ▸ hV _ (G.valid n _ hn')
    have hw : dlW ((expCollection H G hV).index n r) = n :=
      hidx ▸ (G.wellFormed n _ hn').dlW_eq
    generalize (expCollection H G hV).index n r = j at hv hw ⊢
    rw [expCollection_sample]
    simp only [expCollection_decD]
    have h := ((dla_statClose_expDec H hv hw).map
      (Option.map (expCollection_domEquiv H G hV j).symm)).comp_equiv_right
        (expCollection_domEquiv H G hV j)
    have hY : (fun x : (expCollection H G hV).D j =>
        Option.map (expCollection_domEquiv H G hV j).symm (some (expCollection_domEquiv H G hV j x))) =
        fun x => some x := by
      funext x
      rw [Option.map_some, Equiv.symm_apply_apply]
    rw [hY] at h
    exact h

/-- **An inverter's success is a discrete-log success** at a valid index of width `n`: if `A`'s
answer `w` decodes under `expDec` to a preimage of `g^y`, then `w` is the `n`-bit numeral of `y`
(`expF_injective`). -/
private theorem dla_dl_of_inv {i w : List Bool} {n : ℕ} (hv : ExpValid i) (hw : dlW i = n)
    {y : ZMod (expOrd i)} (h : ∃ x', expDec i w = some x' ∧ expF i x' = expF i y) :
    ∃ x : Fin n → Bool, decodeFin n w = some x ∧ bitsToNat x = y.val := by
  obtain ⟨x', hdec, hf⟩ := h
  obtain rfl := expF_injective hv hf
  rw [expDec] at hdec
  split_ifs at hdec with hc
  obtain ⟨hlen, hlt⟩ := hc
  rw [hw] at hlen
  rw [decodeFin_eq, dif_pos hlen]
  refine ⟨_, rfl, ?_⟩
  rw [bitsToNat_eq_listToNat, ← List.ofFn_congr hlen w.get, List.ofFn_get, ← Option.some.inj hdec,
    ZMod.val_natCast, Nat.mod_eq_of_lt hlt]

/-- **Inverting the collection is the discrete-log experiment** [PS10, proof of Theorem 52.3,
"the discrete log assumption implies that `f_{p,g}` is hard to invert"]: for `n ≥ n₀`, the
inversion probability of `A` against the exponentiation collection is at most its
discrete-log probability (the same machine, no reduction needed).

**Proof sketch.** Unfold both averages over the generator's coins (`OneWay.uexp_mono`) and
fix `r`; the index `i = Gen(1^n; r)` is valid and well formed (`hV`, `G.valid`,
`G.wellFormed`, `dlW i = n`). If `A`'s answer `w` decodes under `expDec` to `x'` with
`expF i x' = expF i x`, then `x' = x` (`expF_injective`), `w.length = n` and
`listToNat w = x.val`, so `decodeFin n w = some x''` with `bitsToNat x'' = listToNat w = x.val`
(`decodeFin`, `bitsToNat_eq_listToNat`, `List.ofFn_get`); `uprob_mono` with the coin types
identified through `expCollection_coinsEquiv` (`expCollection_index`,
`expCollection_coinsEquiv_uexp`). -/
theorem expCollection_invProbAt_le {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (A : NUPPT) {n : ℕ} (hn : G.n₀ ≤ n) :
    (expCollection H G hV).invProbAt A n ≤ G.dlProb A n := by
  rw [Collection.invProbAt_eq, ExpGroupGen.dlProb_eq]
  refine le_of_le_of_eq (OneWay.uexp_mono fun r => ?_) (expCollection_coinsEquiv_uexp H G hV n _)
  have hv : ExpValid (G.gen.runAt n [] (expCollection_coinsEquiv H G hV n r)) := hV _ (G.valid n _ hn)
  have hw : dlW (G.gen.runAt n [] (expCollection_coinsEquiv H G hV n r)) = n :=
    (G.wellFormed n _ hn).dlW_eq
  rw [expCollection_index H G hV n r hn]
  generalize G.gen.runAt n [] (expCollection_coinsEquiv H G hV n r) = i at hv hw ⊢
  -- read the domain `D i` as `Z_m` (`expCollection_domEquiv`) and compare pointwise
  rw [← uprob_comp_equiv
    (Equiv.prodCongr (expCollection_domEquiv H G hV i).symm (Equiv.refl (A.Coins n)))]
  refine uprob_mono fun z hz => ?_
  obtain ⟨x', hdec, hf⟩ := hz
  simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply,
    expCollection_f, expCollection_decD, Equiv.apply_symm_apply] at hdec hf
  obtain ⟨x'', hx'', rfl⟩ := Option.map_eq_some_iff.1 hdec
  rw [Equiv.apply_symm_apply] at hf
  exact dla_dl_of_inv hv hw ⟨x'', hx'', hf⟩

/-- **The exponentiation collection is one-way under discrete-log hardness** (the generic
form of [PS10, Theorem 52.3]).

**Proof sketch.** The sampling clause is `expCollection_sampleClose H G hV`. For the
hardness clause fix `A`: `expCollection_invProbAt_le H G hV A` bounds the inversion
probability by `G.dlProb A n` for `n ≥ n₀`, negligible by `hG A`; conclude by
`Negligible.mono` (`Collection.invProbAt_nonneg`, threshold `n₀`). -/
theorem expCollection_oneWay {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (hG : G.DLHard) : (expCollection H G hV).OneWay := by
  refine ⟨expCollection_sampleClose H G hV, fun A => ?_⟩
  refine ((ExpGroupGen.dlHard_iff G).1 hG A).mono ⟨G.n₀, fun n hn => ?_⟩
  rw [abs_of_nonneg (Collection.invProbAt_nonneg _ A n), abs_of_nonneg (G.dlProb_nonneg A n)]
  exact expCollection_invProbAt_le H G hV A hn

/-! ## Safe primes: the discrete-log assumption and the collection `DL` -/

/-- A **safe-prime instance** `⟨p, ⟨q, g⟩⟩`: a valid index whose order `q` is prime with
`p = 2q + 1`, so that `g` generates the subgroup of squares `G_q ≤ Z_p^*` of prime order `q`
[PS10, Assumption 52.2 and p. 52, "the subgroup of squares … has order `q` which is prime"]. -/
def SafePrimeValid (i : List Bool) : Prop :=
  ExpValid i ∧ (dlM i).Prime ∧ dlP i = 2 * dlM i + 1

/-- Unfolding `SafePrimeValid`: `i` is a safe-prime instance iff it is valid, `m` is prime and
`p = 2m + 1`. -/
theorem safePrimeValid_iff (i : List Bool) :
    SafePrimeValid i ↔ ExpValid i ∧ (dlM i).Prime ∧ dlP i = 2 * dlM i + 1 := Iff.rfl

/-- A safe-prime instance is a valid instance. -/
theorem SafePrimeValid.expValid {i : List Bool} (h : SafePrimeValid i) : ExpValid i := h.1

/-- **Safe-prime instance generators**: PPTs `Gen(1^n) = ⟨p, ⟨q, g⟩⟩` outputting safe primes
`p = 2q + 1` of length `n` with a generator `g` of the order-`q` subgroup of squares — the
formal "`q ← Π_n; g ← Gen_{G_q}`" of [PS10, Assumption 52.2] and the "`p ← Π̃_n; y ← Gen_q`"
of [PS10, Assumption 105.1]. -/
abbrev SafePrimeGen : Type 1 := ExpGroupGen SafePrimeValid

/-- **The discrete-log assumption** [PS10, Assumption 52.2] relative to a safe-prime instance
generator `G`: for every non-uniform PPT `A`,
`Pr[(p, q, g) ← Gen(1^n); x ← Z_q : A(1^n, ⟨⟨p, ⟨q, g⟩⟩, g^x⟩) = x]` is negligible.

**Deviation:** `A` receives `1^n` and the instance `(p, q, g)` (the text's `A(g^x)`, source
error 8); the group is the subgroup of squares of `Z_p^*` for a safe prime; the instance law
is the generator's (the text's ideal `q ← Π_n; g ← Gen_{G_q}` has no known efficient
sampler, p. 52); "`< ε(n)`" is "negligible" (module docstring). -/
def DLAssumption (G : SafePrimeGen) : Prop := G.DLHard

/-- Unfolding: the discrete-log assumption is the negligibility of every `dlProb`. -/
theorem dlAssumption_iff (G : SafePrimeGen) :
    DLAssumption G ↔ ∀ A : NUPPT, Negligible fun n => G.dlProb A n := Iff.rfl

/-- **The collection `DL`** [PS10, Theorem 52.3]: indices `(q, g)` (with `p`), domains
`D_i = Z_q`, ranges `R_i = G_q`, `f_{q,g}(x) = g^x`, with the instance generator `G` as
`Gen`, the rejection sampler of `Z_q` and the modular-exponentiation evaluator.

**Deviation:** the text's `R_i = G_p`, `f_{p,g}` are read as `G_q`, `f_{q,g}` (source
error 8) and the parameter `k` as `n`; the range `G_q` is encoded as residues modulo `p`
(`expF`). -/
noncomputable def dlCollection (H : ArithmeticFP) (G : SafePrimeGen) : Collection :=
  expCollection H G fun _ h => h.expValid

/-- **The domain of `DL` is `Z_q`**: the published equivalence
`(dlCollection H G).D i ≃ ZMod (expOrd i)` (the identity), the interface to the domain
(`dlCollection_f`, `dlCollection_encD`, `dlCollection_decD`; see `expCollection_domEquiv`). -/
def dlCollection_domEquiv (H : ArithmeticFP) (G : SafePrimeGen) (i : List Bool) :
    (dlCollection H G).D i ≃ ZMod (expOrd i) :=
  expCollection_domEquiv H G (fun _ h => h.expValid) i

/-- **The domain equivalence carries the uniform distribution**: for `P` on `Z_q`,
`Pr_{x ← D i}[P (φ x)] = Pr_y[P y]` with `φ = dlCollection_domEquiv H G i` (`uprob_comp_equiv`),
the form in which uniform statements over the domain are read. -/
theorem dlCollection_domEquiv_uprob (H : ArithmeticFP) (G : SafePrimeGen) (i : List Bool)
    (P : ZMod (expOrd i) → Prop) :
    uprob (fun x : (dlCollection H G).D i => P (dlCollection_domEquiv H G i x)) = uprob P :=
  uprob_comp_equiv _ P

/-- The function of `DL` is `expF`, read through the domain equivalence:
`(dlCollection H G).f i x = expF i (dlCollection_domEquiv H G i x)`. -/
theorem dlCollection_f (H : ArithmeticFP) (G : SafePrimeGen) (i : List Bool)
    (x : (dlCollection H G).D i) :
    (dlCollection H G).f i x = expF i (dlCollection_domEquiv H G i x) :=
  expCollection_f H G (fun _ h => h.expValid) i x

/-- The encoder of `DL` is `expEnc`, read through the domain equivalence:
`(dlCollection H G).encD i x = expEnc i (dlCollection_domEquiv H G i x)`. -/
theorem dlCollection_encD (H : ArithmeticFP) (G : SafePrimeGen) (i : List Bool)
    (x : (dlCollection H G).D i) :
    (dlCollection H G).encD i x = expEnc i (dlCollection_domEquiv H G i x) :=
  expCollection_encD H G (fun _ h => h.expValid) i x

/-- The decoder of `DL` is `expDec`, carried back along the domain equivalence:
`(dlCollection H G).decD i w = (expDec i w).map (dlCollection_domEquiv H G i).symm`. -/
theorem dlCollection_decD (H : ArithmeticFP) (G : SafePrimeGen) (i w : List Bool) :
    (dlCollection H G).decD i w = (expDec i w).map (dlCollection_domEquiv H G i).symm :=
  expCollection_decD H G (fun _ h => h.expValid) i w

/-- The index generator of `DL` is `expGen G`. -/
theorem dlCollection_gen (H : ArithmeticFP) (G : SafePrimeGen) :
    (dlCollection H G).gen = expGen G :=
  expCollection_gen H G (fun _ h => h.expValid)

/-- The domain sampler of `DL` is `expSampler H`. -/
theorem dlCollection_sample (H : ArithmeticFP) (G : SafePrimeGen) :
    (dlCollection H G).sample = expSampler H :=
  expCollection_sample H G (fun _ h => h.expValid)

/-- The evaluator of `DL` is `expEval`. -/
theorem dlCollection_eval (H : ArithmeticFP) (G : SafePrimeGen) :
    (dlCollection H G).eval = expEval :=
  expCollection_eval H G (fun _ h => h.expValid)

/-- **The coins of `DL`'s generator are the instance generator's**: the published equivalence
`(dlCollection H G).gen.Coins n ≃ G.gen.Coins n` (`expCollection_coinsEquiv`). -/
noncomputable def dlCollection_coinsEquiv (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ) :
    (dlCollection H G).gen.Coins n ≃ G.gen.Coins n :=
  expCollection_coinsEquiv H G (fun _ h => h.expValid) n

/-- The coin equivalence keeps the coin string:
`List.ofFn (dlCollection_coinsEquiv H G n r) = List.ofFn r`. -/
theorem dlCollection_coinsEquiv_ofFn (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ)
    (r : (dlCollection H G).gen.Coins n) :
    List.ofFn (dlCollection_coinsEquiv H G n r) = List.ofFn r :=
  expGen_coinsEquiv_ofFn G n r

/-- The index generated by `DL` from `n₀` on is the instance generator's output `⟨p, ⟨q, g⟩⟩`
on the coins read through `dlCollection_coinsEquiv`. -/
theorem dlCollection_index (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ)
    (r : (dlCollection H G).gen.Coins n) (hn : G.n₀ ≤ n) :
    (dlCollection H G).index n r = G.gen.runAt n [] (dlCollection_coinsEquiv H G n r) :=
  expCollection_index H G _ n r hn

/-- **Theorem 52.3** [PS10, Theorem 52.3]: under the discrete-log assumption (and the
arithmetic hypotheses), `DL` is a collection of one-way functions.

**Deviation:** see `dlCollection` and the module docstring (instance generator, safe primes,
rejection-sampled domain).

**Proof sketch.** `expCollection_oneWay` with `hV := SafePrimeValid.expValid`: the sampler
is close to uniform (`expCollection_sampleClose`) and inverting the collection is the
discrete-log experiment (`expCollection_invProbAt_le`), negligible by `hDL`. -/
theorem dlCollection_oneWay (H : ArithmeticFP) (G : SafePrimeGen) (hDL : DLAssumption G) :
    (dlCollection H G).OneWay :=
  expCollection_oneWay H G (fun _ h => h.expValid) hDL

end TCSlib.Cryptography.Candidates

## ===== TCSlib/Cryptography/Hashing.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Hashing.CollisionResistant
import TCSlib.Cryptography.Hashing.FromDiscreteLog
import TCSlib.Cryptography.Hashing.FromDiscreteLog.Algebra
import TCSlib.Cryptography.Hashing.FromDiscreteLog.Coins
import TCSlib.Cryptography.Hashing.FromDiscreteLog.Encoding
import TCSlib.Cryptography.Hashing.FromDiscreteLog.Probability
import TCSlib.Cryptography.Hashing.FromDiscreteLog.Reduction
import TCSlib.Cryptography.Hashing.FromDiscreteLog.Sampling
import TCSlib.Cryptography.Hashing.SIS

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Cryptographic hashing constructions

## Contents

* `CollisionResistant` — the machine-level hash family interface, compression, and collision game.
* `FromDiscreteLog` — the discrete-log hash family, efficient evaluator and security statement.
* `SIS` — binary matrix hashing, its encoded evaluator, and the negligible raw-collision bound
  for the dyadic profile under the independent SIS assumption [Pei16, §5.1].

`Authentication.Signatures.HashAndSign` consumes the hash interface to extend a signature
scheme's message space. The hash domain and digest width conditions are stated there.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 140.1, Protocol 142.2 and Theorem 142.3.
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016.
-/
