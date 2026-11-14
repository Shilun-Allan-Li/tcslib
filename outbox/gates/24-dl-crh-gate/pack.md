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
