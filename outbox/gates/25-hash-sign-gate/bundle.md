## ===== briefs/pass-shelat-ch5-8/gates/25-hash-sign/pack.md =====

# Gate 25 · Hash-and-sign is one-time secure (`hash-sign`, Theorem 144.1)

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #308](https://github.com/Shilun-Allan-Li/tcslib/pull/308) at
  `4f0280c85fae8730ca0dfad980b41749452980fa` (branch `land/pass-shelat-hash-sign`, tree
  `4485fafd1abee34129c24c8aa76f4325230eb442`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `dee0de32ee33d7188afe97bdc3089fac68412057` (the merge base).
  - The fill was issued on `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`, the merge of #299.
  - Between the issue base and the PR base, two merged PRs change non-record files: #303 (merge
    `d82e9a50414c6be160bcb3bd63ffdeb95e41e21c`, the four ext-nosrc files under `Randomness/`) and #305 (merge
    `8d0db40144102b847921b51ee2d1ebfd2994836d`, `scripts/campaign_style_lint.py` only). Neither touches a file of this PR.
    Every other commit in that range, and every commit from the PR base to the current records tip, touches records
    only (`PassShelatChapter5-8Plan.md` and `briefs/`). The PR diff equals the unit's diff from the issue base.
- **Commits:** 7.
  - The Codex worker's 4 patches (job `hash-sign`), applied with `git am` and rebased without conflict, author (Codex)
    kept: `e6bcdd62a3fd200fc1cb594c89e8f469471ae26a` (the collision reduction and fixed-tape coupling),
    `f92c2f7297daa46403734dacee5f54129349a089` (the forwarding reduction's game equality),
    `dcf726fef324664d2f7033657d3a7227cfeb3285` (one-time security with sealed-width reductions) and
    `b7e4249b0af1c6b4fcaeef99e71bf1ac452b4aaf` (collision padding and split words through published equations).
  - Landing edit **LE-width** `189f1c21092b287b39ff65b8658f2ba41f249418`: whitespace only, re-wrapping the one
    101-character statement line of `expect_hashAndSign_sign`.
  - Landing edit **LE-facade** `6056f3ed7774d308846f7293e2c6ed992ce9d4f8`: order only, swapping the imports of
    `OneQuerySampling` and `OneQuery` so the eight helpers are in alphabetical order.
  - Landing edit **LE-doc** `4f0280c85fae8730ca0dfad980b41749452980fa` (the head): 109 formula docstrings and 1 proof
    sketch; docstrings only.
- **Scope:** a **proof audit**. The job proves the admitted `Authentication.hashAndSign_oneTimeSecure` [PS10, Theorem
  144.1]: hash-and-sign of a one-time secure signature scheme with a collision-resistant hash family is one-time
  secure. Its statement passed Gate 06 and is frozen.
- **Brief:** `fills/hash-sign/issued-r1/brief.md` on the records branch (SHA-256 `d4ddbdb3…`; exchange pack
  `b436d19a`): three checkpoints following the docstring sketch, the owned file plus the helper directory
  `HashAndSign/` only, `Lamport.lean` (owned by the parallel `lamport` fill) and `Games/Efficiency.lean` frozen, no
  dependence on Lamport's proof, the duplication rule with "overlap" disclosures, and the evidence-completeness rule.

## What changed

All paths are under `TCSlib/Cryptography/Authentication/`; `HS/` is `Signatures/HashAndSign/`. The PR touches 10 Lean
files: 2 modified and 8 new (2247 insertions, 7 deletions).

| File | Status | Lines |
|---|---|---:|
| `Signatures/HashAndSign.lean` | owned, modified | 417 → 660 |
| `HS/CodecReaders.lean` | helper, new | 110 |
| `HS/CollisionGame.lean` | helper, new | 180 |
| `HS/CollisionHandler.lean` | helper, new | 541 |
| `HS/FixedGame.lean` | helper, new | 199 |
| `HS/ForwardGame.lean` | helper, new | 445 |
| `HS/ForwardHandler.lean` | helper, new | 382 |
| `HS/OneQuery.lean` | helper, new | 65 |
| `HS/OneQuerySampling.lean` | helper, new | 67 |
| `../Authentication.lean` | frozen facade, approved imports | 52 → 60 |

The proof follows [PS10, Theorem 144.1] (REPORT § Proof, review § Content):
1. **Common transcript:** the forge game equals a common logged transcript with independent signature-key, hash-index,
   adversary and signing tapes (`hashAndSign_forge_eq_common`); the one-query sampling law draws the possible signing
   tape before the run without changing its law (`OneQuerySampling`).
2. **Two cases** (`hashAndSign_success_cases`): a success is either a collision or a forward success.
   - **Collision:** adversary B, built with T1 (`Games.exists_handlerMachine`), remembers the queried message and
     outputs it with the final message; freshness gives distinctness and `hdom` gives domain membership.
     `exists_collisionGame_bound` bounds the averaged event by B's CRH collision probability.
   - **Forward:** adversary C, built with T2 (`exists_interactiveHandlerMachine`, `perCall = 1`, `finCall = 0`), is an
     original-scheme forger; `exists_forwardGame` is an exact equality of the original forge game and the
     common-transcript event.
3. **Conclusion:** a union bound, then `Negligible.add`.

The edge cases are no query (the forward branch), `m′ = m` (excluded by freshness), the `hlen` casts (through
`Fin.cast`), empty logs, zero widths, malformed or noncanonical words and signatures, and timeouts
(`forgerCodec_eq_bitCodec`).

**Statements:** decls2 from the issue base to the head gives 110 ADDED, 0 CHANGED, 0 REMOVED. All 32 pre-existing
declaration headers are byte-identical, the target's included; only the target's body and sketch changed.

## Rulings and records in force (2026-11-14)

1. **The eight facade imports are an approved scope extension (Seyoon).** The brief froze every file outside the owned
   file and helper directory. The required lint flagged the facade `Authentication.lean` for not importing the eight
   new helpers. The worker put the exact patch and the eight lint lines to Seyoon in its chat, and Seyoon answered
   "Authorize the eight imports" (`worker/inputs/session-overrides.md`); the decision log confirms exactly eight. Against
   the base, the facade diff is exactly the eight import lines of the worker's
   `evidence/escalations/proposed-authentication-imports.patch` (`worker/escalations/`), as a set.
   - **LE-facade** (the maintainer's) only re-orders two of them, so the helpers follow `Signatures.HashAndSign` in
     alphabetical order, as in `Randomness.lean` and `PrivateKey.lean`. The file's lines are the same multiset before
     and after.
   - **Not a finding.** What you can raise: any facade change beyond those eight lines, a cycle, or a change to what the
     facade's other imports export.
2. **Rule 10: a `CoeFun`/`Coe` instance whose body is a structure projection is notation (Seyoon).** This is
   `FinDist`'s `⟨FinDist.prob⟩`. The coe-variant seals are canonical, and the strict variant is still run with its
   differences attributed. **For this unit the two variants agree:** seals A and B pass for all 10 files at the head and
   for the owned file and the facade at the base, with 0 failing declarations in either variant.
3. **The facade-completeness lint fix, #305 (Seyoon's ruling to fix the bug by a PR on our branch; merged by
   Seyoon).** The Cryptography baseline is now **92 FAIL / 102 WARN**. At the LE-doc head the lint gives 92 / 102 with
   the same FAIL and WARN lines as the records tip (`ledoc-evidence.zip`), and the eight helpers raise no facade FAIL.
   Under the old lint the count was 216 / 102 at the base and at the head, with identical lines.
4. **The landing edits are the maintainer's** (the ext-nosrc, cca2-ett and dl-crh precedents; decision log rows of
   2026-11-14).
   - **LE-width** is whitespace only.
   - **LE-facade** is order only (ruling 1).
   - **LE-doc** is docstrings only: its 109 hunks all lie inside doc comments; with doc comments blanked, all 9 changed
     files are byte-identical (`Authentication.lean` is untouched by it); all 142 declaration headers are
     byte-identical; decls2 against the LE-facade head is empty. The target's docstring is untouched: it keeps its
     book-statement first line and its `[PS10, Theorem 144.1]` tag.

## What is frozen

- **The target's statement** (quoted in the brief), the 31 other pre-existing declarations of `HashAndSign.lean`, the
  statement prose and the global simp attributes.
- **Every file outside** `Signatures/HashAndSign.lean` and `Signatures/HashAndSign/`, except the eight approved
  facade imports. That includes `Signatures/Lamport.lean`, `Signatures/Defs.lean`, `Hashing/CollisionResistant.lean`,
  `Games/Forwarding.lean` and `Games/Efficiency.lean`.
- **The landing edits:** LE-width changes whitespace only, LE-facade import order only, and LE-doc docstrings only.

## Questions for the audit

**1. Correctness against [PS10, Theorem 144.1]**
- Does the proof establish the frozen statement for every forger, under `hlen`, `hdom`, `hH` and `hS`, including no
  query, `m′ = m`, the `hlen` casts, malformed words and signatures, and timeouts?
- Is the common transcript equal in law to the forge game of `hashAndSign H S hlen`, and does drawing the signing tape
  before the run preserve that law?
- Collision case: is B a legitimate CRH collision finder (uniform, polynomial-time, T1's handler bounds), and is every
  "equal hash, fresh message" success a collision of distinct domain points?
- Forward case: is C a legitimate one-time forger against `S` (T2 with `perCall = 1`, `finCall = 0`), and is
  `exists_forwardGame` an exact equality, with freshness of the final hash among the forwarded queries?
- Does the proof avoid any dependence on `lamport_oneTimeSecure` (still admitted at this base)?
- Does the edited target sketch describe the delivered proof?

**2. Frozen-statement integrity and the approved exception (ruling 1)**
- Are the target's header and the other 31 pre-existing declarations byte-identical (`landing/header-bytes.txt`,
  `landing/decls2.tsv`, `landing/touched.tsv`)?
- Is the `Authentication.lean` change exactly the eight approved imports, in LE-facade's order?

**3. Rule 10 (ruling 2)**
- Do the seals, collected from the elaborated terms plus matchers, cover every touched declaration of the 10 files over
  the full closure, at the base and at the head, in both variants (`landing/seal-table.txt`)?
- Do the paired controls (20 probes, 57 sealed negatives, ALL_OK; `landing/ctlcheck.log`) show that the seals bite?
  They cover `padFin`, `PolyExpr.eval`, `padStr`, `splitBits`, `atParam`, `CRH.hash`, `HashSignForward.hashWord`,
  `HashSignFill.hashedReply` and `OracleComp.CostBoundedBy`.
- Explicit-unfold scan: 406 items at the head and 57 at the base, 0 foreign definitions.
- `MachineCodec.ext_of_fields` destructures a foreign structure with `cases` (review O1). Is that a read of a foreign
  definition?

**4. LE-doc formula and sketch accuracy**
- Does each of the 109 new formulas state what its declaration proves or defines, and does the new sketch of
  `polyTimeComputable_collisionRun` describe its proof (`landing-ledoc/0001-LE-doc.patch`; `docaudit-after.tsv` 110 OK
  plus the target, whose first line is the book statement; `sketchaudit-after.tsv` 0 missing)? A formula or sketch
  that misstates its declaration is a minor.
- Is LE-doc docstrings only, as ruling 4 records?

**5. Duplication**
- Does any new declaration duplicate a public TCSlib or Mathlib lemma beyond DL-42 (below)?
- Is any private lemma of another file copied rather than re-derived from published readers, beyond the two disclosed
  overlaps (`Games/Forwarding.lean` `fwdRun`, `polyTimeComputable_fwdRun`; the owned file's
  `polyTimeComputable_hsHashList`)?

## Known dispositions (not findings)

- **DL-42** (duplication ledger, open, deferred):
  - `HashSignForward.roundWord`/`handler` repeats the `Games/Forwarding` pattern (`fwdRun`/`fwdHandler`), but hashes
    each query and uses different inner and outer widths, which `fwdHandler` cannot express (disclosed). Fix:
    generalize `fwdHandler` with a query map;
  - `splitBits_pad_concat` is a corollary of `Games.padFin_append_split`; `expect_simulate_sample_once` is close to
    `Games.expect_simulate_eager` but does not restate it. Fix: promote, as the worker requests;
  - **the overlap with `lamport`**: the parallel `lamport` delivery's `lamport_codec_ext` ≈ `MachineCodec.ext_of_fields`,
    `lamport_forgerCodec` is an instance of `forgerCodec_eq_bitCodec`, and `exists_pure_of_cost_zero` ≈
    `eq_pure_of_cost_zero`. `lamport` is **under review and not landed** (its delivery is at exchange `5a50cdc0`). The
    fold happens after both units land; the lamport review records the same overlap from its side.
  What you can raise: a copy outside DL-42, or a disagreement with it. The lamport code is not part of this audit.
- **7 unused declarations, accepted as published API** (review M2): `sampledHashSign` with its `_eq` and `_apply`
  readers, `expect_sampledHashSign_eq_transcript`, `collisionAdv_seedIn`, `forward_fresh` and `hashWord_eq_hash`. A
  definition with its readers, plus three statement-level facts; removing them would be a code change for no gain.
- **`exists_oneTimeSecure_of_crh_owf` keeps `sorryAx`**, through `lamport_oneTimeSecure`, as at the base. It is
  pre-existing and outside this fill; its `sorryAx` comes only through Lamport's admission (the target itself is
  `sorryAx`-free).
- **The facade lands in sequence with `lamport`:** the `lamport` delivery also adds imports (sixteen, approved by
  Seyoon) to `Authentication.lean`; the two are merged into one consistently ordered facade at landing.
- **The facade's one line over 100 characters** is the base's (a line of its module docstring).
- **The worker's commit hashes** cannot be reproduced, because the delivery records no committer metadata. The content
  is verified: `git am` at the base gives the REPORT's tree `20aa8ef6`, and the 10 files are byte-identical to `src/`.
- **The review's verdict line** says LE-doc "is in progress". Its closing LE-doc section records the build that
  followed; the review record is not edited.

## Also check

**Axioms**
- The target prints `[propext, Classical.choice, Quot.sound]`. At the base it also had `sorryAx`.
- Of the 176 stored constants of the 10 files, only the pre-existing `exists_oneTimeSecure_of_crh_owf` carries
  `sorryAx` (above); all others use subsets of those three (the review's census; the landing edits change no proof).
- Nothing new is `@[simp]` or an instance; the only abbreviations are the pre-existing `hsGen` and `hsSign`.

**Admissions:** 22 → 21 in the 12 issued modules; only the target is removed (`landing/sorry-census.txt`).

**Sizes and widths:** every file is under 1000 lines; every line is at most 100 characters except the facade's
pre-existing line (`source-head.json`).

**Build:** at `4f0280c8`, the 15 changed and downstream modules (the 8 helpers, `HashAndSign`, `Authentication`,
#303's 4 base-delta modules and root `TCSlib`) have rc 0, 0 errors and 0 sorries (`landing/root-checks.jsonl`), and the
whole-tree check passes for 1209 modules at the head's source and olean hashes (`landing/final-tree-check.txt`). No
`audits/*/Checks` module imports the unit. The olean tree was restored to the base snapshot afterwards. The facade
`Authentication.lean` also imports `Hashing.FromDiscreteLog`, which draft PR #307 (Gate 24) changes; each PR was built
on its own base, and the files of the two PRs are disjoint.

## Evidence

- **`review.md`:** the maintainer's delivery review, verdict ACCEPT WITH LANDING EDITS, with its LE-doc section at the
  end.
- **`verification.zip`** (39 entries): every file the review cites, as byte-identical originals. Its `SHA256SUMS`
  lists every other entry, and `PROVENANCE.txt` gives each entry's source. It holds:
  - `review-evidence.zip` (`fills/hash-sign/final-r1/`, SHA-256 `e20cf9f0…`, 420 entries under `hash-sign-r1/`: the
    419 manifest paths plus that folder's `SHA256SUMS`) and `review-evidence-SHA256SUMS`, its manifest. It covers
    integrity, the build and the full-tree check with the restore, decls2, header bytes, `touched`, the docstring and
    sketch audits, the census and axioms, the strict and coe-variant seals at the base and the head, the paired
    controls, the scan, the old and new lint, sizes and the duplication grep;
  - `ledoc-evidence.zip` (SHA-256 `ab6c3d64…`, 110 entries) and `ledoc-evidence-SHA256SUMS`: the LE-doc patch, the
    docstring-only checks, the build at the head, the #305 lint and the restore;
  - `landing/` and `landing-ledoc/`: the review's extracts, each a byte copy of an entry of the matching ZIP;
  - `records/`: the issue package `fills/hash-sign/issued-r1/`, the duplication ledger, the decision log and the #305
    record `maintainer/lint-facade-fix-2026-11-14/` (README and patch), at records
    `65d89e5700b283e5b9d373335c78b0cf8391bd35`;
  - `worker/`: the worker's `evidence/escalations/` (`proposed-authentication-imports.patch`, `lint-new-fails.json`)
    and `evidence/inputs/session-overrides.md` (Seyoon's replies, verbatim), byte copies from exchange
    `90e4b3c833e5e7fed134941e016724531ad64f1f`.
- **The worker's own evidence:** on the exchange at `90e4b3c833e5e7fed134941e016724531ad64f1f`, under
  `inbox/fills/hash-sign/`. Its `PAYLOAD-SHA256SUMS` lists 1226 files and `evidence/SHA256SUMS` 1210, all delivered.
- **`landing/`:** at the final head.
  - `root-checks.jsonl`: the 15 modules at `4f0280c8`, rc 0, each changed file's `source_sha256` matching
    `source-head.json` (= `build/results.jsonl` of `ledoc-evidence.zip`).
  - `final-tree-check.txt`: 1209/1209 modules at `4f0280c8`'s source and olean hashes
    (= `build/tree-check-head.txt` of `ledoc-evidence.zip`).
  - `axioms-head.txt`: the review's census summary and the axioms of the target, `lamport_oneTimeSecure` and
    `exists_oneTimeSecure_of_crh_owf` (= `final-r1/landing/census-summary.txt`).
- **`worker-report.md`:** the worker's `REPORT.md`, at exchange `90e4b3c8`.
- **`pr.diff.txt`:** `git diff` from the base to the head (10 paths, 2247 insertions, 7 deletions).
- **`source-head.json`:** the head hashes, line counts and over-width counts of the 10 changed files.
- **`sources.zip`:** the source closure at the head of every changed module, 169 files.

## Findings delivery

Return `gate25-hash-sign-findings.md` as a Markdown file in this chat. If you have several evidence files, return a
ZIP. The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish the frozen statement, or a scope
  violation beyond the approved facade imports.
- **major:** a changed frozen statement, a forbidden read in a touched declaration not covered by the rulings, an
  undisclosed copied private lemma, or necessary evidence that cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring or proof sketch.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.

## ===== briefs/pass-shelat-ch5-8/gates/25-hash-sign/review.md =====

# hash-sign · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS.** The landing edits LE-width and LE-facade are done. LE-doc (109 formulas and
one sketch, docstrings only) is in progress.

## Delivery and landing branch

**Delivery**
- **Source:** Codex worker, exchange `90e4b3c833e5e7fed134941e016724531ad64f1f` (`inbox/fills/hash-sign/`): 4 patches on
  the issue base `eff2dcd0`.
- **Target:** `Authentication.hashAndSign_oneTimeSecure`, [PS10, Theorem 144.1]: hash-and-sign of a one-time scheme
  with a CRH family is one-time secure. The brief is `../issued-r1/brief.md`, SHA-256 `d4ddbdb3…`.
- **Files:**
  - the owned file `Authentication/Signatures/HashAndSign.lean`;
  - 8 new helpers in `HashAndSign/`: `CodecReaders`, `CollisionGame`, `CollisionHandler`, `FixedGame`,
    `ForwardGame`, `ForwardHandler`, `OneQuery` and `OneQuerySampling`;
  - the facade `Authentication.lean`.
- **Approved exception** (Seyoon, 2026-11-14): exactly eight helper imports in `Authentication.lean`. Against the
  base, the facade diff is exactly those 8 lines.

**Landing branch:** `land/pass-shelat-hash-sign`.
- **Base:** the worker commits are rebased onto records tip `dee0de32ee33d7188afe97bdc3089fac68412057`, which is after
  #303 and #305. Neither rebase had a conflict, and the Lean content did not change.
- **Worker commits:** `e6bcdd62`, `f92c2f72`, `dcf726fe` and `b7e4249b`. Their author (Codex) is kept.
- **Landing edits:**
  - **LE-width** `189f1c21`: re-wraps the one 101-character statement line of `expect_hashAndSign_sign`. Whitespace
    only.
  - **LE-facade** `6056f3ed7774d308846f7293e2c6ed992ce9d4f8` (tree `683ac79ce6e8f7c8a00321293a81c344a1fa05b1`):
    swaps `OneQuerySampling` and `OneQuery`, so the helpers follow `Signatures.HashAndSign` in alphabetical order, as
    in `Randomness.lean` and `PrivateKey.lean`. Order only.
- **The worker's commit hashes:** they cannot be reproduced, because no committer metadata was delivered. The REPORT's
  tree `20aa8ef6` does reproduce.

**Evidence:** `review-evidence.zip`.
- SHA-256 `e20cf9f08838b9b0a6464f8398fb9fa44a942e3ea43f37a8df4b8e86cc6b0cbf`.
- It has 420 entries under `hash-sign-r1/`: the 419 manifest paths plus `SHA256SUMS`. The manifest is
  `evidence-SHA256SUMS`.
- Extracts are in `landing/`.

## Checks

**Integrity**
- `PAYLOAD-SHA256SUMS` verifies 1226/1226 and `evidence/SHA256SUMS` 1210/1210, with exact path sets.
- The issue package verifies 7/7 and `SOURCE-SHA256SUMS` 150/150.
- `git am` at the base gives tree `20aa8ef6`. The 10 files are byte-identical to `src/`, and `src/` holds nothing else.

**Build** on `$SP/dl-oleans` (verified first as the base snapshot)
- 15 modules, all with rc 0 and 0 errors: the 8 helpers, `HashAndSign`, `Authentication`, the #303 base-delta modules
  and root `TCSlib`.
- After the edits, `HashAndSign`, `Authentication` and `TCSlib` were rebuilt, also with rc 0.
- Whole-tree check at the head: 1209 modules plus PFR.
- No `audits/*/Checks` module imports the unit.
- The tree was restored to the base snapshot (`landing/tree-check-post.txt`).

**Statements**
- decls2 against `eff2dcd0`: 110 ADDED, 0 CHANGED, 0 REMOVED.
- All 32 pre-existing declaration headers are byte-identical, the target's included. Only the target's body and
  sketch changed.

**Axioms**
- The target prints `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.
- `lamport_oneTimeSecure` is still admitted at this base, and the target does not depend on it.
- Of the 176 stored constants, only the pre-existing `exists_oneTimeSecure_of_crh_owf` carries `sorryAx`, through
  Lamport, as at the base.
- There are no new `@[simp]` lemmas and no new instances.

**Rule 10**
- Seals A and B, in both the strict and the coe variant, pass for all 10 files at the head, and for the owned file and
  the facade at the base. The two variants agree.
- Paired controls: 20 probes and 57 sealed negatives, ALL_OK.
- The explicit-unfold scan finds 0 foreign definitions.

**Admissions:** 22 → 21. Only the target was removed.

**Lint**
- New lint (#305): 92/102 at the records tip and at the head, with identical lines.
- Old lint: 216/102 at the base and at the head, with identical lines.
- Every file is under 1000 lines and every line is at most 100 characters, except one pre-existing facade line.

**Content.** The proof follows [PS10, Theorem 144.1].
1. **Common transcript.** The forge game equals a common transcript.
2. **Two cases.** A success is either a collision or a forward success.
   - The collision case is handled by adversary B, built with T1, using freshness and `hdom`.
   - The forward case is handled by adversary C, built with T2, as an exact equality.
3. **Conclusion.** A union bound, then `Negligible.add`.
4. **Edge cases:**
   - with no query, the run takes the forward branch;
   - `m′ = m` is excluded by freshness;
   - the `hlen` casts go through `Fin.cast`;
   - timeouts are handled by `forgerCodec_eq_bitCodec`.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| M1 | minor | 109 new public declarations have no formula in their docstrings. `polyTimeComputable_collisionRun` (16 lines) has no proof sketch. | **LE-doc**, docstrings only (ext-nosrc, cca2-ett and dl-crh precedent). In progress. |
| M2 | minor | 7 new declarations are not used anywhere: `sampledHashSign` with its `_eq` and `_apply` readers, `expect_sampledHashSign_eq_transcript`, `collisionAdv_seedIn`, `forward_fresh` and `hashWord_eq_hash`. | **Accepted** as published API: a definition with its readers, plus three statement-level facts. Removing them would be a code change and gains nothing. Disclosed to the gate. |
| M3a | minor | `HashSignForward.roundWord`/`handler` repeats the `Games/Forwarding` pattern (`fwdRun`/`fwdHandler`), but hashes each query and uses different inner and outer widths, which `fwdHandler` cannot express. Disclosed by the worker. | Ledger **DL-42**: generalize `fwdHandler` with a query map. |
| M3b | minor | `splitBits_pad_concat` is a corollary of `Games.padFin_append_split`. `expect_simulate_sample_once` is close to `Games.expect_simulate_eager` but does not restate it. | Ledger **DL-42**: promote, as the worker requests. |
| M3c | minor | Overlap with the parallel `lamport` delivery: its `lamport_codec_ext` ≈ `MachineCodec.ext_of_fields`, `lamport_forgerCodec` is an instance of `forgerCodec_eq_bitCodec`, and its `exists_pure_of_cost_zero` ≈ `eq_pure_of_cost_zero`. | Ledger **DL-42**: fold after both land. The lamport review records the same overlap from its side. |
| O1 | obs | `MachineCodec.ext_of_fields` destructures a foreign structure with `cases`. This reads no foreign definition. | Accepted. Promote to `Games/Machines` with no attribute. |

## LE-doc · `4f0280c8` (built)

- **Head:** `4f0280c85fae8730ca0dfad980b41749452980fa`, tree `4485fafd1abee34129c24c8aa76f4325230eb442`.
- **Change:** 109 formula docstrings and 1 proof sketch (`polyTimeComputable_collisionRun`). Docstrings only:
  - every hunk lies inside a doc comment, and with doc comments blanked the files are byte-identical;
  - all headers are byte-identical, and decls2 against the previous head is empty;
  - every new public declaration now passes the docaudit, except the target, whose first line is prose.
- **Rebase:** No rebase was needed: origin had only records commits after `dee0de32`.
- **Build** on `$SP/dl-oleans`: 15 modules (the 8 helpers, `HashAndSign`, `Authentication`, base-delta, root `TCSlib`) rc 0; full head check 1209 modules OK. The tree was restored to the base snapshot afterwards.
- **Lint (#305):** 92 FAIL / 102 WARN, with the same lines at the head as at the records tip.
- **Evidence:** `ledoc-evidence.zip`, SHA-256 `ab6c3d6492425d73d0b1caf35fa1d2ec0960696796daaa9e5cf9af2aa16dd7c9`, 110 entries. Its manifest is `ledoc-evidence-SHA256SUMS`, and extracts
  are in `landing-ledoc/`.
- **PR:** draft [PR #308](https://github.com/Shilun-Allan-Li/tcslib/pull/308).

## ===== briefs/pass-shelat-ch5-8/gates/25-hash-sign/worker-report.md =====

# hash-sign — final

**Theorem proved and required verification complete.**
`TCSlib.Cryptography.Authentication.hashAndSign_oneTimeSecure` proves PS10
Theorem 144.1 with its frozen statement unchanged. Final checked coverage is
169 modules with zero errors; admissions change only from 22 to 21 by removing
the target. Its axioms are exactly `propext`, `Classical.choice` and `Quot.sound`.
All twenty final A/B seals, both parent-facade baseline seals and all eleven
final control pairs pass. The complete raw evidence accompanies the source and
four-patch series; packaging verifies both manifests and the ZIP contents.

- Issue base: `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`.
- Issued exchange pack: `b436d19a0310265b214447ea6710deba32df6dd8`.
- Final source: `2e9d455a003c83d33b89149c83a6ab0610a63a4f`.
- Local-only branch: `fill/hash-sign`.
- Lean 4.25.0; Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.

## Proof and source changes

The proof follows the issued route. A common logged transcript fixes independent
signature-key, hash-index, adversary and signing tapes. The one-query sampling
law draws the possible signing tape before the run without changing its law.
T1 supplies the collision finder, which remembers the queried message and emits
it followed by the final message. Source freshness supplies distinctness;
`hdom` supplies domain membership. `exists_collisionGame_bound` bounds the
averaged equal-hash/fresh-message event by its actual CRH collision probability.

T2 supplies the original-scheme forger with `perCall = 1`, `finCall = 0`.
`exists_forwardGame` gives an exact original forgery-game/common-transcript
equality: acceptance and freshness of the final hash among forwarded queries.
The union bound and `Negligible.add` finish the theorem. The proof covers empty
logs, zero widths, malformed/noncanonical words and signatures, timeout outputs,
`m′ = m` and `hlen` casts. With no query the collision handler retains its zero
initial state; the forwarding forger covers that branch, so no collision success
is asserted for that default.

The main title/status and `## Contents` now describe a proved theorem. The sketch
records the shared transcript and tapes; its no-query description matches the
implementation. The final fourth patch makes two collision proofs use explicit
published padding/split readers and synchronizes that prose. It changes neither
the theorem statement nor any original declaration other than the target proof.

All paths below are relative to the repository. `HS/` denotes
`TCSlib/Cryptography/Authentication/Signatures/HashAndSign/`.

| Changed file | Lines | Purpose |
|---|---:|---|
| `TCSlib/Cryptography/Authentication.lean` | 60 | Eight specifically authorized helper imports. |
| `TCSlib/Cryptography/Authentication/Signatures/HashAndSign.lean` | 639 | Source/common-game readers, case split and final proof. |
| `HS/CodecReaders.lean` | 104 | Codec extensionality and split/concatenation readers. |
| `HS/CollisionGame.lean` | 171 | Averaged collision-game bound. |
| `HS/CollisionHandler.lean` | 450 | T1 construction, tape coupling and collision soundness. |
| `HS/FixedGame.lean` | 168 | Common transcript, fixed/fresh signers and success event. |
| `HS/ForwardGame.lean` | 384 | T2 transcript/log/output coupling and exact game equality. |
| `HS/ForwardHandler.lean` | 337 | T2 construction and typed call/finalization/width readers. |
| `HS/OneQuery.lean` | 63 | Zero/one-query normal forms. |
| `HS/OneQuerySampling.lean` | 63 | Drawing one possible answer tape before the run. |

Every file is below 1,000 lines. The full inventory,
`evidence/logs/final-source-declarations.json`, records 110 explicit additions
(26 definitions, 84 theorems) and 15 generated `simps` readers: 125 source-level
names. Its explicit list agrees with the touched-declaration census. The six
new main-file theorems are `hsHashList_eq_hashWord`, `expect_hashAndSign_sign`,
`hashAndSign_accepts_iff`, `runAt_hsGen_split`, `hashAndSign_forge_eq_common` and
`hashAndSign_success_cases`. The existing target is a changed proof, not a new
name. The final collector separately covers all 176 stored constants, including
auxiliaries: 50 in the main file, 126 in helpers, zero in the parent facade.

## Scope and reuse disclosures

`evidence/logs/source-scope.json` confirms the unchanged target header and all
other original declarations. No new admission or global simp attribute is
introduced. `Lamport.lean` and `Games/Efficiency.lean` are untouched, and the
target proof does not depend on Lamport's parallel proof. No foreign reader
remains missing.

The sole expanded ownership is the exact eight-import parent-facade patch.
After reviewing it and the eight corresponding lint failures, the user answered
“Authorize the eight imports”; `evidence/inputs/session-overrides.md` records
this exception. It authorizes no other parent-facade change.

Promotion requests:

- `MachineCodec.ext_of_fields` → `Games/Machines.lean`.
- `SignatureScheme.forgerCodec_eq_bitCodec` → `Authentication/Signatures/Defs.lean`.
- `splitBits_append`, `splitBits_pad_concat` → `Authentication/Encoding.lean`.
- `eq_pure_of_cost_zero`, `one_query_cases` → `Games/OracleComp.lean`.
- `expect_simulate_sample_once` → `Games/Hopping.lean`.
- `origFixedSign`, `OriginalSuccess`, `forgeGame_eq_fixed` → a signature-game helper module.

Search records are `evidence/logs/generic-searches.log`, `one-query-search.log`,
`split-bits-search.log` and `evidence/rule10/codec-searches.json`. Public sampling,
coin/seed, codec and take/drop facts are imported rather than copied.

overlap: `TCSlib/Cryptography/Games/Forwarding.lean` `fwdRun` and
`polyTimeComputable_fwdRun`. The specialized hashing round follows the same
two-round pattern, rederived from published input/call readers. No private
lemma was copied.

overlap: `TCSlib/Cryptography/Authentication/Signatures/HashAndSign.lean`
`polyTimeComputable_hsHashList`. The reduction hash pads to `S.msgLen` instead
of `H.rangeLen`; its wrapper uses public evaluator/padding combinators. A helper
importing the main file would create a cycle. These variants are disclosed for
maintainer review.

## Environment and checks

The isolated checkout `/private/tmp/hash-sign-fill/repo` uses disk-backed APFS.
The preflight records macOS substitutes for unavailable Linux `nproc`, cgroups,
`/proc` and GNU `df`: 12 CPUs; physical memory 19,327,352,832 bytes; non-file use
11,676,270,592; headroom 7,651,082,240; disk free 271,874,621,440. Both floors pass.

The user overrode the original single-Lean rule: unlimited checks for twenty
minutes from about 05:42 UTC, then at most three concurrent Lean jobs. Later
coordination clarified the host-wide cap and reserved capacity for `dl-crh`
and Lamport. The launcher counts both bare `lean` and full executable paths and
was tightened to one worker slot while other projects were active. Unrelated
jobs were not interrupted. All hash-sign native checks had closed before the
final Lamport coordination note; subsequent work uses only file/Git operations. Checks remain one module per `scripts/lean_check_tree.sh`
invocation in this checkout's tree; Python runs as `python3 -I`.

All seven pack hashes and 150 pinned source hashes pass. The same narrowed 82
Mathlib roots suffice. Cache retrieval exits 0, unpacking 2,339 files without
failed downloads; no archives were downloaded because the tool's hash-checked
store already held them. Its pre-session 32,667 files total 1,595,387,830 bytes,
origin unknown. Present package pins all match; absent documentation packages
are recorded as absent. There are no empty oleans and the root-import probe
passes. No project `lake build` or unfiltered cache command was run.

The extended order contains the issued 150 modules, eleven existing T1/T2/bridge
prerequisites and eight helpers. The full sweep at `8e4234934` passed; after the
two reader repairs, ordered indices 164–168 passed again. All 164 prefix sources
are byte-identical, and every selected row's SHA matches the final source.
`evidence/logs/final-sweep-results.jsonl` and `sweep-summary.json` establish
169/169 exit-zero, error-free final coverage. This accurately records reused
prefix checks and fresh tail checks.

`admission-delta.json` reports only the target removed (22 → 21). The target's
printed axioms are the expected three. The latest
`evidence/rule10/final-r2/axioms-summary.json` audits all 176 constants: all new
constants use only those axioms; the unchanged
`exists_oneTimeSecure_of_crh_owf` alone retains `sorryAx` through Lamport as at
base. Style lint (`python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography
--check8b`) reports 216 inherited FAIL at both base and final, zero new/removed
FAIL. Its exit 1 reflects inherited failures; the required comparison passes.

## Rule 10 results and provenance

Seals cover each owner's full TCSlib import closure. A excludes `PolyExpr.eval`
as notation; B seals it. Counts come from `evidence/rule10/final-r2/seal-A/manifest.json` and its B counterpart.

| Owner | A requests / result | B requests / result |
|---|---:|---:|
| `Authentication` | 2220 / pass | 2221 / pass |
| `HashAndSign` | 2112 / pass | 2113 / pass |
| `CodecReaders` | 789 / pass | 790 / pass |
| `CollisionGame` | 2058 / pass | 2059 / pass |
| `CollisionHandler` | 2050 / pass | 2051 / pass |
| `FixedGame` | 2045 / pass | 2046 / pass |
| `ForwardGame` | 2051 / pass | 2052 / pass |
| `ForwardHandler` | 2039 / pass | 2040 / pass |
| `OneQuery` | 617 / pass | 618 / pass |
| `OneQuerySampling` | 634 / pass | 635 / pass |

All twenty final A/B checks have zero failing declarations and complete native-guard
coverage; `evidence/rule10/final-r2/seal-matrix.json` records every check and source hash. Raw results,
request records and guard audits are retained under `evidence/rule10/` in
`final/`, `final-2250/` and `final-r2/`, with source hashes identifying byte-identical checks carried
forward.

The original main-file base seals pass A/B with 1,546/1,547 requests; seven
baseline paired controls pass. The added import-only parent facade has zero
stored constants. Its separately reconstructed baseline plans have 2,035/2,036
requests: both pass with complete native guards. This reconstruction uses exact base source/import
graph and preserved native metadata, but loads current compiled owned
dependencies. It is **not an authentic old Lean environment** and checks no
changed proof at base;
`evidence/rule10/base-facade-2250/catalog-reconstruction.json` records
that limitation.

The source-seal ledger records exactly three historical diagnostics, all with
passing resolutions on the latest bytes: `exists_forwardMachine` had a foreign
output-width elaboration dependency; `ofFn_collisionReply` and
`collisionHandler_collision` needed explicit published padding/split readers.
See `evidence/rule10/source-seal-failure-ledger.json` for original source hashes,
raw diagnostics, declarations and resolving guard audits. No failing declaration
is omitted or relabeled as an environment failure.

Earlier 1,000-request batches and the controlled 2,250-request workflow are both
retained. The switch changes batching only: request coverage, native-name
identity guards, instance masking and EOF verification are unchanged. A check
counts as a pass only with its complete installation/mask/EOF audit, not merely
an error-free proof log. Hash-addressed tool versions, pilot records, manifests,
requests and raw `results.jsonl` establish the executed workflow.

The completed explicit scan reviews 406 items: 361 public theorem uses (including
20 method/open aliases verified against native theorem names), six own-definition
uses and 39 local proof/let bindings; zero foreign-definition uses remain.
`evidence/rule10/final-r2/explicit-final.json`, its `explicit-review.json` and native probe logs
preserve this classification and the scanner's alias-resolution limitation.
All twenty-two final controls with minimal imports pass their expectations:
eleven unsealed probes pass; each of eleven sealed negatives fails exactly once
at its planned declaration; every published-reader positive passes. Independent
audits verify native identity, installation, instance masks and EOF for every
sealed control. See `evidence/rule10/final-r2/control-audit-summary.json`.

## Reproduction and delivery

The four complete format-patches are based on
`eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`, in this order:
`6bb523434a3a49abf8410a73f6eccf1db6cddca1`,
`15f43fd73b9f466263312403896953ca0ece0017`,
`8e4234934690fe4e3e00e46965112998e1d09a31`,
`2e9d455a003c83d33b89149c83a6ab0610a63a4f`.
Applying them reproduces exact tree `20aa8ef6247e3f0f7e58a6c4e096873219c9017c`;
`evidence/logs/patch-reproduction.json` passes. `src/` follows full repository
paths and matches the committed files.

Checkpoint 1 was pushed at exchange commit
`07d53012fdbe748fe2cfa7ae3dc04d166396dba0`; checkpoint 2 at
`053edd270ba3b2bd082ca2edcffb25c3cc2b3857`, only under
`inbox/fills/hash-sign/`. Both followed pull-with-rebase; no force-push occurred.
The user's direct push authorization supersedes the older generic README's
Codex chat-only rule. The proof branch remains local; other delivery paths are
untouched. `evidence/logs/exchange-deliveries.json` records provenance.

`evidence/logs/final-verification.json` independently checks the twenty seal
cells and their raw-log/request hashes, all seventy-four indexed Rule-10 logs,
controls, baseline checks, axioms, explicit scan, scope, admission delta, lint
and patch reproduction. Every check passes.

The final packager includes every evidence file, including original/superseded
sources, requests, manifests, raw logs, `results.jsonl`, probes and all used tool
versions. The native stack diagnostic is retained losslessly compressed.
`evidence/SHA256SUMS` covers exactly the evidence files except itself;
`PAYLOAD-SHA256SUMS` covers all other payload files. The packager verifies both
path sets and hashes, exact committed `src/` bytes, ZIP integrity and its sole
`hash-sign/` root. The assigned-path mirror verifies byte equality with that
snapshot before the final commit and pull-with-rebase/push.

The final exchange revision and fallback ZIP checksum accompany the chat
delivery. Only `inbox/fills/hash-sign/` is written on the exchange. Campaign
landing remains a maintainer PR for Seyoon's approval.

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

## ===== briefs/pass-shelat-ch5-8/fills/hash-sign/issued-r1/brief.md =====

# Codex fill · hash-and-sign is one-time secure (`hashAndSign_oneTimeSecure`, Theorem 144.1)

**Issue base** `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9` on `cryptography/pass-shelat-ch2-4` (the merge of #299).
**Unit** `hash-sign`. **Worker** Codex (Seyoon, 2026-11-14). **Lean** 4.25.0 and the Mathlib revision in that
commit's `lake-manifest.json`.

Prove the admitted theorem `hashAndSign_oneTimeSecure` of [PS10, Theorem 144.1] in `TCSlib/Cryptography/Authentication/Signatures/HashAndSign.lean`. The
statement passed Gate 06 (prong A) and is frozen. Its docstring holds the maintainer's proof sketch.

## Checkout and delivery

- Work in a local checkout of the repository. Fetch `cryptography/pass-shelat-ch2-4` and start a local branch
  `fill/hash-sign` at the exact issue base. Record the base in `REPORT.md`. Keep the proof branch local: never push it.
- Read `policy.md`, the attached environment addendum and `README.md`.
- **Deliver** every checkpoint and the final payload under `inbox/fills/hash-sign/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `src/`: the changed and new files;
  - `evidence/`, with a `SHA256SUMS` manifest (see *Evidence completeness*).
- Commit as `fill hash-sign: checkpoint N` and `fill hash-sign: final`. Pull with rebase before pushing, push only your
  delivery path, and never force-push.
- **At the end, also return the final payload in the chat** as a ZIP with `hash-sign/` at its root, holding the same
  `REPORT.md`, `patches/`, `src/` and `evidence/`. This is a fallback in case the push fails.
- Campaign changes land by a maintainer PR for Seyoon's approval.

## Target (frozen; quoted from the issue base)

```lean
theorem hashAndSign_oneTimeSecure (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) (hdom : ∀ n i x, H.inDom n i x = true)
    (hH : H.CollisionResistant) (hS : S.OneTimeSecure) :
    (hashAndSign H S hlen).OneTimeSecure := by
  sorry
```

It lives in namespace `TCSlib.Cryptography.Authentication`. There are no section variables. `hashAndSign H S hlen` signs `h_i(m)` with `S` (`hsSign`, `hsVerFun`, `hashAndSign_sign/_ver`); `OneTimeSecure` is in `Signatures/Defs.lean` and `CollisionResistant` in `Hashing/CollisionResistant.lean`. The file imports `Lamport.lean`, which the parallel `lamport` fill owns: do not edit it, and do not depend on its proof.

The target's docstring sketch is the route. You may edit it to describe the delivered proof.

## Published interfaces

| Interface | Provider |
|---|---|
| `hsSign`, `hsVerFun`, the hash-and-sign machines and readers, `hashAndSign_sign`, `hashAndSign_ver` and the other `hashAndSign_*` fields | owned file |
| `SignatureScheme`, `OneTimeSecure` and its experiment readers | `Authentication/Signatures/Defs.lean` |
| `CRH`, `CollisionResistant` and readers | `Hashing/CollisionResistant.lean` |
| T1 `Games.exists_handlerMachine`, T2 `Games.exists_interactiveHandlerMachine`, the `PolyHandler`/`InteractiveHandler` readers, `fwdHandler` | `Games/Efficiency.lean`, `Games/Forwarding.lean` |
| `NUPPT.exists_comp`, `exists_withAdvice(On)`; run/coin readers; `Negligible.add`, `mono` | `Complexity/Randomized/Closure.lean`, `Asymptotic/*`, `Foundations/Negligible.lean` |
| `simulate` and `OracleComp` laws, `buildComp_*`, `CostBoundedBy`, `bitCodec_*`, `ProbComp.expect_*`, `advantage_eq`, `accept_eq`, `prob_eq_until_bad` | `Games/*` |

## Proof route and checkpoints

1. **Checkpoint 1 · the collision finder (sketch step 2).** Build `B(1^n, i)` with T1: sample `(pk, sk)`, run `A` on `⟨pk, i⟩` answering its query with `Sign_sk(h_i(m))`, output `(m, m')`. Show that `B` collides whenever `A` forges with `h_i(m') = h_i(m)` (`hdom` gives domain membership). Send this checkpoint.
2. **Checkpoint 2 · the forger against `S` (sketch step 3).** Build `C^{Sign_sk}(1^n, pk)` with T2 (`perCall = 1`, `finCall = 0`): sample `i`, forward `A`'s query as `h_i(m)`, output `(h_i(m'), σ')`. Show this is a valid one-time forgery against `S` when `A` made no query or `h_i(m') ≠ h_i(m)`. Send this checkpoint.
3. **Final · the union (sketch step 4).** `A`'s success is at most `B`'s plus `C`'s, so it is negligible.

Check the edge cases: no query; a query outside the domain or of the wrong length; `m' = m`; malformed signatures; the codecs' timeout outputs; `hlen` length casts.

If the sketch is wrong, or the target is false as stated, stop and escalate with the exact obligation: a
checkpoint with the counterexample or the missing fact. Do not weaken the statement.

## Scope and proof discipline

- **Owned file.** You own `Authentication/Signatures/HashAndSign.lean`. Replace the target's proof body and edit its sketch. Update the module title (drop
  "(statement phase)") and the `## Main results` status.
- **Helper modules.** They are permitted under `TCSlib/Cryptography/Authentication/Signatures/HashAndSign/`. The owned file imports them precisely and
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

- **Bootstrap.** Bootstrap from `order.txt` (150 modules) and the narrow `roots.txt` (82), following the
  addendum. Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree. Never run
  `lake build` or an unfiltered cache get. Run Python as `python3 -I`. Insert helper modules before their consumers.
- **Sweep.**
  - Recheck the owned module, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (22 declarations in 12 modules). The only change
    must be the removal of `hashAndSign_oneTimeSecure`.
- **Axioms.**
  - Print the axioms of `hashAndSign_oneTimeSecure`. Expect only `propext`, `Classical.choice` and `Quot.sound`.
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

## ===== briefs/pass-shelat-ch5-8/gates/25-hash-sign/pr.diff.txt =====

diff --git a/TCSlib/Cryptography/Authentication.lean b/TCSlib/Cryptography/Authentication.lean
index e33d4b40f..2f5b41765 100644
--- a/TCSlib/Cryptography/Authentication.lean
+++ b/TCSlib/Cryptography/Authentication.lean
@@ -14,6 +14,14 @@ import TCSlib.Cryptography.Authentication.MAC.FromPRF
 import TCSlib.Cryptography.Authentication.Signatures.Lamport
 import TCSlib.Cryptography.Hashing.FromDiscreteLog
 import TCSlib.Cryptography.Authentication.Signatures.HashAndSign
+import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CodecReaders
+import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CollisionGame
+import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CollisionHandler
+import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.FixedGame
+import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.ForwardGame
+import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.ForwardHandler
+import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.OneQuery
+import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.OneQuerySampling
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
diff --git a/TCSlib/Cryptography/Authentication/Signatures/HashAndSign.lean b/TCSlib/Cryptography/Authentication/Signatures/HashAndSign.lean
index e18032a6f..d9a0eef41 100644
--- a/TCSlib/Cryptography/Authentication/Signatures/HashAndSign.lean
+++ b/TCSlib/Cryptography/Authentication/Signatures/HashAndSign.lean
@@ -7,13 +7,23 @@ import TCSlib.Cryptography.Authentication.Signatures.Defs
 import TCSlib.Cryptography.Hashing.CollisionResistant
 import TCSlib.Cryptography.Authentication.Encoding
 import TCSlib.Cryptography.Asymptotic.CollectionsLemmas
+import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
+import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.FixedGame
+import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CodecReaders
+import TCSlib.Cryptography.Games.Bridges.Experiments
+import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CollisionGame
+import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.ForwardGame
+import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CollisionHandler
+import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.ForwardHandler
+import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.OneQuery
+import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.OneQuerySampling
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
 set_option autoImplicit false
 
 /-!
-# Hash-and-sign (statement phase)
+# Hash-and-sign
 
 [PS10, Protocol 144.2]: from a family of collision-resistant hash functions `{h_i}` and a
 signature scheme `(Gen, Sign, Ver)` for the hash values,
@@ -53,11 +63,22 @@ collisions the CRH game counts.
 * The `hsHashList_eq`, key/index and algorithm equations expose the string computations.
 * `Authentication.hashAndSign_msgLen`, `hashAndSign_sigLen`, `hashAndSign_gen`,
   `hashAndSign_sign`, `hashAndSign_ver`: the signature-scheme data fields.
-* `Authentication.hashAndSign_oneTimeSecure` (Thm 144.1, stated; a `sorry` under the source's
-  sketch).
+* `Authentication.hashAndSign_oneTimeSecure` (Thm 144.1): one-time security from collision
+  resistance and one-time security of the original scheme, proved by the two reductions.
 * `Authentication.exists_oneTimeSecure_of_crh_owf`: the source's existential form, with
   Lamport's scheme (proved from Theorems 137.2 and 144.1).
 
+## Contents
+
+* `HashAndSign.CodecReaders`: canonical forger codecs and split-word readers.
+* `HashAndSign.OneQuery`: zero/one-query computation normal forms.
+* `HashAndSign.OneQuerySampling`: drawing one signing tape in advance.
+* `HashAndSign.ForwardHandler`: the efficient hashing/forwarding handler.
+* `HashAndSign.FixedGame`: the common fixed-tape transcript.
+* `HashAndSign.CollisionHandler`: the efficient collision finder and its soundness.
+* `HashAndSign.CollisionGame`: the collision-finding probability bound.
+* `HashAndSign.ForwardGame`: the original-scheme forgery probability equality.
+
 ## References
 
 * [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
@@ -369,16 +390,213 @@ theorem hashAndSign_ver (H : CRH) (S : SignatureScheme)
 
 /-! ### Theorem 144.1 -/
 
+/-- When hash and signature message widths agree, the hash-and-sign hash word equals the
+word used by the two reduction handlers, including on arbitrary list inputs: under `hlen`,
+`hsHashList H (List.replicate n true) i m =
+HashSignForward.hashWord H S (List.replicate n true) i m`. -/
+theorem hsHashList_eq_hashWord (H : CRH) (S : SignatureScheme)
+    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) (n : ℕ) (i m : List Bool) :
+    hsHashList H (List.replicate n true) i m =
+      HashSignForward.hashWord H S (List.replicate n true) i m := by
+  simp only [hsHashList_eq, HashSignForward.hashWord_eq, padStr_eq,
+    List.length_replicate, hlen n]
+
+/-- For a computation making at most one signing query, the hash-and-sign signing oracle
+has the same expected logged payoff as sampling one original signing tape before the run:
+if `c.CostBoundedBy (fun _ => 1) 1`, then
+`ProbComp.expect (simulate ((hashAndSign H S hlen).signImpl n (pairEncode sk i)).withLog c
+((), [])) g = ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
+ProbComp.expect (simulate (HashSignFill.fixedSign H S n sk i rs).withLog c ((), [])) g)`.
+
+**Proof sketch.** First move the wrapper signer's randomness outside the simulation using
+the one-query sampling law. Its coin bijection with the original signer preserves uniform
+sampling. The published wrapper run equation and the hash-width equation identify each
+fixed-tape answer with the common experiment's answer. -/
+theorem expect_hashAndSign_sign (H : CRH) (S : SignatureScheme)
+    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) (n : ℕ) (sk i : List Bool)
+    (c : OracleComp (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
+      (fun _ => S.sigLen.eval n)) (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool))
+    (hc : c.CostBoundedBy (fun _ => 1) 1)
+    (g : (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
+      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
+        (fun _ => S.sigLen.eval n))) → ℝ) :
+    ProbComp.expect
+        (simulate ((hashAndSign H S hlen).signImpl n (pairEncode sk i)).withLog c ((), [])) g =
+      ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
+        ProbComp.expect (simulate (HashSignFill.fixedSign H S n sk i rs).withLog c ((), []))
+          g) := by
+  have hraw := HashSignFill.expect_simulate_sample_once
+    (fun (_ : Fin 1) (m : Fin (H.domLen.eval n) → Bool) (rs : (hsSign S H).Coins n) =>
+      padFin (S.sigLen.eval n)
+        ((hsSign S H).runAt n (pairEncode (pairEncode sk i) (List.ofFn m)) rs)) c hc g
+  have hfirst : ProbComp.expect
+      (simulate ((hashAndSign H S hlen).signImpl n (pairEncode sk i)).withLog c ((), [])) g =
+      ProbComp.expect (ProbComp.sample ((hsSign S H).Coins n)) (fun rs =>
+        ProbComp.expect
+          (simulate (QueryImpl.withLog (fun (_ : Fin 1) (m : Fin (H.domLen.eval n) → Bool)
+            (_ : Unit) => (OracleComp.pure
+              (padFin (S.sigLen.eval n)
+                ((hsSign S H).runAt n (pairEncode (pairEncode sk i) (List.ofFn m)) rs), ()) :
+              ProbComp ((Fin (S.sigLen.eval n) → Bool) × Unit)))) c ((), [])) g) := by
+    simpa only [SignatureScheme.signImpl_eq, hashAndSign_sign, hashAndSign_sigLen] using hraw
+  rw [hfirst]
+  let e : S.sign.Coins n ≃ (hsSign S H).Coins n :=
+    NUPPT.coinsCongr (A := S.sign) (B := hsSign S H)
+      (NUPPT.coins_ofPolyTimeUniform (polyTimeComputable_hsSignFun S H) S.sign.coins).symm n
+  rw [← ProbComp.expect_sample_equiv e]
+  apply congrArg (ProbComp.expect (ProbComp.sample (S.sign.Coins n)))
+  funext rs
+  have hi : (fun (_ : Fin 1) (m : Fin (H.domLen.eval n) → Bool) (_ : Unit) =>
+      (OracleComp.pure (padFin (S.sigLen.eval n)
+        ((hsSign S H).runAt n (pairEncode (pairEncode sk i) (List.ofFn m)) (e rs)), ()) :
+        ProbComp ((Fin (S.sigLen.eval n) → Bool) × Unit))) =
+      HashSignFill.fixedSign H S n sk i rs := by
+    funext j m s
+    rw [HashSignFill.fixedSign_apply, HashSignFill.hashedReply_eq,
+      runAt_hsSign, hsHashList_eq_hashWord H S hlen]
+  rw [hi]
+
+/-- Hash-and-sign accepts a message/signature pair exactly when the original scheme accepts
+the padded hash of that message with the same signature:
+`(hashAndSign H S hlen).Accepts n (pairEncode pk i) m σ ↔
+S.Accepts n pk (padFin (S.msgLen.eval n) (H.eval (atParam n (pairEncode i (List.ofFn m))))) σ`. -/
+theorem hashAndSign_accepts_iff (H : CRH) (S : SignatureScheme)
+    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) (n : ℕ) (pk i : List Bool)
+    (m : Fin (H.domLen.eval n) → Bool) (σ : Fin (S.sigLen.eval n) → Bool) :
+    (hashAndSign H S hlen).Accepts n (pairEncode pk i) m σ ↔
+      S.Accepts n pk (padFin (S.msgLen.eval n)
+        (H.eval (atParam n (pairEncode i (List.ofFn m))))) σ := by
+  simp only [SignatureScheme.accepts_iff, hashAndSign_ver, hsVerFun_eq, atParam_eq,
+    pairFstD_pairEncode, pairSndD_pairEncode, hsHashList_eq_hashWord H S hlen,
+    HashSignForward.hashWord_unary]
+
+/-- On concatenated original-generator and hash-generator tapes, the combined generator
+returns the original public and secret keys each paired with the same generated hash index:
+`(hsGen S H).runAt n [] (EnsembleLemmas.coinsEquiv (hsGen_coinLen S H n) (rg, ri)) =
+pairEncode (pairEncode pk i) (pairEncode sk i)`, where
+`pk = pairFstD (S.gen.runAt n [] rg)`, `sk = pairSndD (S.gen.runAt n [] rg)` and
+`i = H.gen.runAt n [] ri`.
+
+**Proof sketch.** The published coin-splitting bijection has the concatenated encoding.
+Transporting to the combined width preserves that encoding, so its two projections are
+the original tapes. The combined generator's run equation then gives the paired keys. -/
+theorem runAt_hsGen_split (S : SignatureScheme) (H : CRH) (n : ℕ)
+    (rg : S.gen.Coins n) (ri : H.gen.Coins n) :
+    (hsGen S H).runAt n []
+        (EnsembleLemmas.coinsEquiv (hsGen_coinLen S H n) (rg, ri)) =
+      pairEncode
+        (pairEncode (pairFstD (S.gen.runAt n [] rg)) (H.gen.runAt n [] ri))
+        (pairEncode (pairSndD (S.gen.runAt n [] rg)) (H.gen.runAt n [] ri)) := by
+  let ρ := EnsembleLemmas.coinsEquiv (hsGen_coinLen S H n) (rg, ri)
+  let σ : Fin (S.gen.coinLen n + H.gen.coinLen n) → Bool :=
+    fun j => ρ (Fin.cast (hsGen_coinLen S H n).symm j)
+  have hσ : σ = Fin.append rg ri := by
+    apply List.ofFn_injective
+    exact (List.ofFn_congr (hsGen_coinLen S H n) ρ).symm.trans
+      ((EnsembleLemmas.ofFn_coinsEquiv (hsGen_coinLen S H n) (rg, ri)).trans
+        (List.ofFn_fin_append rg ri).symm)
+  rw [runAt_hsGen]
+  change pairEncode
+    (pairEncode (pairFstD (S.gen.runAt n [] (fun j => σ (Fin.castAdd (H.gen.coinLen n) j))))
+      (H.gen.runAt n [] (fun j => σ (Fin.natAdd (S.gen.coinLen n) j))))
+    (pairEncode (pairSndD (S.gen.runAt n [] (fun j => σ (Fin.castAdd (H.gen.coinLen n) j))))
+      (H.gen.runAt n [] (fun j => σ (Fin.natAdd (S.gen.coinLen n) j)))) = _
+  simp only [hσ, Fin.append_left, Fin.append_right]
+
+/-- The hash-and-sign forgery probability equals the common transcript's success
+probability averaged over independent original key, hash-index, adversary and signing tapes:
+`accept ((hashAndSign H S hlen).forgeGame A 1 n) = 𝔼 rg : S.gen.Coins n, 𝔼 ri : H.gen.Coins n,
+𝔼 rA : A.Coins n, 𝔼 rs : S.sign.Coins n, ProbComp.prob
+(HashSignFill.transcript H S A n pk sk i rs rA) (HashSignFill.Success H S n pk i)`,
+writing `𝔼 x : X, f x` for `ProbComp.expect (ProbComp.sample X) (fun x => f x)`, with
+`pk = pairFstD (S.gen.runAt n [] rg)`, `sk = pairSndD (S.gen.runAt n [] rg)` and
+`i = H.gen.runAt n [] ri`.
+
+**Proof sketch.** Read the forgery experiment through its published equation. Reindex the
+combined generator tape by the product of the original generator tapes and use its run
+equation. Finally move the single signing tape outside the logged simulation and identify
+verification with original-scheme verification on the hash. -/
+theorem hashAndSign_forge_eq_common (H : CRH) (S : SignatureScheme)
+    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) (A : NUPPT) (n : ℕ) :
+    accept ((hashAndSign H S hlen).forgeGame A 1 n) =
+      ProbComp.expect (ProbComp.sample (S.gen.Coins n)) (fun rg =>
+        ProbComp.expect (ProbComp.sample (H.gen.Coins n)) (fun ri =>
+          ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA =>
+            ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
+              ProbComp.prob
+                (HashSignFill.transcript H S A n (pairFstD (S.gen.runAt n [] rg))
+                  (pairSndD (S.gen.runAt n [] rg)) (H.gen.runAt n [] ri) rs rA)
+                (HashSignFill.Success H S n (pairFstD (S.gen.runAt n [] rg))
+                  (H.gen.runAt n [] ri)))))) := by
+  classical
+  rw [SignatureScheme.forgeGame_eq, accept_eq, ProbComp.prob_eq_expect]
+  simp only [ProbComp.expect_bind, ProbComp.expect_pure, decide_eq_true_eq,
+    hashAndSign_gen]
+  rw [← ProbComp.expect_sample_equiv (EnsembleLemmas.coinsEquiv (hsGen_coinLen S H n))]
+  rw [← Bridge.expect_sample_pair]
+  simp only [ProbComp.expect_bind, ProbComp.expect_pure]
+  apply congrArg (ProbComp.expect (ProbComp.sample (S.gen.Coins n)))
+  funext rg
+  apply congrArg (ProbComp.expect (ProbComp.sample (H.gen.Coins n)))
+  funext ri
+  simp only [runAt_hsGen_split, pairFstD_pairEncode, pairSndD_pairEncode,
+    SignatureScheme.forgerCodec_eq_bitCodec, hashAndSign_msgLen, hashAndSign_sigLen]
+  apply congrArg (ProbComp.expect (ProbComp.sample (A.Coins n)))
+  funext rA
+  rw [expect_hashAndSign_sign H S hlen n _ _ _ (A.toCompOn_costBoundedBy _ n 1 _ rA)]
+  apply congrArg (ProbComp.expect (ProbComp.sample (S.sign.Coins n)))
+  funext rs
+  simp only [HashSignFill.transcript_eq, ProbComp.prob_eq_expect,
+    HashSignFill.success_iff, hashAndSign_accepts_iff]
+  apply congrArg (ProbComp.expect _)
+  funext res
+  split <;> rfl
+
+/-- Every successful common transcript either gives a fresh-message hash collision or
+is a successful forgery after forwarding hashes to the original signing oracle: under `hlen`,
+`HashSignFill.Success H S n pk i res →
+HashSignFill.CollisionCase H S n i res ∨ HashSignFill.ForwardSuccess H S n pk i res`.
+
+**Proof sketch.** If a queried message has the final message's hash, use source freshness
+for the collision case. Otherwise the final hash is fresh among forwarded queries.
+The range-width equation transports equality of the forwarded hash vectors back to
+equality of CRH hash vectors, including at width zero. -/
+theorem hashAndSign_success_cases (H : CRH) (S : SignatureScheme)
+    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) (n : ℕ) (pk i : List Bool)
+    (res : (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
+      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
+        (fun _ => S.sigLen.eval n))))
+    (h : HashSignFill.Success H S n pk i res) :
+    HashSignFill.CollisionCase H S n i res ∨
+      HashSignFill.ForwardSuccess H S n pk i res := by
+  classical
+  obtain ⟨haccept, hfresh⟩ := (HashSignFill.success_iff H S n pk i res).mp h
+  by_cases heq : ∃ e ∈ res.2.2,
+      H.hash n i e.2.1 = H.hash n i (splitBits res.1).1
+  · exact Or.inl ((HashSignFill.collisionCase_iff H S n i res).mpr ⟨hfresh, heq⟩)
+  · apply Or.inr
+    apply (HashSignFill.forwardSuccess_iff H S n pk i res).mpr
+    constructor
+    · simpa only [HashSignFill.queryHash_eq] using haccept
+    · intro e hem hsame
+      apply heq
+      refine ⟨e, hem, ?_⟩
+      funext j
+      have hv := congrFun hsame (Fin.cast (hlen n) j)
+      simpa only [HashSignFill.queryHash_eq, CRH.hash_eq, padFin_apply, Fin.coe_cast] using hv
+
 /-- **Theorem 144.1: hash-and-sign is one-time secure** [PS10, Theorem 144.1] when the hash
 family is collision resistant on its full domain and the signature scheme is one-time secure.
 
-**Proof sketch** (the source's).
+**Proof sketch.** The source's two reductions are implemented with independent key,
+hash-index, adversary and signing tapes; a one-query sampling law couples their common
+logged transcript, including no-query and codec-timeout outputs.
 1. Let `A` be a one-time forger against `hashAndSign`, querying `m` (or nothing) and outputting
    `(m′, σ′)` with `m′ ≠ m` and `Ver_pk(h_i(m′), σ′)` accepting.
 2. *Case `h_i(m′) = h_i(m)`.* The collision finder `B(1^n, i)` samples `(pk, sk) ← Gen(1^n)`,
    runs `A` on `⟨pk, i⟩` answering its query with `Sign_sk(h_i(m))`, and outputs `(m, m′)`
-   (aborting if `A` made no query). Since `m′ ≠ m` and both lie in `D_i` (`hdom`), this is a
-   collision. `B` answers `A`'s queries itself, so it is a machine by T1
+   (using the initial zero word if no query was made). For the queried case, freshness and
+   `hdom` give a collision. `B` answers `A`'s queries itself, so it is a machine by T1
    (`Games.exists_handlerMachine`), with `advIn` supplying `⟨pk, i⟩`, `out` returning `(m, m′)`,
    and the seed holding the coins of `Gen` and `Sign`.
 3. *Case `A` made no query or `h_i(m′) ≠ h_i(m)`.* The forger `C^{Sign_sk}(1^n, pk)` samples
@@ -392,7 +610,32 @@ theorem hashAndSign_oneTimeSecure (H : CRH) (S : SignatureScheme)
     (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) (hdom : ∀ n i x, H.inDom n i x = true)
     (hH : H.CollisionResistant) (hS : S.OneTimeSecure) :
     (hashAndSign H S hlen).OneTimeSecure := by
-  sorry
+  classical
+  apply (SignatureScheme.oneTimeSecure_iff _).mpr
+  intro A
+  obtain ⟨B, hB⟩ := HashSignFill.exists_collisionGame_bound H S A hdom
+  obtain ⟨C, hC⟩ := HashSignFill.exists_forwardGame H S A
+  obtain ⟨εB, hεB, hboundB⟩ := (CRH.collisionResistant_iff H).mp hH B
+  obtain ⟨εC, hεC, hboundC⟩ := (SignatureScheme.oneTimeSecure_iff S).mp hS C
+  refine ⟨fun n => εB n + εC n, hεB.add hεC, fun n => ?_⟩
+  rw [hashAndSign_forge_eq_common H S hlen A n]
+  refine le_trans ?_ (add_le_add (hboundB n) (hboundC n))
+  refine le_trans ?_ (add_le_add (hB n) (le_of_eq (hC n).symm))
+  -- Bound the success event by the union before averaging the independent tapes.
+  rw [← ProbComp.expect_add]
+  apply ProbComp.expect_mono
+  intro rg
+  rw [← ProbComp.expect_add]
+  apply ProbComp.expect_mono
+  intro ri
+  rw [← ProbComp.expect_add]
+  apply ProbComp.expect_mono
+  intro rA
+  rw [← ProbComp.expect_add]
+  apply ProbComp.expect_mono
+  intro rs
+  exact (ProbComp.prob_mono _ (fun res hs =>
+    hashAndSign_success_cases H S hlen n _ _ res hs)).trans (ProbComp.prob_or_le _ _ _)
 
 /-- **The existential form of Theorem 144.1** [PS10]: a collision-resistant hash family
 `{0,1}^{d(n)} → {0,1}^n` on its full domain, and a one-way function, give a one-time secure
diff --git a/TCSlib/Cryptography/Authentication/Signatures/HashAndSign/CodecReaders.lean b/TCSlib/Cryptography/Authentication/Signatures/HashAndSign/CodecReaders.lean
new file mode 100644
index 000000000..d0681b48f
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/Signatures/HashAndSign/CodecReaders.lean
@@ -0,0 +1,110 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Authentication.Signatures.Defs
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Signature forger codecs read through their published fields
+
+## Main definitions
+
+This module introduces no definitions.
+
+## Main results
+
+* `Games.MachineCodec.ext_of_fields`: codecs with equal decoding, entry encoding,
+  and timeout fields are equal.
+* `Authentication.SignatureScheme.forgerCodec_eq_bitCodec`: the signature
+  forger codec equals the canonical bit codec at its declared lengths.
+* `HashSignFill.splitBits_append`, `splitBits_pad_concat`: splitting fixed-width
+  concatenated words recovers their components, including zero widths.
+
+The generic extensionality lemma is a promotion request for `Games/Machines`;
+the signature-specific reader belongs beside its definition in `Signatures/Defs`.
+The two split-word readers are promotion requests for `Authentication/Encoding`.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
+  January 2010, Theorem 144.1 (technical support for its machine reductions).
+-/
+
+namespace TCSlib.Cryptography.Games.MachineCodec
+
+/-- Two machine codecs are equal when their move decoders, entry encoders and timeout
+outputs are equal:
+`a.decodeMove = b.decodeMove → a.encodeEntry = b.encodeEntry → a.timeout = b.timeout → a = b`.
+These are all three fields of `MachineCodec`.
+
+**Proof sketch.** Destructure the two records. Substituting the three field equalities
+leaves the same constructor on both sides. -/
+theorem ext_of_fields {ι α : Type} {spec : OracleSpec ι}
+    (a b : MachineCodec spec α)
+    (hdecode : a.decodeMove = b.decodeMove)
+    (hentry : a.encodeEntry = b.encodeEntry)
+    (htimeout : a.timeout = b.timeout) : a = b := by
+  cases a
+  cases b
+  cases hdecode
+  cases hentry
+  cases htimeout
+  rfl
+
+end TCSlib.Cryptography.Games.MachineCodec
+
+namespace TCSlib.Cryptography.Authentication.SignatureScheme
+
+open TCSlib.Cryptography.Games
+
+/-- The signature forger codec is the bit codec with message-length queries,
+signature-length answers and a message-plus-signature-length final output:
+`S.forgerCodec n = bitCodec (fun _ : Fin 1 => S.msgLen.eval n) (fun _ : Fin 1 => S.sigLen.eval n)
+(S.msgLen.eval n + S.sigLen.eval n)`.
+
+**Proof sketch.** The published decoding, entry-encoding and timeout equations agree
+with those of the bit codec. Codec extensionality turns those field equations into
+equality of the complete records; neither codec's definition is unfolded. -/
+theorem forgerCodec_eq_bitCodec (S : SignatureScheme) (n : ℕ) :
+    S.forgerCodec n =
+      bitCodec (fun _ : Fin 1 => S.msgLen.eval n) (fun _ : Fin 1 => S.sigLen.eval n)
+        (S.msgLen.eval n + S.sigLen.eval n) := by
+  apply MachineCodec.ext_of_fields
+  · funext w
+    exact (S.forgerCodec_decodeMove n w).trans
+      (bitCodec_decodeMove (fun _ : Fin 1 => S.msgLen.eval n)
+        (fun _ : Fin 1 => S.sigLen.eval n) (S.msgLen.eval n + S.sigLen.eval n) w).symm
+  · funext e
+    exact (S.forgerCodec_encodeEntry n e).trans
+      (bitCodec_encodeEntry (fun _ : Fin 1 => S.msgLen.eval n)
+        (fun _ : Fin 1 => S.sigLen.eval n) (S.msgLen.eval n + S.sigLen.eval n) e).symm
+  · exact (S.forgerCodec_timeout n).trans
+      (bitCodec_timeout (fun _ : Fin 1 => S.msgLen.eval n)
+        (fun _ : Fin 1 => S.sigLen.eval n) (S.msgLen.eval n + S.sigLen.eval n)).symm
+
+end TCSlib.Cryptography.Authentication.SignatureScheme
+
+namespace TCSlib.Cryptography.Authentication.HashSignFill
+
+/-- Splitting the concatenation of two fixed-width words recovers the two words:
+`splitBits (Fin.append x y) = (x, y)`. -/
+theorem splitBits_append {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) :
+    splitBits (Fin.append x y) = (x, y) := by
+  apply Prod.ext
+  · funext j
+    rw [splitBits_fst, Fin.append_left]
+  · funext j
+    rw [splitBits_snd, Fin.append_right]
+
+/-- Reading the concatenated encodings of two words at their total width and splitting the
+result recovers the original words: `splitBits (padFin (a + b) (List.ofFn x ++ List.ofFn y)) =
+(x, y)`. This also covers zero widths. -/
+theorem splitBits_pad_concat {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) :
+    splitBits (padFin (a + b) (List.ofFn x ++ List.ofFn y)) = (x, y) := by
+  rw [← List.ofFn_fin_append, padFin_ofFn, splitBits_append]
+
+end TCSlib.Cryptography.Authentication.HashSignFill
diff --git a/TCSlib/Cryptography/Authentication/Signatures/HashAndSign/CollisionGame.lean b/TCSlib/Cryptography/Authentication/Signatures/HashAndSign/CollisionGame.lean
new file mode 100644
index 000000000..24885ee92
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/Signatures/HashAndSign/CollisionGame.lean
@@ -0,0 +1,180 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CollisionHandler
+import TCSlib.Cryptography.Games.Bridges.Experiments
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The collision probability in the hash-and-sign reduction
+
+## Main definitions
+
+* `HashSignFill.CollisionCase`: the final message is fresh and has the same hash as some
+  logged query.
+
+## Main results
+
+* `HashSignFill.exists_collisionGame_bound`: the common transcript's collision case is
+  bounded by the collision probability of one machine.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 144.1, collision-finding case.
+-/
+
+namespace TCSlib.Cryptography.Authentication.HashSignFill
+
+open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
+
+/-- The collision case of a common transcript: its final message is distinct from every
+logged query, and some logged query has its hash,
+`CollisionCase H S n i res ↔ (∀ e ∈ res.2.2, e.2.1 ≠ m) ∧
+∃ e ∈ res.2.2, H.hash n i e.2.1 = H.hash n i m`, where `m = (splitBits res.1).1`
+[PS10, Theorem 144.1]. -/
+def CollisionCase (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
+    (res : (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
+      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
+        (fun _ => S.sigLen.eval n)))) : Prop :=
+  (∀ e ∈ res.2.2, e.2.1 ≠ (splitBits res.1).1) ∧
+    ∃ e ∈ res.2.2, H.hash n i e.2.1 = H.hash n i (splitBits res.1).1
+
+/-- The collision case holds exactly when the final message is fresh and a logged query
+has the same hash as that message: `CollisionCase H S n i res ↔ (∀ e ∈ res.2.2, e.2.1 ≠ m) ∧
+∃ e ∈ res.2.2, H.hash n i e.2.1 = H.hash n i m`, where `m = (splitBits res.1).1`. -/
+theorem collisionCase_iff (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
+    (res : (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
+      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
+        (fun _ => S.sigLen.eval n)))) :
+    CollisionCase H S n i res ↔
+      (∀ e ∈ res.2.2, e.2.1 ≠ (splitBits res.1).1) ∧
+        ∃ e ∈ res.2.2, H.hash n i e.2.1 = H.hash n i (splitBits res.1).1 := Iff.rfl
+
+/-- A machine's collision probability bounds the collision case of the common transcript,
+averaged over the original keys, hash index, adversary tape and signing tape: if
+`∀ n i x, H.inDom n i x = true`, then `∃ B : NUPPT, ∀ n, 𝔼 rg : S.gen.Coins n,
+𝔼 ri : H.gen.Coins n, 𝔼 rA : A.Coins n, 𝔼 rs : S.sign.Coins n, ProbComp.prob
+(transcript H S A n pk sk i rs rA) (CollisionCase H S n i) ≤ accept (H.collisionGame B n)`,
+writing `𝔼 x : X, f x` for `ProbComp.expect (ProbComp.sample X) (fun x => f x)`, with
+`pk = pairFstD (S.gen.runAt n [] rg)`, `sk = pairSndD (S.gen.runAt n [] rg)` and
+`i = H.gen.runAt n [] ri` [PS10, Theorem 144.1].
+
+**Proof sketch.** T1 constructs a machine with the same deterministic transcript on each
+choice of seed and adversary tape. In the collision case its output satisfies the exact
+CRH collision predicate. Average this pointwise indicator inequality. The seed equivalence
+concatenates the original generator and signer tapes; the T1 coin equivalence then turns
+the seed and adversary tapes into uniform collision-finder coins. Independent samples may
+be exchanged, so the resulting average is exactly the CRH game's acceptance probability. -/
+theorem exists_collisionGame_bound (H : CRH) (S : SignatureScheme) (A : NUPPT)
+    (hdom : ∀ n i x, H.inDom n i x = true) :
+    ∃ B : NUPPT, ∀ n,
+      ProbComp.expect (ProbComp.sample (S.gen.Coins n)) (fun rg =>
+        ProbComp.expect (ProbComp.sample (H.gen.Coins n)) (fun ri =>
+          ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA =>
+            ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
+              ProbComp.prob (transcript H S A n (pairFstD (S.gen.runAt n [] rg))
+                (pairSndD (S.gen.runAt n [] rg)) (H.gen.runAt n [] ri) rs rA)
+                (CollisionCase H S n (H.gen.runAt n [] ri)))))) ≤
+        accept (H.collisionGame B n) := by
+  classical
+  obtain ⟨B, hB⟩ := exists_collisionMachine_transcript H S A
+  refine ⟨B, fun n => ?_⟩
+  obtain ⟨φ, hφ⟩ := hB n
+  let seed : S.gen.Coins n × S.sign.Coins n ≃
+      (Fin ((collisionHandler H S).seedLen.eval n) → Bool) :=
+    EnsembleLemmas.seedEquiv (A := S.gen) (B := S.sign) (collisionHandler_seedLen H S) n
+  let win : List Bool → B.Coins n → Prop := fun i r =>
+    let xx := splitBits (padFin (H.domLen.eval n + H.domLen.eval n) (B.runAt n i r))
+    H.inDom n i xx.1 = true ∧ H.inDom n i xx.2 = true ∧ xx.1 ≠ xx.2 ∧
+      H.hash n i xx.1 = H.hash n i xx.2
+  let payoff : List Bool → B.Coins n → ℝ := fun i r => if win i r then 1 else 0
+  have hpoint (rg : S.gen.Coins n) (rs : S.sign.Coins n) (rA : A.Coins n) (i : List Bool) :
+      ProbComp.prob (transcript H S A n (pairFstD (S.gen.runAt n [] rg))
+        (pairSndD (S.gen.runAt n [] rg)) i rs rA) (CollisionCase H S n i) ≤
+        payoff i (φ (seed (rg, rs), rA)) := by
+    obtain ⟨a, s, L, ht, hinv, hrun⟩ := hφ i rg rs (seed (rg, rs)) rA
+      (EnsembleLemmas.seedEquiv_ofFn (collisionHandler_seedLen H S) n (rg, rs))
+    rw [ht, ProbComp.prob_pure]
+    dsimp only [payoff]
+    by_cases hcase : CollisionCase H S n i (a, ((), L))
+    · have hclauses := (collisionCase_iff H S n i (a, ((), L))).mp hcase
+      have hw : win i (φ (seed (rg, rs), rA)) := by
+        dsimp only [win]
+        rw [hrun]
+        exact collisionHandler_collision H S hdom n (pairSndD (S.gen.runAt n [] rg)) i rs
+          (seed (rg, rs)) a s L hinv hclauses.1 hclauses.2
+      simp only [hcase, hw, if_true]
+      exact le_rfl
+    · simp only [hcase, if_false]
+      split_ifs <;> norm_num
+  have hcoins (i : List Bool) :
+      ProbComp.expect (ProbComp.sample (S.gen.Coins n)) (fun rg =>
+        ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
+          ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA =>
+            payoff i (φ (seed (rg, rs), rA))))) =
+        ProbComp.expect (ProbComp.sample (B.Coins n)) (fun r =>
+          payoff i r) := by
+    calc
+      _ = ProbComp.expect (ProbComp.sample (S.gen.Coins n × S.sign.Coins n)) (fun p =>
+          ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA =>
+            payoff i (φ (seed p, rA)))) := by
+        simpa only [ProbComp.expect_bind, ProbComp.expect_pure] using
+          Bridge.expect_sample_pair (fun p : S.gen.Coins n × S.sign.Coins n =>
+            ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA =>
+              payoff i (φ (seed p, rA))))
+      _ = ProbComp.expect
+          (ProbComp.sample (Fin ((collisionHandler H S).seedLen.eval n) → Bool)) (fun ω =>
+          ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA =>
+            payoff i (φ (ω, rA)))) := by
+        exact ProbComp.expect_sample_equiv seed (fun ω =>
+          ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA => payoff i (φ (ω, rA))))
+      _ = ProbComp.expect (ProbComp.sample
+          ((Fin ((collisionHandler H S).seedLen.eval n) → Bool) × A.Coins n)) (fun p =>
+          payoff i (φ p)) := by
+        simpa only [ProbComp.expect_bind, ProbComp.expect_pure] using
+          Bridge.expect_sample_pair (fun p :
+            (Fin ((collisionHandler H S).seedLen.eval n) → Bool) × A.Coins n =>
+            payoff i (φ p))
+      _ = _ := by
+        exact ProbComp.expect_sample_equiv φ (payoff i)
+  calc
+    _ ≤ ProbComp.expect (ProbComp.sample (S.gen.Coins n)) (fun rg =>
+        ProbComp.expect (ProbComp.sample (H.gen.Coins n)) (fun ri =>
+          ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA =>
+            ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
+              payoff (H.gen.runAt n [] ri) (φ (seed (rg, rs), rA)))))) := by
+      apply ProbComp.expect_mono
+      intro rg
+      apply ProbComp.expect_mono
+      intro ri
+      apply ProbComp.expect_mono
+      intro rA
+      exact ProbComp.expect_mono _ (fun rs => hpoint rg rs rA (H.gen.runAt n [] ri))
+    _ = ProbComp.expect (ProbComp.sample (H.gen.Coins n)) (fun ri =>
+        ProbComp.expect (ProbComp.sample (S.gen.Coins n)) (fun rg =>
+          ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
+            ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA =>
+              payoff (H.gen.runAt n [] ri) (φ (seed (rg, rs), rA)))))) := by
+      rw [ProbComp.expect_sample_comm]
+      congr 1
+      funext ri
+      congr 1
+      funext rg
+      exact ProbComp.expect_sample_comm _
+    _ = ProbComp.expect (ProbComp.sample (H.gen.Coins n)) (fun ri =>
+        ProbComp.expect (ProbComp.sample (B.Coins n)) (fun r =>
+          payoff (H.gen.runAt n [] ri) r)) := by
+      congr 1
+      funext ri
+      exact hcoins (H.gen.runAt n [] ri)
+    _ = accept (H.collisionGame B n) := by
+      conv_rhs =>
+        simp only [accept_eq, CRH.collisionGame_eq, ProbComp.prob_bind, ProbComp.prob_pure,
+          decide_eq_true_eq]
+
+end TCSlib.Cryptography.Authentication.HashSignFill
diff --git a/TCSlib/Cryptography/Authentication/Signatures/HashAndSign/CollisionHandler.lean b/TCSlib/Cryptography/Authentication/Signatures/HashAndSign/CollisionHandler.lean
new file mode 100644
index 000000000..b8292c00c
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/Signatures/HashAndSign/CollisionHandler.lean
@@ -0,0 +1,541 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Games.Efficiency
+import TCSlib.Cryptography.Authentication.Signatures.Defs
+import TCSlib.Cryptography.Hashing.CollisionResistant
+import TCSlib.Cryptography.Asymptotic.CollectionsLemmas
+import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.FixedGame
+import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CodecReaders
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The collision-finding handler for hash-and-sign
+
+The non-interactive reduction in [PS10, Theorem 144.1] receives the hash index, samples
+signature keys, and answers the sole signing query itself. Its state remembers that query;
+the final output concatenates the query and the forged message for the CRH collision game.
+
+## Main definitions
+
+* `HashSignFill.collisionKey`, `collisionAdv`, `collisionHash`, `collisionRun`,
+  `collisionOut`: the string computations of the reduction.
+* `HashSignFill.collisionHandler`: their polynomial-time T1 handler.
+
+## Main results
+
+* The string equations and handler field equations expose every computation.
+* `HashSignFill.exists_collisionMachine`: T1 realizes this handler as a machine.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
+  January 2010, Theorem 144.1, collision-finding case.
+-/
+
+namespace TCSlib.Cryptography.Authentication.HashSignFill
+
+open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
+
+/-- The signature key word generated from the first `S.gen.coins(n)` bits of the
+context seed, with empty argument and advice,
+`collisionKey S c = S.gen.output (NUPPT.layout u [] [] (ω.take (S.gen.coins.eval u.length)))`,
+where `u = pairFstD c` and `ω = pairSndD (pairSndD c)` [PS10, Theorem 144.1]. -/
+def collisionKey (S : SignatureScheme) (c : List Bool) : List Bool :=
+  S.gen.output (NUPPT.layout (pairFstD c) [] []
+    ((pairSndD (pairSndD c)).take (S.gen.coins.eval (pairFstD c).length)))
+
+/-- `collisionKey S c` runs the original key generator on the parameter and the first
+generator-sized segment of the context seed:
+`collisionKey S c = S.gen.output (NUPPT.layout u [] [] (ω.take (S.gen.coins.eval u.length)))`,
+where `u = pairFstD c` and `ω = pairSndD (pairSndD c)`. -/
+theorem collisionKey_eq (S : SignatureScheme) (c : List Bool) :
+    collisionKey S c = S.gen.output (NUPPT.layout (pairFstD c) [] []
+      ((pairSndD (pairSndD c)).take (S.gen.coins.eval (pairFstD c).length))) := rfl
+
+/-- Generating the signature key from a context is polynomial-time:
+`PolyTimeComputable (collisionKey S)`, for `collisionKey S : List Bool → List Bool`.
+The tape segment is
+computed by the published polynomial-length take construction. -/
+theorem polyTimeComputable_collisionKey (S : SignatureScheme) :
+    PolyTimeComputable (collisionKey S) :=
+  let hW := polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD
+  let hT := ((polyTimeComputable_pairTakePoly S.gen.coins).comp'
+    (polyTimeComputable_pairFstD.pairEncode hW)).congr (fun _ =>
+      congrArg₂ (fun u w : List Bool => w.take (S.gen.coins.eval u.length))
+        (pairFstD_pairEncode _ _) (pairSndD_pairEncode _ _))
+  S.gen.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout
+    polyTimeComputable_pairFstD (polyTimeComputable_const [])
+    (polyTimeComputable_const []) hT)
+
+/-- When the context seed concatenates generator and signing tapes, `collisionKey` is
+exactly the original generator's run on its own tape:
+`collisionKey S (seedIn n i (List.ofFn rg ++ List.ofFn rs)) = S.gen.runAt n [] rg`. -/
+theorem collisionKey_seed (S : SignatureScheme) (n : ℕ) (i : List Bool)
+    (rg : S.gen.Coins n) (rs : S.sign.Coins n) :
+    collisionKey S (seedIn n i (List.ofFn rg ++ List.ofFn rs)) = S.gen.runAt n [] rg := by
+  simp only [collisionKey_eq, seedIn_eq, pairFstD_pairEncode, pairSndD_pairEncode,
+    List.length_replicate]
+  rw [← NUPPT.coinLen_eq S.gen n, List.take_left' List.length_ofFn,
+    S.gen_uniform.runAt_eq, NUPPT.layout_eq, NUPPT.advInput_eq]
+
+/-- The adversary receives `⟨pk, i⟩`, where the context supplies the hash index and
+`collisionKey` supplies the public signature key,
+`collisionAdv S c = pairEncode (pairFstD (collisionKey S c)) (pairFstD (pairSndD c))`
+[PS10, Theorem 144.1]. -/
+def collisionAdv (S : SignatureScheme) (c : List Bool) : List Bool :=
+  pairEncode (pairFstD (collisionKey S c)) (pairFstD (pairSndD c))
+
+/-- The adversary input is the original public key paired with the context index:
+`collisionAdv S c = pairEncode (pairFstD (collisionKey S c)) (pairFstD (pairSndD c))`. -/
+theorem collisionAdv_eq (S : SignatureScheme) (c : List Bool) :
+    collisionAdv S c =
+      pairEncode (pairFstD (collisionKey S c)) (pairFstD (pairSndD c)) := rfl
+
+/-- Pairing the generated public key with the index is polynomial-time:
+`PolyTimeComputable (collisionAdv S)`, for `collisionAdv S : List Bool → List Bool`. -/
+theorem polyTimeComputable_collisionAdv (S : SignatureScheme) :
+    PolyTimeComputable (collisionAdv S) :=
+  (polyTimeComputable_pairFstD.comp' (polyTimeComputable_collisionKey S)).pairEncode
+    (polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD)
+
+/-- At `seedIn n i ω`, the adversary input is `⟨pk, i⟩`, where the original generator
+runs with the first `S.gen.coins(n)` seed bits: `collisionAdv S (seedIn n i ω) =
+pairEncode (pairFstD (S.gen.output (NUPPT.layout (List.replicate n true) [] []
+(ω.take (S.gen.coins.eval n))))) i`. -/
+theorem collisionAdv_seedIn (S : SignatureScheme) (n : ℕ) (i ω : List Bool) :
+    collisionAdv S (seedIn n i ω) =
+      pairEncode (pairFstD (S.gen.output (NUPPT.layout (List.replicate n true) [] []
+        (ω.take (S.gen.coins.eval n))))) i := by
+  simp only [collisionAdv_eq, collisionKey_eq, seedIn_eq, pairFstD_pairEncode,
+    pairSndD_pairEncode, List.length_replicate]
+
+/-- On concatenated generator and signing tapes, the adversary receives the public key
+from that generator run paired with the supplied hash index:
+`collisionAdv S (seedIn n i (List.ofFn rg ++ List.ofFn rs)) =
+pairEncode (pairFstD (S.gen.runAt n [] rg)) i`. -/
+theorem collisionAdv_seed (S : SignatureScheme) (n : ℕ) (i : List Bool)
+    (rg : S.gen.Coins n) (rs : S.sign.Coins n) :
+    collisionAdv S (seedIn n i (List.ofFn rg ++ List.ofFn rs)) =
+      pairEncode (pairFstD (S.gen.runAt n [] rg)) i := by
+  rw [collisionAdv_eq, collisionKey_seed, seedIn_eq,
+    pairSndD_pairEncode, pairFstD_pairEncode]
+
+/-- The query hash in a handler-round word is the CRH evaluator padded to the signature
+message length: `collisionHash H S w = padStr S.msgLen u (H.eval (pairEncode u (pairEncode i x)))`,
+where `u = pairFstD (pairFstD w)`, `i = pairFstD (pairSndD (pairFstD w))` and
+`x = pairSndD (pairSndD (pairSndD w))`.
+The theorem's length hypothesis later identifies this with `H.hash`
+[PS10, Theorem 144.1]. -/
+def collisionHash (H : CRH) (S : SignatureScheme) (w : List Bool) : List Bool :=
+  padStr S.msgLen (pairFstD (pairFstD w))
+    (H.eval (pairEncode (pairFstD (pairFstD w))
+      (pairEncode (pairFstD (pairSndD (pairFstD w)))
+        (pairSndD (pairSndD (pairSndD w))))))
+
+/-- The query hash runs the evaluator at the context parameter and index on the query
+word and pads its output to the signature message length:
+`collisionHash H S w = padStr S.msgLen u (H.eval (pairEncode u (pairEncode i x)))`, where
+`u = pairFstD (pairFstD w)`, `i = pairFstD (pairSndD (pairFstD w))` and
+`x = pairSndD (pairSndD (pairSndD w))`. -/
+theorem collisionHash_eq (H : CRH) (S : SignatureScheme) (w : List Bool) :
+    collisionHash H S w = padStr S.msgLen (pairFstD (pairFstD w))
+      (H.eval (pairEncode (pairFstD (pairFstD w))
+        (pairEncode (pairFstD (pairSndD (pairFstD w)))
+          (pairSndD (pairSndD (pairSndD w)))))) := rfl
+
+/-- Evaluating and padding the query hash is polynomial-time by the CRH evaluator and
+the published padding construction: `PolyTimeComputable (collisionHash H S)`, for
+`collisionHash H S : List Bool → List Bool`. -/
+theorem polyTimeComputable_collisionHash (H : CRH) (S : SignatureScheme) :
+    PolyTimeComputable (collisionHash H S) :=
+  let hU := polyTimeComputable_pairFstD.comp' polyTimeComputable_pairFstD
+  let hI := polyTimeComputable_pairFstD.comp'
+    (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairFstD)
+  let hX := polyTimeComputable_pairSndD.comp'
+    (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD)
+  (HashSignForward.polyTimeComputable_hashWord H S hU hI hX).congr (fun w =>
+    (HashSignForward.hashWord_eq H S _ _ _).trans (collisionHash_eq H S w).symm)
+
+/-- A collision-finder round signs the query hash using the remaining seed and records
+the query as its new state, `collisionRun H S w = pairEncode (padStr S.sigLen u
+(S.sign.output (NUPPT.layout u (pairEncode (pairSndD (collisionKey S (pairFstD w)))
+(collisionHash H S w)) [] (ω.drop (S.gen.coins.eval u.length))))) x`, where
+`u = pairFstD (pairFstD w)`, `ω = pairSndD (pairSndD (pairFstD w))` and
+`x = pairSndD (pairSndD (pairSndD w))` [PS10, Theorem 144.1]. -/
+def collisionRun (H : CRH) (S : SignatureScheme) (w : List Bool) : List Bool :=
+  pairEncode
+    (padStr S.sigLen (pairFstD (pairFstD w))
+      (S.sign.output (NUPPT.layout (pairFstD (pairFstD w))
+        (pairEncode (pairSndD (collisionKey S (pairFstD w))) (collisionHash H S w)) []
+        ((pairSndD (pairSndD (pairFstD w))).drop
+          (S.gen.coins.eval (pairFstD (pairFstD w)).length)))))
+    (pairSndD (pairSndD (pairSndD w)))
+
+/-- A round returns the padded original signature and the queried message:
+`collisionRun H S w = pairEncode (padStr S.sigLen u (S.sign.output (NUPPT.layout u
+(pairEncode (pairSndD (collisionKey S (pairFstD w))) (collisionHash H S w)) []
+(ω.drop (S.gen.coins.eval u.length))))) x`, where `u = pairFstD (pairFstD w)`,
+`ω = pairSndD (pairSndD (pairFstD w))` and `x = pairSndD (pairSndD (pairSndD w))`. -/
+theorem collisionRun_eq (H : CRH) (S : SignatureScheme) (w : List Bool) :
+    collisionRun H S w = pairEncode
+      (padStr S.sigLen (pairFstD (pairFstD w))
+        (S.sign.output (NUPPT.layout (pairFstD (pairFstD w))
+          (pairEncode (pairSndD (collisionKey S (pairFstD w))) (collisionHash H S w)) []
+          ((pairSndD (pairSndD (pairFstD w))).drop
+            (S.gen.coins.eval (pairFstD (pairFstD w)).length)))))
+      (pairSndD (pairSndD (pairSndD w))) := rfl
+
+/-- The collision-finder round is polynomial-time: `PolyTimeComputable (collisionRun H S)`,
+for `collisionRun H S : List Bool → List Bool`. It uses a polynomial-length coin suffix,
+the polynomial-time signer and padding, then pairs the result with the query.
+
+**Proof sketch.** Write `u` for the parameter word, `ω` for the context seed and `x` for the
+query word of a round input; each is a composition of pair projections, hence polynomial-time.
+The signer's tape is `ω` with its first `S.gen.coins(|u|)` bits dropped, computed by the
+published polynomial-length drop construction on the pair `⟨u, ω⟩`. The secret key is the
+second component of the polynomial-time `collisionKey`, and the query hash is polynomial-time
+(`polyTimeComputable_collisionHash`). The original signer's output on the layout of `u`, the
+pair of key and hash, empty advice and that tape is then polynomial-time, and so is padding
+it to `S.sigLen(|u|)` bits by the published padding construction on `⟨u, ·⟩`. Pairing the
+padded signature with `x` gives the round. -/
+theorem polyTimeComputable_collisionRun (H : CRH) (S : SignatureScheme) :
+    PolyTimeComputable (collisionRun H S) :=
+  let hU := polyTimeComputable_pairFstD.comp' polyTimeComputable_pairFstD
+  let hW := polyTimeComputable_pairSndD.comp'
+    (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairFstD)
+  let hR := ((polyTimeComputable_pairDropPoly S.gen.coins).comp'
+    (hU.pairEncode hW)).congr (fun _ =>
+      congrArg₂ (fun u r : List Bool => r.drop (S.gen.coins.eval u.length))
+        (pairFstD_pairEncode _ _) (pairSndD_pairEncode _ _))
+  let hK := polyTimeComputable_pairSndD.comp'
+    ((polyTimeComputable_collisionKey S).comp' polyTimeComputable_pairFstD)
+  let hSig := S.sign.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout hU
+    (hK.pairEncode (polyTimeComputable_collisionHash H S)) (polyTimeComputable_const []) hR)
+  let hPad := ((polyTimeComputable_padStr S.sigLen).comp' (hU.pairEncode hSig)).congr
+    (fun _ => congrArg₂ (padStr S.sigLen)
+      (pairFstD_pairEncode _ _) (pairSndD_pairEncode _ _))
+  hPad.pairEncode (polyTimeComputable_pairSndD.comp'
+    (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD))
+
+/-- The collision output concatenates the remembered query with the first `H.domLen(n)`
+bits of the adversary's final word, `collisionOut H w = pairFstD (pairSndD w) ++
+(pairSndD (pairSndD w)).take (H.domLen.eval (pairFstD (pairFstD w)).length)`
+[PS10, Theorem 144.1]. -/
+def collisionOut (H : CRH) (w : List Bool) : List Bool :=
+  pairFstD (pairSndD w) ++
+    (pairSndD (pairSndD w)).take (H.domLen.eval (pairFstD (pairFstD w)).length)
+
+/-- The collision output is the state followed by the message prefix of the forgery:
+`collisionOut H w = pairFstD (pairSndD w) ++
+(pairSndD (pairSndD w)).take (H.domLen.eval (pairFstD (pairFstD w)).length)`. -/
+theorem collisionOut_eq (H : CRH) (w : List Bool) :
+    collisionOut H w = pairFstD (pairSndD w) ++
+      (pairSndD (pairSndD w)).take (H.domLen.eval (pairFstD (pairFstD w)).length) := rfl
+
+/-- Reading a polynomial-length forgery prefix and appending it to the stored query is
+polynomial-time: `PolyTimeComputable (collisionOut H)`, for
+`collisionOut H : List Bool → List Bool`. -/
+theorem polyTimeComputable_collisionOut (H : CRH) :
+    PolyTimeComputable (collisionOut H) :=
+  let hU := polyTimeComputable_pairFstD.comp' polyTimeComputable_pairFstD
+  let hA := polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD
+  let hT := ((polyTimeComputable_pairTakePoly H.domLen).comp' (hU.pairEncode hA)).congr
+    (fun _ => congrArg₂ (fun u a : List Bool => a.take (H.domLen.eval u.length))
+      (pairFstD_pairEncode _ _) (pairSndD_pairEncode _ _))
+  (polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD).append hT
+
+/-- The T1 collision finder samples signature-generation and signing coins, remembers one
+domain-width query, and emits the query followed by the forged message: its fields are
+`stateLen = H.domLen`, `seedLen = .add S.gen.coins S.sign.coins`, `init _ = zeroBits _`,
+`run = collisionRun H S`, `advIn = collisionAdv S` and `out = collisionOut H`
+[PS10, Theorem 144.1]. -/
+def collisionHandler (H : CRH) (S : SignatureScheme) :
+    PolyHandler 1 (fun _ => H.domLen) (fun _ => S.sigLen) where
+  stateLen := H.domLen
+  seedLen := .add S.gen.coins S.sign.coins
+  init _ := zeroBits _
+  run := collisionRun H S
+  poly := polyTimeComputable_collisionRun H S
+  advIn := collisionAdv S
+  advIn_poly := polyTimeComputable_collisionAdv S
+  out := collisionOut H
+  out_poly := polyTimeComputable_collisionOut H
+
+attribute [simps (config := { isSimp := false }) stateLen seedLen init run advIn out]
+  collisionHandler
+
+/-- On a well-formed round input, the collision handler returns the padded signature on
+the query hash and stores exactly the query:
+`(collisionHandler H S).run (PolyHandler.input n i ω s j m) = pairEncode (padStr S.sigLen u σ) m`,
+where `u = List.replicate n true` and
+`σ = S.sign.output (NUPPT.layout u (pairEncode (pairSndD (collisionKey S (seedIn n i ω)))
+(padStr S.msgLen u (H.eval (pairEncode u (pairEncode i m))))) [] (ω.drop (S.gen.coins.eval n)))`.
+The generator reads the seed prefix and
+the signer reads its suffix; the old state and oracle index are ignored. -/
+theorem collisionHandler_run_input (H : CRH) (S : SignatureScheme) (n : ℕ)
+    (i ω s : List Bool) (j : Fin 1) (m : List Bool) :
+    (collisionHandler H S).run (PolyHandler.input n i ω s j m) =
+      pairEncode
+        (padStr S.sigLen (List.replicate n true)
+          (S.sign.output (NUPPT.layout (List.replicate n true)
+            (pairEncode
+              (pairSndD (collisionKey S (seedIn n i ω)))
+              (padStr S.msgLen (List.replicate n true)
+                (H.eval (pairEncode (List.replicate n true) (pairEncode i m))))) []
+            (ω.drop (S.gen.coins.eval n))))) m := by
+  simp only [collisionHandler_run, collisionRun_eq, collisionHash_eq, PolyHandler.input_eq,
+    seedIn_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
+
+/-- The typed signature returned by the collision handler: run the original signer on the
+hashed message with the seed suffix and pad its output to `S.sigLen(n)` bits,
+`collisionReply H S n i ω m = padFin (S.sigLen.eval n) σ`, where `u = List.replicate n true` and
+`σ = S.sign.output (NUPPT.layout u (pairEncode (pairSndD (collisionKey S (seedIn n i ω)))
+(padStr S.msgLen u (H.eval (pairEncode u (pairEncode i m))))) [] (ω.drop (S.gen.coins.eval n)))`. -/
+def collisionReply (H : CRH) (S : SignatureScheme) (n : ℕ) (i ω m : List Bool) :
+    Fin (S.sigLen.eval n) → Bool :=
+  padFin (S.sigLen.eval n)
+    (S.sign.output (NUPPT.layout (List.replicate n true)
+      (pairEncode (pairSndD (collisionKey S (seedIn n i ω)))
+        (padStr S.msgLen (List.replicate n true)
+          (H.eval (pairEncode (List.replicate n true) (pairEncode i m))))) []
+      (ω.drop (S.gen.coins.eval n))))
+
+/-- The typed reply is the original signer output padded to the signature length:
+`collisionReply H S n i ω m = padFin (S.sigLen.eval n) σ`, where `u = List.replicate n true` and
+`σ = S.sign.output (NUPPT.layout u (pairEncode (pairSndD (collisionKey S (seedIn n i ω)))
+(padStr S.msgLen u (H.eval (pairEncode u (pairEncode i m))))) [] (ω.drop (S.gen.coins.eval n)))`. -/
+theorem collisionReply_eq (H : CRH) (S : SignatureScheme) (n : ℕ) (i ω m : List Bool) :
+    collisionReply H S n i ω m = padFin (S.sigLen.eval n)
+      (S.sign.output (NUPPT.layout (List.replicate n true)
+        (pairEncode (pairSndD (collisionKey S (seedIn n i ω)))
+          (padStr S.msgLen (List.replicate n true)
+            (H.eval (pairEncode (List.replicate n true) (pairEncode i m))))) []
+        (ω.drop (S.gen.coins.eval n)))) := rfl
+
+/-- With the generator and signing tapes concatenated into the context seed, the collision
+handler's reply is the fixed experiment's hashed reply under those same generated keys:
+`collisionReply H S n i (List.ofFn rg ++ List.ofFn rs) (List.ofFn m) =
+hashedReply H S n (pairSndD (S.gen.runAt n [] rg)) i rs m`. -/
+theorem collisionReply_seed (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
+    (rg : S.gen.Coins n) (rs : S.sign.Coins n) (m : Fin (H.domLen.eval n) → Bool) :
+    collisionReply H S n i (List.ofFn rg ++ List.ofFn rs) (List.ofFn m) =
+      hashedReply H S n (pairSndD (S.gen.runAt n [] rg)) i rs m := by
+  rw [collisionReply_eq, collisionKey_seed, hashedReply_eq,
+    ← NUPPT.coinLen_eq S.gen n, List.drop_left' List.length_ofFn,
+    S.sign_uniform.runAt_eq, HashSignForward.hashWord_eq,
+    NUPPT.layout_eq, NUPPT.advInput_eq]
+
+/-- Encoding the typed reply gives exactly the padded signature word emitted by a
+collision-handler round: `List.ofFn (collisionReply H S n i ω m) = padStr S.sigLen u σ`, where
+`u = List.replicate n true` and
+`σ = S.sign.output (NUPPT.layout u (pairEncode (pairSndD (collisionKey S (seedIn n i ω)))
+(padStr S.msgLen u (H.eval (pairEncode u (pairEncode i m))))) [] (ω.drop (S.gen.coins.eval n)))`. -/
+theorem ofFn_collisionReply (H : CRH) (S : SignatureScheme) (n : ℕ) (i ω m : List Bool) :
+    List.ofFn (collisionReply H S n i ω m) =
+      padStr S.sigLen (List.replicate n true)
+        (S.sign.output (NUPPT.layout (List.replicate n true)
+          (pairEncode (pairSndD (collisionKey S (seedIn n i ω)))
+            (padStr S.msgLen (List.replicate n true)
+              (H.eval (pairEncode (List.replicate n true) (pairEncode i m))))) []
+          (ω.drop (S.gen.coins.eval n)))) := by
+  simp only [collisionReply_eq, ofFn_padFin_eq_take, padStr_eq, List.length_replicate]
+
+/-- The collision handler answers each typed query with its padded original signature and
+sets the state to that query, asking no further oracle: `(collisionHandler H S).impl n i ω j m s =
+.pure (collisionReply H S n i (List.ofFn ω) (List.ofFn m), m)`. -/
+theorem collisionHandler_impl (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
+    (ω : Fin ((collisionHandler H S).seedLen.eval n) → Bool) (j : Fin 1)
+    (m s : Fin (H.domLen.eval n) → Bool) :
+    (collisionHandler H S).impl n i ω j m s =
+      .pure (collisionReply H S n i (List.ofFn ω) (List.ofFn m), m) := by
+  rw [PolyHandler.impl_apply]
+  congr 1
+  apply PolyHandler.answer_of_run_eq
+  rw [collisionHandler_run_input, ofFn_collisionReply]
+
+/-- Finalization returns the remembered query followed by the domain-width message prefix
+of the adversary's output: `(collisionHandler H S).result n i ω s a =
+List.ofFn s ++ (List.ofFn a).take (H.domLen.eval n)`. -/
+theorem collisionHandler_result (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
+    (ω : Fin ((collisionHandler H S).seedLen.eval n) → Bool)
+    (s : Fin (H.domLen.eval n) → Bool) {d : ℕ} (a : Fin d → Bool) :
+    (collisionHandler H S).result n i ω s a =
+      List.ofFn s ++ (List.ofFn a).take (H.domLen.eval n) := by
+  simp only [PolyHandler.result_eq, collisionHandler_out, collisionOut_eq, seedIn_eq,
+    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
+
+/-- The collision handler and common fixed-tape transcript return the same adversary
+output: if `List.ofFn ω = List.ofFn rg ++ List.ofFn rs`, then `∃ a s L,
+simulate ((collisionHandler H S).impl n i ω) (A.toCompOn cod n 1
+((collisionHandler H S).advInput n i ω) rA) ((collisionHandler H S).init n) = .pure (a, s) ∧
+transcript H S A n pk sk i rs rA = .pure (a, ((), L)) ∧
+(L = [] ∨ ∃ j m, L = [⟨j, m, hashedReply H S n sk i rs m⟩] ∧ s = m)`, where
+`pk = pairFstD (S.gen.runAt n [] rg)`, `sk = pairSndD (S.gen.runAt n [] rg)` and
+`cod = bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
+(H.domLen.eval n + S.sigLen.eval n)`.
+Their query log is empty, or consists of one query which is exactly the handler's
+final state, answered by the same original signing tape.
+
+**Proof sketch.** The adversary's computation has at most one query. If it returns
+immediately, both simulations return that value and the transcript log is empty. Otherwise,
+the seed equations identify the handler's response with the fixed experiment's response;
+the handler stores the query while the fixed experiment logs it. Both continuations
+therefore return the same function of that response. -/
+theorem collisionHandler_transcript (H : CRH) (S : SignatureScheme) (A : NUPPT) (n : ℕ)
+    (i : List Bool) (rg : S.gen.Coins n) (rs : S.sign.Coins n) (rA : A.Coins n)
+    (ω : Fin ((collisionHandler H S).seedLen.eval n) → Bool)
+    (hω : List.ofFn ω = List.ofFn rg ++ List.ofFn rs) :
+    ∃ (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool)
+      (s : Fin (H.domLen.eval n) → Bool)
+      (L : QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
+        (fun _ => S.sigLen.eval n))),
+      simulate ((collisionHandler H S).impl n i ω)
+          (A.toCompOn (bitCodec (fun _ : Fin 1 => H.domLen.eval n)
+            (fun _ => S.sigLen.eval n) (H.domLen.eval n + S.sigLen.eval n)) n 1
+            ((collisionHandler H S).advInput n i ω) rA) ((collisionHandler H S).init n) =
+          .pure (a, s) ∧
+        transcript H S A n (pairFstD (S.gen.runAt n [] rg))
+          (pairSndD (S.gen.runAt n [] rg)) i rs rA = .pure (a, ((), L)) ∧
+        (L = [] ∨ ∃ (j : Fin 1) (m : Fin (H.domLen.eval n) → Bool),
+          L = [⟨j, m, hashedReply H S n (pairSndD (S.gen.runAt n [] rg)) i rs m⟩] ∧ s = m) := by
+  have hinput : (collisionHandler H S).advInput n i ω =
+      pairEncode (pairFstD (S.gen.runAt n [] rg)) i := by
+    rw [PolyHandler.advInput_eq, collisionHandler_advIn, hω, collisionAdv_seed]
+  let c := A.toCompOn (bitCodec (fun _ : Fin 1 => H.domLen.eval n)
+    (fun _ => S.sigLen.eval n) (H.domLen.eval n + S.sigLen.eval n)) n 1
+    (pairEncode (pairFstD (S.gen.runAt n [] rg)) i) rA
+  have hc : c.CostBoundedBy (fun _ => 1) 1 := A.toCompOn_costBoundedBy _ n 1 _ rA
+  rcases one_query_cases c hc with ⟨a, hcase⟩ | ⟨j, m, f, hcase⟩
+  all_goals dsimp only [c] at hcase
+  · refine ⟨a, (collisionHandler H S).init n, [], ?_, ?_, Or.inl rfl⟩
+    · rw [hinput, hcase, simulate_pure]
+    · rw [transcript_eq, hcase, simulate_pure]
+  · let y := hashedReply H S n (pairSndD (S.gen.runAt n [] rg)) i rs m
+    refine ⟨f y, m, [⟨j, m, y⟩], ?_, ?_, Or.inr ⟨j, m, rfl, rfl⟩⟩
+    · rw [hinput, hcase, simulate_query, collisionHandler_impl, hω, collisionReply_seed,
+        OracleComp.pure_bind, simulate_pure]
+    · rw [transcript_eq, hcase]
+      simp only [simulate_query, QueryImpl.withLog_apply, fixedSign_apply,
+        OracleComp.pure_bind, simulate_pure, List.nil_append]
+      rfl
+
+/-- If the common transcript is fresh and contains a query with the forged message's
+hash, the collision handler's final output satisfies the CRH game's exact collision
+predicate on the full domain: given `∀ n i x, H.inDom n i x = true`,
+`L = [] ∨ ∃ j m, L = [⟨j, m, hashedReply H S n sk i rs m⟩] ∧ s = m`,
+`∀ e ∈ L, e.2.1 ≠ (splitBits a).1` and `∃ e ∈ L, H.hash n i e.2.1 = H.hash n i (splitBits a).1`,
+then `H.inDom n i x₁ = true ∧ H.inDom n i x₂ = true ∧ x₁ ≠ x₂ ∧ H.hash n i x₁ = H.hash n i x₂`,
+where `(x₁, x₂) = splitBits (padFin (H.domLen.eval n + H.domLen.eval n)
+((collisionHandler H S).result n i ω s a))` [PS10, Theorem 144.1, collision case].
+
+**Proof sketch.** The equal-hash witness rules out an empty log. The one-query invariant
+then identifies its query with the final handler state. Freshness makes that query distinct
+from the forged message. The finalization reader and fixed-width concatenation reader show
+that the CRH game decodes precisely these two messages. Full domain membership supplies
+the remaining two clauses of the collision predicate. -/
+theorem collisionHandler_collision (H : CRH) (S : SignatureScheme)
+    (hdom : ∀ n i x, H.inDom n i x = true) (n : ℕ) (sk i : List Bool)
+    (rs : S.sign.Coins n) (ω : Fin ((collisionHandler H S).seedLen.eval n) → Bool)
+    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) (s : Fin (H.domLen.eval n) → Bool)
+    (L : QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)))
+    (hinv : L = [] ∨ ∃ (j : Fin 1) (m : Fin (H.domLen.eval n) → Bool),
+      L = [⟨j, m, hashedReply H S n sk i rs m⟩] ∧ s = m)
+    (hfresh : ∀ e ∈ L, e.2.1 ≠ (splitBits a).1)
+    (hsame : ∃ e ∈ L, H.hash n i e.2.1 = H.hash n i (splitBits a).1) :
+    let xx := splitBits (padFin (H.domLen.eval n + H.domLen.eval n)
+      ((collisionHandler H S).result n i ω s a))
+    H.inDom n i xx.1 = true ∧ H.inDom n i xx.2 = true ∧ xx.1 ≠ xx.2 ∧
+      H.hash n i xx.1 = H.hash n i xx.2 := by
+  rcases hinv with hnil | ⟨j, m, hL, hs⟩
+  · obtain ⟨e, he, _⟩ := hsame
+    rw [hnil] at he
+    exact False.elim (List.not_mem_nil he)
+  · subst L
+    subst s
+    obtain ⟨e, he, hhash⟩ := hsame
+    have heq := List.mem_singleton.mp he
+    subst e
+    have hne : m ≠ (splitBits a).1 := hfresh _ (List.mem_singleton_self _)
+    have hp : (List.ofFn a).take (H.domLen.eval n) = List.ofFn (splitBits a).1 :=
+      (EffFill.ofFn_take_drop_add a).1.trans
+        (congrArg List.ofFn (funext fun j => splitBits_fst a j)).symm
+    have hdecode : splitBits (padFin (H.domLen.eval n + H.domLen.eval n)
+        ((collisionHandler H S).result n i ω m a)) = (m, (splitBits a).1) := by
+      rw [collisionHandler_result, hp, splitBits_pad_concat]
+    dsimp only
+    rw [hdecode]
+    exact ⟨hdom n i m, hdom n i _, hne, hhash⟩
+
+/-- T1 realizes the collision handler as a machine: on matching seed/adversary coins,
+its output equals `collisionHandler.result` after the deterministic simulation,
+`∃ B : NUPPT, ∀ n, ∃ φ : (Fin (K.seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n, ∀ i ω r,
+∃ a s, simulate (K.impl n i ω) (A.toCompOn cod n ((.const 1 : PolyExpr).eval n)
+(K.advInput n i ω) r) (K.init n) = .pure (a, s) ∧ B.runAt n i (φ (ω, r)) = K.result n i ω s a`,
+where `K = collisionHandler H S` and `cod = bitCodec (fun _ : Fin 1 => H.domLen.eval n)
+(fun _ : Fin 1 => S.sigLen.eval n) ((PolyExpr.add H.domLen S.sigLen).eval n)`. This is
+the machine-construction part of [PS10, Theorem 144.1], before relating the collision event. -/
+theorem exists_collisionMachine (H : CRH) (S : SignatureScheme) (A : NUPPT) :
+    ∃ B : NUPPT, ∀ n : ℕ, ∃ φ :
+      (Fin ((collisionHandler H S).seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n,
+      ∀ (i : List Bool) (ω : Fin ((collisionHandler H S).seedLen.eval n) → Bool)
+        (r : A.Coins n),
+        ∃ (a : Fin ((PolyExpr.add H.domLen S.sigLen).eval n) → Bool)
+          (s : Fin ((collisionHandler H S).stateLen.eval n) → Bool),
+          simulate ((collisionHandler H S).impl n i ω)
+              (A.toCompOn (bitCodec (fun _ : Fin 1 => H.domLen.eval n)
+                (fun _ : Fin 1 => S.sigLen.eval n) ((PolyExpr.add H.domLen S.sigLen).eval n))
+                n ((.const 1 : PolyExpr).eval n) ((collisionHandler H S).advInput n i ω) r)
+              ((collisionHandler H S).init n) = .pure (a, s) ∧
+            B.runAt n i (φ (ω, r)) = (collisionHandler H S).result n i ω s a :=
+  exists_handlerMachine A (.const 1) (fun _ => H.domLen) (fun _ => S.sigLen)
+    (.add H.domLen S.sigLen) (collisionHandler H S)
+
+/-- T1 supplies a collision machine whose output is the finalization of the common
+fixed-tape transcript: `∃ B : NUPPT, ∀ n, ∃ φ : (Fin (K.seedLen.eval n) → Bool) × A.Coins n ≃
+B.Coins n, ∀ i rg rs ω rA, List.ofFn ω = List.ofFn rg ++ List.ofFn rs → ∃ a s L,
+transcript H S A n pk sk i rs rA = .pure (a, ((), L)) ∧
+(L = [] ∨ ∃ j m, L = [⟨j, m, hashedReply H S n sk i rs m⟩] ∧ s = m) ∧
+B.runAt n i (φ (ω, rA)) = K.result n i ω s a`, where `K = collisionHandler H S`,
+`pk = pairFstD (S.gen.runAt n [] rg)` and `sk = pairSndD (S.gen.runAt n [] rg)`.
+Its coins correspond bijectively to the handler seed and adversary
+tape; concatenated generator/signing tapes give the same adversary output and one-query
+invariant as `collisionHandler_transcript` [PS10, Theorem 144.1].
+
+**Proof sketch.** Apply the T1 machine contract and the common-transcript coupling to the
+same seed and adversary tape. Both describe the same deterministic handler simulation as
+a pure computation. Injectivity of the pure constructor identifies their final outputs
+and states, so the T1 run equation becomes the claimed common-transcript run equation. -/
+theorem exists_collisionMachine_transcript (H : CRH) (S : SignatureScheme) (A : NUPPT) :
+    ∃ B : NUPPT, ∀ n : ℕ, ∃ φ :
+      (Fin ((collisionHandler H S).seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n,
+      ∀ (i : List Bool) (rg : S.gen.Coins n) (rs : S.sign.Coins n)
+        (ω : Fin ((collisionHandler H S).seedLen.eval n) → Bool) (rA : A.Coins n),
+        List.ofFn ω = List.ofFn rg ++ List.ofFn rs →
+        ∃ (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool)
+          (s : Fin (H.domLen.eval n) → Bool)
+          (L : QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
+            (fun _ => S.sigLen.eval n))),
+          transcript H S A n (pairFstD (S.gen.runAt n [] rg))
+            (pairSndD (S.gen.runAt n [] rg)) i rs rA = .pure (a, ((), L)) ∧
+          (L = [] ∨ ∃ (j : Fin 1) (m : Fin (H.domLen.eval n) → Bool),
+            L = [⟨j, m, hashedReply H S n (pairSndD (S.gen.runAt n [] rg)) i rs m⟩] ∧ s = m) ∧
+          B.runAt n i (φ (ω, rA)) = (collisionHandler H S).result n i ω s a := by
+  obtain ⟨B, hB⟩ := exists_collisionMachine H S A
+  refine ⟨B, fun n => ?_⟩
+  obtain ⟨φ, hφ⟩ := hB n
+  refine ⟨φ, fun i rg rs ω rA hω => ?_⟩
+  simp only [PolyExpr.eval_add, PolyExpr.eval_const] at hφ
+  obtain ⟨a₀, s₀, hsim, hrun⟩ := hφ i ω rA
+  obtain ⟨a, s, L, hsame, ht, hinv⟩ :=
+    collisionHandler_transcript H S A n i rg rs rA ω hω
+  have heq : (a₀, s₀) = (a, s) := OracleComp.pure.inj (hsim.symm.trans hsame)
+  obtain ⟨ha, hs⟩ := Prod.mk.inj heq
+  refine ⟨a, s, L, ht, hinv, ?_⟩
+  simpa only [ha, hs] using hrun
+
+end TCSlib.Cryptography.Authentication.HashSignFill
diff --git a/TCSlib/Cryptography/Authentication/Signatures/HashAndSign/FixedGame.lean b/TCSlib/Cryptography/Authentication/Signatures/HashAndSign/FixedGame.lean
new file mode 100644
index 000000000..06dce554d
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/Signatures/HashAndSign/FixedGame.lean
@@ -0,0 +1,199 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.ForwardHandler
+import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.OneQuerySampling
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# A common transcript for the hash-and-sign reductions
+
+Fix the signature keys, hash index, adversary tape and signing tape. The resulting
+transcript is shared by the collision-finding and signature-forging reductions of
+[PS10, Theorem 144.1]. Because the adversary makes at most one query, sampling signing
+coins per query has the same law as drawing the signing tape before this transcript.
+
+## Main definitions
+
+* `HashSignFill.hashedReply`: the original signer applied to the hashed message.
+* `HashSignFill.fixedSign`, `sampledHashSign`: the fixed-tape and fresh-tape signing oracles.
+* `HashSignFill.transcript`: the adversary's output and full signing-query log.
+* `HashSignFill.Success`: acceptance and message freshness in a common transcript.
+
+## Main results
+
+* The defining equations and application readers expose each computation.
+* `HashSignFill.expect_sampledHashSign_eq_transcript`: signing randomness may be sampled
+  before the common transcript.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 144.1, book pp. 144–145.
+-/
+
+namespace TCSlib.Cryptography.Authentication.HashSignFill
+
+open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
+
+/-- With signing tape `rs` fixed, hash `m` and run the original signer under `sk`, padding
+the signature to the declared signature width, `hashedReply H S n sk i rs m =
+padFin (S.sigLen.eval n) (S.sign.runAt n (pairEncode sk (hashWord H S u i (List.ofFn m))) rs)`,
+where `u = List.replicate n true` and `hashWord = HashSignForward.hashWord`
+[PS10, Theorem 144.1]. -/
+def hashedReply (H : CRH) (S : SignatureScheme) (n : ℕ) (sk i : List Bool)
+    (rs : S.sign.Coins n) (m : Fin (H.domLen.eval n) → Bool) :
+    Fin (S.sigLen.eval n) → Bool :=
+  padFin (S.sigLen.eval n) (S.sign.runAt n
+    (pairEncode sk (HashSignForward.hashWord H S (List.replicate n true) i (List.ofFn m))) rs)
+
+/-- The fixed-tape hashed reply is the padded original signer output on `⟨sk, h_i(m)⟩`:
+`hashedReply H S n sk i rs m =
+padFin (S.sigLen.eval n) (S.sign.runAt n (pairEncode sk (hashWord H S u i (List.ofFn m))) rs)`,
+where `u = List.replicate n true` and `hashWord = HashSignForward.hashWord`. -/
+theorem hashedReply_eq (H : CRH) (S : SignatureScheme) (n : ℕ) (sk i : List Bool)
+    (rs : S.sign.Coins n) (m : Fin (H.domLen.eval n) → Bool) :
+    hashedReply H S n sk i rs m =
+      padFin (S.sigLen.eval n) (S.sign.runAt n
+        (pairEncode sk (HashSignForward.hashWord H S (List.replicate n true) i (List.ofFn m)))
+        rs) := rfl
+
+/-- The fixed-tape signing oracle answers every query using `hashedReply` and has trivial
+state, `fixedSign H S n sk i rs j m s = .pure (hashedReply H S n sk i rs m, ())`
+[PS10, Theorem 144.1]. -/
+def fixedSign (H : CRH) (S : SignatureScheme) (n : ℕ) (sk i : List Bool)
+    (rs : S.sign.Coins n) :
+    QueryImpl (bitSpec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n))
+      Unit unifSpec :=
+  fun _ m _ => .pure (hashedReply H S n sk i rs m, ())
+
+/-- The fixed-tape oracle is the pure answer function `m ↦ (hashedReply m, ())`:
+`fixedSign H S n sk i rs = fun _ m _ => .pure (hashedReply H S n sk i rs m, ())`. -/
+theorem fixedSign_eq (H : CRH) (S : SignatureScheme) (n : ℕ) (sk i : List Bool)
+    (rs : S.sign.Coins n) :
+    fixedSign H S n sk i rs = fun _ m _ => .pure (hashedReply H S n sk i rs m, ()) := rfl
+
+/-- Applying the fixed-tape oracle returns the hashed signature and trivial state:
+`fixedSign H S n sk i rs j m s = .pure (hashedReply H S n sk i rs m, ())`. -/
+theorem fixedSign_apply (H : CRH) (S : SignatureScheme) (n : ℕ) (sk i : List Bool)
+    (rs : S.sign.Coins n) (j : Fin 1) (m : Fin (H.domLen.eval n) → Bool) (s : Unit) :
+    fixedSign H S n sk i rs j m s = .pure (hashedReply H S n sk i rs m, ()) := rfl
+
+/-- The common transcript runs `A` on `⟨pk,i⟩` with one query allowed, fixed signing tape,
+and a full query log, `transcript H S A n pk sk i rs rA =
+simulate (fixedSign H S n sk i rs).withLog (A.toCompOn cod n 1 (pairEncode pk i) rA) ((), [])`,
+where `cod = bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
+(H.domLen.eval n + S.sigLen.eval n)` [PS10, Theorem 144.1]. -/
+def transcript (H : CRH) (S : SignatureScheme) (A : NUPPT) (n : ℕ)
+    (pk sk i : List Bool) (rs : S.sign.Coins n) (rA : A.Coins n) :
+    ProbComp ((Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
+      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
+        (fun _ => S.sigLen.eval n)))) :=
+  simulate (fixedSign H S n sk i rs).withLog
+    (A.toCompOn (bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
+      (H.domLen.eval n + S.sigLen.eval n)) n 1 (pairEncode pk i) rA) ((), [])
+
+/-- The common transcript is the logged simulation with the fixed-tape signing oracle:
+`transcript H S A n pk sk i rs rA =
+simulate (fixedSign H S n sk i rs).withLog (A.toCompOn cod n 1 (pairEncode pk i) rA) ((), [])`,
+where `cod = bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
+(H.domLen.eval n + S.sigLen.eval n)`. -/
+theorem transcript_eq (H : CRH) (S : SignatureScheme) (A : NUPPT) (n : ℕ)
+    (pk sk i : List Bool) (rs : S.sign.Coins n) (rA : A.Coins n) :
+    transcript H S A n pk sk i rs rA =
+      simulate (fixedSign H S n sk i rs).withLog
+        (A.toCompOn (bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
+          (H.domLen.eval n + S.sigLen.eval n)) n 1 (pairEncode pk i) rA) ((), []) := rfl
+
+/-- The fresh-tape hash-and-sign oracle samples an original signing tape independently
+for every query and keeps trivial state, `sampledHashSign H S n sk i = QueryImpl.ofComp
+fun _ m => (ProbComp.sample (S.sign.Coins n)).bind fun rs => .pure (hashedReply H S n sk i rs m)`
+[PS10, Theorem 144.1]. -/
+noncomputable def sampledHashSign (H : CRH) (S : SignatureScheme) (n : ℕ) (sk i : List Bool) :
+    QueryImpl (bitSpec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n))
+      Unit unifSpec :=
+  QueryImpl.ofComp fun _ m => (ProbComp.sample (S.sign.Coins n)).bind fun rs =>
+    .pure (hashedReply H S n sk i rs m)
+
+/-- The fresh-tape oracle is `ofComp` of the original signing-tape sample followed by
+the corresponding fixed-tape hashed reply: `sampledHashSign H S n sk i = QueryImpl.ofComp
+(fun _ m => (ProbComp.sample (S.sign.Coins n)).bind fun rs =>
+.pure (hashedReply H S n sk i rs m))`. -/
+theorem sampledHashSign_eq (H : CRH) (S : SignatureScheme) (n : ℕ) (sk i : List Bool) :
+    sampledHashSign H S n sk i =
+      QueryImpl.ofComp (fun _ m => (ProbComp.sample (S.sign.Coins n)).bind fun rs =>
+        .pure (hashedReply H S n sk i rs m)) := rfl
+
+/-- Applying the fresh-tape oracle samples one signing tape, returns its hashed signature,
+and preserves the trivial state: `sampledHashSign H S n sk i j m s =
+(ProbComp.sample (S.sign.Coins n)).bind fun rs => .pure (hashedReply H S n sk i rs m, s)`. -/
+theorem sampledHashSign_apply (H : CRH) (S : SignatureScheme) (n : ℕ) (sk i : List Bool)
+    (j : Fin 1) (m : Fin (H.domLen.eval n) → Bool) (s : Unit) :
+    sampledHashSign H S n sk i j m s =
+      (ProbComp.sample (S.sign.Coins n)).bind fun rs =>
+        .pure (hashedReply H S n sk i rs m, s) := by
+  simp only [sampledHashSign_eq, QueryImpl.ofComp_apply,
+    OracleComp.bind_assoc, OracleComp.pure_bind]
+
+/-- The expected payoff of a fresh-tape hash-and-sign simulation equals the expectation
+obtained by drawing one signing tape and running the common transcript, including its log:
+`ProbComp.expect (simulate (sampledHashSign H S n sk i).withLog
+(A.toCompOn cod n 1 (pairEncode pk i) rA) ((), [])) g = ProbComp.expect
+(ProbComp.sample (S.sign.Coins n)) (fun rs =>
+ProbComp.expect (transcript H S A n pk sk i rs rA) g)`,
+where `cod = bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
+(H.domLen.eval n + S.sigLen.eval n)`.
+
+**Proof sketch.** The machine computation has unit query cost at most one by its published
+budget contract. `expect_simulate_sample_once` therefore moves the signing-tape sample
+outside the logged simulation; the fixed-tape implementation is exactly `fixedSign`. -/
+theorem expect_sampledHashSign_eq_transcript (H : CRH) (S : SignatureScheme) (A : NUPPT)
+    (n : ℕ) (pk sk i : List Bool) (rA : A.Coins n)
+    (g : (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
+      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
+        (fun _ => S.sigLen.eval n))) → ℝ) :
+    ProbComp.expect
+        (simulate (sampledHashSign H S n sk i).withLog
+          (A.toCompOn (bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
+            (H.domLen.eval n + S.sigLen.eval n)) n 1 (pairEncode pk i) rA) ((), [])) g =
+      ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
+        ProbComp.expect (transcript H S A n pk sk i rs rA) g) := by
+  simpa only [sampledHashSign_eq, transcript_eq, fixedSign_eq] using
+    expect_simulate_sample_once (fun (_ : Fin 1) m rs => hashedReply H S n sk i rs m)
+      (A.toCompOn (bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
+        (H.domLen.eval n + S.sigLen.eval n)) n 1 (pairEncode pk i) rA)
+      (A.toCompOn_costBoundedBy _ n 1 (pairEncode pk i) rA) g
+
+/-- The common transcript is a successful hash-and-sign forgery when the original verifier
+accepts the hashed final message and that message did not occur in the inner query log,
+`Success H S n pk i res ↔ S.Accepts n pk (padFin (S.msgLen.eval n)
+(H.eval (atParam n (pairEncode i (List.ofFn m))))) σ ∧ ∀ e ∈ res.2.2, e.2.1 ≠ m`, where
+`(m, σ) = splitBits res.1` [PS10, Theorem 144.1]. -/
+def Success (H : CRH) (S : SignatureScheme) (n : ℕ) (pk i : List Bool)
+    (res : (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
+      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
+        (fun _ => S.sigLen.eval n)))) : Prop :=
+  S.Accepts n pk (padFin (S.msgLen.eval n)
+      (H.eval (atParam n (pairEncode i (List.ofFn (splitBits res.1).1)))))
+    (splitBits res.1).2 ∧
+    ∀ e ∈ res.2.2, e.2.1 ≠ (splitBits res.1).1
+
+/-- Success is original-scheme acceptance on the hash, together with freshness of the
+unhashed final message in the common query log: `Success H S n pk i res ↔
+S.Accepts n pk (padFin (S.msgLen.eval n) (H.eval (atParam n (pairEncode i (List.ofFn m))))) σ ∧
+∀ e ∈ res.2.2, e.2.1 ≠ m`, where `(m, σ) = splitBits res.1`. -/
+theorem success_iff (H : CRH) (S : SignatureScheme) (n : ℕ) (pk i : List Bool)
+    (res : (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
+      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
+        (fun _ => S.sigLen.eval n)))) :
+    Success H S n pk i res ↔
+      S.Accepts n pk (padFin (S.msgLen.eval n)
+        (H.eval (atParam n (pairEncode i (List.ofFn (splitBits res.1).1)))))
+        (splitBits res.1).2 ∧
+      ∀ e ∈ res.2.2, e.2.1 ≠ (splitBits res.1).1 := Iff.rfl
+
+end TCSlib.Cryptography.Authentication.HashSignFill
diff --git a/TCSlib/Cryptography/Authentication/Signatures/HashAndSign/ForwardGame.lean b/TCSlib/Cryptography/Authentication/Signatures/HashAndSign/ForwardGame.lean
new file mode 100644
index 000000000..2db10388d
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/Signatures/HashAndSign/ForwardGame.lean
@@ -0,0 +1,445 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.FixedGame
+import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CodecReaders
+import TCSlib.Cryptography.Games.Bridges.Experiments
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The common transcript of the forwarding reduction
+
+## Main definitions
+
+* `HashSignFill.queryHash`: the typed hash at the original signature message width.
+* `HashSignFill.origFixedSign`: the original signer with one fixed signing tape.
+* `HashSignFill.forwardEntry`, `forwardOutput`: hashing the query log and final message.
+
+## Main results
+
+The forwarding handler and the common fixed-tape transcript have the same adversary
+output, with the outer log obtained by hashing every query. Distinct queried hashes
+therefore give freshness in the original signature game.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
+  January 2010, Theorem 144.1, book pp. 144–145.
+-/
+
+namespace TCSlib.Cryptography.Authentication.HashSignFill
+
+open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
+
+/-- The hash of a domain-width message, padded to the original signature message width:
+`queryHash H S n i m =
+padFin (S.msgLen.eval n) (H.eval (atParam n (pairEncode i (List.ofFn m))))`. -/
+def queryHash (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
+    (m : Fin (H.domLen.eval n) → Bool) : Fin (S.msgLen.eval n) → Bool :=
+  padFin (S.msgLen.eval n) (H.eval (atParam n (pairEncode i (List.ofFn m))))
+
+/-- The typed hash reads the evaluator output at the original message width:
+`queryHash H S n i m =
+padFin (S.msgLen.eval n) (H.eval (atParam n (pairEncode i (List.ofFn m))))`. -/
+theorem queryHash_eq (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
+    (m : Fin (H.domLen.eval n) → Bool) :
+    queryHash H S n i m =
+      padFin (S.msgLen.eval n) (H.eval (atParam n (pairEncode i (List.ofFn m)))) := rfl
+
+/-- The original signature oracle with a fixed signing tape and trivial state:
+`origFixedSign S n sk rs j m s =
+.pure (padFin (S.sigLen.eval n) (S.sign.runAt n (pairEncode sk (List.ofFn m)) rs), ())`. -/
+def origFixedSign (S : SignatureScheme) (n : ℕ) (sk : List Bool)
+    (rs : S.sign.Coins n) :
+    QueryImpl (bitSpec (fun _ : Fin 1 => S.msgLen.eval n) (fun _ => S.sigLen.eval n))
+      Unit unifSpec :=
+  fun _ m _ => .pure (padFin (S.sigLen.eval n)
+    (S.sign.runAt n (pairEncode sk (List.ofFn m)) rs), ())
+
+/-- The fixed original signer returns its padded signature and trivial state:
+`origFixedSign S n sk rs = fun _ m _ =>
+.pure (padFin (S.sigLen.eval n) (S.sign.runAt n (pairEncode sk (List.ofFn m)) rs), ())`. -/
+theorem origFixedSign_eq (S : SignatureScheme) (n : ℕ) (sk : List Bool)
+    (rs : S.sign.Coins n) :
+    origFixedSign S n sk rs = fun _ m _ =>
+      .pure (padFin (S.sigLen.eval n) (S.sign.runAt n (pairEncode sk (List.ofFn m)) rs), ()) := rfl
+
+/-- Applying the fixed original signer returns its padded signature:
+`origFixedSign S n sk rs j m s =
+.pure (padFin (S.sigLen.eval n) (S.sign.runAt n (pairEncode sk (List.ofFn m)) rs), ())`. -/
+theorem origFixedSign_apply (S : SignatureScheme) (n : ℕ) (sk : List Bool)
+    (rs : S.sign.Coins n) (j : Fin 1) (m : Fin (S.msgLen.eval n) → Bool) (s : Unit) :
+    origFixedSign S n sk rs j m s =
+      .pure (padFin (S.sigLen.eval n) (S.sign.runAt n (pairEncode sk (List.ofFn m)) rs), ()) := rfl
+
+/-- A forwarded log entry asks oracle zero the hash of the inner query and records the
+same signature answer: `forwardEntry H S n i e = ⟨0, queryHash H S n i e.2.1, e.2.2⟩`. -/
+def forwardEntry (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
+    (e : Σ _ : Fin 1, (Fin (H.domLen.eval n) → Bool) × (Fin (S.sigLen.eval n) → Bool)) :
+    Σ _ : Fin 1, (Fin (S.msgLen.eval n) → Bool) × (Fin (S.sigLen.eval n) → Bool) :=
+  ⟨0, queryHash H S n i e.2.1, e.2.2⟩
+
+/-- Forwarding an entry replaces its query by its hash and retains its signature answer:
+`forwardEntry H S n i e = ⟨0, queryHash H S n i e.2.1, e.2.2⟩`. -/
+theorem forwardEntry_eq (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
+    (e : Σ _ : Fin 1, (Fin (H.domLen.eval n) → Bool) × (Fin (S.sigLen.eval n) → Bool)) :
+    forwardEntry H S n i e = ⟨0, queryHash H S n i e.2.1, e.2.2⟩ := rfl
+
+/-- The forwarded output is the hashed message followed by the unchanged signature:
+`forwardOutput H S n i a = Fin.append (queryHash H S n i (splitBits a).1) (splitBits a).2`. -/
+def forwardOutput (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
+    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) :
+    Fin (S.msgLen.eval n + S.sigLen.eval n) → Bool :=
+  Fin.append (queryHash H S n i (splitBits a).1) (splitBits a).2
+
+/-- The forwarded output concatenates the hash of the message with the signature:
+`forwardOutput H S n i a = Fin.append (queryHash H S n i (splitBits a).1) (splitBits a).2`. -/
+theorem forwardOutput_eq (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
+    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) :
+    forwardOutput H S n i a =
+      Fin.append (queryHash H S n i (splitBits a).1) (splitBits a).2 := rfl
+
+/-- The forwarded output transported to the declared handler output width:
+`handlerOutput H S n i a j =
+forwardOutput H S n i a (Fin.cast (HashSignForward.handler_output_width H S n) j)`. -/
+def handlerOutput (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
+    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) :
+    Fin ((HashSignForward.handler H S).outLen.eval n) → Bool :=
+  fun j => forwardOutput H S n i a (Fin.cast (HashSignForward.handler_output_width H S n) j)
+
+/-- The handler output is the forwarded output evaluated through its width cast:
+`handlerOutput H S n i a =
+fun j => forwardOutput H S n i a (Fin.cast (HashSignForward.handler_output_width H S n) j)`. -/
+theorem handlerOutput_eq (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
+    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) :
+    handlerOutput H S n i a = fun j => forwardOutput H S n i a
+      (Fin.cast (HashSignForward.handler_output_width H S n) j) := rfl
+
+/-- Querying the original fixed signer on a typed hash gives the common transcript's
+hashed reply: `origFixedSign S n sk rs 0 (queryHash H S n i m) () =
+.pure (hashedReply H S n sk i rs m, ())`. -/
+theorem origFixedSign_queryHash (H : CRH) (S : SignatureScheme) (n : ℕ) (sk i : List Bool)
+    (rs : S.sign.Coins n) (m : Fin (H.domLen.eval n) → Bool) :
+    origFixedSign S n sk rs 0 (queryHash H S n i m) () =
+      .pure (hashedReply H S n sk i rs m, ()) := by
+  rw [origFixedSign_apply, hashedReply_eq, HashSignForward.hashWord_unary, queryHash_eq]
+
+/-- The forwarding handler's finalization returns the transported forwarded output:
+`(HashSignForward.handler H S).finish n pk ω s a =
+.pure (handlerOutput H S n (H.gen.runAtL n [] (List.ofFn ω)) a)`. -/
+theorem handler_finish_output (H : CRH) (S : SignatureScheme) (n : ℕ) (pk : List Bool)
+    (ω : Fin ((HashSignForward.handler H S).seedLen.eval n) → Bool)
+    (s : Fin ((HashSignForward.handler H S).stateLen.eval n) → Bool)
+    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) :
+    (HashSignForward.handler H S).finish n pk ω s a =
+      .pure (handlerOutput H S n (H.gen.runAtL n [] (List.ofFn ω)) a) := by
+  rw [HashSignForward.handler_finish_split, handlerOutput_eq, forwardOutput_eq, queryHash_eq]
+
+/-- Fixing the signing tape gives a common adversary output for the inner transcript
+and the forwarding reduction: if `c.CostBoundedBy (fun _ => 1) 1`, then `∃ a L,
+simulate (fixedSign H S n sk i rs).withLog c ((), []) = .pure (a, ((), L)) ∧
+simulate (origFixedSign S n sk rs).withLog ((simulate (K.impl n pk ω) c (K.init n)).bind
+fun res => K.finish n pk ω res.2 res.1) ((), []) =
+.pure (handlerOutput H S n i a, ((), L.map (forwardEntry H S n i)))`, where
+`K = HashSignForward.handler H S` and `i = H.gen.runAtL n [] (List.ofFn ω)`.
+The outer query log is obtained by hashing each inner
+query and retaining its signature answer.
+
+**Proof sketch.** A one-query computation either returns immediately or asks one query
+and returns a function of its answer. In the first case both logs are empty. In the
+second case the handler forwards the typed hash, the original fixed signer gives the
+same hashed reply as the inner fixed signer, and both continuations return the same
+adversary output. Finalization hashes that output's message component. -/
+theorem forward_transcript (H : CRH) (S : SignatureScheme) (n : ℕ) (pk sk : List Bool)
+    (ω : Fin ((HashSignForward.handler H S).seedLen.eval n) → Bool)
+    (rs : S.sign.Coins n)
+    (c : OracleComp
+      (bitSpec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n))
+      (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool))
+    (hc : c.CostBoundedBy (fun _ => 1) 1) :
+    ∃ (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool)
+      (L : QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
+        (fun _ => S.sigLen.eval n))),
+      simulate (fixedSign H S n sk (H.gen.runAtL n [] (List.ofFn ω)) rs).withLog c
+          ((), []) = .pure (a, ((), L)) ∧
+        simulate (origFixedSign S n sk rs).withLog
+          ((simulate ((HashSignForward.handler H S).impl n pk ω) c
+            ((HashSignForward.handler H S).init n)).bind
+              (fun res => (HashSignForward.handler H S).finish n pk ω res.2 res.1))
+          ((), []) =
+          .pure (handlerOutput H S n (H.gen.runAtL n [] (List.ofFn ω)) a,
+            ((), L.map (forwardEntry H S n (H.gen.runAtL n [] (List.ofFn ω))))) := by
+  rcases one_query_cases c hc with ⟨a, rfl⟩ | ⟨j, m, f, rfl⟩
+  · refine ⟨a, [], ?_, ?_⟩
+    · rw [simulate_pure]
+    · simp only [simulate_pure, OracleComp.pure_bind, handler_finish_output, List.map_nil]
+  · refine ⟨f (hashedReply H S n sk (H.gen.runAtL n [] (List.ofFn ω)) rs m),
+      [⟨j, m, hashedReply H S n sk (H.gen.runAtL n [] (List.ofFn ω)) rs m⟩], ?_, ?_⟩
+    · simp only [simulate_query, QueryImpl.withLog_apply, fixedSign_apply,
+        OracleComp.pure_bind, simulate_pure, List.nil_append]
+    · simp only [simulate_query, HashSignForward.handler_impl, ← queryHash_eq,
+        OracleComp.query_bind, OracleComp.pure_bind, simulate_pure, handler_finish_output,
+        QueryImpl.withLog_apply, origFixedSign_queryHash, List.nil_append,
+        List.map_cons, List.map_nil, forwardEntry_eq]
+
+/-- The message component of the forwarded output is the hash of the inner message:
+`(splitBits (forwardOutput H S n i a)).1 = queryHash H S n i (splitBits a).1`. -/
+theorem forwardOutput_message (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
+    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) :
+    (splitBits (forwardOutput H S n i a)).1 = queryHash H S n i (splitBits a).1 := by
+  funext j
+  rw [splitBits_fst, forwardOutput_eq, Fin.append_left]
+
+/-- The signature component of the forwarded output is the original signature component:
+`(splitBits (forwardOutput H S n i a)).2 = (splitBits a).2`. -/
+theorem forwardOutput_signature (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
+    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) :
+    (splitBits (forwardOutput H S n i a)).2 = (splitBits a).2 := by
+  funext j
+  rw [splitBits_snd, forwardOutput_eq, Fin.append_right]
+
+/-- If no logged inner query has the hash of the final message, the final hashed message
+is fresh in the forwarded log:
+`(∀ e ∈ L, queryHash H S n i e.2.1 ≠ queryHash H S n i (splitBits a).1) →
+∀ e ∈ L.map (forwardEntry H S n i), e.2.1 ≠ (splitBits (forwardOutput H S n i a)).1`.
+This includes the case of an empty inner log. -/
+theorem forward_fresh (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
+    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool)
+    (L : QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
+      (fun _ => S.sigLen.eval n)))
+    (hfresh : ∀ e ∈ L, queryHash H S n i e.2.1 ≠ queryHash H S n i (splitBits a).1) :
+    ∀ e ∈ L.map (forwardEntry H S n i),
+      e.2.1 ≠ (splitBits (forwardOutput H S n i a)).1 := by
+  intro e he
+  obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
+  rw [forwardEntry_eq, forwardOutput_message]
+  exact hfresh e' he'
+
+/-- Forwarding succeeds when the original verifier accepts the final hashed message and
+no inner query has that hash, `ForwardSuccess H S n pk i res ↔
+S.Accepts n pk (queryHash H S n i m) σ ∧
+∀ e ∈ res.2.2, queryHash H S n i e.2.1 ≠ queryHash H S n i m`,
+where `(m, σ) = splitBits res.1` [PS10, Theorem 144.1]. -/
+def ForwardSuccess (H : CRH) (S : SignatureScheme) (n : ℕ) (pk i : List Bool)
+    (res : (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
+      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
+        (fun _ => S.sigLen.eval n)))) : Prop :=
+  S.Accepts n pk (queryHash H S n i (splitBits res.1).1) (splitBits res.1).2 ∧
+    ∀ e ∈ res.2.2, queryHash H S n i e.2.1 ≠ queryHash H S n i (splitBits res.1).1
+
+/-- Forwarding success is original-scheme acceptance and freshness of the final hash
+among all hashed inner queries: `ForwardSuccess H S n pk i res ↔
+S.Accepts n pk (queryHash H S n i m) σ ∧
+∀ e ∈ res.2.2, queryHash H S n i e.2.1 ≠ queryHash H S n i m`,
+where `(m, σ) = splitBits res.1`. -/
+theorem forwardSuccess_iff (H : CRH) (S : SignatureScheme) (n : ℕ) (pk i : List Bool)
+    (res : (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
+      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
+        (fun _ => S.sigLen.eval n)))) :
+    ForwardSuccess H S n pk i res ↔
+      S.Accepts n pk (queryHash H S n i (splitBits res.1).1) (splitBits res.1).2 ∧
+        ∀ e ∈ res.2.2, queryHash H S n i e.2.1 ≠ queryHash H S n i (splitBits res.1).1 :=
+  Iff.rfl
+
+/-- The original forgery event tests acceptance and message freshness on a logged
+original-signature transcript,
+`OriginalSuccess S n pk res ↔ S.Accepts n pk m σ ∧ ∀ e ∈ res.2.2, e.2.1 ≠ m`, where
+`(m, σ) = splitBits res.1` [PS10, Definition 136.2]. -/
+def OriginalSuccess (S : SignatureScheme) (n : ℕ) (pk : List Bool)
+    (res : (Fin (S.msgLen.eval n + S.sigLen.eval n) → Bool) ×
+      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => S.msgLen.eval n)
+        (fun _ => S.sigLen.eval n)))) : Prop :=
+  S.Accepts n pk (splitBits res.1).1 (splitBits res.1).2 ∧
+    ∀ e ∈ res.2.2, e.2.1 ≠ (splitBits res.1).1
+
+/-- The original forgery event is acceptance together with freshness in its logged
+original-message queries:
+`OriginalSuccess S n pk res ↔ S.Accepts n pk m σ ∧ ∀ e ∈ res.2.2, e.2.1 ≠ m`, where
+`(m, σ) = splitBits res.1`. -/
+theorem originalSuccess_iff (S : SignatureScheme) (n : ℕ) (pk : List Bool)
+    (res : (Fin (S.msgLen.eval n + S.sigLen.eval n) → Bool) ×
+      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => S.msgLen.eval n)
+        (fun _ => S.sigLen.eval n)))) :
+    OriginalSuccess S n pk res ↔
+      S.Accepts n pk (splitBits res.1).1 (splitBits res.1).2 ∧
+        ∀ e ∈ res.2.2, e.2.1 ≠ (splitBits res.1).1 := Iff.rfl
+
+/-- Hashing the output and every logged query turns the original forgery event into
+the common transcript's forwarding-success event:
+`OriginalSuccess S n pk (forwardOutput H S n i a, ((), L.map (forwardEntry H S n i))) ↔
+ForwardSuccess H S n pk i (a, ((), L))`. -/
+theorem originalSuccess_forwardOutput (H : CRH) (S : SignatureScheme) (n : ℕ)
+    (pk i : List Bool) (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool)
+    (L : QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
+      (fun _ => S.sigLen.eval n))) :
+    OriginalSuccess S n pk (forwardOutput H S n i a, ((), L.map (forwardEntry H S n i))) ↔
+      ForwardSuccess H S n pk i (a, ((), L)) := by
+  rw [originalSuccess_iff, forwardSuccess_iff, forwardOutput_message, forwardOutput_signature]
+  apply and_congr_right
+  intro _
+  constructor
+  · intro hf e he
+    exact hf (forwardEntry H S n i e) (List.mem_map.mpr ⟨e, he, rfl⟩)
+  · intro hf e he
+    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
+    exact hf e' he'
+
+/-- The original one-query forgery game may draw its signing tape before the logged
+simulation, `accept (S.forgeGame C 1 n) = 𝔼 rg : S.gen.Coins n, 𝔼 r : C.Coins n,
+𝔼 rs : S.sign.Coins n, ProbComp.prob (simulate (origFixedSign S n sk rs).withLog
+(C.toCompOn cod n 1 pk r) ((), [])) (OriginalSuccess S n pk)`,
+writing `𝔼 x : X, f x` for `ProbComp.expect (ProbComp.sample X) (fun x => f x)`, with
+`pk = pairFstD (S.gen.runAt n [] rg)`, `sk = pairSndD (S.gen.runAt n [] rg)` and
+`cod = bitCodec (fun _ : Fin 1 => S.msgLen.eval n) (fun _ => S.sigLen.eval n)
+(S.msgLen.eval n + S.sigLen.eval n)` [PS10, Definition 136.2, one-time specialization].
+
+**Proof sketch.** Read key sampling, adversary sampling and the forgery test from the
+published game equation. The adversary has at most one query, so the one-query sampling
+lemma moves its fresh signing-tape sample outside the simulation. -/
+theorem forgeGame_eq_fixed (S : SignatureScheme) (C : NUPPT) (n : ℕ) :
+    accept (S.forgeGame C 1 n) =
+      ProbComp.expect (ProbComp.sample (S.gen.Coins n)) (fun rg =>
+        ProbComp.expect (ProbComp.sample (C.Coins n)) (fun r =>
+          ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
+            ProbComp.prob
+              (simulate (origFixedSign S n (pairSndD (S.gen.runAt n [] rg)) rs).withLog
+                (C.toCompOn
+                  (bitCodec (fun _ : Fin 1 => S.msgLen.eval n) (fun _ => S.sigLen.eval n)
+                    (S.msgLen.eval n + S.sigLen.eval n)) n 1
+                  (pairFstD (S.gen.runAt n [] rg)) r) ((), []))
+              (OriginalSuccess S n (pairFstD (S.gen.runAt n [] rg)))))) := by
+  classical
+  rw [S.forgeGame_eq, accept_eq, ProbComp.prob_eq_expect]
+  simp only [ProbComp.expect_bind, ProbComp.expect_pure, decide_eq_true_eq,
+    S.forgerCodec_eq_bitCodec]
+  apply congrArg (ProbComp.expect (ProbComp.sample (S.gen.Coins n)))
+  funext rg
+  apply congrArg (ProbComp.expect (ProbComp.sample (C.Coins n)))
+  funext r
+  have hraw := expect_simulate_sample_once
+    (fun (_ : Fin 1) m rs => padFin (S.sigLen.eval n)
+      (S.sign.runAt n (pairEncode (pairSndD (S.gen.runAt n [] rg)) (List.ofFn m)) rs))
+    (C.toCompOn
+      (bitCodec (fun _ : Fin 1 => S.msgLen.eval n) (fun _ => S.sigLen.eval n)
+        (S.msgLen.eval n + S.sigLen.eval n)) n 1 (pairFstD (S.gen.runAt n [] rg)) r)
+    (C.toCompOn_costBoundedBy _ n 1 _ r)
+    (fun res => if OriginalSuccess S n (pairFstD (S.gen.runAt n [] rg)) res then 1 else 0)
+  simpa only [S.signImpl_eq, originalSuccess_iff, origFixedSign_eq,
+    ProbComp.prob_eq_expect] using hraw
+
+/-- The transported handler output and the forwarded output have the same bit list:
+`List.ofFn (handlerOutput H S n i a) = List.ofFn (forwardOutput H S n i a)`. -/
+theorem ofFn_handlerOutput (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
+    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) :
+    List.ofFn (handlerOutput H S n i a) = List.ofFn (forwardOutput H S n i a) := by
+  rw [handlerOutput_eq]
+  exact (List.ofFn_congr (HashSignForward.handler_output_width H S n).symm
+    (forwardOutput H S n i a)).symm
+
+/-- With all tapes fixed, reading the forwarding reduction's output list at the original
+game's width gives the common transcript's forwarding-success probability: if
+`c.CostBoundedBy (fun _ => 1) 1`, then `ProbComp.prob ((simulate (origFixedSign S n sk rs).withLog
+R ((), [])).bind fun res => .pure (padFin (S.msgLen.eval n + S.sigLen.eval n) (List.ofFn res.1),
+res.2)) (OriginalSuccess S n pk) = ProbComp.prob
+(simulate (fixedSign H S n sk i rs).withLog c ((), [])) (ForwardSuccess H S n pk i)`, where
+`R = (simulate (K.impl n pk ω) c (K.init n)).bind fun res => K.finish n pk ω res.2 res.1`,
+`K = HashSignForward.handler H S` and `i = H.gen.runAtL n [] (List.ofFn ω)`.
+
+**Proof sketch.** The deterministic coupling gives the same adversary output and a log
+whose queries are precisely the inner query hashes. The output-component and event
+readers identify the two success tests, so their probabilities on these pure runs agree. -/
+theorem forward_prob_transcript (H : CRH) (S : SignatureScheme) (n : ℕ) (pk sk : List Bool)
+    (ω : Fin ((HashSignForward.handler H S).seedLen.eval n) → Bool)
+    (rs : S.sign.Coins n)
+    (c : OracleComp
+      (bitSpec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n))
+      (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool))
+    (hc : c.CostBoundedBy (fun _ => 1) 1) :
+    ProbComp.prob
+      ((simulate (origFixedSign S n sk rs).withLog
+        ((simulate ((HashSignForward.handler H S).impl n pk ω) c
+          ((HashSignForward.handler H S).init n)).bind
+            (fun res => (HashSignForward.handler H S).finish n pk ω res.2 res.1))
+        ((), [])).bind (fun res =>
+          .pure (padFin (S.msgLen.eval n + S.sigLen.eval n) (List.ofFn res.1), res.2)))
+      (OriginalSuccess S n pk) =
+      ProbComp.prob
+        (simulate (fixedSign H S n sk (H.gen.runAtL n [] (List.ofFn ω)) rs).withLog c ((), []))
+        (ForwardSuccess H S n pk (H.gen.runAtL n [] (List.ofFn ω))) := by
+  classical
+  obtain ⟨a, L, hinner, houter⟩ := forward_transcript H S n pk sk ω rs c hc
+  rw [houter, hinner, OracleComp.pure_bind, ProbComp.prob_pure, ofFn_handlerOutput,
+    padFin_ofFn, ProbComp.prob_pure]
+  exact if_congr (originalSuccess_forwardOutput H S n pk _ a L) rfl rfl
+
+/-- A one-query machine against the original scheme realizes exactly the common
+transcript's forwarding-success probability, `∃ C : NUPPT, ∀ n, accept (S.forgeGame C 1 n) =
+𝔼 rg : S.gen.Coins n, 𝔼 ri : H.gen.Coins n, 𝔼 rA : A.Coins n, 𝔼 rs : S.sign.Coins n,
+ProbComp.prob (transcript H S A n pk sk i rs rA) (ForwardSuccess H S n pk i)`,
+writing `𝔼 x : X, f x` for `ProbComp.expect (ProbComp.sample X) (fun x => f x)`, with
+`pk = pairFstD (S.gen.runAt n [] rg)`, `sk = pairSndD (S.gen.runAt n [] rg)` and
+`i = H.gen.runAt n [] ri` [PS10, Theorem 144.1].
+
+**Proof sketch.** T2 supplies the forwarding machine and a bijection between its coins
+and the independent hash-generator seed and original adversary coins. Reindex the
+original forgery experiment by this bijection and then by the hash generator's published
+coin equivalence. Drawing the single signing tape in advance gives the deterministic
+coupling, whose mapped query log and hashed output identify the two success events. -/
+theorem exists_forwardGame (H : CRH) (S : SignatureScheme) (A : NUPPT) :
+    ∃ C : NUPPT, ∀ n : ℕ,
+      accept (S.forgeGame C 1 n) =
+        ProbComp.expect (ProbComp.sample (S.gen.Coins n)) (fun rg =>
+          ProbComp.expect (ProbComp.sample (H.gen.Coins n)) (fun ri =>
+            ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA =>
+              ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
+                ProbComp.prob
+                  (transcript H S A n (pairFstD (S.gen.runAt n [] rg))
+                    (pairSndD (S.gen.runAt n [] rg)) (H.gen.runAt n [] ri) rs rA)
+                  (ForwardSuccess H S n (pairFstD (S.gen.runAt n [] rg))
+                    (H.gen.runAt n [] ri)))))) := by
+  classical
+  obtain ⟨C, hC⟩ := HashSignForward.exists_forwardMachine H S A
+  refine ⟨C, fun n => ?_⟩
+  obtain ⟨φ, hφ⟩ := hC n
+  let e := NUPPT.coinsEquivPoly (A := H.gen) (HashSignForward.handler_seedLen H S).symm n
+  have he : ∀ ri : H.gen.Coins n, List.ofFn (e ri) = List.ofFn ri :=
+    NUPPT.coinsEquivPoly_ofFn _ n
+  rw [forgeGame_eq_fixed]
+  apply congrArg (ProbComp.expect (ProbComp.sample (S.gen.Coins n)))
+  funext rg
+  rw [← ProbComp.expect_sample_equiv φ, ← Bridge.expect_sample_pair]
+  simp only [ProbComp.expect_bind, ProbComp.expect_pure]
+  rw [← ProbComp.expect_sample_equiv e]
+  apply congrArg (ProbComp.expect (ProbComp.sample (H.gen.Coins n)))
+  funext ri
+  apply congrArg (ProbComp.expect (ProbComp.sample (A.Coins n)))
+  funext rA
+  apply congrArg (ProbComp.expect (ProbComp.sample (S.sign.Coins n)))
+  funext rs
+  have hout := expect_toCompOn_outLen
+    (origFixedSign S n (pairSndD (S.gen.runAt n [] rg)) rs).withLog C n 1
+    (pairFstD (S.gen.runAt n [] rg)) (φ (e ri, rA)) ((), [])
+    (HashSignForward.handler_output_width H S n).symm
+    (fun res => if OriginalSuccess S n (pairFstD (S.gen.runAt n [] rg))
+      (padFin (S.msgLen.eval n + S.sigLen.eval n) res.1, res.2) then 1 else 0)
+  simp only [padFin_ofFn] at hout
+  rw [ProbComp.prob_eq_expect, hout]
+  rw [← hφ _ (e ri) rA]
+  let c := A.toCompOn
+    (bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
+      (H.domLen.eval n + S.sigLen.eval n)) n 1
+    ((HashSignForward.handler H S).advInput n (pairFstD (S.gen.runAt n [] rg)) (e ri)) rA
+  have hforward := forward_prob_transcript H S n (pairFstD (S.gen.runAt n [] rg))
+    (pairSndD (S.gen.runAt n [] rg)) (e ri) rs c
+    (A.toCompOn_costBoundedBy _ n 1 _ rA)
+  rw [ProbComp.prob_bind] at hforward
+  simp only [ProbComp.prob_pure, padFin_ofFn] at hforward
+  rw [hforward]
+  dsimp only [c]
+  rw [HashSignForward.handler_advInput, he, ← NUPPT.runAt_eq, transcript_eq]
+
+end TCSlib.Cryptography.Authentication.HashSignFill
diff --git a/TCSlib/Cryptography/Authentication/Signatures/HashAndSign/ForwardHandler.lean b/TCSlib/Cryptography/Authentication/Signatures/HashAndSign/ForwardHandler.lean
new file mode 100644
index 000000000..7cbc4dda5
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/Signatures/HashAndSign/ForwardHandler.lean
@@ -0,0 +1,382 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Games.Forwarding
+import TCSlib.Cryptography.Authentication.Signatures.Defs
+import TCSlib.Cryptography.Hashing.CollisionResistant
+import TCSlib.Cryptography.Asymptotic.CollectionsLemmas
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The hash-and-sign forwarding handler
+
+The one-time forger reduction samples a hash index, gives the public key and index to
+its adversary, hashes each query before forwarding it, and hashes the final message.
+
+## Main definitions
+
+* `HashSignForward.indexWord`: the hash index obtained from the handler's seed.
+* `HashSignForward.hashWord`: the hash read at the original signature message length.
+* `HashSignForward.handler`: the interactive handler of [PS10, Theorem 144.1].
+
+## Main results
+
+The string functions are polynomial-time, and the handler's published field equations
+expose its seed, budgets, adversary input, round and finalization.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
+  January 2010, Theorem 144.1, book pp. 144–145.
+-/
+
+namespace TCSlib.Cryptography.Authentication.HashSignForward
+
+open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
+open InteractiveHandler
+
+/-- The index generator on parameter word `u` and seed `ω`, with empty input and advice:
+`indexWord H u ω = H.gen.output (NUPPT.layout u [] [] ω)`. -/
+def indexWord (H : CRH) (u ω : List Bool) : List Bool :=
+  H.gen.output (NUPPT.layout u [] [] ω)
+
+/-- The index word is `H.gen.output (NUPPT.layout u [] [] ω)`:
+`indexWord H u ω = H.gen.output (NUPPT.layout u [] [] ω)`. -/
+theorem indexWord_eq (H : CRH) (u ω : List Bool) :
+    indexWord H u ω = H.gen.output (NUPPT.layout u [] [] ω) := rfl
+
+/-- The hash of `m` at index `i`, padded to the original scheme's message length:
+`hashWord H S u i m = padStr S.msgLen u (H.eval (pairEncode u (pairEncode i m)))`. -/
+def hashWord (H : CRH) (S : SignatureScheme) (u i m : List Bool) : List Bool :=
+  padStr S.msgLen u (H.eval (pairEncode u (pairEncode i m)))
+
+/-- The hash word is the evaluator output padded to `S.msgLen(|u|)` bits:
+`hashWord H S u i m = padStr S.msgLen u (H.eval (pairEncode u (pairEncode i m)))`. -/
+theorem hashWord_eq (H : CRH) (S : SignatureScheme) (u i m : List Bool) :
+    hashWord H S u i m =
+      padStr S.msgLen u (H.eval (pairEncode u (pairEncode i m))) := rfl
+
+/-- The reduction gives its adversary the public key paired with its sampled index:
+`advWord H w =
+pairEncode (pairFstD (pairSndD w)) (indexWord H (pairFstD w) (pairSndD (pairSndD w)))`. -/
+def advWord (H : CRH) (w : List Bool) : List Bool :=
+  pairEncode (pairFstD (pairSndD w))
+    (indexWord H (pairFstD w) (pairSndD (pairSndD w)))
+
+/-- The adversary input pairs the reduction input with the index obtained from its seed:
+`advWord H w =
+pairEncode (pairFstD (pairSndD w)) (indexWord H (pairFstD w) (pairSndD (pairSndD w)))`. -/
+theorem advWord_eq (H : CRH) (w : List Bool) :
+    advWord H w = pairEncode (pairFstD (pairSndD w))
+      (indexWord H (pairFstD w) (pairSndD (pairSndD w))) := rfl
+
+/-- The first round asks the original signing oracle the hashed message; the second
+round returns the outer signature and preserves the state: `roundWord H S w =
+if decide (rL w = []) then pairEncode [false] (pairEncode [] (hashWord H S u (indexWord H u (rW w))
+(rX w))) else pairEncode [true] (rAns w ++ rS w)`, where `u = rU w`. -/
+def roundWord (H : CRH) (S : SignatureScheme) (w : List Bool) : List Bool :=
+  if decide (rL w = []) then
+    pairEncode [false] (pairEncode []
+      (hashWord H S (rU w) (indexWord H (rU w) (rW w)) (rX w)))
+  else pairEncode [true] (rAns w ++ rS w)
+
+/-- The round asks the hashed query when its outer log is empty, and otherwise returns
+the first outer answer together with its unchanged state: `roundWord H S w =
+if decide (rL w = []) then pairEncode [false] (pairEncode [] (hashWord H S u (indexWord H u (rW w))
+(rX w))) else pairEncode [true] (rAns w ++ rS w)`, where `u = rU w`. -/
+theorem roundWord_eq (H : CRH) (S : SignatureScheme) (w : List Bool) :
+    roundWord H S w =
+      if decide (rL w = []) then
+        pairEncode [false] (pairEncode []
+          (hashWord H S (rU w) (indexWord H (rU w) (rW w)) (rX w)))
+      else pairEncode [true] (rAns w ++ rS w) := rfl
+
+/-- The finalization hashes the message prefix of the adversary output and retains
+its signature suffix, making no further oracle query: `finalWord H S w =
+pairEncode [true] (hashWord H S u (indexWord H u (rW w)) (a.take k) ++ a.drop k)`, where
+`u = rU w`, `a = finA w` and `k = H.domLen.eval u.length`. -/
+def finalWord (H : CRH) (S : SignatureScheme) (w : List Bool) : List Bool :=
+  pairEncode [true]
+    (hashWord H S (rU w) (indexWord H (rU w) (rW w))
+      ((finA w).take (H.domLen.eval (rU w).length)) ++
+      (finA w).drop (H.domLen.eval (rU w).length))
+
+/-- The final output is the hashed message prefix concatenated with the signature suffix:
+`finalWord H S w =
+pairEncode [true] (hashWord H S u (indexWord H u (rW w)) (a.take k) ++ a.drop k)`, where
+`u = rU w`, `a = finA w` and `k = H.domLen.eval u.length`. -/
+theorem finalWord_eq (H : CRH) (S : SignatureScheme) (w : List Bool) :
+    finalWord H S w = pairEncode [true]
+      (hashWord H S (rU w) (indexWord H (rU w) (rW w))
+        ((finA w).take (H.domLen.eval (rU w).length)) ++
+        (finA w).drop (H.domLen.eval (rU w).length)) := rfl
+
+/-- Running the index generator on polynomial-time parameter and seed words is
+polynomial-time: `PolyTimeComputable u → PolyTimeComputable ω →
+PolyTimeComputable fun w => indexWord H (u w) (ω w)`. -/
+theorem polyTimeComputable_indexWord (H : CRH) {u ω : List Bool → List Bool}
+    (hu : PolyTimeComputable u) (hω : PolyTimeComputable ω) :
+    PolyTimeComputable fun w => indexWord H (u w) (ω w) := by
+  simpa only [indexWord, Function.comp_apply] using
+    H.gen.polyTimeComputable_output.comp
+      (NUPPT.polyTimeComputable_layout hu (polyTimeComputable_const [])
+        (polyTimeComputable_const []) hω)
+
+/-- Hashing polynomial-time parameter, index and message words and padding the result
+to the original signature message length is polynomial-time: `PolyTimeComputable u →
+PolyTimeComputable i → PolyTimeComputable m →
+PolyTimeComputable fun w => hashWord H S (u w) (i w) (m w)`. -/
+theorem polyTimeComputable_hashWord (H : CRH) (S : SignatureScheme)
+    {u i m : List Bool → List Bool} (hu : PolyTimeComputable u)
+    (hi : PolyTimeComputable i) (hm : PolyTimeComputable m) :
+    PolyTimeComputable fun w => hashWord H S (u w) (i w) (m w) := by
+  have h := (polyTimeComputable_padStr S.msgLen).comp
+    (hu.pairEncode (H.eval_poly.comp (hu.pairEncode (hi.pairEncode hm))))
+  refine (congrArg PolyTimeComputable
+    (?_ : (fun w => hashWord H S (u w) (i w) (m w)) = _)).mpr h
+  funext w
+  simp only [hashWord_eq, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
+
+/-- Pairing the supplied public key with the index generated from the seed is
+polynomial-time: `PolyTimeComputable (advWord H)`, for `advWord H : List Bool → List Bool`. -/
+theorem polyTimeComputable_advWord (H : CRH) : PolyTimeComputable (advWord H) := by
+  exact (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).pairEncode
+    (polyTimeComputable_indexWord H polyTimeComputable_pairFstD
+      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
+
+/-- One hashing-and-forwarding round is polynomial-time, `PolyTimeComputable (roundWord H S)`
+for `roundWord H S : List Bool → List Bool`: it tests whether the outer log is empty, then
+either emits the hash query or returns the recorded answer. -/
+theorem polyTimeComputable_roundWord (H : CRH) (S : SignatureScheme) :
+    PolyTimeComputable (roundWord H S) := by
+  exact polyTimeComputable_ite
+    (polyTimeComputable_isNil.comp polyTimeComputable_rL)
+    ((polyTimeComputable_const [false]).pairEncode
+      ((polyTimeComputable_const []).pairEncode
+        (polyTimeComputable_hashWord H S polyTimeComputable_rU
+          (polyTimeComputable_indexWord H polyTimeComputable_rU polyTimeComputable_rW)
+          polyTimeComputable_rX)))
+    ((polyTimeComputable_const [true]).pairEncode
+      (polyTimeComputable_rAns.append polyTimeComputable_rS))
+
+/-- Finalization is polynomial-time, `PolyTimeComputable (finalWord H S)` for
+`finalWord H S : List Bool → List Bool`: split at the polynomial domain width, hash the
+message prefix and concatenate the original signature suffix.
+
+**Proof sketch.** The published polynomial take and drop operations apply to the parameter
+and output fields. The parameter, seed and output readers and the index and hash operations
+are polynomial-time, so composition and concatenation give the result. -/
+theorem polyTimeComputable_finalWord (H : CRH) (S : SignatureScheme) :
+    PolyTimeComputable (finalWord H S) := by
+  have hm := (polyTimeComputable_pairTakePoly H.domLen).comp
+    (polyTimeComputable_rU.pairEncode polyTimeComputable_finA)
+  have hs := (polyTimeComputable_pairDropPoly H.domLen).comp
+    (polyTimeComputable_rU.pairEncode polyTimeComputable_finA)
+  have h := (polyTimeComputable_const [true]).pairEncode
+    ((polyTimeComputable_hashWord H S polyTimeComputable_rU
+      (polyTimeComputable_indexWord H polyTimeComputable_rU polyTimeComputable_rW) hm).append hs)
+  refine (congrArg PolyTimeComputable (?_ : finalWord H S = _)).mpr h
+  funext w
+  simp only [finalWord_eq, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
+
+/-- The hash-and-sign reduction handler [PS10, Theorem 144.1]: sample one hash index,
+provide `⟨pk,i⟩`, forward each query after hashing it, and hash the final message, with
+`seedLen = H.gen.coins`, `advIn = advWord H`, `run = roundWord H S`, `finRun = finalWord H S`,
+`init _ = zeroBits _` and `outLen = .add S.msgLen S.sigLen`. Its state
+is empty, each inner call makes one outer call and finalization makes none. -/
+def handler (H : CRH) (S : SignatureScheme) :
+    InteractiveHandler 1 (fun _ => H.domLen) (fun _ => S.sigLen)
+      1 (fun _ => S.msgLen) (fun _ => S.sigLen) where
+  stateLen := .const 0
+  seedLen := H.gen.coins
+  perCall := .const 1
+  init _ := zeroBits _
+  run := roundWord H S
+  poly := polyTimeComputable_roundWord H S
+  advIn := advWord H
+  advIn_poly := polyTimeComputable_advWord H
+  outLen := .add S.msgLen S.sigLen
+  finCall := .const 0
+  finRun := finalWord H S
+  finRun_poly := polyTimeComputable_finalWord H S
+
+attribute [simps (config := { isSimp := false }) stateLen seedLen perCall init run advIn outLen
+  finCall finRun] handler
+
+/-- At a unary parameter, the generated index word is the hash generator's literal run
+with the supplied list of coins: `indexWord H (List.replicate n true) ω = H.gen.runAtL n [] ω`. -/
+theorem indexWord_unary (H : CRH) (n : ℕ) (ω : List Bool) :
+    indexWord H (List.replicate n true) ω = H.gen.runAtL n [] ω := by
+  rw [indexWord_eq, H.gen_uniform.runAtL_eq, NUPPT.layout_eq, NUPPT.advInput_eq]
+
+/-- At unary parameter `1^n`, the hash word is the list of the padded evaluator at
+the original signature message length: `hashWord H S (List.replicate n true) i m =
+List.ofFn (padFin (S.msgLen.eval n) (H.eval (atParam n (pairEncode i m))))`. -/
+theorem hashWord_unary (H : CRH) (S : SignatureScheme) (n : ℕ) (i m : List Bool) :
+    hashWord H S (List.replicate n true) i m =
+      List.ofFn (padFin (S.msgLen.eval n) (H.eval (atParam n (pairEncode i m)))) := by
+  rw [hashWord_eq, ← ofFn_padFin_eq_padStr, List.length_replicate, atParam_eq]
+
+/-- The handler gives the adversary `⟨pk,i⟩`, where `i` is the hash generator's run
+on its seed: `(handler H S).advInput n pk ω = pairEncode pk (H.gen.runAtL n [] (List.ofFn ω))`. -/
+theorem handler_advInput (H : CRH) (S : SignatureScheme) (n : ℕ) (pk : List Bool)
+    (ω : Fin ((handler H S).seedLen.eval n) → Bool) :
+    (handler H S).advInput n pk ω =
+      pairEncode pk (H.gen.runAtL n [] (List.ofFn ω)) := by
+  rw [InteractiveHandler.advInput_eq, handler_advIn, advWord_eq, seedIn_eq]
+  simp only [pairFstD_pairEncode, pairSndD_pairEncode, indexWord_unary]
+
+/-- Each call asks the original signing oracle for the hash of its inner message and
+returns the outer signature unchanged, preserving the handler state:
+`(handler H S).impl n pk ω i x s = .query 0 (padFin (S.msgLen.eval n)
+(H.eval (atParam n (pairEncode (H.gen.runAtL n [] (List.ofFn ω)) (List.ofFn x)))))
+fun y => .pure (y, s)`.
+
+**Proof sketch.** The first round has an empty outer log and emits precisely the padded
+hash query. The second round reads the first outer answer and returns it with the state.
+The published one-query call rule therefore identifies the entire call computation. -/
+theorem handler_impl (H : CRH) (S : SignatureScheme) (n : ℕ) (pk : List Bool)
+    (ω : Fin ((handler H S).seedLen.eval n) → Bool) (i : Fin 1)
+    (x : Fin (H.domLen.eval n) → Bool)
+    (s : Fin ((handler H S).stateLen.eval n) → Bool) :
+    (handler H S).impl n pk ω i x s =
+      .query 0
+        (padFin (S.msgLen.eval n) (H.eval
+          (atParam n (pairEncode (H.gen.runAtL n [] (List.ofFn ω)) (List.ofFn x)))))
+        fun y => .pure (y, s) := by
+  refine InteractiveHandler.impl_of_query (handler H S) n pk ω x s 0 _
+    (fun y => y) (fun _ => s) ?_ ?_ ?_
+  · rw [handler_perCall, PolyExpr.eval_const]
+  · rw [handler_run, roundWord_eq, rL_input, rU_input, rW_input, rX_input,
+      indexWord_unary, hashWord_unary, if_pos (decide_eq_true rfl)]
+    rfl
+  · intro y
+    rw [handler_run, roundWord_eq, rL_input, rAns_input, rS_input,
+      if_neg (fun h => pairEncode_ne_nil _ _ (of_decide_eq_true h))]
+
+/-- Finalization makes no oracle query and returns the hash of the adversary's message
+prefix concatenated with its signature suffix, read at the handler's output length:
+`(handler H S).finish n pk ω s a = .pure (padFin ((handler H S).outLen.eval n)
+(hashWord H S (List.replicate n true) i ((List.ofFn a).take d) ++ (List.ofFn a).drop d))`,
+where `i = H.gen.runAtL n [] (List.ofFn ω)` and `d = H.domLen.eval n`.
+
+**Proof sketch.** The hash word has the signature scheme's message width. The suffix of
+the correctly sized adversary output has the signature width, so the concatenation has
+the declared output width. The first finalization round returns this word; the published
+immediate-return finalization rule identifies its computation. -/
+theorem handler_finish (H : CRH) (S : SignatureScheme) (n : ℕ) (pk : List Bool)
+    (ω : Fin ((handler H S).seedLen.eval n) → Bool)
+    (s : Fin ((handler H S).stateLen.eval n) → Bool)
+    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) :
+    (handler H S).finish n pk ω s a =
+      .pure (padFin ((handler H S).outLen.eval n)
+        (hashWord H S (List.replicate n true) (H.gen.runAtL n [] (List.ofFn ω))
+          ((List.ofFn a).take (H.domLen.eval n)) ++
+          (List.ofFn a).drop (H.domLen.eval n))) := by
+  refine InteractiveHandler.finish_of_ret_padFin (handler H S) n pk ω s a _ ?_ ?_
+  · rw [List.length_append, hashWord_unary, List.length_ofFn, List.length_drop,
+      List.length_ofFn, handler_outLen, PolyExpr.eval_add]
+    omega
+  · rw [handler_finRun, finalWord_eq, rU_finInput, rW_finInput, finA_finInput,
+      indexWord_unary, List.length_replicate]
+
+/-- When the hash range and signature message widths agree, hashing a typed domain
+message gives the list of the CRH hash, transported to the signature message width: for
+`hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n`,
+`hashWord H S (List.replicate n true) i (List.ofFn x) =
+List.ofFn (fun j : Fin (S.msgLen.eval n) => H.hash n i x (Fin.cast (hlen n).symm j))`. -/
+theorem hashWord_eq_hash (H : CRH) (S : SignatureScheme)
+    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) (n : ℕ) (i : List Bool)
+    (x : Fin (H.domLen.eval n) → Bool) :
+    hashWord H S (List.replicate n true) i (List.ofFn x) =
+      List.ofFn (fun j : Fin (S.msgLen.eval n) =>
+        H.hash n i x (Fin.cast (hlen n).symm j)) := by
+  rw [hashWord_unary]
+  apply congrArg List.ofFn
+  funext j
+  rw [CRH.hash_eq, padFin_apply, padFin_apply, Fin.coe_cast]
+
+/-- The hash-and-sign forwarding reduction is a one-query oracle machine,
+`∃ C : NUPPT, ∀ n, ∃ φ : (Fin (K.seedLen.eval n) → Bool) × A.Coins n ≃ C.Coins n, ∀ pk ω r,
+(simulate (K.impl n pk ω) (A.toCompOn cod n 1 (K.advInput n pk ω) r) (K.init n)).bind
+(fun res => K.finish n pk ω res.2 res.1) = C.toCompOn cod' n 1 pk (φ (ω, r))`, where
+`K = handler H S`, `cod = bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
+(H.domLen.eval n + S.sigLen.eval n)` and `cod' = bitCodec (fun _ : Fin 1 => S.msgLen.eval n)
+(fun _ => S.sigLen.eval n) (K.outLen.eval n)` [PS10, Theorem 144.1].
+For every parameter, a bijection identifies its coins with the
+handler seed and the original adversary coins, and its computation is the handler's
+simulation followed by finalization.
+
+**Proof sketch.** Apply T2 to the hashing handler and the constant-one inner query
+budget. One outer query per inner query and zero finalization queries give outer
+budget `1 · 1 + 0 = 1`; the codec widths are the signature message and signature widths. -/
+theorem exists_forwardMachine (H : CRH) (S : SignatureScheme) (A : NUPPT) :
+    ∃ C : NUPPT, ∀ n : ℕ,
+      ∃ φ : (Fin ((handler H S).seedLen.eval n) → Bool) × A.Coins n ≃ C.Coins n,
+        ∀ (pk : List Bool) (ω : Fin ((handler H S).seedLen.eval n) → Bool)
+          (r : A.Coins n),
+          (simulate ((handler H S).impl n pk ω)
+            (A.toCompOn
+              (bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
+                (H.domLen.eval n + S.sigLen.eval n))
+              n 1 ((handler H S).advInput n pk ω) r)
+            ((handler H S).init n)).bind
+              (fun res => (handler H S).finish n pk ω res.2 res.1) =
+            C.toCompOn
+              (bitCodec (fun _ : Fin 1 => S.msgLen.eval n) (fun _ => S.sigLen.eval n)
+                ((handler H S).outLen.eval n))
+              n 1 pk (φ (ω, r)) := by
+  obtain ⟨C, hC⟩ := exists_interactiveHandlerMachine A (.const 1)
+    (fun _ : Fin 1 => H.domLen) (fun _ => S.sigLen)
+    (fun _ : Fin 1 => S.msgLen) (fun _ => S.sigLen)
+    (.add H.domLen S.sigLen) (handler H S)
+  simp only [PolyExpr.eval_const, PolyExpr.eval_add, handler_perCall,
+    handler_finCall, Nat.one_mul, Nat.add_zero] at hC
+  exact ⟨C, hC⟩
+
+/-- The handler output width is the sum of the original message and signature widths:
+`(handler H S).outLen.eval n = S.msgLen.eval n + S.sigLen.eval n`. -/
+theorem handler_output_width (H : CRH) (S : SignatureScheme) (n : ℕ) :
+    (handler H S).outLen.eval n = S.msgLen.eval n + S.sigLen.eval n :=
+  (congrArg (fun p : PolyExpr => p.eval n) (handler_outLen H S)).trans
+    (PolyExpr.eval_add S.msgLen S.sigLen n)
+
+/-- Finalization returns the hashed message component paired by concatenation with
+the adversary's signature component: `(handler H S).finish n pk ω s a = .pure (fun j =>
+Fin.append
+(padFin (S.msgLen.eval n) (H.eval (atParam n (pairEncode i (List.ofFn (splitBits a).1)))))
+(splitBits a).2 (Fin.cast (handler_output_width H S n) j))`, where
+`i = H.gen.runAtL n [] (List.ofFn ω)`. The displayed cast transports the declared handler
+output width to the sum of message and signature widths.
+
+**Proof sketch.** Read finalization as a padded list, split the adversary list at the
+domain width with the published take/drop lemma, and identify the concatenation as the
+list of a `Fin.append` vector. Reading that list at its width recovers the vector. -/
+theorem handler_finish_split (H : CRH) (S : SignatureScheme) (n : ℕ) (pk : List Bool)
+    (ω : Fin ((handler H S).seedLen.eval n) → Bool)
+    (s : Fin ((handler H S).stateLen.eval n) → Bool)
+    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) :
+    (handler H S).finish n pk ω s a =
+      .pure (fun j =>
+        Fin.append
+          (padFin (S.msgLen.eval n) (H.eval (atParam n
+            (pairEncode (H.gen.runAtL n [] (List.ofFn ω))
+              (List.ofFn (splitBits a).1)))))
+          (splitBits a).2 (Fin.cast (handler_output_width H S n) j)) := by
+  have hf : (splitBits a).1 = fun j => a (Fin.castAdd (S.sigLen.eval n) j) :=
+    funext fun j => splitBits_fst a j
+  have hs : (splitBits a).2 = fun j => a (Fin.natAdd (H.domLen.eval n) j) :=
+    funext fun j => splitBits_snd a j
+  rw [hf, hs]
+  rw [handler_finish, (EffFill.ofFn_take_drop_add a).1,
+    (EffFill.ofFn_take_drop_add a).2, hashWord_unary, ← List.ofFn_fin_append]
+  congr 1
+  funext j
+  rw [padFin_apply, ← Fin.coe_cast (handler_output_width H S n) j,
+    ← padFin_apply, padFin_ofFn]
+
+end TCSlib.Cryptography.Authentication.HashSignForward
diff --git a/TCSlib/Cryptography/Authentication/Signatures/HashAndSign/OneQuery.lean b/TCSlib/Cryptography/Authentication/Signatures/HashAndSign/OneQuery.lean
new file mode 100644
index 000000000..3b9536d97
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/Signatures/HashAndSign/OneQuery.lean
@@ -0,0 +1,65 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Games.Machines
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Computations with at most one oracle query
+
+## Main definitions
+
+This module introduces no definitions.
+
+## Main results
+
+* `HashSignFill.eq_pure_of_cost_zero`: a zero-budget computation returns a value.
+* `HashSignFill.one_query_cases`: a one-budget computation either returns immediately or
+  asks one query and returns a function of its answer.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 144.1 (technical support for its one-query reductions).
+-/
+
+namespace TCSlib.Cryptography.Authentication.HashSignFill
+
+open TCSlib.Cryptography.Games
+
+/-- A computation whose every query costs one and whose budget is zero is `pure a` for some
+value `a`: a query would require `1 ≤ 0`. -/
+theorem eq_pure_of_cost_zero {ι α : Type} {spec : OracleSpec ι}
+    (c : OracleComp spec α) (h : c.CostBoundedBy (fun _ => 1) 0) :
+    ∃ a, c = .pure a := by
+  cases c with
+  | pure a => exact ⟨a, rfl⟩
+  | query i x k =>
+    have hbad := (OracleComp.costBoundedBy_query _ _ _ _ _).mp h
+    omega
+
+/-- A computation with unit query costs and budget one either returns immediately or is one
+query followed by a return: `c.CostBoundedBy (fun _ => 1) 1 →
+(∃ a, c = .pure a) ∨ ∃ i x f, c = .query i x (fun y => .pure (f y))`.
+The continuation of a query has budget zero, so each of its
+branches is pure; choosing those return values gives its answer function. -/
+theorem one_query_cases {ι α : Type} {spec : OracleSpec ι}
+    (c : OracleComp spec α) (h : c.CostBoundedBy (fun _ => 1) 1) :
+    (∃ a, c = .pure a) ∨
+      ∃ (i : ι) (x : spec.dom i) (f : spec.rng i → α),
+        c = .query i x (fun y => .pure (f y)) := by
+  classical
+  cases c with
+  | pure a => exact Or.inl ⟨a, rfl⟩
+  | query i x k =>
+    have hk := (OracleComp.costBoundedBy_query _ _ _ _ _).mp h
+    have hp : ∀ y, ∃ a, k y = .pure a :=
+      fun y => eq_pure_of_cost_zero (k y) (hk.2 y)
+    choose f hf using hp
+    exact Or.inr ⟨i, x, f, congrArg (OracleComp.query i x) (funext hf)⟩
+
+end TCSlib.Cryptography.Authentication.HashSignFill
diff --git a/TCSlib/Cryptography/Authentication/Signatures/HashAndSign/OneQuerySampling.lean b/TCSlib/Cryptography/Authentication/Signatures/HashAndSign/OneQuerySampling.lean
new file mode 100644
index 000000000..386e80a5d
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/Signatures/HashAndSign/OneQuerySampling.lean
@@ -0,0 +1,67 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.OneQuery
+import TCSlib.Cryptography.Games.Probability
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Drawing one-query oracle randomness in advance
+
+## Main definitions
+
+This module introduces no definitions.
+
+## Main results
+
+* `HashSignFill.expect_simulate_sample_once`: for a computation making at most one query,
+  freshly sampling the oracle's answer tape has the same law, including its query log, as
+  drawing that tape before the computation.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 144.1 (technical support for the collision-finding reduction).
+-/
+
+namespace TCSlib.Cryptography.Authentication.HashSignFill
+
+open TCSlib.Cryptography.Games
+
+/-- For a computation making at most one query, sampling an independent tape for every
+oracle answer is equivalent to sampling one tape before the computation, for every real
+payoff of the returned value and full query log: if `c.CostBoundedBy (fun _ => 1) 1`, then
+`ProbComp.expect (simulate (QueryImpl.ofComp (σ := Unit) (fun i x =>
+(ProbComp.sample R).bind fun r => .pure (ans i x r))).withLog c ((), [])) g =
+ProbComp.expect (ProbComp.sample R) (fun r => ProbComp.expect
+(simulate (QueryImpl.withLog (fun i x _ => .pure (ans i x r, ()))) c ((), [])) g)`.
+
+**Proof sketch.** A computation of unit cost at most one either returns immediately or
+asks a fixed query and returns a function of its answer (`one_query_cases`). In the first
+case the extra sample integrates a constant. In the second case both expectations reduce
+to the same expectation over the single answer tape, with the same one-entry log. -/
+theorem expect_simulate_sample_once {ι α R : Type} {spec : OracleSpec ι}
+    [Fintype R] [Nonempty R] (ans : ∀ i, spec.dom i → R → spec.rng i)
+    (c : OracleComp spec α) (hc : c.CostBoundedBy (fun _ => 1) 1)
+    (g : α × (Unit × QueryLog spec) → ℝ) :
+    ProbComp.expect
+        (simulate
+          (QueryImpl.ofComp (σ := Unit) (fun i x =>
+            (ProbComp.sample R).bind fun r => .pure (ans i x r))).withLog c ((), [])) g =
+      ProbComp.expect (ProbComp.sample R) (fun r =>
+        ProbComp.expect
+          (simulate
+            (QueryImpl.withLog (fun (i : ι) (x : spec.dom i) (_ : Unit) =>
+              (OracleComp.pure (ans i x r, ()) : ProbComp (spec.rng i × Unit))))
+            c ((), [])) g) := by
+  rcases one_query_cases c hc with ⟨a, rfl⟩ | ⟨i, x, f, rfl⟩
+  · simp only [simulate_pure, ProbComp.expect_pure]
+    exact (ProbComp.expect_const _ _).symm
+  · simp only [simulate_query, QueryImpl.withLog_apply, QueryImpl.ofComp_apply,
+      ProbComp.expect_bind, ProbComp.expect_pure, simulate_pure]
+
+end TCSlib.Cryptography.Authentication.HashSignFill

## ===== TCSlib/Cryptography/Authentication/Signatures/HashAndSign.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Lamport
import TCSlib.Cryptography.Authentication.Signatures.Defs
import TCSlib.Cryptography.Hashing.CollisionResistant
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.FixedGame
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CodecReaders
import TCSlib.Cryptography.Games.Bridges.Experiments
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CollisionGame
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.ForwardGame
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CollisionHandler
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.ForwardHandler
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.OneQuery
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.OneQuerySampling

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hash-and-sign

[PS10, Protocol 144.2]: from a family of collision-resistant hash functions `{h_i}` and a
signature scheme `(Gen, Sign, Ver)` for the hash values,
- `Gen′(1^n)` runs `(pk, sk) ← Gen(1^n)` and `i ← Gen_CRH(1^n)`, and outputs
  `pk′ = (pk, i)` and `sk′ = (sk, i)`;
- `Sign′_{sk′}(m) = Sign_sk(h_i(m))`;
- `Ver′_{pk′}(m, σ) = Ver_pk(h_i(m), σ)`.

Theorem 144.1: if the hash family is collision resistant and the signature scheme is one-time
secure, so is the new scheme.

**Message lengths (decision D-3).** The source hashes `{0,1}^*`. Here, per D-3, the CRH has
`d(n)`-bit inputs, and the new scheme signs `d(n)`-bit messages. Messages of any length up to
`p(n)` embed injectively into `p(n) + 1` bits: append `1`, then pad with `0`s. So the fixed-length
form covers them with `d = p + 1`. The unbounded form (with Merkle–Damgård) is optional.

**Hypotheses on the CRH.**
- **The domain is full:** `D_i` is every `d(n)`-bit string (`hdom` of the theorem), as for the
  source's `{0,1}^*`. Without it the theorem is false. Take a CRH whose `h_i` is constant off a
  small `D_i`: it is collision resistant, since its game counts only collisions inside `D_i`. But
  a forger queries some `m ∉ D_i` and outputs another `m′ ∉ D_i` with the same signature.
- **The hash values fit the signature scheme:** `r(n) = ℓ(n)`, the message length of
  `(Gen, Sign, Ver)` (`hlen`). It is a pointwise equation of lengths, used only inside the
  correctness proof, so the statements carry no casts.

The hash value is `h_i(m)` read at `r(n)` bits (`CRH.hash`, `padFin`), the very string whose
collisions the CRH game counts.

## Main definitions

* `Authentication.hsHashList`, `hsGenFun`, `hsSignFun`, `hsVerFun`: the hash and the three
  algorithms as string functions.
* `Authentication.hashAndSign`: Protocol 144.2 as a `SignatureScheme`, with correctness proved.

## Main results

* The `hsHashList_eq`, key/index and algorithm equations expose the string computations.
* `Authentication.hashAndSign_msgLen`, `hashAndSign_sigLen`, `hashAndSign_gen`,
  `hashAndSign_sign`, `hashAndSign_ver`: the signature-scheme data fields.
* `Authentication.hashAndSign_oneTimeSecure` (Thm 144.1): one-time security from collision
  resistance and one-time security of the original scheme, proved by the two reductions.
* `Authentication.exists_oneTimeSecure_of_crh_owf`: the source's existential form, with
  Lamport's scheme (proved from Theorems 137.2 and 144.1).

## Contents

* `HashAndSign.CodecReaders`: canonical forger codecs and split-word readers.
* `HashAndSign.OneQuery`: zero/one-query computation normal forms.
* `HashAndSign.OneQuerySampling`: drawing one signing tape in advance.
* `HashAndSign.ForwardHandler`: the efficient hashing/forwarding handler.
* `HashAndSign.FixedGame`: the common fixed-tape transcript.
* `HashAndSign.CollisionHandler`: the efficient collision finder and its soundness.
* `HashAndSign.CollisionGame`: the collision-finding probability bound.
* `HashAndSign.ForwardGame`: the original-scheme forgery probability equality.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §5.6, Theorem 144.1 and Protocol 144.2 (book pp. 144–145).
-/

namespace TCSlib.Cryptography.Authentication

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! ### The string functions -/

/-- The hash value `h_i(m)` at `r(n)` bits, with `n = |u|` read off `u = 1^n`: `H.eval` on
`⟨1^n, ⟨i, m⟩⟩`, padded or truncated (`padStr`, the string form of `CRH.hash`). -/
def hsHashList (H : CRH) (u i m : List Bool) : List Bool :=
  padStr H.rangeLen u (H.eval (pairEncode u (pairEncode i m)))

/-- The hash word is the evaluator output padded or truncated to the hash range length. -/
theorem hsHashList_eq (H : CRH) (u i m : List Bool) :
    hsHashList H u i m = padStr H.rangeLen u (H.eval (pairEncode u (pairEncode i m))) := rfl

/-- The key `⟨pk, sk⟩ = Gen(1^n)` of the signature scheme, from the first `coins_Gen(n)` coins of
the layout `⟨⟨⟨1^n, y⟩, α⟩, ρ⟩`. -/
def hsSigKey (S : SignatureScheme) (z : List Bool) : List Bool :=
  S.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
    ((NUPPT.inCoins z).take (S.gen.coins.eval (NUPPT.inParam z).length)))

/-- The signature-key word runs the original generator with empty argument and advice on
the first generator-sized segment of the tape. -/
theorem hsSigKey_eq (S : SignatureScheme) (z : List Bool) :
    hsSigKey S z =
      S.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
        ((NUPPT.inCoins z).take (S.gen.coins.eval (NUPPT.inParam z).length))) := rfl

/-- The index `i = Gen_CRH(1^n)`, from the remaining coins. -/
def hsIdx (S : SignatureScheme) (H : CRH) (z : List Bool) : List Bool :=
  H.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
    ((NUPPT.inCoins z).drop (S.gen.coins.eval (NUPPT.inParam z).length)))

/-- The hash-index word runs the hash generator with empty argument and advice on the tape
after the original generator's coin segment. -/
theorem hsIdx_eq (S : SignatureScheme) (H : CRH) (z : List Bool) :
    hsIdx S H z =
      H.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
        ((NUPPT.inCoins z).drop (S.gen.coins.eval (NUPPT.inParam z).length))) := rfl

/-- `Gen′`: the key `⟨pk′, sk′⟩ = ⟨⟨pk, i⟩, ⟨sk, i⟩⟩`. -/
def hsGenFun (S : SignatureScheme) (H : CRH) (z : List Bool) : List Bool :=
  pairEncode (pairEncode (pairFstD (hsSigKey S z)) (hsIdx S H z))
    (pairEncode (pairSndD (hsSigKey S z)) (hsIdx S H z))

/-- The new key word pairs the public key with the hash index and the secret key with that
same index. -/
theorem hsGenFun_eq (S : SignatureScheme) (H : CRH) (z : List Bool) :
    hsGenFun S H z =
      pairEncode (pairEncode (pairFstD (hsSigKey S z)) (hsIdx S H z))
        (pairEncode (pairSndD (hsSigKey S z)) (hsIdx S H z)) := rfl

/-- `Sign′` on the layout `⟨⟨⟨1^n, ⟨⟨sk, i⟩, m⟩⟩, α⟩, ρ⟩`: `Sign` on `⟨sk, h_i(m)⟩` with the same
coins. -/
def hsSignFun (S : SignatureScheme) (H : CRH) (z : List Bool) : List Bool :=
  S.sign.output (NUPPT.layout (NUPPT.inParam z)
    (pairEncode (pairFstD (pairFstD (NUPPT.inArg z)))
      (hsHashList H (NUPPT.inParam z) (pairSndD (pairFstD (NUPPT.inArg z)))
        (pairSndD (NUPPT.inArg z))))
    [] (NUPPT.inCoins z))

/-- The signing word runs the original signer on the secret key paired with the hash word,
retaining the parameter and coins and using empty advice. -/
theorem hsSignFun_eq (S : SignatureScheme) (H : CRH) (z : List Bool) :
    hsSignFun S H z =
      S.sign.output (NUPPT.layout (NUPPT.inParam z)
        (pairEncode (pairFstD (pairFstD (NUPPT.inArg z)))
          (hsHashList H (NUPPT.inParam z) (pairSndD (pairFstD (NUPPT.inArg z)))
            (pairSndD (NUPPT.inArg z))))
        [] (NUPPT.inCoins z)) := rfl

/-- `Ver′` on `⟨1^n, ⟨⟨pk, i⟩, ⟨m, σ⟩⟩⟩`: `Ver` on `⟨1^n, ⟨pk, ⟨h_i(m), σ⟩⟩⟩`. -/
def hsVerFun (S : SignatureScheme) (H : CRH) (w : List Bool) : List Bool :=
  S.ver (pairEncode (pairFstD w) (pairEncode (pairFstD (pairFstD (pairSndD w)))
    (pairEncode (hsHashList H (pairFstD w) (pairSndD (pairFstD (pairSndD w)))
        (pairFstD (pairSndD (pairSndD w))))
      (pairSndD (pairSndD (pairSndD w))))))

/-- The verification word passes the original public key, hashed message and signature to
the original verifier at the same parameter. -/
theorem hsVerFun_eq (S : SignatureScheme) (H : CRH) (w : List Bool) :
    hsVerFun S H w =
      S.ver (pairEncode (pairFstD w) (pairEncode (pairFstD (pairFstD (pairSndD w)))
        (pairEncode (hsHashList H (pairFstD w) (pairSndD (pairFstD (pairSndD w)))
            (pairFstD (pairSndD (pairSndD w))))
          (pairSndD (pairSndD (pairSndD w)))))) := rfl

/-! ### Efficiency -/

/-- The hash value is polynomial-time on any polynomial-time choice of `u`, `i` and `m`. -/
theorem polyTimeComputable_hsHashList (H : CRH) {u i m : List Bool → List Bool}
    (hu : PolyTimeComputable u) (hi : PolyTimeComputable i) (hm : PolyTimeComputable m) :
    PolyTimeComputable fun z => hsHashList H (u z) (i z) (m z) := by
  have h := (polyTimeComputable_padStr H.rangeLen).comp
    (hu.pairEncode (H.eval_poly.comp (hu.pairEncode (hi.pairEncode hm))))
  refine (congrArg PolyTimeComputable (?_ : (fun z => hsHashList H (u z) (i z) (m z)) = _)).mpr h
  funext z
  simp only [hsHashList, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- The signature key of `Gen′` is polynomial-time. -/
theorem polyTimeComputable_hsSigKey (S : SignatureScheme) : PolyTimeComputable (hsSigKey S) := by
  have ht := (polyTimeComputable_pairTakePoly S.gen.coins).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins)
  have h := S.gen.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam (polyTimeComputable_const []) (polyTimeComputable_const [])
    ht)
  refine (congrArg PolyTimeComputable (?_ : hsSigKey S = _)).mpr h
  funext z
  simp only [hsSigKey, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- The index of `Gen′` is polynomial-time. -/
theorem polyTimeComputable_hsIdx (S : SignatureScheme) (H : CRH) :
    PolyTimeComputable (hsIdx S H) := by
  have hd := (polyTimeComputable_pairDropPoly S.gen.coins).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins)
  have h := H.gen.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam (polyTimeComputable_const []) (polyTimeComputable_const [])
    hd)
  refine (congrArg PolyTimeComputable (?_ : hsIdx S H = _)).mpr h
  funext z
  simp only [hsIdx, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- `Gen′` is polynomial-time. -/
theorem polyTimeComputable_hsGenFun (S : SignatureScheme) (H : CRH) :
    PolyTimeComputable (hsGenFun S H) := by
  have hk := polyTimeComputable_hsSigKey S
  have hi := polyTimeComputable_hsIdx S H
  exact ((polyTimeComputable_pairFstD.comp hk).pairEncode hi).pairEncode
    ((polyTimeComputable_pairSndD.comp hk).pairEncode hi)

/-- `Sign′` is polynomial-time. -/
theorem polyTimeComputable_hsSignFun (S : SignatureScheme) (H : CRH) :
    PolyTimeComputable (hsSignFun S H) := by
  have hA := NUPPT.polyTimeComputable_inArg
  have hl := polyTimeComputable_hsHashList H NUPPT.polyTimeComputable_inParam
    ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD).comp hA)
    (polyTimeComputable_pairSndD.comp hA)
  have h := S.sign.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam
    (((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).comp hA).pairEncode hl)
    (polyTimeComputable_const []) NUPPT.polyTimeComputable_inCoins)
  refine (congrArg PolyTimeComputable (?_ : hsSignFun S H = _)).mpr h
  funext z
  simp only [hsSignFun, Function.comp_apply]

/-- `Ver′` is polynomial-time. -/
theorem polyTimeComputable_hsVerFun (S : SignatureScheme) (H : CRH) :
    PolyTimeComputable (hsVerFun S H) := by
  have hT := polyTimeComputable_pairSndD
  have hl := polyTimeComputable_hsHashList H polyTimeComputable_pairFstD
    ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD).comp hT)
    ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp hT)
  have h := S.ver_poly.comp (polyTimeComputable_pairFstD.pairEncode
    (((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).comp hT).pairEncode
      (hl.pairEncode ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).comp hT))))
  refine (congrArg PolyTimeComputable (?_ : hsVerFun S H = _)).mpr h
  funext z
  simp only [hsVerFun, Function.comp_apply]

/-! ### The machines -/

/-- The machine `Gen′`, with the coins of `Gen` followed by those of `Gen_CRH`. -/
noncomputable abbrev hsGen (S : SignatureScheme) (H : CRH) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_hsGenFun S H) (.add S.gen.coins H.gen.coins)

/-- The hash-and-sign generator uses `S.gen.coinLen n + H.gen.coinLen n` coins at parameter
`n`, with the signature-generator segment first and the hash-index segment second. -/
theorem hsGen_coinLen (S : SignatureScheme) (H : CRH) (n : ℕ) :
    (hsGen S H).coinLen n = S.gen.coinLen n + H.gen.coinLen n :=
  (NUPPT.coinLen_eq (hsGen S H) n).trans
    ((congrArg (fun p : PolyExpr => p.eval n)
      (NUPPT.coins_ofPolyTimeUniform (polyTimeComputable_hsGenFun S H)
        (.add S.gen.coins H.gen.coins))).trans
      ((PolyExpr.eval_add S.gen.coins H.gen.coins n).trans
        (congrArg₂ Nat.add (NUPPT.coinLen_eq S.gen n).symm
          (NUPPT.coinLen_eq H.gen n).symm)))

/-- The machine `Sign′`, with the coins of `Sign`. -/
noncomputable abbrev hsSign (S : SignatureScheme) (H : CRH) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_hsSignFun S H) S.sign.coins

/-- The coins of `Gen′` split as those of `Gen`, then those of `Gen_CRH`. -/
theorem ofFn_coins_split {a b : ℕ} (ρ : Fin (a + b) → Bool) :
    (List.ofFn ρ).take a = List.ofFn (fun j : Fin a => ρ (Fin.castAdd b j)) ∧
      (List.ofFn ρ).drop a = List.ofFn (fun j : Fin b => ρ (Fin.natAdd a j)) := by
  rw [List.ofFn_add]
  constructor
  · exact List.take_left' (by simp)
  · exact List.drop_left' (by simp)

/-- `Gen′` outputs `⟨⟨pk, i⟩, ⟨sk, i⟩⟩` with `⟨pk, sk⟩ = Gen(1^n)` on the first coins and
`i = Gen_CRH(1^n)` on the rest. -/
theorem runAt_hsGen (S : SignatureScheme) (H : CRH) (n : ℕ) (ρ : (hsGen S H).Coins n) :
    (hsGen S H).runAt n [] ρ =
      let σ : Fin (S.gen.coinLen n + H.gen.coinLen n) → Bool :=
        fun j => ρ (Fin.cast (hsGen_coinLen S H n).symm j)
      pairEncode
        (pairEncode (pairFstD (S.gen.runAt n [] fun j => σ (Fin.castAdd (H.gen.coinLen n) j)))
          (H.gen.runAt n [] fun j => σ (Fin.natAdd (S.gen.coinLen n) j)))
        (pairEncode (pairSndD (S.gen.runAt n [] fun j => σ (Fin.castAdd (H.gen.coinLen n) j)))
          (H.gen.runAt n [] fun j => σ (Fin.natAdd (S.gen.coinLen n) j))) := by
  let σ : Fin (S.gen.coinLen n + H.gen.coinLen n) → Bool :=
    fun j => ρ (Fin.cast (hsGen_coinLen S H n).symm j)
  have hρ : List.ofFn ρ = List.ofFn σ := List.ofFn_congr (hsGen_coinLen S H n) ρ
  obtain ⟨h₁, h₂⟩ := ofFn_coins_split σ
  simp only [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform,
    S.gen_uniform.runAtL_eq, H.gen_uniform.runAtL_eq,
    hsGenFun_eq, hsSigKey_eq, hsIdx_eq, NUPPT.inParam_eq, NUPPT.inCoins_eq,
    NUPPT.advInput_eq, NUPPT.layout_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate, ← NUPPT.coinLen_eq S.gen n, hρ, h₁, h₂]
  rfl

/-- `Sign′` on `⟨⟨sk, i⟩, m⟩` is `Sign` on `⟨sk, h_i(m)⟩` with the same coins. -/
theorem runAt_hsSign (S : SignatureScheme) (H : CRH) (n : ℕ) (sk i m : List Bool)
    (r : S.sign.Coins n) :
    (hsSign S H).runAt n (pairEncode (pairEncode sk i) m)
        (NUPPT.coinsCongr (A := S.sign) (B := hsSign S H)
          (NUPPT.coins_ofPolyTimeUniform (polyTimeComputable_hsSignFun S H)
            S.sign.coins).symm n r) =
      S.sign.runAt n (pairEncode sk (hsHashList H (List.replicate n true) i m)) r := by
  rw [NUPPT.runAt_coinsCongr, NUPPT.runAtL_ofPolyTimeUniform, S.sign_uniform.runAt_eq]
  simp only [hsSignFun_eq, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inCoins_eq,
    NUPPT.advInput_eq, NUPPT.layout_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-! ### The scheme -/

/-- **Protocol 144.2** [PS10]: hash with `H`, then sign the hash with `S`. Messages have the
CRH's input length `d(n)`; signatures are `S`'s. `hlen` says that the hash values have `S`'s
message length.

**Proof sketch.** The generator's published coin-length equation splits its tape into the
original signature-generator and hash-index tapes. The signer wrapper's published coin
equivalence carries its tape back to the original signer. The two run equations reduce
verification to `S`'s verifier on the hash word; `hlen` and `List.ofFn_congr` encode that word at
`S`'s message length. Original-scheme correctness applies to these same keys and coin tapes. -/
noncomputable def hashAndSign (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) : SignatureScheme where
  msgLen := H.domLen
  sigLen := S.sigLen
  gen := hsGen S H
  sign := hsSign S H
  ver := hsVerFun S H
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  sign_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  ver_poly := polyTimeComputable_hsVerFun S H
  correct := by
    intro n m rg rs
    let ρ : Fin (S.gen.coinLen n + H.gen.coinLen n) → Bool :=
      fun j => rg (Fin.cast (hsGen_coinLen S H n).symm j)
    let rg₁ : S.gen.Coins n := fun j => ρ (Fin.castAdd (H.gen.coinLen n) j)
    let ri : H.gen.Coins n := fun j => ρ (Fin.natAdd (S.gen.coinLen n) j)
    let i : List Bool := H.gen.runAt n [] ri
    let e : S.sign.Coins n ≃ (hsSign S H).Coins n :=
      NUPPT.coinsCongr (A := S.sign) (B := hsSign S H)
        (NUPPT.coins_ofPolyTimeUniform (polyTimeComputable_hsSignFun S H)
          S.sign.coins).symm n
    have hgen : (hsGen S H).runAt n [] rg =
        pairEncode
          (pairEncode (pairFstD (S.gen.runAt n [] rg₁)) i)
          (pairEncode (pairSndD (S.gen.runAt n [] rg₁)) i) :=
      runAt_hsGen S H n rg
    simp only [hgen, pairFstD_pairEncode, pairSndD_pairEncode]
    rw [← e.apply_symm_apply rs, runAt_hsSign]
    simp only [hsVerFun_eq, atParam_eq, pairFstD_pairEncode, pairSndD_pairEncode]
    let w : List Bool := H.eval (pairEncode (List.replicate n true)
      (pairEncode i (List.ofFn m)))
    have hl : H.rangeLen.eval (List.replicate n true).length = S.msgLen.eval n :=
      (congrArg (fun k : ℕ => H.rangeLen.eval k)
        (List.length_replicate (n := n) (a := true))).trans (hlen n)
    let mh : Fin (S.msgLen.eval n) → Bool := fun j =>
      padFin (H.rangeLen.eval (List.replicate n true).length) w (Fin.cast hl.symm j)
    have hm₀ : List.ofFn mh = hsHashList H (List.replicate n true) i (List.ofFn m) :=
      (List.ofFn_congr hl
        (padFin (H.rangeLen.eval (List.replicate n true).length) w)).symm.trans
          ((ofFn_padFin_eq_padStr H.rangeLen (List.replicate n true) w).trans
            (hsHashList_eq H (List.replicate n true) i (List.ofFn m)).symm)
    simpa only [atParam_eq, hm₀] using S.correct n mh rg₁ (e.symm rs)

/-- Hash-and-sign uses the hash family's domain length as its message length. -/
theorem hashAndSign_msgLen (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) :
    (hashAndSign H S hlen).msgLen = H.domLen := rfl

/-- Hash-and-sign retains the original signature length. -/
theorem hashAndSign_sigLen (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) :
    (hashAndSign H S hlen).sigLen = S.sigLen := rfl

/-- Hash-and-sign uses the combined signature-key and hash-index generator. -/
theorem hashAndSign_gen (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) :
    (hashAndSign H S hlen).gen = hsGen S H := rfl

/-- Hash-and-sign uses the signer that hashes its message before calling the original signer. -/
theorem hashAndSign_sign (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) :
    (hashAndSign H S hlen).sign = hsSign S H := rfl

/-- Hash-and-sign uses the verifier that hashes its message before calling the original verifier. -/
theorem hashAndSign_ver (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) :
    (hashAndSign H S hlen).ver = hsVerFun S H := rfl

/-! ### Theorem 144.1 -/

/-- When hash and signature message widths agree, the hash-and-sign hash word equals the
word used by the two reduction handlers, including on arbitrary list inputs: under `hlen`,
`hsHashList H (List.replicate n true) i m =
HashSignForward.hashWord H S (List.replicate n true) i m`. -/
theorem hsHashList_eq_hashWord (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) (n : ℕ) (i m : List Bool) :
    hsHashList H (List.replicate n true) i m =
      HashSignForward.hashWord H S (List.replicate n true) i m := by
  simp only [hsHashList_eq, HashSignForward.hashWord_eq, padStr_eq,
    List.length_replicate, hlen n]

/-- For a computation making at most one signing query, the hash-and-sign signing oracle
has the same expected logged payoff as sampling one original signing tape before the run:
if `c.CostBoundedBy (fun _ => 1) 1`, then
`ProbComp.expect (simulate ((hashAndSign H S hlen).signImpl n (pairEncode sk i)).withLog c
((), [])) g = ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
ProbComp.expect (simulate (HashSignFill.fixedSign H S n sk i rs).withLog c ((), [])) g)`.

**Proof sketch.** First move the wrapper signer's randomness outside the simulation using
the one-query sampling law. Its coin bijection with the original signer preserves uniform
sampling. The published wrapper run equation and the hash-width equation identify each
fixed-tape answer with the common experiment's answer. -/
theorem expect_hashAndSign_sign (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) (n : ℕ) (sk i : List Bool)
    (c : OracleComp (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
      (fun _ => S.sigLen.eval n)) (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool))
    (hc : c.CostBoundedBy (fun _ => 1) 1)
    (g : (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
        (fun _ => S.sigLen.eval n))) → ℝ) :
    ProbComp.expect
        (simulate ((hashAndSign H S hlen).signImpl n (pairEncode sk i)).withLog c ((), [])) g =
      ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
        ProbComp.expect (simulate (HashSignFill.fixedSign H S n sk i rs).withLog c ((), []))
          g) := by
  have hraw := HashSignFill.expect_simulate_sample_once
    (fun (_ : Fin 1) (m : Fin (H.domLen.eval n) → Bool) (rs : (hsSign S H).Coins n) =>
      padFin (S.sigLen.eval n)
        ((hsSign S H).runAt n (pairEncode (pairEncode sk i) (List.ofFn m)) rs)) c hc g
  have hfirst : ProbComp.expect
      (simulate ((hashAndSign H S hlen).signImpl n (pairEncode sk i)).withLog c ((), [])) g =
      ProbComp.expect (ProbComp.sample ((hsSign S H).Coins n)) (fun rs =>
        ProbComp.expect
          (simulate (QueryImpl.withLog (fun (_ : Fin 1) (m : Fin (H.domLen.eval n) → Bool)
            (_ : Unit) => (OracleComp.pure
              (padFin (S.sigLen.eval n)
                ((hsSign S H).runAt n (pairEncode (pairEncode sk i) (List.ofFn m)) rs), ()) :
              ProbComp ((Fin (S.sigLen.eval n) → Bool) × Unit)))) c ((), [])) g) := by
    simpa only [SignatureScheme.signImpl_eq, hashAndSign_sign, hashAndSign_sigLen] using hraw
  rw [hfirst]
  let e : S.sign.Coins n ≃ (hsSign S H).Coins n :=
    NUPPT.coinsCongr (A := S.sign) (B := hsSign S H)
      (NUPPT.coins_ofPolyTimeUniform (polyTimeComputable_hsSignFun S H) S.sign.coins).symm n
  rw [← ProbComp.expect_sample_equiv e]
  apply congrArg (ProbComp.expect (ProbComp.sample (S.sign.Coins n)))
  funext rs
  have hi : (fun (_ : Fin 1) (m : Fin (H.domLen.eval n) → Bool) (_ : Unit) =>
      (OracleComp.pure (padFin (S.sigLen.eval n)
        ((hsSign S H).runAt n (pairEncode (pairEncode sk i) (List.ofFn m)) (e rs)), ()) :
        ProbComp ((Fin (S.sigLen.eval n) → Bool) × Unit))) =
      HashSignFill.fixedSign H S n sk i rs := by
    funext j m s
    rw [HashSignFill.fixedSign_apply, HashSignFill.hashedReply_eq,
      runAt_hsSign, hsHashList_eq_hashWord H S hlen]
  rw [hi]

/-- Hash-and-sign accepts a message/signature pair exactly when the original scheme accepts
the padded hash of that message with the same signature:
`(hashAndSign H S hlen).Accepts n (pairEncode pk i) m σ ↔
S.Accepts n pk (padFin (S.msgLen.eval n) (H.eval (atParam n (pairEncode i (List.ofFn m))))) σ`. -/
theorem hashAndSign_accepts_iff (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) (n : ℕ) (pk i : List Bool)
    (m : Fin (H.domLen.eval n) → Bool) (σ : Fin (S.sigLen.eval n) → Bool) :
    (hashAndSign H S hlen).Accepts n (pairEncode pk i) m σ ↔
      S.Accepts n pk (padFin (S.msgLen.eval n)
        (H.eval (atParam n (pairEncode i (List.ofFn m))))) σ := by
  simp only [SignatureScheme.accepts_iff, hashAndSign_ver, hsVerFun_eq, atParam_eq,
    pairFstD_pairEncode, pairSndD_pairEncode, hsHashList_eq_hashWord H S hlen,
    HashSignForward.hashWord_unary]

/-- On concatenated original-generator and hash-generator tapes, the combined generator
returns the original public and secret keys each paired with the same generated hash index:
`(hsGen S H).runAt n [] (EnsembleLemmas.coinsEquiv (hsGen_coinLen S H n) (rg, ri)) =
pairEncode (pairEncode pk i) (pairEncode sk i)`, where
`pk = pairFstD (S.gen.runAt n [] rg)`, `sk = pairSndD (S.gen.runAt n [] rg)` and
`i = H.gen.runAt n [] ri`.

**Proof sketch.** The published coin-splitting bijection has the concatenated encoding.
Transporting to the combined width preserves that encoding, so its two projections are
the original tapes. The combined generator's run equation then gives the paired keys. -/
theorem runAt_hsGen_split (S : SignatureScheme) (H : CRH) (n : ℕ)
    (rg : S.gen.Coins n) (ri : H.gen.Coins n) :
    (hsGen S H).runAt n []
        (EnsembleLemmas.coinsEquiv (hsGen_coinLen S H n) (rg, ri)) =
      pairEncode
        (pairEncode (pairFstD (S.gen.runAt n [] rg)) (H.gen.runAt n [] ri))
        (pairEncode (pairSndD (S.gen.runAt n [] rg)) (H.gen.runAt n [] ri)) := by
  let ρ := EnsembleLemmas.coinsEquiv (hsGen_coinLen S H n) (rg, ri)
  let σ : Fin (S.gen.coinLen n + H.gen.coinLen n) → Bool :=
    fun j => ρ (Fin.cast (hsGen_coinLen S H n).symm j)
  have hσ : σ = Fin.append rg ri := by
    apply List.ofFn_injective
    exact (List.ofFn_congr (hsGen_coinLen S H n) ρ).symm.trans
      ((EnsembleLemmas.ofFn_coinsEquiv (hsGen_coinLen S H n) (rg, ri)).trans
        (List.ofFn_fin_append rg ri).symm)
  rw [runAt_hsGen]
  change pairEncode
    (pairEncode (pairFstD (S.gen.runAt n [] (fun j => σ (Fin.castAdd (H.gen.coinLen n) j))))
      (H.gen.runAt n [] (fun j => σ (Fin.natAdd (S.gen.coinLen n) j))))
    (pairEncode (pairSndD (S.gen.runAt n [] (fun j => σ (Fin.castAdd (H.gen.coinLen n) j))))
      (H.gen.runAt n [] (fun j => σ (Fin.natAdd (S.gen.coinLen n) j)))) = _
  simp only [hσ, Fin.append_left, Fin.append_right]

/-- The hash-and-sign forgery probability equals the common transcript's success
probability averaged over independent original key, hash-index, adversary and signing tapes:
`accept ((hashAndSign H S hlen).forgeGame A 1 n) = 𝔼 rg : S.gen.Coins n, 𝔼 ri : H.gen.Coins n,
𝔼 rA : A.Coins n, 𝔼 rs : S.sign.Coins n, ProbComp.prob
(HashSignFill.transcript H S A n pk sk i rs rA) (HashSignFill.Success H S n pk i)`,
writing `𝔼 x : X, f x` for `ProbComp.expect (ProbComp.sample X) (fun x => f x)`, with
`pk = pairFstD (S.gen.runAt n [] rg)`, `sk = pairSndD (S.gen.runAt n [] rg)` and
`i = H.gen.runAt n [] ri`.

**Proof sketch.** Read the forgery experiment through its published equation. Reindex the
combined generator tape by the product of the original generator tapes and use its run
equation. Finally move the single signing tape outside the logged simulation and identify
verification with original-scheme verification on the hash. -/
theorem hashAndSign_forge_eq_common (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) (A : NUPPT) (n : ℕ) :
    accept ((hashAndSign H S hlen).forgeGame A 1 n) =
      ProbComp.expect (ProbComp.sample (S.gen.Coins n)) (fun rg =>
        ProbComp.expect (ProbComp.sample (H.gen.Coins n)) (fun ri =>
          ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA =>
            ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
              ProbComp.prob
                (HashSignFill.transcript H S A n (pairFstD (S.gen.runAt n [] rg))
                  (pairSndD (S.gen.runAt n [] rg)) (H.gen.runAt n [] ri) rs rA)
                (HashSignFill.Success H S n (pairFstD (S.gen.runAt n [] rg))
                  (H.gen.runAt n [] ri)))))) := by
  classical
  rw [SignatureScheme.forgeGame_eq, accept_eq, ProbComp.prob_eq_expect]
  simp only [ProbComp.expect_bind, ProbComp.expect_pure, decide_eq_true_eq,
    hashAndSign_gen]
  rw [← ProbComp.expect_sample_equiv (EnsembleLemmas.coinsEquiv (hsGen_coinLen S H n))]
  rw [← Bridge.expect_sample_pair]
  simp only [ProbComp.expect_bind, ProbComp.expect_pure]
  apply congrArg (ProbComp.expect (ProbComp.sample (S.gen.Coins n)))
  funext rg
  apply congrArg (ProbComp.expect (ProbComp.sample (H.gen.Coins n)))
  funext ri
  simp only [runAt_hsGen_split, pairFstD_pairEncode, pairSndD_pairEncode,
    SignatureScheme.forgerCodec_eq_bitCodec, hashAndSign_msgLen, hashAndSign_sigLen]
  apply congrArg (ProbComp.expect (ProbComp.sample (A.Coins n)))
  funext rA
  rw [expect_hashAndSign_sign H S hlen n _ _ _ (A.toCompOn_costBoundedBy _ n 1 _ rA)]
  apply congrArg (ProbComp.expect (ProbComp.sample (S.sign.Coins n)))
  funext rs
  simp only [HashSignFill.transcript_eq, ProbComp.prob_eq_expect,
    HashSignFill.success_iff, hashAndSign_accepts_iff]
  apply congrArg (ProbComp.expect _)
  funext res
  split <;> rfl

/-- Every successful common transcript either gives a fresh-message hash collision or
is a successful forgery after forwarding hashes to the original signing oracle: under `hlen`,
`HashSignFill.Success H S n pk i res →
HashSignFill.CollisionCase H S n i res ∨ HashSignFill.ForwardSuccess H S n pk i res`.

**Proof sketch.** If a queried message has the final message's hash, use source freshness
for the collision case. Otherwise the final hash is fresh among forwarded queries.
The range-width equation transports equality of the forwarded hash vectors back to
equality of CRH hash vectors, including at width zero. -/
theorem hashAndSign_success_cases (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) (n : ℕ) (pk i : List Bool)
    (res : (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
        (fun _ => S.sigLen.eval n))))
    (h : HashSignFill.Success H S n pk i res) :
    HashSignFill.CollisionCase H S n i res ∨
      HashSignFill.ForwardSuccess H S n pk i res := by
  classical
  obtain ⟨haccept, hfresh⟩ := (HashSignFill.success_iff H S n pk i res).mp h
  by_cases heq : ∃ e ∈ res.2.2,
      H.hash n i e.2.1 = H.hash n i (splitBits res.1).1
  · exact Or.inl ((HashSignFill.collisionCase_iff H S n i res).mpr ⟨hfresh, heq⟩)
  · apply Or.inr
    apply (HashSignFill.forwardSuccess_iff H S n pk i res).mpr
    constructor
    · simpa only [HashSignFill.queryHash_eq] using haccept
    · intro e hem hsame
      apply heq
      refine ⟨e, hem, ?_⟩
      funext j
      have hv := congrFun hsame (Fin.cast (hlen n) j)
      simpa only [HashSignFill.queryHash_eq, CRH.hash_eq, padFin_apply, Fin.coe_cast] using hv

/-- **Theorem 144.1: hash-and-sign is one-time secure** [PS10, Theorem 144.1] when the hash
family is collision resistant on its full domain and the signature scheme is one-time secure.

**Proof sketch.** The source's two reductions are implemented with independent key,
hash-index, adversary and signing tapes; a one-query sampling law couples their common
logged transcript, including no-query and codec-timeout outputs.
1. Let `A` be a one-time forger against `hashAndSign`, querying `m` (or nothing) and outputting
   `(m′, σ′)` with `m′ ≠ m` and `Ver_pk(h_i(m′), σ′)` accepting.
2. *Case `h_i(m′) = h_i(m)`.* The collision finder `B(1^n, i)` samples `(pk, sk) ← Gen(1^n)`,
   runs `A` on `⟨pk, i⟩` answering its query with `Sign_sk(h_i(m))`, and outputs `(m, m′)`
   (using the initial zero word if no query was made). For the queried case, freshness and
   `hdom` give a collision. `B` answers `A`'s queries itself, so it is a machine by T1
   (`Games.exists_handlerMachine`), with `advIn` supplying `⟨pk, i⟩`, `out` returning `(m, m′)`,
   and the seed holding the coins of `Gen` and `Sign`.
3. *Case `A` made no query or `h_i(m′) ≠ h_i(m)`.* The forger `C^{Sign_sk}(1^n, pk)` samples
   `i ← Gen_CRH(1^n)`, runs `A` on `⟨pk, i⟩` forwarding its query `m` as `h_i(m)`, and outputs
   `(h_i(m′), σ′)`. That is a one-time forgery against `S`: `C` makes at most one query, and
   `h_i(m′)` was not queried. T2 (`Games.exists_interactiveHandlerMachine`) uses
   `advIn = ⟨pk, i⟩`, forwards each query as `h_i(m)` (`perCall = 1`), and finishes without
   another oracle query (`finCall = 0`).
4. `A`'s success probability is at most `B`'s plus `C`'s, both negligible. -/
theorem hashAndSign_oneTimeSecure (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) (hdom : ∀ n i x, H.inDom n i x = true)
    (hH : H.CollisionResistant) (hS : S.OneTimeSecure) :
    (hashAndSign H S hlen).OneTimeSecure := by
  classical
  apply (SignatureScheme.oneTimeSecure_iff _).mpr
  intro A
  obtain ⟨B, hB⟩ := HashSignFill.exists_collisionGame_bound H S A hdom
  obtain ⟨C, hC⟩ := HashSignFill.exists_forwardGame H S A
  obtain ⟨εB, hεB, hboundB⟩ := (CRH.collisionResistant_iff H).mp hH B
  obtain ⟨εC, hεC, hboundC⟩ := (SignatureScheme.oneTimeSecure_iff S).mp hS C
  refine ⟨fun n => εB n + εC n, hεB.add hεC, fun n => ?_⟩
  rw [hashAndSign_forge_eq_common H S hlen A n]
  refine le_trans ?_ (add_le_add (hboundB n) (hboundC n))
  refine le_trans ?_ (add_le_add (hB n) (le_of_eq (hC n).symm))
  -- Bound the success event by the union before averaging the independent tapes.
  rw [← ProbComp.expect_add]
  apply ProbComp.expect_mono
  intro rg
  rw [← ProbComp.expect_add]
  apply ProbComp.expect_mono
  intro ri
  rw [← ProbComp.expect_add]
  apply ProbComp.expect_mono
  intro rA
  rw [← ProbComp.expect_add]
  apply ProbComp.expect_mono
  intro rs
  exact (ProbComp.prob_mono _ (fun res hs =>
    hashAndSign_success_cases H S hlen n _ _ res hs)).trans (ProbComp.prob_or_le _ _ _)

/-- **The existential form of Theorem 144.1** [PS10]: a collision-resistant hash family
`{0,1}^{d(n)} → {0,1}^n` on its full domain, and a one-way function, give a one-time secure
signature scheme for `d(n)`-bit messages: hash-and-sign over Lamport's scheme
(`lamport_oneTimeSecure`). Lamport signs `n`-bit messages, so the hash values have `n` bits. -/
theorem exists_oneTimeSecure_of_crh_owf (H : CRH) (hn : ∀ n, H.rangeLen.eval n = n)
    (hdom : ∀ n i x, H.inDom n i x = true) (hH : H.CollisionResistant)
    (L : PolyExpr) (f : ∀ n, (Fin n → Bool) → (Fin (L.eval n) → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hfE : ∀ n (x : Fin n → Bool), E (NUPPT.advInput n (List.ofFn x)) = List.ofFn (f n x))
    (hf : (lamportOWF L f).StrongOneWay) :
    ∃ S : SignatureScheme, S.msgLen = H.domLen ∧ S.OneTimeSecure :=
  let hlen : ∀ n, H.rangeLen.eval n = (lamport L f E hE hfE).msgLen.eval n :=
    fun n => (hn n).trans
      ((congrArg (fun p : PolyExpr => p.eval n)
        (lamport_msgLen L f E hE hfE)).trans (PolyExpr.eval_var n)).symm
  ⟨hashAndSign H (lamport L f E hE hfE) hlen,
    hashAndSign_msgLen H (lamport L f E hE hfE) hlen,
    hashAndSign_oneTimeSecure H (lamport L f E hE hfE) hlen hdom hH
      (lamport_oneTimeSecure L f E hE hfE hf)⟩

end TCSlib.Cryptography.Authentication

## ===== TCSlib/Cryptography/Authentication/Signatures/HashAndSign/CodecReaders.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Signature forger codecs read through their published fields

## Main definitions

This module introduces no definitions.

## Main results

* `Games.MachineCodec.ext_of_fields`: codecs with equal decoding, entry encoding,
  and timeout fields are equal.
* `Authentication.SignatureScheme.forgerCodec_eq_bitCodec`: the signature
  forger codec equals the canonical bit codec at its declared lengths.
* `HashSignFill.splitBits_append`, `splitBits_pad_concat`: splitting fixed-width
  concatenated words recovers their components, including zero widths.

The generic extensionality lemma is a promotion request for `Games/Machines`;
the signature-specific reader belongs beside its definition in `Signatures/Defs`.
The two split-word readers are promotion requests for `Authentication/Encoding`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Theorem 144.1 (technical support for its machine reductions).
-/

namespace TCSlib.Cryptography.Games.MachineCodec

/-- Two machine codecs are equal when their move decoders, entry encoders and timeout
outputs are equal:
`a.decodeMove = b.decodeMove → a.encodeEntry = b.encodeEntry → a.timeout = b.timeout → a = b`.
These are all three fields of `MachineCodec`.

**Proof sketch.** Destructure the two records. Substituting the three field equalities
leaves the same constructor on both sides. -/
theorem ext_of_fields {ι α : Type} {spec : OracleSpec ι}
    (a b : MachineCodec spec α)
    (hdecode : a.decodeMove = b.decodeMove)
    (hentry : a.encodeEntry = b.encodeEntry)
    (htimeout : a.timeout = b.timeout) : a = b := by
  cases a
  cases b
  cases hdecode
  cases hentry
  cases htimeout
  rfl

end TCSlib.Cryptography.Games.MachineCodec

namespace TCSlib.Cryptography.Authentication.SignatureScheme

open TCSlib.Cryptography.Games

/-- The signature forger codec is the bit codec with message-length queries,
signature-length answers and a message-plus-signature-length final output:
`S.forgerCodec n = bitCodec (fun _ : Fin 1 => S.msgLen.eval n) (fun _ : Fin 1 => S.sigLen.eval n)
(S.msgLen.eval n + S.sigLen.eval n)`.

**Proof sketch.** The published decoding, entry-encoding and timeout equations agree
with those of the bit codec. Codec extensionality turns those field equations into
equality of the complete records; neither codec's definition is unfolded. -/
theorem forgerCodec_eq_bitCodec (S : SignatureScheme) (n : ℕ) :
    S.forgerCodec n =
      bitCodec (fun _ : Fin 1 => S.msgLen.eval n) (fun _ : Fin 1 => S.sigLen.eval n)
        (S.msgLen.eval n + S.sigLen.eval n) := by
  apply MachineCodec.ext_of_fields
  · funext w
    exact (S.forgerCodec_decodeMove n w).trans
      (bitCodec_decodeMove (fun _ : Fin 1 => S.msgLen.eval n)
        (fun _ : Fin 1 => S.sigLen.eval n) (S.msgLen.eval n + S.sigLen.eval n) w).symm
  · funext e
    exact (S.forgerCodec_encodeEntry n e).trans
      (bitCodec_encodeEntry (fun _ : Fin 1 => S.msgLen.eval n)
        (fun _ : Fin 1 => S.sigLen.eval n) (S.msgLen.eval n + S.sigLen.eval n) e).symm
  · exact (S.forgerCodec_timeout n).trans
      (bitCodec_timeout (fun _ : Fin 1 => S.msgLen.eval n)
        (fun _ : Fin 1 => S.sigLen.eval n) (S.msgLen.eval n + S.sigLen.eval n)).symm

end TCSlib.Cryptography.Authentication.SignatureScheme

namespace TCSlib.Cryptography.Authentication.HashSignFill

/-- Splitting the concatenation of two fixed-width words recovers the two words:
`splitBits (Fin.append x y) = (x, y)`. -/
theorem splitBits_append {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) :
    splitBits (Fin.append x y) = (x, y) := by
  apply Prod.ext
  · funext j
    rw [splitBits_fst, Fin.append_left]
  · funext j
    rw [splitBits_snd, Fin.append_right]

/-- Reading the concatenated encodings of two words at their total width and splitting the
result recovers the original words: `splitBits (padFin (a + b) (List.ofFn x ++ List.ofFn y)) =
(x, y)`. This also covers zero widths. -/
theorem splitBits_pad_concat {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) :
    splitBits (padFin (a + b) (List.ofFn x ++ List.ofFn y)) = (x, y) := by
  rw [← List.ofFn_fin_append, padFin_ofFn, splitBits_append]

end TCSlib.Cryptography.Authentication.HashSignFill

## ===== TCSlib/Cryptography/Authentication/Signatures/HashAndSign/CollisionGame.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CollisionHandler
import TCSlib.Cryptography.Games.Bridges.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The collision probability in the hash-and-sign reduction

## Main definitions

* `HashSignFill.CollisionCase`: the final message is fresh and has the same hash as some
  logged query.

## Main results

* `HashSignFill.exists_collisionGame_bound`: the common transcript's collision case is
  bounded by the collision probability of one machine.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 144.1, collision-finding case.
-/

namespace TCSlib.Cryptography.Authentication.HashSignFill

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-- The collision case of a common transcript: its final message is distinct from every
logged query, and some logged query has its hash,
`CollisionCase H S n i res ↔ (∀ e ∈ res.2.2, e.2.1 ≠ m) ∧
∃ e ∈ res.2.2, H.hash n i e.2.1 = H.hash n i m`, where `m = (splitBits res.1).1`
[PS10, Theorem 144.1]. -/
def CollisionCase (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
    (res : (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
        (fun _ => S.sigLen.eval n)))) : Prop :=
  (∀ e ∈ res.2.2, e.2.1 ≠ (splitBits res.1).1) ∧
    ∃ e ∈ res.2.2, H.hash n i e.2.1 = H.hash n i (splitBits res.1).1

/-- The collision case holds exactly when the final message is fresh and a logged query
has the same hash as that message: `CollisionCase H S n i res ↔ (∀ e ∈ res.2.2, e.2.1 ≠ m) ∧
∃ e ∈ res.2.2, H.hash n i e.2.1 = H.hash n i m`, where `m = (splitBits res.1).1`. -/
theorem collisionCase_iff (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
    (res : (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
        (fun _ => S.sigLen.eval n)))) :
    CollisionCase H S n i res ↔
      (∀ e ∈ res.2.2, e.2.1 ≠ (splitBits res.1).1) ∧
        ∃ e ∈ res.2.2, H.hash n i e.2.1 = H.hash n i (splitBits res.1).1 := Iff.rfl

/-- A machine's collision probability bounds the collision case of the common transcript,
averaged over the original keys, hash index, adversary tape and signing tape: if
`∀ n i x, H.inDom n i x = true`, then `∃ B : NUPPT, ∀ n, 𝔼 rg : S.gen.Coins n,
𝔼 ri : H.gen.Coins n, 𝔼 rA : A.Coins n, 𝔼 rs : S.sign.Coins n, ProbComp.prob
(transcript H S A n pk sk i rs rA) (CollisionCase H S n i) ≤ accept (H.collisionGame B n)`,
writing `𝔼 x : X, f x` for `ProbComp.expect (ProbComp.sample X) (fun x => f x)`, with
`pk = pairFstD (S.gen.runAt n [] rg)`, `sk = pairSndD (S.gen.runAt n [] rg)` and
`i = H.gen.runAt n [] ri` [PS10, Theorem 144.1].

**Proof sketch.** T1 constructs a machine with the same deterministic transcript on each
choice of seed and adversary tape. In the collision case its output satisfies the exact
CRH collision predicate. Average this pointwise indicator inequality. The seed equivalence
concatenates the original generator and signer tapes; the T1 coin equivalence then turns
the seed and adversary tapes into uniform collision-finder coins. Independent samples may
be exchanged, so the resulting average is exactly the CRH game's acceptance probability. -/
theorem exists_collisionGame_bound (H : CRH) (S : SignatureScheme) (A : NUPPT)
    (hdom : ∀ n i x, H.inDom n i x = true) :
    ∃ B : NUPPT, ∀ n,
      ProbComp.expect (ProbComp.sample (S.gen.Coins n)) (fun rg =>
        ProbComp.expect (ProbComp.sample (H.gen.Coins n)) (fun ri =>
          ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA =>
            ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
              ProbComp.prob (transcript H S A n (pairFstD (S.gen.runAt n [] rg))
                (pairSndD (S.gen.runAt n [] rg)) (H.gen.runAt n [] ri) rs rA)
                (CollisionCase H S n (H.gen.runAt n [] ri)))))) ≤
        accept (H.collisionGame B n) := by
  classical
  obtain ⟨B, hB⟩ := exists_collisionMachine_transcript H S A
  refine ⟨B, fun n => ?_⟩
  obtain ⟨φ, hφ⟩ := hB n
  let seed : S.gen.Coins n × S.sign.Coins n ≃
      (Fin ((collisionHandler H S).seedLen.eval n) → Bool) :=
    EnsembleLemmas.seedEquiv (A := S.gen) (B := S.sign) (collisionHandler_seedLen H S) n
  let win : List Bool → B.Coins n → Prop := fun i r =>
    let xx := splitBits (padFin (H.domLen.eval n + H.domLen.eval n) (B.runAt n i r))
    H.inDom n i xx.1 = true ∧ H.inDom n i xx.2 = true ∧ xx.1 ≠ xx.2 ∧
      H.hash n i xx.1 = H.hash n i xx.2
  let payoff : List Bool → B.Coins n → ℝ := fun i r => if win i r then 1 else 0
  have hpoint (rg : S.gen.Coins n) (rs : S.sign.Coins n) (rA : A.Coins n) (i : List Bool) :
      ProbComp.prob (transcript H S A n (pairFstD (S.gen.runAt n [] rg))
        (pairSndD (S.gen.runAt n [] rg)) i rs rA) (CollisionCase H S n i) ≤
        payoff i (φ (seed (rg, rs), rA)) := by
    obtain ⟨a, s, L, ht, hinv, hrun⟩ := hφ i rg rs (seed (rg, rs)) rA
      (EnsembleLemmas.seedEquiv_ofFn (collisionHandler_seedLen H S) n (rg, rs))
    rw [ht, ProbComp.prob_pure]
    dsimp only [payoff]
    by_cases hcase : CollisionCase H S n i (a, ((), L))
    · have hclauses := (collisionCase_iff H S n i (a, ((), L))).mp hcase
      have hw : win i (φ (seed (rg, rs), rA)) := by
        dsimp only [win]
        rw [hrun]
        exact collisionHandler_collision H S hdom n (pairSndD (S.gen.runAt n [] rg)) i rs
          (seed (rg, rs)) a s L hinv hclauses.1 hclauses.2
      simp only [hcase, hw, if_true]
      exact le_rfl
    · simp only [hcase, if_false]
      split_ifs <;> norm_num
  have hcoins (i : List Bool) :
      ProbComp.expect (ProbComp.sample (S.gen.Coins n)) (fun rg =>
        ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
          ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA =>
            payoff i (φ (seed (rg, rs), rA))))) =
        ProbComp.expect (ProbComp.sample (B.Coins n)) (fun r =>
          payoff i r) := by
    calc
      _ = ProbComp.expect (ProbComp.sample (S.gen.Coins n × S.sign.Coins n)) (fun p =>
          ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA =>
            payoff i (φ (seed p, rA)))) := by
        simpa only [ProbComp.expect_bind, ProbComp.expect_pure] using
          Bridge.expect_sample_pair (fun p : S.gen.Coins n × S.sign.Coins n =>
            ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA =>
              payoff i (φ (seed p, rA))))
      _ = ProbComp.expect
          (ProbComp.sample (Fin ((collisionHandler H S).seedLen.eval n) → Bool)) (fun ω =>
          ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA =>
            payoff i (φ (ω, rA)))) := by
        exact ProbComp.expect_sample_equiv seed (fun ω =>
          ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA => payoff i (φ (ω, rA))))
      _ = ProbComp.expect (ProbComp.sample
          ((Fin ((collisionHandler H S).seedLen.eval n) → Bool) × A.Coins n)) (fun p =>
          payoff i (φ p)) := by
        simpa only [ProbComp.expect_bind, ProbComp.expect_pure] using
          Bridge.expect_sample_pair (fun p :
            (Fin ((collisionHandler H S).seedLen.eval n) → Bool) × A.Coins n =>
            payoff i (φ p))
      _ = _ := by
        exact ProbComp.expect_sample_equiv φ (payoff i)
  calc
    _ ≤ ProbComp.expect (ProbComp.sample (S.gen.Coins n)) (fun rg =>
        ProbComp.expect (ProbComp.sample (H.gen.Coins n)) (fun ri =>
          ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA =>
            ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
              payoff (H.gen.runAt n [] ri) (φ (seed (rg, rs), rA)))))) := by
      apply ProbComp.expect_mono
      intro rg
      apply ProbComp.expect_mono
      intro ri
      apply ProbComp.expect_mono
      intro rA
      exact ProbComp.expect_mono _ (fun rs => hpoint rg rs rA (H.gen.runAt n [] ri))
    _ = ProbComp.expect (ProbComp.sample (H.gen.Coins n)) (fun ri =>
        ProbComp.expect (ProbComp.sample (S.gen.Coins n)) (fun rg =>
          ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
            ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA =>
              payoff (H.gen.runAt n [] ri) (φ (seed (rg, rs), rA)))))) := by
      rw [ProbComp.expect_sample_comm]
      congr 1
      funext ri
      congr 1
      funext rg
      exact ProbComp.expect_sample_comm _
    _ = ProbComp.expect (ProbComp.sample (H.gen.Coins n)) (fun ri =>
        ProbComp.expect (ProbComp.sample (B.Coins n)) (fun r =>
          payoff (H.gen.runAt n [] ri) r)) := by
      congr 1
      funext ri
      exact hcoins (H.gen.runAt n [] ri)
    _ = accept (H.collisionGame B n) := by
      conv_rhs =>
        simp only [accept_eq, CRH.collisionGame_eq, ProbComp.prob_bind, ProbComp.prob_pure,
          decide_eq_true_eq]

end TCSlib.Cryptography.Authentication.HashSignFill

## ===== TCSlib/Cryptography/Authentication/Signatures/HashAndSign/CollisionHandler.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Authentication.Signatures.Defs
import TCSlib.Cryptography.Hashing.CollisionResistant
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.FixedGame
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CodecReaders

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The collision-finding handler for hash-and-sign

The non-interactive reduction in [PS10, Theorem 144.1] receives the hash index, samples
signature keys, and answers the sole signing query itself. Its state remembers that query;
the final output concatenates the query and the forged message for the CRH collision game.

## Main definitions

* `HashSignFill.collisionKey`, `collisionAdv`, `collisionHash`, `collisionRun`,
  `collisionOut`: the string computations of the reduction.
* `HashSignFill.collisionHandler`: their polynomial-time T1 handler.

## Main results

* The string equations and handler field equations expose every computation.
* `HashSignFill.exists_collisionMachine`: T1 realizes this handler as a machine.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Theorem 144.1, collision-finding case.
-/

namespace TCSlib.Cryptography.Authentication.HashSignFill

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-- The signature key word generated from the first `S.gen.coins(n)` bits of the
context seed, with empty argument and advice,
`collisionKey S c = S.gen.output (NUPPT.layout u [] [] (ω.take (S.gen.coins.eval u.length)))`,
where `u = pairFstD c` and `ω = pairSndD (pairSndD c)` [PS10, Theorem 144.1]. -/
def collisionKey (S : SignatureScheme) (c : List Bool) : List Bool :=
  S.gen.output (NUPPT.layout (pairFstD c) [] []
    ((pairSndD (pairSndD c)).take (S.gen.coins.eval (pairFstD c).length)))

/-- `collisionKey S c` runs the original key generator on the parameter and the first
generator-sized segment of the context seed:
`collisionKey S c = S.gen.output (NUPPT.layout u [] [] (ω.take (S.gen.coins.eval u.length)))`,
where `u = pairFstD c` and `ω = pairSndD (pairSndD c)`. -/
theorem collisionKey_eq (S : SignatureScheme) (c : List Bool) :
    collisionKey S c = S.gen.output (NUPPT.layout (pairFstD c) [] []
      ((pairSndD (pairSndD c)).take (S.gen.coins.eval (pairFstD c).length))) := rfl

/-- Generating the signature key from a context is polynomial-time:
`PolyTimeComputable (collisionKey S)`, for `collisionKey S : List Bool → List Bool`.
The tape segment is
computed by the published polynomial-length take construction. -/
theorem polyTimeComputable_collisionKey (S : SignatureScheme) :
    PolyTimeComputable (collisionKey S) :=
  let hW := polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD
  let hT := ((polyTimeComputable_pairTakePoly S.gen.coins).comp'
    (polyTimeComputable_pairFstD.pairEncode hW)).congr (fun _ =>
      congrArg₂ (fun u w : List Bool => w.take (S.gen.coins.eval u.length))
        (pairFstD_pairEncode _ _) (pairSndD_pairEncode _ _))
  S.gen.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout
    polyTimeComputable_pairFstD (polyTimeComputable_const [])
    (polyTimeComputable_const []) hT)

/-- When the context seed concatenates generator and signing tapes, `collisionKey` is
exactly the original generator's run on its own tape:
`collisionKey S (seedIn n i (List.ofFn rg ++ List.ofFn rs)) = S.gen.runAt n [] rg`. -/
theorem collisionKey_seed (S : SignatureScheme) (n : ℕ) (i : List Bool)
    (rg : S.gen.Coins n) (rs : S.sign.Coins n) :
    collisionKey S (seedIn n i (List.ofFn rg ++ List.ofFn rs)) = S.gen.runAt n [] rg := by
  simp only [collisionKey_eq, seedIn_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate]
  rw [← NUPPT.coinLen_eq S.gen n, List.take_left' List.length_ofFn,
    S.gen_uniform.runAt_eq, NUPPT.layout_eq, NUPPT.advInput_eq]

/-- The adversary receives `⟨pk, i⟩`, where the context supplies the hash index and
`collisionKey` supplies the public signature key,
`collisionAdv S c = pairEncode (pairFstD (collisionKey S c)) (pairFstD (pairSndD c))`
[PS10, Theorem 144.1]. -/
def collisionAdv (S : SignatureScheme) (c : List Bool) : List Bool :=
  pairEncode (pairFstD (collisionKey S c)) (pairFstD (pairSndD c))

/-- The adversary input is the original public key paired with the context index:
`collisionAdv S c = pairEncode (pairFstD (collisionKey S c)) (pairFstD (pairSndD c))`. -/
theorem collisionAdv_eq (S : SignatureScheme) (c : List Bool) :
    collisionAdv S c =
      pairEncode (pairFstD (collisionKey S c)) (pairFstD (pairSndD c)) := rfl

/-- Pairing the generated public key with the index is polynomial-time:
`PolyTimeComputable (collisionAdv S)`, for `collisionAdv S : List Bool → List Bool`. -/
theorem polyTimeComputable_collisionAdv (S : SignatureScheme) :
    PolyTimeComputable (collisionAdv S) :=
  (polyTimeComputable_pairFstD.comp' (polyTimeComputable_collisionKey S)).pairEncode
    (polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD)

/-- At `seedIn n i ω`, the adversary input is `⟨pk, i⟩`, where the original generator
runs with the first `S.gen.coins(n)` seed bits: `collisionAdv S (seedIn n i ω) =
pairEncode (pairFstD (S.gen.output (NUPPT.layout (List.replicate n true) [] []
(ω.take (S.gen.coins.eval n))))) i`. -/
theorem collisionAdv_seedIn (S : SignatureScheme) (n : ℕ) (i ω : List Bool) :
    collisionAdv S (seedIn n i ω) =
      pairEncode (pairFstD (S.gen.output (NUPPT.layout (List.replicate n true) [] []
        (ω.take (S.gen.coins.eval n))))) i := by
  simp only [collisionAdv_eq, collisionKey_eq, seedIn_eq, pairFstD_pairEncode,
    pairSndD_pairEncode, List.length_replicate]

/-- On concatenated generator and signing tapes, the adversary receives the public key
from that generator run paired with the supplied hash index:
`collisionAdv S (seedIn n i (List.ofFn rg ++ List.ofFn rs)) =
pairEncode (pairFstD (S.gen.runAt n [] rg)) i`. -/
theorem collisionAdv_seed (S : SignatureScheme) (n : ℕ) (i : List Bool)
    (rg : S.gen.Coins n) (rs : S.sign.Coins n) :
    collisionAdv S (seedIn n i (List.ofFn rg ++ List.ofFn rs)) =
      pairEncode (pairFstD (S.gen.runAt n [] rg)) i := by
  rw [collisionAdv_eq, collisionKey_seed, seedIn_eq,
    pairSndD_pairEncode, pairFstD_pairEncode]

/-- The query hash in a handler-round word is the CRH evaluator padded to the signature
message length: `collisionHash H S w = padStr S.msgLen u (H.eval (pairEncode u (pairEncode i x)))`,
where `u = pairFstD (pairFstD w)`, `i = pairFstD (pairSndD (pairFstD w))` and
`x = pairSndD (pairSndD (pairSndD w))`.
The theorem's length hypothesis later identifies this with `H.hash`
[PS10, Theorem 144.1]. -/
def collisionHash (H : CRH) (S : SignatureScheme) (w : List Bool) : List Bool :=
  padStr S.msgLen (pairFstD (pairFstD w))
    (H.eval (pairEncode (pairFstD (pairFstD w))
      (pairEncode (pairFstD (pairSndD (pairFstD w)))
        (pairSndD (pairSndD (pairSndD w))))))

/-- The query hash runs the evaluator at the context parameter and index on the query
word and pads its output to the signature message length:
`collisionHash H S w = padStr S.msgLen u (H.eval (pairEncode u (pairEncode i x)))`, where
`u = pairFstD (pairFstD w)`, `i = pairFstD (pairSndD (pairFstD w))` and
`x = pairSndD (pairSndD (pairSndD w))`. -/
theorem collisionHash_eq (H : CRH) (S : SignatureScheme) (w : List Bool) :
    collisionHash H S w = padStr S.msgLen (pairFstD (pairFstD w))
      (H.eval (pairEncode (pairFstD (pairFstD w))
        (pairEncode (pairFstD (pairSndD (pairFstD w)))
          (pairSndD (pairSndD (pairSndD w)))))) := rfl

/-- Evaluating and padding the query hash is polynomial-time by the CRH evaluator and
the published padding construction: `PolyTimeComputable (collisionHash H S)`, for
`collisionHash H S : List Bool → List Bool`. -/
theorem polyTimeComputable_collisionHash (H : CRH) (S : SignatureScheme) :
    PolyTimeComputable (collisionHash H S) :=
  let hU := polyTimeComputable_pairFstD.comp' polyTimeComputable_pairFstD
  let hI := polyTimeComputable_pairFstD.comp'
    (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairFstD)
  let hX := polyTimeComputable_pairSndD.comp'
    (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD)
  (HashSignForward.polyTimeComputable_hashWord H S hU hI hX).congr (fun w =>
    (HashSignForward.hashWord_eq H S _ _ _).trans (collisionHash_eq H S w).symm)

/-- A collision-finder round signs the query hash using the remaining seed and records
the query as its new state, `collisionRun H S w = pairEncode (padStr S.sigLen u
(S.sign.output (NUPPT.layout u (pairEncode (pairSndD (collisionKey S (pairFstD w)))
(collisionHash H S w)) [] (ω.drop (S.gen.coins.eval u.length))))) x`, where
`u = pairFstD (pairFstD w)`, `ω = pairSndD (pairSndD (pairFstD w))` and
`x = pairSndD (pairSndD (pairSndD w))` [PS10, Theorem 144.1]. -/
def collisionRun (H : CRH) (S : SignatureScheme) (w : List Bool) : List Bool :=
  pairEncode
    (padStr S.sigLen (pairFstD (pairFstD w))
      (S.sign.output (NUPPT.layout (pairFstD (pairFstD w))
        (pairEncode (pairSndD (collisionKey S (pairFstD w))) (collisionHash H S w)) []
        ((pairSndD (pairSndD (pairFstD w))).drop
          (S.gen.coins.eval (pairFstD (pairFstD w)).length)))))
    (pairSndD (pairSndD (pairSndD w)))

/-- A round returns the padded original signature and the queried message:
`collisionRun H S w = pairEncode (padStr S.sigLen u (S.sign.output (NUPPT.layout u
(pairEncode (pairSndD (collisionKey S (pairFstD w))) (collisionHash H S w)) []
(ω.drop (S.gen.coins.eval u.length))))) x`, where `u = pairFstD (pairFstD w)`,
`ω = pairSndD (pairSndD (pairFstD w))` and `x = pairSndD (pairSndD (pairSndD w))`. -/
theorem collisionRun_eq (H : CRH) (S : SignatureScheme) (w : List Bool) :
    collisionRun H S w = pairEncode
      (padStr S.sigLen (pairFstD (pairFstD w))
        (S.sign.output (NUPPT.layout (pairFstD (pairFstD w))
          (pairEncode (pairSndD (collisionKey S (pairFstD w))) (collisionHash H S w)) []
          ((pairSndD (pairSndD (pairFstD w))).drop
            (S.gen.coins.eval (pairFstD (pairFstD w)).length)))))
      (pairSndD (pairSndD (pairSndD w))) := rfl

/-- The collision-finder round is polynomial-time: `PolyTimeComputable (collisionRun H S)`,
for `collisionRun H S : List Bool → List Bool`. It uses a polynomial-length coin suffix,
the polynomial-time signer and padding, then pairs the result with the query.

**Proof sketch.** Write `u` for the parameter word, `ω` for the context seed and `x` for the
query word of a round input; each is a composition of pair projections, hence polynomial-time.
The signer's tape is `ω` with its first `S.gen.coins(|u|)` bits dropped, computed by the
published polynomial-length drop construction on the pair `⟨u, ω⟩`. The secret key is the
second component of the polynomial-time `collisionKey`, and the query hash is polynomial-time
(`polyTimeComputable_collisionHash`). The original signer's output on the layout of `u`, the
pair of key and hash, empty advice and that tape is then polynomial-time, and so is padding
it to `S.sigLen(|u|)` bits by the published padding construction on `⟨u, ·⟩`. Pairing the
padded signature with `x` gives the round. -/
theorem polyTimeComputable_collisionRun (H : CRH) (S : SignatureScheme) :
    PolyTimeComputable (collisionRun H S) :=
  let hU := polyTimeComputable_pairFstD.comp' polyTimeComputable_pairFstD
  let hW := polyTimeComputable_pairSndD.comp'
    (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairFstD)
  let hR := ((polyTimeComputable_pairDropPoly S.gen.coins).comp'
    (hU.pairEncode hW)).congr (fun _ =>
      congrArg₂ (fun u r : List Bool => r.drop (S.gen.coins.eval u.length))
        (pairFstD_pairEncode _ _) (pairSndD_pairEncode _ _))
  let hK := polyTimeComputable_pairSndD.comp'
    ((polyTimeComputable_collisionKey S).comp' polyTimeComputable_pairFstD)
  let hSig := S.sign.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout hU
    (hK.pairEncode (polyTimeComputable_collisionHash H S)) (polyTimeComputable_const []) hR)
  let hPad := ((polyTimeComputable_padStr S.sigLen).comp' (hU.pairEncode hSig)).congr
    (fun _ => congrArg₂ (padStr S.sigLen)
      (pairFstD_pairEncode _ _) (pairSndD_pairEncode _ _))
  hPad.pairEncode (polyTimeComputable_pairSndD.comp'
    (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD))

/-- The collision output concatenates the remembered query with the first `H.domLen(n)`
bits of the adversary's final word, `collisionOut H w = pairFstD (pairSndD w) ++
(pairSndD (pairSndD w)).take (H.domLen.eval (pairFstD (pairFstD w)).length)`
[PS10, Theorem 144.1]. -/
def collisionOut (H : CRH) (w : List Bool) : List Bool :=
  pairFstD (pairSndD w) ++
    (pairSndD (pairSndD w)).take (H.domLen.eval (pairFstD (pairFstD w)).length)

/-- The collision output is the state followed by the message prefix of the forgery:
`collisionOut H w = pairFstD (pairSndD w) ++
(pairSndD (pairSndD w)).take (H.domLen.eval (pairFstD (pairFstD w)).length)`. -/
theorem collisionOut_eq (H : CRH) (w : List Bool) :
    collisionOut H w = pairFstD (pairSndD w) ++
      (pairSndD (pairSndD w)).take (H.domLen.eval (pairFstD (pairFstD w)).length) := rfl

/-- Reading a polynomial-length forgery prefix and appending it to the stored query is
polynomial-time: `PolyTimeComputable (collisionOut H)`, for
`collisionOut H : List Bool → List Bool`. -/
theorem polyTimeComputable_collisionOut (H : CRH) :
    PolyTimeComputable (collisionOut H) :=
  let hU := polyTimeComputable_pairFstD.comp' polyTimeComputable_pairFstD
  let hA := polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD
  let hT := ((polyTimeComputable_pairTakePoly H.domLen).comp' (hU.pairEncode hA)).congr
    (fun _ => congrArg₂ (fun u a : List Bool => a.take (H.domLen.eval u.length))
      (pairFstD_pairEncode _ _) (pairSndD_pairEncode _ _))
  (polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD).append hT

/-- The T1 collision finder samples signature-generation and signing coins, remembers one
domain-width query, and emits the query followed by the forged message: its fields are
`stateLen = H.domLen`, `seedLen = .add S.gen.coins S.sign.coins`, `init _ = zeroBits _`,
`run = collisionRun H S`, `advIn = collisionAdv S` and `out = collisionOut H`
[PS10, Theorem 144.1]. -/
def collisionHandler (H : CRH) (S : SignatureScheme) :
    PolyHandler 1 (fun _ => H.domLen) (fun _ => S.sigLen) where
  stateLen := H.domLen
  seedLen := .add S.gen.coins S.sign.coins
  init _ := zeroBits _
  run := collisionRun H S
  poly := polyTimeComputable_collisionRun H S
  advIn := collisionAdv S
  advIn_poly := polyTimeComputable_collisionAdv S
  out := collisionOut H
  out_poly := polyTimeComputable_collisionOut H

attribute [simps (config := { isSimp := false }) stateLen seedLen init run advIn out]
  collisionHandler

/-- On a well-formed round input, the collision handler returns the padded signature on
the query hash and stores exactly the query:
`(collisionHandler H S).run (PolyHandler.input n i ω s j m) = pairEncode (padStr S.sigLen u σ) m`,
where `u = List.replicate n true` and
`σ = S.sign.output (NUPPT.layout u (pairEncode (pairSndD (collisionKey S (seedIn n i ω)))
(padStr S.msgLen u (H.eval (pairEncode u (pairEncode i m))))) [] (ω.drop (S.gen.coins.eval n)))`.
The generator reads the seed prefix and
the signer reads its suffix; the old state and oracle index are ignored. -/
theorem collisionHandler_run_input (H : CRH) (S : SignatureScheme) (n : ℕ)
    (i ω s : List Bool) (j : Fin 1) (m : List Bool) :
    (collisionHandler H S).run (PolyHandler.input n i ω s j m) =
      pairEncode
        (padStr S.sigLen (List.replicate n true)
          (S.sign.output (NUPPT.layout (List.replicate n true)
            (pairEncode
              (pairSndD (collisionKey S (seedIn n i ω)))
              (padStr S.msgLen (List.replicate n true)
                (H.eval (pairEncode (List.replicate n true) (pairEncode i m))))) []
            (ω.drop (S.gen.coins.eval n))))) m := by
  simp only [collisionHandler_run, collisionRun_eq, collisionHash_eq, PolyHandler.input_eq,
    seedIn_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- The typed signature returned by the collision handler: run the original signer on the
hashed message with the seed suffix and pad its output to `S.sigLen(n)` bits,
`collisionReply H S n i ω m = padFin (S.sigLen.eval n) σ`, where `u = List.replicate n true` and
`σ = S.sign.output (NUPPT.layout u (pairEncode (pairSndD (collisionKey S (seedIn n i ω)))
(padStr S.msgLen u (H.eval (pairEncode u (pairEncode i m))))) [] (ω.drop (S.gen.coins.eval n)))`. -/
def collisionReply (H : CRH) (S : SignatureScheme) (n : ℕ) (i ω m : List Bool) :
    Fin (S.sigLen.eval n) → Bool :=
  padFin (S.sigLen.eval n)
    (S.sign.output (NUPPT.layout (List.replicate n true)
      (pairEncode (pairSndD (collisionKey S (seedIn n i ω)))
        (padStr S.msgLen (List.replicate n true)
          (H.eval (pairEncode (List.replicate n true) (pairEncode i m))))) []
      (ω.drop (S.gen.coins.eval n))))

/-- The typed reply is the original signer output padded to the signature length:
`collisionReply H S n i ω m = padFin (S.sigLen.eval n) σ`, where `u = List.replicate n true` and
`σ = S.sign.output (NUPPT.layout u (pairEncode (pairSndD (collisionKey S (seedIn n i ω)))
(padStr S.msgLen u (H.eval (pairEncode u (pairEncode i m))))) [] (ω.drop (S.gen.coins.eval n)))`. -/
theorem collisionReply_eq (H : CRH) (S : SignatureScheme) (n : ℕ) (i ω m : List Bool) :
    collisionReply H S n i ω m = padFin (S.sigLen.eval n)
      (S.sign.output (NUPPT.layout (List.replicate n true)
        (pairEncode (pairSndD (collisionKey S (seedIn n i ω)))
          (padStr S.msgLen (List.replicate n true)
            (H.eval (pairEncode (List.replicate n true) (pairEncode i m))))) []
        (ω.drop (S.gen.coins.eval n)))) := rfl

/-- With the generator and signing tapes concatenated into the context seed, the collision
handler's reply is the fixed experiment's hashed reply under those same generated keys:
`collisionReply H S n i (List.ofFn rg ++ List.ofFn rs) (List.ofFn m) =
hashedReply H S n (pairSndD (S.gen.runAt n [] rg)) i rs m`. -/
theorem collisionReply_seed (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
    (rg : S.gen.Coins n) (rs : S.sign.Coins n) (m : Fin (H.domLen.eval n) → Bool) :
    collisionReply H S n i (List.ofFn rg ++ List.ofFn rs) (List.ofFn m) =
      hashedReply H S n (pairSndD (S.gen.runAt n [] rg)) i rs m := by
  rw [collisionReply_eq, collisionKey_seed, hashedReply_eq,
    ← NUPPT.coinLen_eq S.gen n, List.drop_left' List.length_ofFn,
    S.sign_uniform.runAt_eq, HashSignForward.hashWord_eq,
    NUPPT.layout_eq, NUPPT.advInput_eq]

/-- Encoding the typed reply gives exactly the padded signature word emitted by a
collision-handler round: `List.ofFn (collisionReply H S n i ω m) = padStr S.sigLen u σ`, where
`u = List.replicate n true` and
`σ = S.sign.output (NUPPT.layout u (pairEncode (pairSndD (collisionKey S (seedIn n i ω)))
(padStr S.msgLen u (H.eval (pairEncode u (pairEncode i m))))) [] (ω.drop (S.gen.coins.eval n)))`. -/
theorem ofFn_collisionReply (H : CRH) (S : SignatureScheme) (n : ℕ) (i ω m : List Bool) :
    List.ofFn (collisionReply H S n i ω m) =
      padStr S.sigLen (List.replicate n true)
        (S.sign.output (NUPPT.layout (List.replicate n true)
          (pairEncode (pairSndD (collisionKey S (seedIn n i ω)))
            (padStr S.msgLen (List.replicate n true)
              (H.eval (pairEncode (List.replicate n true) (pairEncode i m))))) []
          (ω.drop (S.gen.coins.eval n)))) := by
  simp only [collisionReply_eq, ofFn_padFin_eq_take, padStr_eq, List.length_replicate]

/-- The collision handler answers each typed query with its padded original signature and
sets the state to that query, asking no further oracle: `(collisionHandler H S).impl n i ω j m s =
.pure (collisionReply H S n i (List.ofFn ω) (List.ofFn m), m)`. -/
theorem collisionHandler_impl (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
    (ω : Fin ((collisionHandler H S).seedLen.eval n) → Bool) (j : Fin 1)
    (m s : Fin (H.domLen.eval n) → Bool) :
    (collisionHandler H S).impl n i ω j m s =
      .pure (collisionReply H S n i (List.ofFn ω) (List.ofFn m), m) := by
  rw [PolyHandler.impl_apply]
  congr 1
  apply PolyHandler.answer_of_run_eq
  rw [collisionHandler_run_input, ofFn_collisionReply]

/-- Finalization returns the remembered query followed by the domain-width message prefix
of the adversary's output: `(collisionHandler H S).result n i ω s a =
List.ofFn s ++ (List.ofFn a).take (H.domLen.eval n)`. -/
theorem collisionHandler_result (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
    (ω : Fin ((collisionHandler H S).seedLen.eval n) → Bool)
    (s : Fin (H.domLen.eval n) → Bool) {d : ℕ} (a : Fin d → Bool) :
    (collisionHandler H S).result n i ω s a =
      List.ofFn s ++ (List.ofFn a).take (H.domLen.eval n) := by
  simp only [PolyHandler.result_eq, collisionHandler_out, collisionOut_eq, seedIn_eq,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- The collision handler and common fixed-tape transcript return the same adversary
output: if `List.ofFn ω = List.ofFn rg ++ List.ofFn rs`, then `∃ a s L,
simulate ((collisionHandler H S).impl n i ω) (A.toCompOn cod n 1
((collisionHandler H S).advInput n i ω) rA) ((collisionHandler H S).init n) = .pure (a, s) ∧
transcript H S A n pk sk i rs rA = .pure (a, ((), L)) ∧
(L = [] ∨ ∃ j m, L = [⟨j, m, hashedReply H S n sk i rs m⟩] ∧ s = m)`, where
`pk = pairFstD (S.gen.runAt n [] rg)`, `sk = pairSndD (S.gen.runAt n [] rg)` and
`cod = bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
(H.domLen.eval n + S.sigLen.eval n)`.
Their query log is empty, or consists of one query which is exactly the handler's
final state, answered by the same original signing tape.

**Proof sketch.** The adversary's computation has at most one query. If it returns
immediately, both simulations return that value and the transcript log is empty. Otherwise,
the seed equations identify the handler's response with the fixed experiment's response;
the handler stores the query while the fixed experiment logs it. Both continuations
therefore return the same function of that response. -/
theorem collisionHandler_transcript (H : CRH) (S : SignatureScheme) (A : NUPPT) (n : ℕ)
    (i : List Bool) (rg : S.gen.Coins n) (rs : S.sign.Coins n) (rA : A.Coins n)
    (ω : Fin ((collisionHandler H S).seedLen.eval n) → Bool)
    (hω : List.ofFn ω = List.ofFn rg ++ List.ofFn rs) :
    ∃ (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool)
      (s : Fin (H.domLen.eval n) → Bool)
      (L : QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
        (fun _ => S.sigLen.eval n))),
      simulate ((collisionHandler H S).impl n i ω)
          (A.toCompOn (bitCodec (fun _ : Fin 1 => H.domLen.eval n)
            (fun _ => S.sigLen.eval n) (H.domLen.eval n + S.sigLen.eval n)) n 1
            ((collisionHandler H S).advInput n i ω) rA) ((collisionHandler H S).init n) =
          .pure (a, s) ∧
        transcript H S A n (pairFstD (S.gen.runAt n [] rg))
          (pairSndD (S.gen.runAt n [] rg)) i rs rA = .pure (a, ((), L)) ∧
        (L = [] ∨ ∃ (j : Fin 1) (m : Fin (H.domLen.eval n) → Bool),
          L = [⟨j, m, hashedReply H S n (pairSndD (S.gen.runAt n [] rg)) i rs m⟩] ∧ s = m) := by
  have hinput : (collisionHandler H S).advInput n i ω =
      pairEncode (pairFstD (S.gen.runAt n [] rg)) i := by
    rw [PolyHandler.advInput_eq, collisionHandler_advIn, hω, collisionAdv_seed]
  let c := A.toCompOn (bitCodec (fun _ : Fin 1 => H.domLen.eval n)
    (fun _ => S.sigLen.eval n) (H.domLen.eval n + S.sigLen.eval n)) n 1
    (pairEncode (pairFstD (S.gen.runAt n [] rg)) i) rA
  have hc : c.CostBoundedBy (fun _ => 1) 1 := A.toCompOn_costBoundedBy _ n 1 _ rA
  rcases one_query_cases c hc with ⟨a, hcase⟩ | ⟨j, m, f, hcase⟩
  all_goals dsimp only [c] at hcase
  · refine ⟨a, (collisionHandler H S).init n, [], ?_, ?_, Or.inl rfl⟩
    · rw [hinput, hcase, simulate_pure]
    · rw [transcript_eq, hcase, simulate_pure]
  · let y := hashedReply H S n (pairSndD (S.gen.runAt n [] rg)) i rs m
    refine ⟨f y, m, [⟨j, m, y⟩], ?_, ?_, Or.inr ⟨j, m, rfl, rfl⟩⟩
    · rw [hinput, hcase, simulate_query, collisionHandler_impl, hω, collisionReply_seed,
        OracleComp.pure_bind, simulate_pure]
    · rw [transcript_eq, hcase]
      simp only [simulate_query, QueryImpl.withLog_apply, fixedSign_apply,
        OracleComp.pure_bind, simulate_pure, List.nil_append]
      rfl

/-- If the common transcript is fresh and contains a query with the forged message's
hash, the collision handler's final output satisfies the CRH game's exact collision
predicate on the full domain: given `∀ n i x, H.inDom n i x = true`,
`L = [] ∨ ∃ j m, L = [⟨j, m, hashedReply H S n sk i rs m⟩] ∧ s = m`,
`∀ e ∈ L, e.2.1 ≠ (splitBits a).1` and `∃ e ∈ L, H.hash n i e.2.1 = H.hash n i (splitBits a).1`,
then `H.inDom n i x₁ = true ∧ H.inDom n i x₂ = true ∧ x₁ ≠ x₂ ∧ H.hash n i x₁ = H.hash n i x₂`,
where `(x₁, x₂) = splitBits (padFin (H.domLen.eval n + H.domLen.eval n)
((collisionHandler H S).result n i ω s a))` [PS10, Theorem 144.1, collision case].

**Proof sketch.** The equal-hash witness rules out an empty log. The one-query invariant
then identifies its query with the final handler state. Freshness makes that query distinct
from the forged message. The finalization reader and fixed-width concatenation reader show
that the CRH game decodes precisely these two messages. Full domain membership supplies
the remaining two clauses of the collision predicate. -/
theorem collisionHandler_collision (H : CRH) (S : SignatureScheme)
    (hdom : ∀ n i x, H.inDom n i x = true) (n : ℕ) (sk i : List Bool)
    (rs : S.sign.Coins n) (ω : Fin ((collisionHandler H S).seedLen.eval n) → Bool)
    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) (s : Fin (H.domLen.eval n) → Bool)
    (L : QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)))
    (hinv : L = [] ∨ ∃ (j : Fin 1) (m : Fin (H.domLen.eval n) → Bool),
      L = [⟨j, m, hashedReply H S n sk i rs m⟩] ∧ s = m)
    (hfresh : ∀ e ∈ L, e.2.1 ≠ (splitBits a).1)
    (hsame : ∃ e ∈ L, H.hash n i e.2.1 = H.hash n i (splitBits a).1) :
    let xx := splitBits (padFin (H.domLen.eval n + H.domLen.eval n)
      ((collisionHandler H S).result n i ω s a))
    H.inDom n i xx.1 = true ∧ H.inDom n i xx.2 = true ∧ xx.1 ≠ xx.2 ∧
      H.hash n i xx.1 = H.hash n i xx.2 := by
  rcases hinv with hnil | ⟨j, m, hL, hs⟩
  · obtain ⟨e, he, _⟩ := hsame
    rw [hnil] at he
    exact False.elim (List.not_mem_nil he)
  · subst L
    subst s
    obtain ⟨e, he, hhash⟩ := hsame
    have heq := List.mem_singleton.mp he
    subst e
    have hne : m ≠ (splitBits a).1 := hfresh _ (List.mem_singleton_self _)
    have hp : (List.ofFn a).take (H.domLen.eval n) = List.ofFn (splitBits a).1 :=
      (EffFill.ofFn_take_drop_add a).1.trans
        (congrArg List.ofFn (funext fun j => splitBits_fst a j)).symm
    have hdecode : splitBits (padFin (H.domLen.eval n + H.domLen.eval n)
        ((collisionHandler H S).result n i ω m a)) = (m, (splitBits a).1) := by
      rw [collisionHandler_result, hp, splitBits_pad_concat]
    dsimp only
    rw [hdecode]
    exact ⟨hdom n i m, hdom n i _, hne, hhash⟩

/-- T1 realizes the collision handler as a machine: on matching seed/adversary coins,
its output equals `collisionHandler.result` after the deterministic simulation,
`∃ B : NUPPT, ∀ n, ∃ φ : (Fin (K.seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n, ∀ i ω r,
∃ a s, simulate (K.impl n i ω) (A.toCompOn cod n ((.const 1 : PolyExpr).eval n)
(K.advInput n i ω) r) (K.init n) = .pure (a, s) ∧ B.runAt n i (φ (ω, r)) = K.result n i ω s a`,
where `K = collisionHandler H S` and `cod = bitCodec (fun _ : Fin 1 => H.domLen.eval n)
(fun _ : Fin 1 => S.sigLen.eval n) ((PolyExpr.add H.domLen S.sigLen).eval n)`. This is
the machine-construction part of [PS10, Theorem 144.1], before relating the collision event. -/
theorem exists_collisionMachine (H : CRH) (S : SignatureScheme) (A : NUPPT) :
    ∃ B : NUPPT, ∀ n : ℕ, ∃ φ :
      (Fin ((collisionHandler H S).seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n,
      ∀ (i : List Bool) (ω : Fin ((collisionHandler H S).seedLen.eval n) → Bool)
        (r : A.Coins n),
        ∃ (a : Fin ((PolyExpr.add H.domLen S.sigLen).eval n) → Bool)
          (s : Fin ((collisionHandler H S).stateLen.eval n) → Bool),
          simulate ((collisionHandler H S).impl n i ω)
              (A.toCompOn (bitCodec (fun _ : Fin 1 => H.domLen.eval n)
                (fun _ : Fin 1 => S.sigLen.eval n) ((PolyExpr.add H.domLen S.sigLen).eval n))
                n ((.const 1 : PolyExpr).eval n) ((collisionHandler H S).advInput n i ω) r)
              ((collisionHandler H S).init n) = .pure (a, s) ∧
            B.runAt n i (φ (ω, r)) = (collisionHandler H S).result n i ω s a :=
  exists_handlerMachine A (.const 1) (fun _ => H.domLen) (fun _ => S.sigLen)
    (.add H.domLen S.sigLen) (collisionHandler H S)

/-- T1 supplies a collision machine whose output is the finalization of the common
fixed-tape transcript: `∃ B : NUPPT, ∀ n, ∃ φ : (Fin (K.seedLen.eval n) → Bool) × A.Coins n ≃
B.Coins n, ∀ i rg rs ω rA, List.ofFn ω = List.ofFn rg ++ List.ofFn rs → ∃ a s L,
transcript H S A n pk sk i rs rA = .pure (a, ((), L)) ∧
(L = [] ∨ ∃ j m, L = [⟨j, m, hashedReply H S n sk i rs m⟩] ∧ s = m) ∧
B.runAt n i (φ (ω, rA)) = K.result n i ω s a`, where `K = collisionHandler H S`,
`pk = pairFstD (S.gen.runAt n [] rg)` and `sk = pairSndD (S.gen.runAt n [] rg)`.
Its coins correspond bijectively to the handler seed and adversary
tape; concatenated generator/signing tapes give the same adversary output and one-query
invariant as `collisionHandler_transcript` [PS10, Theorem 144.1].

**Proof sketch.** Apply the T1 machine contract and the common-transcript coupling to the
same seed and adversary tape. Both describe the same deterministic handler simulation as
a pure computation. Injectivity of the pure constructor identifies their final outputs
and states, so the T1 run equation becomes the claimed common-transcript run equation. -/
theorem exists_collisionMachine_transcript (H : CRH) (S : SignatureScheme) (A : NUPPT) :
    ∃ B : NUPPT, ∀ n : ℕ, ∃ φ :
      (Fin ((collisionHandler H S).seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n,
      ∀ (i : List Bool) (rg : S.gen.Coins n) (rs : S.sign.Coins n)
        (ω : Fin ((collisionHandler H S).seedLen.eval n) → Bool) (rA : A.Coins n),
        List.ofFn ω = List.ofFn rg ++ List.ofFn rs →
        ∃ (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool)
          (s : Fin (H.domLen.eval n) → Bool)
          (L : QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
            (fun _ => S.sigLen.eval n))),
          transcript H S A n (pairFstD (S.gen.runAt n [] rg))
            (pairSndD (S.gen.runAt n [] rg)) i rs rA = .pure (a, ((), L)) ∧
          (L = [] ∨ ∃ (j : Fin 1) (m : Fin (H.domLen.eval n) → Bool),
            L = [⟨j, m, hashedReply H S n (pairSndD (S.gen.runAt n [] rg)) i rs m⟩] ∧ s = m) ∧
          B.runAt n i (φ (ω, rA)) = (collisionHandler H S).result n i ω s a := by
  obtain ⟨B, hB⟩ := exists_collisionMachine H S A
  refine ⟨B, fun n => ?_⟩
  obtain ⟨φ, hφ⟩ := hB n
  refine ⟨φ, fun i rg rs ω rA hω => ?_⟩
  simp only [PolyExpr.eval_add, PolyExpr.eval_const] at hφ
  obtain ⟨a₀, s₀, hsim, hrun⟩ := hφ i ω rA
  obtain ⟨a, s, L, hsame, ht, hinv⟩ :=
    collisionHandler_transcript H S A n i rg rs rA ω hω
  have heq : (a₀, s₀) = (a, s) := OracleComp.pure.inj (hsim.symm.trans hsame)
  obtain ⟨ha, hs⟩ := Prod.mk.inj heq
  refine ⟨a, s, L, ht, hinv, ?_⟩
  simpa only [ha, hs] using hrun

end TCSlib.Cryptography.Authentication.HashSignFill

## ===== TCSlib/Cryptography/Authentication/Signatures/HashAndSign/FixedGame.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.ForwardHandler
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.OneQuerySampling

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A common transcript for the hash-and-sign reductions

Fix the signature keys, hash index, adversary tape and signing tape. The resulting
transcript is shared by the collision-finding and signature-forging reductions of
[PS10, Theorem 144.1]. Because the adversary makes at most one query, sampling signing
coins per query has the same law as drawing the signing tape before this transcript.

## Main definitions

* `HashSignFill.hashedReply`: the original signer applied to the hashed message.
* `HashSignFill.fixedSign`, `sampledHashSign`: the fixed-tape and fresh-tape signing oracles.
* `HashSignFill.transcript`: the adversary's output and full signing-query log.
* `HashSignFill.Success`: acceptance and message freshness in a common transcript.

## Main results

* The defining equations and application readers expose each computation.
* `HashSignFill.expect_sampledHashSign_eq_transcript`: signing randomness may be sampled
  before the common transcript.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 144.1, book pp. 144–145.
-/

namespace TCSlib.Cryptography.Authentication.HashSignFill

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-- With signing tape `rs` fixed, hash `m` and run the original signer under `sk`, padding
the signature to the declared signature width, `hashedReply H S n sk i rs m =
padFin (S.sigLen.eval n) (S.sign.runAt n (pairEncode sk (hashWord H S u i (List.ofFn m))) rs)`,
where `u = List.replicate n true` and `hashWord = HashSignForward.hashWord`
[PS10, Theorem 144.1]. -/
def hashedReply (H : CRH) (S : SignatureScheme) (n : ℕ) (sk i : List Bool)
    (rs : S.sign.Coins n) (m : Fin (H.domLen.eval n) → Bool) :
    Fin (S.sigLen.eval n) → Bool :=
  padFin (S.sigLen.eval n) (S.sign.runAt n
    (pairEncode sk (HashSignForward.hashWord H S (List.replicate n true) i (List.ofFn m))) rs)

/-- The fixed-tape hashed reply is the padded original signer output on `⟨sk, h_i(m)⟩`:
`hashedReply H S n sk i rs m =
padFin (S.sigLen.eval n) (S.sign.runAt n (pairEncode sk (hashWord H S u i (List.ofFn m))) rs)`,
where `u = List.replicate n true` and `hashWord = HashSignForward.hashWord`. -/
theorem hashedReply_eq (H : CRH) (S : SignatureScheme) (n : ℕ) (sk i : List Bool)
    (rs : S.sign.Coins n) (m : Fin (H.domLen.eval n) → Bool) :
    hashedReply H S n sk i rs m =
      padFin (S.sigLen.eval n) (S.sign.runAt n
        (pairEncode sk (HashSignForward.hashWord H S (List.replicate n true) i (List.ofFn m)))
        rs) := rfl

/-- The fixed-tape signing oracle answers every query using `hashedReply` and has trivial
state, `fixedSign H S n sk i rs j m s = .pure (hashedReply H S n sk i rs m, ())`
[PS10, Theorem 144.1]. -/
def fixedSign (H : CRH) (S : SignatureScheme) (n : ℕ) (sk i : List Bool)
    (rs : S.sign.Coins n) :
    QueryImpl (bitSpec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n))
      Unit unifSpec :=
  fun _ m _ => .pure (hashedReply H S n sk i rs m, ())

/-- The fixed-tape oracle is the pure answer function `m ↦ (hashedReply m, ())`:
`fixedSign H S n sk i rs = fun _ m _ => .pure (hashedReply H S n sk i rs m, ())`. -/
theorem fixedSign_eq (H : CRH) (S : SignatureScheme) (n : ℕ) (sk i : List Bool)
    (rs : S.sign.Coins n) :
    fixedSign H S n sk i rs = fun _ m _ => .pure (hashedReply H S n sk i rs m, ()) := rfl

/-- Applying the fixed-tape oracle returns the hashed signature and trivial state:
`fixedSign H S n sk i rs j m s = .pure (hashedReply H S n sk i rs m, ())`. -/
theorem fixedSign_apply (H : CRH) (S : SignatureScheme) (n : ℕ) (sk i : List Bool)
    (rs : S.sign.Coins n) (j : Fin 1) (m : Fin (H.domLen.eval n) → Bool) (s : Unit) :
    fixedSign H S n sk i rs j m s = .pure (hashedReply H S n sk i rs m, ()) := rfl

/-- The common transcript runs `A` on `⟨pk,i⟩` with one query allowed, fixed signing tape,
and a full query log, `transcript H S A n pk sk i rs rA =
simulate (fixedSign H S n sk i rs).withLog (A.toCompOn cod n 1 (pairEncode pk i) rA) ((), [])`,
where `cod = bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
(H.domLen.eval n + S.sigLen.eval n)` [PS10, Theorem 144.1]. -/
def transcript (H : CRH) (S : SignatureScheme) (A : NUPPT) (n : ℕ)
    (pk sk i : List Bool) (rs : S.sign.Coins n) (rA : A.Coins n) :
    ProbComp ((Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
        (fun _ => S.sigLen.eval n)))) :=
  simulate (fixedSign H S n sk i rs).withLog
    (A.toCompOn (bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
      (H.domLen.eval n + S.sigLen.eval n)) n 1 (pairEncode pk i) rA) ((), [])

/-- The common transcript is the logged simulation with the fixed-tape signing oracle:
`transcript H S A n pk sk i rs rA =
simulate (fixedSign H S n sk i rs).withLog (A.toCompOn cod n 1 (pairEncode pk i) rA) ((), [])`,
where `cod = bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
(H.domLen.eval n + S.sigLen.eval n)`. -/
theorem transcript_eq (H : CRH) (S : SignatureScheme) (A : NUPPT) (n : ℕ)
    (pk sk i : List Bool) (rs : S.sign.Coins n) (rA : A.Coins n) :
    transcript H S A n pk sk i rs rA =
      simulate (fixedSign H S n sk i rs).withLog
        (A.toCompOn (bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
          (H.domLen.eval n + S.sigLen.eval n)) n 1 (pairEncode pk i) rA) ((), []) := rfl

/-- The fresh-tape hash-and-sign oracle samples an original signing tape independently
for every query and keeps trivial state, `sampledHashSign H S n sk i = QueryImpl.ofComp
fun _ m => (ProbComp.sample (S.sign.Coins n)).bind fun rs => .pure (hashedReply H S n sk i rs m)`
[PS10, Theorem 144.1]. -/
noncomputable def sampledHashSign (H : CRH) (S : SignatureScheme) (n : ℕ) (sk i : List Bool) :
    QueryImpl (bitSpec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n))
      Unit unifSpec :=
  QueryImpl.ofComp fun _ m => (ProbComp.sample (S.sign.Coins n)).bind fun rs =>
    .pure (hashedReply H S n sk i rs m)

/-- The fresh-tape oracle is `ofComp` of the original signing-tape sample followed by
the corresponding fixed-tape hashed reply: `sampledHashSign H S n sk i = QueryImpl.ofComp
(fun _ m => (ProbComp.sample (S.sign.Coins n)).bind fun rs =>
.pure (hashedReply H S n sk i rs m))`. -/
theorem sampledHashSign_eq (H : CRH) (S : SignatureScheme) (n : ℕ) (sk i : List Bool) :
    sampledHashSign H S n sk i =
      QueryImpl.ofComp (fun _ m => (ProbComp.sample (S.sign.Coins n)).bind fun rs =>
        .pure (hashedReply H S n sk i rs m)) := rfl

/-- Applying the fresh-tape oracle samples one signing tape, returns its hashed signature,
and preserves the trivial state: `sampledHashSign H S n sk i j m s =
(ProbComp.sample (S.sign.Coins n)).bind fun rs => .pure (hashedReply H S n sk i rs m, s)`. -/
theorem sampledHashSign_apply (H : CRH) (S : SignatureScheme) (n : ℕ) (sk i : List Bool)
    (j : Fin 1) (m : Fin (H.domLen.eval n) → Bool) (s : Unit) :
    sampledHashSign H S n sk i j m s =
      (ProbComp.sample (S.sign.Coins n)).bind fun rs =>
        .pure (hashedReply H S n sk i rs m, s) := by
  simp only [sampledHashSign_eq, QueryImpl.ofComp_apply,
    OracleComp.bind_assoc, OracleComp.pure_bind]

/-- The expected payoff of a fresh-tape hash-and-sign simulation equals the expectation
obtained by drawing one signing tape and running the common transcript, including its log:
`ProbComp.expect (simulate (sampledHashSign H S n sk i).withLog
(A.toCompOn cod n 1 (pairEncode pk i) rA) ((), [])) g = ProbComp.expect
(ProbComp.sample (S.sign.Coins n)) (fun rs =>
ProbComp.expect (transcript H S A n pk sk i rs rA) g)`,
where `cod = bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
(H.domLen.eval n + S.sigLen.eval n)`.

**Proof sketch.** The machine computation has unit query cost at most one by its published
budget contract. `expect_simulate_sample_once` therefore moves the signing-tape sample
outside the logged simulation; the fixed-tape implementation is exactly `fixedSign`. -/
theorem expect_sampledHashSign_eq_transcript (H : CRH) (S : SignatureScheme) (A : NUPPT)
    (n : ℕ) (pk sk i : List Bool) (rA : A.Coins n)
    (g : (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
        (fun _ => S.sigLen.eval n))) → ℝ) :
    ProbComp.expect
        (simulate (sampledHashSign H S n sk i).withLog
          (A.toCompOn (bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
            (H.domLen.eval n + S.sigLen.eval n)) n 1 (pairEncode pk i) rA) ((), [])) g =
      ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
        ProbComp.expect (transcript H S A n pk sk i rs rA) g) := by
  simpa only [sampledHashSign_eq, transcript_eq, fixedSign_eq] using
    expect_simulate_sample_once (fun (_ : Fin 1) m rs => hashedReply H S n sk i rs m)
      (A.toCompOn (bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
        (H.domLen.eval n + S.sigLen.eval n)) n 1 (pairEncode pk i) rA)
      (A.toCompOn_costBoundedBy _ n 1 (pairEncode pk i) rA) g

/-- The common transcript is a successful hash-and-sign forgery when the original verifier
accepts the hashed final message and that message did not occur in the inner query log,
`Success H S n pk i res ↔ S.Accepts n pk (padFin (S.msgLen.eval n)
(H.eval (atParam n (pairEncode i (List.ofFn m))))) σ ∧ ∀ e ∈ res.2.2, e.2.1 ≠ m`, where
`(m, σ) = splitBits res.1` [PS10, Theorem 144.1]. -/
def Success (H : CRH) (S : SignatureScheme) (n : ℕ) (pk i : List Bool)
    (res : (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
        (fun _ => S.sigLen.eval n)))) : Prop :=
  S.Accepts n pk (padFin (S.msgLen.eval n)
      (H.eval (atParam n (pairEncode i (List.ofFn (splitBits res.1).1)))))
    (splitBits res.1).2 ∧
    ∀ e ∈ res.2.2, e.2.1 ≠ (splitBits res.1).1

/-- Success is original-scheme acceptance on the hash, together with freshness of the
unhashed final message in the common query log: `Success H S n pk i res ↔
S.Accepts n pk (padFin (S.msgLen.eval n) (H.eval (atParam n (pairEncode i (List.ofFn m))))) σ ∧
∀ e ∈ res.2.2, e.2.1 ≠ m`, where `(m, σ) = splitBits res.1`. -/
theorem success_iff (H : CRH) (S : SignatureScheme) (n : ℕ) (pk i : List Bool)
    (res : (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
        (fun _ => S.sigLen.eval n)))) :
    Success H S n pk i res ↔
      S.Accepts n pk (padFin (S.msgLen.eval n)
        (H.eval (atParam n (pairEncode i (List.ofFn (splitBits res.1).1)))))
        (splitBits res.1).2 ∧
      ∀ e ∈ res.2.2, e.2.1 ≠ (splitBits res.1).1 := Iff.rfl

end TCSlib.Cryptography.Authentication.HashSignFill

## ===== TCSlib/Cryptography/Authentication/Signatures/HashAndSign/ForwardGame.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.FixedGame
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CodecReaders
import TCSlib.Cryptography.Games.Bridges.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The common transcript of the forwarding reduction

## Main definitions

* `HashSignFill.queryHash`: the typed hash at the original signature message width.
* `HashSignFill.origFixedSign`: the original signer with one fixed signing tape.
* `HashSignFill.forwardEntry`, `forwardOutput`: hashing the query log and final message.

## Main results

The forwarding handler and the common fixed-tape transcript have the same adversary
output, with the outer log obtained by hashing every query. Distinct queried hashes
therefore give freshness in the original signature game.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Theorem 144.1, book pp. 144–145.
-/

namespace TCSlib.Cryptography.Authentication.HashSignFill

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-- The hash of a domain-width message, padded to the original signature message width:
`queryHash H S n i m =
padFin (S.msgLen.eval n) (H.eval (atParam n (pairEncode i (List.ofFn m))))`. -/
def queryHash (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
    (m : Fin (H.domLen.eval n) → Bool) : Fin (S.msgLen.eval n) → Bool :=
  padFin (S.msgLen.eval n) (H.eval (atParam n (pairEncode i (List.ofFn m))))

/-- The typed hash reads the evaluator output at the original message width:
`queryHash H S n i m =
padFin (S.msgLen.eval n) (H.eval (atParam n (pairEncode i (List.ofFn m))))`. -/
theorem queryHash_eq (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
    (m : Fin (H.domLen.eval n) → Bool) :
    queryHash H S n i m =
      padFin (S.msgLen.eval n) (H.eval (atParam n (pairEncode i (List.ofFn m)))) := rfl

/-- The original signature oracle with a fixed signing tape and trivial state:
`origFixedSign S n sk rs j m s =
.pure (padFin (S.sigLen.eval n) (S.sign.runAt n (pairEncode sk (List.ofFn m)) rs), ())`. -/
def origFixedSign (S : SignatureScheme) (n : ℕ) (sk : List Bool)
    (rs : S.sign.Coins n) :
    QueryImpl (bitSpec (fun _ : Fin 1 => S.msgLen.eval n) (fun _ => S.sigLen.eval n))
      Unit unifSpec :=
  fun _ m _ => .pure (padFin (S.sigLen.eval n)
    (S.sign.runAt n (pairEncode sk (List.ofFn m)) rs), ())

/-- The fixed original signer returns its padded signature and trivial state:
`origFixedSign S n sk rs = fun _ m _ =>
.pure (padFin (S.sigLen.eval n) (S.sign.runAt n (pairEncode sk (List.ofFn m)) rs), ())`. -/
theorem origFixedSign_eq (S : SignatureScheme) (n : ℕ) (sk : List Bool)
    (rs : S.sign.Coins n) :
    origFixedSign S n sk rs = fun _ m _ =>
      .pure (padFin (S.sigLen.eval n) (S.sign.runAt n (pairEncode sk (List.ofFn m)) rs), ()) := rfl

/-- Applying the fixed original signer returns its padded signature:
`origFixedSign S n sk rs j m s =
.pure (padFin (S.sigLen.eval n) (S.sign.runAt n (pairEncode sk (List.ofFn m)) rs), ())`. -/
theorem origFixedSign_apply (S : SignatureScheme) (n : ℕ) (sk : List Bool)
    (rs : S.sign.Coins n) (j : Fin 1) (m : Fin (S.msgLen.eval n) → Bool) (s : Unit) :
    origFixedSign S n sk rs j m s =
      .pure (padFin (S.sigLen.eval n) (S.sign.runAt n (pairEncode sk (List.ofFn m)) rs), ()) := rfl

/-- A forwarded log entry asks oracle zero the hash of the inner query and records the
same signature answer: `forwardEntry H S n i e = ⟨0, queryHash H S n i e.2.1, e.2.2⟩`. -/
def forwardEntry (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
    (e : Σ _ : Fin 1, (Fin (H.domLen.eval n) → Bool) × (Fin (S.sigLen.eval n) → Bool)) :
    Σ _ : Fin 1, (Fin (S.msgLen.eval n) → Bool) × (Fin (S.sigLen.eval n) → Bool) :=
  ⟨0, queryHash H S n i e.2.1, e.2.2⟩

/-- Forwarding an entry replaces its query by its hash and retains its signature answer:
`forwardEntry H S n i e = ⟨0, queryHash H S n i e.2.1, e.2.2⟩`. -/
theorem forwardEntry_eq (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
    (e : Σ _ : Fin 1, (Fin (H.domLen.eval n) → Bool) × (Fin (S.sigLen.eval n) → Bool)) :
    forwardEntry H S n i e = ⟨0, queryHash H S n i e.2.1, e.2.2⟩ := rfl

/-- The forwarded output is the hashed message followed by the unchanged signature:
`forwardOutput H S n i a = Fin.append (queryHash H S n i (splitBits a).1) (splitBits a).2`. -/
def forwardOutput (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) :
    Fin (S.msgLen.eval n + S.sigLen.eval n) → Bool :=
  Fin.append (queryHash H S n i (splitBits a).1) (splitBits a).2

/-- The forwarded output concatenates the hash of the message with the signature:
`forwardOutput H S n i a = Fin.append (queryHash H S n i (splitBits a).1) (splitBits a).2`. -/
theorem forwardOutput_eq (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) :
    forwardOutput H S n i a =
      Fin.append (queryHash H S n i (splitBits a).1) (splitBits a).2 := rfl

/-- The forwarded output transported to the declared handler output width:
`handlerOutput H S n i a j =
forwardOutput H S n i a (Fin.cast (HashSignForward.handler_output_width H S n) j)`. -/
def handlerOutput (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) :
    Fin ((HashSignForward.handler H S).outLen.eval n) → Bool :=
  fun j => forwardOutput H S n i a (Fin.cast (HashSignForward.handler_output_width H S n) j)

/-- The handler output is the forwarded output evaluated through its width cast:
`handlerOutput H S n i a =
fun j => forwardOutput H S n i a (Fin.cast (HashSignForward.handler_output_width H S n) j)`. -/
theorem handlerOutput_eq (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) :
    handlerOutput H S n i a = fun j => forwardOutput H S n i a
      (Fin.cast (HashSignForward.handler_output_width H S n) j) := rfl

/-- Querying the original fixed signer on a typed hash gives the common transcript's
hashed reply: `origFixedSign S n sk rs 0 (queryHash H S n i m) () =
.pure (hashedReply H S n sk i rs m, ())`. -/
theorem origFixedSign_queryHash (H : CRH) (S : SignatureScheme) (n : ℕ) (sk i : List Bool)
    (rs : S.sign.Coins n) (m : Fin (H.domLen.eval n) → Bool) :
    origFixedSign S n sk rs 0 (queryHash H S n i m) () =
      .pure (hashedReply H S n sk i rs m, ()) := by
  rw [origFixedSign_apply, hashedReply_eq, HashSignForward.hashWord_unary, queryHash_eq]

/-- The forwarding handler's finalization returns the transported forwarded output:
`(HashSignForward.handler H S).finish n pk ω s a =
.pure (handlerOutput H S n (H.gen.runAtL n [] (List.ofFn ω)) a)`. -/
theorem handler_finish_output (H : CRH) (S : SignatureScheme) (n : ℕ) (pk : List Bool)
    (ω : Fin ((HashSignForward.handler H S).seedLen.eval n) → Bool)
    (s : Fin ((HashSignForward.handler H S).stateLen.eval n) → Bool)
    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) :
    (HashSignForward.handler H S).finish n pk ω s a =
      .pure (handlerOutput H S n (H.gen.runAtL n [] (List.ofFn ω)) a) := by
  rw [HashSignForward.handler_finish_split, handlerOutput_eq, forwardOutput_eq, queryHash_eq]

/-- Fixing the signing tape gives a common adversary output for the inner transcript
and the forwarding reduction: if `c.CostBoundedBy (fun _ => 1) 1`, then `∃ a L,
simulate (fixedSign H S n sk i rs).withLog c ((), []) = .pure (a, ((), L)) ∧
simulate (origFixedSign S n sk rs).withLog ((simulate (K.impl n pk ω) c (K.init n)).bind
fun res => K.finish n pk ω res.2 res.1) ((), []) =
.pure (handlerOutput H S n i a, ((), L.map (forwardEntry H S n i)))`, where
`K = HashSignForward.handler H S` and `i = H.gen.runAtL n [] (List.ofFn ω)`.
The outer query log is obtained by hashing each inner
query and retaining its signature answer.

**Proof sketch.** A one-query computation either returns immediately or asks one query
and returns a function of its answer. In the first case both logs are empty. In the
second case the handler forwards the typed hash, the original fixed signer gives the
same hashed reply as the inner fixed signer, and both continuations return the same
adversary output. Finalization hashes that output's message component. -/
theorem forward_transcript (H : CRH) (S : SignatureScheme) (n : ℕ) (pk sk : List Bool)
    (ω : Fin ((HashSignForward.handler H S).seedLen.eval n) → Bool)
    (rs : S.sign.Coins n)
    (c : OracleComp
      (bitSpec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n))
      (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool))
    (hc : c.CostBoundedBy (fun _ => 1) 1) :
    ∃ (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool)
      (L : QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
        (fun _ => S.sigLen.eval n))),
      simulate (fixedSign H S n sk (H.gen.runAtL n [] (List.ofFn ω)) rs).withLog c
          ((), []) = .pure (a, ((), L)) ∧
        simulate (origFixedSign S n sk rs).withLog
          ((simulate ((HashSignForward.handler H S).impl n pk ω) c
            ((HashSignForward.handler H S).init n)).bind
              (fun res => (HashSignForward.handler H S).finish n pk ω res.2 res.1))
          ((), []) =
          .pure (handlerOutput H S n (H.gen.runAtL n [] (List.ofFn ω)) a,
            ((), L.map (forwardEntry H S n (H.gen.runAtL n [] (List.ofFn ω))))) := by
  rcases one_query_cases c hc with ⟨a, rfl⟩ | ⟨j, m, f, rfl⟩
  · refine ⟨a, [], ?_, ?_⟩
    · rw [simulate_pure]
    · simp only [simulate_pure, OracleComp.pure_bind, handler_finish_output, List.map_nil]
  · refine ⟨f (hashedReply H S n sk (H.gen.runAtL n [] (List.ofFn ω)) rs m),
      [⟨j, m, hashedReply H S n sk (H.gen.runAtL n [] (List.ofFn ω)) rs m⟩], ?_, ?_⟩
    · simp only [simulate_query, QueryImpl.withLog_apply, fixedSign_apply,
        OracleComp.pure_bind, simulate_pure, List.nil_append]
    · simp only [simulate_query, HashSignForward.handler_impl, ← queryHash_eq,
        OracleComp.query_bind, OracleComp.pure_bind, simulate_pure, handler_finish_output,
        QueryImpl.withLog_apply, origFixedSign_queryHash, List.nil_append,
        List.map_cons, List.map_nil, forwardEntry_eq]

/-- The message component of the forwarded output is the hash of the inner message:
`(splitBits (forwardOutput H S n i a)).1 = queryHash H S n i (splitBits a).1`. -/
theorem forwardOutput_message (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) :
    (splitBits (forwardOutput H S n i a)).1 = queryHash H S n i (splitBits a).1 := by
  funext j
  rw [splitBits_fst, forwardOutput_eq, Fin.append_left]

/-- The signature component of the forwarded output is the original signature component:
`(splitBits (forwardOutput H S n i a)).2 = (splitBits a).2`. -/
theorem forwardOutput_signature (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) :
    (splitBits (forwardOutput H S n i a)).2 = (splitBits a).2 := by
  funext j
  rw [splitBits_snd, forwardOutput_eq, Fin.append_right]

/-- If no logged inner query has the hash of the final message, the final hashed message
is fresh in the forwarded log:
`(∀ e ∈ L, queryHash H S n i e.2.1 ≠ queryHash H S n i (splitBits a).1) →
∀ e ∈ L.map (forwardEntry H S n i), e.2.1 ≠ (splitBits (forwardOutput H S n i a)).1`.
This includes the case of an empty inner log. -/
theorem forward_fresh (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool)
    (L : QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
      (fun _ => S.sigLen.eval n)))
    (hfresh : ∀ e ∈ L, queryHash H S n i e.2.1 ≠ queryHash H S n i (splitBits a).1) :
    ∀ e ∈ L.map (forwardEntry H S n i),
      e.2.1 ≠ (splitBits (forwardOutput H S n i a)).1 := by
  intro e he
  obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
  rw [forwardEntry_eq, forwardOutput_message]
  exact hfresh e' he'

/-- Forwarding succeeds when the original verifier accepts the final hashed message and
no inner query has that hash, `ForwardSuccess H S n pk i res ↔
S.Accepts n pk (queryHash H S n i m) σ ∧
∀ e ∈ res.2.2, queryHash H S n i e.2.1 ≠ queryHash H S n i m`,
where `(m, σ) = splitBits res.1` [PS10, Theorem 144.1]. -/
def ForwardSuccess (H : CRH) (S : SignatureScheme) (n : ℕ) (pk i : List Bool)
    (res : (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
        (fun _ => S.sigLen.eval n)))) : Prop :=
  S.Accepts n pk (queryHash H S n i (splitBits res.1).1) (splitBits res.1).2 ∧
    ∀ e ∈ res.2.2, queryHash H S n i e.2.1 ≠ queryHash H S n i (splitBits res.1).1

/-- Forwarding success is original-scheme acceptance and freshness of the final hash
among all hashed inner queries: `ForwardSuccess H S n pk i res ↔
S.Accepts n pk (queryHash H S n i m) σ ∧
∀ e ∈ res.2.2, queryHash H S n i e.2.1 ≠ queryHash H S n i m`,
where `(m, σ) = splitBits res.1`. -/
theorem forwardSuccess_iff (H : CRH) (S : SignatureScheme) (n : ℕ) (pk i : List Bool)
    (res : (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
        (fun _ => S.sigLen.eval n)))) :
    ForwardSuccess H S n pk i res ↔
      S.Accepts n pk (queryHash H S n i (splitBits res.1).1) (splitBits res.1).2 ∧
        ∀ e ∈ res.2.2, queryHash H S n i e.2.1 ≠ queryHash H S n i (splitBits res.1).1 :=
  Iff.rfl

/-- The original forgery event tests acceptance and message freshness on a logged
original-signature transcript,
`OriginalSuccess S n pk res ↔ S.Accepts n pk m σ ∧ ∀ e ∈ res.2.2, e.2.1 ≠ m`, where
`(m, σ) = splitBits res.1` [PS10, Definition 136.2]. -/
def OriginalSuccess (S : SignatureScheme) (n : ℕ) (pk : List Bool)
    (res : (Fin (S.msgLen.eval n + S.sigLen.eval n) → Bool) ×
      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => S.msgLen.eval n)
        (fun _ => S.sigLen.eval n)))) : Prop :=
  S.Accepts n pk (splitBits res.1).1 (splitBits res.1).2 ∧
    ∀ e ∈ res.2.2, e.2.1 ≠ (splitBits res.1).1

/-- The original forgery event is acceptance together with freshness in its logged
original-message queries:
`OriginalSuccess S n pk res ↔ S.Accepts n pk m σ ∧ ∀ e ∈ res.2.2, e.2.1 ≠ m`, where
`(m, σ) = splitBits res.1`. -/
theorem originalSuccess_iff (S : SignatureScheme) (n : ℕ) (pk : List Bool)
    (res : (Fin (S.msgLen.eval n + S.sigLen.eval n) → Bool) ×
      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => S.msgLen.eval n)
        (fun _ => S.sigLen.eval n)))) :
    OriginalSuccess S n pk res ↔
      S.Accepts n pk (splitBits res.1).1 (splitBits res.1).2 ∧
        ∀ e ∈ res.2.2, e.2.1 ≠ (splitBits res.1).1 := Iff.rfl

/-- Hashing the output and every logged query turns the original forgery event into
the common transcript's forwarding-success event:
`OriginalSuccess S n pk (forwardOutput H S n i a, ((), L.map (forwardEntry H S n i))) ↔
ForwardSuccess H S n pk i (a, ((), L))`. -/
theorem originalSuccess_forwardOutput (H : CRH) (S : SignatureScheme) (n : ℕ)
    (pk i : List Bool) (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool)
    (L : QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
      (fun _ => S.sigLen.eval n))) :
    OriginalSuccess S n pk (forwardOutput H S n i a, ((), L.map (forwardEntry H S n i))) ↔
      ForwardSuccess H S n pk i (a, ((), L)) := by
  rw [originalSuccess_iff, forwardSuccess_iff, forwardOutput_message, forwardOutput_signature]
  apply and_congr_right
  intro _
  constructor
  · intro hf e he
    exact hf (forwardEntry H S n i e) (List.mem_map.mpr ⟨e, he, rfl⟩)
  · intro hf e he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    exact hf e' he'

/-- The original one-query forgery game may draw its signing tape before the logged
simulation, `accept (S.forgeGame C 1 n) = 𝔼 rg : S.gen.Coins n, 𝔼 r : C.Coins n,
𝔼 rs : S.sign.Coins n, ProbComp.prob (simulate (origFixedSign S n sk rs).withLog
(C.toCompOn cod n 1 pk r) ((), [])) (OriginalSuccess S n pk)`,
writing `𝔼 x : X, f x` for `ProbComp.expect (ProbComp.sample X) (fun x => f x)`, with
`pk = pairFstD (S.gen.runAt n [] rg)`, `sk = pairSndD (S.gen.runAt n [] rg)` and
`cod = bitCodec (fun _ : Fin 1 => S.msgLen.eval n) (fun _ => S.sigLen.eval n)
(S.msgLen.eval n + S.sigLen.eval n)` [PS10, Definition 136.2, one-time specialization].

**Proof sketch.** Read key sampling, adversary sampling and the forgery test from the
published game equation. The adversary has at most one query, so the one-query sampling
lemma moves its fresh signing-tape sample outside the simulation. -/
theorem forgeGame_eq_fixed (S : SignatureScheme) (C : NUPPT) (n : ℕ) :
    accept (S.forgeGame C 1 n) =
      ProbComp.expect (ProbComp.sample (S.gen.Coins n)) (fun rg =>
        ProbComp.expect (ProbComp.sample (C.Coins n)) (fun r =>
          ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
            ProbComp.prob
              (simulate (origFixedSign S n (pairSndD (S.gen.runAt n [] rg)) rs).withLog
                (C.toCompOn
                  (bitCodec (fun _ : Fin 1 => S.msgLen.eval n) (fun _ => S.sigLen.eval n)
                    (S.msgLen.eval n + S.sigLen.eval n)) n 1
                  (pairFstD (S.gen.runAt n [] rg)) r) ((), []))
              (OriginalSuccess S n (pairFstD (S.gen.runAt n [] rg)))))) := by
  classical
  rw [S.forgeGame_eq, accept_eq, ProbComp.prob_eq_expect]
  simp only [ProbComp.expect_bind, ProbComp.expect_pure, decide_eq_true_eq,
    S.forgerCodec_eq_bitCodec]
  apply congrArg (ProbComp.expect (ProbComp.sample (S.gen.Coins n)))
  funext rg
  apply congrArg (ProbComp.expect (ProbComp.sample (C.Coins n)))
  funext r
  have hraw := expect_simulate_sample_once
    (fun (_ : Fin 1) m rs => padFin (S.sigLen.eval n)
      (S.sign.runAt n (pairEncode (pairSndD (S.gen.runAt n [] rg)) (List.ofFn m)) rs))
    (C.toCompOn
      (bitCodec (fun _ : Fin 1 => S.msgLen.eval n) (fun _ => S.sigLen.eval n)
        (S.msgLen.eval n + S.sigLen.eval n)) n 1 (pairFstD (S.gen.runAt n [] rg)) r)
    (C.toCompOn_costBoundedBy _ n 1 _ r)
    (fun res => if OriginalSuccess S n (pairFstD (S.gen.runAt n [] rg)) res then 1 else 0)
  simpa only [S.signImpl_eq, originalSuccess_iff, origFixedSign_eq,
    ProbComp.prob_eq_expect] using hraw

/-- The transported handler output and the forwarded output have the same bit list:
`List.ofFn (handlerOutput H S n i a) = List.ofFn (forwardOutput H S n i a)`. -/
theorem ofFn_handlerOutput (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) :
    List.ofFn (handlerOutput H S n i a) = List.ofFn (forwardOutput H S n i a) := by
  rw [handlerOutput_eq]
  exact (List.ofFn_congr (HashSignForward.handler_output_width H S n).symm
    (forwardOutput H S n i a)).symm

/-- With all tapes fixed, reading the forwarding reduction's output list at the original
game's width gives the common transcript's forwarding-success probability: if
`c.CostBoundedBy (fun _ => 1) 1`, then `ProbComp.prob ((simulate (origFixedSign S n sk rs).withLog
R ((), [])).bind fun res => .pure (padFin (S.msgLen.eval n + S.sigLen.eval n) (List.ofFn res.1),
res.2)) (OriginalSuccess S n pk) = ProbComp.prob
(simulate (fixedSign H S n sk i rs).withLog c ((), [])) (ForwardSuccess H S n pk i)`, where
`R = (simulate (K.impl n pk ω) c (K.init n)).bind fun res => K.finish n pk ω res.2 res.1`,
`K = HashSignForward.handler H S` and `i = H.gen.runAtL n [] (List.ofFn ω)`.

**Proof sketch.** The deterministic coupling gives the same adversary output and a log
whose queries are precisely the inner query hashes. The output-component and event
readers identify the two success tests, so their probabilities on these pure runs agree. -/
theorem forward_prob_transcript (H : CRH) (S : SignatureScheme) (n : ℕ) (pk sk : List Bool)
    (ω : Fin ((HashSignForward.handler H S).seedLen.eval n) → Bool)
    (rs : S.sign.Coins n)
    (c : OracleComp
      (bitSpec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n))
      (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool))
    (hc : c.CostBoundedBy (fun _ => 1) 1) :
    ProbComp.prob
      ((simulate (origFixedSign S n sk rs).withLog
        ((simulate ((HashSignForward.handler H S).impl n pk ω) c
          ((HashSignForward.handler H S).init n)).bind
            (fun res => (HashSignForward.handler H S).finish n pk ω res.2 res.1))
        ((), [])).bind (fun res =>
          .pure (padFin (S.msgLen.eval n + S.sigLen.eval n) (List.ofFn res.1), res.2)))
      (OriginalSuccess S n pk) =
      ProbComp.prob
        (simulate (fixedSign H S n sk (H.gen.runAtL n [] (List.ofFn ω)) rs).withLog c ((), []))
        (ForwardSuccess H S n pk (H.gen.runAtL n [] (List.ofFn ω))) := by
  classical
  obtain ⟨a, L, hinner, houter⟩ := forward_transcript H S n pk sk ω rs c hc
  rw [houter, hinner, OracleComp.pure_bind, ProbComp.prob_pure, ofFn_handlerOutput,
    padFin_ofFn, ProbComp.prob_pure]
  exact if_congr (originalSuccess_forwardOutput H S n pk _ a L) rfl rfl

/-- A one-query machine against the original scheme realizes exactly the common
transcript's forwarding-success probability, `∃ C : NUPPT, ∀ n, accept (S.forgeGame C 1 n) =
𝔼 rg : S.gen.Coins n, 𝔼 ri : H.gen.Coins n, 𝔼 rA : A.Coins n, 𝔼 rs : S.sign.Coins n,
ProbComp.prob (transcript H S A n pk sk i rs rA) (ForwardSuccess H S n pk i)`,
writing `𝔼 x : X, f x` for `ProbComp.expect (ProbComp.sample X) (fun x => f x)`, with
`pk = pairFstD (S.gen.runAt n [] rg)`, `sk = pairSndD (S.gen.runAt n [] rg)` and
`i = H.gen.runAt n [] ri` [PS10, Theorem 144.1].

**Proof sketch.** T2 supplies the forwarding machine and a bijection between its coins
and the independent hash-generator seed and original adversary coins. Reindex the
original forgery experiment by this bijection and then by the hash generator's published
coin equivalence. Drawing the single signing tape in advance gives the deterministic
coupling, whose mapped query log and hashed output identify the two success events. -/
theorem exists_forwardGame (H : CRH) (S : SignatureScheme) (A : NUPPT) :
    ∃ C : NUPPT, ∀ n : ℕ,
      accept (S.forgeGame C 1 n) =
        ProbComp.expect (ProbComp.sample (S.gen.Coins n)) (fun rg =>
          ProbComp.expect (ProbComp.sample (H.gen.Coins n)) (fun ri =>
            ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA =>
              ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
                ProbComp.prob
                  (transcript H S A n (pairFstD (S.gen.runAt n [] rg))
                    (pairSndD (S.gen.runAt n [] rg)) (H.gen.runAt n [] ri) rs rA)
                  (ForwardSuccess H S n (pairFstD (S.gen.runAt n [] rg))
                    (H.gen.runAt n [] ri)))))) := by
  classical
  obtain ⟨C, hC⟩ := HashSignForward.exists_forwardMachine H S A
  refine ⟨C, fun n => ?_⟩
  obtain ⟨φ, hφ⟩ := hC n
  let e := NUPPT.coinsEquivPoly (A := H.gen) (HashSignForward.handler_seedLen H S).symm n
  have he : ∀ ri : H.gen.Coins n, List.ofFn (e ri) = List.ofFn ri :=
    NUPPT.coinsEquivPoly_ofFn _ n
  rw [forgeGame_eq_fixed]
  apply congrArg (ProbComp.expect (ProbComp.sample (S.gen.Coins n)))
  funext rg
  rw [← ProbComp.expect_sample_equiv φ, ← Bridge.expect_sample_pair]
  simp only [ProbComp.expect_bind, ProbComp.expect_pure]
  rw [← ProbComp.expect_sample_equiv e]
  apply congrArg (ProbComp.expect (ProbComp.sample (H.gen.Coins n)))
  funext ri
  apply congrArg (ProbComp.expect (ProbComp.sample (A.Coins n)))
  funext rA
  apply congrArg (ProbComp.expect (ProbComp.sample (S.sign.Coins n)))
  funext rs
  have hout := expect_toCompOn_outLen
    (origFixedSign S n (pairSndD (S.gen.runAt n [] rg)) rs).withLog C n 1
    (pairFstD (S.gen.runAt n [] rg)) (φ (e ri, rA)) ((), [])
    (HashSignForward.handler_output_width H S n).symm
    (fun res => if OriginalSuccess S n (pairFstD (S.gen.runAt n [] rg))
      (padFin (S.msgLen.eval n + S.sigLen.eval n) res.1, res.2) then 1 else 0)
  simp only [padFin_ofFn] at hout
  rw [ProbComp.prob_eq_expect, hout]
  rw [← hφ _ (e ri) rA]
  let c := A.toCompOn
    (bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
      (H.domLen.eval n + S.sigLen.eval n)) n 1
    ((HashSignForward.handler H S).advInput n (pairFstD (S.gen.runAt n [] rg)) (e ri)) rA
  have hforward := forward_prob_transcript H S n (pairFstD (S.gen.runAt n [] rg))
    (pairSndD (S.gen.runAt n [] rg)) (e ri) rs c
    (A.toCompOn_costBoundedBy _ n 1 _ rA)
  rw [ProbComp.prob_bind] at hforward
  simp only [ProbComp.prob_pure, padFin_ofFn] at hforward
  rw [hforward]
  dsimp only [c]
  rw [HashSignForward.handler_advInput, he, ← NUPPT.runAt_eq, transcript_eq]

end TCSlib.Cryptography.Authentication.HashSignFill

## ===== TCSlib/Cryptography/Authentication/Signatures/HashAndSign/ForwardHandler.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Forwarding
import TCSlib.Cryptography.Authentication.Signatures.Defs
import TCSlib.Cryptography.Hashing.CollisionResistant
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The hash-and-sign forwarding handler

The one-time forger reduction samples a hash index, gives the public key and index to
its adversary, hashes each query before forwarding it, and hashes the final message.

## Main definitions

* `HashSignForward.indexWord`: the hash index obtained from the handler's seed.
* `HashSignForward.hashWord`: the hash read at the original signature message length.
* `HashSignForward.handler`: the interactive handler of [PS10, Theorem 144.1].

## Main results

The string functions are polynomial-time, and the handler's published field equations
expose its seed, budgets, adversary input, round and finalization.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Theorem 144.1, book pp. 144–145.
-/

namespace TCSlib.Cryptography.Authentication.HashSignForward

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open InteractiveHandler

/-- The index generator on parameter word `u` and seed `ω`, with empty input and advice:
`indexWord H u ω = H.gen.output (NUPPT.layout u [] [] ω)`. -/
def indexWord (H : CRH) (u ω : List Bool) : List Bool :=
  H.gen.output (NUPPT.layout u [] [] ω)

/-- The index word is `H.gen.output (NUPPT.layout u [] [] ω)`:
`indexWord H u ω = H.gen.output (NUPPT.layout u [] [] ω)`. -/
theorem indexWord_eq (H : CRH) (u ω : List Bool) :
    indexWord H u ω = H.gen.output (NUPPT.layout u [] [] ω) := rfl

/-- The hash of `m` at index `i`, padded to the original scheme's message length:
`hashWord H S u i m = padStr S.msgLen u (H.eval (pairEncode u (pairEncode i m)))`. -/
def hashWord (H : CRH) (S : SignatureScheme) (u i m : List Bool) : List Bool :=
  padStr S.msgLen u (H.eval (pairEncode u (pairEncode i m)))

/-- The hash word is the evaluator output padded to `S.msgLen(|u|)` bits:
`hashWord H S u i m = padStr S.msgLen u (H.eval (pairEncode u (pairEncode i m)))`. -/
theorem hashWord_eq (H : CRH) (S : SignatureScheme) (u i m : List Bool) :
    hashWord H S u i m =
      padStr S.msgLen u (H.eval (pairEncode u (pairEncode i m))) := rfl

/-- The reduction gives its adversary the public key paired with its sampled index:
`advWord H w =
pairEncode (pairFstD (pairSndD w)) (indexWord H (pairFstD w) (pairSndD (pairSndD w)))`. -/
def advWord (H : CRH) (w : List Bool) : List Bool :=
  pairEncode (pairFstD (pairSndD w))
    (indexWord H (pairFstD w) (pairSndD (pairSndD w)))

/-- The adversary input pairs the reduction input with the index obtained from its seed:
`advWord H w =
pairEncode (pairFstD (pairSndD w)) (indexWord H (pairFstD w) (pairSndD (pairSndD w)))`. -/
theorem advWord_eq (H : CRH) (w : List Bool) :
    advWord H w = pairEncode (pairFstD (pairSndD w))
      (indexWord H (pairFstD w) (pairSndD (pairSndD w))) := rfl

/-- The first round asks the original signing oracle the hashed message; the second
round returns the outer signature and preserves the state: `roundWord H S w =
if decide (rL w = []) then pairEncode [false] (pairEncode [] (hashWord H S u (indexWord H u (rW w))
(rX w))) else pairEncode [true] (rAns w ++ rS w)`, where `u = rU w`. -/
def roundWord (H : CRH) (S : SignatureScheme) (w : List Bool) : List Bool :=
  if decide (rL w = []) then
    pairEncode [false] (pairEncode []
      (hashWord H S (rU w) (indexWord H (rU w) (rW w)) (rX w)))
  else pairEncode [true] (rAns w ++ rS w)

/-- The round asks the hashed query when its outer log is empty, and otherwise returns
the first outer answer together with its unchanged state: `roundWord H S w =
if decide (rL w = []) then pairEncode [false] (pairEncode [] (hashWord H S u (indexWord H u (rW w))
(rX w))) else pairEncode [true] (rAns w ++ rS w)`, where `u = rU w`. -/
theorem roundWord_eq (H : CRH) (S : SignatureScheme) (w : List Bool) :
    roundWord H S w =
      if decide (rL w = []) then
        pairEncode [false] (pairEncode []
          (hashWord H S (rU w) (indexWord H (rU w) (rW w)) (rX w)))
      else pairEncode [true] (rAns w ++ rS w) := rfl

/-- The finalization hashes the message prefix of the adversary output and retains
its signature suffix, making no further oracle query: `finalWord H S w =
pairEncode [true] (hashWord H S u (indexWord H u (rW w)) (a.take k) ++ a.drop k)`, where
`u = rU w`, `a = finA w` and `k = H.domLen.eval u.length`. -/
def finalWord (H : CRH) (S : SignatureScheme) (w : List Bool) : List Bool :=
  pairEncode [true]
    (hashWord H S (rU w) (indexWord H (rU w) (rW w))
      ((finA w).take (H.domLen.eval (rU w).length)) ++
      (finA w).drop (H.domLen.eval (rU w).length))

/-- The final output is the hashed message prefix concatenated with the signature suffix:
`finalWord H S w =
pairEncode [true] (hashWord H S u (indexWord H u (rW w)) (a.take k) ++ a.drop k)`, where
`u = rU w`, `a = finA w` and `k = H.domLen.eval u.length`. -/
theorem finalWord_eq (H : CRH) (S : SignatureScheme) (w : List Bool) :
    finalWord H S w = pairEncode [true]
      (hashWord H S (rU w) (indexWord H (rU w) (rW w))
        ((finA w).take (H.domLen.eval (rU w).length)) ++
        (finA w).drop (H.domLen.eval (rU w).length)) := rfl

/-- Running the index generator on polynomial-time parameter and seed words is
polynomial-time: `PolyTimeComputable u → PolyTimeComputable ω →
PolyTimeComputable fun w => indexWord H (u w) (ω w)`. -/
theorem polyTimeComputable_indexWord (H : CRH) {u ω : List Bool → List Bool}
    (hu : PolyTimeComputable u) (hω : PolyTimeComputable ω) :
    PolyTimeComputable fun w => indexWord H (u w) (ω w) := by
  simpa only [indexWord, Function.comp_apply] using
    H.gen.polyTimeComputable_output.comp
      (NUPPT.polyTimeComputable_layout hu (polyTimeComputable_const [])
        (polyTimeComputable_const []) hω)

/-- Hashing polynomial-time parameter, index and message words and padding the result
to the original signature message length is polynomial-time: `PolyTimeComputable u →
PolyTimeComputable i → PolyTimeComputable m →
PolyTimeComputable fun w => hashWord H S (u w) (i w) (m w)`. -/
theorem polyTimeComputable_hashWord (H : CRH) (S : SignatureScheme)
    {u i m : List Bool → List Bool} (hu : PolyTimeComputable u)
    (hi : PolyTimeComputable i) (hm : PolyTimeComputable m) :
    PolyTimeComputable fun w => hashWord H S (u w) (i w) (m w) := by
  have h := (polyTimeComputable_padStr S.msgLen).comp
    (hu.pairEncode (H.eval_poly.comp (hu.pairEncode (hi.pairEncode hm))))
  refine (congrArg PolyTimeComputable
    (?_ : (fun w => hashWord H S (u w) (i w) (m w)) = _)).mpr h
  funext w
  simp only [hashWord_eq, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- Pairing the supplied public key with the index generated from the seed is
polynomial-time: `PolyTimeComputable (advWord H)`, for `advWord H : List Bool → List Bool`. -/
theorem polyTimeComputable_advWord (H : CRH) : PolyTimeComputable (advWord H) := by
  exact (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).pairEncode
    (polyTimeComputable_indexWord H polyTimeComputable_pairFstD
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))

/-- One hashing-and-forwarding round is polynomial-time, `PolyTimeComputable (roundWord H S)`
for `roundWord H S : List Bool → List Bool`: it tests whether the outer log is empty, then
either emits the hash query or returns the recorded answer. -/
theorem polyTimeComputable_roundWord (H : CRH) (S : SignatureScheme) :
    PolyTimeComputable (roundWord H S) := by
  exact polyTimeComputable_ite
    (polyTimeComputable_isNil.comp polyTimeComputable_rL)
    ((polyTimeComputable_const [false]).pairEncode
      ((polyTimeComputable_const []).pairEncode
        (polyTimeComputable_hashWord H S polyTimeComputable_rU
          (polyTimeComputable_indexWord H polyTimeComputable_rU polyTimeComputable_rW)
          polyTimeComputable_rX)))
    ((polyTimeComputable_const [true]).pairEncode
      (polyTimeComputable_rAns.append polyTimeComputable_rS))

/-- Finalization is polynomial-time, `PolyTimeComputable (finalWord H S)` for
`finalWord H S : List Bool → List Bool`: split at the polynomial domain width, hash the
message prefix and concatenate the original signature suffix.

**Proof sketch.** The published polynomial take and drop operations apply to the parameter
and output fields. The parameter, seed and output readers and the index and hash operations
are polynomial-time, so composition and concatenation give the result. -/
theorem polyTimeComputable_finalWord (H : CRH) (S : SignatureScheme) :
    PolyTimeComputable (finalWord H S) := by
  have hm := (polyTimeComputable_pairTakePoly H.domLen).comp
    (polyTimeComputable_rU.pairEncode polyTimeComputable_finA)
  have hs := (polyTimeComputable_pairDropPoly H.domLen).comp
    (polyTimeComputable_rU.pairEncode polyTimeComputable_finA)
  have h := (polyTimeComputable_const [true]).pairEncode
    ((polyTimeComputable_hashWord H S polyTimeComputable_rU
      (polyTimeComputable_indexWord H polyTimeComputable_rU polyTimeComputable_rW) hm).append hs)
  refine (congrArg PolyTimeComputable (?_ : finalWord H S = _)).mpr h
  funext w
  simp only [finalWord_eq, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- The hash-and-sign reduction handler [PS10, Theorem 144.1]: sample one hash index,
provide `⟨pk,i⟩`, forward each query after hashing it, and hash the final message, with
`seedLen = H.gen.coins`, `advIn = advWord H`, `run = roundWord H S`, `finRun = finalWord H S`,
`init _ = zeroBits _` and `outLen = .add S.msgLen S.sigLen`. Its state
is empty, each inner call makes one outer call and finalization makes none. -/
def handler (H : CRH) (S : SignatureScheme) :
    InteractiveHandler 1 (fun _ => H.domLen) (fun _ => S.sigLen)
      1 (fun _ => S.msgLen) (fun _ => S.sigLen) where
  stateLen := .const 0
  seedLen := H.gen.coins
  perCall := .const 1
  init _ := zeroBits _
  run := roundWord H S
  poly := polyTimeComputable_roundWord H S
  advIn := advWord H
  advIn_poly := polyTimeComputable_advWord H
  outLen := .add S.msgLen S.sigLen
  finCall := .const 0
  finRun := finalWord H S
  finRun_poly := polyTimeComputable_finalWord H S

attribute [simps (config := { isSimp := false }) stateLen seedLen perCall init run advIn outLen
  finCall finRun] handler

/-- At a unary parameter, the generated index word is the hash generator's literal run
with the supplied list of coins: `indexWord H (List.replicate n true) ω = H.gen.runAtL n [] ω`. -/
theorem indexWord_unary (H : CRH) (n : ℕ) (ω : List Bool) :
    indexWord H (List.replicate n true) ω = H.gen.runAtL n [] ω := by
  rw [indexWord_eq, H.gen_uniform.runAtL_eq, NUPPT.layout_eq, NUPPT.advInput_eq]

/-- At unary parameter `1^n`, the hash word is the list of the padded evaluator at
the original signature message length: `hashWord H S (List.replicate n true) i m =
List.ofFn (padFin (S.msgLen.eval n) (H.eval (atParam n (pairEncode i m))))`. -/
theorem hashWord_unary (H : CRH) (S : SignatureScheme) (n : ℕ) (i m : List Bool) :
    hashWord H S (List.replicate n true) i m =
      List.ofFn (padFin (S.msgLen.eval n) (H.eval (atParam n (pairEncode i m)))) := by
  rw [hashWord_eq, ← ofFn_padFin_eq_padStr, List.length_replicate, atParam_eq]

/-- The handler gives the adversary `⟨pk,i⟩`, where `i` is the hash generator's run
on its seed: `(handler H S).advInput n pk ω = pairEncode pk (H.gen.runAtL n [] (List.ofFn ω))`. -/
theorem handler_advInput (H : CRH) (S : SignatureScheme) (n : ℕ) (pk : List Bool)
    (ω : Fin ((handler H S).seedLen.eval n) → Bool) :
    (handler H S).advInput n pk ω =
      pairEncode pk (H.gen.runAtL n [] (List.ofFn ω)) := by
  rw [InteractiveHandler.advInput_eq, handler_advIn, advWord_eq, seedIn_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, indexWord_unary]

/-- Each call asks the original signing oracle for the hash of its inner message and
returns the outer signature unchanged, preserving the handler state:
`(handler H S).impl n pk ω i x s = .query 0 (padFin (S.msgLen.eval n)
(H.eval (atParam n (pairEncode (H.gen.runAtL n [] (List.ofFn ω)) (List.ofFn x)))))
fun y => .pure (y, s)`.

**Proof sketch.** The first round has an empty outer log and emits precisely the padded
hash query. The second round reads the first outer answer and returns it with the state.
The published one-query call rule therefore identifies the entire call computation. -/
theorem handler_impl (H : CRH) (S : SignatureScheme) (n : ℕ) (pk : List Bool)
    (ω : Fin ((handler H S).seedLen.eval n) → Bool) (i : Fin 1)
    (x : Fin (H.domLen.eval n) → Bool)
    (s : Fin ((handler H S).stateLen.eval n) → Bool) :
    (handler H S).impl n pk ω i x s =
      .query 0
        (padFin (S.msgLen.eval n) (H.eval
          (atParam n (pairEncode (H.gen.runAtL n [] (List.ofFn ω)) (List.ofFn x)))))
        fun y => .pure (y, s) := by
  refine InteractiveHandler.impl_of_query (handler H S) n pk ω x s 0 _
    (fun y => y) (fun _ => s) ?_ ?_ ?_
  · rw [handler_perCall, PolyExpr.eval_const]
  · rw [handler_run, roundWord_eq, rL_input, rU_input, rW_input, rX_input,
      indexWord_unary, hashWord_unary, if_pos (decide_eq_true rfl)]
    rfl
  · intro y
    rw [handler_run, roundWord_eq, rL_input, rAns_input, rS_input,
      if_neg (fun h => pairEncode_ne_nil _ _ (of_decide_eq_true h))]

/-- Finalization makes no oracle query and returns the hash of the adversary's message
prefix concatenated with its signature suffix, read at the handler's output length:
`(handler H S).finish n pk ω s a = .pure (padFin ((handler H S).outLen.eval n)
(hashWord H S (List.replicate n true) i ((List.ofFn a).take d) ++ (List.ofFn a).drop d))`,
where `i = H.gen.runAtL n [] (List.ofFn ω)` and `d = H.domLen.eval n`.

**Proof sketch.** The hash word has the signature scheme's message width. The suffix of
the correctly sized adversary output has the signature width, so the concatenation has
the declared output width. The first finalization round returns this word; the published
immediate-return finalization rule identifies its computation. -/
theorem handler_finish (H : CRH) (S : SignatureScheme) (n : ℕ) (pk : List Bool)
    (ω : Fin ((handler H S).seedLen.eval n) → Bool)
    (s : Fin ((handler H S).stateLen.eval n) → Bool)
    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) :
    (handler H S).finish n pk ω s a =
      .pure (padFin ((handler H S).outLen.eval n)
        (hashWord H S (List.replicate n true) (H.gen.runAtL n [] (List.ofFn ω))
          ((List.ofFn a).take (H.domLen.eval n)) ++
          (List.ofFn a).drop (H.domLen.eval n))) := by
  refine InteractiveHandler.finish_of_ret_padFin (handler H S) n pk ω s a _ ?_ ?_
  · rw [List.length_append, hashWord_unary, List.length_ofFn, List.length_drop,
      List.length_ofFn, handler_outLen, PolyExpr.eval_add]
    omega
  · rw [handler_finRun, finalWord_eq, rU_finInput, rW_finInput, finA_finInput,
      indexWord_unary, List.length_replicate]

/-- When the hash range and signature message widths agree, hashing a typed domain
message gives the list of the CRH hash, transported to the signature message width: for
`hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n`,
`hashWord H S (List.replicate n true) i (List.ofFn x) =
List.ofFn (fun j : Fin (S.msgLen.eval n) => H.hash n i x (Fin.cast (hlen n).symm j))`. -/
theorem hashWord_eq_hash (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) (n : ℕ) (i : List Bool)
    (x : Fin (H.domLen.eval n) → Bool) :
    hashWord H S (List.replicate n true) i (List.ofFn x) =
      List.ofFn (fun j : Fin (S.msgLen.eval n) =>
        H.hash n i x (Fin.cast (hlen n).symm j)) := by
  rw [hashWord_unary]
  apply congrArg List.ofFn
  funext j
  rw [CRH.hash_eq, padFin_apply, padFin_apply, Fin.coe_cast]

/-- The hash-and-sign forwarding reduction is a one-query oracle machine,
`∃ C : NUPPT, ∀ n, ∃ φ : (Fin (K.seedLen.eval n) → Bool) × A.Coins n ≃ C.Coins n, ∀ pk ω r,
(simulate (K.impl n pk ω) (A.toCompOn cod n 1 (K.advInput n pk ω) r) (K.init n)).bind
(fun res => K.finish n pk ω res.2 res.1) = C.toCompOn cod' n 1 pk (φ (ω, r))`, where
`K = handler H S`, `cod = bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
(H.domLen.eval n + S.sigLen.eval n)` and `cod' = bitCodec (fun _ : Fin 1 => S.msgLen.eval n)
(fun _ => S.sigLen.eval n) (K.outLen.eval n)` [PS10, Theorem 144.1].
For every parameter, a bijection identifies its coins with the
handler seed and the original adversary coins, and its computation is the handler's
simulation followed by finalization.

**Proof sketch.** Apply T2 to the hashing handler and the constant-one inner query
budget. One outer query per inner query and zero finalization queries give outer
budget `1 · 1 + 0 = 1`; the codec widths are the signature message and signature widths. -/
theorem exists_forwardMachine (H : CRH) (S : SignatureScheme) (A : NUPPT) :
    ∃ C : NUPPT, ∀ n : ℕ,
      ∃ φ : (Fin ((handler H S).seedLen.eval n) → Bool) × A.Coins n ≃ C.Coins n,
        ∀ (pk : List Bool) (ω : Fin ((handler H S).seedLen.eval n) → Bool)
          (r : A.Coins n),
          (simulate ((handler H S).impl n pk ω)
            (A.toCompOn
              (bitCodec (fun _ : Fin 1 => H.domLen.eval n) (fun _ => S.sigLen.eval n)
                (H.domLen.eval n + S.sigLen.eval n))
              n 1 ((handler H S).advInput n pk ω) r)
            ((handler H S).init n)).bind
              (fun res => (handler H S).finish n pk ω res.2 res.1) =
            C.toCompOn
              (bitCodec (fun _ : Fin 1 => S.msgLen.eval n) (fun _ => S.sigLen.eval n)
                ((handler H S).outLen.eval n))
              n 1 pk (φ (ω, r)) := by
  obtain ⟨C, hC⟩ := exists_interactiveHandlerMachine A (.const 1)
    (fun _ : Fin 1 => H.domLen) (fun _ => S.sigLen)
    (fun _ : Fin 1 => S.msgLen) (fun _ => S.sigLen)
    (.add H.domLen S.sigLen) (handler H S)
  simp only [PolyExpr.eval_const, PolyExpr.eval_add, handler_perCall,
    handler_finCall, Nat.one_mul, Nat.add_zero] at hC
  exact ⟨C, hC⟩

/-- The handler output width is the sum of the original message and signature widths:
`(handler H S).outLen.eval n = S.msgLen.eval n + S.sigLen.eval n`. -/
theorem handler_output_width (H : CRH) (S : SignatureScheme) (n : ℕ) :
    (handler H S).outLen.eval n = S.msgLen.eval n + S.sigLen.eval n :=
  (congrArg (fun p : PolyExpr => p.eval n) (handler_outLen H S)).trans
    (PolyExpr.eval_add S.msgLen S.sigLen n)

/-- Finalization returns the hashed message component paired by concatenation with
the adversary's signature component: `(handler H S).finish n pk ω s a = .pure (fun j =>
Fin.append
(padFin (S.msgLen.eval n) (H.eval (atParam n (pairEncode i (List.ofFn (splitBits a).1)))))
(splitBits a).2 (Fin.cast (handler_output_width H S n) j))`, where
`i = H.gen.runAtL n [] (List.ofFn ω)`. The displayed cast transports the declared handler
output width to the sum of message and signature widths.

**Proof sketch.** Read finalization as a padded list, split the adversary list at the
domain width with the published take/drop lemma, and identify the concatenation as the
list of a `Fin.append` vector. Reading that list at its width recovers the vector. -/
theorem handler_finish_split (H : CRH) (S : SignatureScheme) (n : ℕ) (pk : List Bool)
    (ω : Fin ((handler H S).seedLen.eval n) → Bool)
    (s : Fin ((handler H S).stateLen.eval n) → Bool)
    (a : Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) :
    (handler H S).finish n pk ω s a =
      .pure (fun j =>
        Fin.append
          (padFin (S.msgLen.eval n) (H.eval (atParam n
            (pairEncode (H.gen.runAtL n [] (List.ofFn ω))
              (List.ofFn (splitBits a).1)))))
          (splitBits a).2 (Fin.cast (handler_output_width H S n) j)) := by
  have hf : (splitBits a).1 = fun j => a (Fin.castAdd (S.sigLen.eval n) j) :=
    funext fun j => splitBits_fst a j
  have hs : (splitBits a).2 = fun j => a (Fin.natAdd (H.domLen.eval n) j) :=
    funext fun j => splitBits_snd a j
  rw [hf, hs]
  rw [handler_finish, (EffFill.ofFn_take_drop_add a).1,
    (EffFill.ofFn_take_drop_add a).2, hashWord_unary, ← List.ofFn_fin_append]
  congr 1
  funext j
  rw [padFin_apply, ← Fin.coe_cast (handler_output_width H S n) j,
    ← padFin_apply, padFin_ofFn]

end TCSlib.Cryptography.Authentication.HashSignForward

## ===== TCSlib/Cryptography/Authentication/Signatures/HashAndSign/OneQuery.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Machines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Computations with at most one oracle query

## Main definitions

This module introduces no definitions.

## Main results

* `HashSignFill.eq_pure_of_cost_zero`: a zero-budget computation returns a value.
* `HashSignFill.one_query_cases`: a one-budget computation either returns immediately or
  asks one query and returns a function of its answer.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 144.1 (technical support for its one-query reductions).
-/

namespace TCSlib.Cryptography.Authentication.HashSignFill

open TCSlib.Cryptography.Games

/-- A computation whose every query costs one and whose budget is zero is `pure a` for some
value `a`: a query would require `1 ≤ 0`. -/
theorem eq_pure_of_cost_zero {ι α : Type} {spec : OracleSpec ι}
    (c : OracleComp spec α) (h : c.CostBoundedBy (fun _ => 1) 0) :
    ∃ a, c = .pure a := by
  cases c with
  | pure a => exact ⟨a, rfl⟩
  | query i x k =>
    have hbad := (OracleComp.costBoundedBy_query _ _ _ _ _).mp h
    omega

/-- A computation with unit query costs and budget one either returns immediately or is one
query followed by a return: `c.CostBoundedBy (fun _ => 1) 1 →
(∃ a, c = .pure a) ∨ ∃ i x f, c = .query i x (fun y => .pure (f y))`.
The continuation of a query has budget zero, so each of its
branches is pure; choosing those return values gives its answer function. -/
theorem one_query_cases {ι α : Type} {spec : OracleSpec ι}
    (c : OracleComp spec α) (h : c.CostBoundedBy (fun _ => 1) 1) :
    (∃ a, c = .pure a) ∨
      ∃ (i : ι) (x : spec.dom i) (f : spec.rng i → α),
        c = .query i x (fun y => .pure (f y)) := by
  classical
  cases c with
  | pure a => exact Or.inl ⟨a, rfl⟩
  | query i x k =>
    have hk := (OracleComp.costBoundedBy_query _ _ _ _ _).mp h
    have hp : ∀ y, ∃ a, k y = .pure a :=
      fun y => eq_pure_of_cost_zero (k y) (hk.2 y)
    choose f hf using hp
    exact Or.inr ⟨i, x, f, congrArg (OracleComp.query i x) (funext hf)⟩

end TCSlib.Cryptography.Authentication.HashSignFill

## ===== TCSlib/Cryptography/Authentication/Signatures/HashAndSign/OneQuerySampling.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.OneQuery
import TCSlib.Cryptography.Games.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Drawing one-query oracle randomness in advance

## Main definitions

This module introduces no definitions.

## Main results

* `HashSignFill.expect_simulate_sample_once`: for a computation making at most one query,
  freshly sampling the oracle's answer tape has the same law, including its query log, as
  drawing that tape before the computation.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 144.1 (technical support for the collision-finding reduction).
-/

namespace TCSlib.Cryptography.Authentication.HashSignFill

open TCSlib.Cryptography.Games

/-- For a computation making at most one query, sampling an independent tape for every
oracle answer is equivalent to sampling one tape before the computation, for every real
payoff of the returned value and full query log: if `c.CostBoundedBy (fun _ => 1) 1`, then
`ProbComp.expect (simulate (QueryImpl.ofComp (σ := Unit) (fun i x =>
(ProbComp.sample R).bind fun r => .pure (ans i x r))).withLog c ((), [])) g =
ProbComp.expect (ProbComp.sample R) (fun r => ProbComp.expect
(simulate (QueryImpl.withLog (fun i x _ => .pure (ans i x r, ()))) c ((), [])) g)`.

**Proof sketch.** A computation of unit cost at most one either returns immediately or
asks a fixed query and returns a function of its answer (`one_query_cases`). In the first
case the extra sample integrates a constant. In the second case both expectations reduce
to the same expectation over the single answer tape, with the same one-entry log. -/
theorem expect_simulate_sample_once {ι α R : Type} {spec : OracleSpec ι}
    [Fintype R] [Nonempty R] (ans : ∀ i, spec.dom i → R → spec.rng i)
    (c : OracleComp spec α) (hc : c.CostBoundedBy (fun _ => 1) 1)
    (g : α × (Unit × QueryLog spec) → ℝ) :
    ProbComp.expect
        (simulate
          (QueryImpl.ofComp (σ := Unit) (fun i x =>
            (ProbComp.sample R).bind fun r => .pure (ans i x r))).withLog c ((), [])) g =
      ProbComp.expect (ProbComp.sample R) (fun r =>
        ProbComp.expect
          (simulate
            (QueryImpl.withLog (fun (i : ι) (x : spec.dom i) (_ : Unit) =>
              (OracleComp.pure (ans i x r, ()) : ProbComp (spec.rng i × Unit))))
            c ((), [])) g) := by
  rcases one_query_cases c hc with ⟨a, rfl⟩ | ⟨i, x, f, rfl⟩
  · simp only [simulate_pure, ProbComp.expect_pure]
    exact (ProbComp.expect_const _ _).symm
  · simp only [simulate_query, QueryImpl.withLog_apply, QueryImpl.ofComp_apply,
      ProbComp.expect_bind, ProbComp.expect_pure, simulate_pure]

end TCSlib.Cryptography.Authentication.HashSignFill

## ===== TCSlib/Cryptography/Authentication.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Defs
import TCSlib.Cryptography.Authentication.Signatures.Defs
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Authentication.MAC.Defs
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.FromPermutation
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM
import TCSlib.Cryptography.Authentication.MAC.FromPRF
import TCSlib.Cryptography.Authentication.Signatures.Lamport
import TCSlib.Cryptography.Hashing.FromDiscreteLog
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CodecReaders
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CollisionGame
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CollisionHandler
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.FixedGame
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.ForwardGame
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.ForwardHandler
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.OneQuery
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.OneQuerySampling

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Authentication: MACs and signatures

The authentication constructions and games of [PS10, Chapter 5]. The hashing interface and
discrete-log construction are indexed in `TCSlib.Cryptography.Hashing`.
The individual modules record deviations, proof sketches and outstanding admissions.

## Main definitions

See the definitions and construction modules listed below.

## Main results

See the theorem statements and correctness results in the constituent modules.

## Contents

* `Encoding` — shared encodings for the games and algorithms.
* `MAC.Defs` — the MAC interface and unforgeability game.
* `MAC.FromPRF` — the PRF-based MAC, correctness proof and security statement.
* `Signatures.Defs` — the signature interface and forgery games.
* `Signatures.Lamport` — the one-time signature construction from a strong one-way function.
* `Signatures.HashAndSign` — signatures for the hash family's full domain when the digest width fits.
* `Defs` — shared facade for the MAC, signature, and hash interfaces.
* `Hashing.FromDiscreteLog` — the discrete-log hash family used alongside these
  constructions.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., January 2010.
-/
