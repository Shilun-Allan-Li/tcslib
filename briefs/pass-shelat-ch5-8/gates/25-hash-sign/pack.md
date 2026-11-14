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
