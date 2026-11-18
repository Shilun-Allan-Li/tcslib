# Gate 53 · the GSW 6b fills gate for U12 and U13: PR #392 · round 1

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews). This is **Gate 53**,
the fills gate for two of the five GSW phase-6b fill units: the proofs of nine 6b targets that #377 stated and Gate 46
cleared (CLEAR in round 1, closed by LE-g46b). One open draft PR is audited.

- **PR #392** ([link](https://github.com/Shilun-Allan-Li/tcslib/pull/392)), branch `land/gsw-6b-u12-u13`, head
  **`4b2ede271e1af88ad2eee207dafd9b674f19a306`** (tree `86526169369d6b3ea2dcd70240f94b1a71c7ed84`, `TCSlib` tree
  **`745bf4b494b6581a5666ef9ca0a6e735a68ddcef`**), base `cryptography/pass-shelat-ch2-4`. Its REST `base.sha` and its
  merge base with the records tip are both `fb56166b6454b18d73d697b84d8eb71f8247251c`. Three SSH-signed commits; 2 files,
  +157/−20.
- **B6** = `bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d`, the #377 merge and olean snapshot #11's T (`TCSlib` tree
  `949dfd63c2539e1ccd738ab96ec424ee6cb17798`). The merge base `fb56166b`, the records tip at staging
  `96b743bfd8566f40cd8a06c29f31d760ecc29bb6` and the pin are records-only on top of B6: their `TCSlib`, `TCSlib.lean`,
  `audits/`, `lean-toolchain` and `lake-manifest.json` equal B6's (`staging-checks-r1.txt` §2). **The frozen statements
  are B6's.**
- **Records pin:** the commit that files this directory, `briefs/lattice-gsw/gates/53-gsw-6b-u12-u13-fills/`.
  `dispatch-r1.md` and the prompt name it. Its parent is the records tip at staging (`96b743bf`, "Records: U12/U13
  rulings; landing PR #392"), and it adds this directory and, at most, decision-log rows, so every record this pack
  cites reads the same at `96b743bf` and at the pin (`source-head-r1.json` `records_sha256_at_staging_tip`).
- **Mathlib** `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, **Batteries** `39260e31b7b3f7f05643da95242463b462dc05f1`
  (`lake-manifest.json` at the head), toolchain `leanprover/lean4:v4.25.0`.

Paths below are under `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/` unless they start with `TCSlib/` or
`briefs/`. `ISSUED/` is `briefs/lattice-gsw/phase6/issued-6b-fills-r1/`. Line numbers are at the head.

## How this gate runs (standing rules 17 and 18)

- **Cloud, reading only.** Every input is in the repository: the records branch at the pin, the PR branch, and the
  exchange branch at the delivery commit. Nothing is needed from Seyoon's machine.
- **No Lean replay, no cache.** The auditor does not run `lean`, `lake` or `lake exe cache get`, and builds nothing.
  The maintainer replayed in house on a copy of snapshot #11 (U12/U13 `final-r1/phase2.md`), and that replay is the
  gate's build evidence. The audit grades it by reading: the evidence ZIP, its logs and its probe sources.
- Python as `python3 -I`; `git`, `sha256sum`, `unzip` and reading tools only. Mathlib/Batteries source may be read at
  the pinned revisions (GitHub, or a blob-filtered fetch), never built.

## Scope

| Unit | File | Targets | Commits on the PR | What changes |
|---|---|---|---|---|
| **U12** `gsw-6b-u12` | `Branching.lean` | G1 `Encrypts.select` (`:121`), G2 `encrypts_homEvalPBP` (`:177`), G3 `encrypts_homEvalFormula` (`:242`) | `bd9d1ed3244e97334b6732ca913a64a061be4ee3`, `55d2afb19532348f5e7318cd77b44a3c61bee8cf` | 3 proof bodies; one **private** glue lemma `encrypts_select_ite` (`:147`, 13 lines with docstring; the brief allows private helpers); the three `**Proof sketch.**` paragraphs refreshed; the module's admission sentence; +102/−13, 179 → 268 lines |
| **U13** `gsw-6b-u13` | `DecryptFormula.lean` | G5 `vecMul_secretVector_eq_sum` (`:143`), G6 `decryptFormula_eval` (`:170`), G7 `nandFormula_eval` (`:200`), G8 `depth_nandFormula_le` (`:213`), `maxFanin_nandFormula_le` (`:231`), `decDepth_le` (`:251`) | `4b2ede271e1af88ad2eee207dafd9b674f19a306` | 6 proof bodies; no helper; no sketch changed; the module's admission sentence; +55/−7, 216 → 264 lines |

- **The commits are the worker's patches.** The maintainer applied the delivered patches with `git am -3` on `fb56166b`
  and signed them; `git patch-id --stable` of each PR commit equals that of its delivered patch (3/3), and both files
  at the head are blob-identical to the delivered `src/` and to the review evidence's `frozen/*.head.lean`
  (`staging-checks-r1.txt` §4–§5). The worker's own commits (`f0a51d1e`, `afdaa9e2`; `74fb355a`) are unsigned and on no
  ref; they exist only as the patches and as the review's reproductions.
- **Deliveries** (exchange `exchange/pass-shelat-ch5-8`): U12 at `9b4ab065f58581ac93ba6641f29a0d4051482dfa`
  (`inbox/fills/gsw-6b-u12/`, checkpoint `f190df177e9e3f78d491abf81e8ac27b5fa0af56`); U13 at
  `87012e786e70134018a22156d3a299c2c55b943a` (`inbox/fills/gsw-6b-u13/`, checkpoint
  `ab9d1ec3a01ea2fabe97efe92ad2fcb0866bc1bf`); `9b4ab065` contains both. Each has `REPORT.md`, `SHA256SUMS`,
  `patches/` with `COMMITS.tsv`, `src/` and `evidence/`.
- **Issued pack:** `ISSUED/` at its pin `bbc930b3853adb29ba96324568e984d521abd257` (`README.md`, `COMMON.md`,
  `U12/brief.md`, `U13/brief.md`, the dispatch prompts, `dup-sweep.md` §0/§U12/§U13, `targets.txt`, `base-sorries.txt`).
  Since that pin only the U12/U13 dispatch prompts changed (the pin hash filled in).

**Out of scope** (mention only if something in scope depends on it):
- The 6b **statements** (#377, Gate 46 CLEAR, merged at B6): their fidelity to the sources is settled. They are the
  **base** of question B, not an audit item.
- The other 6b units (U14-U16, U15-U17, U18-U19), EF-R1, and the open questions Q-6BF-1..7 of `ISSUED/README.md`.
- Rule 15 beyond this PR: the fills prove correctness and noise bounds; no target is an efficiency claim (COMMON §6).
  Check only that the PR adds no hypothesis and no helper whose hypothesis is an efficiency claim. G46-03 and the
  lattice remediation plan (`briefs/efficiency-gaps/`) are known and tracked there.
- The merge conditions: the snapshot #12 adoption (a replay of whatever merges) and the merge itself.

## Rulings and records in force

1. **Q-U12-1 / Q-U13-1 (A), Seyoon, 2026-11-18** (decision log `LatticeCryptographyPlan.md`, row "U12/U13 rulings
   (Seyoon) and landing"): the issued pack's `rulings.md` was never filed (review findings **U12-F01/U13-F01**). It is
   **ruled: no ruling applied to these units**; the deliveries are accepted as they are; `ISSUED/rulings.md` is filed,
   with the Q-6BF-1..7 answers, before any further 6b dispatch. Do not raise the missing file as a finding against
   #392; grade U12-F01/U13-F01 as records-side items.
2. **Q-6B-F2** (decision log, "6b statements rulings (Seyoon), all as recommended"; question text in
   `briefs/lattice-gsw/phase6/final-6b-r1/review.md`, *Q-6B-F2*): "`decDepth_le` stays an admitted target". Its
   recommended option said "The U13 fill proves it from F10". **F2 is discharged as planned**: it kept `decDepth_le`
   admitted in statement PR #377 only, so that this fill would prove it. Gate 46 judged the statement a valid
   weakening of F10 (`gates/46-gsw-6b/findings-r1.md`); G6B-F05 and Gate 46 `dup-sweep.md` N1 disclose the
   specialization. U13's review (*`decDepth_le` and ruling Q-6B-F2*, U13-F02) gives the reading.
3. **Q-U12-3 (A)**: `IsFiveCycle.apply_ne` (`TCSlib/Complexity/BranchingPrograms/Barrington.lean:384`) **stays
   private**; G3 proves `sigma1 0 ≠ 0` by the reader `sigma1_eq` and kernel `decide` on `Fin 5` instead of copying it.
4. **Q-C1** (`briefs/lattice-gsw/phase6/checkpoint1-6b-review.md`, G6B-C1-F03): G6 must use the owner-side
   `decrypt_eq_decode_dotProduct` (`Scheme.lean:162`, from #368, Gate 50), not re-derive it.
5. **Phase-6 rulings** `briefs/lattice-gsw/phase6/rulings.md` and plan section r3
   `briefs/lattice-gsw/phase6/plan-section.md` (G1–G8, §H3.3: no term linear in `ℓ`).
6. **Fill rules:** `ISSUED/COMMON.md` §4 (what a fill may change; the frozen regions), §5 (Rule 10, duplication, hosts
   first, attribution, form), §6 (Rule 15); the unit briefs' targets, routes, must-reuse lists and unit checks.
7. **Duplication** (policy §1; precedents G44-01, G48-01, G45-01, GF-F01, S1/DL-61): disclosure is not acceptance; an
   undisclosed or unaccepted re-proof of a public TCSlib or Mathlib lemma, including an inline re-derivation, is a
   **major**.
8. **Rule 10** (policy §1, COMMON §5.1): other files' definitions are read only through published readers and lemmas;
   core/Mathlib definitions may reduce in `rfl`/`decide`/`show` steps; canonical coe-A seals are the check.
9. **Policy** (`policy.md`): attribution (tags or "Glue."), formula docstrings, a `**Proof sketch.**` for every proof of
   about 20 lines or more, width ≤ 100, files 150–600 target and < 1,000.
10. **Standing rules** `briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` §2 (3, 5, 15, 17, 18).

## Questions for the audit

**A. Correctness of the proofs (nine targets and the glue).** Read each proof against its frozen statement. Does it
establish the statement as stated, for every parameter (no special case through an instance or a `decide` that does
not cover the statement)? Is the private glue true as stated and used as its docstring says?
- **G1** (U12-F02): `mul_bit` on the product whose left operand encrypts `1`, `Encrypts.mul` on the one whose left
  operand encrypts `0` (`|0|·βV = 0`), so the sum is `2·(N·β) + βV`. Is the frozen bound `βV + 2·(N·β)` reached in both
  cases, and is the message `(1 − b)·u + b·v`? (`Encrypts.mul` `Noise.lean:216`, `Encrypts.mul_bit` `Noise.lean:247`.)
- **G2**: the relation `R τ` handed to the host `BranchingProgram.evalWith_rel` (`Eval.lean:157`); step 0 by
  `Pi.single`; the step by `Instr.stepWith_of_isPermutation` (`Eval.lean:127`) after `hι` (the two readers
  `isPermutation_iff` `Defs.lean:323` and `Instr.isPermutation_iff` `Defs.lean:104`); the end by `evalWith_single`
  (`Eval.lean:211`) and `hm`. Does `R` carry the right noise (`τ·(2·(N·β))`) and are the instantiated host arguments the
  ones the statement's `homEvalPBP` uses?
- **G3**: G2 for `barrington c sigma1` at `s₀ = 0`, `i = sigma1 0`; `barrington_yield_zero` with `hc` and
  `isFiveCycle_sigma1`; `sigma1 0 ≠ 0` by `sigma1_eq` and `decide`; the noise by `barrington_length_le`.
- **G5**: `t = G·x` by `keyBits_eq` and `gadget_mulVec_decomposeVec`, then `Matrix.dotProduct_mulVec` and
  `decConstants_eq`, closed by `rfl` (Mathlib's `dotProduct` is the stated `∑`).
- **G6**: `decrypt_eq_decode_dotProduct` (Q-C1); `hval` (G5, `Nat.cast_sum`, `Nat.cast_mul`, `ZMod.natCast_zmod_val`,
  `ZMod.val_natCast`); `hlh`/`hhq` (`decodeLo ≤ decodeHi ≤ q` from `decodeLo_eq`/`decodeHi_eq` and `modulus_ge_two`);
  `FormulaArith.modSumInterval_eval` with `ZMod.val_lt`; `decode_iff_mem_Ico` (O2, `TCSlib/Cryptography/LWE/
  BitEncoding.lean:151`).
- **G7, G8**: the readers and F1/F3/F9/F10 bounds; `decDepth_le` by `Nat.clog_le_iff_le_pow`, `Nat.clog_mono_right`,
  `FormulaArith.modSumDepth_le` (`TCSlib/Complexity/CircuitComplexity/FormulaArith/ModSum.lean:365`) and `omega`.
- Axioms (maintainer evidence, not re-run): every target `[propext, Classical.choice, Quot.sound]`, 13 stored constants
  in `Branching` and 23 in `DecryptFormula`, 0 `sorryAx`, a `sorry` control flagged. Is the census consistent with the
  proofs you read (e.g. the `_proof_` auxiliaries)?

**B. Frozen-statement fidelity.** Against B6 (`git show bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d:<path>`):
- Is every target header (keyword through `:= by`) and its statement prose before `**Proof sketch.**` byte-identical?
  Is every definition, reader, the instance `Parameters.neZero_columns`, every `import`, `set_option`, namespace and
  `variable` line unchanged? The staging classified every removed line (`staging-checks-r1.txt` §6): 9 `sorry` bodies,
  2 module admission sentences, and 9 lines of the G1/G2/G3 sketch paragraphs; the review's normalization reproduced
  B6 byte for byte with controls (evidence `frozen/`).
- Are the refreshed U12 sketches accurate descriptions of the delivered proofs, and are U13's unchanged sketches
  still accurate (the review says "no sketch refreshed" is right)?
- Are the two new module sentences ("All three are proved here; …", "All are proved, as are the definitions and the
  instance.") true at the head, and are they the permitted admission-sentence edits of COMMON §4?
- Is the one new declaration private, placed before its first use, and not `@[simp]`? (decls2: 0 ADDED / 0 CHANGED /
  0 REMOVED; a control making the glue public gives 1 ADDED.)

**C. Scope and integrity.** Does the PR change exactly the two owned files and nothing else (no 6a, phase-5, LWE,
facade, `blueprint/` or `audits/` file)? Do the three PR commits equal the delivered patches and the head files the
delivered `src/` (`staging-checks-r1.txt` §3–§5)? Is the PR's `TCSlib` tree the reviewed stack's (`745bf4b4`), and is
the merge with the records tip Lean-equal to it?

**D. The rulings.** Is the proof of `decDepth_le` consistent with Q-6B-F2 as recorded (item 2 above), with its header
byte-identical to B6? Does G6 use `decrypt_eq_decode_dotProduct` rather than re-derive it (Q-C1)? Does G3 avoid copying
the private `IsFiveCycle.apply_ne` (Q-U12-3 A), and is kernel `decide` on `Fin 5` after `sigma1_eq` an acceptable
route? Does any choice of either worker depend on an unrecorded Q-6BF ruling?

**E. Duplication** (binding; question 7 of the rulings above).
- `ISSUED/dup-sweep.md` §U12 and §U13 must-reuse lists: is every item used, or is the review's reason for not using it
  right (U12: `mul_eq`, `encrypts_iff`, the family `isPermutation_iff` `Defs.lean:450`, `isFiveCycle_iff`; U13:
  `secretVector_eq`, `vecMul_secretVector_augmented`)?
- The private glue `encrypts_select_ite`: a disclosed in-file specialization of G1 used only by G2. Is it a restatement
  of any public lemma?
- The inline facts the reviews probed with `exact?` and found nothing for (evidence `probe-src/DupProbe.lean`,
  `runs/dup/`): **D1** G2's `hm` (`Pi.single … i` as `(decide _).toNat`), **D2** G2's `hι` (an instruction of a
  permutation program is a permutation instruction), **D3** G6's `hval` (the `ZMod` subset-sum representative), **D4**
  G6's `hlh`/`hhq`. Is any of them, or any other inline step, a public TCSlib, Batteries or Mathlib lemma at the pinned
  revisions (search by name and by statement shape)?
- `sigma1 0 ≠ 0` against the private `IsFiveCycle.apply_ne`; `decDepth_le` against F10 (`modSumDepth_le`, cited).
- Anything the issued sweep and the reviews missed.

**F. Policy and form** (`policy.md` §1–§3, COMMON §5.4–5.5). Every proof of about 20 lines or more has a sketch, with
step comments at its major `have`s (G2's body is 42 lines, G6's 20, G3's 19); the glue has a formula docstring and
"Glue."; no new or changed source tag or anchor (the targets' citations are B6's); width ≤ 100, no micro sign, sizes
268 and 264 lines (`staging-checks-r1.txt` §7).

**G. Rule 10.** Does any proof read a foreign TCSlib definition other than through a published reader? Read every name
passed to `rw`/`simp`/`simpa`, and every `rfl`/`decide`/`show` step (G2's `hm` closes by `rfl` on `Bool.toNat` casts;
G3's `decide` runs on `List.formPerm` over `Fin 5` after `sigma1_eq`; G5 closes by `rfl` on Mathlib's `dotProduct`).
Then grade the maintainer's seal evidence (phase 2 § P2-5 of each unit): canonical coe-A and seal B over the whole
closure, 0 errors (U12: 200 requests, 10 excluded abbreviations; U13: 380, 6 excluded); 2 liveness pairs per unit
(`evalWith`, `GSW.mul`; `GSW.decrypt`, `decodeLo`), ALL_OK; the explicit-unfold scan, 0 TCSlib definitions. Is that
sufficient, and is anything sealed or excluded that should not be?

**H. The evidence binding** (§ *Evidence binding*). Does each piece bind to the PR's code? Is anything necessary
missing or unverifiable? A missing or non-binding piece of necessary evidence is a **major**.

**I. Is anything undisclosed?** Among the commits, the PR description, the two reviews, the workers' `REPORT.md`s and
the records, is any change, claim or omission undisclosed? The known slips are below. Grade the review findings
**U12-F01..F04** and **U13-F01..F03** in a separate table (agree, or regrade with the reason).

## Evidence binding

| Evidence | Bound to | What it shows | Reaches the PR head by |
|---|---|---|---|
| Deliveries `inbox/fills/gsw-6b-u12/`, `gsw-6b-u13/` (exchange `9b4ab065`, `87012e78`) | worker heads `afdaa9e2f29604052537652bf01165e61c52fb32`, `74fb355a17a47076d7de44a0f691ea03572cb170` on B6 | the patches, `src/`, the workers' evidence (seals, axioms, controls, census) and `REPORT.md` | patch-id 3/3 equal; head blobs = delivered `src/` |
| U12 `review.md`, U13 `review.md` (phase 1, static) | `afdaa9e2`, `74fb355a` reproduced by `git am` on B6 | integrity, reproduction, scope, decls2 0/0/0, exact header comparison, frozen-region normalization with controls, admissions, duplication (must-reuse, D1–D4), hygiene, lint, clashes | the same patches |
| U12/U13 `phase2.md`, `gsw-6b-u12-u13-final-r1-evidence.zip` (`5a220db3c56024d4de5f760e75aeb5b741d2b670c2398a2a3e273dbb69b97202`, one ZIP filed in both folders; `evidence-SHA256SUMS`) | stack check head `51d46089e37030f582b24c1f84ee68ac21c98829` (scratch, on no ref; tree `fb6884d14882417682957ee056aab4bf6376652c` = `merge-tree afdaa9e2 74fb355a`), records tip `31247fe71e7ab60a1d7f8f1939291147e1b5645a` (Lean = B6), snapshot #11 | stack 12/12 rc 0 incl. root `TCSlib`, state 1,456 OK; each unit alone 11/11; admissions 33 in 14 (39 and 36 alone); axioms; coe-A/seal B; liveness pairs; unfold scan; `exact?` probes D1–D4; lint; snapshot rehash 0/0/0 | `51d46089`'s `TCSlib` tree is `745bf4b4`, the PR head's; `frozen/*.head.lean` are blob-equal to the head files and `frozen/*.base.lean` to B6's (`staging-checks-r1.txt` §2, §5) |
| This pack's `staging-checks-r1.txt`, `source-head-r1.json` | the PR head and the records tip at staging | pins, Lean equality, scope, patch-ids, blobs, removed-line classes, file statistics, the evidence ZIP's manifests | git objects only |

The evidence ZIP's inner `SHA256SUMS` lists 230 files, all verify; it does not list itself (§8). `51d46089` cannot be
fetched (it is on no ref); its binding is through the `TCSlib` tree and the blobs, which the auditor can check from the
PR head and the ZIP.

## Known dispositions and slips (not findings)

- **Review findings:** U12-F01/U13-F01 (minor, records side: `rulings.md` never filed; **ruled**, item 1 above),
  U12-F02 (info: `ISSUED/dup-sweep.md` §U12's G1 hint would overshoot the bound; the issued pack stays as pinned and the
  review carries the correction), U12-F03 (info: `sigma1 0 ≠ 0` by kernel `decide`; promotion declined, Q-U12-3 A),
  U12-F04 (info: worker host housekeeping), U13-F02 (info: `decDepth_le` proved, F2 as planned), U13-F03 (info: the
  worker briefly ran 5 Lean processes on its own host, disclosed; host housekeeping). **Grade them.**
- **Q-U12-2** (accept G1's route as delivered; do not edit the pinned sweep) has **no recorded answer** in the decision
  log: the row "U12/U13 rulings (Seyoon) and landing" records Q-U12-1/Q-U13-1 and Q-U12-3 only. The landing took the
  delivery as is, which is option A.
- **Decision-log wording:** the row "GSW 6b U12 and U13 finals delivered" says `decDepth_le` is the target "which
  Gate 46 F2 had left admitted"; U13-F02 records the reading (no deviation).
- **Hashes in the reviews:** "B6 … tree `845bdc98…`" is B6's root tree; the Lean (`TCSlib`) tree is `949dfd63`. The
  reviews read the records tip `31247fe7` (Lean = B6); the PR sits on `fb56166b` (Lean = B6).
- **Evidence nit:** U12's review says the ZIP's inner `SHA256SUMS` covers "271 files"; the ZIP has 272 entries, of which
  41 are directory entries, and `SHA256SUMS` has 230 rows (all verify) plus itself unlisted.
- **PR description:** "4 paired controls ALL_OK" is the two units' 2 + 2 liveness pairs; "200 / 380 requests" are
  U12's and U13's seal closures.
- **Commits and signatures:** `git am -3` kept the worker's author and committer data, so the U13 commit `4b2ede27`
  carries a committer date (21:51:48Z) earlier than its parent's (22:10:29Z). The three PR commits carry SSH signatures
  of the account's shared Claude key (BS-F08); no signature was cryptographically verified (no allowed-signers file).
  The worker's commits are unsigned (`COMMITS.tsv`).
- **Authorship:** the proofs are two external Claude workers'; the landing (application and signing) is the
  maintainer's. There is no landing edit.
- **Not re-run:** the maintainer did not re-run anything after landing; the PR's `TCSlib` tree equals the replayed one,
  so no re-run is needed for the binding.
- **No Lean, no `lake`** was run for this staging. `staging-checks-r1.txt` is git objects and `python3 -I` only.

## Merge interaction (maintainer merge conditions, not audit items)

- #392 × the records tip at staging: `merge-tree` clean, `TCSlib` tree `745bf4b4` (= the reviewed stack).
- **Adoption:** snapshot #12 from a fresh replay of the merge (about 12 modules; the review's replay trees were deleted).
- No other open PR touches the two files.

## Files of this directory

- **`pack-r1.md`** (this file) and **`dispatch-r1.md`** (the Codex prompt; postdates the pin; not in `SHA256SUMS-r1`).
- **`pr392.diff.txt`**: `git diff origin/cryptography/pass-shelat-ch2-4...4b2ede271e1af88ad2eee207dafd9b674f19a306`
  (= `git diff bff0567b 4b2ede27 -- TCSlib TCSlib.lean`, byte for byte).
- **`pr392-u12.diff.txt`** (`fb56166b..55d2afb1`, U12's two commits) and **`pr392-u13.diff.txt`** (`55d2afb1..4b2ede27`).
- **`pr392-description.md`**: the PR body at staging (REST `.body`, raw).
- **`source-head-r1.json`**: pins, Lean equality, the three commits (parents, trees, author, committer, signature
  kind, files, patch-ids against the delivered patches), the deliveries, both files' SHA-256, blob, lines, width,
  over-width, tabs, trailing spaces, `sorry` and micro-sign counts at B6 and at the head, the review files' SHA-256,
  and the SHA-256 of every record this pack cites at the records tip.
- **`staging-checks-r1.txt`**: the staging's checks, §1–§9.
- **`SHA256SUMS-r1`**: the files above other than `dispatch-r1.md`.

## Findings delivery

Return **`findings-r1.md`** as Markdown in the Codex chat. If you have evidence files (search logs, scripts), return a
ZIP with `findings-r1.md` at its root. Push nothing, write nothing to the repository, open no PR. The user dispatches
and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

Number the findings **G53-01, G53-02, …**. Grade U12-F01..F04 and U13-F01..F03 in a separate table. Report the audited
head, the records pin, the evidence ZIP's SHA-256 as you computed it, the searches you ran (with hit counts), the counts
by severity, and a verdict for **PR #392**:
- **CLEAR:** zero blockers and zero majors.
- **HOLD:** otherwise.

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish its frozen statement, or a scope
  violation (a change outside the two owned files or outside COMMON §4's permitted regions).
- **major:** any of the following:
  - a changed frozen header, statement prose, definition, reader, instance or `set_option`;
  - a forbidden read (Rule 10) not covered by the rulings;
  - an undisclosed copied private lemma, or an undisclosed (or unaccepted) re-proof of a public one, including an
    inline re-derivation of a TCSlib, Batteries or Mathlib lemma;
  - a fabricated source tag;
  - necessary evidence that cannot be verified or does not bind to the PR head.
- **minor:** documentation or API defects, including an inaccurate formula docstring, glue note, proof sketch, module
  sentence, review statement or PR description.
- **note:** anything else.
