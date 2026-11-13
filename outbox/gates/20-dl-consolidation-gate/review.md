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
