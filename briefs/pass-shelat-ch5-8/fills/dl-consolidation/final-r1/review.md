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
