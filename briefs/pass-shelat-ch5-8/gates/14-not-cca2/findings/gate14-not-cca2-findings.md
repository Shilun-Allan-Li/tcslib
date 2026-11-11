# Pass–shelat Gate 14: not-CCA2 findings

**Verdict: CLEAR.** The gate can close at the audited head: zero blockers and zero majors.

External Codex audit of draft [PR #289](https://github.com/Shilun-Allan-Li/tcslib/pull/289), 11 November 2026. Counts: **0 blockers, 0 majors, 1 minor, 0 notes**. The minor is an acknowledged evidence-log defect, not a defect in the theorem.

| Input | Audited revision |
|---|---|
| Exchange | `35c6ffb76b0b6a679680396a7f7b86843a5eafda` |
| Lean head | `7960d6d4c3254797fdec191fff72c8d4c0147e1a` |
| Campaign records | `de2f7f0e890f0cdb972b4d5258c4e8f569cdcb1a` |
| Landing base | `fe757f17aa6bda2f711e69abe7e2470ce5872e04` |

## Findings

| # | Severity | File and declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G14-01 | minor | `outbox/gates/14-not-cca2-gate/landing/axioms.log:9`; `TCSlib.Cryptography.prfScheme_dec` | The landing axiom probe fails because it inserts an extra `Composability` namespace. Its log is not a successful complete probe run. | Lines 9–11 report an unknown constant, exit status 1, and no fresh olean. The correct declaration is `TCSlib.Cryptography.prfScheme_dec`, at `PrivateKey/FromPRF.lean:228`. The pack discloses the typo. The earlier correctly qualified census covers the reader, whose source is unchanged by the landing edits. | Regenerate the landing log using `#print axioms TCSlib.Cryptography.prfScheme_dec`, retaining a successful exit status. This is nonblocking; the independent head probe described below checks the correct name. |

## Integrity and scope

Read the exchange README and the gate README, pack, complete bundle, policy, both briefs, both worker reports, and maintainer review as material under audit.

- All **17/17** entries in `SHA256SUMS` pass; the manifest itself matches its pinned Git blob.
- All **11** bundle sections match the revision-qualified `BUNDLE-FILES.txt` in order and reproduce the indexed Git bytes, excluding only the bundle's framing newline.
- All **130** Lean files in `sources.zip` match the pinned head's Git blob hashes: the complete **129-module** target closure plus the private-key facade. The four changed-file SHA-256 values agree with `source-head.json`.
- The bundled PR diff reproduces the Git diff between the base and head. Only the four declared Lean files change.
- All **364/364** internal checksums in `verification.zip` pass. The supplied bootstrap, probe, and seal log bytes also match their JSONL log hashes.
- The source book matches SHA-256 `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`. Compared Algorithm 99.1, Definition 168.1 and §7.1.3 on book pages 99, 168–169 (PDF pages 111, 180–181).

| File | SHA-256 |
|---|---|
| `bundle.md` (139,875 bytes) | `d571c15512b3dae83e55715520b92d9232af7587a05f7efa8e6bccae266a46ac` |
| `sources.zip` | `8b12fdf96792f328f191ed52d511ff2795a7ca820d140d9c45e54b1fca45f0eb` |
| `verification.zip` | `27ba267b220c4b3cf842606b4e9d1fcf73ab4423b30fdddcfda4287365104439` |

The independent declaration comparison finds exactly **7 public additions**, with **0 existing public statements changed or removed**. Inspection of the full diff confirms the older declarations and CPA/CCA1 admissions are preserved. The facade change is documentation only.

## Proof audit

References below are line numbers at the audited Lean head, under `TCSlib/Cryptography/Encryption/PrivateKey/`.

1. **Uniform efficient adversary** — `OracleFromPRF.lean:207–263`. `cca2Next_poly` assembles the activation function from existing polynomial-time combinators. `cca2Adversary` is `NUPPT.ofPolyTimeUniform ... (.const 0)`; its activation equation ignores its coins. The log cases request Challenge on the all-false/all-true messages, request Dec on the altered challenge, then return the complement of the second answer's last bit.
2. **Budget and legality** — `OracleFromPRF.lean:447–521`. `cca2Run` proves the actual codec and simulation execution. The two query indices are 2 and 1; Enc (index 0) is never queried. Two applications of `buildComp_succ_of_query` leave budget zero, where `buildComp_zero_of_ret` still reads the third activation. Timeout is not used. `cca2Alter_ne` and `decOpen_cca2` establish that the decryption query is permitted.
3. **Ciphertext and decryption** — `OracleFromPRF.lean:295–433`. `cca2Encrypt` establishes the exact serialized ciphertext at width `3 * n + 2`. At positive message length, the final bit is in the masked payload, so `cca2Cipher` preserves the nonce and framing while changing the ciphertext. `cca2Decrypt` uses the published decryption readers and well-formed-input run theorem. `cca2FlipBits_unmask` proves XOR cancellation; `cca2LastBit` reads the flipped message bit after the validity prefix. Positivity is used for the nonempty payload and last-bit position.
4. **Probability and corollary** — `OracleFromPRF.lean:540–577`. The decryption hypothesis of `cca2Run` is discharged for every generated key and every encryption/decryption tape. Averaging constants gives acceptance 0 in the false-bit game and 1 in the true-bit game, hence advantage exactly 1. The unchanged corollary contradicts negligibility at a positive parameter. No PRF-security hypothesis or CPA/CCA1 admission is needed.

This is a complete attack proof in the stated model, consistent with the source's attack. The docstring explicitly explains the interpretation of the source's “plus one” as a fixed last-bit XOR modification.

## Readers, Rule 10, and landing edits

The seven additions are the authorized `prfScheme_dec` and six `FixedLengthScheme` readers: four width equalities plus `indImpl_dec_onSpec` and `indImpl_challenge_none_onSpec`. All are public, have docstrings stating their formulas, and introduce no simp attributes.

**The answer cast in `indImpl_dec_onSpec` is appropriate.** The concrete valid answer has type `Fin (n + 1) → Bool`, while the oracle returns `(S.indSpec n).rng 1`. The cast along `indSpec_decRng` makes that transport explicit. The challenge reader similarly transports its query and answer. The consumer removes explicit inverse double casts through `cast_cast`/`cast_eq`; `cca2OfFn_cast` uses a published width equality. This does not require unfolding the provider's length functions. Omitting the unused Enc and repeated-challenge readers follows the round-2 brief.

Verified that each supplied whole-file seal is the original source plus the recorded insertions, and inspected its installation, instance-unfolding mask, typeclass-lookup preservation, and EOF checks. The foreign-definition sets contain 1,754 / 678 / 1,842 requests for FromPRF / OracleSecurity / OracleFromPRF, including generated matchers and instances. The explicit-scan unresolved touched items are local hypotheses or the published `S.*` equation lemmas, not hidden foreign definitions.

The landing edits correct the two documentation passages, delete the unused `cca2Unmask`, and replace the duplicate padding lemma with the existing public `GGMRed.ofFn_padFin_of_length`. They change no statement or proof route. The independent seals below include those edits at the final source.

## Verification

Independent runtime: **Lean 4.25.0**, compiler commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`; **Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`**, with its pinned dependencies. Checks use a fresh olean tree and serial invocations of the repository's pinned `scripts/lean_check_tree.sh`.

| Independent check | Result |
|---|---|
| Fresh target closure | **129/129 modules pass**, zero errors, fresh oleans |
| Target module's admissions | Only the unchanged `prfFixedScheme_cpa` and `prfFixedScheme_cca1` warnings remain |
| Axiom probe | Both target theorems and all seven readers pass; each uses exactly `[propext, Classical.choice, Quot.sound]` |
| Final-source whole-file seals | **3/3 pass**, with 1,754 / 678 / 1,842 requests verified at installation and EOF; typeclass lookup preserved |
| Controls | **6/6 behave as specified**: all unsealed controls pass; all 14 designated negative tests fail once under seal; reader controls pass; zero unexpected errors |
| Style lint | **0 FAIL, 5 WARN over 10 files**, matching the supplied baseline warnings |

The final seals retain the inspected harness insertions around the exact final source, including the maintainer's padding-lemma replacement. Control diagnostics were checked against each declared source-line range, rather than accepting a nonzero exit status by itself.

The supplied broader evidence reports 238 closure modules, 4 modules rebuilt after the landing edits, and 18 downstream modules through `TCSlib` and `Checks`, all with exit status 0 and zero errors. I checked these records and the raw closure/probe/seal log hashes; I did not independently rebuild the complete broader tree. The source hashes of all 130 archived files agree with these build records, using the archived pre-edit versions where appropriate. The supplied admission census is 32 → 31 at the landing base; only the target admission disappears.

No commits, pushes, PR edits, or merges were performed. Dispatch and merge remain with the user.

**Notation:** `n` is the security parameter; `S` is a fixed-length encryption scheme. Both are the audited source's names.
