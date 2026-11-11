# Pass–shelat Gate 15 — CPA pilot proofs

**Verdict: CLEAR for both pinned PR heads.** Zero blockers, zero majors; one minor documentation finding on #291. The gate's zero-blocker/zero-major condition is met.

| Scope | Blocker | Major | Minor | Note |
|---|---:|---:|---:|---:|
| PR #290 | 0 | 0 | 0 | 0 |
| PR #291, stacked on #290 | 0 | 0 | 1 | 0 |
| Combined | 0 | 0 | 1 | 0 |

This is an independent source and evidence audit. I verified committed Git bytes, inspected the proofs and verification harness, and reran the mechanical style lint and evidence-consistency checks. **I did not execute Lean:** this executor has no Lean/Lake toolchain. The compilation, sealing and axiom results below are verified archived evidence, not fresh compiler runs by this auditor. Nothing was pushed, dispatched or merged.

## Audited revisions and scope

Repository: [Shilun-Allan-Li/tcslib](https://github.com/Shilun-Allan-Li/tcslib).

| Input | Exact revision |
|---|---|
| Exchange pack | `c53e2baace2497ceca5814ffc8b1f57e9c04eaf8` |
| Campaign records | `315f781b6d7daf051c9f639fe6fba2e12839d4c2` |
| #290 base | `eedf7c1b13a244513c2c90e30bc2344291c077aa` |
| [PR #290](https://github.com/Shilun-Allan-Li/tcslib/pull/290) head | `95df0b4fa15e140ffd8f692699c66d0683fc916d` |
| #291 base | `95df0b4fa15e140ffd8f692699c66d0683fc916d` |
| [PR #291](https://github.com/Shilun-Allan-Li/tcslib/pull/291) head | `c286bc6a9b372036f959a033729d841ce10dfa16` |

Read the pinned `README.md`, `pack.md`, all 19 sections of `bundle.md`, policy, both issued briefs, worker reports, maintainer reviews and duplication ledger. Reviewed all nine changed Lean files, the unchanged `AdaptiveSecurity.lean` interface and relevant imported contracts. #290 changes five files; #291 changes four. The seven new helper modules and two filled theorem bodies stay within the issued ownership boundaries.

## Finding

| # | Severity | PR · file · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G15-01 | minor | #291 · `BitwiseCPA/QueryHandler.lean`: `qRun_eq`; `BitwiseCPA/Planted.lean`: `plantTuple_eq`, `plantAns_eq`, `plantOut_eq` | Four new public reader docstrings remain label-only and do not state the equation or behavior they assert. | At final head: `QueryHandler.lean:93`; `Planted.lean:124,224,259`. Each says only “The defining equation of” the named definition. This falls short of the pack's formula-docstring requirement and policy §2's requirement for an informative public statement. | Add a short behavioral statement/formula to each reader's docstring. The corresponding definition docstrings already describe the behavior; reuse that description without repeating the long projection expressions. |

Pinned evidence: [qRun_eq](https://github.com/Shilun-Allan-Li/tcslib/blob/c286bc6a9b372036f959a033729d841ce10dfa16/TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA/QueryHandler.lean#L93), [plantTuple_eq](https://github.com/Shilun-Allan-Li/tcslib/blob/c286bc6a9b372036f959a033729d841ce10dfa16/TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA/Planted.lean#L124), [plantAns_eq](https://github.com/Shilun-Allan-Li/tcslib/blob/c286bc6a9b372036f959a033729d841ce10dfa16/TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA/Planted.lean#L224), [plantOut_eq](https://github.com/Shilun-Allan-Li/tcslib/blob/c286bc6a9b372036f959a033729d841ce10dfa16/TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA/Planted.lean#L259).

The readers exist and have the correct equations. This finding concerns documentation, not their statements or proofs.

## Integrity and statement freeze

- **Outer checksums: 22/22 pass.** Checked every entry of `SHA256SUMS`, including both verification ZIPs and every landing log. All 23 pack files, including `SHA256SUMS` itself, also match the exchange commit's Git blobs.
- **Bundle: 19/19 ordered sections match.** Checked `BUNDLE-FILES.txt` against section order and compared each section with its revision-qualified committed bytes, allowing only the bundle's separator newlines. Its SHA-256 is `c602d0899f818b4a70a7b09b5833b7460bfe6864d95bf23474599f05396794e0`.
- **Sources: 161/161 archive files match Git.** Every source in `sources.zip` matches #291's pinned tree; all nine `source-head.json` hashes match. The five adaptive files are unchanged between #290 and #291.
- **Inner checksums: 357/357 and 380/380 pass.** These are the contents of `verification-290.zip` and `verification-291.zip` respectively. Archived module-log hashes match the corresponding recorded runs.
- **Diffs match Git.** Both supplied PR diffs reproduce the pinned base-to-head changes exactly using the recorded nine-character object abbreviations.
- **Frozen declarations are preserved.** Both target headers and both existing corollary headers are unchanged. The proof bodies of `bitwise_padded_adaptive_cpa` and `exists_adaptive_cpa` are byte-identical to their base versions. No older declaration outside the two target proof/sketch edits changes.
- **No new admissions or shortcuts.** The nine final files contain no proof admissions, new axioms, unsafe declarations, `native_decide`, unsafe reducibility overrides or global simp attributes. The archived admission census records #290's removal of `adaptive_cpa` and #291's removal of `bitwise_padded_cpa`, with no additions. Its 25/24 remaining admissions concern the checked closure, not these target proofs.

## Proof review

### #290 — `INDSecure.adaptive_cpa`

1. **Endpoints and codecs.** `castImpl_adaptiveIndImpl` uses the published adaptive/single-challenge equations. CPA decryption always refuses; fresh challenges encrypt the selected half and prepend one history entry; full-cap challenges repeat the latest ciphertext; empty history at cap zero gives the zero answer. `acHyb_lt_zero` and `acHyb_lt_cap` therefore identify the correct endpoints. Width transport preserves the actual query, answer and output strings.
2. **Efficient reduction.** `acHandler` has `perCall = 1`, `finCall = 0`, polynomial state/seed lengths, and a polynomial-time round function. It forwards only the advised fresh call; other fresh calls use distinct seed-tape slots. Its encryption equation uses `S.enc_uniform`. The advised index is nonuniform advice, permitted by the `NUPPT`/T2 contracts; its bound by `cap` keeps the encoded initial state within the stated length.
3. **Exact hybrid simulation.** `comp_acAbs` tracks the call count, latest ciphertext and forwarded ciphertext through the history abstraction. The forwarded call sees an unchallenged outer oracle. Every fresh call increments history length even if its ciphertext equals an earlier value. `simulate_tapeImpl_congr` proves that the continuation ignores already-used tape slots; the resampling argument in `expect_tapeImpl` consequently remains valid for adaptive queries. `accept_indGame_acHyb` then identifies the reduction's acceptance rate with the adjacent hybrid.
4. **Bound and edge cases.** The chosen hybrid gap is bounded by `cap(n)` times one fixed reduction's advantage. Security is applied at the polynomial outer budget `q·perCall + finCall`; `Negligible.polyExpr_mul cap` concludes. The cap-zero branch is explicit. There is no assumption that `n > 0`. Budget zero, decryption-only/no-challenge runs, an unreached forwarded call, repeated ciphertexts, full-cap repeats and timeout outputs are covered by the simulation equations.

No incomplete argument or changed proof route found.

### #291 — `SingleBitSecure.bitwise_padded_cpa`

1. **Endpoints.** `accept_indGame_eq` aligns the eager-coin bit hybrids with the padded CPA games through published padding, bitwise-encryption and coin-block readers. The public key is sampled before the adversary chooses its messages; no fixed-message ensemble-security assumption is substituted.
2. **Efficient distinguisher.** `exists_qHandlerMachine` applies T1 to the public query-recording handler. The first challenge is recorded and later challenges receive the same answer. `bwAux_length` proves the polynomial advice bound. `plantTuple_spec` places the supplied ciphertext at the advised block, uses right-message bits before it and left-message bits after it, and uses the correct coin offsets. The padding-length obligation is proved before applying the handler's machine equation.
3. **Signed identity.** `hyb_advantage_eq` proves equality of the adjacent hybrid advantage and the single-bit distinguishing advantage. Before the first challenge, the computation depends on the public key and adversary coins, not the supplied challenge ciphertext. Resampling the planted coin block gives the two adjacent hybrids. For selected bits `(0,1)` the output preserves the bit; for `(1,0)` it flips it; equal bits give zero. Without a challenge the distinguisher outputs zero and the hybrid difference is zero. Thus the identity is established before taking absolute values, avoiding a cancellation gap.
4. **Bound and corollaries.** The hybrid bound loses a factor of `n`, absorbed by `Negligible.polyExpr_mul .var` after `singleBitSecure_iff`. The `n = 0` branch identifies the identical endpoint hybrids directly. Budget zero, repeated challenges and timeout outputs are covered by the deterministic-run and machine equations. The unchanged corollaries then combine this proof with #290, including preservation of the key generator.

No incomplete argument or changed proof route found.

## Rule 10, builds and landing edits

**Rule 10 evidence.** Independently compared the nine original whole-file request sets with the collector's complete imported-definition catalog: no missing eligible definition. Helpers are foreign to each other. Verified the seal sources' hashes and insertion metadata; removing only harness insertions reconstructs the exact audited source bytes. The harness checks actual name components, home modules, definition/instance metadata, installed irreducibility and end-of-file persistence, while preserving typeclass lookup state. Abbreviation/notation exclusions match the recorded policy.

| Archived check | #290 | #291 |
|---|---|---|
| Original whole-file seals | 5 pass; 685–2,174 requests | 4 pass; 2,021–2,185 requests |
| Base control | Pass | Pass |
| Paired control probes | 10 | 8 |
| Negative controls, unsealed pass / sealed fail | 55/55 | 60/60 |
| Reader-positive controls under sealing | 50/50 | 56/56 |
| Explicit-reader scan | 627 items; zero foreign-definition reads reported | 412 items; zero foreign-definition reads reported |
| Distinct modules in recorded fresh build | 201, zero errors | 204, zero errors |
| Final affected-module rebuild | 8, zero errors | 6, zero errors |
| Final downstream/root checks | 22, zero errors | 7, zero errors |

I independently recomputed the control outcomes from error locations and checked for stray errors, installation records and end-of-file records. The sealed-control failures are expected negative results. Checked unresolved scan heads and the new/edited explicit readers against the source; no forbidden new read found.

**Landing edits.** Fetched both landing-parent commits, `12367474570e5ec54f598915fa6de6264354807d` and `e2002c5cb9aa47e555364642db7b1b32e959c45e`. Every archived before/after file matches its actual parent/final Git version. #290's removed private pairing lemma is replaced by the published theorem in the reverse orientation; the other edits change documentation or remove an unused simp argument. #291 removes the two parallel-fill duplicates and consumes #290's readers; the three `convert` replacements use pointwise `PolyTimeComputable.congr`. These preserve statements and the mathematical proof route. #291's four edited files also have archived whole-file reseals. Final rebuild/root-record source hashes match the pinned heads.

**Axioms.** Checked all 175 and 97 stored-constant rows in the respective pre-landing censuses: only `propext`, `Classical.choice`, `Quot.sound` occur. These counts describe those pre-edit trees. At #291's final head, `landing-291/axioms-head.log` prints exactly those three axioms for both targets and both corollaries, including `exists_adaptive_cpa`; no `sorryAx` appears.

**Style/API and duplication.** Independently reran `campaign_style_lint.py ... --check8b` on the base and both final heads: zero failures and the same six pre-existing warnings in each case. Every changed file is below 1,000 lines; the largest is 596. New definitions have equation/case/field/run readers, and both facades list their helper modules. G15-01 is the remaining formula-docstring defect. Reviewed DL-30–DL-33 and the removed duplicates; no additional undisclosed copy found, and no objection to the pack's recorded consolidation deferral.

Evidence directory: [pinned Gate 15 pack](https://github.com/Shilun-Allan-Li/tcslib/tree/c53e2baace2497ceca5814ffc8b1f57e9c04eaf8/outbox/gates/15-cpa-pilot-proofs-gate). This verdict applies to the exact heads above; the user dispatches and merges.
