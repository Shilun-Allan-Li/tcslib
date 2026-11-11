# Pass–shelat Gate 13: padded CPA proof audit

**Verdict: CLEAR.** No blockers, majors, minors, or new notes. The gate's closing threshold is met for the pinned head.

| Severity | Count |
|---|---:|
| Blocker | 0 |
| Major | 0 |
| Minor | 0 |
| Note | 0 |

This is an independent source and evidence audit. I verified the committed inputs, inspected the proof and landing changes, and checked the supplied build, axiom, seal, and control records against their source bytes. **I did not execute Lean locally:** no Lean toolchain or compiled dependencies were available in this audit environment. Compilation and elaborated-axiom results below are verified supplied evidence, not a new auditor build.

## Audited revisions and scope

Repository: [Shilun-Allan-Li/tcslib](https://github.com/Shilun-Allan-Li/tcslib), draft [PR #288](https://github.com/Shilun-Allan-Li/tcslib/pull/288).

| Input | Exact revision |
|---|---|
| Exchange | `35ea3015a726096b19e1852b58114991ba332be9` |
| Lean head | `892a3f3c78abcde8bdf822a3b4168ab3302b4272` |
| Campaign records | `f6b8de11291e56858eeb76990d53469cacc3f852` |
| Frozen PR base | `2950c4a74c45b98185a5eaf4601cf8b88a7528c2` |
| Parent before landing edits | `c13e0764e566d443b9c4ad498702cc6fb1c4ad7a` |

The audited changes are exactly these three files under `TCSlib/Cryptography/Encryption/PublicKey/`:

- `OracleSecurity.lean`, principally `expect_simulate_indImpl_cpa`, `padded_cpa_advantage_eq`, and `BitPublicKeyScheme.SingleBitSecure.padded_cpa`.
- `OracleSecurity/ChallengeSim.lean`.
- `OracleSecurity/RecordHandler.lean`.

I also inspected the relevant T1 contract in `Games/Efficiency.lean`, the single-bit security readers in `PublicKey/EnsembleSecurity.lean`, and the cited source. `Pass–Shelat.pdf` has SHA-256 `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`; Definition 171.5 and its following claim are on book pp. 171–172, PDF pp. 183–184. The padding and oracle encoding conventions are already explicit in the frozen formalization.

## Integrity and statement freeze

All checks below passed independently against fetched Git objects, rather than trusting the bundle's descriptions.

| Check | Result |
|---|---|
| Exchange `SHA256SUMS` | 17/17 files match |
| Ordered `BUNDLE-FILES.txt` | 10/10 sections, in order, match the exact Git blobs at their indexed revisions |
| `sources.zip` | All 151 Lean files match the pinned head's Git blob IDs |
| `source-head.json` | All three changed-file SHA-256 values match |
| `verification.zip` inner manifest | 351/351 files match |
| Pack's `pr.diff.txt` | Byte-identical to the frozen base-to-head Git diff with nine-character object abbreviations |
| Frozen theorem header | Byte-for-byte identical to the base |
| All earlier declarations in `OracleSecurity.lean` | Code unchanged; only imports and module documentation change before the new section |
| New public declarations | 41, in the two helper modules; six additional private helpers in the owner |

The bundle is 210,102 bytes; its SHA-256 is `5eec54c8946a62f9fa80e38301c3442919e5e8cf091e76756c85c431e9cebe44`. The inner verification manifest has SHA-256 `85eabe28931c472bc8a18cccebf825abd2c48c4d6f3eae1f2ce0848bd25d1b2c`.

## Proof review

**1. Eager coins.** `expect_simulate_indImpl_cpa` proves the expectation identity for every output function and every initial challenge state. Its induction handles returns, unavailable decryption, and repeated challenges directly. At a first challenge, it samples the challenge coins and applies the induction hypothesis to the continuation. That introduces another average, but `chRun_some_congr` makes the recorded-state continuation independent of those extra coins; `expect_const` removes that average. Returns and runs that never challenge also marginalize the unused coins. No independence of an adaptively chosen message from the public key is assumed.

**2. First challenge.** `firstQ` follows decryption queries using the fixed all-false answer and stops at the first challenge query. It does not take an answer function. `chRun_congr` therefore has the required hypothesis: agreement only at that query. Once the first answer is recorded, `chRun_some_congr` covers the entire continuation, including repeated challenges with different requested messages. `length_of_firstQ_eq_some` supplies the two-bit length needed for the final case split.

**3. Recording handler and T1.** The lengths are correct: query widths `[L(n), 2]`, answer widths `[2, L(n)]`, and a one-bit final output. `hins` and `houts` establish their equality to the padded scheme's lengths. `chRun_toCompOn_transport` transports both the output list and the first query by substitution, without assuming the codecs are definitionally identical.

The handler's three state bits are initially `000`; the first challenge records `[true, m₀, m₁]`. Decryption returns `00`. Every challenge returns the same context-derived padded ciphertext. `simulate_recHandler_recorded` and `simulate_recHandler_init` prove these behaviors through `PolyHandler.answer_of_run_eq`, with the answer and state lengths checked before decoding. The polynomial-time obligations use the published closure combinators.

T1 supplies one distinguisher machine, with a coin equivalence at each parameter that works for every reduction input. The proof correctly transports the encryptor's coins using `NUPPT.coinsCongr (padEnc_coins …)`, reindexes the distinguisher's coins through T1's equivalence, and removes the unique empty seed. No probability factor is lost.

**4. Exact advantage identity.** For fixed key-generation and adversary coins, let `p₀` and `p₁` be the adversary's acceptance probabilities when every challenge is answered with an encryption of bit `0` or bit `1`, respectively, averaging over encryption coins. The first query is independent of those coins. The signed differences agree before taking absolute values:

| First challenge | Game difference | Distinguisher output rule | Distinguisher difference |
|---|---|---|---|
| `(0, 1)` | `p₀ − p₁` | Adversary's bit | `p₀ − p₁` |
| `(1, 0)` | `p₁ − p₀` | Negated adversary bit | `(1 − p₀) − (1 − p₁) = p₁ − p₀` |
| Equal messages | `0` | Constant false | `0` |
| No challenge | `0` | Constant false | `0` |

This is exactly `expect_indicator_sub` and the surrounding `firstQ` case split in `padded_cpa_advantage_eq`. Averaging over the remaining coins and taking absolute values proves the claimed identity. The final theorem applies `singleBitSecure_iff` to this single machine and closes `INDSecure_iff` with its negligible advantage.

**Boundary cases.** No positive-budget or positive-parameter assumption is introduced. Budget zero, no challenge, repeated challenges, malformed-move termination, and timeout remain covered by the same computation and T1 contract. In particular, after a reversed message pair, finalization may turn the adversary's false timeout bit into true; this is the intended negation, and its constant contribution cancels in the difference.

## Rule 10, API, and landing edits

I checked that the three whole-file seal probes contain the unmodified pre-landing sources, apart from the added harness and its import separator. Their source and probe hashes match the recorded revisions. The installation and end-of-file payloads agree, with 2,100, 669, and 2,006 distinct requested definitions, respectively. The logs verify installation, instance-unfolding masks with typeclass lookup preserved, and persistence through EOF; all three source seals and the base control pass. The final controls supersede the failed first attempt: all 17 sealed negative controls fail as intended, their unsealed versions pass, and the reader controls pass.

The explicit-reader scan reports 388 items and no foreign definition reads. I inspected its unresolved items used in touched declarations: they are local facts, published probability theorems, or the owner's `indImpl` readers. Neither helper imports `OracleSecurity`. New public definitions have equation/case readers or the six non-simp `recHandler` projection lemmas. Nontrivial proofs have corresponding sketches. No new global simp attribute is introduced. Head file lengths are 982, 274, and 333 lines.

The landing commit changes documentation and scopes the `open` to `PaddedCPA`. Its only proof edit replaces the product-expectation calculation by `Bridge.expect_sample_pair`, `expect_bind`, and `expect_pure`. This consumes published theorems, preserves the statement and reduction route, and addresses the reported duplicate proof. The supplied seals precede this edit; I reviewed this small delta directly rather than treating those seals as runs on the final head.

DL-30 (moving the generic probability lemmas) and DL-31 (consolidating existing padding readers) remain the recorded follow-up work. Neither creates an additional correctness or scope finding here.

## Build and axiom evidence

The landing closure log has 233 module rows, in the declared order, all with return code zero and zero errors. The downstream log has 15 successful module rows, including `TCSlib` and `audits/pass-shelat/Checks`. **Every source SHA-256 in both logs matches the exact pinned head.** I also checked the archived review's module-log hashes and distinguished its superseded controls from the final passing controls.

The recorded admission census is 31 → 30, removing only `padded_cpa`. Both `padded_cpa` and `TrapdoorCollection.tdpBitScheme_padded_cpa` have exactly `[propext, Classical.choice, Quot.sound]` in the landing axiom log; the review's 43-declaration axiom summary reports no additional axioms. The three changed sources contain no admissions or unsafe escape. Recorded style lint has zero failures and the same six warnings in unchanged files.

## Findings

| # | Severity | File and declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| — | — | — | No findings | Source and evidence checks above | None |

No repository changes, dispatches, reviews, pushes, or merges were performed. The user retains dispatch and merge control.

**Notation introduced in this report:** `p₀`, `p₁` are the conditional acceptance probabilities defined in proof-review step 4.
