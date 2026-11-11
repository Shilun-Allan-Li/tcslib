# Pass–shelat Gate 12, round 2: CPA pilot statement audit

**Verdict: CLEAR.** Open findings: **0 blockers, 0 majors, 1 minor**. **G12-01, G12-02 and G12-03 are fixed** in the audited source and pack. The gate's closing condition is met. The remaining minor concerns the live PR description.

This clears the statement gate. The two intended theorem admissions remain; the corollaries depend on them. This report does not certify completed security proofs. No changes were submitted, dispatched, pushed or merged.

## Audited revisions

| Material | Revision |
|---|---|
| Exchange | `29828d20fdabc6c8f29d1f308dc3312a2496654e` |
| Draft PR | [#287](https://github.com/Shilun-Allan-Li/tcslib/pull/287) |
| Lean head | `80825587f3d6bda7db2b6472fb0cc88e728e73e7` |
| Pinned comparison base | `ed0f723871e0fd65e674bcf3f55c7e0ee173fdf5` |
| Campaign records | `d1ff29f87becde67d7d992e53da45bcede32f9c0` |
| Round-1 Lean head | `135d54511dc0e5c42d93d1d680bf1f26c6aba5cc` |

The PR head matched the requested Lean head when inspected. The comparison uses the pack's pinned base, independently of subsequent movement of the campaign branch.

## Integrity and verification

Read the gate README, `pack-r2.md`, `resolutions-r1.md`, bundle, revision-qualified index, diffs, source manifest, and supplied replay, seal and axiom evidence. Retrieved the indexed originals and replayed module sources separately from GitHub at their specified revisions.

- **15/15 `SHA256SUMS` entries pass.** The bundle is **197,611 bytes**, with SHA-256 `1302e45e76c064f2ee99a8350cf45a711cbd5aed49d59cabdbe312a9126500ac`.
- All **13 bundle sections** match `BUNDLE-FILES.txt` in order and match their separately retrieved originals, allowing only the bundle's separating newlines. The separately retrieved pack and resolutions therefore also match the campaign records pin.
- Independently checked the Git blob SHA-1 of **32 retrieved text files** against GitHub's returned blob identifiers. All four entries in `source-head-r2.json` match the pinned source bytes.
- All **15 replay rows** match the independently retrieved source SHA-256 at the audited head. Their order equals `replay-order.txt`; every module row records `rc = 0` and `errors = 0`, including both new modules, the public-key facade, `TCSlib`, and `audits/pass-shelat/Checks`.
- The replay reports **six admissions**: the two new targets and four existing admissions. The three modules containing those four existing admissions are byte-for-byte unchanged from the pinned base.
- Applied `pr.diff.txt` to the pinned base files in an isolated verification directory: it reproduces all four changed files exactly. Applied `r1-to-r2.diff.txt` to the separately retrieved round-1 files: it reproduces both round-2 files exactly. Removing block comments leaves identical round-1 and round-2 Lean code.
- The recorded round-1 findings hash is correct: `8d33edf17d26349eafd7e2916c6102be5d721a2d0edb0fc039573cf33cc032a2`.

These independently reproduce the content and hash checks. Lean and Lake are absent from this auditor's PATH, so the Lean executions were **not independently rerun**. The successful compilation claims above refer to the supplied, source-matched replay. Its recorded object and log hashes were not checked against separately supplied compiled objects or individual raw replay logs.

## Round-1 resolutions

| Finding | Status | Independent check |
|---|---|---|
| **G12-01 — major: final-source replay mismatch** | **Fixed** | `AdaptiveCPA.lean` and its replay row both hash to `9aea1a66fa55363ffb0892a364e9e39d174aee235430c6dbe74bfa6f71f5161e`. All 15 affected module rows now match the audited head, including the formerly missing direct check of the final adaptive module. |
| **G12-02 — minor: incorrect hybrid attribution** | **Fixed** | Both modules now attribute the bitwise/single-to-many argument to book p. 103. The adaptive module explicitly identifies its adaptive extension as additional reasoning. Algorithm 104.3 and Theorem 104.4 are retained as the single-bit trapdoor construction and security result, on pp. 104–105. Checked these locations and Definition 171.5 against the original Cornell notes, and checked Cornell lecture 13, Theorem 2. |
| **G12-03 — minor: inaccurate admission count in pack** | **Fixed** | `pack-r2.md` correctly says two admissions are introduced and four existing admissions also appear in the replay. Source inspection confirms the replay's distribution: `OracleSecurity` 1, `AdaptiveCPA` 1, `BitwiseCPA` 1, non-malleability indistinguishability 1, non-malleability simulation 2. The separate live-PR wording issue is recorded below. |

The round-1 note is also addressed: the adaptive sketch now selects its hybrid index whenever **`cap(n) > 0`**, including at parameter zero. It no longer imposes the unnecessary `n > 0` condition.

## Open finding

| # | Severity | File and declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| **G12-R2-01** | **minor** | PR #287 description, “Checks” | The live PR description retains the obsolete warning-count claim. | It says “The `sorry` warnings are exactly the two targets.” The refreshed, verified replay records six: two new and four existing. The round-2 pack itself is correct. | Update the PR description to distinguish two new admissions from the four existing admissions reported by replay, and identify the round-2 checked head. |

This documentation correction does not block the statement gate. No additional blocker, major, statement defect or missing hypothesis was identified.

## Statement review

### Generic adaptive CPA lift

`PublicKey/AdaptiveCPA.lean:65`, `FixedLengthPKScheme.INDSecure.adaptive_cpa`, has the appropriate general header: every fixed-length public-key scheme secure in the single-challenge CPA game is secure in the audited adaptive CPA game. No additional scheme premise was identified.

1. The published adaptive oracle equations give the required cap semantics. Every fresh challenge adds one history entry, including a repeated ciphertext value. At the cap, later challenges return the latest ciphertext. Cap zero preserves empty history and returns zero. Both decryption cases return the refusal reply under CPA, regardless of history.
2. Consequently, the sketch's `H_0` and `H_cap` are the false-bit and true-bit experiments. The reduction must count fresh challenges and remember the latest ciphertext; CPA does not require it to retain the full refusal history.
3. At positive cap, `exists_advantage_hybrid_gap` supplies the selected index. `InteractiveHandler.init` permits parameter-dependent advice of polynomial length, so the index can be chosen non-uniformly. Forwarding only the selected fresh challenge, locally encrypting earlier right messages and later left messages, and repeating the saved ciphertext after the cap gives the adjacent hybrids. If the selected challenge is never reached, both simulations agree.
4. T2, `exists_interactiveHandlerMachine`, supplies the required machine and coin bijection, with outer budget `q(n) · perCall(n) + finCall(n)`. Here `perCall = 1` and `finCall = 0` suffice. The seed of `cap(n)` encryption tapes has polynomial length; unused tapes do not change the distribution.
5. The hybrid bound is the cap times the selected reduction's advantage. Applying single-challenge security and `Negligible.polyExpr_mul` supplies the required negligible bound. Cap zero and query budget zero have zero advantage directly.

**Interface assessment:** no necessary missing reader was identified. In particular, `adaptiveIndImpl_dec_issued`, `adaptiveIndImpl_dec_other`, and `indImpl_dec_cpa`, with the public specification-type equations, suffice for CPA refusal. A fill must still construct the handler and prove simulation, eager-coin transport, and endpoint equalities through those interfaces.

### Padded bitwise CPA

`PublicKey/BitwiseCPA.lean:69`, `BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa`, has the right premise and padding hypotheses. `hL` bounds the actual bitwise encryptor on every generated key, message and encryption tape; `hmsg` supplies the message-width condition for the padding constructor.

1. Messages may be chosen after the public key. Ordinary `PublicKeyScheme.Secure` only covers pairs fixed independently of that key, so it does not justify this step in general. The single-bit premise supports the required key-dependent orientation through the flip/zero reduction.
2. `bitwise_enc`, `bitwise_enc_runAt`, `bitwiseEncCoins`, and `bitwiseEncCoins_ofFn` expose the exact ciphertext layout and independent single-bit tapes. `padded_enc`, `runAt_padEnc`, and the public coin identifications expose padding without unfolding foreign definitions. The bit-hybrid endpoints are the two CPA games; at `n = 0`, both messages are empty and their advantage is zero.
3. The proposed output rule preserves the signed gap exactly. Condition on the public key and pre-challenge execution, whose distribution is independent of the supplied ciphertext's plaintext bit. Write `p_t` for the subsequent acceptance probability when the planted block encrypts bit `t`:

| Selected message-bit pair | Adjacent hybrid difference | Reduction difference: input bit 0 minus input bit 1 |
|---|---|---|
| `(0,1)` | `p_0 - p_1` | `p_0 - p_1` |
| `(1,0)` | `p_1 - p_0` | `(1-p_0) - (1-p_1) = p_1 - p_0` |
| Equal bits | `0` | `0`, by the zero-output rule |
| No challenge | `0` | `0`, by the zero-output rule |

Averaging these signed equalities and then taking absolute values gives the exact single-bit advantage identity, with no extra factor of two. Repeated challenge queries must reuse the assembled ciphertext and the orientation of the first challenge.

4. T1, `exists_handlerMachine`, supports one run of the adversary, the advised bit index, the final output transformation, and `n` encryption tapes. `singleBitSecure_iff` bounds that single non-uniform reduction machine. The total loss is a factor of `n`, handled by `Negligible.polyExpr_mul` with `.var`.

No necessary missing reader or extra hypothesis was identified. These are feasible proof plans, not completed Lean reductions.

### Corollaries, readers and policy

- **`bitwise_padded_adaptive_cpa`** is the direct composition of the two target statements. Its proof introduces no further admission.
- **`exists_adaptive_cpa`** supplies a meaningful witness: `msgLen = .var`, the same key generator, and adaptive CPA security. It uses `exists_padBound`, `padded_msgLen`, `padded_gen`, and `bitwise_gen`. The `FixedLengthPKScheme` record already carries uniform efficient generation/encryption, efficient decryption, fixed ciphertext width and perfect correctness. No additional generic correctness or efficiency premise is needed for the intended RSA/Rabin composition; candidate-specific bridges remain separate work.
- **`bitwise_gen`, `bitwise_enc`, `bitwise_dec`**, at `EnsembleSecurity.lean:299`, `:303`, and `:307`, state the definition's three fields exactly. They are public, have formula-bearing docstrings, are beside the definition, and have no `@[simp]` attribute. Their local `rfl` proofs read their own module's definition.
- The corollary terms use published readers. The supplied seal probe covers both corollaries with the listed constructors, predicates and operations sealed; its only Lean diagnostic is the intended body-reading control at line 27. The associated failure summaries are consequences of that control, not additional theorem failures. The axiom log reports standard axioms for the readers and `sorryAx` for the existence corollary, consistent with the two admitted targets.
- The reviewed comparison APIs do not duplicate the new statements: `Secure.multiMessageSecure` and `SingleBitSecure.bitwise` concern fixed-message ensembles; `AdaptiveINDSecure.single` is the reverse implication. No duplicate public result was identified in the reviewed APIs.
- The two new theorem files have specific imports, source citations and proof sketches. The public-key facade imports and documents both, and the root reaches that facade. All 190 added diff lines satisfy the 100-character limit. No new definition or private host is introduced.

## Disposition and references

Gate 12 round 2 may close as a **statement audit**. Correct G12-R2-01 when updating the PR description. The later proof audit must check the actual reductions, their interface discipline, and removal of the two target admissions.

- [Pinned exchange gate](https://github.com/Shilun-Allan-Li/tcslib/tree/29828d20fdabc6c8f29d1f308dc3312a2496654e/outbox/gates/12-cpa-pilot-r2-gate)
- [Pinned adaptive CPA statement](https://github.com/Shilun-Allan-Li/tcslib/blob/80825587f3d6bda7db2b6472fb0cc88e728e73e7/TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA.lean#L65)
- [Pinned bitwise statements and corollaries](https://github.com/Shilun-Allan-Li/tcslib/blob/80825587f3d6bda7db2b6472fb0cc88e728e73e7/TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA.lean#L69)
- [Pinned policy](https://github.com/Shilun-Allan-Li/tcslib/blob/d1ff29f87becde67d7d992e53da45bcede32f9c0/policy.md)
- [Pass–shelat, third edition, January 2010](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf): book pp. 103–105 and 171–172 (PDF pp. 115–117 and 183–184).
- [Cornell CS 6830, lecture 13](https://www.cs.cornell.edu/courses/cs6830/2009fa/scribes/lecture13.pdf), Theorem 2: the fixed-vector single-to-many argument; the oracle-adaptive extension is additional reasoning in this development.

**Notation glossary:** `n` is the security parameter; `q` and `cap` are the polynomial total-query and fresh-challenge budgets; `H_i` is the sketch's hybrid after switching the first `i` challenges or bits; `p_t` is the conditional acceptance probability with planted plaintext bit `t`. Other code-formatted names are repository identifiers.
