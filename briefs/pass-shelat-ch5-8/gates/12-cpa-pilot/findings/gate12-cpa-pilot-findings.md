# Pass–shelat Gate 12: CPA pilot statement audit

**Verdict: HOLD.** Counts: **0 blockers, 1 major, 2 minors**. The closing condition of zero blockers and zero majors is not met. No false mathematical statement or missing mathematical hypothesis was identified; the major concerns missing verification of the final source bytes.

This is a statement audit, not certification of completed proofs. The two intended theorem admissions remain, and the corollaries inherit them. No repository changes, dispatches, pushes, or merges were made.

## Audited revisions and integrity

| Material | Pinned revision |
|---|---|
| Exchange | `2b8a52de306d6d2bd097887d6cfc6a173479aca9` |
| Draft PR | [#287](https://github.com/Shilun-Allan-Li/tcslib/pull/287) |
| Lean head | `135d54511dc0e5c42d93d1d680bf1f26c6aba5cc` |
| Parent / comparison base | `ed0f723871e0fd65e674bcf3f55c7e0ee173fdf5` |
| Campaign records | `8e8bc7672630a99abb9fee646006357d4153bacb` |

Read the exchange README and gate README, pack, complete bundle, index, diff, source manifest, and all supplied evidence. Retrieved committed file bytes through GitHub and independently checked their Git blob hashes.

- **14/14** entries in `SHA256SUMS` pass.
- The bundle is **190,181 bytes**, with SHA-256 `9715ff33bb4f8802c1d55eed0ea6d1894b04cfa324d3accc8138d202d6bdf676`.
- All **12** bundle sections match the revision-qualified `BUNDLE-FILES.txt` in order and match their separately retrieved committed contents, allowing only the bundle's separating newline.
- All four hashes in `source-head.json` match the pinned Lean files. Commit metadata confirms four changed files, 188 additions, and no deletions.
- Checked the source book against the pinned root-tree blob: SHA-256 `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`. Read book pp. 103–105 and 171–172, and the cited Cornell lecture.

These checks establish pack integrity; they do not establish the accuracy of every claim in the pack.

## Findings

Paths below are relative to the repository, except evidence paths, which are relative to the exchange gate directory.

| # | Severity | File and declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G12-01 | **major** | `PublicKey/AdaptiveCPA.lean`, `FixedLengthPKScheme.INDSecure.adaptive_cpa`; replay evidence | The supplied successful replay does not verify this file at the audited head. | Its committed SHA-256 is `5b7914843e1f7313693b134bd44cc48b9f1a39472804cda9658d92ffe96815ea`; the sole matching module row in `evidence/replay.jsonl` records `f036d2cee7b0404b90fdcd4f4f8c1852344281a83c66b4367878cbdbc4497483`. The eight-module `replay-after-docfix.jsonl` contains no `AdaptiveCPA` row. See details below. | Replay the final `AdaptiveCPA.lean` and its affected dependents, binding successful checks to the final source hashes. Supply the resulting evidence and regenerate the pack checksums. |
| G12-02 | **minor** | `PublicKey/AdaptiveCPA.lean:16–28,39–40`; `PublicKey/BitwiseCPA.lean:14,44` | The hybrid argument is attributed to the wrong textbook theorem. | Algorithm 104.3 constructs a trapdoor-based **single-bit** scheme. Theorem 104.4 proves its security by the prediction lemma and a hard-core-bit reduction, on book pp. 104–105. The bitwise extension and single-to-many hybrid discussion are on p. 103. | Cite p. 103 and the hybrid lemma for the lifting argument; retain Definition 171.5 for the CPA game. Identify the adaptive extension explicitly. Keep Algorithm 104.3 / Theorem 104.4 as context for the concrete single-bit construction. |
| G12-03 | **minor** | Gate `pack.md:58–60`, evidence summary | The statement that replay `sorry` warnings are exactly the two targets is inaccurate. | The 15-module replay records six `sorry` warnings: one each in `OracleSecurity`, `AdaptiveCPA`, `BitwiseCPA`, and `NonMalleability/Indistinguishability`, plus two in `NonMalleability/Simulation`. | Say that the change introduces exactly two admissions, while replay also reports four existing admissions. Preserve the distinction between new and inherited proof debt. |

### G12-01: what is and is not established

The source manifest and independently retrieved Git bytes agree on the final `AdaptiveCPA.lean` hash. The replay row agrees on a different hash. The follow-up replay starts at `TrapdoorCPA` and checks eight downstream modules; it does not recheck either new CPA module. The original replay does match the final bytes of `BitwiseCPA`, `EnsembleSecurity`, and the public-key facade.

The description of a final docstring wrap is not accompanied by the earlier `AdaptiveCPA.lean` bytes or an exact before/after diff tied to the replay hash. Therefore this pack does not establish that the replayed version differs only in comments. Rechecking a downstream facade or the root does not, by itself, bind an imported dependency's compiled object to its final source.

This is **not** a claim that the final file fails elaboration. It is a missing final-source check, required by policy §3's review checklist, item 6, and classified as major under the pack's necessary-evidence criterion. Lean and Lake are absent from this auditor's environment, so no independent Lean replay was performed. That environment limitation alone is not a finding.

## Statement and reduction review

### Adaptive CPA lift

The proposed header is mathematically appropriate for every `FixedLengthPKScheme`; no extra premise was identified.

1. Read `adaptiveIndImpl` through its published fresh, full-cap, zero-cap, and decryption equations. Under CPA both decryption branches return the refusal reply and preserve history. Fresh challenges prepend one ciphertext even when its value repeats. Full-cap challenges repeat the latest ciphertext. Starting from empty history, cap zero returns zero on every challenge, independently of the hidden bit.
2. For the hybrids described in the sketch, the endpoints are exactly the false-bit and true-bit games. The reduction must count **fresh challenges**, retain the latest ciphertext, and repeat it after the cap. It need not retain the full history under CPA.
3. At positive cap, `exists_advantage_hybrid_gap` supplies an index. Encoding that index in `InteractiveHandler.init` is permitted: T2 explicitly allows arbitrary parameter-dependent initial state and incorporates it into non-uniform advice. The index and counter have polynomial encodings.
4. Forward only the selected fresh challenge; encrypt the earlier right messages and later left messages locally. Independent seed tapes reproduce the honest fresh-encryption distributions, including branches that never reach the selected challenge. This gives the stated adjacent hybrid pair. T2 supplies the machine and the polynomial outer budget `q.eval n * H.perCall.eval n + H.finCall.eval n`; `perCall = 1` and `finCall = 0` suffice.
5. The hybrid bound gives endpoint advantage at most `cap.eval n * ε n`. The published `Negligible.polyExpr_mul` handles this factor. Cap zero has advantage zero, and query budget zero also gives identical experiments.

For the fill, the sketch's unnecessary restriction to `n > 0` should be removed when selecting the index: the hybrid lemma only needs positive **cap**. At parameter zero a general fixed-length scheme can still have nonempty messages. Alternatively, account for that finite exception explicitly in the negligible bound.

No missing reader was identified. In particular, the CPA decryption fact can be derived from `adaptiveIndImpl_dec_issued`, `adaptiveIndImpl_dec_other`, and `indImpl_dec_cpa`, using the public specification-type equalities. A dedicated adaptive CPA decryption reader would be convenient, but is not necessary. The fill still has to construct the handler and prove its simulation and coin-transport lemmas.

### Padded bitwise CPA theorem

The premise `SingleBitSecure` is suitable. The bound `hL` quantifies over the actual bitwise generator, all `n`-bit messages, and all bitwise encryption tapes. Together with `hmsg`, it is exactly the input needed by `PublicKeyScheme.padded`.

1. The published `bitwise_enc` reader connects the scheme projection to the machine used in `bitwise_enc_runAt`. The equivalence `bitwiseEncCoins` and its `ofFn` reader expose independent single-bit tapes. Padding is read through `padded_enc`, `runAt_padEnc`, and the public coin identifications.
2. Consequently, the zero-bit and all-bit hybrids are the original left and right CPA games. At `n = 0` both messages are empty, so the two experiments agree.
3. For a selected bit, the proposed flip/zero rule preserves the **signed** hybrid gap before taking absolute values. Condition on the public key and the pre-challenge execution, which the distinguisher runs without inspecting its supplied ciphertext. If `p_t` is the conditional acceptance probability after planting an encryption of bit `t`, the calculation is:

| Selected message-bit pair | Hybrid acceptance difference | Distinguisher difference, input bit 0 minus input bit 1 |
|---|---|---|
| `(0,1)` | `p_0 - p_1` | `p_0 - p_1` |
| `(1,0)` | `p_1 - p_0` | `(1-p_0) - (1-p_1) = p_1-p_0` |
| Equal bits | `0` | `0`, by the zero-output rule |
| No challenge | `0` | `0`, by the zero-output rule |

The conditioning distribution is independent of the supplied plaintext bit. Averaging these equalities and then taking absolute values gives the claimed exact advantage identity, without an extra factor of two. Repeated challenge queries must return the assembled ciphertext already stored in the handler state.

4. T1 supports this one-run handler, its final output transformation, the advised bit index, and `n` encryption tapes. `singleBitSecure_iff` bounds the resulting single machine; the total hybrid loss is a factor of `n`, handled by polynomial-times-negligible closure.

The module's distinction from fixed-message ensemble security is correct. For example, conditionally on a secure base scheme, publish a fresh uniform `n`-bit string in the public key and append to each ciphertext a flag indicating whether its plaintext equals that string. Any fixed message pair meets the published string with probability at most `2·2^(-n)`, while a key-visible adversary can select that string and a distinct message and read the flag. Thus fixed-message security alone does not justify this adaptive message selection. This separation argument is a semantic check, not a new Lean formalization.

### Corollaries, readers, and reuse

- `bitwise_padded_adaptive_cpa` is the direct composition of the two targets.
- `exists_adaptive_cpa` uses `S.bitwise.exists_padBound` and the published message-length and generator equations. Its witness has `msgLen = .var` and the same key generator. Correctness, uniform generation and encryption, polynomial-time decryption, and ciphertext width are carried by `FixedLengthPKScheme`. No additional generic hypothesis is needed for the intended RSA/Rabin catalog composition; candidate-specific bridges remain separate work.
- The three new readers state the `bitwise` definition's fields exactly, live beside that definition, have formula-bearing docstrings, and are public without `@[simp]`.
- Source inspection of both corollary terms found no foreign-definition read. The supplied seal probe seals the listed constructors, predicates, and operations; its log reports only the intended failing `rfl` control at line 27. This supports the corollaries' interface discipline but does not replace final-source replay.
- The supplied axiom log reports standard axioms for the readers and `sorryAx` for `exists_adaptive_cpa`, consistent with the admitted targets. It is not evidence of completed security proofs.
- The existing `Secure.multiMessageSecure` and `SingleBitSecure.bitwise` concern fixed-message ensembles; `AdaptiveINDSecure.single` goes in the reverse direction. The new statements do not duplicate those results. No duplicate of these scheme-specific statements was identified in the reviewed public APIs.
- The new files separate the generic adaptive lift from the bitwise application. Their imports are specific, the public-key facade imports and documents both, and `TCSlib.lean` already imports that facade. No new host or construction machinery is introduced at this statement stage.

## Required disposition

Keep Gate 12 on **HOLD** until G12-01 is resolved with final-source replay evidence. Correct G12-02 and G12-03 when refreshing the pack. The mathematical headers need no change on the basis of this audit. A later fill audit must verify the actual reductions and removal of the two admissions.

## Source links

- [Pinned exchange gate](https://github.com/Shilun-Allan-Li/tcslib/tree/2b8a52de306d6d2bd097887d6cfc6a173479aca9/outbox/gates/12-cpa-pilot-gate)
- [Pinned adaptive CPA module](https://github.com/Shilun-Allan-Li/tcslib/blob/135d54511dc0e5c42d93d1d680bf1f26c6aba5cc/TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA.lean)
- [Pinned bitwise CPA module](https://github.com/Shilun-Allan-Li/tcslib/blob/135d54511dc0e5c42d93d1d680bf1f26c6aba5cc/TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA.lean)
- [Pinned policy](https://github.com/Shilun-Allan-Li/tcslib/blob/8e8bc7672630a99abb9fee646006357d4153bacb/policy.md)
- [Pinned source book](https://github.com/Shilun-Allan-Li/tcslib/blob/135d54511dc0e5c42d93d1d680bf1f26c6aba5cc/Pass%E2%80%93Shelat.pdf), book pp. 103–105 and 171–172 (PDF pp. 115–117 and 183–184)
- [Cornell CS 6830 lecture 13](https://www.cs.cornell.edu/courses/cs6830/2009fa/scribes/lecture13.pdf), Theorem 2: fixed-vector single-to-many public-key security; the oracle-adaptive extension is additional reasoning here.

**Notation glossary:** `n` is the security parameter; `q` and `cap` are the polynomial query and fresh-challenge budgets; `ε` is a negligible advantage bound; `D` is the single-bit reduction distinguisher; `p_t` is its underlying adversary's conditional acceptance probability when the selected block encrypts bit `t`. Other identifiers are the repository's declaration or field names.
