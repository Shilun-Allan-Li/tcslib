# Pass–shelat Gate 18 — nm-cca2 findings

**Verdict: CLEAR (PASS)** at Lean head `1636480237286f538bb75b0021b2285edcd0b5b9`.

**Findings: 0 blockers, 0 majors, 0 minors, 0 notes.** No repair is required to close this gate. The accepted consolidation work recorded in DL-36 remains scheduled follow-up.

| Audited item | Pin |
|---|---|
| Repository / PR | [Shilun-Allan-Li/tcslib, draft #294](https://github.com/Shilun-Allan-Li/tcslib/pull/294) |
| Exchange | `5f79e1a72d300eb6bc737532167ee6a4384b6595` |
| Lean source | `1636480237286f538bb75b0021b2285edcd0b5b9` |
| PR base | `4d10bc4e577a90345717c8777b6a9d16ffd7f1f8` |
| Campaign records | `3c6ee34a713a6a3db4c930b6b16f195484c63896` |

The audited theorem is `FixedLengthPKScheme.indSecure_cca2_iff_nmSecure_cca2`, the frozen fixed-length public-key formulation of [PS10, Theorem 175.9](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf#page=187). The independent Lean replay prints exactly:

```lean
∀ (S : FixedLengthPKScheme), S.INDSecure .cca2 ↔ S.NMSecure .cca2
```

I read the README, pack, all bundle sections, the three helper modules, both oracle-security interfaces, the handler interface, and the maintainer's landing diff. The repository and packet were checked as audit evidence.

All **15 outer SHA-256 entries** pass. All **16 packet Git blobs**, including SHA256SUMS itself, match the pinned exchange tree. The **13 ordered bundle sections** reproduce their revision-qualified Git files exactly, apart from the bundle's separator newline. Every file in the **159-module source closure** matches its head Git blob. All **635 inner evidence checksums** pass with no unlisted payload files. The bundled PR diff equals the independently obtained Git diff.

The bundle is 274,306 bytes; its SHA-256 is:

```text
0213c22e7782399705c0e48b9cc7de487449ffd04894aa1d52b05d26511c0349
```

The statement freeze passes. All pre-existing non-malleability declarations preceding the new proof section are byte-identical to the base, and the target declaration's signature is byte-identical. Removing the two authorized reader additions from `PublicKey/OracleSecurity.lean` reproduces its base bytes exactly. `NonMalleability/Simulation.lean` is unchanged. The final maintainer commit contains the disclosed reader move, import/module removal, consumer re-pointing and documentation/whitespace edits.

The proof checks as follows:

1. **IND-CCA2 ⇒ NM-CCA2.** The forwarding handler preserves every query and answer. The finalization counts only its own decryption log, decrypts the output blocks in order, and runs the distinguisher with the correct advice and coins. `castImpl_indImpl_dec` identifies each answer with `nmDecrypt`, including refusal and invalid decryption. `decAnswers_eq_nmOutput` identifies the concatenation. `accept_indGame_decRed` proves equality of acceptance probabilities for each challenge bit, with polynomial budget `q(n) + ℓ(n)`. The advice transformation preserves the oracle computation for every codec and budget.
2. **NM-CCA2 ⇒ IND-CCA2, positive message length.** The finalization outputs honest encryptions of the repeated guess bit and its complement. Perfect correctness makes these ciphertexts distinct, since their plaintexts differ at the first bit. At most one can equal the recorded challenge. `guessDist_nmOutput` therefore recovers the guess from the first valid decryption, or from the complement in the second. `accept_nmGame_encRed` proves equality of acceptance probabilities, with two output ciphertexts and budget `q(n)`.
3. **Zero message length.** `indImpl_eq_of_msgLen_eq_zero` proves equality of the two oracle implementations through published readers. Thus the original IND advantage is zero; the reverse proof does not assume recovery of a guess from an empty plaintext. Its negligible bound is nonnegative by the NM advantage bound.
4. **Assembly.** The target pairs the two proved directions. The coin equivalences, sampling reorderings, codec transports and polynomial-budget instantiations retain the stated quantifiers. Neither direction introduces an advantage loss in its comparison.

| Edge case | Checked behavior |
|---|---|
| Query budget zero | The compiled reduction preserves the adversary's bounded computation; finalization retains its separate budget. |
| Zero output ciphertexts | Decryption finalization immediately runs the distinguisher on the empty list. |
| No challenge | Both decryption mechanisms accept every ciphertext for ordinary decryption. |
| Repeated challenges | Both runs retain the same first recorded ciphertext. |
| Output equals challenge | Both forward-comparison sides return the all-false refusal encoding. |
| Invalid decryption | Both forward-comparison sides use `decAnswer none`, the same all-false encoding. |
| Malformed machine output | The same codec decoding/default is transported through the reduction. |
| Codec timeout | The forward reduction preserves the default output; the reverse reduction handles the default false guess. |
| Ciphertext/message width zero | No positivity assumption is used in the forward proof; the reverse proof separates empty messages explicitly. |

The independent replay used **Lean 4.25.0**, commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`, and **Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`**. All nine dependency checkouts present for this narrowed closure agree with the audited manifest. The fresh 159-module build uses an initially empty olean tree and the pinned checking script, one Lean process at a time: **159/159 compile, zero errors**. Each result records its source hash and log hash.

The target, both directions and both added readers each print exactly `[propext, Classical.choice, Quot.sound]`. The fresh census checks **all 313 stored constants of the five changed files**, including auxiliary constants and the pre-existing OracleSecurity material: none has a nonstandard axiom dependency. The separately rebuilt, unchanged Simulation module retains its two admissions, and `simNMSecure_cpa_iff_nmSecure_cpa` still prints `sorryAx`; this dependency does not enter the audited equivalence.

Both final-head seal variants were independently replayed. Their request sets match a newly collected import-closure census, including generated matchers and imported instances. The instrumentation was checked to preserve the exact source body. Four additional paired controls confirm that definitional reads succeed unsealed, fail sealed, and close through published readers.

| Final source | A requests / result | B requests / result |
|---|---|---|
| `Indistinguishability.lean` | 2205 / pass | 2206 / pass |
| `Forward.lean` | 1996 / pass | 1997 / pass |
| `Decrypt.lean` | 2165 / pass | 2166 / pass |
| `Encrypt.lean` | 2165 / pass | 2166 / pass |
| `OracleSecurity.lean` | 2101 / pass | 2102 / four inherited errors |

Variant B also seals `PolyExpr.eval`. The four OracleSecurity failures have identical source locations and diagnostic headers in the independently replayed base control and head. They precede the added readers; neither reader fails. Accordingly, the full OracleSecurity B file is **not** described as a clean compilation. Its new declarations introduce no additional failure.

The two authorized readers are public, have formula docstrings, carry no `@[simp]`, and live beside `indImpl_dec_onSpec`. The old `Readers.lean` is removed. All five changed files stay below 1000 lines: 655, 350, 350, 332 and 999. The local style check on the available public-key subset has zero failures; its two warnings concern unchanged files. The supplied full public-key lint has zero failures and the same six baseline warnings. The explicit-unfold evidence reports zero foreign-definition items. I manually reconciled its 133 local/unresolved rows against local hypotheses, published readers and scheme proof fields; none conceals an explicit foreign-definition body read.

I also checked the supplied 253-module build/admission evidence and all 29 final landing records. The final records have zero errors, follow the stated order, and all 29 source hashes match the pinned head. These downstream/root builds were supplied evidence; the independent local build covers the target's full upstream closure and the unchanged Simulation module. The supplied broader admission census changes 27 → 26 by removing exactly the target admission.

DL-36 covers the observed log-processing, round-input-reader and block-extraction overlap and gives concrete consolidation destinations. I agree with the pack's deferral. I found no additional undisclosed copy requiring a new finding. The scheduled OracleSecurity split remains justified by its 999-line size.

The companion ZIP contains this Markdown, source-bound fresh build/probe logs, the input and freeze checks, the axiom/seal census, diagnostic comparison, audit probes and reproduction scripts. See `evidence/README.md` for the distinction between fresh checks and supplied attestations.

**Notation:** `S` is the fixed-length public-key scheme; `n` is the security parameter; `q(n)` is the adversary's query budget; `ℓ(n)` is its number of output ciphertexts. A and B name the seal variants defined above.
