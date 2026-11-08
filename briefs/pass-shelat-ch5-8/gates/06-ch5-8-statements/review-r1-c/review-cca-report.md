# Gate06C CCA findings: independent bounded review

**Disposition: accept C-01, C-02 and C-04 as minor comment/sketch issues. No algorithm, theorem, hypothesis, cost or admission change is needed. No new material defect was found in these CCA scopes.** The proposed patch is unapplied and comment-only.

The complete 522-line received report was read as data, with SHA-256 `577621ca9f6fa665dbc6bd3150f4625ddf2b05d19b9f6021bf652c30c8580ac4`. HEAD was independently read as `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`; the CCA source and four relevant owners were compared byte-for-byte with Git objects at that pin. No native/build/app, incoming script, tracked-source/main/exchange edit, branch or job was run/created.

## C-01 — valid zero-parameter example; positive parameters parse correctly

The pairing is doubled first data, separator 01, then the suffix. At zero, the generated key has empty components and the honest ciphertext is 0101. For 0000, pairDecode fails, so all ciphertext projections are empty. Both length tests pass at n=0, and hFE at zero forces E(⟨[],[]⟩)=[] for the unique empty inputs. Decryption returns [], which decodeFin at zero accepts as the unique empty plaintext. Its four-bit length is exactly the game's ctLen(0), so this is a permitted malformed query.

For n>0, an unsuccessful outer parse would give an empty nonce and fail the first length test. A failed inner parse would give an empty masked word and fail the second. Thus acceptance forces both parses. The public inverse-parser equation makes the original word exactly ⟨r,⟨c₁,t⟩⟩. Generated keys have lengths n and 2n; hFE then makes the checked tag 2n bits, and the ciphertext has exactly 6n+4 bits. There is no missed positive-parameter parsing counterexample in this argument.

The proposal qualifies rejection by generated keys/positive n and explicitly discloses 0000 at zero. The source's all-n correctness/security statements stay intact. At zero there is only one message, so the challenge bit cannot select distinct plaintexts; no asymptotic security counterexample follows. An explicit parser guard would change the algorithm and is unnecessary for this minor disposition.

## C-02 — first-discrepancy coupling repairs adaptive guesses

Put M=2^(2n). In the actual random-tag game, after a failed guess at an unexposed pair, a different guess has conditional success 1/(M−1), not 1/M. The report correctly identifies this problem.

Instead compare with a game that always rejects fresh-pair decryption queries, where fresh means absent from the encryption/challenge tag table. Couple tapes and the same random function. Before the first fresh valid-tag query, both transcripts agree. In the forced-rejection run, rejected guesses reveal no tag. At each candidate query its input is absent from the monotonically growing exposed table, so its tag remains uniform conditional on that forced-game history, even when that input was guessed before. Each candidate hits with probability at most 1/M. A union bound over at most q candidates bounds the first discrepancy by q/M **in each bit-game**. Nonfresh valid-tag inputs reproduce a prior canonical answer, with the challenge equality refusal preserved.

One further numerical precision is folded into C-02's comment repair: advantage is |accept(G₀)−accept(G₁)|. Comparing both bit-games by separate couplings can give 2q/M, plus analogous fixed reduction factors. The original exact coefficient-one advantage sentence is therefore replaced by fixed-constant-factor wording. This has no effect on the existential negligible-bound statement and creates no new proof obligation or premise.

## C-04 — equality branch is negligible, not impossible

For the hypothetical variant tagging only c₁, write P for the pad function, choose challenge messages 0^n and 1^n at positive n, and obtain one auxiliary encryption of zero. The altered query equals the challenge exactly when P(r₁)=P(r*) XOR m_b; tag equality then follows from using the same tag input. If r₁=r* and m_b=0, equality is certain, for every evaluator. Thus the original unconditional query-distinctness claim is false.

The adversary can test equality and avoid the forbidden query on that branch. Outside it, decryption yields the pad and recovers m_b. For a uniform n-bit random pad function, let p=2^(−n). With m_b=0 the failure probability is p+(1−p)p; with the nonzero selected message it is (1−p)p. Both are at most 2p. A PRF-to-random-pad reduction adds negligible error, so the attack is overwhelmingly successful. This analysis concerns the stated hypothetical short-tag variant; actual ccaEncFun already authenticates r||c₁ and is unchanged.

## Proposal and limits

CCA2Scheme-comment-only.patch edits three comment regions: the short-tag attack, the malformed-input qualification, and the admitted CCA2 proof sketch. Separate baseline/proposed .source.txt snapshots are retained. Own validation checks that every replaced old region is comment text and the complete comment-stripped code token/string sequence is identical. The one CCA admission remains byte-identical; all other modules are untouched. No statement, machine, definition body, hypothesis, quantitative contract or attribute changes.

Own finite Python checks illustrate the encoding/guard for n=0,1,2 and enumerate the two small random-function collision distributions. They confirm the stated examples but are not kernel, general asymptotic or pseudorandomness tests. The general arguments above use the actual formulas. Source access/provenance and native claims from the external report were not independently re-audited beyond this bounded task.

The report's CCA table also says the private XOR lemma has no docstring; frozen source lines 299–300 already contain its formula docstring. This is a nonmaterial report inaccuracy, not an additional source defect. No additional material CCA issue arose from the rest of the report. C-03 and other prongs remain outside this review.

No user ruling is required for these authorized comment-only qualifications. Native combined-source acceptance, gate closure and any source PR remain Root/user actions; no new proof branch, fill or external job is proposed.

**Not yet clear to merge — the comment proposal is unapplied and combined-source checks/gate dispositions remain outstanding.**
