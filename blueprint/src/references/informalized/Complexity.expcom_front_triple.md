<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/EXPCOM.lean :: Complexity.expcom_front_triple -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Front Transformation on Encoded Triples

**Claim.** For Boolean words α and x and a natural number n, applying the front transformation to the encoding of α, x, and n true bits yields the encoding of the pair whose first component encodes the binary representation of 2ⁿ together with α, and whose second component is x.

**Proof.** The validity characterization (expcom_ok_iff) shows that the specified nested encoding passes the validity test, so the front transformation takes its simulator-input branch. In that branch, extracting the successive second components recovers the block of n true bits, while extracting the first components recovers α and x. Appending a false bit to the true-bit block makes the fixed-width increment succeed: the increment rule for a block of true bits followed by a word (incFixed_replicate_true_append) reduces this to incrementing the final false bit, producing n false bits followed by true. This is precisely the bit list for 2ⁿ (bits_two_pow_eq_replicate). Substituting these components into the pair encodings gives the claimed output.

**Key facts.** `Complexity.expcom_ok_iff`, `Turing.incFixed_replicate_true_append`, `Turing.bits_two_pow_eq_replicate`.
