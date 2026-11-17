<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/BitString.lean :: CommunicationComplexity.BitString.signedInner_eq_agreementCount_sub_hammingDist -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreements minus disagreements

**Claim.** The signed inner product equals the agreement count minus the Hamming distance, with both counts interpreted as integers.

**Proof.** The signed inner product is $n-2d_H(x,y)$ by the formula expressing it in terms of length and Hamming distance (signedInner_eq_length_sub_twice_hammingDist). The agreement count is $n-d_H(x,y)$ by the corresponding formula for agreements (agreementCount_eq_length_sub_hammingDist). Subtracting the Hamming distance from this latter expression gives $n-2d_H(x,y)$, so the two expressions agree.

**Key facts.** `CommunicationComplexity.BitString.signedInner_eq_length_sub_twice_hammingDist`, `CommunicationComplexity.BitString.agreementCount_eq_length_sub_hammingDist`.
