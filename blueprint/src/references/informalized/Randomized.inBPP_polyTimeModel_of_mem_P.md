<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Inclusions.lean :: Randomized.inBPP_polyTimeModel_of_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Polynomial-Time Recognition in BPP

**Claim.** Every language in $\mathrm{P}$ belongs to BPP in the polynomial-time verifier model.

**Proof.** Let a deterministic polynomial-time decider recognize the language. Use a verifier that ignores its random string and returns the decider's answer. To certify efficiency in the stated model, take both accepting and rejecting verifier languages to be the inverse image of the language (respectively its complement) under the projection that recovers the input from the paired encoding. The projection is polynomial-time computable, and polynomial time is closed under polynomial-time preimages; the complement of a polynomial-time language is also in $\mathrm{P}$. The pairing projection recovers the original input, so these languages describe exactly the verifier's two answers. On an input in the language the verifier always returns true, and outside it always returns false. Thus the required acceptance and rejection probabilities are both $1$, using zero random bits.

**Key facts.** `Complexity.preimage_mem_P`, `Complexity.compl_mem_P`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.pairFstD_pairEncode`, `Randomized.randProb_congr`, `Randomized.randProb_true`.
