<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.expect_matrixCharacter_mismatch_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matrix character mismatch under translation

**Claim.** For a uniformly random binary matrix represented by a flattened binary vector, the probability that $q$ disagrees with the matrix character after translating by $X$ equals the relative Hamming distance between $q$ and that character.

**Proof.** First identify the relative Hamming distance between functions on matrices with the corresponding distance after composing both functions with the flattening map (`FABL.relativeHammingDist_unflattenBinaryMatrix`). The probability of disagreement is that relative Hamming distance (`FABL.uniformProbability_ne_eq_relativeHammingDist`). Let $a$ be the flattened vector of $X$. Translation $z\mapsto z+a$ is a bijection of the binary cube, so it preserves uniform expectation. Under this change of variables, unflattening the translated vector gives the original matrix plus $X$, because unflattening respects addition (`FABL.unflattenBinaryMatrix_add`). The translated mismatch expectation is therefore the unshifted relative Hamming distance, as claimed.

**Key facts.** `FABL.relativeHammingDist_unflattenBinaryMatrix`, `FABL.uniformProbability_ne_eq_relativeHammingDist`, `FABL.unflattenBinaryMatrix_add`.
