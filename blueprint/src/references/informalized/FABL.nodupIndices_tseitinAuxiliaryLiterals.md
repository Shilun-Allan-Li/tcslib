<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.nodupIndices_tseitinAuxiliaryLiterals -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct Auxiliary Literal Indices

**Claim.** For any clause index, the list of auxiliary literals has pairwise distinct variable indices.

**Proof.** Write the auxiliary index at position $r$ as the image under the natural-number offset embedding of the pair encoding $(r,j)$. If two such indices agree, injectivity of the offset embedding gives equality of the encoded pairs. The pair encoding is injective, so the pairs agree; taking their first coordinates shows the two positions are equal. Thus distinct positions cannot yield repeated indices, and the list has no repetitions.
