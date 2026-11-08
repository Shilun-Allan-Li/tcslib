<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.length_tseitinAuxiliaryLiterals -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Auxiliary list length

**Claim.** For any clause index, the auxiliary literal list has length equal to the block size.

**Proof.** The list is formed by `List.ofFn` over the finite type of positions in a block of size $b$. Such a list has one entry for each element of that type, so its length is exactly $b$. The clause index and the entries’ coordinates do not affect the count.
