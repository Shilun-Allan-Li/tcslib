<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.DepthCircuit.get_retainedLayer1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indexing retained first-layer terms

**Claim.** For any position in the retained first-layer list, the term at that position is the original first-layer term at the corresponding retained index.

**Proof.** The retained list is formed by applying the finite-list constructor to the function that sends each index to its original first-layer term, using the retained-index embedding. Its length is the number of retained indices. Thus a list position is identified with an index in that finite type, and evaluating the list there gives precisely the original term selected by the embedding. The stated length lemma supplies the cast between the list's position type and the retained-index type.

**Key facts.** `FABL.DepthCircuit.length_retainedLayer1`.
