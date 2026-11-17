<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.DepthCircuit.length_retainedLayer1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the retained first layer

**Claim.** The list of retained first-layer terms has length equal to the number of retained first-layer indices.

**Proof.** The retained list is formed by applying the indexed-list constructor to the retained indices, with one term for each such index. Its length is therefore the cardinality of that index set.
