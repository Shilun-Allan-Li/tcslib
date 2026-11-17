<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.DepthCircuit.retainedLayer1Embedding_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Retained Indices Under the Embedding

**Claim.** Every position in the retained-index coordinate type maps to an index in the finite set of retained first-layer indices.

**Proof.** The embedding sends a coordinate to the underlying first-layer index of its preimage under the inverse of the finite-set equivalence. That preimage is an element of the subtype of retained indices, so its defining property says precisely that its underlying index belongs to the retained-index set. Hence the image is retained.
