<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.DepthCircuit.retainedLayer1Embedding_equivFin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Retained-Index Embedding Inverse Law

**Claim.** For a retained first-layer index $i$, applying the retained-index embedding to the finite-set equivalence coordinate corresponding to $i$ returns $i$.

**Proof.** The retained-index embedding is formed by first converting a coordinate in the finite set of retained indices back to its subtype element, then taking the underlying first-layer index. Starting with the coordinate assigned to $i$ by the finite-set equivalence, the inverse conversion returns that same subtype element; taking its underlying index therefore gives $i$.
