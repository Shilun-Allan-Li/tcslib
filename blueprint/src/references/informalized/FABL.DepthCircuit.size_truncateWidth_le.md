<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.DepthCircuit.size_truncateWidth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size after width truncation

**Claim.** For every depth circuit and every natural-number width bound, the size of the circuit obtained by retaining only first-layer terms of width at most that bound and restricting the later layers accordingly is at most the original size.

**Proof.** The input-index cast and the pullback of the later layers preserve the tail's internal-node count (the cast invariance fact, `FABL.CircuitTail.internalNodeCount_castInput`, and the pullback invariance fact, `FABL.CircuitTail.internalNodeCount_pullInputs`). Thus the truncated circuit's size is the number of retained first-layer terms plus the original tail count. The retained terms are indexed by a subset of the original first-layer indices, so their number is at most the original number of terms. Adding the same tail count to both sides gives the desired size inequality.

**Key facts.** `FABL.CircuitTail.internalNodeCount_castInput`, `FABL.CircuitTail.internalNodeCount_pullInputs`.
