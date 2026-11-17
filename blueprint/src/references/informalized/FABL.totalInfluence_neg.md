<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/Basic.lean :: FABL.totalInfluence_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Invariance of Total Influence

**Claim.** For any real-valued function $f$ on the Boolean cube, negating $f$ leaves its total influence unchanged.

**Proof.** Fix a coordinate. Linearity of the discrete derivative gives that the derivative of $-f$ is the negative of the derivative of $f$. Their squares are therefore equal at every input, so their expected squared derivatives, and hence their influences in that coordinate, agree. Summing over all coordinates proves the result.
