<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.pairVectorSnd_snoc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second coordinates of an appended pair vector

**Claim.** Taking second coordinates of the vector obtained by appending a pair gives the vector of second coordinates with the appended pair's second coordinate appended.

**Proof.** Check the vector equality at each index. The final index reads the appended pair's second coordinate. Every earlier index reads the second coordinate of the corresponding unchanged pair from the original vector, which is the corresponding entry of its second-coordinate vector.
