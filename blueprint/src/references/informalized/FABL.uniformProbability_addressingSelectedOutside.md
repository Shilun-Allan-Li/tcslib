<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/FriedgutNecessity.lean :: FABL.uniformProbability_addressingSelectedOutside -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of selecting outside a coordinate set

**Claim.** For uniform signs on the first $m+2^m$ positions, the probability that the address-selected data coordinate lies outside $J$ equals the fraction of the $2^m$ data coordinates that lie outside $J$.

**Proof.** Re-express a sign vector as a pair consisting of its first $m$ address signs and the signs at the $2^m$ data positions. This is a bijective reindexing, so it preserves the uniform average. The event indicator depends only on the address signs; averaging over all data signs therefore leaves that indicator unchanged. The address signs range bijectively over the $2^m$ data indices, so the remaining average is the number of indices whose corresponding data coordinate is outside $J$, divided by the total number $2^m$.
