<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingExercises.lean :: FABL.equalityPairRepair_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Repair produces equal pairs

**Claim.** The repaired Boolean string has equal values at the two positions of every indexed pair.

**Proof.** Fix an index $i$. By definition, the repaired string at either position of the pair is obtained by applying the inverse product-coordinate identification to that position, taking its pair index, and reading the original string at side $0$. For the two positions indexed by $(i,0)$ and $(i,1)$, this inverse identification returns the same pair index $i$. Hence both repaired values are the original value at $(i,0)$, so they are equal.
