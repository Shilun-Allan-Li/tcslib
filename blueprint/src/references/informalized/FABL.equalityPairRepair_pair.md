<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingExercises.lean :: FABL.equalityPairRepair_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Repaired value on a pair

**Claim.** At either position of the indexed pair, the repaired string takes the original string's value at the pair's first position.

**Proof.** Evaluate the repair at the position indexed by $(i,\text{side})$. The inverse product-coordinate identification sends this position back to $(i,\text{side})$; the repair then discards the side and reads the original string at $(i,0)$. This gives the claimed equality for either side.
