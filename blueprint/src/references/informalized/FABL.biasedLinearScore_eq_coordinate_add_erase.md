<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.biasedLinearScore_eq_coordinate_add_erase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Decomposition of the Biased Linear Score

**Claim.** The sum of the standardized biased signs over all coordinates equals the contribution at coordinate $i$ plus the sum over all other coordinates.

**Proof.** The score is the sum over the full coordinate set. Partition that set into the singleton containing $i$ and the set with $i$ erased. The finite sum therefore equals the term at $i$ plus the sum over the remaining coordinates.
