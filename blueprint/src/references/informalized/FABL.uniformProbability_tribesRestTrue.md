<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.uniformProbability_tribesRestTrue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of a Tribes Block Condition

**Claim.** For a uniformly chosen sign vector on the $sw$ coordinates, the probability that every coordinate in the block containing $i$, except $i$, equals $-1$ is $2^{-(w-1)}$.

**Proof.** First, the block condition is equivalent to requiring that every coordinate in the set of rest coordinates for the block containing $i$ equals $-1$ (the equivalence is `tribesRestTrue_iff_all_neg_on_restCoordinates`). For any finite set of coordinates, the probability that all its signs equal $-1$ is $2^{-k}$, where $k$ is the size of that set (`uniformProbability_all_neg_one_on_finset`). The rest-coordinate set has size $w-1$ (`card_tribesRestCoordinates`), so the probability is $2^{-(w-1)}$.

**Key facts.** `FABL.tribesRestTrue_iff_all_neg_on_restCoordinates`, `FABL.uniformProbability_all_neg_one_on_finset`, `FABL.card_tribesRestCoordinates`.
