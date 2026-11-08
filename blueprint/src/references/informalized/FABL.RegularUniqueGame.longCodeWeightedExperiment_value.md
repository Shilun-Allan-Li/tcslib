<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.longCodeWeightedExperiment_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted experiment value identity

**Claim.** Under the assignment induced by a long-code table, the weighted constraint experiment value equals the long-code experiment value.

**Proof.** For each sampled outcome, the weighted experiment evaluates the tester predicate on the assignment at the scope positions. By the definitions of that scope and of the induced assignment, these values are precisely the long-code responses at the sampled neighbour positions. The predicate and sampling law are also the same, so the payoff functions agree pointwise and hence their expectations, which define the two values, are equal.
