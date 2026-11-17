<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.card_empiricalInfluentialCoordinates_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on selected coordinates

**Claim.** For a positive rational influence bound $t$, a learning parameter $\varepsilon$ with $0<\varepsilon\leq 1/2$, and any prescribed samples for every coordinate, the empirical influential-coordinate set has cardinality at most its coordinate cap, defined from $t$ and $\varepsilon$.

**Proof.** Let $R$ be the uncapped empirical influential-coordinate set. If $|R|$ is at most the coordinate cap, the definition returns $R$, and the desired bound is exactly this case assumption. If $|R|$ exceeds the cap, the definition returns the empty set, whose cardinality is zero and therefore is at most the cap, a natural number.
