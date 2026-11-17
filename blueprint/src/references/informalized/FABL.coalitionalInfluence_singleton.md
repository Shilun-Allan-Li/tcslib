<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.coalitionalInfluence_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton Coalitional Influence

**Claim.** For a Boolean function $f$ and coordinate $i$, its coalitional influence on the singleton $\{i\}$ equals its Boolean influence at $i$, the probability that flipping $i$ changes the function's value.

**Proof.** Both quantities are uniform probabilities, so compare their indicator functions on each input. The event that both signs can be attained by changing only coordinate $i$ is equivalent to the function being pivotal at $i$ (`FABL.coalitionCanAttain_singleton_both_iff_isPivotal`). Thus the two indicators agree at every input, and so do their uniform averages.

**Key facts.** `FABL.coalitionCanAttain_singleton_both_iff_isPivotal`.
