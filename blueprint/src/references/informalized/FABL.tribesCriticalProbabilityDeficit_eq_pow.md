<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.tribesCriticalProbabilityDeficit_eq_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical probability deficit formula

**Claim.** The critical probability deficit equals $(1-2^{-w})^s-\tfrac12$, where $s$ is the critical size.

**Proof.** The deficit is one half minus the probability that the critical tribes function takes the value $-1$. By the probability formula for tribes (`tribes_neg_one_probability`), that probability is $1-(1-2^{-w})^s$. Subtracting it from one half and simplifying gives $(1-2^{-w})^s-\tfrac12$.

**Key facts.** `FABL.tribes_neg_one_probability`.
