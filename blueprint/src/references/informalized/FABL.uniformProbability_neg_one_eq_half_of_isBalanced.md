<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.uniformProbability_neg_one_eq_half_of_isBalanced -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Balanced functions have equal sign probabilities

**Claim.** If a Boolean sign-valued function is balanced, then its uniform probability of taking value $-1$ is $1/2$.

**Proof.** Balance implies that the probability of the value $1$ is $1/2`, by the equivalence between balance and this probability identity (`FABL.isBalanced_iff_uniformProbability_one_eq_half`). The probabilities of the two possible signs sum to $1$ (`FABL.uniformProbability_one_add_neg_one_eq_one`). Subtracting the probability of $1$ therefore gives probability $1/2$ for the value $-1$.

**Key facts.** `FABL.isBalanced_iff_uniformProbability_one_eq_half`, `FABL.uniformProbability_one_add_neg_one_eq_one`.
