<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.uniformProbability_andFunction_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of a positive AND output

**Claim.** For every $w\ge0$, the uniform probability that the AND function outputs $1$ is $1-2^{-w}$.

**Proof.** The AND function takes only the two sign values $1$ and $-1$, so the probabilities of these two outputs sum to $1$ (\texttt{FABL.uniformProbability_one_add_neg_one_eq_one}). The probability of output $-1$ is $2^{-w}$ (\texttt{FABL.uniformProbability_andFunction_eq_neg_one}). Subtracting this from $1$ gives the probability of output $1$, namely $1-2^{-w}$.

**Key facts.** `FABL.uniformProbability_one_add_neg_one_eq_one`, `FABL.uniformProbability_andFunction_eq_neg_one`.
