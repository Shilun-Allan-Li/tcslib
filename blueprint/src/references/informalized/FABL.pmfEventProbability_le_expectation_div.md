<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.pmfEventProbability_le_expectation_div -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Markov Bound for a Finite Distribution

**Claim.** For a pointwise nonnegative function $Y$ and $a>0$, the probability that $Y\ge a$ is at most $\mathbb E_p[Y]/a$.

**Proof.** The weighted event bound states that $a$ times the probability of the event $Y\ge a$ is at most the expectation of $Y$, provided $Y$ is pointwise nonnegative (\texttt{mul_pmfEventProbability_le_expectation}). Since $a>0$, division by $a$ preserves the inequality and gives the claimed bound.

**Key facts.** `FABL.mul_pmfEventProbability_le_expectation`.
