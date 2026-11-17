<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Resources.lean :: FABL.goldreichLevinQueryProgram_incorrectProbability_le_one_twentieth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Goldreich–Levin Output Failure Bound

**Claim.** The probability that the Goldreich–Levin query program produces a state failing any of the required active-set correctness and size conditions is at most $1/20$.

**Proof.** By the incorrectness-versus-estimate-failure bound (\texttt{goldreichLevinQueryProgram\_incorrectProbability\_le\_failureProbability}), the probability of an incorrect output is at most the probability that its trace contains an estimate with error at least $\tau^2/4$. The estimate-failure probability is at most $1/20$ by the query program failure bound (\texttt{goldreichLevinQueryProgram\_failureProbability\_le\_one\_twentieth}). Chaining these two inequalities proves the claim.

**Key facts.** `FABL.goldreichLevinQueryProgram_incorrectProbability_le_failureProbability`, `FABL.goldreichLevinQueryProgram_failureProbability_le_one_twentieth`.
