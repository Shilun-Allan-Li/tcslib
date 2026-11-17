<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Resources.lean :: FABL.goldreichLevinQueryProgram_failureProbability_le_one_twentieth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Goldreich–Levin Failure Probability Bound

**Claim.** The probability that the Goldreich–Levin query program’s trace contains an estimate whose error is at least $\tau^2/4$ is at most $1/20$.

**Proof.** The stagewise failure estimate bounds the outer probability of a failed trace after $k$ stages by $k$ times the stage failure budget (\texttt{goldreichLevinQueryRunUpTo\_outerFailureProbability\_le}). At $k=n$, this gives an outer probability at most $n$ times the per-stage budget. The event probability is the real-valued version of this outer probability; since the bound is finite, monotonicity of the extended-real-to-real map transfers the inequality. The budget’s real value simplifies to $n$ times $2$ times the active-set cap times the call confidence. Finally, the rational failure-budget estimate (\texttt{goldreichLevinFailureBudget\_rat\_le\_one\_twentieth}) bounds the corresponding rational expression by $1/20$; embedding the rational inequality into the reals gives the claimed bound.

**Key facts.** `FABL.goldreichLevinQueryRunUpTo_outerFailureProbability_le`, `FABL.goldreichLevinFailureBudget_rat_le_one_twentieth`.
