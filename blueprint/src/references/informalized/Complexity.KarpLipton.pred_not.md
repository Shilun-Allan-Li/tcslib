<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.KarpLipton.pred_not -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Languages Are Closed Under Complement

**Claim.** If the language defined by predicate $p$ belongs to $\mathsf{P}$, then its complement, defined by strings for which $p$ does not hold, also belongs to $\mathsf{P}$.

**Proof.** Apply closure of polynomial time under complement (`compl_mem_P`) to the language defined by $p$. Its complement consists exactly of strings satisfying $\neg p$, so the claimed language belongs to $\mathsf{P}$.

**Key facts.** `Complexity.compl_mem_P`.
