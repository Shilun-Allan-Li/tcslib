<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Equisat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cook–Levin Tableau Certificate Equivalence

**Claim.** Under the stated obliviousness and time-bound hypotheses, the tableau CNF at the specified producer horizon is satisfiable exactly when there is a string $u$ of the prescribed length for which $xu$ belongs to $V$.

**Proof.** Set $m=|x|+C(|x|+1)^e$, the length of a machine input consisting of $x$ followed by a certificate of the required length. The assumed decision-time bound implies that every string $y$ of length $m$ is decided by $M$ within the producer horizon: substituting $|y|=m$ into the time bound gives exactly that horizon. This supplies the uniform computation hypothesis needed by the tableau soundness and completeness results. If a certificate $u$ of the prescribed length has $xu\in V$, tableau completeness (`clA5Complete`) gives a satisfying assignment for the tableau CNF. Conversely, any satisfying assignment yields, by tableau soundness (`clA5Sound`), a certificate $u$ of that length with $xu\in V$. These two implications establish the equivalence.

**Key facts.** `Complexity.clA5Complete`, `Complexity.clA5Sound`.
