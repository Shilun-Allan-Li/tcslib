<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassOracle/Classes.lean :: Complexity.P_subset_POracle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Time with an Oracle

**Claim.** For any binary oracle language $O$, every language decidable in polynomial time is decidable in polynomial time with oracle $O$: $\mathsf{P} \subseteq \mathsf{P}^{O}$.

**Proof.** Take $L \in \mathsf{P}$. By the definition of $\mathsf{P}$ as a union of polynomial-time bounds, there is an exponent and a time-bounded machine deciding $L$. Regard that machine as an oracle machine with oracle $O$. The conversion theorem states that, on every input, its oracle-machine computation within the same time bound is equivalent to its original computation (\(\texttt{Turing.FinTM.toFinOracleTM\_computesInTime}\)). Thus this oracle machine decides $L$ within the chosen polynomial bound, placing $L$ in $\mathsf{P}^{O}$.

**Key facts.** `Turing.FinTM.toFinOracleTM_computesInTime`.
