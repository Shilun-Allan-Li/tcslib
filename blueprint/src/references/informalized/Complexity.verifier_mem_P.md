<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NP.lean :: Complexity.verifier_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time indicators define P languages

**Claim.** If the one-bit indicator function of a language $V$ is polynomial-time computable, then $V$ belongs to $\mathsf{P}$.

**Proof.** Polynomial-time computability supplies a machine $M$ and natural numbers $C,c$ such that, on every input of length $n$, $M$ outputs the indicator of $V$ within time $C(n+1)^c$. The characterization of membership in $\mathsf{P}$ by such a deciding machine and a bound of this form then gives $V\in\mathsf{P}$ (\texttt{Complexity.mem_P_iff}).

**Key facts.** `Complexity.mem_P_iff`.
