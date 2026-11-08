<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.KarpLipton.length_query -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nested pair encoding length

**Claim.** If $|u|=C(|x|+1)^c$ and $|e|=C(|x|+1)^c+1$, then the length of $\langle\langle x,u\rangle,e\rangle$ equals $q(C,c,x)$.

**Proof.** The length of a pair encoding is twice the length of its first component, plus two separator bits, plus the length of its second component (\texttt{Turing.length_pairEncode}). Apply this first to the inner pair and then to the outer pair, and substitute the assumed lengths of $u$ and $e$. The resulting expression is exactly the defining formula for $q(C,c,x)$.

**Key facts.** `Turing.length_pairEncode`.
