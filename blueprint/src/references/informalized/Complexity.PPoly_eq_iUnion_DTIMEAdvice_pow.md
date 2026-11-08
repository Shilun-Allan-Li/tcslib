<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PAdviceSubsetPPoly.lean :: Complexity.PPoly_eq_iUnion_DTIMEAdvice_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Circuit Size as a Union of Advice Classes

**Claim.** A Boolean language has fan-in-two circuits of size at most $a(n+1)^k$ for some natural numbers $a,k$ exactly when it belongs to one of the advice classes with computation bound $n^c+1$ and advice length exactly $n^d$, for some natural numbers $c,d$.

**Proof.** Unpack the equality as a membership equivalence. In the forward direction, a size bound of the form $a(n+1)^k$ supplies a circuit family whose language is the given language; the circuit-to-advice simulation yields exponents $c,d$ for which the language is decidable in time $n^c+1$ with advice of length exactly $n^d$ (\texttt{Complexity.mem_DTIMEAdvice_pow_of_inSIZE}). In the reverse direction, suppose the language has such an advice-time decider. Its advice length satisfies $n^d\le(n+1)^d$, since $n\le n+1$. The advice-to-circuit simulation, with size constant $C=1$, then produces polynomial-size fan-in-two circuits for the language (\texttt{Complexity.mem_PPoly_of_mem_DTIMEAdvice}). These two directions establish the equality with the union over $c,d$.

**Key facts.** `Complexity.mem_DTIMEAdvice_pow_of_inSIZE`, `Complexity.mem_PPoly_of_mem_DTIMEAdvice`.
