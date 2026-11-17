<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Advice.lean :: Complexity.mem_PAdvicePoly_of_le_allOnes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Advice for All-Ones Languages

**Claim.** If every word in a language consists entirely of ones, then the language belongs to polynomial time with polynomial-length advice.

**Proof.** The all-ones advice construction (`Complexity.mem_DTIMEAdvice_one_of_le_allOnes`) supplies a machine deciding the language with advice of length exactly $n+1$ on inputs of length $n$, in time bounded by a constant multiple of $n+1$. The general inclusion from polynomially bounded advice time into polynomial advice time (`Complexity.DTIMEAdvice_subset_PAdvicePoly`) applies with polynomial-time exponent $1$, advice bound $1\cdot(n+1)^1$, and advice-length exponent $0$. These parameters express the supplied advice length as $1\cdot(n+1)^1$ and its running-time bound as a constant multiple of $n^1+1$. Hence the language lies in $\mathsf{PAdvicePoly}$.

**Key facts.** `Complexity.mem_DTIMEAdvice_one_of_le_allOnes`, `Complexity.DTIMEAdvice_subset_PAdvicePoly`.
