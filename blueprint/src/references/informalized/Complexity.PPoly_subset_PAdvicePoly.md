<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PPolyAdvice.lean :: Complexity.PPoly_subset_PAdvicePoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit languages have polynomial advice algorithms

**Claim.** Every language recognized by a polynomial-size, fan-in-two circuit family has a deterministic polynomial-time algorithm with polynomial-length advice, with advice length and running-time bounds of the stated forms.

**Proof.** Fix a language with circuit size at most $a(n+1)^k$. The circuit-to-advice theorem (`Complexity.mem_DTIMEAdvice_of_inSIZE`) gives a constant $c$ and an advice algorithm for this language, with advice length $(12a^2+1)(n+1)^{2k}$ and time bounded by a constant multiple of $n^c+1$. The inclusion of each such advice-time class in the union defining polynomial advice (`Complexity.DTIMEAdvice_subset_PAdvicePoly`) places the language in $	extsf{PAdvicePoly}$.

**Key facts.** `Complexity.mem_DTIMEAdvice_of_inSIZE`, `Complexity.DTIMEAdvice_subset_PAdvicePoly`.
