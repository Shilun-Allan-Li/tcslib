<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PAdviceSubsetPPoly.lean :: Complexity.PPoly_eq_iUnion_DTIMEAdvice_pow' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Polynomial Time as a Union of Advice Classes

**Claim.** The polynomial-size fan-in-two circuit class equals the union, over natural numbers $c,d$, of classes decidable in time $n^c+1$ with advice strings of length exactly $n^d$.

**Proof.** The preceding equality identifies languages with polynomial-size fan-in-two circuits as the union of the stated advice classes (\texttt{Complexity.PPoly_eq_iUnion_DTIMEAdvice_pow}). The circuit class is defined by that same polynomial circuit property, so the equality gives the result directly.

**Key facts.** `Complexity.PPoly_eq_iUnion_DTIMEAdvice_pow`.
