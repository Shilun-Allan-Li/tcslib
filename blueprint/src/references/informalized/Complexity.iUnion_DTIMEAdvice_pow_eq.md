<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Advice.lean :: Complexity.iUnion_DTIMEAdvice_pow_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Advice-Time Classes

**Claim.** The union over all $c,d\in\mathbb{N}$ of the classes decidable with advice of length $n^d$ in time a constant multiple of $n^c$ equals the union over all $d\in\mathbb{N}$ of the classes decidable with the same advice lengths in constant time up to a constant factor.

**Proof.** Take a language in the left-hand union, witnessed by exponents $c,d$. If $c=0$, then $n^c=1$ for every $n$, so the same witness places the language in the right-hand union at exponent $d$. If $c\ne0$, the supplied fact that the advice-time class for the bound $n^c$ is empty (`DTIMEAdvice_pow_eq_empty`) rules out this case. Conversely, a language in the right-hand union has a witness with advice exponent $d$ and time bound a constant multiple of $1$. Choose $c=0$ on the left; since $n^0=1$, this is the same time bound, so the language belongs to the left-hand union.

**Key facts.** `Complexity.DTIMEAdvice_pow_eq_empty`.
