<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Add_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Addition Closure

**Claim.** If the unary words for $f(x)$ and $g(x)$ are polynomial-time computable, then the unary word for $f(x)+g(x)$ is polynomial-time computable.

**Proof.** Apply the polynomial-time closure under concatenation (`Complexity.clNative_append`) to the two unary-output functions. Their concatenated output consists of $f(x)+g(x)$ copies of $1$, by the list identity that concatenating these two replicated words gives the replication of their sum.

**Key facts.** `Complexity.clNative_append`.
