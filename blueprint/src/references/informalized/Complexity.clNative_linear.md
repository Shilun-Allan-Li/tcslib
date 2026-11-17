<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clNative_linear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear Time Implies Polynomial Time

**Claim.** If a finite Boolean Turing machine computes $f$ within $a(n+1)$ steps on every input of length $n$, then $f$ is polynomial-time computable.

**Proof.** Choose the machine $M$ and constant $a$ supplied by the hypothesis. In the definition of polynomial-time computability, use this same machine, take the multiplicative constant to be $a$, and take the exponent to be $1$. The resulting time bound is $a(n+1)^1=a(n+1)$, exactly the assumed bound, so $M$ computes $f$ within the required polynomial time.
