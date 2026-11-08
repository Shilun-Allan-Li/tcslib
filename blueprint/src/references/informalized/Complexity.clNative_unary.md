<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clNative_unary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Unary Output

**Claim.** For all natural numbers $C$ and $e$, the function that sends $x$ to the word of exactly $C(|x|+1)^e$ copies of $1$ is polynomial-time computable.

**Proof.** A machine construction directly computes this unary-output function within $c(n+1)^{e+1}$ steps for some constant $c$. Take that machine and constant in the definition of polynomial-time computability, with exponent $e+1$. This is exactly the required polynomial time bound.

**Key facts.** `Turing.FinTM.computesFunInTime_polyUnary`.
