<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a3n_poly_linear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear Time Implies Polynomial Time

**Claim.** If a finite Turing machine computes $f$ in time $a(n+1)$ on every input of length $n$, for some natural number $a$, then $f$ is polynomial-time computable.

**Proof.** Use the given machine and choose polynomial exponent $1$. For every input length $n$, the linear bound $a(n+1)$ is exactly $a(n+1)^1$, so it is a polynomial-time bound.
