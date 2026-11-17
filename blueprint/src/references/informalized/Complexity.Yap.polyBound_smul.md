<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Yap.lean :: Complexity.Yap.polyBound_smul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Bound Under Scaling

**Claim.** If $f$ is polynomially bounded, then $n\mapsto qf(n)$ is polynomially bounded for each natural number $q$.

**Proof.** Let $f(n)\le A(n+1)^\alpha$ be a polynomial bound. Multiplication by the nonnegative integer $q$ preserves the inequality, yielding $qf(n)\le qA(n+1)^\alpha$. Hence coefficient $qA$ and exponent $\alpha$ give a polynomial bound for the scaled function.
