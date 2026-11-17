<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/PrimeFind.lean :: Complexity.BinArith.lovaszBits_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lovász bit count bound

**Claim.** For every natural number $n$, the ceiling of the base-$2$ logarithm of $2n$ is at most $n+1$.

**Proof.** By the characterization of the natural logarithmic ceiling, it suffices to show $2n\le 2^{n+1}$. Write the right side as $2\cdot 2^n$. The standard inequality $n<2^n$ for natural numbers gives $2n<2\cdot2^n$, and hence the required weak inequality.
