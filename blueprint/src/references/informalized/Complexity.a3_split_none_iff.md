<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_split_none_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failure of the split search

**Claim.** The exponential-split search fails exactly when there is no natural number $n$ satisfying $n+C\cdot 2^{(n+1)^c}=m$.

**Proof.** The search scans the finite list of natural numbers below $m+1$ and returns the first one satisfying the displayed equation. If it fails, then no member of that list satisfies the equation. Any natural number satisfying the equation is less than or equal to $m$, since the other summand is nonnegative, so it belongs to the scanned list. Thus failure rules out every possible solution. Conversely, if there is no solution, then in particular no member of the scanned list satisfies the equation, and the search returns no value.
