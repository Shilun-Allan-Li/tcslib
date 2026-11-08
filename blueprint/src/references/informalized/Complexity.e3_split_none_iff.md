<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.e3_split_none_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failure criterion for split search

**Claim.** The exponential split search at length $m$ returns no value exactly when there is no natural number $n$ satisfying $n+C\cdot 2^{(n+1)^c}=m$.

**Proof.** By the characterization of `List.find?` returning `none`, this happens exactly when no member of the search list passes its test. If such an $n$ satisfies the equation, then $n<m+1$, since the added term is nonnegative, so $n$ belongs to `List.range (m+1)`; the test succeeds there. Conversely, any list member passing the test supplies an $n$ satisfying the equation. Thus the search returns `none` precisely when no such $n$ exists.
