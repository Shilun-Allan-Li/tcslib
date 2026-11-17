<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_split_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Specification of a successful split

**Claim.** If the exponential-split search on $(C,c,m)$ returns $n$, then $n\le m$ and $n+C\cdot 2^{(n+1)^c}=m$.

**Proof.** A value returned by the search occurs in the scanned list, whose elements are strictly less than $m+1$; hence $n\le m$. The search returns a value only when that value passes its defining test, which is precisely the equation $n+C\cdot 2^{(n+1)^c}=m$.
