<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSigmaEXP.lean :: Complexity.Meyer.solveSplit_self' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Polynomial Padding Split

**Claim.** For natural numbers $C,c,n$, the least index $i$ in the search range satisfying $i+C(i+1)^c=n+C(n+1)^c$ is $n$.

**Proof.** Let $F(j)=j+C(j+1)^c$. This function is strictly increasing: if $a<b$, then $(a+1)^c\le(b+1)^c$, so the polynomial term at $a$ is no larger than at $b$, while the first term increases strictly. The index $n$ belongs to the search range and satisfies the equation by definition of the target, so a solution exists. Any index $j$ returned by the search satisfies $F(j)=F(n)$; strict monotonicity makes $F$ injective, hence $j=n$. Therefore the search returns exactly $n$.
