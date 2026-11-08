<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/Index.lean :: Nat.mul_add_le_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Plus Summand Bound

**Claim.** For natural numbers $a,b,m,n$, if $a<m$ and $b\le n$, then $an+b\le mn$.

**Proof.** From $b\le n$, adding $an$ to both sides gives $an+b\le an+n$. The right-hand side is $(a+1)n$, by distributivity. Since $a<m$, we have $a+1\le m$, so multiplying this inequality by the nonnegative number $n$ gives $(a+1)n\le mn$. Combining the two inequalities proves the result.
