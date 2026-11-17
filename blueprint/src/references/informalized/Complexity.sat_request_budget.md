<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_request_budget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Request Budget Inequality

**Claim.** For natural numbers $A,d,D,n,m$ with $d\le D$ and $m+1\le32(n+1)$, one has $A(m+1)^d\le A(32(n+1))^D$.

**Proof.** The base inequality $m+1\le32(n+1)$ implies $(m+1)^d\le(32(n+1))^d$ by monotonicity of natural-number powers in the base. Since $32(n+1)\ge1$ and $d\le D$, increasing the exponent gives $(32(n+1))^d\le(32(n+1))^D$. Multiplying the resulting inequality by the nonnegative number $A$ proves the claim.
