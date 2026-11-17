<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/Index.lean :: Nat.mul_add_lt_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict Product Plus Summand Bound

**Claim.** For natural numbers $a,b,m,n$, if $a<m$ and $b<n$, then $an+b<mn$.

**Proof.** Apply the natural-number product-and-sum inequality for two strict bounds to $a<m$ and $b<n$, obtaining $na+b<mn$. Since multiplication of natural numbers is commutative, $na=an$, which gives the claimed inequality.
