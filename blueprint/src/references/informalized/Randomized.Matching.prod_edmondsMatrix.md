<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/MatchingMath.lean :: Randomized.Matching.prod_edmondsMatrix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Along a Permutation

**Claim.** The product of the Edmonds matrix entries in positions $(i,\sigma(i))$ is the monomial with coefficient $1$ and exponent vector having exponent $1$ at each pair $(i,\sigma(i))$ if every corresponding entry of $A$ is true, and is zero otherwise.

**Proof.** Split according to whether $A(i,\sigma(i))$ is true for every $i$. If all are true, each factor in the product is the variable $X_{(i,\sigma(i))}$. The product of these variables is the monomial whose exponent vector is the sum of the single-coordinate exponent vectors, namely $\mathrm{matchMono}(\sigma)$, and whose coefficient is $1$. If some entry is false, choose an index $i$ where it is false. The corresponding Edmonds matrix factor is zero, so the whole product is zero.
