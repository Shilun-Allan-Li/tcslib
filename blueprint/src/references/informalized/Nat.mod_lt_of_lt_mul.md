<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/Index.lean :: Nat.mod_lt_of_lt_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Remainder Bound from a Product Bound

**Claim.** For natural numbers $t,m,n$, if $t<mn$, then $t\bmod n<n$.

**Proof.** The hypothesis implies $t>0$, since $mn$ is strictly greater than $t$. Consequently $n>0$ as well: a product with right factor zero could not be greater than $t$. The standard remainder bound for a positive divisor states that $t\bmod n<n$, which proves the claim.
