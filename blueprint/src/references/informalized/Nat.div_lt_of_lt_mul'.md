<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/Index.lean :: Nat.div_lt_of_lt_mul' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quotient Bound from a Product Bound

**Claim.** For natural numbers $t,m,n$, if $t<mn$, then $t/n<m$.

**Proof.** Rewrite the product as $mn$ using commutativity, so the hypothesis has the form $t<nm$. The standard quotient bound says that if $t$ is less than $n$ times a natural number, then dividing $t$ by $n$ gives a quotient less than that number. Applying it with quotient bound $m$ gives $t/n<m$.
