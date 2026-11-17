<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PrimalityMath.lean :: Randomized.two_mul_card_eulerLiarSubgroup_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Euler liar subgroup size

**Claim.** For odd $N>1$ that is not prime, twice the cardinality of the Euler liar subgroup is at most $N$'s totient.

**Proof.** The subgroup is proper by the fact that it is not the whole unit group under the stated hypotheses ($\texttt{eulerLiarSubgroup_ne_top}$). Its index is therefore not $1$. The unit group is finite, so the subgroup's index is also nonzero; hence its integer index is at least $2$. The subgroup order times its index equals the order of the full unit group. That full order is $N$'s totient, so multiplying the subgroup cardinality by $2$ gives at most the product of its cardinality and index, namely the totient.

**Key facts.** `Randomized.eulerLiarSubgroup_ne_top`.
