<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/MatchingMath.lean :: Randomized.Matching.matchMono_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Matching Monomials

**Claim.** The assignment from a permutation to its matching monomial is injective.

**Proof.** Suppose two permutations $\sigma$ and $\tau$ give the same monomial. Fix any index $a$ and inspect the exponent at the pair $(a,\sigma(a))$. For the monomial of $\sigma$ this exponent is $1$. Equality of the monomials makes the corresponding exponent for $\tau$ also $1$. By the entry formula for matching monomials (`matchMono_apply`), this means $\tau(a)=\sigma(a)$. Since this holds for every $a$, the permutations agree.

**Key facts.** `Randomized.Matching.matchMono_apply`.
