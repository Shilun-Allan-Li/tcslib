<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.card_partitePerfectMatching_le_factorial_bound_printed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factorial Matching Bound

**Claim.** The number of perfect matchings on $2r$ parts of size $k$ is at most $((2r-1)/r)^{rk}((rk)!)^2$.

**Proof.** First apply the stronger bound (`FABL.card_partitePerfectMatching_le_factorial_bound_strong`), which gives $((2r-1)/r)^{rk}(rk)!$. Since $(rk)!ge 1$, we have $(rk)!le ((rk)!)^2$. The other factor is nonnegative, so multiplying this factorial inequality by it preserves the order and yields the claimed bound.

**Key facts.** `FABL.card_partitePerfectMatching_le_factorial_bound_strong`.
