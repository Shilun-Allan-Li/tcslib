<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.multinomial_const_le_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multinomial Coefficient Bound

**Claim.** For natural numbers $r$ and $k$, the multinomial coefficient with $r$ parts, each equal to $k$, is at most $r^{rk}$.

**Proof.** Consider the vector of counts that assigns $k$ to every one of the $r$ positions. Its entries sum to $rk$, so it is one term in the multinomial expansion of $(1+\cdots+1)^{rk}$, with $r$ summands. Each term in that expansion is nonnegative; consequently this particular multinomial coefficient is at most the whole sum. The whole sum is $r^{rk}$, proving the bound.
