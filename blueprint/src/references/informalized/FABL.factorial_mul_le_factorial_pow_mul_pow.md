<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.factorial_mul_le_factorial_pow_mul_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factorial Product Bound

**Claim.** For all natural numbers $r,k$, $(rk)!\le (k!)^r r^{rk}$.

**Proof.** Assign the value $k$ to each of the $r$ positions in the finite index set of size $r$. The multinomial formula expresses $(rk)!$ as the product of the $r$ individual factorials, $(k!)^r$, times the multinomial coefficient counting arrangements with these prescribed counts. That coefficient is at most $r^{rk}$: it counts some of the length-$rk$ words over an alphabet of $r$ symbols, of which there are $r^{rk}$ in total (the bound is `multinomial_const_le_pow`). Combining these identities and the bound gives $(rk)!\le (k!)^r r^{rk}$.

**Key facts.** `FABL.multinomial_const_le_pow`.
