<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.sum_range_two_mul_add_one_eq_sum_even -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd-Zero Sum Reduces to Even Terms

**Claim.** If $F(2j+1)=0$ for every $j<r$, then the sum of $F(j)$ for $0\le j<2r+1$ equals the sum of $F(2j)$ for $0\le j<r+1$.

**Proof.** Proceed by induction on $r$. At $r=0$, both sums contain only $F(0)$. For the step from $r$ to $r+1$, extend the left sum through the two new indices $2r+1$ and $2r+2$. The hypothesis gives $F(2r+1)=0$, since $r<r+1$. The induction hypothesis rewrites the earlier part as the sum of even-indexed terms through $F(2r)$; adjoining $F(2r+2)=F(2(r+1))$ gives exactly the even-indexed sum through the new endpoint.
