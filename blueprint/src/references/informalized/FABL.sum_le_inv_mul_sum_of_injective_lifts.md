<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.sum_le_inv_mul_sum_of_injective_lifts -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weight bound from injective lifts

**Claim.** If each source weight is copied to the images of its $m$ lifts under an injective map, and all target weights are nonnegative, then the sum of the source weights is at most $1/m$ times the sum of the target weights.

**Proof.** Fix $a\in A$. Since $m>0$, the fiber $[m]$ contains $0$, so the lift of $(a,0)$ has target weight $w(a)$. Nonnegativity of target weights therefore gives $w(a)\ge 0$. Injectivity of the lift identifies the sum of target weights over its image with the sum over all pairs $(a,i)$. This image is a subset of $B$, and every omitted target weight is nonnegative, so the sum over the lifted points is at most the sum over all of $B$. By the prescribed weight identity, the lifted sum is $\sum_{a\in A}\sum_{i\in[m]}w(a)=m\sum_{a\in A}w(a)$. Dividing this inequality by the positive number $m$ yields the stated bound.
