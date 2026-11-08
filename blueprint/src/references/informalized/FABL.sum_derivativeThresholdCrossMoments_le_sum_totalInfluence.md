<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdInfluence.lean :: FABL.sum_derivativeThresholdCrossMoments_le_sum_totalInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cross moments and total influence

**Claim.** For the derivative threshold functions, the sum of the cross moments over ordered distinct coordinate pairs is at most the sum of their total influences.

**Proof.** Set $a(i,j)=I_j(g_i)$, where $g_i$ is the threshold function associated with the derivative in coordinate $i$. For each distinct pair $(i,j)$, the cross moment is at most $(a(i,j)+a(j,i))/2$, by the bound on a derivative-threshold cross moment (in `derivativeThresholdCrossMoment_le_half_influences`). Summing these inequalities gives an upper bound by the sum of these symmetric averages over all ordered distinct pairs. The sum of the transposed terms $a(j,i)$ equals the sum of $a(i,j)$ over the same pairs: swapping the two indices permutes the set of ordered distinct pairs, as expressed by `sum_erase_swap`. Thus the averaged sum equals the sum of $a(i,j)$ over distinct $j\ne i$. For each fixed $i$, this is bounded by the sum over all $j$, since the omitted diagonal terms $I_i(g_i)$ are nonnegative (`influence_nonneg`). Summing over $i$ gives the asserted bound by the sum of the total influences.

**Key facts.** `FABL.derivativeThresholdCrossMoment_le_half_influences`, `FABL.sum_erase_swap`, `FABL.influence_nonneg`.
