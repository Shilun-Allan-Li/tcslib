<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.lemma4_21 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier concentration from restriction tails

**Claim.** For a Boolean function $f$, a restriction parameter $0<\delta\leq1$, and a positive integer $k$, the Fourier weight above degree $3k/\delta$ is at most three times the probability that the restricted decision tree has depth at least $k$.

**Proof.** Write the weighted intersection-tail sum as the sum over all coordinate sets $U$ of the probability that the random restriction leaves at least $k$ coordinates of $U$ free, multiplied by $\widehat f(U)^2$. The identity equating this sum to the expected restricted Fourier weight at degrees at least $k$ is the expected restricted Fourier weight formula (`expect_restrictedFourierWeightAtLeast_eq_sum_intersectionTail`). The expected restricted weight is at most the switching-failure probability, by the comparison of restricted Fourier weight with decision-tree failure (`expect_restrictedFourierWeightAtLeast_le_switchingFailureProbability`).

For each $U$ with $3k/\delta<|U|$, the intersection-tail estimate gives a weight of at least $1/3$ (`one_third_le_deltaRandomIntersectionTail`). Multiplying by the nonnegative square $\widehat f(U)^2$ and summing over these sets shows that one third of the Fourier weight above the cutoff is bounded by the full weighted intersection-tail sum. Extending this restricted sum to all coordinate sets is valid because every added term is nonnegative; nonnegativity of the intersection-tail weights is supplied by `deltaRandomIntersectionTail_nonneg`. Combining the upper and lower bounds and multiplying by $3$ proves the claimed concentration estimate.

**Key facts.** `FABL.expect_restrictedFourierWeightAtLeast_eq_sum_intersectionTail`, `FABL.expect_restrictedFourierWeightAtLeast_le_switchingFailureProbability`, `FABL.one_third_le_deltaRandomIntersectionTail`, `FABL.deltaRandomIntersectionTail_nonneg`.
