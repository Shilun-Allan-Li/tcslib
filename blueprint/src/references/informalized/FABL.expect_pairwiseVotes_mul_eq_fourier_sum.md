<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/Arrow.lean :: FABL.expect_pairwiseVotes_mul_eq_fourier_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pairwise vote Fourier sum

**Claim.** For two distinct pairwise contests, the average over ranking profiles of the product of the two cube functions evaluated on the corresponding vote vectors is the sum of $(-1/3)^{|S|}\widehat f(S)\widehat g(S)$ over all subsets $S$.

**Proof.** Expand each cube function in its Fourier basis (`fourier_expansion`). Multiplying the two finite sums produces terms indexed by pairs $(S,T)$, with the corresponding coefficient factors and monomials on the two vote vectors. Average term by term and sum first over $T$. The expected product of those monomials is zero unless $S=T$, and when $S=T$ it is $(-1/3)^{|S|}$ (`expect_monomial_pairwiseVotes_mul`). Thus only the diagonal terms remain, giving the stated sum.

**Key facts.** `FABL.fourier_expansion`, `FABL.expect_monomial_pairwiseVotes_mul`.
