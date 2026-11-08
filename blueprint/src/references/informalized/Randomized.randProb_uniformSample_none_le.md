<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UniformSample.lean :: Randomized.randProb_uniformSample_none_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Sampling Failure

**Claim.** If $1\le N$, the probability that all $k$ blocks fail to produce a value less than $N$ is at most $(1/2)^k$.

**Proof.** By the exact failure-probability formula (`randProb_uniformSample_none`), the probability is the $k$th power of $(2^L-N)/2^L$, where $L=\mathrm{size}(N-1)$. The size bound (`le_two_pow_size_pred`) gives $N\le 2^L<2N$. Hence $2^L-N$ is nonnegative and at most $2^{L-1}$ in the corresponding rational inequality: equivalently, $2(2^L-N)\le 2^L$. Since $2^L>0$, this says $(2^L-N)/2^L\le 1/2$. Raising nonnegative quantities to the $k$th power preserves the inequality, yielding the result.

**Key facts.** `Randomized.randProb_uniformSample_none`, `Randomized.le_two_pow_size_pred`.
