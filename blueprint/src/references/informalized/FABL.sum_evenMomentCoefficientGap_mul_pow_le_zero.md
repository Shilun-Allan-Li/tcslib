<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveMomentSharpness.lean :: FABL.sum_evenMomentCoefficientGap_mul_pow_le_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even-moment coefficient gap

**Claim.** Under the stated second-moment, odd-moment, and hypercontractivity assumptions, the weighted sum of even-moment coefficient gaps is nonpositive for every real $t$.

**Proof.** Apply the affine even-moment consequence of hypercontractivity (`affine_evenMoment_le_of_hypercontractive`) to obtain $\mathbb{E}[(1+\rho tX)^{2r}]\le (1+t^2)^r$. Expand the left side using the vanishing odd moments (`pmfExpectation_affine_evenMoment_of_oddMoments`): it becomes the sum, over $0\le l\le r$, of $\binom{2r}{2l}\rho^{2l}t^{2l}\mathbb{E}[X^{2l}]$. By the binomial theorem, $(1+t^2)^r$ is the sum over the same range of $\binom rl t^{2l}$. Subtracting the latter sum from the former gives exactly the claimed sum of coefficient gaps: use $(\rho t)^{2l}=\rho^{2l}t^{2l}$ to group each term. The affine-moment inequality says this difference is at most zero.

**Key facts.** `FABL.affine_evenMoment_le_of_hypercontractive`, `FABL.pmfExpectation_affine_evenMoment_of_oddMoments`.
