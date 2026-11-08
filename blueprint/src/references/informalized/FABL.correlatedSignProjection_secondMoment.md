<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/CorrelatedGaussianLimit.lean :: FABL.correlatedSignProjection_secondMoment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Moment of the Correlated Sign Projection

**Claim.** For every $\rho\in[-1,1]$ and every vector $t=(t_1,t_2)$ in the real two-dimensional correlation plane, the expected square of $Xt_1+Yt_2$ under the correlated sign-pair law with parameter $\rho$ is $t_1^2+2\rho t_1t_2+t_2^2$.

**Proof.** Write $a=t_1$ and $b=t_2$. Since each sign is either $-1$ or $1$, expanding $(Xa+Yb)^2$ gives $a^2+2abXY+b^2$: the identities $X^2=Y^2=1$ account for the two square terms. Take expectations term by term. The constant terms retain their values, while the mixed term uses the correlated-sign product mean $\mathbb E[XY]=\rho$ (`correlatedSignPairPMF_expect_signValue_mul`). The result is $a^2+2ab\rho+b^2$, which is the stated quadratic form after rearranging factors.

**Key facts.** `FABL.signValue_eq_neg_one_or_one`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_const_mul`, `FABL.correlatedSignPairPMF_expect_signValue_mul`.
