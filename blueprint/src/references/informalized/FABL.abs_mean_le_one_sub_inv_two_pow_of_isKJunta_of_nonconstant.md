<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.abs_mean_le_one_sub_inv_two_pow_of_isKJunta_of_nonconstant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean Bound for a Nonconstant Junta

**Claim.** If a Boolean sign function depends on at most $k$ coordinates and is nonconstant, then its uniform mean satisfies $|\mathbb E f|\leq 1-2^{-k}$.

**Proof.** If $k=0$, a function depending on no coordinates is constant, contradicting the nonconstancy hypothesis. Thus $k>0$. Put $g=2^{-k}$. The junta hypothesis bounds the Fourier degree of the real-valued sign function by $k$ (\(\texttt{FABL.fourierDegree_toReal_le_of_isKJunta}\)). The variance lower bound for a nonconstant Boolean function of Fourier degree at most $k$ gives $2^{-(k-1)}\leq\operatorname{Var}(f)$ (\(\texttt{FABL.inv_two_pow_pred_le_variance_of_fourierDegree_le}\)); since $2^{-(k-1)}=2g$, this says $2g\leq\operatorname{Var}(f)$. For a sign-valued function, its variance is $1-(\mathbb E f)^2$ (\(\texttt{FABL.variance_eq_four_mul_probabilities}\)). If the claimed bound failed, then $|\mathbb E f|>1-g$. As $0\leq g\leq1$, squaring yields $(\mathbb E f)^2>(1-g)^2$, and hence $\operatorname{Var}(f)<1-(1-g)^2=2g-g^2<2g$, contradicting the variance lower bound.

**Key facts.** `FABL.exists_eq_const_of_isKJunta_zero`, `FABL.fourierDegree_toReal_le_of_isKJunta`, `FABL.inv_two_pow_pred_le_variance_of_fourierDegree_le`, `FABL.variance_eq_four_mul_probabilities`.
