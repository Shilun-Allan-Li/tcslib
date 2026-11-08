<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.isDualFourierGranular_signValue_of_finrank_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Granularity in Positive Dimension

**Claim.** If $V$ is a finite-dimensional vector space over $\mathbb F_2$ of positive dimension and $f:V\to\{-1,1\}$, then every dual Fourier coefficient of its real-valued version is an integer multiple of $2(1/2)^{\dim V}$.

**Proof.** Fix a dual functional $\psi$. At each $x\in V$, its Walsh character is $1$ when $\psi(x)=0$ and $-1$ when $\psi(x)\ne0$: the latter follows because the only nonzero element of $\mathbb F_2$ is $1$ and `binarySign_one` gives character value $-1$ there. Also, `signValue_eq_neg_one_or_one` says the value of $f$ is either $-1$ or $1$. Consequently the pointwise product of $f(x)$ and the Walsh character takes only the values $-1$ and $1$. The positive dimension assumption gives $1\le \dim V$, and the finite-vector-space cardinality formula gives $|V|=2^{\dim V}$. Applying `expect_sign_values_eq_int_mul_two_inv_pow` to that pointwise product shows its uniform average is an integer multiple of $2(1/2)^{\dim V}$. Finally, `dualFourierCoeff_eq_expect` identifies this average with the dual Fourier coefficient, and `degreeFourierGranularity_cast` identifies the displayed scale with the claimed granularity.

**Key facts.** `FABL.signValue_eq_neg_one_or_one`, `FABL.dualWalshCharacter_apply`, `FABL.binarySign_one`, `FABL.expect_sign_values_eq_int_mul_two_inv_pow`, `FABL.dualFourierCoeff_eq_expect`, `FABL.degreeFourierGranularity_cast`.
