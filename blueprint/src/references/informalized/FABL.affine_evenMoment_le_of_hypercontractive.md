<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveMomentSharpness.lean :: FABL.affine_evenMoment_le_of_hypercontractive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine even-moment bound

**Claim.** If the normalized random variable has mean zero and second moment one, and its affine functions satisfy the stated two-norm hypercontractive inequality, then for every real $t$, the even moment of $1+\rho tX$ of order $2r$ is at most $(1+t^2)^r$.

**Proof.** The odd-moment hypothesis at order one gives $\mathbb E[X]=0$. Apply the assumed hypercontractive inequality with affine parameters $a=1$ and $b=t$, then raise both nonnegative sides to the power $2r$. By the even-power norm identity ($\texttt{pmfLpNorm_even_pow_eq_pmfExpectation_even}$), the left side becomes $\mathbb E[(1+\rho tX)^{2r}]$. The centered affine second-norm formula ($\texttt{pmfLpNorm_two_affine_centered}$), using the zero mean and unit second moment, identifies the right norm as $\sqrt{1+t^2}$. Its $2r$-th power is $(1+t^2)^r$, since $1+t^2\ge0$. This yields the claimed bound.

**Key facts.** `FABL.pmfLpNorm_even_pow_eq_pmfExpectation_even`, `FABL.pmfLpNorm_two_affine_centered`.
