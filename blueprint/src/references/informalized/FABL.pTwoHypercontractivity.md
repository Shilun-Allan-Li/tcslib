<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.pTwoHypercontractivity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-norm hypercontractivity

**Claim.** For $1\le p\le2$, applying the noise operator with parameter $\sqrt{p-1}$ to $f$ does not increase its uniform $L^p$ norm when measured in the uniform $L^2$ norm.

**Proof.** Set $\rho=\sqrt{p-1}$. First, $\rho^2=p-1$. The square of the uniform $L^2$ norm of the smoothed function equals its uniform inner product with itself. By self-adjointness of the noise operator, this inner product can be moved onto the second factor, giving $\langle f,T_\rho(T_\rho f)\rangle$. The composition law for noise operators identifies the iterated operator as $T_{\rho^2}$, so the expression is $\langle f,T_{p-1}f\rangle$. The noise-stability bound says this is at most $\|f\|_p^2$. Since both norms are nonnegative, taking square roots yields the desired inequality.

**Key facts.** `FABL.uniformLpNorm_two_sq_eq_uniformInner`, `FABL.uniformInner_noiseOperator_left`, `FABL.noiseOperator_comp`, `FABL.noiseStability_pSubOne_le_uniformLpNorm_sq`, `FABL.uniformLpNorm_nonneg`.
