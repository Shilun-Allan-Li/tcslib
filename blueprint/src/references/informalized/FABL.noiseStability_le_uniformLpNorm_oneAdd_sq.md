<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveApplications.lean :: FABL.noiseStability_le_uniformLpNorm_oneAdd_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Stability and Uniform Norms

**Claim.** For $0\le\rho\le1$, the noise stability of $f$ is at most $\|f\|_{1+\rho}^2$.

**Proof.** Let $r=\sqrt{\rho}$, so $r^2=\rho$. The $(p,2)$ hypercontractive inequality with $p=1+\rho$ gives $\|T_r f\|_2\le\|f\|_{1+\rho}$, since $r=\sqrt{p-1}$ (\texttt{pTwoHypercontractivity}). Squaring preserves this inequality because the norms are nonnegative (\texttt{uniformLpNorm_nonneg}); the squared $2$-norm is the uniform inner product of a function with itself (\texttt{uniformLpNorm_two_sq_eq_uniformInner}). By self-adjointness of the noise operator, this inner product equals $\langle f,T_r(T_r f)\rangle$. The composition rule gives $T_r(T_r f)=T_{r^2}f=T_\rho f$ (\texttt{uniformInner_noiseOperator_left}, \texttt{noiseOperator_comp}). Finally, stability is the inner product $\langle f,T_\rho f\rangle$ (\texttt{noiseStability_eq_uniformInner_noiseOperator}), so the squared hypercontractive inequality is exactly the asserted bound.

**Key facts.** `FABL.pTwoHypercontractivity`, `FABL.uniformLpNorm_nonneg`, `FABL.uniformLpNorm_two_sq_eq_uniformInner`, `FABL.uniformInner_noiseOperator_left`, `FABL.noiseOperator_comp`, `FABL.noiseStability_eq_uniformInner_noiseOperator`.
