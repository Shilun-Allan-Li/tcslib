<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractivityExercises.lean :: FABL.lowDegree_uniformLpNorm_two_le_weak -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-degree norm comparison

**Claim.** If $1<p<2$ and $f$ has Fourier degree at most $k$, then its uniform $L^2$ norm is at most $(p-1)^{-k/2}$ times its uniform $L^p$ norm.

**Proof.** Let $r=p/(p-1)$, the Hölder conjugate of $p$. The assumption $p>1$ ensures this is defined, and $p<2$ implies $r\ge2$. The degree truncation operator, which keeps only Fourier terms of degree at most $k$, satisfies an $L^2$-to-$L^r$ bound with constant $\sqrt{r-1}^{\,k}$ (`degreeTruncation_norm_le_two_of_two_le`). It is self-adjoint for the uniform inner product (`degreeTruncation_selfAdjoint`), so duality transfers that bound to an $L^p$-to-$L^2$ bound with the same constant (`selfAdjoint_dual_bound`). Because $f$ has degree at most $k$, truncating it leaves it unchanged (`degreeTruncation_eq_self_of_fourierDegree_le`). Finally, $r-1=(p-1)^{-1}$, so $\sqrt{r-1}=(p-1)^{-1/2}$, giving the claimed inequality.

**Key facts.** `FABL.degreeTruncation_norm_le_two_of_two_le`, `FABL.degreeTruncation_selfAdjoint`, `FABL.selfAdjoint_dual_bound`, `FABL.degreeTruncation_eq_self_of_fourierDegree_le`.
