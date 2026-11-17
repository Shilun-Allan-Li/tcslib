<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.homogeneous_uniformLpNorm_le_sqrt_two_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-degree norm bound

**Claim.** If the Fourier degree of $f$ is at most $k$, then $\|f\|_{2r}\le \sqrt{2r}^{\,k}\|f\|_2$ for positive integer $r$.

**Proof.** Since $r>0$, we have $2\le 2r$. The low-degree uniform norm estimate (FABL.lowDegree_uniformLpNorm_le), applied with exponent $q=2r$, first gives $\|f\|_{2r}\le \sqrt{2r-1}^{\,k}\|f\|_2$. Also $0\le 2r-1\le 2r$, so monotonicity of the square root gives $\sqrt{2r-1}\le\sqrt{2r}$. Raising these nonnegative quantities to the integer power $k$ preserves the inequality; multiplying by the nonnegative norm $\|f\|_2$ completes the comparison.

**Key facts.** `FABL.lowDegree_uniformLpNorm_le`, `FABL.uniformLpNorm_nonneg`.
