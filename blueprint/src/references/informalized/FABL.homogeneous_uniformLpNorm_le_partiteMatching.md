<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.homogeneous_uniformLpNorm_le_partiteMatching -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Homogeneous moment matching bound

**Claim.** For a Fourier-homogeneous function of degree $k$, its uniform $2r$-norm is at most the matching-count factor times its uniform $2$-norm, with the factor given by the $2r$-th root of the number of partite perfect matchings divided by $\sqrt{k!}$.

**Proof.** Write $C$ for the number of partite perfect matchings, $F=k!$, and $N=\|f\|_2$. Set $B=C^{1/(2r)}N/\sqrt F$, which is nonnegative. The homogeneous even-moment matching bound gives $\mathbb E f^{2r}\le (C/F^r) W_k(f)^r$, where $W_k(f)$ is the Fourier weight at level $k$. By the homogeneous Fourier-weight identity, $W_k(f)=N^2$. Hence the right side is $(C/F^r)N^{2r}=B^{2r}$. The even-moment identity for the uniform norm then yields $\|f\|_{2r}^{2r}\le B^{2r}$. Since both sides are nonnegative and $2r>0$, taking the $2r$-th root proves the claimed bound.

**Key facts.** `FABL.homogeneous_evenMoment_le_partiteMatching_count`, `FABL.fourierWeightAtLevel_eq_uniformLpNorm_two_sq_of_homogeneous`, `FABL.uniformLpNorm_even_pow_eq_expect_even`, `FABL.uniformLpNorm_nonneg`.
