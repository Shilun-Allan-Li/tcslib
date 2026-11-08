<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.distanceToAffineSigns_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distance and Fourier Norm

**Claim.** For a sign-valued function $f$, its distance to the affine sign functions is $\frac12-\frac12\|\widehat f\|_\infty$.

**Proof.** Choose a Fourier index $\gamma$ at which the maximum absolute Fourier coefficient is attained. Choose a sign $\sigma$ whose value has the sign of that coefficient, so that $\operatorname{signValue}(\sigma)\widehat f(\gamma)=|\widehat f(\gamma)|$ (`exists_signValue_mul_eq_abs`). The distance to this particular affine sign function is $\frac12-\frac12|\widehat f(\gamma)|$, by the formula for distance to an affine sign function (`relativeHammingDist_affineSignFunction`). Since the distance to the family is an infimum, this gives the upper bound by $\frac12-\frac12\|\widehat f\|_\infty$.\n\nFor the reverse bound, consider any affine sign function with parameters $(\sigma,\gamma)$. Its distance from $f$ is $\frac12-\frac12\operatorname{signValue}(\sigma)\widehat f(\gamma)$. The absolute coefficient is at most the maximum Fourier magnitude, and $\operatorname{signValue}(\sigma)$ is either $-1$ or $1$ (`signValue_eq_neg_one_or_one`), so the signed coefficient is at most that maximum. Therefore every such distance is at least $\frac12-\frac12\|\widehat f\|_\infty$. Taking the infimum gives the reverse bound, and hence equality.

**Key facts.** `FABL.exists_signValue_mul_eq_abs`, `FABL.relativeHammingDist_affineSignFunction`, `FABL.signValue_eq_neg_one_or_one`.
