<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.relativeHammingDist_affineSignFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distance to an Affine Sign Function

**Claim.** If $f$ is sign-valued, then for every sign $\sigma$ and binary vector $\gamma$, its relative Hamming distance from the affine sign function determined by them is $\frac12-\frac{\operatorname{signValue}(\sigma)}2\widehat f(\gamma)$.

**Proof.** First express relative Hamming distance as the uniform probability that the two functions differ (`FABL.uniformProbability_ne_eq_relativeHammingDist`). Since both values are signs, pointwise the disagreement indicator equals $(1-f(x)\,a(x))/2$, where $a$ is the affine sign function: the product is $1$ when they agree and $-1$ when they differ. The affine sign function is sign-valued (`FABL.isSignValued_affineSignFunction`), and its evaluation is $\operatorname{signValue}(\sigma)$ times the Walsh character (`FABL.affineSignFunction_apply`). Averaging the product $f(x)a(x)$ therefore gives $\operatorname{signValue}(\sigma)$ times the Fourier coefficient, by the expectation formula for that coefficient (`FABL.vectorFourierCoeff_eq_expect`). Finally, the uniform expectation of $1$ is $1$, so averaging $(1-f(x)a(x))/2$ gives the claimed expression.

**Key facts.** `FABL.uniformProbability_ne_eq_relativeHammingDist`, `FABL.isSignValued_affineSignFunction`, `FABL.affineSignFunction_apply`, `FABL.vectorFourierCoeff_eq_expect`.
