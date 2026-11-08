<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.strictCdfError_le_nonuniform -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonuniform Gaussian CDF error bound

**Claim.** If the difference between the distribution functions of a probability measure and the standard Gaussian is bounded by $K/(1+|y|^3)$ for every $y$, then the same bound holds for the difference of their measures of $(-\infty,x)$ at every $x$.

**Proof.** By the left-limit formula for strict half-lines, each measure of $(-\infty,x)$ equals the left limit of its distribution function at $x$ (\(`FABL.measureReal_Iio_eq_leftLim_cdf`\)). As $y$ approaches $x$ from below, monotonicity of both distribution functions ensures their difference converges to the difference of their left limits; taking absolute values preserves this convergence. Meanwhile, the function $y\mapsto K/(1+|y|^3)$ is continuous, so its limit is $K/(1+|x|^3)$. Passing the assumed pointwise inequality to these limits gives the desired bound, since the Gaussian distribution function is continuous from the left at $x$ (\(`FABL.gaussianReal_cdf_leftLim`\)).

**Key facts.** `FABL.measureReal_Iio_eq_leftLim_cdf`, `FABL.gaussianReal_cdf_leftLim`.
