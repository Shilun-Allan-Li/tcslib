<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.standardGaussian_measureReal_Ioo_eq_integral -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Measure of an Open Interval

**Claim.** For all real numbers $a$ and $b$, the standard Gaussian measure of $(a,b)$ equals the integral of its density over that interval: $\gamma((a,b))=\int_{(a,b)}\varphi(x)\,dx$.

**Proof.** The standard Gaussian measure of a measurable set is given by integrating its Gaussian density over that set (`gaussianReal_apply_eq_integral`). Applying this formula to $(a,b)$ and taking the real-valued measure gives the desired integral. The conversion from the extended-real integral is valid because the density is nonnegative, so the integral is nonnegative.
