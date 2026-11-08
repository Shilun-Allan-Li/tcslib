<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: hasSubgaussianMGF_id_rademacherReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rademacher Sub-Gaussian Bound

**Claim.** The identity function on the real line under the Rademacher measure has a sub-Gaussian moment-generating function with variance proxy $1$.

**Proof.** The Rademacher variable is measurable, has mean zero, and lies almost surely in the interval $[-1,1]$. The bounded, mean-zero sub-Gaussian estimate for a variable supported in an interval gives a variance proxy equal to one quarter of the square of the interval's length. Here that length is $2$, so the proxy is $2^2/4=1$.

**Key facts.** `rademacherReal_mem_Icc`, `integral_id_rademacherReal`.
