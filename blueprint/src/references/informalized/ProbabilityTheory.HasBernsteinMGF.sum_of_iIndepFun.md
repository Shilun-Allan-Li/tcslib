<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Bernstein.lean :: ProbabilityTheory.HasBernsteinMGF.sum_of_iIndepFun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bernstein bound for independent sums

**Claim.** For a finite set of indices, the sum of independent random variables with individual Bernstein moment-generating-function bounds has a Bernstein bound whose quadratic parameter is the sum of the individual parameters and whose range parameter is unchanged.

**Proof.** Fix a parameter $t$ in the allowed range. Independence and the individual integrability assumptions imply integrability of the exponential of $t$ times the sum. Independence also factors the moment-generating function of the sum into the product of the individual moment-generating functions. Bound each factor by $\exp(c_i t^2)$ and multiply; the product is $\exp((\sum_i c_i)t^2)$. These two conclusions give the required integrability and moment-generating-function bound for the sum.
