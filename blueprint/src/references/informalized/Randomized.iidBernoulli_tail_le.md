<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ErrorReduction.lean :: Randomized.iidBernoulli_tail_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bernoulli Sum Tail Bound

**Claim.** For $k>0$, if the random variables $Y_1,\ldots,Y_k$ are independent and each has sub-Gaussian moment-generating-function parameter $(1/2)^2$ under the product distribution of Bernoulli-$p$ bits, then for every $t\ge0$ the probability that their sum is at least $tk$ is at most $\exp(-2t^2k)$.

**Proof.** Apply the sub-Gaussian tail inequality for a sum of independent random variables to the family $(Y_i)$, using the common parameter $(1/2)^2$ and threshold $tk$. Its nonnegativity follows from $t\ge0$ and $k\ge0$. The inequality bounds the event probability by the exponential of minus the squared threshold divided by twice the sum of the parameters. There are $k$ terms, so that sum is $k/4$; substituting the threshold gives $\exp(-(tk)^2/(2(k/4)))=\exp(-2t^2k)$. The measure-to-probability conversion is valid because the product measure is a probability measure.
