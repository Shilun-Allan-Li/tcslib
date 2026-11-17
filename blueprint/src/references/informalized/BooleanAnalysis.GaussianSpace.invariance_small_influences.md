<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance.lean :: BooleanAnalysis.GaussianSpace.invariance_small_influences -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small-influence invariance bound

**Claim.** Under the Basic Invariance Principle hypotheses, if the variance of the multilinear polynomial on the cube is at most one and each influence is at most $\epsilon$, then the difference between its two smoothed expectations is at most $(C/12)k9^k\epsilon$.

**Proof.** Apply the Basic Invariance Principle (\texttt{BooleanAnalysis.GaussianSpace.basic_invariance_principle}) to bound the absolute difference of expectations by $(C/12)9^k\sum_i \operatorname{Inf}_i(F)^2$. The polynomial’s degree hypothesis gives the required degree bound for its evaluation (\texttt{BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.has_degree_at_most_eval}). The variance bound and the coordinatewise influence bound then imply $\sum_i \operatorname{Inf}_i(F)^2\le k\epsilon$ by the sum-of-squared-influences estimate (\texttt{BooleanAnalysis.Hypercontractivity.sum_sq_influences_le_degree_mul}). Since the prefactor is nonnegative, substituting this estimate into the first bound and rearranging the real factors yields $(C/12)k9^k\epsilon$.

**Key facts.** `BooleanAnalysis.GaussianSpace.basic_invariance_principle`, `BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.has_degree_at_most_eval`, `BooleanAnalysis.Hypercontractivity.sum_sq_influences_le_degree_mul`.
