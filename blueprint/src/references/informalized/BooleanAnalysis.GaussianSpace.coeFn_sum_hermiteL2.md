<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Truncation.lean :: BooleanAnalysis.GaussianSpace.coeFn_sum_hermiteL2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pointwise representative of a finite Hermite sum

**Claim.** Under standard Gaussian measure, the function represented in $L^2$ by the finite sum of Hermite functions with coefficients $c_\alpha$ agrees almost everywhere with the corresponding pointwise sum.

**Proof.** Induct on the finite set of indices. For the empty set, both sums are zero, and the zero element of $L^2$ has zero almost-everywhere representative. For an insertion of an index $\alpha$ not already in the set, the new sum is the old sum plus $c_\alpha$ times the $L^2$ element represented by the Hermite function at $\alpha$. Almost everywhere, the representative of an $L^2$ sum is the sum of representatives, and scalar multiplication acts pointwise. The representative of the Hermite element is the Hermite function itself because that function belongs to $L^2$ (hermiteFunction_memLp_two). Combining these facts with the induction hypothesis identifies the new representative with the pointwise sum over the enlarged set.

**Key facts.** `BooleanAnalysis.GaussianSpace.hermiteFunction_memLp_two`.
