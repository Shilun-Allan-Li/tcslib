<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/LinearThresholdInfluence.lean :: BooleanAnalysis.ThresholdFunctions.isLinearThreshold_affine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Linear Threshold Representation

**Claim.** For real coefficients $c$ and $a_i$, the function $x\mapsto\operatorname{sgn}(c+\sum_i a_i x_i)$ is a linear threshold function.

**Proof.** Use the affine multilinear polynomial whose constant coefficient is $c$, whose singleton coefficient at $i$ is $a_i$, and whose other coefficients vanish. The affine-degree lemma (`affinePoly_hasDegreeAtMost_one`) ensures that this polynomial has degree at most one. The degree-one evaluation formula (`MultilinearPolynomial.eval_of_degree_le_one`) says its value at each cube point is exactly $c+\sum_i a_i\,\mathrm{boolToSign}(x_i)$. Applying the threshold sign therefore gives the desired function, so this polynomial witnesses that the function is a linear threshold.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.affinePoly_hasDegreeAtMost_one`, `BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.eval_of_degree_le_one`.
