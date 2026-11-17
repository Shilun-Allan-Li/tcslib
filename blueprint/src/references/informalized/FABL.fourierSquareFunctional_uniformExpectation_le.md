<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/FourierSquareConvexity.lean :: FABL.fourierSquareFunctional_uniformExpectation_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convexity of the Fourier square functional

**Claim.** For nonnegative weights on Fourier subsets, the weighted sum of squared Fourier coefficients of the uniform average of a nonempty finite family is at most the uniform average of the individual weighted sums.

**Proof.** Give every member of the finite index set the weight equal to the reciprocal of its cardinality. These weights are nonnegative and sum to one. The functional is convex on the space of real-valued functions, by the convexity result for the Fourier square functional (`convexOn_fourierSquareFunctional`). Its finite convexity inequality therefore bounds its value at the weighted average of the functions by the same weighted average of their functional values. Pointwise, the weighted average of the functions is their uniform expectation; likewise, the weighted average of their functional values is the uniform expectation of those values. Substituting these identifications gives the claim.

**Key facts.** `FABL.convexOn_fourierSquareFunctional`.
