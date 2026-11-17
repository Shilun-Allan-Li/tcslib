<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.fixedCoordinateFrequencyLift_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonzero lifted frequency

**Claim.** Extending a nonzero frequency on the coordinates outside $J$ by zero on $J$ produces a nonzero frequency on all coordinates.

**Proof.** Suppose, to the contrary, that the lifted frequency is zero. For every frequency vector $z$ on the coordinates outside $J$, the dot product of the lifted frequency with the extension of $z$ to all coordinates equals the dot product of the original frequency $\gamma$ with $z$ (`f₂DotProduct_fixedCoordinateFrequencyLift`). The projection of that extension back to the coordinates outside $J$ is exactly $z$ (`fixedCoordinateProjectionLinear_fixedCoordinateExtension`); since the lift is zero, the dot product is therefore zero for every $z$. In particular, the linear functionals represented by $\gamma$ and by the zero frequency agree on every vector. The dot-product equivalence is injective, so this forces $\gamma=0$, contradicting the hypothesis.

**Key facts.** `FABL.f₂DotProduct_fixedCoordinateFrequencyLift`, `FABL.fixedCoordinateProjectionLinear_fixedCoordinateExtension`.
