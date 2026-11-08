<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/GaussianBobkov.lean :: BooleanAnalysis.GaussianSpace.bobkov_normalizedBoolBlocks_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bobkov Bound for Normalized Boolean Blocks

**Claim.** For a $[0,1]$-valued differentiable function with globally Lipschitz derivative, the closed Gaussian profile of its expectation over normalized Boolean blocks is bounded by the expected derivative expression plus the stated error term.

**Proof.** For each Boolean array, let $z$ be its vector of normalized block sums and apply the Bobkov inequality for Boolean arrays to the function $x\mapsto f(z(x))$. For a fixed array, changing one bit in block $i$ changes the normalized vector by a signed step of size $2/\sqrt m$ in coordinate $i$. The derivative formula and the global Lipschitz bound on $D$ imply that the resulting half-difference of function values differs from $D(z)(e_i)/\sqrt m$ by at most $2C/m$ (`abs_normalizedBoolBlocks_half_difference_sub_derivative_le`). Applying the Euclidean norm comparison for the array of these half-differences bounds the square-root integrand from the array inequality by the square root involving the directional derivatives, plus $\sqrt{nm}\,(2C/m)$ (`sqrt_sq_add_array_sq_le`). Integrate this pointwise bound; since the uniform product measure has total mass one, the constant error integrates to itself. Combining with the array inequality (`bobkov_inequality_array`) yields the result.

**Key facts.** `BooleanAnalysis.GaussianSpace.abs_normalizedBoolBlocks_half_difference_sub_derivative_le`, `BooleanAnalysis.GaussianSpace.bobkov_inequality_array`, `BooleanAnalysis.GaussianSpace.sqrt_sq_add_array_sq_le`.
