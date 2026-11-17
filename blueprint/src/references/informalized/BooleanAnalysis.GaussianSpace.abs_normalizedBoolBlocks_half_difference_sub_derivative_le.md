<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/DiscreteApproximation.lean :: BooleanAnalysis.GaussianSpace.abs_normalizedBoolBlocks_half_difference_sub_derivative_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Block Half-Difference Approximation

**Claim.** Changing one Boolean entry from false to true gives a half-difference of function values that approximates the derivative in the corresponding coordinate, with error at most $2C/m$.

**Proof.** Let $z$ be the normalized block-sum vector and let $e_i$ be the $i$th coordinate vector. Updating the chosen Boolean entry changes the normalized vector by a scalar multiple of $e_i$ (`normalizedBoolBlocks_update`). The two possible signs of that entry are $1$ and $-1$ (`boolToSign_false`, `boolToSign_true`), so the two vectors differ by a step of magnitude $2/\sqrt m$ along that coordinate. The half-increment derivative estimate (`abs_half_increment_sub_derivative_le`) bounds the error for a step $h$ by $(C/2)h^2\|e_i\|^2$. Here $\|e_i\|=1$ and $h^2=4/m$, giving $2C/m$. If the original bit is true, the order of the two endpoint values is reversed; negating the corresponding half-increment expression leaves its absolute value unchanged and gives the same estimate.

**Key facts.** `BooleanAnalysis.GaussianSpace.normalizedBoolBlocks_update`, `BooleanAnalysis.boolToSign_false`, `BooleanAnalysis.boolToSign_true`, `BooleanAnalysis.GaussianSpace.abs_half_increment_sub_derivative_le`.
