<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Basic.lean :: BooleanAnalysis.Hypercontractivity.fourierCoeff_derivative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficient of a Derivative

**Claim.** For the discrete derivative in coordinate $i$, the Fourier coefficient at $S$ is zero when $i\in S$, and otherwise equals the coefficient of the original function at $S\cup\{i\}$.

**Proof.** Write the coefficient as the expectation of the derivative times the character. The bit-flip map in coordinate $i$ is an involution, hence a bijection of the cube; changing variables by this map preserves uniform expectation. The derivative is invariant under this flip, while the character changes sign exactly when $i\in S$ (the character flip identity, `chiS_flipBit_eq`). If $i\in S$, the change of variables therefore makes the expectation its own negative, so it vanishes. If $i\notin S$, pair each point with its flipped point. The derivative's definition and the fact that the character on $S\cup\{i\}$ gains the factor associated with coordinate $i$ show that the average of the two paired summands is the original function times that larger-set character. Averaging over the cube gives the coefficient at $S\cup\{i\}$. This uses linearity of expectation (`expect_add`, `expect_const_mul`) and its compatibility with negation (`expect_neg`) to pass between the paired expression and its expectation.

**Key facts.** `BooleanAnalysis.flipBit_flipBit`, `BooleanAnalysis.chiS_flipBit_eq`, `BooleanAnalysis.ThresholdFunctions.expect_neg`, `BooleanAnalysis.ThresholdFunctions.expect_const_mul`, `BooleanAnalysis.ThresholdFunctions.expect_add`.
