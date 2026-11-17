<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductDifferentiation.lean :: BooleanAnalysis.GaussianSpace.abs_coordinate_le_of_mem_ball -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Bound in a Maximum Norm Ball

**Claim.** If $m$ lies in the open ball of radius $\varepsilon$ about $c$ for the supremum norm, then each coordinate satisfies $|m(i)|\le\|c\|+\varepsilon$.

**Proof.** Membership in the ball means $\|m-c\|<\varepsilon$. The triangle inequality gives $\|m\|\le\|m-c\|+\|c\|$, while each coordinate is bounded by the supremum norm: $|m(i)|\le\|m\|$. Combining these inequalities yields $|m(i)|<\varepsilon+\|c\|$, and hence the stated weak inequality.
