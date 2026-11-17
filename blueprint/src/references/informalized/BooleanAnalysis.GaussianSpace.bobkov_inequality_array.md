<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/BooleanBlocks.lean :: BooleanAnalysis.GaussianSpace.bobkov_inequality_array -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bobkov Inequality for Boolean Arrays

**Claim.** For a function on a finite Boolean array taking values in $[0,1]$, the closed Gaussian profile of its expectation is bounded by the expectation of the square root of the squared profile plus the sum of squared coordinate derivatives.

**Proof.** Regard the array coordinates as the single finite index set $I\times J$, and apply the finite-coordinate Bobkov inequality (`bobkov_inequality_finite_index`) to the function obtained by currying the array. The curry map preserves the product of uniform bit measures (`measurePreserving_finiteCurry`), so the mean on the product index set is the stated array mean. Under this coordinate identification, the derivative in coordinate $(i,j)$ is exactly the difference obtained by resetting entry $(i,j)$ to $0$ and to $1$, divided by $2$. Reindexing the derivative sum over $I\times J$ as an iterated sum over $i$ and $j$, and transporting the integral back through the measure-preserving curry map, gives the asserted inequality.

**Key facts.** `BooleanAnalysis.GaussianSpace.bobkov_inequality_finite_index`, `BooleanAnalysis.GaussianSpace.measurePreserving_finiteCurry`.
