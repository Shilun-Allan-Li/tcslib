<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductDensity.lean :: BooleanAnalysis.GaussianSpace.norm_coordinateProjection_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate projection norm bound

**Claim.** For a finite index set $I$ and $i\in I$, the coordinate projection from $\mathbb R^I$ to $\mathbb R$ has operator norm at most $1$.

**Proof.** To bound the operator norm by $1$, it suffices to show that the norm of the projection's value at each vector is at most the norm of that vector. The projection returns the $i$th coordinate, and the norm of any coordinate is bounded by the supremum norm on the finite product. Hence the required pointwise bound holds, proving the operator norm estimate.
