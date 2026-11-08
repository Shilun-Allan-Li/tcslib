<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/RestrictedWeights.lean :: FABL.expect_freeProjection_signCubeSplitEquiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Free-Coordinate Projection

**Claim.** For a subset $J$ of the coordinates and a real-valued function $g$ on sign assignments to $J$, its expected value on the restriction of a uniform assignment to all coordinates equals its uniform expectation over assignments to $J$.

**Proof.** Split every assignment on the full cube into its coordinates in $J$ and its complementary coordinates. The resulting map is a bijection between full assignments and pairs $(y,z)$ of free and fixed-coordinate assignments, so changing variables along this bijection leaves the expectation unchanged. Averaging $g(y)$ over all such pairs factors into the average over $y$ and the average over $z$; since the integrand does not depend on $z$, the latter average is $1$. What remains is precisely the uniform expectation of $g$ over the free coordinates.
