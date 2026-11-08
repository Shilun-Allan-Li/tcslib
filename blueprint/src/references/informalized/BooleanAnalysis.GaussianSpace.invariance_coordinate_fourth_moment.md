<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Moments.lean :: BooleanAnalysis.GaussianSpace.invariance_coordinate_fourth_moment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth Moment of a Coordinate Derivative

**Claim.** For a degree-at-most-$k+1$ coefficient family and a coordinate $i$, the fourth moment of the random-input evaluation of its coordinate-derivative coefficient family is at most $9^k\mathrm{Inf}_i[F]^2$.

**Proof.** The coordinate-derivative coefficients have degree at most $k$ (`coordinateDerivative_degree`). Apply the polynomial fourth-moment bound (`invariance_polynomial_fourth_moment`) to this coefficient family and the given independent coordinates. It bounds the integral by $9^k$ times the square of the sum of the squared derivative coefficients. The coefficient-energy identity (`coordinateDerivative_sum_sq`) identifies that sum with the influence of coordinate $i$ in the Boolean-cube evaluation of $F$. Substitution gives the required bound.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.coordinateDerivative_degree`, `BooleanAnalysis.GaussianSpace.invariance_polynomial_fourth_moment`, `BooleanAnalysis.GaussianSpace.Invariance.coordinateDerivative_sum_sq`.
