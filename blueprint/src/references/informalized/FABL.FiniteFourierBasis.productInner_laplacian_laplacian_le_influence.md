<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.FiniteFourierBasis.productInner_laplacian_laplacian_le_influence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed-function Laplacian bound

**Claim.** If $f$ and $g$ take only the values $-1$ and $1$, then the inner product of their coordinate Laplacians is at most the influence of $g$ at that coordinate.

**Proof.** Self-adjointness of the coordinate Laplacian changes the left-hand side to the inner product of $f$ with the coordinate Laplacian of $g$. Pointwise, since $f$ is either $-1$ or $1$, multiplying the latter function by $f$ gives a value at most its absolute value. Monotonicity of expectation therefore bounds this inner product by the expected absolute value of the coordinate Laplacian of $g$, which is its $L^1$ norm. For sign-valued $g$, the established identity between this norm and coordinate influence identifies that upper bound with the influence of $g$.

**Key facts.** `FABL.FiniteFourierBasis.productInner_laplacian_laplacian_eq`, `FABL.pmfExpectation_mono`, `FABL.FiniteFourierBasis.productLaplacianL1_eq_influence_of_hasSignRange`.
