<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.FiniteFourierBasis.productInner_laplacian_laplacian_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Self-adjointness of the coordinate Laplacian

**Claim.** For any functions $f,g$, the inner product of their coordinate Laplacians equals the inner product of $f$ with the coordinate Laplacian of $g$.

**Proof.** Use Plancherel to express both inner products as sums of products of Fourier coefficients. The coordinate Laplacian keeps precisely the coefficients whose index has a nonconstant entry at coordinate $j$ and sets the others to zero. Therefore, in either inner product, each such index contributes the product of the corresponding coefficients of $f$ and $g$, while all remaining indices contribute zero. The sums agree.

**Key facts.** `FABL.FiniteFourierBasis.plancherel`, `FABL.FiniteFourierBasis.fourierCoeff_productCoordinateLaplacian`.
