<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Coordinates.lean :: BooleanAnalysis.GaussianSpace.Invariance.coordinate_parts_eq_of_off_coordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate independence of polynomial parts

**Claim.** If the random inputs $X$ and $Y$ agree at every coordinate other than $i$, then the random-input evaluations of both the coordinate-free part and the coordinate derivative polynomial agree as functions on $\Omega$.

**Proof.** The coordinate-free part has zero coefficients on all sets containing $i$. The coordinate derivative polynomial also has zero coefficients on such sets, by its coefficient formula. The evaluation invariance theorem says that a polynomial with all coefficients on sets containing $i$ equal to zero has the same random-input evaluation whenever the input families agree at every other coordinate. Applying this fact first to the coordinate-free part and then to the coordinate derivative polynomial proves both equalities.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.coordinateDerivative_coeff`, `BooleanAnalysis.Hypercontractivity.MultilinearMoments.eval_eq_of_off_coordinate`.
