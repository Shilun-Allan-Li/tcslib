<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.fknOptimalitySmallSetMass_approx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small-Set Mass Approximation

**Claim.** For each natural number $q$, the uniform probability of the selected cube’s upper-tail set differs from the target Gaussian mass by less than half that mass.

**Proof.** The selected dimension is defined from a witness to the approximation property. By the specification of that chosen dimension (`fknOptimalityDimensionIndex_spec`), the first component of the property gives precisely the required bound on the cube average. Unfolding the selected tail dimension and small-set indicator identifies that average with the stated small-set mass.

**Key facts.** `FABL.fknOptimalityDimensionIndex_spec`.
