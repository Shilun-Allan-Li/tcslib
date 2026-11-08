<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.fknOptimalitySmallSetWeight_approx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Level-One Fourier Weight Approximation

**Claim.** For each natural number $q$, the sum of the squared level-one Fourier coefficients of the selected upper-tail indicator differs from the square of the Gaussian density at the threshold by less than half that square.

**Proof.** The chosen dimension satisfies the approximation property, whose second component bounds the difference between the level-one Fourier weight and the square of the Gaussian boundary by less than half that boundary square (`fknOptimalityDimensionIndex_spec`). At the selected tail dimension, the set’s indicator is exactly the threshold indicator in that property. Substituting these definitions yields the claimed inequality.

**Key facts.** `FABL.fknOptimalityDimensionIndex_spec`.
