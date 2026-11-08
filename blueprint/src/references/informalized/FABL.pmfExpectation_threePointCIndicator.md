<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.pmfExpectation_threePointCIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation of a Point Indicator

**Claim.** Under the uniform distribution on the three-point set, the expectation of the indicator of $c$ is $1/3$.

**Proof.** Apply the coefficient identity for the indicator of $c$ at the index $0\in\mathrm{Fin}(3)$: the expectation of the product of that indicator with the zeroth three-point basis function equals its zeroth coefficient (`threePointCIndicator_coefficient`). In this construction, the zeroth basis function is constant $1$, so the expectation is just that of the indicator itself; its zeroth coefficient is $1/3$.

**Key facts.** `FABL.threePointCIndicator_coefficient`.
