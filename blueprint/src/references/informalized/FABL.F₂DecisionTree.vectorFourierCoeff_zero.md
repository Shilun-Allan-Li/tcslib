<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.vectorFourierCoeff_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Fourier coefficient

**Claim.** For every binary-cube vector $\gamma$, the vector Fourier coefficient of the zero function at $\gamma$ is zero.

**Proof.** Express the coefficient as the uniform average of the zero function multiplied by the Walsh character, using the expectation formula (\texttt{vectorFourierCoeff\_eq\_expect}). The integrand is identically zero, so its average is zero.

**Key facts.** `FABL.vectorFourierCoeff_eq_expect`.
