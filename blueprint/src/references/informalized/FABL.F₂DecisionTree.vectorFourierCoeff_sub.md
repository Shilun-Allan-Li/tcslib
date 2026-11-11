<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.vectorFourierCoeff_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subtraction of Fourier coefficients

**Claim.** The vector Fourier coefficient of the difference $f-g$ at $\gamma$ equals the coefficient of $f$ minus the coefficient of $g$ at that index.

**Proof.** Write each vector Fourier coefficient as the uniform average of the function times the corresponding Walsh character, using the expectation formula (\texttt{vectorFourierCoeff\_eq\_expect}). Distribute multiplication over subtraction inside the average. Linearity of the finite uniform average then gives the average for $f$ minus the average for $g$, which is the asserted identity.

**Key facts.** `FABL.vectorFourierCoeff_eq_expect`.
