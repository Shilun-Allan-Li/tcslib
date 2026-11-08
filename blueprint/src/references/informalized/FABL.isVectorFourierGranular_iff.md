<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.isVectorFourierGranular_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vector Fourier granularity criterion

**Claim.** A function on the binary cube is vector Fourier granular with granularity $\varepsilon$ exactly when every vector Fourier coefficient is an integer multiple of $\varepsilon$.

**Proof.** For the forward implication, fix a vector $\gamma$. Its vector Fourier coefficient is the ordinary Fourier coefficient of the corresponding function on the sign cube at the support of $\gamma$ (the identity `vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube`). Granularity on the sign cube therefore supplies an integer multiple of $\varepsilon$. Conversely, fix a subset $S$ of coordinates and take the unique vector $\gamma$ whose support is $S$, using the support-subset correspondence. The assumed vector-coefficient condition gives an integer multiple of $\varepsilon$; applying the same coefficient identity converts it to the required ordinary Fourier coefficient.

**Key facts.** `FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube`.
