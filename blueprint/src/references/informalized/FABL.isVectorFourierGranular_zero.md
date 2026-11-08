<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.isVectorFourierGranular_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Granularity of the zero function

**Claim.** For every real $\varepsilon$, the zero function on the $n$-dimensional binary cube is vector Fourier granular with granularity $\varepsilon$.

**Proof.** By the vector Fourier granularity criterion (`isVectorFourierGranular_iff`), it suffices to check each vector Fourier coefficient. The coefficient is the expectation of the zero function times the corresponding Walsh character (`vectorFourierCoeff_eq_expect`), hence is zero. Choosing the integer $0$ expresses it as $0\cdot\varepsilon$, as required.

**Key facts.** `FABL.isVectorFourierGranular_iff`, `FABL.vectorFourierCoeff_eq_expect`.
