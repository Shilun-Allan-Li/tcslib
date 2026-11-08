<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.vectorFourierDegree_le_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree Characterization by Fourier Support

**Claim.** The vector Fourier degree of $f$ is at most $k$ exactly when every vector Fourier coefficient whose support has size greater than $k$ vanishes.

**Proof.** The degree bound is equivalent to the vanishing of every sign-cube Fourier coefficient indexed by a set of size greater than $k$ (`FABL.fourierDegree_le_iff`). Translate between sign-cube coefficients and vector Fourier coefficients using their equality at the support set (`FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube`). In the reverse direction, every set $S$ is the support of the vector corresponding to $S$ under the inverse of the cube-to-subsets equivalence; that vector's support is exactly $S$. Thus the two vanishing conditions quantify over the same indices, with the same size bound.

**Key facts.** `FABL.fourierDegree_le_iff`, `FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube`.
