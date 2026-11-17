<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/KWiseIndependence.lean :: FABL.isLowDegreeFourierRegular_binaryFunctionOnSignCube_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Regularity under the binary cube encoding

**Claim.** Low-degree Fourier regularity of the sign-cube representation is equivalent to the corresponding coefficient bounds indexed by nonzero vectors on the binary cube.

**Proof.** First suppose the sign-cube representation is regular. Given a nonzero binary vector $\gamma$, its support is nonempty (\texttt{f₂Support\_nonempty\_iff}). The identity equating the vector Fourier coefficient to the sign-cube Fourier coefficient indexed by that support (\texttt{vectorFourierCoeff\_eq\_fourierCoeff\_binaryFunctionOnSignCube}) lets us apply regularity to the support, using its assumed size bound.

Conversely, take a nonempty coordinate set $S$ of size at most $k$. Choose the binary vector corresponding to $S$ under the support-set equivalence, so its support is exactly $S$. It is nonzero because that support is nonempty. Apply the assumed coefficient bound to this vector, and use the same coefficient identity to obtain the required bound for the Fourier coefficient indexed by $S$.

**Key facts.** `FABL.f₂Support_nonempty_iff`, `FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube`.
