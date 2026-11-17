<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.FiniteFourierBasis.projectOnCoordinates_orthogonalComponent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Projection of a support component

**Claim.** Projecting the orthogonal component supported exactly on $S$ onto coordinates in $T$ returns that component if $S\subseteq T$, and returns zero otherwise.

**Proof.** It suffices to compare all Fourier coefficients, since the Fourier coefficient map is injective (fourierCoeff_injective). Fix a multi-index $a$. Projection onto $T$ keeps its coefficient precisely when its support is contained in $T$ (fourierCoeff_projectOnCoordinates), while the component supported on $S$ has coefficient equal to the original coefficient precisely when the support is exactly $S$, and zero otherwise (fourierCoeff_orthogonalComponent). If the support is $S$, the containment test is exactly $S\subseteq T$, so both sides have the same coefficient. If the support differs from $S$, the component has coefficient zero; whether or not the projection retains the coefficient, the right-hand side is either that component or the zero function according as $S\subseteq T$, and has the same coefficient. The Fourier coefficients of the two sides therefore agree at every multi-index, proving equality.

**Key facts.** `FABL.FiniteFourierBasis.fourierCoeff_injective`, `FABL.FiniteFourierBasis.fourierCoeff_projectOnCoordinates`, `FABL.FiniteFourierBasis.fourierCoeff_orthogonalComponent`, `FABL.FiniteFourierBasis.fourierCoeff_ite`, `FABL.FiniteFourierBasis.fourierCoeff_zero`.
