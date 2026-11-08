<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.projectOnCoordinates_selfAdjoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Self-Adjointness of Coordinate Projection

**Claim.** The product inner product satisfies $\langle f,P_Jg\rangle=\langle P_Jf,g\rangle$.

**Proof.** Express each product inner product as a sum of products of Fourier coefficients using Plancherel's identity (\texttt{FABL.FiniteFourierBasis.plancherel}). For each multi-index, the projection coefficient formula (\texttt{FABL.FiniteFourierBasis.fourierCoeff_projectOnCoordinates}) multiplies the coefficient by the same indicator on either side: it is retained exactly when the support is contained in $J$, and otherwise is zero. Consequently the corresponding summands agree term by term, and so do their sums.

**Key facts.** `FABL.FiniteFourierBasis.plancherel`, `FABL.FiniteFourierBasis.fourierCoeff_projectOnCoordinates`.
