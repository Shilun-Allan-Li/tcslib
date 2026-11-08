<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/Restrictions.lean :: FABL.indexedFourierCoeff_fin_eq_fourierCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of Fourier coefficients

**Claim.** For a function on the finite sign cube and a set of coordinates, the indexed Fourier coefficient equals the Fourier coefficient on the finite cube.

**Proof.** The indexed cube on the coordinate type `Fin n` is definitionally the finite sign cube, and the indexed monomial is definitionally the finite-cube monomial. Thus the two expectations have identical integrands and agree by unfolding their definitions.
