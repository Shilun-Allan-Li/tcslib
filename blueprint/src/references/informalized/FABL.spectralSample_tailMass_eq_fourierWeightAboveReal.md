<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.spectralSample_tailMass_eq_fourierWeightAboveReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Spectral tail mass and Fourier weight

**Claim.** For every real threshold $k$, the spectral-sample probability mass on subsets whose cardinality exceeds $k$ equals the Fourier weight above $k$ of the real-valued version of $f$.

**Proof.** For each subset $S$ in the filtered sum, the real-valued spectral-sample mass equals its Fourier weight by \(\texttt{spectralSample\_apply\_toReal}\). Substituting these equalities into the sum over subsets with cardinality greater than $k$ gives exactly the definition of the Fourier weight above $k$.

**Key facts.** `FABL.spectralSample_apply_toReal`.
