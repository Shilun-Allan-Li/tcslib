<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/BasicFourierFormulas.lean :: FABL.spectralSample_card_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Spectral probability at a fixed level

**Claim.** The probability that the spectral sample has exactly $k$ elements equals the sum of the squared Fourier coefficients of the real-valued version of $f$ over all coordinate subsets of cardinality $k$.

**Proof.** For each subset $S$, its spectral-sample probability, expressed as a real number, equals its Fourier weight by \(\texttt{spectralSample\_apply\_toReal}\). Replacing each summand in the sum over subsets of size $k$ by that weight gives precisely the definition of the Fourier weight at level $k$.

**Key facts.** `FABL.spectralSample_apply_toReal`.
