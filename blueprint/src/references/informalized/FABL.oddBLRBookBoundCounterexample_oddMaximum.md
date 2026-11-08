<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.oddBLRBookBoundCounterexample_oddMaximum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd Fourier Maximum

**Claim.** For the negative OR function on the two-dimensional sign cube, the maximum Fourier coefficient over odd-cardinality frequencies is $-1/2$.

**Proof.** In dimension two, the odd-cardinality frequencies are precisely the two singleton coordinate sets (`oddFourierFrequencies_two`). The Fourier coefficient at each singleton is $-1/2` (`fourierCoeff_oddBLRBookBoundCounterexample_zero` and `fourierCoeff_oddBLRBookBoundCounterexample_one`). Thus the set of values being maximized consists of two copies of $-1/2$, so its maximum is $-1/2$.

**Key facts.** `FABL.oddFourierFrequencies_two`, `FABL.fourierCoeff_oddBLRBookBoundCounterexample_zero`, `FABL.fourierCoeff_oddBLRBookBoundCounterexample_one`.
