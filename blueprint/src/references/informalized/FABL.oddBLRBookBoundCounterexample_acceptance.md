<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.oddBLRBookBoundCounterexample_acceptance -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd BLR Counterexample Acceptance

**Claim.** For the negative OR function on the two-dimensional sign cube, the odd BLR test accepts with probability $3/8$.

**Proof.** The odd BLR acceptance formula expresses the probability as $\frac12+\frac12$ times the sum of the cubes of the Fourier coefficients over odd-cardinality frequencies (`oddBLRAcceptanceProbability_eq_fourierSum`). In dimension two, those frequencies are exactly the two singleton coordinate sets (`oddFourierFrequencies_two`). Each corresponding coefficient of the negative OR function is $-1/2$ (`fourierCoeff_oddBLRBookBoundCounterexample_zero` and `fourierCoeff_oddBLRBookBoundCounterexample_one`). The sum of their cubes is therefore $-1/4$, and substituting gives $\frac12+\frac12(-\frac14)=\frac38$.

**Key facts.** `FABL.oddBLRAcceptanceProbability_eq_fourierSum`, `FABL.oddFourierFrequencies_two`, `FABL.fourierCoeff_oddBLRBookBoundCounterexample_zero`, `FABL.fourierCoeff_oddBLRBookBoundCounterexample_one`.
