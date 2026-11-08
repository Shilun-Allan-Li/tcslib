<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.fourierCoeff_oddBLRBookBoundCounterexample_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient at the Second Coordinate

**Claim.** The Fourier coefficient of the odd BLR book-bound counterexample at the singleton coordinate set $\{1\}$ is $-1/2$.

**Proof.** Specialize the general coefficient formula (\(\texttt{FABL.fourierCoeff_oddBLRBookBoundCounterexample}\)) to $T=\{1\}$. This set is nonempty and differs from $\{0\}$ and $\{0,1\}$, so only its own indicator contributes among the three subtracted terms. The formula therefore evaluates to $-1/2$.

**Key facts.** `FABL.fourierCoeff_oddBLRBookBoundCounterexample`.
