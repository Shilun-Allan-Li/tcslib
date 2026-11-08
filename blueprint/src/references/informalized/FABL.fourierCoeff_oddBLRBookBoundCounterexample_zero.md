<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.fourierCoeff_oddBLRBookBoundCounterexample_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A singleton Fourier coefficient

**Claim.** For the fixed Boolean function on the two-dimensional sign cube used as a counterexample to the odd BLR book bound, the Fourier coefficient at the singleton coordinate set $\{0\}$ is $-1/2$.

**Proof.** Apply the explicit coefficient formula for the counterexample ( `fourierCoeff_oddBLRBookBoundCounterexample` ) at $T=\{0\}$. The empty-set term vanishes, the indicator for $\{0\}=T$ contributes $1$, and the indicator for $\{1\}=T$ vanishes. Also, $\{0,1\}\ne\{0\}$, since $1$ belongs to the former but not the latter, so the final indicator vanishes. The formula therefore gives $(0-1-0-0)/2=-1/2$.

**Key facts.** `FABL.fourierCoeff_oddBLRBookBoundCounterexample`.
