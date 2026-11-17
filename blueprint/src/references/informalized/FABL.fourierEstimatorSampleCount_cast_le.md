<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.fourierEstimatorSampleCount_cast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sample-Count Upper Bound

**Claim.** For $\varepsilon,\delta\in(0,1/2]$, the sample count $m=\lceil 2b(\delta)/\varepsilon^2\rceil$ satisfies $m\le4b(\delta)/\varepsilon^2$.

**Proof.** The failure-bit count is a positive integer, so $b(\delta)\ge1$. Also $0<\varepsilon\le1/2$ implies $\varepsilon^2\le1/4$, hence $2b(\delta)/\varepsilon^2\ge1/2$. For every real $x\ge1/2$, its ceiling is at most $2x$. Applying this ceiling bound to $x=2b(\delta)/\varepsilon^2$ gives $m\le4b(\delta)/\varepsilon^2$.

**Key facts.** `FABL.fourierEstimatorFailureBits_pos`.
