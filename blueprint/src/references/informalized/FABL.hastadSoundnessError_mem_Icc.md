<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.hastadSoundnessError_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Soundness error lies in the unit interval

**Claim.** If $0\leq\varepsilon\leq1$, then the soundness error, equal to $\sqrt{\varepsilon}/2$ when $\varepsilon\leq\mathrm{noise}$ and to $1/2$ otherwise, lies in $[0,1]$.

**Proof.** Split according to whether $\varepsilon\leq\mathrm{noise}$. In that case the error is $\sqrt{\varepsilon}/2$: it is nonnegative, and $\sqrt{\varepsilon}\leq1$ follows from $\varepsilon\leq1$, so it is at most $1$. In the other case the error is $1/2$, which also lies in $[0,1]$.
