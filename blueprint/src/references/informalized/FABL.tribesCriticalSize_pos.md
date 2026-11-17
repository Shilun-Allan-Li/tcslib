<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.tribesCriticalSize_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of Critical Size

**Claim.** For every positive natural number $w$, the critical size of tribes of width $w$ is positive.

**Proof.** The inverse parameter $2^{-w}$ lies in $(0,1/2]$ (`criticalInverse_mem_Ioc`). For size one, the candidate condition reduces to $1-(1-2^{-w})=2^{-w}\le1/2$, so size one is a candidate. It is within the search range, since $1\le2^{w+2}$. The greatest candidate is therefore at least one, proving positivity.

**Key facts.** `FABL.criticalInverse_mem_Ioc`.
