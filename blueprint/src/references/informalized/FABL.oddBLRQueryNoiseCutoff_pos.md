<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.oddBLRQueryNoiseCutoff_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Noise Cutoff

**Claim.** If $0<\delta<1/2$, then the noise cutoff $1-(1-2\delta/3)^2$ is positive.

**Proof.** The noise rate $2\delta/3$ is positive, and it is at most $1$ (`oddBLRQueryNoiseRate_mem_Icc`). Thus its complement $r=1-2\delta/3$ is nonnegative and strictly less than $1$. Squaring preserves the strict upper bound for this nonnegative number, so $r^2<1$. Consequently, the cutoff $1-r^2$ is positive.

**Key facts.** `FABL.oddBLRQueryNoiseRate_mem_Icc`.
