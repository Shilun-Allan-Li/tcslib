<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.oddBLRQueryNoiseCutoff_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Cutoff Lies in the Unit Interval

**Claim.** If $0<\delta<1/2$, then the noise cutoff $1-(1-2\delta/3)^2$ lies in $[0,1]$.

**Proof.** The noise rate $2\delta/3$ lies in $[0,1]$ (`oddBLRQueryNoiseRate_mem_Icc`), so its complement $r=1-2\delta/3$ also lies in $[0,1]$. Therefore $r^2\le 1$, which gives $1-r^2\ge 0$. Since every square is nonnegative, $1-r^2\le 1$. These are the two bounds required.

**Key facts.** `FABL.oddBLRQueryNoiseRate_mem_Icc`.
