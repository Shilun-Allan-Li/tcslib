<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.criticalLog_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical Logarithm Positivity

**Claim.** For every positive integer $w$, $0<-\log(1-2^{-w})$.

**Proof.** The critical base bound shows that $q=1-2^{-w}$ belongs to $(0,1)$ (`FABL.criticalBase_mem_Ioo`). The logarithm is strictly negative on this interval, so its negative is strictly positive.

**Key facts.** `FABL.criticalBase_mem_Ioo`.
