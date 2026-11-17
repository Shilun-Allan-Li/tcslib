<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.tribesCriticalSizeError_isTheta_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical size error order

**Claim.** The absolute value of the critical size error is bounded above and below by positive constants for all sufficiently large $w$.

**Proof.** The error lies between $\frac{\log 2}{4}$ and $2$ for every positive $w$ (`tribesCriticalSizeError_mem_Icc`), so it is nonnegative and bounded above by $2$. This gives the upper asymptotic bound by a constant multiple of $1$. For the lower bound, use $\log 2>\tfrac12$; then the error is at least $\frac{\log 2}{4}>\tfrac18$. Thus its absolute value is bounded below by a positive constant as well, proving that it is asymptotically of order $1$.

**Key facts.** `FABL.tribesCriticalSizeError_mem_Icc`.
