<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.tribesCriticalSizeError_isLittleO_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical size error is little-o

**Claim.** The critical size error is little-o of $2^w$ as $w$ tends to infinity.

**Proof.** The critical size error is asymptotically of order $1$ (`tribesCriticalSizeError_isTheta_one`). The constant function $1$ is little-o of $2^w$, since an exponential with base greater than $1$ grows without bound. Transitivity of the asymptotic comparison between order and little-o therefore gives that the critical size error is little-o of $2^w$.

**Key facts.** `FABL.tribesCriticalSizeError_isTheta_one`.
