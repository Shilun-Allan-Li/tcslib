<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.totalInfluence_tribesCritical -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical tribes total influence

**Claim.** For positive block width, the total influence of critical tribes equals its critical dimension times the influence of one critical coordinate.

**Proof.** Apply the total-influence formula for tribes (\texttt{totalInfluence\_tribes}) with the number of blocks set to the critical block count. The critical-size positivity result (\texttt{tribesCriticalSize\_pos}) supplies the required positive number of blocks, while the hypothesis supplies positive block width. By the definitions of critical tribes, critical dimension, and critical-coordinate influence, the resulting formula is exactly critical dimension multiplied by critical-coordinate influence.

**Key facts.** `FABL.totalInfluence_tribes`, `FABL.tribesCriticalSize_pos`.
