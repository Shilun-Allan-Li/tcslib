<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.hastadSoundnessError_tendsto_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Soundness error tends to zero

**Claim.** For every positive noise level $r$, the soundness error tends to zero as $\varepsilon$ tends to zero through positive values.

**Proof.** The function $\varepsilon\mapsto\sqrt{\varepsilon}/2$ tends to zero at zero by continuity of the square root. Since $r>0$, all sufficiently small positive $\varepsilon$ satisfy $\varepsilon\leq r$. On that neighborhood, the soundness error agrees with $\sqrt{\varepsilon}/2$. Therefore it has the same limit, namely zero.
