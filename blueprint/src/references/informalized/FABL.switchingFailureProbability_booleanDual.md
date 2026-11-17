<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.switchingFailureProbability_booleanDual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dual Invariance of Switching Failure

**Claim.** Boolean dualization leaves the switching-failure probability unchanged: $P_{\delta,k}(f^*)=P_{\delta,k}(f)$.

**Proof.** Rewrite each switching-failure probability as its coordinate-restriction version, using the equality of these two formulations (\texttt{coordSwitchingFailureProbability\_eq}). The coordinate-restriction dual-invariance theorem states that these probabilities agree for $f$ and its Boolean dual (\texttt{coordSwitchingFailureProbability\_booleanDual}). Replacing the two coordinate-restriction probabilities by their equal switching-failure probabilities gives the claim.

**Key facts.** `FABL.coordSwitchingFailureProbability_eq`, `FABL.coordSwitchingFailureProbability_booleanDual`.
