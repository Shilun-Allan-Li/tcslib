<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.switchingFailureProbability_reindexBooleanFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate relabeling invariance

**Claim.** Relabeling the coordinates of a Boolean function by a bijection preserves its switching-failure probability at every parameter and threshold.

**Proof.** First identify the switching-failure probability with its coordinate-assignment formulation, using the equality between the two definitions ($\texttt{coordSwitchingFailureProbability_eq}$). In that formulation, relabeling the coordinates by a bijection leaves the probability unchanged ($\texttt{coordSwitchingFailureProbability_reindexBooleanFunction}$). Convert back to the original formulation for the relabeled function, again using $\texttt{coordSwitchingFailureProbability_eq}$, to obtain the claimed equality.

**Key facts.** `FABL.coordSwitchingFailureProbability_eq`, `FABL.coordSwitchingFailureProbability_reindexBooleanFunction`.
