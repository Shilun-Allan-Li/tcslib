<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.switchingFailureProbability_reindexedSignRestriction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction assignment formula

**Claim.** The switching-failure probability of the reindexed restriction of $f$ to $J$ equals the sum over coordinate assignments of their product weights times the indicator that the composed restriction has decision-tree depth at least $k$.

**Proof.** Replace the probability by its coordinate-assignment formulation using the equality of the two probability definitions ($\texttt{coordSwitchingFailureProbability_eq}$). The assignments relevant to the reindexed restriction are exactly assignments on its free coordinates, so the sum over all coordinates can be reduced to a sum over those free coordinates; the product weights are preserved under this reindexing ($\texttt{sum_restrictionAssignmentWeightAt_comp_freeCoordinateEmbedding}$). For each such assignment, composing it with the original restriction specified by $(J,z)$ gives the same restricted function, and hence the same depth-threshold indicator, as first reindexing the restriction and then applying the assignment ($\texttt{coordSwitchingFailureIndicator_compose_coordRestrictionOf}$). Substituting this identity into the sum yields the stated formula.

**Key facts.** `FABL.coordSwitchingFailureProbability_eq`, `FABL.sum_restrictionAssignmentWeightAt_comp_freeCoordinateEmbedding`, `FABL.coordSwitchingFailureIndicator_compose_coordRestrictionOf`.
