<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.switchingFailureProbability_mul_algebraic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Algebraic Restriction Composition

**Claim.** The switching-failure probability at parameter $\delta_1\delta_2$ equals the average over first restrictions at parameter $\delta_1$ of the switching-failure probabilities at parameter $\delta_2$ for the corresponding functions on the free coordinates.

**Proof.** Express the random-restriction average as a finite sum over coordinatewise restriction assignments (\texttt{expectRandomRestriction\_eq\_sum\_assignment}). The composition formula for assignment weights says that summing over a first and then a second restriction gives the weights for their composed restriction (\texttt{sum\_restrictionAssignmentWeightAt\_compose}). Reindexing the left side by the coordinate-restriction probability formulation (\texttt{coordSwitchingFailureProbability\_eq}) lets this composition formula identify the left side with the sum over target restrictions at parameter $\delta_1\delta_2$. For each first assignment, the corresponding inner switching-failure probability for the reindexed restricted function is the sum over second assignments given by (\texttt{switchingFailureProbability\_reindexedSignRestriction}). The restriction identity (\texttt{coordRestrictionOf\_restrictionAtomOfAssignment}) identifies the composed coordinate restriction in that sum with the restriction arising from the two successive assignments. Thus the finite sums agree term by term, proving the identity.

**Key facts.** `FABL.coordSwitchingFailureProbability_eq`, `FABL.sum_restrictionAssignmentWeightAt_compose`, `FABL.expectRandomRestriction_eq_sum_assignment`, `FABL.switchingFailureProbability_reindexedSignRestriction`, `FABL.coordRestrictionOf_restrictionAtomOfAssignment`.
