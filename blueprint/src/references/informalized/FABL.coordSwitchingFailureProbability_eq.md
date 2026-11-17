<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.coordSwitchingFailureProbability_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equivalent Failure Probability Formulas

**Claim.** The coordinate-switching failure probability equals the expectation obtained by first weighting a free-coordinate set by its Bernoulli subset weight and then averaging uniformly over the fixed signs.

**Proof.** Expand the expectation over fixed-sign assignments as a finite sum. For each fixed free-coordinate set $J$, distribute its subset weight across that sum: each pair $(J,z)$ then has weight $\delta^{|J|}(1-\delta)^{n-|J|}/|\mathrm{FixedSignCube}(J)|$. Regard these pairs as the elements of the finite disjoint union of fixed-sign assignments and reindex the sum by the bijection between such pairs and coordinate restrictions. Under this correspondence, the failure indicators agree (\texttt{coordSwitchingFailureIndicator\_coordRestrictionOf}), and the assignment weight is exactly the subset weight divided by the number of fixed-sign choices (\texttt{restrictionAssignmentWeightAt\_coordRestrictionOf\_eq\_div}). Thus the reindexed sum is the coordinate-switching failure probability.

**Key facts.** `FABL.coordSwitchingFailureIndicator_coordRestrictionOf`, `FABL.restrictionAssignmentWeightAt_coordRestrictionOf_eq_div`.
