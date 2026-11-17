<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.sum_restrictionAssignmentWeightAt_compose -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition of Restriction Weights

**Claim.** The weighted sum over two successive coordinatewise restrictions, with parameters $\delta_1$ and $\delta_2$, equals the weighted sum over single restrictions with parameter $\delta_1\delta_2$.

**Proof.** First rewrite the iterated sum as a sum over all pairs of assignments, multiplying their two weights and evaluating $g$ on their composition. The equivalence between a pair of assignments and an assignment of pairs of coordinate restrictions then expresses this as a sum over two-stage coordinate data. Group these terms according to their resulting composed assignment. For each target assignment, the sum of the weights of all two-stage data producing it is exactly its single-stage weight at parameter $\delta_1\delta_2$, by the two-stage fiber-weight identity (`sum_twoStageCoordRestrictionWeight_fiber`). Substituting this identity gives the claimed sum.

**Key facts.** `FABL.sum_twoStageCoordRestrictionWeight_fiber`.
