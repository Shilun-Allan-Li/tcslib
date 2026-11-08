<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.restrictionAssignmentWeightAt_fixCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weight Change Upon Fixing a Coordinate

**Claim.** If coordinate $i$ is free in a restriction assignment and $\delta<1$, its weight equals $2\delta/(1-\delta)$ times the weight after fixing $i$ to either sign and leaving all other coordinates unchanged.

**Proof.** Separate the product defining the restriction weight into the factor at $i$ and the product $P$ of all other factors. Since $i$ is free, its factor is $\delta$, so the original weight is $\delta P$. After fixing $i$ to either sign, its factor is $(1-\delta)/2$; all other factors are unchanged because `fixCoordinate_apply_of_ne` preserves every coordinate other than $i$. The fixed state has the stated factor (`coordRestrictionWeightAt_fixedState`), using `fixCoordinate_apply_self` at $i$. Hence the new weight is $((1-\delta)/2)P$. Since $\delta<1$, the denominator $1-\delta$ is nonzero, and rearranging yields the ratio $2\delta/(1-\delta)$.

**Key facts.** `FABL.CoordRestriction.fixCoordinate_apply_of_ne`, `FABL.CoordRestriction.fixCoordinate_apply_self`, `FABL.coordRestrictionWeightAt_fixedState`.
