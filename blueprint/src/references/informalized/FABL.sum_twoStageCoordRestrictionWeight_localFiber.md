<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.sum_twoStageCoordRestrictionWeight_localFiber -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition of Two Coordinate Restrictions

**Claim.** For either real parameter pair and any target restriction, the sum of the products of the two stage weights over pairs composing to that target equals its restriction weight at parameter $\delta_1\delta_2$.

**Proof.** There are three target cases. If the target is free, the first restriction must be free, while the second may be any of the three states. The sum is $\delta_1$ times the sum of the second-stage weights, which simplifies to $\delta_1\delta_2$. If the target fixes $1$, either the first restriction fixes $1$ (with any second restriction), or the first is free and the second fixes $1$. Summing these possibilities and substituting the weights gives $(1-\delta_1\delta_2)/2$. The case fixing $-1$ has the same possibilities and weights, so gives the same expression. These are exactly the three target weights at parameter $\delta_1\delta_2$.
