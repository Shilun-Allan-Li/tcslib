<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.coordRestrictionWeightAt_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative coordinate weights

**Claim.** If $0\leq\delta\leq1$, then every coordinate restriction has nonnegative weight.

**Proof.** Check the three possible states. For a free coordinate, its weight is $\delta$, which is nonnegative by hypothesis. For either fixed state, the weight is $(1-\delta)/2$; since $\delta\leq1$, its numerator is nonnegative, and division by the positive number $2$ preserves nonnegativity.
