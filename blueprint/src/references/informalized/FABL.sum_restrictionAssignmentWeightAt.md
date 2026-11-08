<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.sum_restrictionAssignmentWeightAt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parameterized Total Restriction Weight

**Claim.** For every real $\delta$, the product weights on assignments that give a free coordinate weight $\delta$ and either fixed value weight $(1-\delta)/2$ sum to $1$.

**Proof.** As in the unparameterized case, the finite product-sum identity factors the sum over assignments into a product over coordinates of the sum of the three possible coordinate weights. For each coordinate, those weights sum to $1$ (`FABL.sum_coordRestrictionWeightAt`). Hence the product, and therefore the total assignment weight, is $1$.

**Key facts.** `FABL.sum_coordRestrictionWeightAt`.
