<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.fknOptimalityDelta_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Optimality Parameter

**Claim.** For every natural number $q$, the optimality parameter is strictly positive.

**Proof.** The mass of the chosen small set is strictly positive by the stated positivity result (`FABL.fknOptimalitySmallSetMass_pos`). Since the parameter is twice that mass and $2>0$, their product is strictly positive.

**Key facts.** `FABL.fknOptimalitySmallSetMass_pos`.
