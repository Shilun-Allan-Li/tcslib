<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.fknOptimalityDelta_lt_three_mul_gaussianMass -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound for the Optimality Parameter

**Claim.** For every natural number $q$, the optimality parameter is less than three times the Gaussian mass $\alpha$.

**Proof.** The parameter is defined as twice the mass of the chosen small set. The cited bound states directly that twice this mass is less than three times the Gaussian mass. Replacing the parameter by its definition gives the claim.

**Key facts.** `FABL.two_mul_fknOptimalitySmallSetMass_lt_three_mul_gaussianMass`.
