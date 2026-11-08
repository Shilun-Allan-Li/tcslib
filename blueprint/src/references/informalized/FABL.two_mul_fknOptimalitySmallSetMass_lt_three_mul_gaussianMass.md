<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.two_mul_fknOptimalitySmallSetMass_lt_three_mul_gaussianMass -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small-Set Mass Bound

**Claim.** For every natural number $q$, twice the uniform probability mass of the associated small set is strictly less than three times its Gaussian mass.

**Proof.** The approximation result `FABL.fknOptimalitySmallSetMass_approx` gives $|M_q-G_q|<G_q/2$, where $M_q$ is the small-set mass and $G_q$ is the Gaussian mass. In particular, $M_q-G_q<G_q/2$, so $M_q<3G_q/2$. Multiplying by $2$ proves $2M_q<3G_q$.

**Key facts.** `FABL.fknOptimalitySmallSetMass_approx`.
