<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.fknOptimalityGaussianMass_lt_two_mul_smallSetMass -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Mass and Small-Set Mass

**Claim.** For the selected Boolean-cube dimension and the associated upper-tail set, its uniform probability satisfies $\alpha<2\mu(A)$, where $\alpha=1/(q+2)$.

**Proof.** The approximation property gives an absolute error between the small-set mass and the Gaussian mass that is less than half the Gaussian mass (`fknOptimalitySmallSetMass_approx`). Its lower bound therefore yields $\mu(A)>\alpha-\alpha/2=\alpha/2$. Rearranging proves $\alpha<2\mu(A)$.

**Key facts.** `FABL.fknOptimalitySmallSetMass_approx`.
