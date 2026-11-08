<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.fknOptimalitySmallSetMass_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of Small-Set Mass

**Claim.** For each natural number $q$, the uniform probability of the selected cube’s upper-tail set is positive.

**Proof.** The mass approximation gives $|\mu(A)-\alpha|<\alpha/2$, where the target mass satisfies $\alpha>0$. In particular, $\alpha-\mu(A)<\alpha/2$, so $\mu(A)>\alpha/2>0$.

**Key facts.** `FABL.fknOptimalitySmallSetMass_approx`.
