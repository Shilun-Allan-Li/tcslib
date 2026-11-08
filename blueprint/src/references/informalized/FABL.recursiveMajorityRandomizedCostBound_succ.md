<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.recursiveMajorityRandomizedCostBound_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomized Cost Bound Recurrence

**Claim.** For each natural number $d$, the randomized cost bound at depth $d+1$ is $\frac{8}{3}$ times the bound at depth $d$.

**Proof.** By definition, the randomized bound at depth $d$ is $(8/3)^d$. The exponent law gives $(8/3)^{d+1}=(8/3)^d(8/3)$. Commutativity of real multiplication puts the factor $8/3$ first, yielding the stated recurrence.
