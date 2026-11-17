<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.recursiveMajorityAverageCostBound_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average Cost Bound Recurrence

**Claim.** For each natural number $d$, the average cost bound at depth $d+1$ is $\frac{5}{2}$ times the bound at depth $d$.

**Proof.** By definition, the bound at depth $d$ is $(5/2)^d$. The exponent law gives $(5/2)^{d+1}=(5/2)^d(5/2)$; commutativity of real multiplication writes this as $(5/2)(5/2)^d$, which is the asserted recurrence.
