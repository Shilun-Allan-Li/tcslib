<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.expect_two_pow_restrictedDecisionTreeDepth_eq_failureSum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth Moment as a Failure-Probability Sum

**Claim.** The random-restriction average of $2^d$ equals $1+\sum_{j=0}^{n-1}2^j q_{j+1}$, where $q_k$ is the average indicator of the event that the restricted decision-tree depth is at least $k$.

**Proof.** For each restriction, expand $2^d$ as one plus the sum of $2^j$ times the indicator that $d\ge j+1$, for $0\le j<n$ (`two_pow_restrictedDecisionTreeDepth_eq_tailIndicators`). Averaging the pointwise identity, additivity and preservation of constants separate the initial $1$ from the finite sum, and finite-sum linearity moves that sum outside the average (`expectRandomRestriction_add`, `expectRandomRestriction_const`, and `expectRandomRestriction_sum`). In each summand, pull out the constant $2^j$ (`expectRandomRestriction_const_mul`); the remaining average is exactly the failure probability $q_{j+1}$ by its definition. This gives the asserted formula.

**Key facts.** `FABL.two_pow_restrictedDecisionTreeDepth_eq_tailIndicators`, `FABL.expectRandomRestriction_add`, `FABL.expectRandomRestriction_const`, `FABL.expectRandomRestriction_sum`, `FABL.expectRandomRestriction_const_mul`.
