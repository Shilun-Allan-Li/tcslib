<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.expect_value_maxLinear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected value of a random linear CSP assignment

**Claim.** For any nonempty instance of the linear-constraint template over $\mathbb F_2$, a uniformly random assignment satisfies, in expectation, exactly half of the constraints; hence its expected value is $1/2$.

**Proof.** Expand the instance value as its satisfied-count divided by the number of constraints. Since expectation is linear over finite sums, the expected satisfied-count is the sum, over constraints with multiplicity, of the expected satisfaction indicator. The fact that this expected count is half the total number of constraints is precisely the result on expected satisfaction indicators (`expect_satisfiedIndicators_maxLinear`). Dividing by the constraint count therefore gives $1/2$. The count is nonzero because the instance is nonempty, so this division is valid.

**Key facts.** `FABL.expect_satisfiedIndicators_maxLinear`.
