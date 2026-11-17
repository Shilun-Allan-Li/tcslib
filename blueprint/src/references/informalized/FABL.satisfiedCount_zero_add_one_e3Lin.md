<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPExamples.lean :: FABL.satisfiedCount_zero_add_one_e3Lin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complementary Constant Assignments

**Claim.** For a finite constraint instance over $\mathbb{F}_2$ with three-variable linear equations, the counts of constraints satisfied by the all-zero and all-one assignments add to the total number of constraints, with multiplicity.

**Proof.** For each constraint, the sum of its three assigned values is $0$ under the all-zero assignment and $1$ under the all-one assignment, since $1+1+1=1$ in $\mathbb{F}_2$. Thus, for either possible right-hand side, exactly one of these two assignments satisfies the constraint. Its two satisfaction indicators therefore sum to $1$. Summing this identity over the constraint multiset gives the result, because the sum of $1$ over that multiset is its cardinality. This is precisely the per-constraint argument packaged by the sum-of-indicators identity (`FABL.sum_satisfiedIndicators_zero_add_one_e3Lin`).

**Key facts.** `FABL.sum_satisfiedIndicators_zero_add_one_e3Lin`.
