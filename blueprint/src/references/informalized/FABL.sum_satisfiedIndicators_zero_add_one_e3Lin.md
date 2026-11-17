<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPExamples.lean :: FABL.sum_satisfiedIndicators_zero_add_one_e3Lin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complementary Satisfaction Counts

**Claim.** For any finite multiset of three-variable linear constraints over $\mathbb F_2$, the total numbers satisfied by the all-zero and all-one assignments add up to the number of constraints.

**Proof.** Induct on the multiset of constraints. The empty multiset contributes zero on both sides. For the inductive step, separate one constraint from the rest. Its satisfaction indicators under the two constant assignments sum to one, by the complementary satisfaction property for each constraint (`satisfiedIndicator_zero_add_one_e3Lin`). The induction hypothesis says the remaining constraints contribute their total number to the two counts. Adding the contributions gives the cardinality of the full multiset.

**Key facts.** `FABL.satisfiedIndicator_zero_add_one_e3Lin`.
