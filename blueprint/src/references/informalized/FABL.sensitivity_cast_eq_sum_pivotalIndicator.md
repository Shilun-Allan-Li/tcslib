<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/Basic.lean :: FABL.sensitivity_cast_eq_sum_pivotalIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sensitivity as a Sum of Pivotal Indicators

**Claim.** The sensitivity of a Boolean function at an input, viewed as a real number, equals the sum over coordinates of the indicator that each coordinate is pivotal there.

**Proof.** Sensitivity is the cardinality of the set of pivotal coordinates. For each coordinate, its pivotal indicator is $1$ when the coordinate belongs to that set and $0$ otherwise. Summing these indicators over all coordinates therefore counts precisely the set's elements, which is its cardinality. Interpreting that cardinality as a real number gives the asserted equality.
