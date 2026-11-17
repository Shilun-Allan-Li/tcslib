<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSP.lean :: FABL.CSPConstraint.satisfiedIndicator_add_unsatisfiedIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complementary Satisfaction Indicators

**Claim.** For every assignment, the satisfied indicator plus the unsatisfied indicator of a constraint equals one.

**Proof.** The predicate evaluation is Boolean. If it is true, the satisfied indicator is one and the unsatisfied indicator is zero; if it is false, their values are zero and one, respectively. In either case their sum is one.
