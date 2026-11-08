<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.OXRSignTester.toSignTester_usesMaxOXR -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negated OXR Predicates

**Claim.** Every predicate used by the sign tester associated with an OXR sign tester is obtained by choosing, for each of its three inputs, whether to negate that input before applying the OXR predicate.

**Proof.** Fix any seed of the associated sign tester. Its check uses the OXR predicate with the input-negation pattern selected by that seed. Hence this predicate is in the range defining the family of all such negated OXR predicates: the seed's negation pattern is a witness, and the two predicates agree by the construction of the check.
