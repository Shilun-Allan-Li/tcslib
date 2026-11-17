<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.localAcceptancePredicate_eq_neg_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of local acceptance

**Claim.** For any fixed seed and sign assignment, the local acceptance predicate equals $-1$ exactly when the verifier accepts the transcript formed by decoding the signs into bits at queried positions and leaving unqueried positions blank.

**Proof.** By definition, the local acceptance predicate is $-1$ when the Boolean condition that the verifier accepts the specified transcript is true, and is $1$ otherwise. Since these are the two possible values, equality of the predicate to $-1$ is equivalent to that acceptance condition.
