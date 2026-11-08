<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_sW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Nested Projection

**Claim.** The function obtained by applying the total second-component projection twice and then the total first-component projection is polynomial-time computable.

**Proof.** The composite that first takes the total second component twice and then the total first component is precisely the projection described in the claim. Its polynomial-time computability is supplied directly by `polyTimeComputable_slot2`.

**Key facts.** `Complexity.BinArith.polyTimeComputable_slot2`.
