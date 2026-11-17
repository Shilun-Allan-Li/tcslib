<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_bodyW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Word body is polynomial-time computable

**Claim.** The function on bit strings that deletes the first four bits is polynomial-time computable.

**Proof.** This function is the list operation that drops four entries. The general result that dropping any fixed number of entries is polynomial-time computable (`polyTimeComputable_drop`) applies with the number set to four.

**Key facts.** `Complexity.BinArith.polyTimeComputable_drop`.
