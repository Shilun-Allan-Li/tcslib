<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean :: Complexity.BinArith.lt_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time comparison language

**Claim.** For a binary string parsed as a pair encoding, using the empty string for an invalid parse, the language in which the value of the first parsed string is strictly less than the value of the second is decidable in polynomial time.

**Proof.** The comparison test computes the Boolean indicating whether the first parsed value is less than the second. The polynomial-time computability result for this test (`polyTimeComputable_lt`) says that the machine can produce its one-bit answer in polynomial time. The general test-to-language theorem (`mem_P_of_test`) then implies that the set of inputs on which this answer is true belongs to polynomial time.

**Key facts.** `Complexity.BinArith.polyTimeComputable_lt`, `Complexity.mem_P_of_test`.
