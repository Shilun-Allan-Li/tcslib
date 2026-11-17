<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.polyTimeComputable_eqW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Binary Equality Test

**Claim.** The test that outputs one exactly when the decoded components have equal lengths and represent equal natural numbers, and zero otherwise, is polynomial-time computable.

**Proof.** The test is the conjunction of two conditions: the decoded components have equal lengths, and their binary values are equal. The length-equality test is polynomial-time computable, as is the binary-value equality test. The polynomial-time conjunction result combines these two one-bit outputs into their Boolean conjunction, which is precisely the required equality test.

**Key facts.** `Complexity.polyTimeComputable_and`, `Complexity.polyTimeComputable_lenEq`, `Complexity.BinArith.polyTimeComputable_beq`.
