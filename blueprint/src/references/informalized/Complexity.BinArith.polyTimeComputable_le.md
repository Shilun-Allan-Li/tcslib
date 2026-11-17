<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean :: Complexity.BinArith.polyTimeComputable_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Comparison

**Claim.** The function returning `[true]` exactly when the first decoded component has value at most the second decoded component, and `[false]` otherwise, is polynomial-time computable.

**Proof.** Swap the decoded components, then apply the polynomial-time strict-comparison function. By the closure of polynomial-time computability under composition, this computes the predicate that the second original value is strictly less than the first. Negating a polynomial-time Boolean-valued function preserves polynomial-time computability. For natural numbers, the negation of “the second value is strictly less than the first” is exactly “the first is at most the second.” Hence the resulting one-bit output is the required comparison.

**Key facts.** `Complexity.BinArith.polyTimeComputable_pairSwap`, `Complexity.BinArith.polyTimeComputable_lt`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_not`.
