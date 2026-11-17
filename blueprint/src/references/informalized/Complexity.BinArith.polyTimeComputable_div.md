<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Div.lean :: Complexity.BinArith.polyTimeComputable_div -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Binary Division

**Claim.** The function returning the binary expansion of the quotient, rounded down, of the natural numbers represented by the decoded input components is polynomial-time computable.

**Proof.** If the decoded divisor is zero, the quotient function returns the empty word; this branch is polynomial-time computable by the zero test and a constant output. Otherwise, form the division loop's final state, take its fourth slot, and normalize that bit string to its canonical binary representation. These operations are polynomial-time computable by closure under composition, using `polyTimeComputable_divLoop`, the slot-four projection, and normalization.

It remains to identify the output. In the zero-divisor case, the natural-number convention for division by zero gives quotient zero, whose binary expansion is empty. In the nonzero case, `divLoop_spec` states that the value of the fourth slot of the final loop state is exactly the quotient of the decoded dividend by the decoded divisor (and also records the remainder). Since normalization preserves the represented value, the output is the desired binary expansion. The polynomial-time conditional closure property combines the two cases.

**Key facts.** `Complexity.BinArith.polyTimeComputable_isZero`, `Complexity.polyTimeComputable_const`, `Complexity.BinArith.polyTimeComputable_divLoop`, `Complexity.BinArith.polyTimeComputable_slot4`, `Complexity.BinArith.polyTimeComputable_normBits`, `Complexity.BinArith.divLoop_spec`, `Complexity.polyTimeComputable_ite`.
