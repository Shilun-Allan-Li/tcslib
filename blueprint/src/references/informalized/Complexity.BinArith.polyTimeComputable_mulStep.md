<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Mul.lean :: Complexity.BinArith.polyTimeComputable_mulStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Multiplication Update

**Claim.** The multiplication update function that leaves the state fixed when the remaining first component is empty, and otherwise performs the specified encoded update, is polynomial-time computable.

**Proof.** Unfold the update into its cases. The test for whether the relevant nested decoded component is empty is polynomial-time computable by composing the second-slot projection with the emptiness test. If it is empty, the update returns the original state, which is polynomial-time computable by the identity function.

In the nonempty case, construct the new first component by prepending false to the first decoded component; this is polynomial-time computable using a constant word, the first-component projection, and the closure result for prepending a computed bit. Construct the new second component by encoding the tail of the relevant decoded component with a further conditional result. The condition reads its head with default false. If that head is true, the result is the sum of the second nested component and the first decoded component, computed by the polynomial-time addition function; otherwise the result is the second nested component itself. The projections, tail operation, pair encodings, addition, and polynomial-time conditional closure establish polynomial-time computability of this branch. Applying the polynomial-time conditional construction to the empty test and these two branches proves the result.

**Key facts.** `Complexity.polyTimeComputable_slot2`, `Complexity.polyTimeComputable_isNil`, `Complexity.polyTimeComputable_id`, `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_cons`, `Complexity.polyTimeComputable_tail`, `Complexity.polyTimeComputable_headD`, `Complexity.polyTimeComputable_slot3`, `Complexity.BinArith.polyTimeComputable_add`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_ite`.
