<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Div.lean :: Complexity.BinArith.polyTimeComputable_divStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Division Step

**Claim.** The function that performs one division-step update on a bit string is polynomial-time computable.

**Proof.** First extract the components needed from the nested pair encoding: the first component of the input, the first component of its second decoded component, and the tail of that second component. The pair projections and slot selectors are polynomial-time computable, and composing them gives these intermediate strings. The head of the second component, with default value false, can also be computed in polynomial time; prepending it to the selected tail gives the current divisor candidate. The fourth decoded slot supplies the residual state carried through the update.

The update first tests whether the selected second component is empty. If so, it returns the original input, which is polynomial-time computable by the identity-function result. Otherwise it tests whether the first component is at most the value of the candidate divisor. This comparison is polynomial-time computable after encoding the two compared strings as a pair.

In the true branch, the output re-encodes the original first component together with an updated state: it drops the head of the second component, computes the difference between the candidate divisor and the original first component, and pairs that with the fourth slot preceded by true. In the false branch it re-encodes the original first component and the same shortened second component, but keeps the candidate divisor and prefixes the fourth slot with false. Each branch is assembled from polynomial-time computable projections, head/tail operations, subtraction, constants and pairing. Since a polynomial-time test with polynomial-time branches yields a polynomial-time function, the complete division step is polynomial-time computable.

**Key facts.** `Complexity.BinArith.polyTimeComputable_slot3`, `Complexity.PolyTimeComputable.comp`, `Complexity.BinArith.polyTimeComputable_slot2`, `Complexity.polyTimeComputable_headD`, `Complexity.BinArith.polyTimeComputable_cons`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_tail`, `Complexity.BinArith.polyTimeComputable_sub`, `Complexity.polyTimeComputable_const`, `Complexity.BinArith.polyTimeComputable_le`, `Complexity.polyTimeComputable_isNil`, `Complexity.polyTimeComputable_id`, `Complexity.polyTimeComputable_ite`, `Complexity.polyTimeComputable_pairFstD`.
