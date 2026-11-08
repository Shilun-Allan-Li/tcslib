<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePairing.lean :: Complexity.polyTimeComputable_unary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Unary Length Function

**Claim.** The function that sends each bit string $x$ to the word consisting of $|x|$ copies of $1$ is polynomial-time computable.

**Proof.** First compute the unary word with $|x|+1$ copies of $1$. The polynomial-time unary-generation result gives a machine for words of length $1\cdot(|x|+1)^1$, hence for this word (`computesFunInTime_polyUnary`); the linear-to-polynomial closure result supplies the stated polynomial-time computability. Pair this word with $x$, using the identity function and the pair-encoding closure theorem (`polyTimeComputable_id`, `PolyTimeComputable.pairEncode`). Next apply a polynomial-time transformation that decodes the pair, removes the final $1$ from its second component, and re-encodes the pair; such a machine is supplied by the strip-last computation result (`computesFunInTime_stripLast`). On this particular input, the decoded second component is a nonempty string of $|x|+1$ ones, and removing its last bit leaves exactly $|x|$ ones (`splitAtLastTrue_replicate_succ`). Finally, extract the second component of the resulting pair, which is polynomial-time computable (`computesFunInTime_pairSnd`), and compose these operations. The pair-encoding and decoding identity ensures that the intermediate pair is recovered as intended (`pairDecode_pairEncode`); closure under composition preserves polynomial-time computability (`PolyTimeComputable.comp`).

**Key facts.** `Turing.FinTM.computesFunInTime_polyUnary`, `Complexity.polyTimeComputable_of_linear`, `Complexity.PolyTimeComputable.pairEncode`, `Turing.FinTM.computesFunInTime_stripLast`, `Complexity.splitAtLastTrue_replicate_succ`, `Turing.pairDecode_pairEncode`, `Turing.FinTM.computesFunInTime_pairSnd`, `Complexity.PolyTimeComputable.comp`.
