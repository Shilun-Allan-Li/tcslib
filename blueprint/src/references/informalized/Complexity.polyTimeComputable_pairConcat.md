<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePairing.lean :: Complexity.polyTimeComputable_pairConcat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time concatenation of pair components

**Claim.** The function that concatenates the two total decoded projections of an input bit string is polynomial-time computable.

**Proof.** A linear-time machine computes the function that decodes an input and outputs the concatenation of its two components when decoding succeeds, and outputs the empty word when decoding fails. The linear-time-to-polynomial-time result therefore makes this function polynomial-time computable. On a valid decoding, the total projections are exactly those two components, so their concatenation is the machine’s output. On a failed decoding, both total projections are empty, and their concatenation is also empty. Hence this function agrees with the target on every input.

**Key facts.** `Complexity.polyTimeComputable_of_linear`, `Turing.FinTM.computesFunInTime_pairConcat`.
