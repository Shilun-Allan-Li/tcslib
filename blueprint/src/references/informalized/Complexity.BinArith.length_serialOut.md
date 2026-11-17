<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.length_serialOut -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Serial output length

**Claim.** For any state set, transition and output functions, starting state, and finite list of bit pairs, the serial output has the same length as the input list.

**Proof.** We argue by induction on the list, allowing the starting state to vary. The empty list produces the empty output, so the lengths agree. For a list with first pair $p$ and tail $ps$, the output consists of one bit, followed by the serial output of $ps$ from the state reached after processing $p$. By the induction hypothesis, that tail output has length $|ps|$; hence the full output has length $1+|ps|$, which is the length of the original list.
