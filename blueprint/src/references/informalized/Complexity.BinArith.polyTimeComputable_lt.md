<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean :: Complexity.BinArith.polyTimeComputable_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Encoded Strict Comparison

**Claim.** The function returning `[true]` exactly when the first decoded binary value is strictly less than the second, and `[false]` otherwise, is polynomial-time computable.

**Proof.** On the decoded pair, run the polynomial-time serial subtraction procedure with borrow as its state and false as its initial state, then return the last bit of its output. The serial procedure is polynomial-time computable, so composing it with the polynomial-time last-bit function is polynomial-time computable. Its output has positive length: the padded pair has length equal to the input length plus two, hence is nonempty, and the serial output has that length. The last bit of the serial output therefore equals its final state (`getLastD_serialOut_self`). The specification of serial subtraction says that this state is true exactly when the first decoded value is strictly less than the second. Thus the returned one-bit word is the required comparison result.

**Key facts.** `Complexity.BinArith.polyTimeComputable_serial`, `Complexity.BinArith.length_padZip`, `Complexity.BinArith.getLastD_serialOut_self`, `Complexity.BinArith.serial_sub_spec`, `Complexity.BinArith.polyTimeComputable_lastBit`, `Complexity.PolyTimeComputable.comp`.
