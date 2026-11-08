<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.codePrimPair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitive Recursiveness of the Aligned Pair Parser

**Claim.** The partial parser that reads aligned two-bit blocks from the left, records the blocks $00$ and $11$, stops at the first $01$, and returns the accumulated first component and untouched suffix is primitive recursive.

**Proof.** The parser is implemented by a list recursion that keeps two option-valued records: the result for the current suffix and the result for its tail. At each step, it examines the head of the suffix. If the head agrees with the current bit, it extends the first component of the recorded result by that bit; if the head differs and the current bit is $1$, parsing fails; and if the head differs and the current bit is $0$, it records the empty first component and the suffix after the two-bit block. These choices use primitive recursive list-head, list-tail, Boolean equality, conditional, option-map, and option-bind operations, so the step function is primitive recursive. List recursion then makes the pair of records primitive recursive. An induction on the input list verifies that these records are exactly the parser's values on the list and its tail; checking the empty, one-entry, and two-entry cases confirms the specified block behavior. Projecting the first record yields the desired parser.
