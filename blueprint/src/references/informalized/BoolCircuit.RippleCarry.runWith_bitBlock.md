<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.RippleCarry.runWith_bitBlock -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Evaluation of a ripple-carry bit block

**Claim.** Under the stated length and index bounds, running the bit block appends $15$ values, and its values at indices $L+8$ and $L+14$ are respectively the specified carry and accumulator expressions.

**Proof.** The length hypothesis identifies $L$ with the length of the initial value list. Split the bit block into its full-adder portion, the following XOR gates, and the final two gates. Running a concatenation of gate lists is the same as running the pieces in sequence (`BoolCircuit.runWith_append`). The full-adder evaluation computes the first two input bits' XOR and carry-related values at their designated positions (`BoolCircuit.runWith_fullAdderGates`). The next XOR gate sequence combines the intermediate sum with $c$; its four appended values occupy indices $L+11$ through $L+14$ relative to the original list, with the XOR result at $L+14$. The final NOT and AND gates then append the complement of that result and its conjunction with the original accumulator value, placing the latter at $L+14$ in the completed block. The gate-by-gate evaluation uses the existing values at $a,b,c,cin,acc$; the bounds ensure these are entries of the original list. Reading off the carry and accumulator positions gives the two stated Boolean expressions, and counting the appended values gives length $L+15$.

**Key facts.** `BoolCircuit.runWith_append`, `BoolCircuit.runWith_fullAdderGates`, `BoolCircuit.runWith_xorGates`.

**Caveat.** The supplied proof's gate positions and claimed final accumulator formula are difficult to reconcile: the displayed gate construction and full-adder output list appear to put the final NOT/AND values at different offsets than the informal statement. The account follows the intended evaluation route, but the exact index bookkeeping is not established by the provided upstream excerpts.
