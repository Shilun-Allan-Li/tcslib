<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.faninTwo_bitBlock -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-in of a bit block

**Claim.** If $a\ne b$, $c<L$, $\mathrm{cin}<L$, and $\mathrm{acc}<L$, every gate in the corresponding bit block is well formed and has at most two inputs.

**Proof.** Expand the bit block into its constituent full-adder gates, XOR gate lists, and final NOT and AND gates. Each displayed gate has at most two arguments. The only two-argument gates have distinct arguments: this follows from $a\ne b$ for the first XOR construction and from the stated index bounds for the later constructions, whose indices are formed by adding distinct offsets to $L$. Each NOT gate has exactly one argument. Thus every argument list has no repetitions, every NOT gate has the required single input, and all gates have fan-in at most two.
