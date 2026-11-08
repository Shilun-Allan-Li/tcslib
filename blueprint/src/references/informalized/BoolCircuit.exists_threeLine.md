<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLineSmall.lean :: BoolCircuit.exists_threeLine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three-line representation of a Boolean function

**Claim.** Every Boolean function on two input bits is computed by a valid straight-line program of length exactly three.

**Proof.** Let $a,b,c,d$ be the function's values on inputs $(0,0),(1,0),(0,1),(1,1)$, respectively. The truth-table construction `table2` selects a three-statement program with operations and input literals arranged to realize these four values. The evaluation formula for a three-line shape (`Shape3.prog_eval`) expresses the output as an outer operation applied to two inner operations on the chosen literals. For an arbitrary input $x$, identify it with the pair $(x_0,x_1)$. The Boolean identity for the selected table shape then says its output is $a$ when both bits are false, $b$ when only the first is true, $c$ when only the second is true, and $d$ when both are true. Thus it equals the function at every input. The constructed program has length three by its definition.

**Key facts.** `BoolCircuit.Shape3.prog_eval`.
