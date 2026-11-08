<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyProgram.lean :: BoolCircuit.progBlocks_getD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Computed block at a program position

**Claim.** At any valid position $i$ in a well-formed program, the block stored at position $i$ is the value of the instruction's kind function on its source bits evaluated against the input and the program's computed blocks.

**Proof.** Split the program at position $i$: write it as its prefix of length $i$, followed by instruction $i$ and the remaining suffix. Execute the prefix first, starting from the empty state, and call the resulting list of blocks $\mathrm{pre}$. Its length is $i$. The concatenation law for execution (BoolCircuit.progRun_append) says that executing the whole program is equivalent to continuing from $\mathrm{pre}$ with instruction $i$ and then the suffix. The earlier-state lookup law (BoolCircuit.progRun_getD_of_lt) shows that executing this continuation leaves every entry at an index below $i$ unchanged; at index $i$, the appended block is precisely the result of applying $F$ to instruction $i$'s kind and its sources evaluated using $\mathrm{pre}$. For each source of instruction $i$, well-formedness makes it either an input, a constant, or a bit of a block at some index below $i$. Its validity therefore ensures its evaluation is unchanged when the earlier blocks in $\mathrm{pre}$ are replaced by the corresponding blocks in the full run (BoolCircuit.BitSrc.eval_congr). Applying this pointwise to the source list identifies the newly appended block with the stated value, proving the claim.

**Key facts.** `BoolCircuit.progRun_append`, `BoolCircuit.progRun_getD_of_lt`, `BoolCircuit.BitSrc.eval_congr`.
