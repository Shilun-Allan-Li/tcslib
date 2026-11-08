<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyProgram.lean :: BoolCircuit.progRun_getD_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of Initial Blocks

**Claim.** For any instruction-kind type, function $F$ assigning a Boolean-list function to each kind, input list $x$, program, initial list of Boolean blocks, and index $i$ below the length of the initial list, executing the program leaves the block at index $i$ equal to its initial value.

**Proof.** Induct on the program, allowing the initial list to vary in the induction hypothesis. The empty program leaves the list unchanged. For a program beginning with instruction $g$ and remaining program $gs$, executing $g$ appends one new block to the initial list: the result is the initial list followed by the block computed from $g$. Since $i$ is below the original list's length, it is still below the length of this extended list. Apply the induction hypothesis to $gs$ with that extended list; the final list's $i$th block is therefore the extended list's $i$th block. Appending a block does not change a lookup at an index already in the original list, so this is exactly the original $i$th block.
