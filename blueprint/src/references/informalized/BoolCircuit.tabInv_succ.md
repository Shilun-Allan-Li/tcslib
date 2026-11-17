<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauCircuit.lean :: BoolCircuit.tabInv_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor Step for the Tabulation Invariant

**Claim.** If the vertex values after the first $i$ instructions satisfy the tabulation invariant, then running the gates for instruction $i$ produces vertex values satisfying it after the first $i+1$ instructions.

**Proof.** Let $V$ be the current vertex-value list. The invariant gives its length as the start of instruction $i$'s block. Since that instruction has exactly $m$ sources, padding its sources does not change the list. Its initial copy gates therefore append the values of precisely those sources: each source is read from a vertex below the current block boundary (BoolCircuit.tabSrc_lt), and the invariant's source-evaluation property identifies that value with the source's program meaning (BoolCircuit.tabSrc_eval). Thus the copied source values occupy the next $m$ positions.

The remaining gates implement the fixed gadget for the instruction kind. The gadget list has one circuit per output coordinate, and its embedded width is at most the common tabulation width (BoolCircuit.kindWidth_le_tabG). Reindexing the gadget inputs by the consecutive positions just filled is justified by the embedding identity for shifted inputs (BoolCircuit.embedAll_range'_eq). Running the embedded gadgets then places their output values at the positions specified by the gadget offsets: the embedding evaluation property (BoolCircuit.runWith_embedAll_getD) reduces each such value to evaluation of the corresponding gadget. Each gadget computes its designated coordinate of the instruction-kind function (BoolCircuit.gadget_eval); the program evaluation identity (BoolCircuit.progBlocks_getD) identifies that coordinate with the desired output of instruction $i$.

The unused portion of the common width is filled by true constant gates, whose evaluation appends exactly those values (BoolCircuit.runWith_eval_constGates). The final copy gates transfer the $w$ gadget outputs into the designated output-coordinate positions. Their offsets lie within the gadget width (BoolCircuit.embedOffset_lt), so these reads are valid. The resulting list consequently has the prescribed next-block length, and the invariant's input, constants, and fixed-prefix entries remain unchanged because all newly appended gates only extend the list (BoolCircuit.runWith_getD_of_lt). Earlier instruction outputs are also unchanged for the same reason. The new block's output entries are exactly the values established for the $w$ coordinates above, completing every clause of the invariant at $i+1$.

**Key facts.** `BoolCircuit.tabSrc_lt`, `BoolCircuit.tabSrc_eval`, `BoolCircuit.kindWidth_le_tabG`, `BoolCircuit.embedAll_range'_eq`, `BoolCircuit.runWith_embedAll_getD`, `BoolCircuit.gadget_eval`, `BoolCircuit.progBlocks_getD`, `BoolCircuit.runWith_eval_constGates`, `BoolCircuit.embedOffset_lt`, `BoolCircuit.runWith_getD_of_lt`.
