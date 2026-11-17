<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigCircuit.lean :: Complexity.cellSrcs_valid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity of Cell Sources

**Claim.** Every source in the list constructed for cell $(t,\tau,r)$ is valid for input length $n$, block width equal to the snapshot width plus $5$, and current block index equal to that cell's index.

**Proof.** Let $i$ be the current cell index. The lower-bound fact (`Complexity.le_cellIdx`) says that the start of time block $t$, namely $t$ times the stride, is at most $i$. Every source bit position used in the list is below $5$, hence below the block width, which is the snapshot width plus $5$. The constant sources are valid automatically.

For each neighbor source, if its condition is false it is a constant and is therefore valid. If its condition is true, it refers to the preceding time block at a cell whose row is within the allowed range. The cell-index bound (`Complexity.cellIdx_lt_succ`) places that referenced cell strictly before the end of the preceding block; `Complexity.prevStep_lt` then shows it is earlier than the current index $i$. Its bit position is within the width by the bound just established. The same reasoning applies to the center-neighbor sources, whose validity condition supplies the required row bound. For each horizontal source, when the row is nonzero the referenced cell at row $r-1$ is earlier than the current cell; otherwise the source is constant. Finally, every source in the appended previous-snapshot list is valid at index $i$ by `Complexity.prevSnapSrcs_valid`, using the lower bound on $i$. These cases cover all entries of the constructed list.

**Key facts.** `Complexity.le_cellIdx`, `Complexity.cellIdx_lt_succ`, `Complexity.prevStep_lt`, `Complexity.prevSnapSrcs_valid`.
