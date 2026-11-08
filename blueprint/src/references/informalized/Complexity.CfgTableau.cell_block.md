<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.CfgTableau.cell_block -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of a Cell Block

**Claim.** If every block before the index assigned to cell $(t,\tau,r)$ agrees with its expected tableau block, then evaluating the padded local sources for this cell and applying the cell update rule gives exactly its expected encoding.

**Proof.** Set $z=r-T$ and let $l$ be the evaluated padded source list. Its first thirteen entries encode the time-zero flag, whether the cell is at the origin, the previous-step head flags and contents at the left, current, and right cells, and the current-step chain information from the left neighbor. All referenced block indices lie before the target cell index, so the block hypothesis identifies their contents with the expected encodings. The source evaluation fact (`eval_block`) and the identification of a cell index with its expected cell encoding (`cfgExp_cellIdx`) therefore supply the stated local data. The source-list decomposition and padding facts (`drop_take_padSrcs` and `length_prevSnapSrcs`) also show that the trailing snapshot sources decode to the snapshot at the preceding time; the encoding-decoding identity (`snapDecode_snapEncode`) recovers that snapshot.

Proceed by cases on $t$. At time zero, the initial configuration has its work head at the origin and its work tape blank, while the work chain is empty (`workChain_zero`). The zero-time cell update rule (`cfgF_cell_zero`) then gives precisely the expected head flag, tape-symbol encoding, and chain encoding.

For $t+1$, every valid cell in row $t$ has index below the target in row $t+1$: the bounds follow from `cellIdx_lt_succ` and `le_cellIdx`. Thus all three neighbor encodings at time $t$ are available under the block hypothesis, including the boundary cases, where the corresponding source flag suppresses an out-of-range neighbor. The head-position bound `abs_workTapePos_le` ensures that the head cannot lie beyond the time-allowed region. The left-neighbor chain bits are obtained from the current-row source list (`chSrc`); when $r=0$, the left chain is empty by `workChain_left`, using $t+1\le T$. With these facts, the successor cell update rule (`cfgF_cell_succ`) applies: its snapshot input is the true preceding snapshot, its three head indicators and current symbol bits are the expected ones, and its left-chain bits match the required chain data. It returns exactly the expected encoding of cell $(t+1,\tau,r)$, completing the induction split.

**Key facts.** `Complexity.eval_block`, `Complexity.cfgExp_cellIdx`, `Complexity.drop_take_padSrcs`, `Complexity.length_prevSnapSrcs`, `Complexity.prevSnapSrcs_eval`, `Complexity.snapDecode_snapEncode`, `Complexity.workChain_zero`, `Complexity.cfgF_cell_zero`, `Complexity.cellIdx_lt_succ`, `Complexity.le_cellIdx`, `Complexity.abs_workTapePos_le`, `Complexity.workChain_left`, `Complexity.cfgF_cell_succ`.
