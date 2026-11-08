<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.mapBuffer_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Capture-Head Rewind

**Claim.** For each $j$ no greater than the original output length, the threaded-map controller runs for $j+1$ steps from capture-rewind state at displacement $j-1$ to input-rewind state at displacement zero, keeping the input head and empty output fixed.

**Proof.** Induct on $j$. At $j=0$, the capture displacement is $-1$, where the buffer tape has no symbol ($\mathrm{bufferTape\_left}$). The controller therefore takes its exit action: its capture-head movement is zero, its input-head movement is zero, and it enters input-rewind state. The zero-run identity and the fact that a zero input-head movement leaves the position fixed ($\mathrm{moveInputPos\_zero}$) give the claimed configuration after one step. For the successor case, the capture displacement corresponding to $j+1$ simplifies to $j$. Since $j$ is within the original output, the capture tape contains the $j$-th output symbol at that position. The controller's rule in capture-rewind state moves the capture head left and remains in that state. The action updates the displacement to $j-1$ and otherwise preserves the represented configuration. The run successor identity reduces the desired run to this first step followed by the induction-hypothesis run from displacement $j-1$. The bound $j+1\le |c.\mathrm{output}|$ ensures the symbol lookup used in this step is valid.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.FinTM.bufferTape_left`, `Turing.FinTM.mapAction_apply`, `Turing.moveInputPos_zero`.
