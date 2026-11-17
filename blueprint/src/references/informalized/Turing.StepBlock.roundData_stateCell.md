<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.roundData_stateCell -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Summary Tape Cell Alignment

**Claim.** For every integer $z\ge -1$, the summary tape of the round configuration at cell $2+z$ contains exactly the symbol that the buffer tape stores for the state word at cell $z$.

**Proof.** By construction, the summary tape is the second of the two auxiliary tapes, and its contents in the round configuration are given by `summaryCells summary word`. The fact that the auxiliary tape index selects this component reduces the desired equality to the shift identity for summary cells: at position $2+z$, the special summary cell at position zero is avoided for $z\ge -1$, and the buffer index becomes $(2+z)-2=z$. Thus the symbol is `FinTM.bufferTape word z`, as claimed.

**Key facts.** `Turing.StepBlock.summaryCells_shift`.
