<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean :: Complexity.LogProg.ps_index -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register-program phase transfer

**Claim.** Under the stated input-size and register bounds, the path program started at the earlier stage with configuration $\sigma$ has the same termination, register-bound, and acceptance properties as the specified run from the intermediate stage.

**Proof.** The proof first uses the row-major index bound (`Complexity.rowMajor_lt`) to see that $s n+\mathrm{nx}<n^2$. Together with the input-size hypothesis, this ensures the input pointer for the indexed entry is within the encoded input; the register bounds also keep the intermediate arithmetic within $B$. From the earlier stage, the program clears its input-pointer register and enters the row-processing phase. The proof transfers the claimed semantics backward through these instructions using the preservation facts for clearing and incrementing a register (`Complexity.LogProg.NSem.clr`, `Complexity.LogProg.NSem.inc`), with the register-bound invariant supplied by `Complexity.LogProg.PReg.reg`. It then applies the row-phase transfer (`Complexity.LogProg.ps_row`), which reduces the claim to the corresponding column-processing phase for the selected row. In that phase, the program clears the column counter and uses its three-increment loop to position the input pointer at the desired row-major entry; the two-increment transfer theorem (`Complexity.LogProg.nsem_addTwice`) establishes the required semantics and bound for this loop. Finally, a configuration equality identifies the resulting state with the one in the hypothesis, so the assumed property transfers back to the earlier stage (`Complexity.LogProg.PS.of_eq`).

**Key facts.** `Complexity.rowMajor_lt`, `Complexity.LogProg.PReg.reg`, `Complexity.LogProg.NSem.clr`, `Complexity.LogProg.NSem.inc`, `Complexity.LogProg.ps_row`, `Complexity.LogProg.nsem_addTwice`, `Complexity.LogProg.PS.of_eq`.
