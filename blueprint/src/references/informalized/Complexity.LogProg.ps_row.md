<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean :: Complexity.LogProg.ps_row -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matrix-row scan

**Claim.** From the row-scan stage, the program terminates within the register bound and accepts exactly when the supplied column-check continuation accepts.

**Proof.** Induct on the difference $s-a$, the number of row increments still needed to reach the source row $s$. If $a=s$, the equality branch goes directly to the column-check stage. The pointer formula is then already the one for row $s$, and the current column is at most $n$, so the assumed continuation applies. If $a<s$, the program takes the unequal branch, clears the column counter, and uses its repeated-increment loop to add $2n$ to the pointer while preserving the other relevant registers (`nsem_addTwice`). It then increments the row counter and sets the column counter to $n$. The pointer now has the required form for row $a+1$; the bounds follow from $a+1\le s<n$, while the matrix-region length assumption supplies the needed input extent. The induction hypothesis therefore applies to the next row, with the original continuation hypothesis still available for every column. The two branches preserve acceptance exactly because they perform only the stated counter and pointer updates before reaching the continuation.

**Key facts.** `Complexity.LogProg.NSem.jeq_pos`, `Complexity.LogProg.NSem.jeq_neg`, `Complexity.LogProg.NSem.clr`, `Complexity.LogProg.nsem_addTwice`, `Complexity.LogProg.NSem.inc`, `Complexity.LogProg.PReg.reg`, `Complexity.LogProg.PS.of_eq`.
