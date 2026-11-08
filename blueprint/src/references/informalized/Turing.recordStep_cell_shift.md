<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_cell_shift -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recorded Cell Mark Shift

**Claim.** The specified scan preserves each cell's content and moves its unique mark from the cell indexed by $h$ to the cell indexed by $h+m$.

**Proof.** For zero movement, the scan leaves the list unchanged: the fold-scan identity (`scanResult_fold`) says the contents are unchanged, and the requested mark position is still $h$. For positive movement, the right-shift scan has the list description given by `scanResult_shiftRight`: each cell receives the previous mark from its left neighbor, with the initial carry false. Comparing entries, contents are unchanged and the mark at index $j$ is precisely the test that $h+1=j-s$. The left-shift scan is described by `scanResult_shiftLeft`, where each cell receives the mark from its right neighbor and the terminal carry is false. Entrywise, its mark is precisely the test that $h-1=j-s$. The bound $|h|\le s$ ensures the shifted mark remains within the displayed window, so the boundary cells correctly receive false. These three cases give the stated formula for every allowed movement.

**Key facts.** `Turing.scanResult_fold`, `Turing.scanResult_shiftRight`, `Turing.scanResult_shiftLeft`.
