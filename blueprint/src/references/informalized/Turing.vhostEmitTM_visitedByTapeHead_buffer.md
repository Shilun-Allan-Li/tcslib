<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean :: Turing.vhostEmitTM_visitedByTapeHead_buffer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Visited Cells of the Virtual Input Head

**Claim.** The buffer tape visits exactly the integer positions obtained by subtracting $1$ from $M$'s input-head position at each time through $t$.

**Proof.** Unfold the visited-cell set as the image of times $0,1,\ldots,t$ under the buffer-head position. At any such time $u$, the run-correspondence theorem (`Turing.vhostEmitTM_runFrom`) identifies the virtual-host configuration with the encoding of $M$'s configuration at time $u$, for a suitable tag. In that encoding, the buffer-head position is the input-head position of $M$ minus $1$. The position functions therefore agree at every time in the range, giving the stated equality of image sets.

**Key facts.** `Turing.vhostEmitTM_runFrom`.
