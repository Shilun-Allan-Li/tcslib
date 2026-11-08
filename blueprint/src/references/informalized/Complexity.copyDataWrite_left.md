<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.copyDataWrite_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Writing the Left Boundary Payload

**Claim.** If every current payload is blank, then writing the left-boundary payload at coordinate $-1$ on the input lane makes every current payload equal to the copied payload with count $0$.

**Proof.** Separate the work lanes from the input lane. A work lane is not modified by this write, so its current payload remains blank by hypothesis, as does its copied payload. On the input lane, at coordinate $-1$ the write replaces the cell's current component by the left-boundary payload $(\mathrm{none},1)$, which is exactly the copied payload at count $0$ there. At every other coordinate, the tape is unchanged and remains blank by hypothesis; the count-zero copied payload is also blank there. Thus the equality holds at each lane and coordinate.
