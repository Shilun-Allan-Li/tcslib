<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.bufferTape_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Left blank cell

**Claim.** The buffer tape for any finite word contains no symbol at integer cell $-1$.

**Proof.** The cell $-1$ is negative, so the nonnegative-cell condition in the buffer-tape definition fails. Hence the tape value there is `none`.
