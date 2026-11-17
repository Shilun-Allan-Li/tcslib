<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ZeroSpace.lean :: Complexity.exists_zeroTape_parity_decider -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-tape parity decider

**Claim.** There exists a finite Turing machine with no work tapes that halts within $|x|+1$ steps on every Boolean word $x$ and outputs $1$ exactly when the number of true entries of $x$ is even, and $0$ otherwise.

**Proof.** Take the machine `evenScanTM`. Its verified time-bound and correctness property is precisely that it decides the even-parity language within $|x|+1$ steps (`evenScanTM_decidesInTime`). The machine has zero work tapes by its definition, so it supplies the required witness.

**Key facts.** `Complexity.evenScanTM_decidesInTime`.
