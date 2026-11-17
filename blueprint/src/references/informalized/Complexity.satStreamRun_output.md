<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamRun_output -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output as Round Chunks

**Claim.** For every input bit string $x$, round count $k$, and initial streaming state $s$, the run's output is the concatenation, in order, of the chunks emitted by each successive round-state update, for rounds $0$ through $k-1$.

**Proof.** Induct on $k$, generalizing over the initial state. At zero rounds both the run's output and the concatenation over the empty range are empty. For a successor number of rounds, the run first performs one round from $s$, then runs the remaining $k$ rounds from the state produced by that round, concatenating the first chunk with the rest of the output. By induction, that remaining output is the concatenation of the chunks at iterates $1$ through $k$. The range decomposition for $k+1$ consists of the initial index followed by those shifted indices, so this is exactly the asserted ordered concatenation.
