<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.unaryTape_unit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unit Markers on the Unary Tape

**Claim.** If $j<N$, then the unary tape with $N$ markers carries a unit marker at cell $j+1$.

**Proof.** Since $j<N$, the position $j+1$ is positive and at most $N$. It is therefore not the origin, and it lies in the interval assigned unit markers by the tape definition. The tape value there is a unit marker.
