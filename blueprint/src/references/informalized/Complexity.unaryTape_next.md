<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.unaryTape_next -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending a Unary Marker

**Claim.** Updating cell $N+1$ of the unary tape with $N$ markers to a unit marker gives the unary tape with $N+1$ markers.

**Proof.** Compare the two tapes at an arbitrary cell $z$. If $z=N+1$, the old tape has no marker there: the position is nonzero and lies just beyond the old unit-marker interval. The update therefore places a unit marker there, exactly as the tape with $N+1$ markers does. If $z\ne N+1$, the update leaves the value unchanged. Away from this endpoint, the old interval of unit-marker positions and the new one agree, and the origin case is unchanged. Thus the tapes agree at every position.
