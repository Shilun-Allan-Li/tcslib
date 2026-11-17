<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.RI_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Input Position

**Claim.** In the initial configuration, the input symbol seen at offset $d$ is the extended input lookup at $1+d$.

**Proof.** The initial configuration places the shifted input head at position $1$. The input read at offset $d$ is therefore the extended lookup at the head position plus $d$, namely $1+d$. Unfolding the definitions gives the stated equality.
