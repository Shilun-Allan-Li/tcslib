<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean :: Complexity.LogProg.valPairs_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Paired-scan validation

**Claim.** Under the transition identities and no-call assumptions, scanning an aligned word either reaches the state and input position associated with its successful scan remainder, or rejects when the scan fails, while preserving the indicated register positions and avoiding call states before the endpoint.

**Proof.** Proceed by two-step induction on $z$, since the scanner reads two bits at a time. For the empty word, scanning cannot return a remainder; the machine rejects at its initial state because the input is at the boundary. For a one-bit word, the first transition consumes that bit and records it in the state. The next input position is the boundary, so the machine rejects there. These boundary rejection steps use `rejects_one`, and the one-step transitions use `reaches_right`.

For $z=b::b'::rest$, the first transition reads $b$ and enters the state remembering it. Split into the four possible pairs. On $00$, the next transition records a previous false bit and returns to the scan state; the induction hypothesis applies to the remaining word with that remembered bit. Both successful reachability and rejection are prefixed by these two transitions using `Reaches.step` and `Rejects.step`. On $11$, the machine similarly records a previous true bit, and the same induction argument applies. In both cases the endpoint position is the two-step advance plus the inductive remainder position; the given alignment equation supplies the required input-position bounds.

On $01$, this pair is the separator. If the remembered bit is false, the scanner rejects immediately, as required by the scan definition. Otherwise it enters the state for validating the final word and the scan result is exactly the remaining suffix; `Reaches.refl` supplies the zero-length continuation to that endpoint. On $10$, the pair is malformed, so the machine rejects immediately. In every branch, the assumed state transitions and no-call conditions ensure that each intermediate configuration has the prescribed register-head positions and is not a call state.

**Key facts.** `Complexity.LogProg.rejects_one`, `Complexity.LogProg.reaches_right`, `Complexity.LogProg.Reaches.step`, `Complexity.LogProg.Rejects.step`, `Complexity.LogProg.Reaches.refl`.
