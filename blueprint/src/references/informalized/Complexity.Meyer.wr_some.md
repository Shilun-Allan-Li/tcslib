<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.wr_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prescribed Tape Write

**Claim.** When the write instruction prescribes a symbol $s$, applying it replaces the tape value at $z$ by $s$ and leaves all other values unchanged.

**Proof.** By definition, a prescribed write returns the function obtained by updating $\tau$ at $z$ with value $s$. This is exactly the asserted tape modification.
