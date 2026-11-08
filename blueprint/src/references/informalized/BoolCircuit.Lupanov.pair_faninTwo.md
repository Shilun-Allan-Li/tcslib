<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.pair_faninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Well-formedness of a two-input gate

**Claim.** If $k$ is not NOT and $a\ne b$, then the gate of kind $k$ with inputs $a,b$ is well formed and has at most two inputs.

**Proof.** The inequality $a\ne b$ says precisely that the two-entry list $[a,b]$ has no repeated entries. Its length is two, so it meets the fan-in bound. Because $k$ is not NOT, the condition that a NOT gate have exactly one input is vacuous. Thus the gate is well formed and has at most two inputs.
