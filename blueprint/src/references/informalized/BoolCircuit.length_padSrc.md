<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauCircuit.lean :: BoolCircuit.length_padSrc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the padded source list

**Claim.** The padded source list has length $m$.

**Proof.** The list is defined by taking the first $m$ entries of a list followed by $m$ false-constant sources. This concatenated list has at least $m$ entries, so taking its first $m$ entries yields a list of length $m$.
