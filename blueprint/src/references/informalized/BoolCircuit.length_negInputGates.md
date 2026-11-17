<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/BookModelBasics.lean :: BoolCircuit.length_negInputGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Number of negation input gates

**Claim.** For every $n\in\mathbb{N}$, the list of negation gates on the $n$ input vertices has length $n$.

**Proof.** The list is formed by mapping the construction of a negation gate over `List.range n`. The range has length $n$, and mapping preserves length, so the gate list has length $n$.
