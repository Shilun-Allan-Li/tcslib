<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: BoolCircuit.length_parityPairs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Number of parity pairs

**Claim.** For every natural number $n$, the list of pairs consisting, for each of the $n$ variables, of its positive and negative literals has length $n$.

**Proof.** The list is obtained by mapping the construction of one literal pair over `List.finRange n`. That range has length $n$, and mapping preserves length. Hence the list of pairs has length $n$.
