<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Hierarchy.lean :: BoolCircuit.padLanguage_inTreeSize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tree-Size Representation of a Padded Language

**Claim.** Under the stated upper bound on $T'(n)$, the language accepted by the padded circuits has a family of tree circuits of size at most $T'(n)$ at every input length, recognizing the language exactly.

**Proof.** Choose the padded circuit family itself as the representing family. At length $n$, widening preserves tree size (`BoolCircuit.widenCircuit_size`), so its size is the size of the universal circuit for $F_n$. The universal-circuit size bound gives a size at most $2^{\ell(n)}(\ell(n)+1)+1$ (`BoolCircuit.universalCircuit_size_le`), which is at most $T'(n)$ by hypothesis. Finally, membership in the padded language is defined by acceptance of the padded circuit at the word's length, so the required recognition equivalence holds directly.

**Key facts.** `BoolCircuit.widenCircuit_size`, `BoolCircuit.universalCircuit_size_le`.
