<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableau.lean :: Complexity.length_tableauSources -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tableau source-list length

**Claim.** For every finite-state Turing machine $M$ with Boolean input alphabet and all $n,t\in\mathbb{N}$, the source list for time $t$ has length equal to the tableau arity $B+3+k(B+1)+1$, where $B$ is the number of bits in a snapshot and $k$ is the number of work tapes.

**Proof.** The first block of sources has length $B$: at time zero it is a list of $B$ repeated constants, and otherwise it is a tableau block indexed by the $B$ snapshot bits. The next fixed block contributes three sources. For each of the $k$ work tapes, its source list has length $B+1$ by the tape-source length result (Complexity.length_tableauTapeSources); hence the flattened collection of tape sources has length $k(B+1)$ by the constant-length flat-map formula (Complexity.CfgTableau.length_flatMap_const). The final accumulator source contributes one more entry. Adding these lengths gives $B+3+k(B+1)+1$, which is the tableau arity.

**Key facts.** `Complexity.length_tableauTapeSources`, `Complexity.CfgTableau.length_flatMap_const`.
