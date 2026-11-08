<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigCircuit.lean :: Complexity.length_snapWorkSrcs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-Tape Snapshot Source Length

**Claim.** For every time $t$, the list of sources encoding the work-tape contents in the snapshot has length $2k$, where $k$ is the number of work tapes of $M$.

**Proof.** The list ranges over the $k$ work tapes and contributes two sources for each tape. By the constant-length flat-map formula, a flat-map whose inner list always has length two has total length equal to the outer list's length times two (`Complexity.CfgTableau.length_flatMap_const`). The finite range of tape indices has length $k$, giving $2k$ after rearranging the product.

**Key facts.** `Complexity.CfgTableau.length_flatMap_const`.
