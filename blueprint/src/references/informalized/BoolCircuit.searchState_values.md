<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonSearch.lean :: BoolCircuit.searchState_values -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values produced by the search construction

**Claim.** After $j$ stages, evaluating the search-state gates on $x$ gives true at vertex $n$, and the listed output vertices have values equal, in order, to the sequential search bits.

**Proof.** Induct on the number of stages. Initially the state contains a constant-true gate and no outputs, so vertex $n$ evaluates to true and the empty output list agrees with the empty search-bit list. For the successor step, let $s$ be the previous state and let `vals` be the values of its gates on $x$. The structural theorem (`searchState_struct`) ensures that the old output vertices are valid and that vertex $n$ is present. The new stage's sources consist of the original input vertices, the old output vertices, and vertex $n$, so they are valid positions in `vals`; their number is exactly the next circuit's input count. The induction hypothesis and the fact that the original input positions retain their values show that these sources carry precisely $x$, the previously found bits, and true. Old vertex values are unchanged when gates are appended (`runWith_getD_of_lt`), so vertex $n$ remains true and the old outputs still give the previous search bits. The embedding evaluation theorem (`runWith_embedGates_getD`) identifies the new output vertex's value with the next circuit evaluated on those sources. Since the sources carry the input, previous bits, and final true bit, this value is exactly the next bit specified by sequential search. Appending that value to the old output values proves the induction step.

**Key facts.** `BoolCircuit.searchState_struct`, `BoolCircuit.runWith_getD_of_lt`, `BoolCircuit.runWith_embedGates_getD`.
