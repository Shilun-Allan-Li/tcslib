<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Hierarchy.lean :: Language.zero_inTreeSize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty Language Tree Size

**Claim.** For any size bound $T$ with $1\le T(n)$ at every input length, the empty language has a Boolean tree circuit at each length whose size is at most $T(n)$ and whose acceptance agrees with membership in the empty language.

**Proof.** At each input length $n$, choose the empty OR-node. Its size is $1$, so the hypothesis $1\le T(n)$ gives the required size bound. Its evaluation is false on every input, since an empty OR-node evaluates to false (`BoolCircuit.eval_node_nil`). No word belongs to the empty language, so membership is false for every word; hence its acceptance condition agrees with membership.

**Key facts.** `BoolCircuit.eval_node_nil`.
