<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonSearchFamily.lean :: BoolCircuit.DAGCircuit.rewire_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation after rewiring

**Claim.** For each assignment $x$ to the $k$ inputs, the rewired circuit evaluates to the value of $C$ when its $i$th input is assigned the value at index `srcs[i]` in the list formed by appending $0,1$ to $x$.

**Proof.** First, running the two constant gates from the initial input values appends $0$ and $1$, so the resulting list is `List.ofFn x ++ [false, true]`; this list has length $k+2$. The run of a gate list followed by another gate list is the run of the first followed by the run of the second (`runWith_append`). Thus the rewired circuit first produces that extended input list and then runs the embedded gates. The embedded-gates evaluation theorem (`runWith_embedGates_getD`) says that the output vertex of this latter run has the value of $C$ evaluated with its $i$th input read from the extended list at `srcs[i]`. The source bound ensures every listed index lies within the extended list, and its length is $k+2$, so this is exactly the claimed evaluation.

**Key facts.** `BoolCircuit.runWith_append`, `BoolCircuit.runWith_embedGates_getD`.
