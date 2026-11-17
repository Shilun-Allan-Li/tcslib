<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.LayeredCircuit.evalNode_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor Layer Evaluation

**Claim.** For a layered circuit $F$, a node $u$ at layer $m+1$ evaluates to the value computed by its gate from the values of its input nodes at layer $m$.

**Proof.** By the recursive definition of node evaluation, evaluation at a successor layer applies the gate attached to that layer to the assignment of values obtained by evaluating the preceding layer. Thus the value of $u$ is the evaluation of its gate on the function sending each preceding-layer node $v$ to its value under the same input assignment.
