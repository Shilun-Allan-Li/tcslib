<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLine.lean :: BoolCircuit.StraightLine.vertexValue_negGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negated Input Gate Values

**Claim.** For an input assignment $x$ and input index $k$, the value at vertex $n+k$ in the list of input-negation gates is $!x_k$.

**Proof.** The initial value list contains the $n$ inputs. The gate at position $k$ in the negation-gate list is the negation gate whose sole argument is input vertex $k$. The value at the corresponding vertex $n+k$ is therefore the evaluation of this gate on the values produced by the preceding gates (BoolCircuit.runWith_getD_gate). Those preceding gates are the negations for inputs below $k$; evaluating their list shows that the value at vertex $k$ is still $x_k$ (BoolCircuit.runWith_getD_of_lt). The gate at $k$ negates that value, giving $!x_k$.

**Key facts.** `BoolCircuit.runWith_getD_gate`, `BoolCircuit.runWith_getD_of_lt`.
