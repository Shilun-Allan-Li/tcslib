<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.vtype_gate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate Vertex Type

**Claim.** Under the stated lookup hypothesis and $n\le V$, the vertex $V$ lies below the circuit size and has type $t$ exactly when the optional gate kind of $g$ equals $t$.

**Proof.** The lookup hypothesis forces $V-n$ to be a valid index in the gate list: otherwise the out-of-range list lookup would be none, contradicting that it equals $g$. Since $n\le V$, vertex $V$ is not an input vertex, so its type is the kind of the gate at index $V-n$. The lookup hypothesis identifies that gate with $g$, hence the type is $\mathrm{some}(g.\mathrm{kind})$. The same index bound gives $V<n+|\mathrm{gates}|$, which is the circuit size. Thus the left-hand condition is equivalent to $\mathrm{some}(g.\mathrm{kind})=t$.
