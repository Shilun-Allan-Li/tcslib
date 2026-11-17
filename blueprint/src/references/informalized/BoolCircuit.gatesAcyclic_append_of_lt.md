<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FanOut.lean :: BoolCircuit.gatesAcyclic_append_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acyclicity under appending gates

**Claim.** If $gs$ is acyclic from index bound $n$ and every input read by a gate in $ext$ is less than $n+|gs|$, then $gs$ followed by $ext$ is acyclic from $n$.

**Proof.** Fix a gate position $i$ in the concatenated list and an input $a$ read by that gate. If $i<|gs|$, the gate at position $i$ is the same as in $gs$, so its input satisfies $a<n+i$ by the assumed acyclicity of $gs$. Otherwise, the gate is in $ext$; the hypothesis gives $a<n+|gs|$. Since $i\ge |gs|$, this implies $a<n+i$. Thus every gate reads only indices below its bound.
