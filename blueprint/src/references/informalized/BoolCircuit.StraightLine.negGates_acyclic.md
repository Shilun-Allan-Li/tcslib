<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLine.lean :: BoolCircuit.StraightLine.negGates_acyclic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acyclicity of the Negation Gates

**Claim.** The list of input-negation gates is acyclic: a gate at position $i$ reads only vertices with index less than $n+i$.

**Proof.** At position $i$ in the mapped range, the corresponding gate has the single argument $i$. The list has length $n$, so its positions satisfy $i<n$. Consequently $i<n+i$, which is the required bound for its only argument.

**Key facts.** `BoolCircuit.StraightLine.length_negGates`.
