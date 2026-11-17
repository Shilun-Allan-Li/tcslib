<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/BookModelBasics.lean :: BoolCircuit.negInputGates_acyclic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acyclicity of input-negation gates

**Claim.** For every nonnegative integer $n$, the list of $n$ input-negation gates is acyclic: at position $i$, every input vertex has index strictly less than $n+i$.

**Proof.** At position $i$ in the list of input-negation gates, the gate reads only vertex $i$, because the list is obtained by mapping the range of indices to NOT gates with that single input. The list has length $n$ (`length_negInputGates`), so the position condition gives $i<n$. Consequently $i<n+i$, which is the required acyclicity bound.

**Key facts.** `BoolCircuit.length_negInputGates`.
