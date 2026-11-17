<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SizeClasses.lean :: BoolCircuit.allOnesFamily_circuit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit of the All-Ones Family

**Claim.** For every natural number $n$, the circuit assigned by the all-ones family to inputs of length $n$ is exactly the depth-one circuit with input nodes indexed by $\mathrm{Fin}(n)$, one output node, and an AND gate taking all $n$ input values.

**Proof.** Both sides are given by the same circuit construction: depth one, input nodes indexed by $\mathrm{Fin}(n)$, a unique output node, and the sole gate is the AND gate whose inputs range over all of $\mathrm{Fin}(n)$. Their defining data therefore agree, so the circuits are equal.
