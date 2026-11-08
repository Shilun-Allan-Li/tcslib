<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean :: BoolCircuit.constZeroCircuit_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the zero circuit

**Claim.** For every natural number $n$, the zero circuit with $n$ inputs has size $2$.

**Proof.** The size counts the nodes in the layers after the input layer. Each of the two layers has node type $\mathrm{Unit}$, a singleton. Their disjoint union therefore has two elements, so the circuit has size $2$.
