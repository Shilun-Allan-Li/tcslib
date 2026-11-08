<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SizeClasses.lean :: BoolCircuit.allOnesCircuit_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the All-Ones Circuit

**Claim.** For every natural number $n$, the all-ones circuit on $n$ inputs has size $1$.

**Proof.** The circuit has depth one, with a single output node at the only gate layer. Thus the set of gate-layer nodes is equivalent to the set of pairs consisting of the unique layer in $\mathrm{Fin}(1)$ and a node of type $\mathrm{Unit}$. This set has exactly one element, so its cardinality, which defines the circuit size, is $1$.
