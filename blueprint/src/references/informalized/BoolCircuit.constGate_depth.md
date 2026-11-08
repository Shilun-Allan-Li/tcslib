<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.constGate_depth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth of a constant gate

**Claim.** For every Boolean value $b$ and every list of assigned vertex depths, the constant gate has depth $1$.

**Proof.** The proof considers the two possible values of $b$. In either case, the constant gate has an empty argument list. The maximum depth contribution from its arguments is therefore the fold of the empty list, which is $0$. Its depth is consequently $1+0=1$.
