<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.circuitQuadraticVariableCount_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic variable count

**Claim.** For a Boolean circuit $C$ with $n$ input bits and $g$ gates, its quadratic variable count is $n+g+1$.

**Proof.** By definition, the variable count is $1+(n+g)$. Associativity and commutativity of natural-number addition rearrange this as $n+g+1$.
