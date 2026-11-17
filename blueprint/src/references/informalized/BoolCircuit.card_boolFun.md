<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/ShannonProbabilistic.lean :: BoolCircuit.card_boolFun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Number of Boolean Functions

**Claim.** For every natural number $n$, the set of Boolean functions on assignments to $n$ Boolean variables has cardinality $2^{2^n}$.

**Proof.** There are $2^n$ assignments to $n$ Boolean variables. A Boolean function chooses one of two output values independently at each assignment, so the number of such functions is $2^{2^n}$.
