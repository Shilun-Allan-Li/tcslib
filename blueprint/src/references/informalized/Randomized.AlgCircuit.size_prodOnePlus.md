<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuitExample.lean :: Randomized.AlgCircuit.size_prodOnePlus -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the product circuit

**Claim.** For every natural number $n$, the circuit constructed to compute the product of the first $n$ factors has size $3n+1$.

**Proof.** The circuit's size is the length of its gate list. The gate-list length formula, which gives length $3k+1$ for `prodOnePlusGates k` (`Randomized.AlgCircuit.length_prodOnePlusGates`), applied at $k=n$ therefore gives the claimed size.

**Key facts.** `Randomized.AlgCircuit.length_prodOnePlusGates`.
