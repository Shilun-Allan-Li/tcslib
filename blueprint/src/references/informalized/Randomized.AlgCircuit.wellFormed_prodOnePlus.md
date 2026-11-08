<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuitExample.lean :: Randomized.AlgCircuit.wellFormed_prodOnePlus -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Well-Formed Product Circuit

**Claim.** For every nonnegative integer $n$, the circuit formed by taking the product of one plus each input is well formed: it has at least one gate, and each gate's references point only to earlier nodes.

**Proof.** The circuit is well formed once we verify its two defining conditions. Its gate list has length $3n+1$ (`length_prodOnePlusGates`), which is positive, so the list is nonempty. For any position $i$ within that list, `refsBelow_prodOnePlusGates` says that the gate at $i$ has all its references below $i$. These are exactly the required conditions.

**Key facts.** `Randomized.AlgCircuit.length_prodOnePlusGates`, `Randomized.AlgCircuit.refsBelow_prodOnePlusGates`.
