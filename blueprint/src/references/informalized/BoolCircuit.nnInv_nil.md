<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictFanOut.lean :: BoolCircuit.nnInv_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariant for the empty gate list

**Claim.** The empty gate list, identity tap map, and counter $n$ satisfy the construction invariant, including acyclicity, tap bounds and injectivity, value preservation, fanout bounds, gate conditions, and the size bound.

**Proof.** With no gates, the counter is $n$ by definition. The empty constructed list is acyclic (`GatesAcyclic.nil`); the identity tap sends each index below $n$ to itself, so it remains below $n$ and is injective. The computation on the empty list leaves the input values unchanged, making value preservation immediate. No vertex is used by a constructed gate, so every fanout is zero and every tapped vertex is unused. The gate-shape condition holds vacuously, and the empty constructed list has size zero.

**Key facts.** `BoolCircuit.GatesAcyclic.nil`.
