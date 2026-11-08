<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FanOut.lean :: BoolCircuit.foInv_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty Circuit Invariants

**Claim.** The empty original gate list, empty reduced list, identity vertex map, and count $n$ satisfy all fanout reduction invariants.

**Proof.** The count equation and length bound reduce to $n=n$ and $0\le 0$. The empty reduced list is acyclic (BoolCircuit.GatesAcyclic.nil). The identity map sends each vertex below $n$ below $n$ and is injective. Both computations agree because the original and reduced lists are empty and the map is the identity. Every fanout is zero in the empty list, so fanouts are at most $2$ and mapped vertices have fanout zero. Finally, the gate conditions hold vacuously because there are no gates.

**Key facts.** `BoolCircuit.GatesAcyclic.nil`.
