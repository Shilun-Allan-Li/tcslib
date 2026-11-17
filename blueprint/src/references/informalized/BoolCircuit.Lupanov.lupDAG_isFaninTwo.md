<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Lupanov.lean :: BoolCircuit.Lupanov.lupDAG_isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-in bound for the constructed circuit

**Claim.** For every Boolean function $f$ on $n$ bits and every $k\le n$, the constructed circuit is well formed and each gate reads at most two vertices.

**Proof.** The gate-list extension property in `lupGates_spec` splits the constructed list into the original Lupanov gates and the gates appended to form the OR tree. For an original gate, membership in the list of gates means it is `gateAt` for some index below the total gate count; the fact that each such gate is well formed and has at most two inputs (`gateAt_faninTwo`) gives the required property. For an appended gate, the specification supplies distinct arguments and at most two arguments. It also says the gate is an OR gate, so it cannot be a NOT gate; hence the NOT-specific condition in well-formedness holds vacuously. These two cases establish both well-formedness and the fan-in bound for every gate.

**Key facts.** `BoolCircuit.Lupanov.lupGates_spec`, `BoolCircuit.Lupanov.gateAt_faninTwo`.
