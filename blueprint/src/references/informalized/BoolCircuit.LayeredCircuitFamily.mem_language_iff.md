<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredPPoly.lean :: BoolCircuit.LayeredCircuitFamily.mem_language_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit-Family Language Membership

**Claim.** A Boolean word belongs to the language accepted by a family of layered circuits exactly when the circuit assigned to its length outputs \(1\) on the word encoded as an assignment in \(\mathrm{Fin}\,2\).

**Proof.** Membership in the language is defined to mean that the family accepts the word, and acceptance is defined by the stated output-equals-one condition. The two sides are therefore identical predicates, giving the equivalence directly.
