<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Yap.lean :: Complexity.Yap.eval_eq_of_encode_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation Determined by Circuit Encoding

**Claim.** If two directed acyclic Boolean circuits have equal encodings and their input assignments have equal associated bit lists, then the circuits evaluate to the same Boolean value on those assignments.

**Proof.** Equal circuit encodings determine equal input counts, gate lists, and output indices by the circuit-encoding uniqueness fact (`eq_of_encode_eq`). Their evaluations are obtained by running the same gate list from the input bit list and reading the same output index. The assumed equality of the input lists therefore makes these evaluations identical.

**Key facts.** `BoolCircuit.DAGCircuit.eq_of_encode_eq`.
