<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_evalModW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time modular evaluation

**Claim.** The function that initializes the encoded gate-evaluation state, iterates the gate-state update for its prescribed number of rounds, and returns the resulting value modulo the encoded modulus is polynomial-time computable.

**Proof.** By definition, the modular-evaluation function sends each input first through `gateRun` and then through `runVal`. The identity of this function with that composition follows by evaluating both sides on an arbitrary input. Since `gateRun` and `runVal` are each polynomial-time computable, closure of polynomial-time computability under composition (`PolyTimeComputable.comp`) proves the claim.

**Key facts.** `Randomized.PIT.polyTimeComputable_gateRun`, `Randomized.PIT.polyTimeComputable_runVal`, `Complexity.PolyTimeComputable.comp`.
