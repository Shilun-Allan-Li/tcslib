<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Codes2Tape.lean :: Turing.zfBFallback_serialize_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fallback Serialization Length

**Claim.** The serialization of the fixed fallback machine has length $354$.

**Proof.** Unfold the serialization into its explicit finite code and expand the fixed fallback machine. The resulting list length is computed by reducing the concatenated code pieces and their lengths; this arithmetic evaluates to $354$.
