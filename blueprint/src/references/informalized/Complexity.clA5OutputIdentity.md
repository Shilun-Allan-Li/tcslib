<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5OutputIdentity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Tableau Serialization

**Claim.** The function sending each input word to the serialization of its Cook–Levin tableau formula at the specified producer horizon is polynomial-time computable.

**Proof.** The proof applies the general theorem that a polynomial-time emitter, when supplied with packed records and emitting the prescribed tableau chunk at each cursor value through the last round (and the empty word afterward), yields a polynomial-time serialization of the full tableau (`clA5Output_of_nativeChunk`). Its hypotheses are supplied by the polynomial-time emitter `clA5Emit_native` and the exact chunk behavior `clA5Emit_exact`: on each packed word, the emitter outputs the corresponding clause-group chunk when the cursor is within the last round and outputs nothing past it. Thus the general chunk-to-serialization result applies and gives the claimed polynomial-time computation.

**Key facts.** `Complexity.clA5Emit_native`, `Complexity.clA5Emit_exact`, `Complexity.clA5Output_of_nativeChunk`.
