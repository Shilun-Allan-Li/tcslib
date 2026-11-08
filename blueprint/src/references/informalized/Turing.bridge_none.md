<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridge_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halt Marker in the Statement Support

**Claim.** For every program, the absent label, which marks halt, belongs to its finite statement support.

**Proof.** Unfold the definition of the statement support. It is formed by collecting the compiled statements over the label support with the absent label adjoined. The absent label is included by construction, and its translated statement collection contains the absent statement, so the halt marker belongs to the resulting support.
