<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.b2f_and -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean conjunction as multiplication

**Claim.** For Booleans $a$ and $b$, the encoding of their conjunction in $\mathrm{Fin}(2)$ is the product of their encodings.

**Proof.** Check the four possible pairs of Boolean values. When either value is false, both the encoded conjunction and the product are zero; when both are true, both are one.
