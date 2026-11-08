<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictSize.lean :: Language.InSIZE.inStrictSIZE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conversion to strict circuit size

**Claim.** A language recognized by fan-in-two circuits of size at most $T(n)$ has a strict circuit family of size at most $4T(n)+12$, with the length-zero circuit still having fan-in at most two.

**Proof.** Choose a fan-in-two family witnessing membership in the size class. Replace it by its strictified family. At length zero, the original fan-in-two property supplies the required condition. At every positive length, the strictification theorem gives strictness (`BoolCircuit.DAGCircuit.strictify_isStrict`), and its size is at most four times the original size plus twelve (`BoolCircuit.DAGCircuit.strictify_size_le`). Since the original size is at most $T(n)$, this is at most $4T(n)+12$. Finally, strictification preserves each circuit's evaluation (`BoolCircuit.DAGCircuitFamily.strictify_eval`); thus the new family recognizes exactly the same language as the original one.

**Key facts.** `BoolCircuit.DAGCircuit.strictify_isStrict`, `BoolCircuit.DAGCircuit.strictify_size_le`, `BoolCircuit.DAGCircuitFamily.strictify_eval`.
