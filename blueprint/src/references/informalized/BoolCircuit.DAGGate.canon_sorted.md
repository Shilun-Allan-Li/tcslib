<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformCanon.lean :: BoolCircuit.DAGGate.canon_sorted -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical arguments are sorted

**Claim.** For every Boolean gate, the argument indices of its canonical form are strictly increasing.

**Proof.** The canonical argument list is obtained by filtering the natural-number range used in its construction. That range is strictly increasing, and filtering a strictly increasing list preserves the order of every pair of retained elements. Hence the canonical arguments are strictly increasing.
