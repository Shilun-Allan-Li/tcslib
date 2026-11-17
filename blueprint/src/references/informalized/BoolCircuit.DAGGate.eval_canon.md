<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformCanon.lean :: BoolCircuit.DAGGate.eval_canon -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation preserved by canonicalization

**Claim.** For every gate and Boolean value list, the canonical form of the gate has the same evaluation as the original gate.

**Proof.** Canonicalization preserves the gate kind (`DAGGate.canon_kind`) and removes repeated arguments. Removing repetitions does not change whether all argument lookups are true, nor whether any argument lookup is true: these properties depend on which arguments occur, not how many times they occur. Thus the all-test and any-test of the canonical argument list agree with those for the original list. Evaluation is one of these tests, or the negation of the all-test for a NOT gate, so it is unchanged in each gate-kind case.

**Key facts.** `BoolCircuit.DAGGate.canon_kind`.
