<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictCircuit.lean :: BoolCircuit.DAGGate.Strict.faninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict gates have fan-in at most two

**Claim.** A strict gate has pairwise distinct argument indices, a NOT gate has exactly one argument, and the gate has at most two arguments.

**Proof.** The distinctness assertion is already part of strictness. If the gate is a NOT gate, its prescribed argument length is one, giving the required well-formedness condition. Its length is also at most two. If it is not a NOT gate, strictness prescribes length two, which is again at most two; the NOT-specific condition holds vacuously. Thus the gate is well formed and has fan-in at most two.
