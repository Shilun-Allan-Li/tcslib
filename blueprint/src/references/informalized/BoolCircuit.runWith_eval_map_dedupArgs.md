<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyGadget.lean :: BoolCircuit.runWith_eval_map_dedupArgs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duplicate arguments do not affect evaluation

**Claim.** Removing repeated arguments from every gate in a Boolean circuit leaves its final execution list unchanged.

**Proof.** Induct on the gate list, allowing the initial value list to vary. The empty list gives the same unchanged result on both sides. For a first gate, the execution rule (`runWith_cons`) reduces each execution to the execution of the tail from the list extended by that first gate’s output. The induction hypothesis equates the tail executions from their respective extended lists. The first gate outputs also agree, because removing repeated arguments does not change its value (`DAGGate.eval_dedupArgs`). Hence the extended lists agree, and so do the final results.

**Key facts.** `BoolCircuit.runWith_cons`, `BoolCircuit.DAGGate.eval_dedupArgs`.
