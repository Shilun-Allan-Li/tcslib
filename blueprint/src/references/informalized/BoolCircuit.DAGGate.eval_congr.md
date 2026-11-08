<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.DAGGate.eval_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation depends on referenced values

**Claim.** If two Boolean value lists have equal defaulted lookups at every argument of a gate, then the gate evaluates equally on the two lists.

**Proof.** For an AND gate, each argument’s lookup agrees, so the conjunction of those lookups agrees (`all_congr_mem`). For an OR gate, the corresponding disjunctions agree (`any_congr_mem`). A NOT gate negates the same conjunction of lookups, so its evaluations also agree.

**Key facts.** `BoolCircuit.all_congr_mem`, `BoolCircuit.any_congr_mem`.
