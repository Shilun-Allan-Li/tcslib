<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyGadget.lean :: BoolCircuit.DAGGate.eval_dedupArgs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation after removing repeated inputs

**Claim.** Removing repeated input indices from any Boolean gate’s input list leaves its evaluation unchanged.

**Proof.** Deduplication preserves the set of arguments occurring in the list. Therefore the conjunction of their defaulted Boolean lookups is unchanged, and so is their disjunction. For an AND gate evaluation is the first of these, for an OR gate it is the second, and for a NOT gate it is the negation of the first. Hence evaluation agrees for every gate kind.
