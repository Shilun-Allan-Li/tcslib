<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGFanin.lean :: BoolCircuit.DAGGate.eval_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of concatenated gate inputs

**Claim.** For an AND or OR gate, evaluation on the concatenation of two input lists equals the gate operation applied to the evaluations on the two lists separately.

**Proof.** There are two possible gate kinds under the hypothesis: AND and OR. For AND, the conjunction over a concatenated list is the conjunction of the conjunctions over its two parts, which is exactly the AND operation on their evaluations. For OR, the disjunction over a concatenated list similarly splits into the disjunctions over the two parts. The excluded NOT case is the only remaining gate kind.
