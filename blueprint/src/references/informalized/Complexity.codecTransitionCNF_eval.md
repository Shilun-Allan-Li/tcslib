<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecTransitionCNF_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transition Formula Evaluation

**Claim.** For any Boolean assignment to the encoded bits, the transition CNF evaluates to true exactly when every position, transition case, and encoded bit gives a gate that evaluates to true on the assignment induced by its gate wires.

**Proof.** The transition CNF is the concatenation of the gate CNFs over the finite list of all gate indices. A concatenation evaluates to true exactly when each component CNF evaluates to true (\texttt{Complexity.codecCnf_eval_flatMap}). For each fixed index, the gate-CNF specification identifies that component’s evaluation with the corresponding gate evaluated on the assignment composed with its wire map (\texttt{Complexity.codecGateCNF_spec}). Finally, the list of indices enumerates all positions, transition cases, and encoded bits, so requiring every component to be true is exactly the stated universal condition.

**Key facts.** `Complexity.codecCnf_eval_flatMap`, `Complexity.codecGateCNF_spec`.
