<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.BooleanCircuit.evalGate_eq_or -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a disjunction gate

**Claim.** If gate $i$ is the disjunction of earlier gates $a$ and $b$, then on every input its value is the disjunction of the values at those two earlier gates.

**Proof.** Unfold gate evaluation at $i$ and use the hypothesis identifying its gate as the disjunction of $a$ and $b$. By the defining disjunction case, the result is the disjunction of the evaluations at their corresponding earlier positions, namely their previous-gate indices.
