<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.BooleanCircuit.evalGate_eq_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a negation gate

**Claim.** If gate $i$ negates earlier gate $j$, then its value on input $x$ is the Boolean negation of the value at $j$.

**Proof.** Unfold gate evaluation at $i$ and use the hypothesis identifying its gate as a negation of $j$. The defining negation case returns the Boolean negation of the evaluation at the corresponding earlier position, which is the previous-gate index of $j$.
