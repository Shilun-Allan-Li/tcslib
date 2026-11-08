<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.BooleanCircuit.evalGate_eq_and -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a conjunction gate

**Claim.** If gate $i$ is the conjunction of earlier gates $j$ and $k$, then its value on input $x$ is the conjunction of the values of those two gates on $x$.

**Proof.** Unfold the definition of gate evaluation at $i$. The hypothesis identifies the gate there as the conjunction of $j$ and $k$, so the defining evaluation is the conjunction of the evaluations at their corresponding earlier positions. These positions are precisely the previous-gate indices for $j$ and $k$.
