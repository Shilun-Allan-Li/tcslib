<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.BooleanCircuit.evalGate_eq_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of an input gate

**Claim.** If gate $i$ reads input position $j$, then its value on input $x$ is $x(j)$.

**Proof.** Unfold gate evaluation at $i$. Since the gate is the input gate reading position $j$, the input case of the definition returns $x(j)$.
