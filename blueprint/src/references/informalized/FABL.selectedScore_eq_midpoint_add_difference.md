<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoise.lean :: FABL.selectedScore_eq_midpoint_add_difference -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Point Selection Identity

**Claim.** For $x\in\{-1,1\}$, the value selected from $a(\text{plus})$ and $a(\text{minus})$ is their midpoint plus half their difference multiplied by $x$.

**Proof.** There are two possibilities for the sign $x$. If $x=1$, the selected value is $a(\text{plus})$, and the right-hand side simplifies to that same value. If $x=-1$, the selected value is $a(\text{minus})$, and the right-hand side simplifies to $a(\text{minus})$. These are all possible signs, so the identity holds.
