<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.completeQuadraticPrefixBit_full -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Full Quadratic Prefix Value

**Claim.** For a Boolean sequence of length $n$, the quadratic value of its full prefix equals the quadratic value of the vector obtained by mapping every coordinate into $\mathbb F_2$.

**Proof.** By definition, the full-prefix value is the quadratic value of the truncation retaining coordinates $i<n$. For each $i\in\mathrm{Fin}(n)$, this condition holds, so the truncation's $i$th coordinate is the image of $w_i$ in $\mathbb F_2$. The Boolean-cube equivalence has exactly the same coordinate values (the coordinate formula is `pcppBoolCubeEquiv_apply`). Thus the two vectors agree at every coordinate, and applying the quadratic-value function to equal vectors proves the claim.

**Key facts.** `FABL.pcppBoolCubeEquiv_apply`.
