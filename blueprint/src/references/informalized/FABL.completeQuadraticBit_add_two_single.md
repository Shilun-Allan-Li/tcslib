<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.completeQuadraticBit_add_two_single -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-coordinate addition law

**Claim.** For distinct coordinates $i,j$, adding $1$ at both coordinates changes the complete quadratic bit by $\sum_{k\ne i}x_k+\sum_{k\ne j}x_k+1$.

**Proof.** First add $1$ at coordinate $i$, using the single-coordinate addition law. Then add $1$ at coordinate $j$ to the resulting vector. Since $i\ne j$, adding at $i$ increases the derivative sum associated with coordinate $j$ by $1$. The two changes therefore contribute the original derivative sums at $i$ and $j$, together with the extra $1$, as asserted.

**Key facts.** `FABL.completeQuadraticBit_add_single`, `FABL.completeQuadraticDerivativeBit_add_single_of_ne`.
