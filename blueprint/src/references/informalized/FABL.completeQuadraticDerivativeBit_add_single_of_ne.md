<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.completeQuadraticDerivativeBit_add_single_of_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative under a coordinate change

**Claim.** If $i$ and $j$ are distinct coordinates, adding $c$ to coordinate $i$ changes the derivative bit at coordinate $j$ by adding $c$.

**Proof.** The derivative at $j$ sums the input coordinates other than $j$. After replacing $x$ by $x+ c e_i$, distribute this sum over the coordinatewise addition. The original terms give the derivative of $x$. In the added terms, every coordinate contributes zero except coordinate $i$, which is included because $i\ne j$; that term contributes $c$. Thus the new derivative is the old derivative plus $c$.
