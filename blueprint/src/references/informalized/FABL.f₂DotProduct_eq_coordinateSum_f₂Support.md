<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.f₂DotProduct_eq_coordinateSum_f₂Support -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dot product as a sum over the support

**Claim.** For $\gamma,x\in\mathbb{F}_2^n$, their dot product equals the sum of the coordinates of $x$ at indices where $\gamma$ is nonzero.

**Proof.** Write the dot product as $\sum_i \gamma_i x_i$. At an index where $\gamma_i=0$, the summand is zero. At any other index, a nonzero element of $\mathbb{F}_2$ equals $1$, so the summand is $x_i$. Thus the sum reduces exactly to the indices in the support of $\gamma$, as claimed.
