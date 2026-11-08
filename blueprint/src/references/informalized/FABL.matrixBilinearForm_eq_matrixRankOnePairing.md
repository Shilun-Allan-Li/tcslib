<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.matrixBilinearForm_eq_matrixRankOnePairing -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matrix Bilinear Form Expansion

**Claim.** For an $n\times n$ matrix $D$ over $\mathbb F_2$ and vectors $x,y\in\mathbb F_2^n$, the bilinear form $x\cdot(Dy)$ equals $\sum_i\sum_j D_{ij}x_i y_j$.

**Proof.** Expand the dot product as the sum over row indices $i$ of $x_i(Dy)_i$. By the definition of matrix-vector multiplication, $(Dy)_i=\sum_j D_{ij}y_j$. Distributing multiplication by $x_i$ through this finite sum yields $\sum_i\sum_j x_iD_{ij}y_j$. Associativity and commutativity of multiplication identify each summand with $D_{ij}(x_i y_j)$, which is the asserted matrix rank-one pairing.
