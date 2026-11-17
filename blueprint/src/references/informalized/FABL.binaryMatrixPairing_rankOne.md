<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.binaryMatrixPairing_rankOne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pairing with an Outer Product

**Claim.** Pairing $A$ with the outer product of $x$ and $y$ equals the double sum of $A_{ij}x_i y_j$.

**Proof.** By definition, the $(i,j)$ entry of the outer product is $x_i y_j$. Substituting this entry into the definition of the matrix pairing gives exactly $\sum_i\sum_j A_{ij}(x_i y_j)$, which is the stated matrix rank-one pairing.
