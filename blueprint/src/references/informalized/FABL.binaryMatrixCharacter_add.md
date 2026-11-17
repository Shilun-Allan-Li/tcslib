<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.binaryMatrixCharacter_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity of the Matrix Character

**Claim.** For matrices $A,B,C$ over $\mathbb F_2$, the matrix character of $A$ at $B+C$ is the sum of its values at $B$ and $C$.

**Proof.** Expand the character as the double sum of entrywise products. Distributivity gives $A_{ij}(B_{ij}+C_{ij})=A_{ij}B_{ij}+A_{ij}C_{ij}$ at each pair of indices. Distributing both finite sums over addition then separates the result into the character at $B$ plus the character at $C$.
