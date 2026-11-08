<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.matrixRankOnePairing_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linearity of the matrix pairing

**Claim.** Let $n$ be a natural number, let $A,B$ be $n\times n$ matrices over $\mathbb{F}_2$, and let $x,y\in\mathbb{F}_2^n$. The pairing of $A-B$ against $x,y$ equals the pairing of $A$ against $x,y$ minus the pairing of $B$ against $x,y$.

**Proof.** In each summand, distributivity gives $(A_{ij}-B_{ij})(x_i y_j)=A_{ij}(x_i y_j)-B_{ij}(x_i y_j)$. Summing first over $j$ turns each inner sum into the difference of the corresponding inner sums for $A$ and $B$. Summing over $i$ then distributes over subtraction as well. The result is the pairing for $A$ minus the pairing for $B$, as claimed.
