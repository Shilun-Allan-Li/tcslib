<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/CompleteQuadraticDecomposition.lean :: FABL.completeQuadraticBit_appendTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic bit after appending two coordinates

**Claim.** Appending coordinates $a,b\in\mathbb{F}_2$ to $x\in\mathbb{F}_2^m$ gives complete quadratic bit $Q(x)+ab+(\sum_i x_i)(a+b)$.

**Proof.** Apply the append formula to $x$ and the two-coordinate vector $(a,b)$. The complete quadratic bit of $(a,b)$ is $ab$, and the sum of its coordinates is $a+b$. Substituting these into the append formula yields the stated identity.

**Key facts.** `FABL.completeQuadraticBit_append`, `FABL.completeQuadraticBit_two`.
