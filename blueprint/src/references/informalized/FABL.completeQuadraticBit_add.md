<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.completeQuadraticBit_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Addition law for the quadratic bit

**Claim.** For $x,z\in\mathbb{F}_2^n$, the complete quadratic bit of $x+z$ is the sum of their complete quadratic bits and the mixed term $\sum_{i<j}(x_i z_j+z_i x_j)$.

**Proof.** Expand each summand $(x_i+z_i)(x_j+z_j)$ in the defining sum over $i<j$. Distributivity gives $x_i x_j+z_i z_j+x_i z_j+z_i x_j$. Summing these four contributions over the same pairs separates them into the complete quadratic bit of $x$, that of $z$, and the stated mixed term.
