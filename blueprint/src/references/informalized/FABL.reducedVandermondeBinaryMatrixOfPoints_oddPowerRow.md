<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ReducedVandermonde.lean :: FABL.reducedVandermondeBinaryMatrixOfPoints_oddPowerRow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd-Power Rows of the Binary Vandermonde Matrix

**Claim.** For each row indexed by $q<k/2$ and basis coordinate $i<\ell$, its entry in column $j$ is the $i$th coordinate of $\alpha_j^{2q+1}$ in the chosen basis.

**Proof.** By definition, the row equivalence sends the row indexed by the inverse image of $(q,i)$ to the odd-power row labeled by $(q,i)$. In that case the matrix entry in column $j$ is defined to be the $i$th coordinate of the encoded element $\alpha_j^{2q+1}$.
