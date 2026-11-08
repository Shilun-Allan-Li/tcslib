<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/SpectralDegree.lean :: FABL.sum_freeSignCube_boolean_eq_anfCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Free-Coordinate Sum and ANF Coefficient

**Claim.** For a binary-valued function $f$, summing its values over inputs that vanish outside $S$ and vary freely on $S$ gives the algebraic normal form coefficient indexed by $S$.

**Proof.** First index the free sign assignments by the subsets $T$ of $S$ corresponding to those assignments. The fact that a free sign assignment gives the binary input supported on the associated subset (`FABL.binaryPointOfFreeSign_eq_f₂CubeOfFinset`) identifies each summand with $f$ evaluated at the input supported on the lifted subset of coordinates. Next, reindex these lifted subsets by the subsets of $S$. This turns the sum into the sum of $f$ over all binary inputs supported on subsets of $S$. That is exactly the defining sum for the algebraic normal form coefficient at $S$.

**Key facts.** `FABL.binaryPointOfFreeSign_eq_f₂CubeOfFinset`.
