<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowers_cauchy_schwarz_last -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Last-coordinate Gowers Cauchy–Schwarz inequality

**Claim.** For a family indexed by the $(k+1)$-cube, its Gowers inner product is at most the product of the square roots of the inner products of the two families obtained by fixing the last coordinate to $0$ and to $1$.

**Proof.** Apply the coordinatewise Gowers Cauchy–Schwarz inequality to the last coordinate of the $(k+1)$-cube. Fixing that coordinate to either value is precisely the corresponding last-coordinate duplication, so its conclusion is the asserted bound.

**Key facts.** `FABL.gowers_cauchy_schwarz_at`.
