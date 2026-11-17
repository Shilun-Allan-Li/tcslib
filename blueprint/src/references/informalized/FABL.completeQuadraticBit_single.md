<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.completeQuadraticBit_single -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic bit on a single-coordinate vector

**Claim.** The complete quadratic bit of a vector supported at just one coordinate is zero.

**Proof.** Expand the complete quadratic bit as a sum over pairs $j<k$. For each such pair, its product can be nonzero only if both coordinates are the distinguished coordinate $i$, because the vector vanishes elsewhere. But $j<k$ implies $j\ne k$, so they cannot both equal $i$. Every summand is therefore zero, and the whole sum vanishes.
