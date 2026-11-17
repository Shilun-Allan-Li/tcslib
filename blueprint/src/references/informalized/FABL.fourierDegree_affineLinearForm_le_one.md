<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdLevelOne.lean :: FABL.fourierDegree_affineLinearForm_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of an affine linear form

**Claim.** The affine linear form $x\mapsto a_0+\sum_i a_i x_i$ on the Boolean cube has Fourier degree at most $1$.

**Proof.** Rewrite the affine linear form using the sign values of the coordinates, so it is exactly the affine sign linear form with constant term $a_0$ and coefficients $a_i$. The degree bound for that function (`FABL.fourierDegree_affineSignLinearForm_le_one`) gives the result.

**Key facts.** `FABL.fourierDegree_affineSignLinearForm_le_one`.
