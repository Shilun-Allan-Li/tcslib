<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/CompleteQuadraticDecomposition.lean :: FABL.pairedAffineLinearForm_succ_appendTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Paired affine form under appending two coordinates

**Claim.** Evaluating the paired affine linear form with parameter $k+1$ on the vector obtained by appending $a,b$ to $x$ equals its value with parameter $k$ on $x$, plus the sum of the coordinates of $x$.

**Proof.** By the recursive definition at parameter $k+1$, the form is the sum of the parameter-$k$ form and the coordinate-sum form, both evaluated on the prefix obtained by removing the last two coordinates. Appending $a,b$ makes that prefix exactly $x$. The two terms are therefore the paired affine form at parameter $k$ evaluated on $x$ and the sum of the coordinates of $x$, respectively; adding them gives the asserted identity.
