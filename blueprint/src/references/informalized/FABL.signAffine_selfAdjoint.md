<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.signAffine_selfAdjoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Self-Adjointness of the Sign Affine Operator

**Claim.** For every real $\rho$ and functions $f,g:\{-1,1\}\to\mathbb R$, the uniform inner product of the affine transform of $f$ with $g$ equals the uniform inner product of $f$ with the affine transform of $g$.

**Proof.** On the two-point sign space, the uniform inner product is the average of the two pointwise products. Expand the affine transforms using their even and odd coefficients, which are respectively the average and half-difference of the two values of each function. At the two signs, the terms involving the constant coefficients and the terms involving the product of the signs match after exchanging $f$ and $g$. Thus the two averages are equal; the remaining equality is elementary algebra.
