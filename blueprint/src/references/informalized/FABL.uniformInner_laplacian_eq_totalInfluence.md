<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/LaplacianAndPoincare.lean :: FABL.uniformInner_laplacian_eq_totalInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Laplacian inner product and total influence

**Claim.** The uniform inner product of a function with its Laplacian equals its total influence.

**Proof.** Write the uniform inner product as an expectation and expand the Laplacian pointwise as the sum of the coordinate Laplacians (\texttt{FABL.laplacian_apply}). Distribute multiplication by the function across this finite sum, then interchange the finite sum over coordinates with the uniform expectation. The result is the sum over coordinates of $\langle f,L_i f\rangle_u$. Each summand equals the influence in that coordinate (\texttt{FABL.uniformInner_coordinateLaplacian_eq_influence}); summing gives the total influence.

**Key facts.** `FABL.laplacian_apply`, `FABL.uniformInner_coordinateLaplacian_eq_influence`.
