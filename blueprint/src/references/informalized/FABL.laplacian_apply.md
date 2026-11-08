<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/LaplacianAndPoincare.lean :: FABL.laplacian_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Laplacian evaluation

**Claim.** For every real-valued function on the Boolean cube and every point, the Laplacian equals the sum of the coordinate Laplacians at that point.

**Proof.** By definition, the Laplacian is the sum of the coordinate Laplacian operators. Evaluating this finite sum of linear maps at a function and then at a point gives the sum of their individual evaluations, which is the asserted identity.
