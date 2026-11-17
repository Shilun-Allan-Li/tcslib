<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixExponentSolver.lean :: FABL.solveLowDegreeF₂SamplesWithBackend_cubic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cubic backend agreement

**Claim.** For any natural numbers $n,\ell,m$ and any $m$ samples in $\{0,1\}^n\times\mathbb F_2$, the low-degree coefficient hypothesis returned using the cubic solver backend equals the one returned by the standard solver.

**Proof.** The cubic backend’s `solve` field is definitionally the standard solver `solveF₂Rows`. Unfolding the two constructions therefore gives the same coefficient family, so the hypotheses are equal by reflexivity.
