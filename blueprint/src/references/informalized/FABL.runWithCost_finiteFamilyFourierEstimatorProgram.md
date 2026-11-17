<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FiniteFamily.lean :: FABL.runWithCost_finiteFamilyFourierEstimatorProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-Family Estimator Law

**Claim.** The finite-family Fourier estimator has the law obtained by drawing a uniform batch of the prescribed size for each member of the family and applying the labeled-sample output function, with the program’s specified cost.

**Proof.** The estimator program is defined directly as a random-example matrix output program, with one batch of the prescribed size for each family member and the finite-family Fourier estimator as its output function. By the definition of the run law for this constructor, its outcome law is exactly the matrix input law mapped through the function that labels each sampled input by the target, computes the estimator output, and records the corresponding cost. Substituting the prescribed sample size and work charge gives the stated law.
