<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FourierEstimation.lean :: FABL.runWithCost_fourierCoeffEstimatorProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficient Estimator Law

**Claim.** For any target, coordinate subset, and sample size, the estimator’s law is obtained from a uniform batch of inputs by returning the empirical Fourier coefficient of their target labels and recording cost $(m,0,m+m(|S|+1))$.

**Proof.** The program first draws a uniform batch of $m$ cube inputs, labels each input with the target value, and then returns the empirical Fourier coefficient of those labeled samples. Its batch constructor charges $(m,0,m)$, while the subsequent computation tick charges $(0,0,m(|S|+1))$. Thus each input batch maps to the stated coefficient and the sum of these costs, giving the claimed law.
