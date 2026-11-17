<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Estimator.lean :: FABL.restrictedFourierWeightEstimatorCost_work_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Estimator Work Bound

**Claim.** The work component of the restricted Fourier weight estimator cost is at most $8(m+1)(n+1)$.

**Proof.** First, $S$ is a finite subset of $J$, and $J$ is a finite subset of the $n$ coordinates, so $|S|\le |J|\le n$. Hence $|S|\le n$. Use the estimator work formula (FABL.restrictedFourierWeightEstimatorCost_work) to write the work as $3mn+m(2+(2n+2|S|+1))+(m+1)$. Substituting the bound $|S|\le n$ and simplifying the resulting polynomial inequality gives the claimed upper bound $8(m+1)(n+1)$.

**Key facts.** `FABL.restrictedFourierWeightEstimatorCost_work`.
