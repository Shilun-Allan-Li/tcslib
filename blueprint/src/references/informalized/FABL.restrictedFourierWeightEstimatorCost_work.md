<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Estimator.lean :: FABL.restrictedFourierWeightEstimatorCost_work -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Estimator Work Formula

**Claim.** The work component of the restricted Fourier weight estimator cost is $3mn+m(2+(2n+2|S|+1))+(m+1)$.

**Proof.** By definition, the estimator cost stores this expression as its work component, with the observation work expanded as $2n+2|S|+1$. Projecting to the work component therefore gives the stated equality by unfolding the definitions.
