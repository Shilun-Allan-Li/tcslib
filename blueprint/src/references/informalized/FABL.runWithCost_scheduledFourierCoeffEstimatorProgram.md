<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FourierEstimation.lean :: FABL.runWithCost_scheduledFourierCoeffEstimatorProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scheduled Fourier Estimator Distribution and Cost

**Claim.** For the prescribed sample count, the scheduled Fourier estimator has the law obtained by drawing a uniform batch of cube inputs and returning the empirical Fourier coefficient of the target labels, with cost $(m,0,m+m(|S|+1))$, where $m$ is that sample count.

**Proof.** The scheduled program is the Fourier coefficient estimator with sample count $m$ chosen by the schedule. Apply the distribution-and-cost formula for the Fourier coefficient estimator ( `runWithCost_fourierCoeffEstimatorProgram`): its run draws a uniform function from the $m$ sample indices to the cube, labels each input by the target, and returns the empirical Fourier coefficient. Substituting the scheduled value of $m$ in that formula yields the asserted law and cost.

**Key facts.** `FABL.runWithCost_fourierCoeffEstimatorProgram`.
