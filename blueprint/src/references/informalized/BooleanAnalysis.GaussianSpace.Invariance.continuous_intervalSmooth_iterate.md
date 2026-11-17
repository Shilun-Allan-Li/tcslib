<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Smoothing.lean :: BooleanAnalysis.GaussianSpace.Invariance.continuous_intervalSmooth_iterate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of iterated interval smoothing

**Claim.** Repeatedly applying interval smoothing to a continuous function gives a continuous function for every finite number of iterations.

**Proof.** Induct on the number of iterations. At zero iterations, the function is the original continuous function. For the successor step, the induction hypothesis says the current iterate is continuous, hence is zero-times continuously differentiable. The regularity gain for interval smoothing applied with $m=0$ shows that the next iterate is continuously differentiable, and therefore continuous.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.contDiff_intervalSmooth`.
