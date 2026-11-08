<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.pmfExpectation_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation of a Finite Sum

**Claim.** The expectation of a finite pointwise sum of functions is the sum of their expectations.

**Proof.** Expand the expectation as a sum over points of the probability weights times the pointwise sum over indices. Distribute each weight across that finite sum, then interchange the two finite summations. The inner sum over points is the expectation of the corresponding function, yielding the stated sum of expectations.
