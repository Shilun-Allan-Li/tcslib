<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.tendsto_fknOptimalityDelta -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing Gaussian Tail Mass

**Claim.** The quantity twice the selected Boolean-cube tail mass tends to zero as $q\to\infty$.

**Proof.** For each $q$, the quantity is positive (`fknOptimalityDelta_pos`) and is bounded above by three times the corresponding Gaussian mass (`fknOptimalityDelta_lt_three_mul_gaussianMass`). That Gaussian mass tends to zero (`tendsto_fknOptimalityGaussianMass_zero`), so the upper bound tends to zero. Squeezing between zero and this vanishing upper bound proves the result.

**Key facts.** `FABL.fknOptimalityDelta_pos`, `FABL.fknOptimalityDelta_lt_three_mul_gaussianMass`, `FABL.tendsto_fknOptimalityGaussianMass_zero`.
