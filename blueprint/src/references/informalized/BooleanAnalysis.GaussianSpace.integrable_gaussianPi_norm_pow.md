<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Fourier.lean :: BooleanAnalysis.GaussianSpace.integrable_gaussianPi_norm_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Gaussian norm moments

**Claim.** For every natural number $k$, the function $x\mapsto\|x\|^k$ on $\mathbb R^n$ is integrable under the product standard Gaussian measure.

**Proof.** It suffices to show that the Gaussian vector has finite $k$th moment of its norm. Each coordinate has finite $k$th moment under the one-dimensional standard Gaussian law (`memLp_id_gaussianReal`). Evaluation at any coordinate preserves this moment bound because the coordinate projection has the corresponding Gaussian marginal. Applying the finite-dimensional $L^p$ criterion for the norm, coordinatewise moment membership yields integrability of $\|x\|^k$.

**Caveat.** The source invokes the general norm-power integrability result `MemLp.integrable_norm_pow'` and the finite-dimensional coordinate criterion `MemLp.of_eval`, but neither appears in the supplied upstream list.
