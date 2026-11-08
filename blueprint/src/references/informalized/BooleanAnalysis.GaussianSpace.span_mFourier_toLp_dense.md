<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Torus.lean :: BooleanAnalysis.GaussianSpace.span_mFourier_toLp_dense -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Density of Torus Fourier Characters

**Claim.** For a finite measure on a finite-dimensional torus and finite $p\ge1$, the complex linear span of all torus Fourier characters is dense in $L^p$.

**Proof.** Continuous complex-valued functions are dense in $L^p$ for a finite measure on the compact torus (ContinuousMap.toLp_denseRange). The torus Fourier characters have linear span dense among continuous functions in the uniform topology, by the Fourier-character density theorem for the torus (UnitAddTorus.span_mFourier_closure_eq_top). Combining these density statements, the image in $L^p$ of the span of the characters is dense: uniform approximation controls the $L^p$ distance because the measure is finite. Therefore the closure of their complex linear span is all of $L^p$.
