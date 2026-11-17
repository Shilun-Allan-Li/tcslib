<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.tendsto_millsF_atBot -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian density expression decays

**Claim.** For $F(x)=\varphi(x)(x^{-3}-x^{-1})$, with reciprocals taken in the real numbers, $F(x)\to0$ as $x\to-\infty$.

**Proof.** Since $x^3\to-\infty$ as $x\to-\infty$ (`tendsto_cube_atBot`), its reciprocal tends to zero. The reciprocal of $x$ also tends to zero as $x\to-\infty$. Hence their difference tends to zero. The standard Gaussian density tends to zero at negative infinity (`tendsto_standardGaussianPDF_atBot`), so the product of that density and the difference tends to zero; this product is exactly $F(x)$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.tendsto_cube_atBot`, `BooleanAnalysis.ThresholdFunctions.tendsto_standardGaussianPDF_atBot`.
