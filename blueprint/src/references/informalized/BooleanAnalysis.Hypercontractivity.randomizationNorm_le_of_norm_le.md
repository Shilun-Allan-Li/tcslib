<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/General.lean :: BooleanAnalysis.Hypercontractivity.randomizationNorm_le_of_norm_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Averaging randomized norm bounds

**Claim.** If every randomized expansion has its \(q\)-moment norm bounded by the norm of \(g\), then the norm obtained by averaging the \(q\)-th powers over both the product space and the uniform Boolean cube has the same bound.

**Proof.** First note that each product-space \(q\)-moment is nonnegative; the corresponding nonnegativity for uniform cube expectations is recorded by \(\texttt{expect\_rpow\_abs\_nonneg}\). Since \(q>0\), raising nonnegative numbers to the power \(1/q\) is order preserving, so each assumed norm bound implies the same bound for the underlying moments. Average those pointwise moment bounds over the Boolean cube. Monotonicity of expectation (\(\texttt{BooleanAnalysis.ThresholdFunctions.expect\_mono}\)) bounds the averaged moment by the constant moment of \(g\); expectation preserves constants (\(\texttt{BooleanAnalysis.ThresholdFunctions.expect\_const}\)). The two orders of finite averaging over the product outcomes and Boolean cube can be interchanged, using the identification of uniform expectation with finite-type expectation (\(\texttt{BooleanAnalysis.expect\_eq\_fintypeExpect}\)). Thus the joint averaged moment is at most the moment of \(g\). Taking the nonnegative \(1/q\)-th power gives the claimed norm inequality.

**Key facts.** `BooleanAnalysis.Hypercontractivity.expect_rpow_abs_nonneg`, `BooleanAnalysis.ThresholdFunctions.expect_mono`, `BooleanAnalysis.ThresholdFunctions.expect_const`, `BooleanAnalysis.expect_eq_fintypeExpect`.
