<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLpInequalities.lean :: FABL.FiniteFourierBasis.abs_anisotropicProductNoiseOperator_rpow_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Anisotropic Noise Operator Moment Bound

**Claim.** For coordinate parameters in $[0,1]$ and $p\geq 1$, the $p$th power of the absolute value of the anisotropic noise operator applied to $f$ is pointwise bounded by the anisotropic noise operator applied to $|f|^p$.

**Proof.** At the chosen input, rewrite each occurrence of the anisotropic noise operator as expectation under its associated noise kernel, using `anisotropicProductNoiseOperator_apply_eq_pmfExpectation`. The desired inequality then becomes the absolute-moment inequality for a probability expectation: for $p\geq1$, the $p$th power of the absolute value of an expectation is at most the expectation of the $p$th power of the absolute value (`abs_pmfExpectation_rpow_le`). Applying that inequality to the noise-kernel distribution proves the result.

**Key facts.** `FABL.FiniteFourierBasis.anisotropicProductNoiseOperator_apply_eq_pmfExpectation`, `FABL.abs_pmfExpectation_rpow_le`.
