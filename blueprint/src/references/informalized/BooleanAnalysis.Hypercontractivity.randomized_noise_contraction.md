<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/General.lean :: BooleanAnalysis.Hypercontractivity.randomized_noise_contraction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomized noise contraction

**Claim.** For every $q>1$, one can choose $0<c\le1$, with $c=2/5$ when $q=4$ or $q=4/3$, so that randomizing the product noise operator with parameter $c$ does not increase the product $q$-moment norm.

**Proof.** Choose $c$ from the signed anisotropic noise contraction theorem. It supplies the stated positivity, upper bound, special values, and, for every product space, sign vector, and function, contraction of the $q$-norm under anisotropic noise with coordinate parameters $c$ times the corresponding signs (`signed_anisotropicNoise_contraction`). For each fixed Boolean sign vector, randomizing the product noise with parameter $c$ agrees with applying this signed anisotropic noise to the original function (`randomization_noise_eq_anisotropicNoise`). Consequently every fixed-sign slice has norm at most the norm of the original function. Averaging these slice bounds gives the same bound for the randomized norm (`randomizationNorm_le_of_norm_le`).

**Key facts.** `BooleanAnalysis.Hypercontractivity.signed_anisotropicNoise_contraction`, `BooleanAnalysis.Hypercontractivity.randomization_noise_eq_anisotropicNoise`, `BooleanAnalysis.Hypercontractivity.randomizationNorm_le_of_norm_le`.
