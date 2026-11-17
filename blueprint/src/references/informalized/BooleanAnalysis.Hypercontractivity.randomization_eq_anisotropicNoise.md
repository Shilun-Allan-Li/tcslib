<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/General.lean :: BooleanAnalysis.Hypercontractivity.randomization_eq_anisotropicNoise -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomization as anisotropic noise

**Claim.** For each Boolean string and outcome, the randomized expansion equals anisotropic product noise with the coordinate rates given by the signs associated to that string.

**Proof.** Both sides are the same finite sum indexed by coordinate subsets: the coefficient of the component indexed by \(S\) in randomization is the product of the coordinate signs over \(S\), which is exactly the coefficient defining anisotropic noise. Hence the expressions agree by unfolding their definitions.
