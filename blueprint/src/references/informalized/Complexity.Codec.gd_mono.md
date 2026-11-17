<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean :: Complexity.Codec.gd_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the guarded bound

**Claim.** If a configuration satisfies the codec precondition and all its registers are bounded by $(8W(N)+8)(|y|+1)$, then it satisfies the same precondition and the bound with the exponent written as $1$.

**Proof.** The guard consists of the codec precondition together with the register bounds. Unfolding the definition of the bound, its numerical expression is already $(8W(N)+8)(|y|+1)$, which is exactly $(8W(N)+8)(|y|+1)^1$. Thus the assumed guard gives both required conclusions directly.
