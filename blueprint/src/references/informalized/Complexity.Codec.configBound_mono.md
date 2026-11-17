<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Bridge.lean :: Complexity.Codec.configBound_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Configuration Bound

**Claim.** For fixed $N$ and input length $n$, the configuration bound at space parameter $s$ is at most the bound at any larger parameter $s'$.

**Proof.** Expand the configuration bound. Its factors independent of the space parameter are nonnegative, so it suffices to compare the factors that depend on $s$. From $s\le s'$, we have $2s+1\le 2s'+1$ and $N.k(2s+1)\le N.k(2s'+1)$. Since the bases are at least one, monotonicity of natural-number powers gives $3^{N.k(2s+1)}\le 3^{N.k(2s'+1)}$ and $(2s+1)^{N.k}\le(2s'+1)^{N.k}$. Multiplying these inequalities by the nonnegative remaining factors yields the desired bound.
