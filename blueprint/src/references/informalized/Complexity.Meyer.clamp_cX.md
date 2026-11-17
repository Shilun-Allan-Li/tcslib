<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSoundInput.lean :: Complexity.Meyer.clamp_cX -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clamped and signed input queries agree

**Claim.** Under the stated local-check hypotheses, for every time $t<2^W$ and every nonzero head movement $m\in\{-1,0,1\}$, the signed input query at offset $m$ equals the symbol query at index $1$ with sign flag indicating whether $m$ is negative.

**Proof.** The all-checks hypothesis gives the sign conversion law `sv_sgn`: the symbol query with sign flag indicating whether $m$ is negative, at index $1$, equals the signed query at offset `sgnZ` of that sign and index. Thus it remains to check that this signed offset is exactly the integer represented by $m$. Since a sign movement has only the three cases negative, zero, and positive, inspect these cases. The hypothesis that $m$ is nonzero excludes the zero case; in each remaining case the sign flag and magnitude give precisely the integer $m$. Substitution yields the desired equality.

**Key facts.** `Complexity.Meyer.sv_sgn`.
