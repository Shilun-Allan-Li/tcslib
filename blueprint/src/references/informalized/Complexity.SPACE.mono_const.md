<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Basic.lean :: Complexity.SPACE.mono_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity under constant scaling

**Claim.** If $s_1(n)\le a s_2(n)$ for every $n$, then every language decidable in space $s_1$ up to a constant factor is also decidable in space $s_2$ up to a constant factor.

**Proof.** Take a language in $\mathrm{SPACE}(s_1)$, witnessed by a constant $c$ and a machine $M$ deciding it within the bound $c s_1(n)$. By the pointwise hypothesis and monotonicity of multiplication by $c$, this bound is at most $c(a s_2(n))=(ca)s_2(n)$. Thus the same machine witnesses membership in $\mathrm{SPACE}(s_2)$, with constant factor $ca$.

**Key facts.** `Turing.FinTM.ComputesInSpace.mono`.
