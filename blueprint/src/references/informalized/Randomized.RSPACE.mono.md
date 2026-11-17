<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Randomized.RSPACE.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Randomized Space

**Claim.** If $s_1(n)\le s_2(n)$ for every input length, then every language in $\mathrm{RSPACE}(s_1)$ is also in $\mathrm{RSPACE}(s_2)$.

**Proof.** Take a machine witnessing membership in $\mathrm{RSPACE}(s_1)$, with constant factor $c$. The assumed pointwise inequality implies $c s_1(n)\le c s_2(n)$ for every $n$, since multiplication by a natural number preserves order. The machine therefore satisfies the larger space bound with the same constant and retains all its halting and acceptance properties, so it witnesses membership in $\mathrm{RSPACE}(s_2)$ by monotonicity of the machine-level space definition (Turing.FinNDTM.RDecidesInSpace.mono).

**Key facts.** `Turing.FinNDTM.RDecidesInSpace.mono`.
