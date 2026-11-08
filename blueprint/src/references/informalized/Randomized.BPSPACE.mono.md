<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Randomized.BPSPACE.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Randomized Space

**Claim.** If $s_1(n)\le s_2(n)$ for every input length, then every language decidable with bounded error using space bounded by a constant multiple of $s_1$ is also decidable with bounded error using space bounded by a constant multiple of $s_2$.

**Proof.** Take a language witnessed in the smaller-space class by a constant $c$ and a machine. The assumed pointwise inequality gives $c s_1(n)\le c s_2(n)$ for every $n$, since multiplication by a natural number preserves order. The machine's space bound and its halting and correctness guarantees are therefore also valid for the larger bound, by monotonicity of bounded-error space decidability (`Turing.FinNDTM.BPDecidesInSpace.mono`). The same constant and machine witness membership in the larger class.

**Key facts.** `Turing.FinNDTM.BPDecidesInSpace.mono`.
