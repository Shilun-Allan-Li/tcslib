<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Valid.lean :: Complexity.Codec.foldl_vStepO_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Missing cell clears validity

**Claim.** If at least one of the first $m$ optional cells is absent, then folding the option-valued update over those cells leaves the first validity flag false.

**Proof.** Induct on $m$. When $m=0$, the hypothesis that an absent entry occurs below $m$ is impossible. For $m+1$, consider the last entry. If it is absent, its update sets the first validity flag to false directly. If it is present, the assumed absent entry must occur among the first $m$ entries, since it cannot be the last entry. By induction the flag after those first $m$ updates is false. The update preserves a false validity flag (`vStepO_ok_false`), so it remains false after processing the last entry.

**Key facts.** `Complexity.Codec.vStepO_ok_false`.
