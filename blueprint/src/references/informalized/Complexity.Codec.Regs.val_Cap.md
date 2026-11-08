<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.val_Cap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of register Cap

**Claim.** For any register record $R$, the value of its indexed register at index $19$ is the value of register $\mathrm{Cap}$ in $R$.

**Proof.** The index $rCap$ is $19$. By the definition of the indexed value, the case at index $19$ returns $R.\mathrm{Cap}$, so the two sides are definitionally equal.
