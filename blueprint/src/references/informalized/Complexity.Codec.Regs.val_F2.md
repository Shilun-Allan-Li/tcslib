<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.val_F2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of register F2

**Claim.** For any register record $R$, the value of its indexed register at index $10$ is the value of register $F2$ in $R$.

**Proof.** The index $rF2$ is $10$. By the definition of the indexed value, the case at index $10$ returns $R.F2$, so the two sides are definitionally equal.
