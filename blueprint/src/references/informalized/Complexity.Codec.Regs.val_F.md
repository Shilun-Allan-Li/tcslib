<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.val_F -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of register F

**Claim.** For any register record $R$, the value of its indexed register at index $8$ is the value of register $F$ in $R$.

**Proof.** The index $rF$ is $8$. By the definition of the indexed value, the case at index $8$ returns $R.F$, so the two sides are definitionally equal.
