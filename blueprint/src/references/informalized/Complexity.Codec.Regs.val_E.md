<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.val_E -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of register E

**Claim.** For any register record $R$, the value of its indexed register at index $7$ is the value of register $E$ in $R$.

**Proof.** The index $rE$ is $7$. By the definition of the indexed value, the case at index $7$ returns $R.E$, so the two sides are definitionally equal.
