<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.val_E2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of register E2

**Claim.** For any register record $R$, the value of its indexed register at index $9$ is the value of register $E2$ in $R$.

**Proof.** The index $rE2$ is $9$. By the definition of the indexed value, the case at index $9$ returns $R.E2$, so the two sides are definitionally equal.
