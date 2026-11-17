<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.val_L -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of register L

**Claim.** For any register record $R$, the value of its indexed register at index $0$ is the value of register $L$ in $R$.

**Proof.** The index $rL$ is $0$. By the definition of the indexed value, the case at index $0$ returns $R.L$, so the two sides are definitionally equal.
