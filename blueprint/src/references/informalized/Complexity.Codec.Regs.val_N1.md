<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.val_N1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of register N1

**Claim.** For any register record $R$, the value of its indexed register at index $5$ is the value of register $N1$ in $R$.

**Proof.** The index $rN1$ is $5$. By the definition of the indexed value, the case at index $5$ returns $R.N1$, so the two sides are definitionally equal.
