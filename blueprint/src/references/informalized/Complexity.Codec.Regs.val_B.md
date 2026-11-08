<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.val_B -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of register B

**Claim.** For any register record $R$, the value of its indexed register at index $3$ is the value of register $B$ in $R$.

**Proof.** The index $rB$ is $3$. By the definition of the indexed value, the case at index $3$ returns $R.B$, so the two sides are definitionally equal.
