<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.val_T -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the T register

**Claim.** For every register record $R$, the value of its coordinate at index $13$ is the value stored in its $T$ register.

**Proof.** The index $r_T$ is $13$, and the coordinate function assigns the $T$ register to index $13$. Evaluating the definition at this index gives the claimed equality.
