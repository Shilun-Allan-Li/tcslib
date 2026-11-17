<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.val_Z -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the Z register

**Claim.** For every register record $R$, the value of its coordinate at index $20$ is the value stored in its $Z$ register.

**Proof.** The index $r_Z$ is $20$. This is the final index of the coordinate function's domain, and the function assigns the $Z$ register there. Evaluating the definition gives the equality.
