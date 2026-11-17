<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.val_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the P Register

**Claim.** For any register record $R$, the value of its slot indexed by $1$ is the value of its $P$ register.

**Proof.** Since the slot index $rP$ is $1$, the defining clause for the value function at index $1$ returns $R.P$. Thus the two sides are equal by the definition of the function.
