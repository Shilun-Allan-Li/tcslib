<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.val_Q2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the Q2 Register

**Claim.** For any register record $R$, the value of its slot indexed by $16$ is the value of its $Q2$ register.

**Proof.** The index $rQ2$ is $16$. The value function's defining clause at index $16$ gives $R.Q2$, proving the equality directly.
