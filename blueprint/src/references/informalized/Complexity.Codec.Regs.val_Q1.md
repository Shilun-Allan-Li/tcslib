<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.val_Q1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the Q1 Register

**Claim.** For any register record $R$, the value of its slot indexed by $15$ is the value of its $Q1$ register.

**Proof.** The index $rQ1$ is $15$, whose defining clause in the value function returns $R.Q1$. Hence the slot value equals the $Q1$ register.
