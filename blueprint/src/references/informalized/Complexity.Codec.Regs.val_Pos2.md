<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.val_Pos2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the Pos2 Register

**Claim.** For any register record $R$, the value of its slot indexed by $12$ is the value of its $Pos2$ register.

**Proof.** The slot index $rPos2$ is $12$. By the defining clause for the value function at index $12$, the value of that slot is $R.Pos2$.
