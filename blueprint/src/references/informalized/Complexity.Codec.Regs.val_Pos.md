<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.val_Pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the Pos Register

**Claim.** For any register record $R$, the value of its slot indexed by $11$ is the value of its $Pos$ register.

**Proof.** The slot index $rPos$ is $11$, and the defining clause for the value function at index $11$ returns $R.Pos$. The claimed equality follows directly from this definition.
