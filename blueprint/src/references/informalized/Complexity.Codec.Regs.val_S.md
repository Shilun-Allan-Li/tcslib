<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.val_S -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the S Register

**Claim.** For any register record $R$, the value of its slot indexed by $4$ is the value of its $S$ register.

**Proof.** The index $rS$ is $4$, and the defining clause for the value function at index $4$ returns $R.S$. Therefore the slot value equals the $S$ register.
