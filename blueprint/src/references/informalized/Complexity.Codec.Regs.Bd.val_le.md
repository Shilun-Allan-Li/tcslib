<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.Bd.val_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indexed Register Bound

**Claim.** If every named register of a register record $R$ is at most $B$, then every one of its 21 indexed register values is at most $B$.

**Proof.** Unpack the hypothesis into the 21 individual bounds, one for each named register. Now fix an index among the 21 possible indices. Its indexed value is, by the definition of the register-value function, the corresponding named register; the relevant bound from the unpacked hypothesis gives the result. The final index case is the $Z$ register, as specified by the definition.
