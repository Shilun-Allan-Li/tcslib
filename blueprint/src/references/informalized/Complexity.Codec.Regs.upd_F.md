<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.upd_F -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the F Register

**Claim.** For any register record $R$ and natural number $v$, updating the indexed register corresponding to $F$ in the register-value function of $R$ to $v$ gives the register-value function of the record obtained by replacing $R.F$ with $v$.

**Proof.** Compare values at an arbitrary index. At the index corresponding to $F$, both sides give $v$. For every other index, both sides give the original value of that named register, since only $F$ is changed. Hence the two functions are equal.
