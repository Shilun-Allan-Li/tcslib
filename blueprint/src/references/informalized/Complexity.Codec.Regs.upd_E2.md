<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.upd_E2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the E2 Register

**Claim.** For any register record $R$ and natural number $v$, updating the indexed register corresponding to $E2$ in the register-value function of $R$ to $v$ gives the register-value function of the record obtained by replacing $R.E2$ with $v$.

**Proof.** At the index corresponding to $E2$, the updated indexed function and the updated record both have value $v$. At every other index, both retain the corresponding named register's original value. The functions consequently agree at every index.
