<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.upd_E -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the E Register

**Claim.** For any register record $R$ and natural number $v$, updating the indexed register corresponding to $E$ in the register-value function of $R$ to $v$ gives the register-value function of the record obtained by replacing $R.E$ with $v$.

**Proof.** Evaluate both functions at an arbitrary register index. At the index corresponding to $E$, each has value $v$; at every other index, the named register is unchanged by the record update, so the values agree there as well. Thus the functions are equal.
