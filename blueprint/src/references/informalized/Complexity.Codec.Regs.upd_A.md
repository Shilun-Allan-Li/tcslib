<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.upd_A -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the A Register

**Claim.** For any register record $R$ and natural number $v$, updating the indexed register corresponding to $A$ in the register-value function of $R$ to $v$ gives the register-value function of the record obtained by replacing $R.A$ with $v$.

**Proof.** Compare the two functions at an arbitrary register index. If the index is the one corresponding to $A$, both functions have value $v$. At every other index, the indexed value is the unchanged named register in $R$, and the record update leaves that register unchanged. Thus the functions agree at every index and are equal.
