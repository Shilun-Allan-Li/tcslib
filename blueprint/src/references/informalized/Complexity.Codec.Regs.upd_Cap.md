<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.upd_Cap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Cap Register

**Claim.** For any register record $R$ and natural number $v$, updating the indexed register corresponding to $Cap$ in the register-value function of $R$ to $v$ gives the register-value function of the record obtained by replacing $R.Cap$ with $v$.

**Proof.** Evaluate both functions at an arbitrary register index. At the index corresponding to $Cap$, each gives $v$; at every other index, each gives the value of the unchanged named register. Therefore the functions are equal.
