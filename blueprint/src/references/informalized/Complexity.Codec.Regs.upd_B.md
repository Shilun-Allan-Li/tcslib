<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.upd_B -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the B Register

**Claim.** For any register record $R$ and natural number $v$, updating the indexed register corresponding to $B$ in the register-value function of $R$ to $v$ gives the register-value function of the record obtained by replacing $R.B$ with $v$.

**Proof.** Compare the two functions at an arbitrary register index. At the index corresponding to $B$, both values are $v$. At every other index, both give the unchanged value of the corresponding named register. Hence the functions agree everywhere.
