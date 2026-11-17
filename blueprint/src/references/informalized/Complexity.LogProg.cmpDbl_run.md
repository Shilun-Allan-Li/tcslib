<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ParseCmp.lean :: Complexity.LogProg.cmpDbl_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Doubled-Word Comparison Run

**Claim.** Starting at the common prefix of the input word and register word, the comparison routine reaches the return state with the correct equality bit, while all earlier configurations remain outside call states and keep the register head within the register word’s range.

**Proof.** Proceed by induction on the remaining input suffix $u_1$. If it is empty, the next two input symbols are the separator $01$. The first comparison action moves right into the false-comparison state; the second sees the separator and returns the equality test for the two words. Since their prefixes already agree and the input suffix is empty, this test is true exactly when the register suffix is empty. The run takes two steps, and its only earlier configurations are the initial state and the intervening false-comparison state; both satisfy the stated head bounds and are not call states.

If $u_1=b::u_1'$, the input hypothesis and the doubled-word encoding show that the next two input symbols are both $b$. The first comparison action moves right into the state corresponding to $b$. If the register has no symbol at the current head, or its symbol differs from $b$, the second action detects the mismatch and returns false immediately. The words cannot be equal in this case; the two-step run and its intermediate configurations have the required bounds.

Otherwise the register symbol is also $b$. The second action advances both heads by one cell and returns to the first comparison state. Apply the induction hypothesis to the remaining suffixes, with the common prefix extended by $b$ and the input head advanced by two. Concatenate the two-step prefix with that run. Its final equality bit is unchanged because the removed leading symbols agree, and the intermediate configurations consist of the two checked states followed by the induction run’s earlier configurations. The transition calculations use the one-step run equations, the specified comparison transitions, and the fact that the register initially contains the given word from cell zero.

**Key facts.** `Complexity.LogProg.reaches_right`, `Complexity.LogProg.rrun_one_x`, `Complexity.LogProg.xCfg_read`, `Complexity.LogProg.apply_xAct`, `Complexity.LogProg.rrun_add`.
