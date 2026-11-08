<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Parse.lean :: Complexity.LogProg.cmpPlain_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Plain-Word Comparison Run

**Claim.** From the common prefix, the comparison routine reaches the return state with the correct equality bit and an input head at the corresponding input offset; before that time, the routine stays in its comparison state and the register head remains within bounds.

**Proof.** Induct on the remaining input suffix $u_1$. If it is empty, the input symbol at the current position is absent. If the register suffix is empty as well, one comparison step returns true; if the register has a next symbol, that step returns false. In either case the final input position is unchanged, the register head is at the prescribed position, and the only earlier configuration is the initial one.

For a nonempty suffix with first bit $a$, the current input symbol is $a$. If the register has no next symbol, or its next bit $b$ differs from $a$, the comparison action returns false in one step. The two words then cannot be equal. If $a=b$, the action advances both heads by one and stays in the comparison state. Apply induction to the remaining suffixes with the common prefix extended by $a$, and join the resulting run to this first step. The equality decision agrees with the original words because their first bits match; the input-position identity and head bounds follow from the induction conclusion and the single-step movement. In every case, the earlier configurations are exactly those described in the corresponding one-step case or inherited from the induction run. The step calculations use the specified comparison transition, the register symbol read from the buffer tape, and the run concatenation law.

**Key facts.** `Complexity.LogProg.rrun_one_x`, `Complexity.LogProg.xCfg_read`, `Complexity.LogProg.apply_xAct`, `Complexity.LogProg.moveInputPos_pos_val`, `Complexity.LogProg.rrun_add`.
