<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_syntax_double -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two Steps on a Doubled Bit

**Claim.** Under the stated position and bit hypotheses, after two verifier steps the syntax state is the result of one syntax transition on the repeated bit, the input position has advanced by two, and the work tape remains empty with its head at zero.

**Proof.** For the first step, the verifier reads the bit at position $i$. The read characterization (`Complexity.taut_read`) and the hypothesis that this bit is $b$ determine the transition from the first syntax substate to the second syntax substate carrying $b$. The right-move property (`Complexity.taut_move_right`) shows that this step advances the input head by one while leaving the empty work tape and its head position unchanged. Apply the same reasoning to the second step: at position $i+1$, the input bit is again $b$, so the second substate transitions to the first syntax substate carrying the state reached by the syntax transition on $b$. A second right move advances the input position to $i+2$. The two-step unfolding of the run (`Turing.MultiTapeTM.runFrom_succ_eq_step`), together with the zero-step identity (`Turing.MultiTapeTM.runFrom_zero`), identifies these two successive transitions with the stated run of length two.

**Key facts.** `Complexity.taut_read`, `Complexity.taut_move_right`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
