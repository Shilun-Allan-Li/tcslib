<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_absorb -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absorption by a Silent Self-Loop

**Claim.** If the machine in state $q_a$ always makes the stationary, output-free action that returns to $q_a$, then every finite iteration of its step function leaves any configuration in state $q_a$ unchanged.

**Proof.** Induct on the number of steps. At zero steps the configuration is unchanged. For the successor step, the iteration equation (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) expresses the result as one machine step after the preceding run. By induction the preceding run is the original configuration, whose state is $q_a$. The transition hypothesis makes the next action the control action with zero input movement and the same state. The control-action application rule (`Turing.FinTM.controlAction_apply`) shows that this action leaves the tapes, head positions, and output intact and changes only the state and input position; the zero-movement identity (`Turing.moveInputPos_zero`) says the input position is unchanged as well. Thus the entire configuration is again the original one.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
