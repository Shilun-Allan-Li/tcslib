<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clInput_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complete Input-Copying Run

**Claim.** For every Boolean word $x$, after exactly $2|x|+2$ steps from the input copier's initial configuration on $x$, the machine is in its return control with $x$ on its work tape, both heads at their initial positions, and empty output.

**Proof.** Identify the initial configuration with the copier configuration in its copying control, with empty tape and both heads at their initial positions. The forward-copying result, run for $|x|$ steps, leaves the full word $x$ on the work tape, the input head at the right boundary, and the work head at position $|x|$. One further step turns the machine into state $1$, moving the input head left and the work head left once, without changing the tape or output. The backward-rewinding result with $j=|x|$ then takes $|x|+1$ steps to enter state $2$, return the input head to position $1$, and return the work head to $0$, preserving the tape and empty output. The run-addition law (Turing.MultiTapeTM.runFrom_add) combines these phases; their total duration is $|x|+1+(|x|+1)=2|x|+2$.

**Key facts.** `Complexity.clInput_forward`, `Turing.FinTM.moveInputPos_neg_val`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Complexity.clInput_backward`.
