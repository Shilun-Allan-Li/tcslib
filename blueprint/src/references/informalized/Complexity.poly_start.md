<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.poly_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Startup of the Box Enumerator

**Claim.** After $2(|x|+1)$ steps from the initial configuration, the machine is in loop level $c$ with input head just right of the input, each work tape containing $1^{|x|+1}$, all work heads at $0$, and empty output.

**Proof.** First, the input-copying phase reaches its copy configuration after $|x|$ steps. One further copy transition reads the blank immediately after the input: it writes a $1$ on each work tape at cell $|x|$, moves the input head to the next blank cell, and moves each work head to $|x|+1$. This yields the setup configuration with tape length $q=|x|+1$ and heads at $q-1$. The run-addition law splits the remaining $|x|+1$ steps from the initial $|x|+1$ steps. The setup-rewind result with $j=|x|$ then shows that those steps enter loop level $c$ and reset all heads to $0$, without changing the tapes or output.

**Key facts.** `Complexity.polyTape_write`, `Complexity.poly_copy`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.moveInputPos_zero`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.poly_setup`.
