<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a2_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complete countdown startup

**Claim.** For every binary input $x$, after exactly $2|x|+2$ steps from the countdown machine’s initial configuration, it is in the borrow phase with work tape $x$, head at $0$, input head at the right boundary, and empty output.

**Proof.** First apply the copy-run result (`a2_copy_run`) with $i=|x|$. Since taking all of $x$ returns $x$, after $|x|$ steps the machine is in its loading phase, with the input head at the right boundary, tape $x$, and work head at $|x|$. The transition at that boundary sees no input symbol; it changes to the startup state, leaves the input position and tape fixed, and moves the work head left to $|x|-1$. Thus after $|x|+1$ steps the configuration is the stated startup configuration. Split the total time as $(|x|+1)+(|x|+1)$. The run concatenation law (`runFrom_add`) lets us continue from that configuration, and `a2_load_rewind` with $j=|x|$ shows that the remaining $|x|+1$ steps rewind the work head to $0$ and enter the borrow phase, preserving the tape, input position, and empty output.

**Key facts.** `Complexity.a2_copy_run`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.moveInputPos_zero`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.a2_load_rewind`.
