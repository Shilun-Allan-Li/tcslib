<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_evaluation_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Startup of the Evaluation Phase

**Claim.** If exact-consumption parsing succeeds on $x$, the verifier on the paired input $(x,u)$ reaches the formula-level evaluation state, with $u$ on its work tape and the work head at zero, within the stated time bound.

**Proof.** Write the paired input as a doubled copy of $x$, followed by the separator and $u$. The syntax scan processes the doubled encoding of $x$ in $2|x|+2$ steps (`Complexity.taut_syntax_run`). Parsing succeeds exactly when the syntax scanner accepts (`Complexity.taut_syntax_parse`), so this scan ends in the copy state. The verifier then copies all of $u$ onto its work tape in $|u|$ steps (`Complexity.taut_copy_run`), leaving the input head at the end and the work head at $|u|$. One transition enters the copy-back state and moves the work head to $|u|-1$. The work-tape rewind result (`Complexity.taut_work_rewind`) scans back to cell zero and enters the rewind-start state. Next, timed input rewind returns the input head to the start of the paired input and enters the formula-level evaluation state (`Turing.FinTM.timed_rewind`); its number of steps is at most the input-position bound supplied by that result. Adding these phases using the run-addition law (`Turing.MultiTapeTM.runFrom_add`) gives the claimed configuration. The total fits the advertised bound after substituting $|\langle x,u\rangle|=2|x|+2+|u|$ (`Turing.universal_pair_length`) and combining the scan, copy, one-step transition, and two rewind bounds. The configuration transitions use the established initialization and input-reading facts (`Complexity.taut_init`, `Complexity.taut_read`) and the movement law for a stationary input head (`Complexity.taut_move_stay`).

**Key facts.** `Complexity.taut_syntax_parse`, `Complexity.taut_syntax_run`, `Complexity.taut_copy_run`, `Complexity.taut_read`, `Complexity.taut_move_stay`, `Complexity.taut_work_rewind`, `Turing.FinTM.timed_rewind`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.universal_pair_length`, `Complexity.taut_init`.
