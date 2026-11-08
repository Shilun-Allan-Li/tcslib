<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_finish_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact-Time Finalization

**Claim.** Starting the finalizer in state $0$ with words $a$ and $c$ on its tapes and heads at their lengths, after $|a|+3|c|+5$ steps it reaches state $5$. The argument tape contains $a$ in emit mode and $c$ otherwise; the capture tape is blank, both heads are at the origin, and the output is $c$ in emit mode and empty otherwise.

**Proof.** The first transition takes state $0$ to state $1$ and moves the argument head left once, giving head position $|a|-1$ (`moveInputPos_zero`). The argument-scan result then takes $|a|+1$ steps to state $2$, erasing the argument in install mode and positioning the capture head for the rewind (`emCall_finish_arg`). The rewind takes $|c|+1$ steps to state $3` (`emCall_finish_rewind`). The transfer phase takes another $|c|+1$ steps to state $4$, copying the capture word to the argument in install mode or emitting it in emit mode (`emCall_finish_transfer`). Finally, the erasure phase takes $|c|+1$ steps to state $5$ and blanks the capture tape (`emCall_finish_erase`). Compose these successive runs with the run-addition law (`MultiTapeTM.runFrom_add`). The initial single step is expressed using the successor-run identity and the zero-run identity (`MultiTapeTM.runFrom_succ_eq_step`, `MultiTapeTM.runFrom_zero`). Adding the phase lengths gives $1+(|a|+1)+(|c|+1)+(|c|+1)+(|c|+1)=|a|+3|c|+5$.

**Key facts.** `Turing.moveInputPos_zero`, `Turing.FinTM.emCall_finish_arg`, `Turing.FinTM.emCall_finish_rewind`, `Turing.FinTM.emCall_finish_transfer`, `Turing.FinTM.emCall_finish_erase`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
