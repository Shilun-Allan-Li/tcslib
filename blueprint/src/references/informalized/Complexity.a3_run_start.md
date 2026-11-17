<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_run_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Arrival at the dispatch configuration

**Claim.** After $2|x|+2$ steps, the wrapper is in state $2$ of its setup states, with the input head back at the first input cell, $x$ on work tape zero, all other work tapes blank, all work-tape heads at zero, and empty output.

**Proof.** First apply the copy-run invariant through $|x|$ steps: the wrapper has reached the end of the input while copying all of $x$ onto work tape zero. At that boundary the input symbol is blank, so one transition moves the input head back one position and changes the setup phase from $0$ to $1$; the work tape contents and empty output are preserved. The remaining $|x|+1$ steps are exactly the rewind phase, whose invariant says that the input head returns to the first input cell while the stored word and other canonical tape data are preserved, and the wrapper enters phase $2$ (Complexity.a3_load_rewind). The time count is $|x|+1$ steps to reach the boundary transition, followed by $|x|+1$ steps to rewind; run addition combines these segments (Turing.MultiTapeTM.runFrom_add), and the boundary transition is identified by the run-successor identity (Turing.MultiTapeTM.runFrom_succ_eq_step'). The one-position backward move has the expected position change by the negative-move identity (Turing.FinTM.moveInputPos_neg_val).

**Key facts.** `Complexity.a3_copy_run`, `Complexity.a3_load_rewind`, `Turing.FinTM.moveInputPos_neg_val`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
