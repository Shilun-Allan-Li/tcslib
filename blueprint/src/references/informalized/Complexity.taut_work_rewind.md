<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_work_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work Tape Rewind

**Claim.** Under the stated transition rule, starting with the work head at position $n-1$ and the tape containing $u$, after $n+1$ steps the machine is in state $d$ with its work head at $0$, and the input head, tape, and output are unchanged.

**Proof.** We argue by induction on $n$, keeping the input, tape, and initial-state data fixed. If $n=0$, the head starts at $-1$, where the tape is blank by the definition of the buffer tape. The transition therefore enters state $d$ and moves the head right to $0$. The auxiliary one-step calculation ( `taut_move_stay` ) records that this move preserves the input head, tape, and output; the run then has the required result after one step. For the induction step, write the starting position as $n$. Since $n<|u|$, the cell at position $n$ contains $u_n$. The transition rule for a nonblank cell keeps the machine in state $q$ and moves the head left, leaving the other configuration data unchanged ( `taut_move_stay` ). Thus the first step takes the configuration with head at $n$ to the one with head at $n-1$. The induction hypothesis, applied to $n$ and the same tape, gives the desired result after the remaining $n+1$ steps. The run decomposition into one step followed by the remaining steps is `runFrom_succ_eq_step`; `runFrom_zero` supplies the zero-step base of the run calculation.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Complexity.taut_move_stay`.
