<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalMachine.lean :: BoolCircuit.CircuitEval.rew -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Erasing a Finite Tape Segment

**Claim.** Under the stated transition and tape hypotheses, starting with both work heads at $h_0-1$ in state $q$, after $h_0+1$ steps the machine is in state $d$ with both heads at zero, while its input position, tapes, and output are unchanged.

**Proof.** We induct on the segment length $h_0$. When $h_0=0$, the head starts at $-1$, where the selected tape is blank by hypothesis. The transition therefore takes the blank branch: it moves both heads right and enters state $d$. The other configuration components remain unchanged, giving the claimed result after the single step. For the successor case, the cell at position $h_0$ is occupied by the hypothesis on cells below $h_0+1$. The first transition consequently takes the occupied branch, keeps state $q$, and moves both heads left from $h_0$ to $h_0-1$, leaving all other components unchanged. Apply the induction hypothesis to the remaining segment of length $h_0$, using the inherited occupancy and left-boundary hypotheses. The run-length law for machine execution, which splits a run into an initial step and the remaining run (`Turing.MultiTapeTM.runFrom_succ_eq_step`), then gives the desired total of $h_0+2$ steps and final head position zero; the zero-step run law (`Turing.MultiTapeTM.runFrom_zero`) handles the base case. The one-step configuration update (`BoolCircuit.CircuitEval.step_cf`) identifies the transition effects, and a zero input-head movement leaves the input position fixed (`Turing.moveInputPos_zero`).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `BoolCircuit.CircuitEval.step_cf`, `Turing.moveInputPos_zero`.
