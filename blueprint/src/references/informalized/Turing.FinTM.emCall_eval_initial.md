<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_eval_initial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Evaluator Configuration

**Claim.** The evaluator configuration formed from the initial configuration of $M$ on $s$, with true boundary tag and physical input-head position $1$, equals the configuration whose initial evaluator state is active, whose first work tape stores $s$, and whose other work tapes are blank.

**Proof.** Configurations are equal once their state, input-head position, work tapes, work-head positions, and output agree. The state is the active evaluator state by the definitions of the initial machine state and the evaluator configuration; both input-head positions are $1$, and both outputs are empty. For the work tapes, the evaluator's tape layout consists of the buffer for $s$ followed by the simulated machine's work tapes. The latter are all blank initially, and the first buffer tape is exactly the tape for $s$. This is precisely the tape assignment specified by the word-state configuration. The work-head positions also agree: the buffer head is at the length of the empty output prefix, hence at zero, and the simulated work heads begin at zero.
