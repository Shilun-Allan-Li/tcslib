<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/ClockMachine.lean :: Complexity.TimeHierarchy.clockTM_setup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Clock Machine Setup

**Claim.** If $K$ halts on $x$ with output $s$ after $t_K$ steps, then the clock machine reaches a decrement configuration with $W$ initialized on $x$, buffer $s$ at head position zero, and empty output, within $t_K+|s|+|x|+5$ steps.

**Proof.** Choose the earliest time $t$ at which $K$ halts, and let $c$ be its configuration then. Since $K$ also halts at time $t_K$, minimality gives $t\le t_K$. The computation specification gives that $c$ halts, and uniqueness of the output across halting computations implies that its output is $s` (`computesInTime_iff`, `ComputesInTime.output_unique`).

The clock machine simulates $K$ for these $t$ steps (`kCfg_init`, `kCfg_run`). Once $K$ halts, the clock configuration is rewound from its current input-head position: the rewind lemma reaches the input-start scan state while preserving $K$’s work tapes and placing its output on the buffer (`kCfg_rewind`). The timed rewind bound ensures this scan takes at most the input-head position plus two steps (`timed_rewind`). The clock’s input-start scan then moves back across the input and enters the decrement state, also with a bound controlled by the input-head position (`timed_rewind`). At this point the buffer contains $s$, its head is at zero, and the simulated configuration is $W$’s initial configuration. Combining the phases with the run-composition law (`runFrom_add`), and using $t\le t_K$ and the input-position bound, gives the stated total bound.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.output_unique`, `Complexity.TimeHierarchy.kCfg_init`, `Complexity.TimeHierarchy.kCfg_run`, `Complexity.TimeHierarchy.kCfg_rewind`, `Turing.FinTM.timed_rewind`, `Turing.MultiTapeTM.runFrom_add`.

**Caveat.** The supplied upstream statement for `timed_rewind` only describes scanning left to input position 1, while the proof also invokes a separate input-start scan argument to reach the decrement state. That auxiliary route and its precise step bound are not included among the supplied upstream statements.
