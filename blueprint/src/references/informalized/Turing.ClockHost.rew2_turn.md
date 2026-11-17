<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.rew2_turn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transition from Rewind to Run

**Claim.** When the yard tape contains the word of $m$ true symbols and its head is at cell $-1$, one host step from phase $	ext{rew2}$ enters phase $	ext{run}$ with $A$ in its initial state and no captured output. The input head moves one position right, the yard head moves to cell $0$, and all other tape data and the output are preserved.

**Proof.** The host-step rule identifies the step from phase $	ext{rew2}$ with the corresponding branch of the host transition function. At the yard index, the tape contains no symbol: the yard tape is defined only on nonnegative cells, so its value at $-1$ is `none` (`yard_neg_one`). Thus the transition takes the empty-yard branch, which moves the input head right, advances the yard head by one, and sets the phase to $	ext{run}$ with state $A.q_0$ and empty capture. Applying this action leaves both machine work-tape blocks unchanged and appends no output; the yard head changes from $-1$ to $0$. The action-on-host-configurations formula records these componentwise updates (`apply_hostCfg`), yielding the stated configuration.

**Key facts.** `Turing.ClockHost.stepWith_hostCfg`, `Turing.ClockHost.yard_neg_one`, `Turing.ClockHost.apply_hostCfg`.
