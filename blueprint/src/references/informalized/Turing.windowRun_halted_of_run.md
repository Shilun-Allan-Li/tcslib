<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/WindowRun.lean :: Turing.windowRun_halted_of_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Window Run Through a Halted Configuration

**Claim.** For a Boolean-input machine, if the run is halted at time $t$, the clock exceeds $t$, and every configuration through time $t$ stays in the radius-$s$ window, then the windowed run halts at that configuration and returns the accumulator obtained by applying $\sigma$ to its output.

**Proof.** Proceed by induction on the clock bound $N$. For $N=0$, the hypotheses $t<N$ are impossible. Suppose the bound is $N+1$. If the initial configuration is already halted, the run remains at that configuration at every time (`runFrom_of_halt`), and the windowed run halts immediately with the initial accumulator. Otherwise, $t$ cannot be zero, since the configuration at time zero would then already be halted. Write $t=t'+1$. The run identity `runFrom_succ_eq_step` identifies the configuration at time $t$ with the run from the one-step successor at time $t'$. The successor lies in the window by the assumed window condition at time one; likewise, all its run configurations through time $t'$ lie in the window, by shifting the original time indices by one. The induction hypothesis therefore applies to this successor with clock $N$. The windowed run takes that first transition and updates its accumulator using the emitted optional symbol. By `step_output`, the successor's output is the original output followed by that symbol, and the defining property of $\sigma$ says precisely that this update produces $\sigma$ of the successor's output. Thus the induction conclusion gives the required halted result.

**Key facts.** `Turing.MultiTapeTM.runFrom_of_halt`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.step_output`.
