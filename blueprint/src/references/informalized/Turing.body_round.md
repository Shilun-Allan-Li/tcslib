<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean :: Turing.body_round -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One round of the iteration body

**Claim.** Under the stated run and first-arrival hypotheses for $E$ and $G$, the emitted iteration body runs $E$, hands control to $G$, and returns to its anchor with $G$'s result on the first work tape, the other work tapes empty, and $E$'s output preserved. The anchor is not visited at any positive time before the end of this round.

**Proof.** 1. Regard the emitted body as a machine that embeds the work tapes and states of $E$ and $G$ into its larger state space. Its first step launches $E$ from the anchor configuration. The embedding step and run results (`embed_step`, `embed_run`) show that, until $E$ reaches its exit state, the body follows exactly the run of $E$ on the embedded tapes. The hypothesis that $E$ does not reach its exit state earlier ensures the embedded simulation remains in the call state at every intermediate step. The run therefore arrives at the embedded exit state after $t_E$ steps, with output $e_s$ (`embed_ofWords_left`, `embedCfg_output`).

2. One control step changes the exit state of $E$ to the start state for $G$, preserving the tapes and output (`control_step`). The next step launches $G$ from the same first-tape word $s$. The embedded-run argument applies again: the first-arrival hypothesis for $G$ ensures the body stays in the call state throughout the simulation, and after $t_G$ simulated steps its work tapes represent $G$'s terminal configuration.

3. The output produced by the body is the prefix $e_s$ followed by any output produced during the $G$ simulation. Since $G$'s terminal configuration has empty output and output only extends during a run (`runFrom_output_extends`), the simulation contributes no additional symbols. Prefix preservation (`runFrom_output_prefix`) thus leaves precisely $e_s$. At this checkpoint the body is in the embedded exit state of $G$; one final control step returns to the anchor (`control_step`), giving the claimed total of $t_E+1+t_G+1$ steps and the stated final configuration.

4. To verify that no earlier positive-time configuration is at the anchor, split the time into the $E$ simulation, the handoff, and the $G$ simulation. During the first simulation, each embedded configuration has a genuine machine state: the terminal run state implies this for every earlier time (`state_isSome_of_runFrom`), and the first-arrival hypothesis excludes the exit state before $t_E$. The handoff state is the distinct start state for $G$. During the second simulation, the same argument gives a genuine $G$ state and excludes its exit state before $t_G$. Hence none of these configurations is the anchor; the final control step is its first return.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.control_step`, `Turing.embedCfg_output`, `Turing.embed_ofWords_left`, `Turing.embed_ofWords_right`, `Turing.embed_run`, `Turing.embed_step`, `Turing.runFrom_one`, `Turing.runFrom_output_extends`, `Turing.runFrom_output_prefix`, `Turing.state_isSome_of_runFrom`.
