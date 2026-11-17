<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_body_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width-Machine Simulation

**Claim.** Under the stated hypotheses on the run of $C$, the controller started in width-start reaches width state $c_x$ at time $t$, with $u$ on the width bank and the other words unchanged, and avoids the anchor at every time through $t$.

**Proof.** Apply the phase-simulation principle with $C$ as the simulated machine, the left-bank embedding as its tape placement, and the width-state constructor as the state embedding. At width-start, the controller's transition agrees with the embedded transition of $C$ from $c_e$. At every embedded state other than the designated exit state $c_x$, its transitions continue to agree with those of the embedded machine. The assumed exclusion of $c_x$ at all intermediate positive times therefore ensures that this simulation reaches the given time-$t$ endpoint. Phase simulation also guarantees anchor avoidance throughout the interval. The left-frame identity translates the simulated endpoint into the controller's bank layout: it places $u$ on the first width-bank tape and leaves the candidate and length-bank word $v$ unchanged.

**Key facts.** `Turing.FinTM.emitterP2_call_phase`, `Turing.FinTM.emitterP2_left_frame`.
