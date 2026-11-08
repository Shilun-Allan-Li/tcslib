<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_body_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length-Machine Simulation

**Claim.** Under the stated hypotheses on the run of $D$, the controller started in its length-start state reaches length state $d_x$ at time $t$, with candidate $s$ and bank words $u,z$, and it avoids the anchor at every time through $t$.

**Proof.** Apply the phase-simulation principle to the length phase, taking $D$ as the simulated machine, the right-bank embedding as its tape placement, and the length-state constructor as the state embedding. Its entry transition agrees with the embedded transition of $D$ from $d_e$; throughout the simulated run, every state before the exit is treated by that same transition rule. The hypothesis that $D$ does not visit $d_x$ at intermediate positive times supplies the required guard, so the controller continues simulating $D$ until the given time-$t$ configuration. The phase-simulation result therefore gives the corresponding embedded configuration at time $t$ and excludes the anchor during the simulated phase. Finally, the right-frame identity identifies that embedded configuration with the controller configuration whose candidate and other bank words remain fixed and whose length-bank word is now $z$. This yields both the asserted endpoint and anchor avoidance.

**Key facts.** `Turing.FinTM.emitterP2_call_phase`, `Turing.FinTM.emitterP2_right_frame`.
