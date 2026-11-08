<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_right_edge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Right Boundary Transition

**Claim.** Starting in right-edge phase with unary head at $B+1$ and guide head at $R+1$, one step enters layout-return phase $0$, moves those heads to $B$ and $R$, and changes the guide tape to the right guide of radius $R$, leaving the other configuration data unchanged.

**Proof.** In the right-edge phase, the transition keeps the input head and budget tape fixed, moves the unary head one cell left, and writes the right-edge marker on the guide tape at the current guide-head position while moving that head one cell left. Applying the configuration-update rule (`setupCfg_apply`) therefore changes the phase to layout-return phase $0$, changes the head positions from $B+1,R+1$ to $B,R$, and updates the guide tape at $R+1$. This single update to the partial guide is exactly the right guide of radius $R$; all remaining configuration components are preserved.

**Key facts.** `Complexity.setupCfg_apply`.
