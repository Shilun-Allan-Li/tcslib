<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_setup_capture -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Setup Simulation Capture

**Claim.** If the program machine halts on input $x$ with output $y$ and uses at most $s$ work-tape cells, then the host reaches its origin phase with its designated tape storing $y$, its head at $|y|$, and every other work-tape cell blank. Up to that time, every work-tape head stays within distance $s+|y|$ of the origin.

**Proof.** Run the cleaned simulation of $M_P$ in the host’s setup phase. The cleaned-capture result (Complexity.b2b_clean_capture) supplies a time and input-head position at which this simulation has produced $y$, has cleaned its simulated work tapes, and has its simulated heads returned to the origin; throughout the run its heads satisfy the bound furnished by that result. The capture-shape lemma (Complexity.b2b_capture_shape) identifies the embedded configuration: the designated host tape now contains the output word and its head is at $|y|$, while the other host tapes retain their blank contents and origin heads. The designated tape is separate from the embedded simulation bank, so the two parts of the configuration combine as claimed. Finally, the setup phase redirects from the cleaned simulation’s exit to the host’s origin phase in one step. The phase-host simulation lemma (Turing.phaseHostTM_run) carries the simulation and its intermediate head bounds through this phase, and the last redirect preserves the bound since the newly positioned tape head is at $|y|\le s+|y|$.

**Key facts.** `Complexity.b2b_clean_capture`, `Complexity.b2b_capture_shape`, `Turing.phaseHostTM_run`.
