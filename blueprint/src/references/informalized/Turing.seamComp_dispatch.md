<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Seam.lean :: Turing.seamComp_dispatch -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seam Handoff at the Exit State

**Claim.** If a configuration of $M_1$ is in state $exit$, one step of the seam-composed machine from its left-state embedding is the same configuration with state changed to the right-state embedding of $entry$.

**Proof.** Unfold the one-step semantics and the state embedding. Since the embedded configuration has state $\mathrm{inl}(exit)$, the seam transition takes its exit branch: it prescribes no tape movement, no writes, and no output, and sets the successor state to $\mathrm{inr}(entry)$. The stationary-action identity (`seam_stationary_apply`) says that applying precisely this action leaves every configuration component unchanged except for setting its state to the prescribed successor. This is exactly the right-state embedding of the original configuration with its state replaced by $entry$.

**Key facts.** `Turing.seam_stationary_apply`.
