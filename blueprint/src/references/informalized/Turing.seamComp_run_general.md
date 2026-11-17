<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Seam.lean :: Turing.seamComp_run_general -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run Through a Seam Handoff

**Claim.** If the first machine reaches its exit state for the first time at time $T_1$, then after the handoff and a further $T_2$ steps, the seam-composed run is the right-state embedding of the corresponding $M_2$ configuration.

**Proof.** Apply the run-through-the-right-component theorem (`seamCompTM_runFrom_right`) with $t=T_2$. It identifies the seam run after $T_1+1+T_2$ steps with the right-state embedding of the $M_2$ run started from $c_1$ with its state replaced by $entry$. The hypothesis that this latter run reaches $c_3$ after $T_2$ steps lets us replace that run by $c_3$; applying the state embedding to the equality preserves it.

**Key facts.** `Turing.seamCompTM_runFrom_right`.
