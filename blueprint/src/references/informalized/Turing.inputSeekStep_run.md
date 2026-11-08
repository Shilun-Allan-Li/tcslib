<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/InputCall.lean :: Turing.inputSeekStep_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Head Seek Run

**Claim.** For every number of steps $r$, running the active input-seek machine from $c$ leaves every configuration component unchanged except the input position, which is obtained by iterating the clamped one-step rightward move $r$ times.

**Proof.** Induct on $r$. At zero steps, the run is the initial configuration, as asserted. For the successor case, the induction hypothesis identifies the configuration after $r$ steps as the original configuration with only its input position replaced by the $r$-fold iterate of the rightward move. The run successor identity (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) says the next configuration is one machine step from this one. Since the state remains active, the transition is the input-move action to the right; the one-step action rule (`Turing.step_of_inputMoveAction`) changes only the input position, applying one more rightward move. This is exactly the $(r+1)$-fold iterate, proving the induction step.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.step_of_inputMoveAction`.
