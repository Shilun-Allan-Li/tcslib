<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_start_core -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entering the Simulation Core

**Claim.** After the specified loading and rewinding steps, the machine is in the state-renamed simulation-core configuration initialized on $x$, with choice word $u$, choice head at $0$, boundary tag true, and physical input head at position $|y|+1$.

**Proof.** First take the single transition from loader state $3$. The loader reads the physical input at position $|y|+1$; the loader-read fact (`Complexity.cont_load_read`) identifies this as the end marker, so this transition moves to loader state $4$ without writing a symbol. The input head stays fixed, and the input-buffer head moves from $|x|$ to $|x|-1$. This is the intermediate configuration recorded in the proof. Next, split the remaining time using the run-composition law (`Turing.MultiTapeTM.runFrom_add`). Rewinding the input buffer for $|x|+1$ steps brings the machine to loader state $5$, with that buffer head at $0$ and the choice-buffer head still at $|u|$ (`Complexity.cont_rewind_input`). Rewinding the choice buffer for $|u|+1$ further steps enters the simulation core, with its choice head at $0$ (`Complexity.cont_rewind_choices`). The initial configuration of the core has the original machine's initial state and the true boundary tag, as required; the fixed physical input position is preserved throughout. The run identities at time zero and one-step time, together with the fact that a zero input-head move leaves its position unchanged, justify the initial transition calculation and the stated time decomposition.

**Key facts.** `Complexity.cont_load_read`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_zero`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.cont_rewind_input`, `Complexity.cont_rewind_choices`.
