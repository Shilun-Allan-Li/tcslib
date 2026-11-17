<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_copy_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix of the Guide-Copying Scan

**Claim.** For $j\le |x|$, after $j$ steps from the zero-copy phase, the machine is in the phase for $j$ copied symbols, with input head at $j+1$, guide head at $j$, and the corresponding partial guide; the other data are unchanged.

**Proof.** Induct on $j$. At zero, the initial configuration already has the stated phase, head positions, and partial guide. For the successor step, the induction hypothesis places the input head at position $j+1$. Since $j<|x|$, it reads the next symbol of $x$, so the copying transition advances the input and guide heads, writes the appropriate origin or interior symbol, and enters the phase for $j+1$ copied symbols. `copyGuide_next` identifies the updated tape with the partial guide for $j+1$. The action on the setup configuration is given by `setupCfg_apply`; the run successor law adds this transition to the first $j$ steps. The bound $j+1\le |x|$ ensures the next symbol exists and the new head positions are valid.

**Key facts.** `Complexity.setupCfg_input`, `Complexity.copyGuide_next`, `Complexity.setupCfg_apply`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
