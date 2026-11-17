<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complete Guide Copying

**Claim.** From copy-left phase with input head at position $1$, guide head at $0$, and blank guide tape, after $2|x|+4$ steps the machine reaches budget-start phase with input head at $|x|+1$, guide head at $0$, and the partial guide containing $|x|+1$ copied cells; the other data are unchanged.

**Proof.** Split the run into the two-step initialization, the scan across the $|x|$ input symbols, the final copying step, and the return scan. `setupCfg_copy_left` performs the initialization, placing the machine in the zero-copy phase. `setupCfg_copy_prefix` carries out the $|x|$-step scan: at each step the current input symbol determines the next copy phase, the input and guide heads advance, and the guide tape is extended by one cell. The final cell is copied by `setupCfg_copy_end`, which changes the phase to copy-return and extends the guide to $|x|+1$ cells. Finally, `setupCfg_copy_return` returns the guide head to cell $0$ and enters budget-start. The run composition and successor laws assemble these pieces; their lengths sum to $2|x|+4$.

**Key facts.** `Complexity.setupCfg_copy_left`, `Complexity.setupCfg_copy_prefix`, `Complexity.setupCfg_copy_end`, `Complexity.setupCfg_copy_return`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
