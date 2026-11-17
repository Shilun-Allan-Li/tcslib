<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterAppend_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run of the Bit Appender

**Claim.** For each $j\le |x|$, after $j$ steps the bit-appending machine is in its scan configuration at head position $j+1$, with output the first $j$ bits of $x$.

**Proof.** Induct on $j$. At zero steps, the initial configuration agrees with the scan configuration at position one and with empty output. For the successor step, the induction hypothesis places the machine at the scan position for $j$. The scan configuration reads the next input symbol (`scanCfg_read`), which is the $j$th bit since $j<|x|$. The successor-run identity (`runFrom_succ_eq_step'`) reduces the next configuration to the machine's transition at that symbol. The transition emits that bit, advances the input head by one (`moveInputPos_pos_of_ne_right`), and remains in the scan state. The output is therefore the first $j+1$ bits, yielding the claimed scan configuration; equality of configurations is checked by their state, head position, and output, since there are no work tapes.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.scanCfg_read`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.Cfg.ext_zero_tapes`.
