<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.scanCopy_suffix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying a Suffix from an Interior Position

**Claim.** If $x=pre++rest$, then after $|rest|+1$ steps from the scan configuration at position $|pre|$ in state $q$ with output $o$, the machine is halted at position $|x|$ with output $o++rest$.

**Proof.** Induct on the suffix `rest`. If it is empty, the scan position is already at the end of the input, so the machine reads blank. Its prescribed transition emits nothing, stays in place, and halts; the resulting configuration has the stated position and output. For a nonempty suffix $b::rest$, the current scanned symbol is $b$. The transition emits $b$, moves right, and remains in state $q$, so one step advances the scan to the position after $pre++[b]$ and changes the output to $o++[b]$. This one-step behavior follows from the scan reading fact (`scanCfg_read`), the right-move position fact (`moveInputPos_pos_of_ne_right`), and equality of configurations from their state, position, and output (`Cfg.ext_zero_tapes`). Apply the induction hypothesis to the remaining suffix, with the advanced prefix and output. Its run length is $|rest|+1$, and together with the first step this is the required $|(b::rest)|+1$ steps; associativity of list append gives output $o++(b::rest)$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.FinTM.scanCfg_read`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.Cfg.ext_zero_tapes`.
